module

public import LeanFlagAlgebras.Automation.ExprHelpers
public import LeanFlagAlgebras.Forbid.Basic
public meta import LeanFlagAlgebras.Automation.ExprHelpers

@[expose] public section

/-! # Automation.FlagMulReduce — the `reduce_flagmul` and `reduce_downward_flagmul` tactics

Part of the Automation layer. This module defines two custom tactics that
reduce flag-algebra product expressions:

* `reduce_flagmul` — proves goals of the shape
  `(flag) * (flag) = (linear combination of flags)`.
  It unfolds flag multiplication to a finite sum, rewrites by the generated
  `flagSet_*_eq_univ` / `flagSet_*_val_eq` lemmas, and closes by algebraic
  normalization.

* `reduce_downward_flagmul` — iteratively eliminates the
  `downward (c • (A * B))` summands on the left-hand side of a `forbidLEWith`/`inducedForbidLE` goal
  by rewriting each flag product `A * B` with its precomputed `flagMul_*`
  expansion theorem and moving the rewritten term onto the right-hand side.
  Plain flag summands (no `downward` wrapper) are moved directly.
  Each rewrite tries the ordinary `forbidLEWith_*` lemma first and falls back to
  the matching `inducedForbidLE_*` lemma, so the tactic drives both the ordinary
  `≤[H]` Flagmatic examples and the induced `≤ᵢ[F]` consumers (e.g. `API/K4freeP4`).

Shared Expr helpers are provided by `Automation.ExprHelpers`.
-/

open FlagAlgebras Forbid
open Lean Elab Tactic Meta

namespace FlagAlgebras.Automation

/--
`reduce_flagmul` proves goals of the shape
`(flag) * (flag) = (linear combination of flags)`.

It unfolds flag multiplication to a finite sum, rewrites by
`flagSet_{N}_{k}_{m}_eq_univ` and `flagSet_{N}_{k}_{m}_val_eq`, and closes by
algebraic normalization. The RHS add-order is handled up to associativity and
commutativity.
-/
syntax (name := reduceFlagMulTac) "reduce_flagmul" : tactic

elab_rules : tactic
  | `(tactic| reduce_flagmul) => do
      withMainContext do
        evalTactic (← `(tactic| try dsimp))
        let goal ← getMainGoal
        let goalTy ← goal.getType
        let some (_, lhs, rhs) := goalTy.eq?
          | throwError "Goal must be an equality."

        let lhsConsts := collectFlagAlgebraConsts lhs
        let rhsConsts := collectFlagAlgebraConsts rhs

        let some lhsConst := lhsConsts[0]?
          | throwError "Could not find a `FlagAlgebra_*` constant on the LHS."
        let some (_, kVal, mVal, _) := parseFlagAlgebraIndices? lhsConst
          | throwError m!"Could not parse indices from LHS constant `{lhsConst}`."

        let rhsNs := rhsConsts.toList.filterMap (fun nm =>
          match parseFlagAlgebraIndices? nm with
          | some (n, _, _, _) => some n
          | none => none)
        if rhsNs.isEmpty then
          throwError "Could not infer target size `N` from RHS `FlagAlgebra_*` constants."
        let nVal := rhsNs.foldl Nat.max 0

        let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
        let valEqName  : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
        let eqUnivId : TSyntax `ident := mkIdent eqUnivName
        let valEqId  : TSyntax `ident := mkIdent valEqName

        evalTactic (← `(tactic| apply Quotient.sound))
        evalTactic (← `(tactic| dsimp))
        evalTactic (← `(tactic| simp [FlagAlgebras.flagVector_mul_eq_nested_sum, FlagAlgebras.flagMul, FlagAlgebras.flagMulWithSize]))
        evalTactic (← `(tactic| have h_eq_univ := $eqUnivId))
        evalTactic (← `(tactic| have h_val_eq := $valEqId))
        evalTactic (← `(tactic| rw [Finset.sum_eq_multiset_sum, ← h_eq_univ]))
        evalTactic (← `(tactic| simp [h_val_eq]))
        try
          evalTactic (← `(tactic| ring_nf))
        catch _ =>
          pure ()
        try
          evalTactic (← `(tactic| apply FlagAlgebras.flagVector_eq_eqv; ring_nf))
        catch _ =>
          pure ()
        try
          evalTactic (← `(tactic| apply FlagAlgebras.flagVector_eq_eqv; simp [add_assoc, add_left_comm, add_comm]))
        catch _ =>
          pure ()

/-!
`reduce_downward_flagmul` automates the rewriting pattern shown in the example
just below.  Given a goal of the form

```
  downward (c₁ • (A₁ * B₁)) + downward (c₂ • (A₂ * B₂)) + ... + downward (cₙ • (Aₙ * Bₙ))
    ≤ᵢ[F_forbid] rhs
```

it repeatedly looks at the head term of the left-hand side (after right-
associating the addition with `simp only [add_assoc]`), looks up the
corresponding `flagMul_<A>_<B>` theorem from the constants used in the head
term, and rewrites the head using

```
  Forbid.forbidLEWith_rw_left_add_right (downward_forbidEqWith_equal_flags
    (forbidEqWith_smul flagMul_<A>_<B>))
  forbidLEWith_move_add_left_iff
```

For the final (right-most) summand it instead uses

```
  forbidLEWith_rw_left (downward_forbidEqWith_equal_flags (forbidEqWith_smul flagMul_<A>_<B>))
  forbidLEWith_move_term_left_iff
```
-/

/-- Build the `forbidEqWith`/`inducedForbidEq` rewrite proof `hfg` for the (already
`downward`-unwrapped) inner term `downInner`, returning `(hfg, g)` where `g` is the
right-hand (expanded) side of `hfg`'s type — the term the head becomes after rewriting.
Returns `none` when `downInner` is not a (possibly smul- or neg-wrapped) flag product;
throws (as the original `rw`-based tactic did) when it *is* a product but no matching
`flagMul_*` theorem exists. `isInduced` selects the induced lemma family. -/
private meta def mkDownwardRewriteProof?
    (downInner : Expr) (isInduced : Bool) (curNs : Name)
    : TacticM (Option (Expr × Expr)) := do
  let mkHfg (stx : TSyntax `term) : TacticM (Expr × Expr) := do
    let hfg ← Lean.Elab.Term.elabTermAndSynthesize stx none
    pure (hfg, (← inferType hfg).getAppArgs.back!)
  let lookup (mulTerm : Expr) (label : String) : TacticM Name := do
    match ← mkFlagMulThmName? mulTerm curNs with
    | some nm => pure nm
    | none =>
        let fNm? := findFlagAlgebraConst? mulTerm |>.orElse (fun _ => findFlagConst? mulTerm)
        throwError m!"reduce_downward_flagmul ({label}): could not find flagMul theorem \
for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
  if let some (c, mulTerm) := getSmulArgs? downInner then
    let thmId : TSyntax `term := mkIdent (← lookup mulTerm "smul branch")
    let cStx ← Lean.Elab.Term.exprToSyntax c
    return some (← mkHfg (← if isInduced then
        `(downward_inducedForbidEq_equal_flags (inducedForbidEq_smul (c := $cStx) $thmId))
      else
        `(downward_forbidEqWith_equal_flags (forbidEqWith_smul (c := $cStx) $thmId))))
  else if let some negInner := stripNeg? downInner then
    if (getMulArgs? negInner).isSome then
      let thmId : TSyntax `term := mkIdent (← lookup negInner "neg-mul branch")
      return some (← mkHfg (← if isInduced then
          `(downward_inducedForbidEq_equal_flags (inducedForbidEq_neg $thmId))
        else
          `(downward_forbidEqWith_equal_flags (forbidEqWith_neg $thmId))))
    else
      return none
  else if (getMulArgs? downInner).isSome then
    let thmId : TSyntax `term := mkIdent (← lookup downInner "bare-mul branch")
    return some (← mkHfg (← if isInduced then
        `(downward_inducedForbidEq_equal_flags $thmId)
      else
        `(downward_forbidEqWith_equal_flags $thmId)))
  else
    return none

/-- Perform a single reduction step **as a term** on the current goal
`goal : R curLhs curRhs` (`R` = `forbidLEWith C` or `inducedForbidLE F`, `cOrF` the
condition / forbidden flag). Move and rewrite lemmas are applied via `mkAppOptM` + `Iff.mpr`
+ `MVarId.assign` rather than `rw`: the goal is root-anchored so no `kabstract` scan is
needed, and `curLhs`/`curRhs` are passed in as state instead of re-read from the goal type.
Returns `some (newGoal, newLhs, newRhs)` on progress, `none` otherwise. The resulting goal
shape is exactly the one the previous `rw`-based tactic produced. -/
private meta def stepReduceDownwardFlagMulTerm
    (goal : MVarId) (cOrF curLhs curRhs : Expr) (isInduced : Bool) (curNs : Name)
    : TacticM (Option (MVarId × Expr × Expr)) := do
  let mkMoveAdd (g rest : Expr) : TacticM Expr :=
    mkAppOptM
      (if isInduced then ``Forbid.inducedForbidLE_move_add_left_iff
       else ``Forbid.forbidLEWith_move_add_left_iff)
      #[none, none, some cOrF, some g, some rest, some curRhs]
  let mkMoveTerm (g : Expr) : TacticM Expr :=
    mkAppOptM
      (if isInduced then ``Forbid.inducedForbidLE_move_term_left_iff
       else ``Forbid.forbidLEWith_move_term_left_iff)
      #[none, none, some cOrF, some g, some curRhs]
  let mkRwAdd (hfg rest : Expr) : TacticM Expr :=
    mkAppOptM
      (if isInduced then ``Forbid.inducedForbidLE_rw_left_add_right
       else ``Forbid.forbidLEWith_rw_left_add_right)
      #[none, none, none, none, none, some rest, some curRhs, some hfg]
  let mkRwTerm (hfg : Expr) : TacticM Expr :=
    mkAppOptM
      (if isInduced then ``Forbid.inducedForbidLE_rw_left
       else ``Forbid.forbidLEWith_rw_left)
      #[none, none, none, none, none, some curRhs, some hfg]
  -- Given the step's `move` iff and a wrapper for the inner proof (identity, or a preceding
  -- `rw` iff), create the new goal, assign the composed `Iff.mpr` proof, and return the new
  -- residual `(lhs, rhs)` read off the new goal type.
  let finish (moveIff : Expr) (wrap : Expr → TacticM Expr) : TacticM (MVarId × Expr × Expr) := do
    let moveTy ← inferType moveIff
    let iffArgs := moveTy.getAppArgs
    unless moveTy.getAppFn.isConstOf ``Iff && iffArgs.size == 2 do
      throwError "reduce_downward_flagmul: move lemma did not produce an `Iff`"
    let newGoalType := iffArgs[1]!
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType
    let proof ← wrap (← mkAppM ``Iff.mpr #[moveIff, newGoal])
    goal.assign proof
    let ga := newGoalType.getAppArgs
    pure (newGoal.mvarId!, ga[ga.size - 2]!, ga[ga.size - 1]!)
  match getAddArgs? curLhs with
  | some (headRaw, rest) =>
    let head := headRaw.consumeMData
    if let some downInner := stripDownward? head then
      match ← mkDownwardRewriteProof? downInner.consumeMData isInduced curNs with
      | some (hfg, g) =>
        let rwIff ← mkRwAdd hfg rest
        return some (← finish (← mkMoveAdd g rest)
          (fun inner => mkAppM ``Iff.mpr #[rwIff, inner]))
      | none => return none
    else if hasFlagConst head then
      return some (← finish (← mkMoveAdd head rest) pure)
    else
      return none
  | none =>
    let lhs := curLhs.consumeMData
    if let some downInner := stripDownward? lhs then
      match ← mkDownwardRewriteProof? downInner.consumeMData isInduced curNs with
      | some (hfg, g) =>
        let rwIff ← mkRwTerm hfg
        return some (← finish (← mkMoveTerm g)
          (fun inner => mkAppM ``Iff.mpr #[rwIff, inner]))
      | none => return none
    else if hasFlagConst lhs then
      return some (← finish (← mkMoveTerm lhs) pure)
    else
      return none

/-- Drive `stepReduceDownwardFlagMulTerm` to a fixpoint (bounded by `fuel`), threading the
residual `(lhs, rhs)` and current goal as state so the goal type is read exactly once (not
once per step). Iterative `for` loop for constant native stack. If no step ever made
progress, fail with a diagnostic describing the goal shape. -/
private meta partial def runReduceDownwardFlagMul
    (fuel : Nat := 16384) : TacticM Unit :=
  withMainContext do
    let curNs  ← getCurrNamespace
    let goal0  ← getMainGoal
    let target ← goal0.getType
    let args   := target.getAppArgs
    if args.size < 3 then
      throwError m!"reduce_downward_flagmul: target has too few args: {target}"
    let isInduced := target.getAppFn.isConstOf ``Forbid.inducedForbidLE
    let cOrF   := args[args.size - 3]!
    let mut curGoal := goal0
    let mut curLhs  := args[args.size - 2]!.consumeMData
    let mut curRhs  := args[args.size - 1]!
    let mut steps : Nat := 0
    for _ in [0:fuel] do
      match ← stepReduceDownwardFlagMulTerm curGoal cOrF curLhs curRhs isInduced curNs with
      | none => break
      | some (g, newLhs, newRhs) =>
        curGoal := g
        curLhs  := newLhs.consumeMData
        curRhs  := newRhs
        steps   := steps + 1
    replaceMainGoal [curGoal]
    if steps = fuel then
      throwError "reduce_downward_flagmul: fuel exhausted"
    if steps = 0 then
      let add?  := getAddArgs? curLhs
      let down? := stripDownward? curLhs
      let smulOnHead? : Option (Expr × Expr) := match add? with
        | some (h, _) =>
            match stripDownward? h.consumeMData with
            | some inner => getSmulArgs? inner.consumeMData
            | none => none
        | none => none
      throwError m!"reduce_downward_flagmul made no progress. lhs={curLhs}; addDetected={add?.isSome}; downwardDetected={down?.isSome}; smulOnHeadDetected={smulOnHead?.isSome}"

/-- Repeatedly rewrite the left-hand side of a `forbidLEWith`/`inducedForbidLE` goal whose summands
have the form `downward (c • (A * B))`, replacing each `A * B` with the
expansion supplied by the corresponding `flagMul_*` theorem and moving the
already-rewritten terms onto the right.

Before iterating, this tactic right-associates the sum with
`simp only [downward_add, add_assoc]`. -/
elab "reduce_downward_flagmul" : tactic => do
  evalTactic (← `(tactic| try simp only [downward_add, add_assoc]))
  runReduceDownwardFlagMul

end FlagAlgebras.Automation
