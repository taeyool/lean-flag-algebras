import LeanFlagAlgebras.Automation.ExprHelpers
import LeanFlagAlgebras.Forbid.Basic

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

/-- Perform a single reduction step on a `forbidLEWith`/`inducedForbidLE` goal with `downward`-wrapped
summands. Returns `true` when progress was made.

Three kinds of head terms inside a `downward (...)` wrapper are handled:
* `downward (c • (A * B))` — smul-wrapped product. Look up the `flagMul_*`
  theorem and rewrite via `forbidEqWith_smul`.
* `downward (A * B)` — bare product (no smul). Same lookup, but without the
  `forbidEqWith_smul` wrapper. This catches terms whose `1 • _` coefficient was
  simplified away by an earlier `simp` step.
* plain flag term (contains a `FlagAlgebra_*` / `Flag_*` constant but is not
  wrapped in `downward`) — move directly with `forbidLEWith_move_add_left_iff` /
  `forbidLEWith_move_term_left_iff` without any rewriting. -/
private def stepReduceDownwardFlagMul : TacticM Bool :=
  withMainContext do
    let curNs ← getCurrNamespace
    let goal   ← getMainGoal
    let target ← goal.getType
    let args   := target.getAppArgs
    if args.size < 2 then
      return false
    let lhs := args[args.size - 2]!.consumeMData
    if let some (head, _rest) := getAddArgs? lhs then
      -- non-final case: head is the leftmost summand
      let head := head.consumeMData
      if let some downInner := stripDownward? head then
        let downInner := downInner.consumeMData
        if let some (_c, mulTerm) := getSmulArgs? downInner then
          -- (a) head = downward (c • (A * B))
          let some thmName ← mkFlagMulThmName? mulTerm curNs
            | do
                let fNm? := findFlagAlgebraConst? mulTerm |>.orElse (fun _ => findFlagConst? mulTerm)
                throwError m!"reduce_downward_flagmul (smul branch): could not find flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            first
            | rw [Forbid.forbidLEWith_rw_left_add_right
                    (downward_forbidEqWith_equal_flags (forbidEqWith_smul (c := _) $thmId)),
                  forbidLEWith_move_add_left_iff]
            | rw [Forbid.inducedForbidLE_rw_left_add_right
                    (downward_inducedForbidEq_equal_flags (inducedForbidEq_smul (c := _) $thmId)),
                  inducedForbidLE_move_add_left_iff]))
          return true
        else if let some negInner := stripNeg? downInner then
          -- (b') head = downward (-(A * B)) — a `(-1) • _` coefficient simplified to a bare negation
          if (getMulArgs? negInner).isSome then
            let some thmName ← mkFlagMulThmName? negInner curNs
              | do
                  let fNm? := findFlagAlgebraConst? negInner |>.orElse (fun _ => findFlagConst? negInner)
                  throwError m!"reduce_downward_flagmul (neg-mul branch): could not find flagMul theorem for mulTerm={negInner}; detectedConst={fNm?.getD Name.anonymous}"
            let thmId : TSyntax `term := mkIdent thmName
            evalTactic (← `(tactic|
              first
              | rw [Forbid.forbidLEWith_rw_left_add_right
                      (downward_forbidEqWith_equal_flags (forbidEqWith_neg $thmId)),
                    forbidLEWith_move_add_left_iff]
              | rw [Forbid.inducedForbidLE_rw_left_add_right
                      (downward_inducedForbidEq_equal_flags (inducedForbidEq_neg $thmId)),
                    inducedForbidLE_move_add_left_iff]))
            return true
          else
            return false
        else if (getMulArgs? downInner).isSome then
          -- (b) head = downward (A * B) — no smul wrapper
          let some thmName ← mkFlagMulThmName? downInner curNs
            | do
                let fNm? := findFlagAlgebraConst? downInner |>.orElse (fun _ => findFlagConst? downInner)
                throwError m!"reduce_downward_flagmul (bare-mul branch): could not find flagMul theorem for mulTerm={downInner}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            first
            | rw [Forbid.forbidLEWith_rw_left_add_right
                    (downward_forbidEqWith_equal_flags $thmId),
                  forbidLEWith_move_add_left_iff]
            | rw [Forbid.inducedForbidLE_rw_left_add_right
                    (downward_inducedForbidEq_equal_flags $thmId),
                  inducedForbidLE_move_add_left_iff]))
          return true
        else
          return false
      else if hasFlagConst head then
        -- head is a plain flag term: move it directly
        evalTactic (← `(tactic| first | rw [forbidLEWith_move_add_left_iff] | rw [inducedForbidLE_move_add_left_iff]))
        return true
      else
        return false
    else
      -- terminal case: lhs itself is a single term
      if let some downInner := stripDownward? lhs then
        let downInner := downInner.consumeMData
        if let some (_c, mulTerm) := getSmulArgs? downInner then
          -- (a) lhs = downward (c • (A * B))
          let some thmName ← mkFlagMulThmName? mulTerm curNs
            | do
                let fNm? := findFlagAlgebraConst? mulTerm |>.orElse (fun _ => findFlagConst? mulTerm)
                throwError m!"reduce_downward_flagmul (terminal smul branch): could not find flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            first
            | rw [forbidLEWith_rw_left
                    (downward_forbidEqWith_equal_flags (forbidEqWith_smul (c := _) $thmId)),
                  forbidLEWith_move_term_left_iff]
            | rw [inducedForbidLE_rw_left
                    (downward_inducedForbidEq_equal_flags (inducedForbidEq_smul (c := _) $thmId)),
                  inducedForbidLE_move_term_left_iff]))
          return true
        else if let some negInner := stripNeg? downInner then
          -- (b') lhs = downward (-(A * B))
          if (getMulArgs? negInner).isSome then
            let some thmName ← mkFlagMulThmName? negInner curNs
              | do
                  let fNm? := findFlagAlgebraConst? negInner |>.orElse (fun _ => findFlagConst? negInner)
                  throwError m!"reduce_downward_flagmul (terminal neg-mul branch): could not find flagMul theorem for mulTerm={negInner}; detectedConst={fNm?.getD Name.anonymous}"
            let thmId : TSyntax `term := mkIdent thmName
            evalTactic (← `(tactic|
              first
              | rw [forbidLEWith_rw_left
                      (downward_forbidEqWith_equal_flags (forbidEqWith_neg $thmId)),
                    forbidLEWith_move_term_left_iff]
              | rw [inducedForbidLE_rw_left
                      (downward_inducedForbidEq_equal_flags (inducedForbidEq_neg $thmId)),
                    inducedForbidLE_move_term_left_iff]))
            return true
          else
            return false
        else if (getMulArgs? downInner).isSome then
          -- (b) lhs = downward (A * B) — no smul wrapper
          let some thmName ← mkFlagMulThmName? downInner curNs
            | do
                let fNm? := findFlagAlgebraConst? downInner |>.orElse (fun _ => findFlagConst? downInner)
                throwError m!"reduce_downward_flagmul (terminal bare-mul branch): could not find flagMul theorem for mulTerm={downInner}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            first
            | rw [forbidLEWith_rw_left
                    (downward_forbidEqWith_equal_flags $thmId),
                  forbidLEWith_move_term_left_iff]
            | rw [inducedForbidLE_rw_left
                    (downward_inducedForbidEq_equal_flags $thmId),
                  inducedForbidLE_move_term_left_iff]))
          return true
        else
          return false
      else if hasFlagConst lhs then
        -- lhs is a plain flag term: move it directly
        evalTactic (← `(tactic| first | rw [forbidLEWith_move_term_left_iff] | rw [inducedForbidLE_move_term_left_iff]))
        return true
      else
        return false

/-- Drive `stepReduceDownwardFlagMul` to a fixpoint (bounded by `fuel`). If no
step ever made progress, fail with a diagnostic describing the goal shape;
otherwise stop once no further progress is possible. -/
private partial def runReduceDownwardFlagMul
    (fuel : Nat := 16384) : TacticM Unit := do
  -- Iterative (not recursive) fixpoint loop: each reduction step rewrites one
  -- summand, and a size-6 SOS needs thousands of steps. A monadic self-recursion
  -- is NOT tail-call optimized through `bind`, so it grows the native stack one
  -- frame per step and overflows it (server crash) on the larger examples. The
  -- `for` loop runs in constant stack.
  let mut steps : Nat := 0
  for _ in [0:fuel] do
    let progressed ← stepReduceDownwardFlagMul
    if !progressed then
      break
    steps := steps + 1
  if steps = fuel then
    throwError "reduce_downward_flagmul: fuel exhausted"
  if steps = 0 then
    withMainContext do
        let goal   ← getMainGoal
        let target ← goal.getType
        let args   := target.getAppArgs
        if args.size < 2 then
          throwError m!"reduce_downward_flagmul: target has too few args: {target}"
        let lhs      := args[args.size - 2]!.consumeMData
        let add?     := getAddArgs? lhs
        let down?    := stripDownward? lhs
        let smulOnHead? := match add? with
          | some (h, _) =>
              match stripDownward? h.consumeMData with
              | some inner => getSmulArgs? inner.consumeMData
              | none => none
          | none => none
        throwError m!"reduce_downward_flagmul made no progress. lhs={lhs}; addDetected={add?.isSome}; downwardDetected={down?.isSome}; smulOnHeadDetected={smulOnHead?.isSome}"

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
