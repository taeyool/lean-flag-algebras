import LeanFlagAlgebras.Forbid.Basic

/-! # API.ReduceFlagMul — the `reduce_downward_flagmul` tactic

Part of the API automation layer. This module defines the single custom tactic
`reduce_downward_flagmul`, which iteratively eliminates the
`downward (c • (A * B))` summands on the left-hand side of a `forbidLE` goal by
rewriting each flag product `A * B` with its precomputed `flagMul_*` expansion
theorem and moving the rewritten term onto the right-hand side. Plain flag
summands (no `downward` wrapper) are moved directly. See the detailed `/-! -/`
block below for the exact rewrite pattern; the file also contains the private
`Expr`-traversal helpers that locate `Flag_*` / `FlagAlgebra_*` constants and
resolve the corresponding `flagMul_*` theorem name.
-/

open FlagAlgebras Forbid
open Lean Elab Tactic Meta

namespace FlagAlgebras.API

/-!
`reduce_downward_flagmul` automates the rewriting pattern shown in the example
just below.  Given a goal of the form

```
  downward (c₁ • (A₁ * B₁)) + downward (c₂ • (A₂ * B₂)) + ... + downward (cₙ • (Aₙ * Bₙ))
    ≤[F_forbid] rhs
```

it repeatedly looks at the head term of the left-hand side (after right-
associating the addition with `simp only [add_assoc]`), looks up the
corresponding `flagMul_<A>_<B>` theorem from the constants used in the head
term, and rewrites the head using

```
  Forbid.forbidLE_rw_left_add_right (downward_forbidEq_equal_flags
    (forbidEq_smul flagMul_<A>_<B>))
  forbidLE_move_add_left_iff
```

For the final (right-most) summand it instead uses

```
  forbidLE_rw_left (downward_forbidEq_equal_flags (forbidEq_smul flagMul_<A>_<B>))
  forbidLE_move_term_left_iff
```

The implementation closely mirrors the `reduce_flagmul` tactic in
`ErdosPentagon/Lemmas.lean`, except that it operates on `forbidLE`-goals whose
summands are wrapped in `downward` and uses the corresponding `forbidLE_*`
lemmas.
-/

/-- The final component of a `Name`, as a string (helper for name matching). -/
private def lastNamePartLE (nm : Name) : String :=
  match nm with
  | .anonymous => ""
  | .str _ s => s
  | .num _ n => toString n

/-- Find the first `FlagAlgebra_*` constant name occurring anywhere in `e`. -/
private partial def findFlagAlgebraConstLE? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if (lastNamePartLE nm).startsWith "FlagAlgebra_" then some nm else none
  | .app f x =>
      match findFlagAlgebraConstLE? f with
      | some nm => some nm
      | none => findFlagAlgebraConstLE? x
  | .lam _ _ b _ => findFlagAlgebraConstLE? b
  | .forallE _ _ b _ => findFlagAlgebraConstLE? b
  | .letE _ _ v b _ =>
      match findFlagAlgebraConstLE? v with
      | some nm => some nm
      | none => findFlagAlgebraConstLE? b
  | .mdata _ b => findFlagAlgebraConstLE? b
  | .proj _ _ b => findFlagAlgebraConstLE? b
  | _ => none

/-- Find the first `Flag_*` constant name occurring anywhere in `e`. -/
private partial def findFlagConstLE? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if (lastNamePartLE nm).startsWith "Flag_" then some nm else none
  | .app f x =>
      match findFlagConstLE? f with
      | some nm => some nm
      | none => findFlagConstLE? x
  | .lam _ _ b _ => findFlagConstLE? b
  | .forallE _ _ b _ => findFlagConstLE? b
  | .letE _ _ v b _ =>
      match findFlagConstLE? v with
      | some nm => some nm
      | none => findFlagConstLE? b
  | .mdata _ b => findFlagConstLE? b
  | .proj _ _ b => findFlagConstLE? b
  | _ => none

/-- Extract the two arguments of a binary application `(.app (.app _ a) b)`. -/
private def getBinAppArgsLE? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app (.app _ a) b => some (a, b)
  | _ => none

/-- If `e` is an addition `x + y`, return its two operands. -/
private def getAddArgsLE? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``Add.add) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

/-- If `e` is a scalar multiplication `c • x`, return `(c, x)`. Returns `none`
for any other shape (including ordinary multiplication `x * y`, which has the
same `.app f x` skeleton and was previously mis-matched here). -/
private def getSmulArgsLE? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HSMul.hSMul || fn.isConstOf ``SMul.smul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

/-- If `e` is a multiplication `x * y`, return its two operands. -/
private def getMulArgsLE? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HMul.hMul || fn.isConstOf ``Mul.mul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    getBinAppArgsLE? e

/-- Strip an outer `FlagAlgebras.downward` application, returning its argument. -/
private def stripDownwardLE? (e : Expr) : Option Expr :=
  if e.isAppOf ``FlagAlgebras.downward then
    let args := e.getAppArgs
    if args.size >= 1 then some args[args.size - 1]! else none
  else none

private def flagToFlagAlgebraLastPartLE (s : String) : String :=
  if s.startsWith "Flag_" then
    "FlagAlgebra_" ++ s.drop 5
  else
    s

/-- Given `mulTerm = A * B`, search the environment for a theorem named
`flagMul_<A>_<B>` (or its reverse).  The lookup mirrors the strategy used by
`reduce_flagmul` in `ErdosPentagon/Lemmas.lean`.

`curNs` is typically the current namespace at the call site, used as a
fallback when the flag constants and the `flagMul_*` theorems live in
different namespaces (e.g. flag constants are at the root but the
`load_mul_theorems` command was issued inside a user namespace). -/
private def mkFlagMulThmNameLE? (mulTerm : Expr) (curNs : Name) : MetaM (Option Name) := do
  let some (fExpr, gExpr) := getMulArgsLE? mulTerm | return none
  let fNm? := findFlagAlgebraConstLE? fExpr
  let gNm? := findFlagAlgebraConstLE? gExpr
  let fFlag? := findFlagConstLE? fExpr
  let gFlag? := findFlagConstLE? gExpr
  let some fNm := fNm?.orElse (fun _ => fFlag?) | return none
  let some gNm := gNm?.orElse (fun _ => gFlag?) | return none
  let env ← getEnv
  let fLast := if fNm?.isSome then lastNamePartLE fNm
               else flagToFlagAlgebraLastPartLE (lastNamePartLE fNm)
  let gLast := if gNm?.isSome then lastNamePartLE gNm
               else flagToFlagAlgebraLastPartLE (lastNamePartLE gNm)
  let thmStrFG := s!"flagMul_{fLast}_{gLast}"
  let thmStrGF := s!"flagMul_{gLast}_{fLast}"
  let epNs := Name.mkSimple "ErdosPentagon"
  let mantelNs := Name.mkSimple "MantelTheorem"
  let cands := [
    Name.str fNm.getPrefix thmStrFG,
    Name.str fNm.getPrefix thmStrGF,
    Name.str curNs thmStrFG,
    Name.str curNs thmStrGF,
    Name.str epNs thmStrFG,
    Name.str epNs thmStrGF,
    Name.str mantelNs thmStrFG,
    Name.str mantelNs thmStrGF,
    Name.mkSimple thmStrFG,
    Name.mkSimple thmStrGF
  ]
  for cand in cands do
    if env.constants.contains cand then
      return some cand
  return none

/-- Returns `true` when `e` contains a `FlagAlgebra_*` or `Flag_*` constant
(i.e. it is a plain flag term rather than a `downward` wrapper). -/
private def hasFlagConstLE (e : Expr) : Bool :=
  (findFlagAlgebraConstLE? e).isSome || (findFlagConstLE? e).isSome

/-- Perform a single reduction step.  Returns `true` when progress was made.

Three kinds of head terms inside a `downward (...)` wrapper are handled:
* `downward (c • (A * B))` — smul-wrapped product. Look up the `flagMul_*`
  theorem and rewrite via `forbidEq_smul`.
* `downward (A * B)` — bare product (no smul). Same lookup, but the rewrite
  drops the `forbidEq_smul` wrapper. This branch catches terms whose `1 • _`
  coefficient was simplified away by an earlier `simp` step.
* plain flag term (contains a `FlagAlgebra_*` / `Flag_*` constant but is not
  wrapped in `downward`) — move directly with `forbidLE_move_add_left_iff` /
  `forbidLE_move_term_left_iff` without any rewriting. -/
private def stepReduceDownwardFlagMul : TacticM Bool :=
  withMainContext do
    let curNs ← getCurrNamespace
    let goal ← getMainGoal
    let target ← goal.getType
    let args := target.getAppArgs
    if args.size < 2 then
      return false
    let lhs := args[args.size - 2]!.consumeMData
    if let some (head, _rest) := getAddArgsLE? lhs then
      -- non-final case: head is the leftmost summand
      let head := head.consumeMData
      if let some downInner := stripDownwardLE? head then
        let downInner := downInner.consumeMData
        if let some (_c, mulTerm) := getSmulArgsLE? downInner then
          -- (a) head = downward (c • (A * B))
          let some thmName ← mkFlagMulThmNameLE? mulTerm curNs
            | do
                let fNm? := findFlagAlgebraConstLE? mulTerm |>.orElse (fun _ => findFlagConstLE? mulTerm)
                throwError m!"reduce_downward_flagmul (smul branch): could not find flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            rw [Forbid.forbidLE_rw_left_add_right
                  (downward_forbidEq_equal_flags (forbidEq_smul (c := _) $thmId)),
                forbidLE_move_add_left_iff]))
          return true
        else if (getMulArgsLE? downInner).isSome then
          -- (b) head = downward (A * B) — no smul wrapper
          let some thmName ← mkFlagMulThmNameLE? downInner curNs
            | do
                let fNm? := findFlagAlgebraConstLE? downInner |>.orElse (fun _ => findFlagConstLE? downInner)
                throwError m!"reduce_downward_flagmul (bare-mul branch): could not find flagMul theorem for mulTerm={downInner}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            rw [Forbid.forbidLE_rw_left_add_right
                  (downward_forbidEq_equal_flags $thmId),
                forbidLE_move_add_left_iff]))
          return true
        else
          return false
      else if hasFlagConstLE head then
        -- head is a plain flag term: move it directly
        evalTactic (← `(tactic| rw [forbidLE_move_add_left_iff]))
        return true
      else
        return false
    else
      -- terminal case: lhs itself is a single term
      if let some downInner := stripDownwardLE? lhs then
        let downInner := downInner.consumeMData
        if let some (_c, mulTerm) := getSmulArgsLE? downInner then
          -- (a) lhs = downward (c • (A * B))
          let some thmName ← mkFlagMulThmNameLE? mulTerm curNs
            | do
                let fNm? := findFlagAlgebraConstLE? mulTerm |>.orElse (fun _ => findFlagConstLE? mulTerm)
                throwError m!"reduce_downward_flagmul (terminal smul branch): could not find flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            rw [forbidLE_rw_left
                  (downward_forbidEq_equal_flags (forbidEq_smul (c := _) $thmId)),
                forbidLE_move_term_left_iff]))
          return true
        else if (getMulArgsLE? downInner).isSome then
          -- (b) lhs = downward (A * B) — no smul wrapper
          let some thmName ← mkFlagMulThmNameLE? downInner curNs
            | do
                let fNm? := findFlagAlgebraConstLE? downInner |>.orElse (fun _ => findFlagConstLE? downInner)
                throwError m!"reduce_downward_flagmul (terminal bare-mul branch): could not find flagMul theorem for mulTerm={downInner}; detectedConst={fNm?.getD Name.anonymous}"
          let thmId : TSyntax `term := mkIdent thmName
          evalTactic (← `(tactic|
            rw [forbidLE_rw_left
                  (downward_forbidEq_equal_flags $thmId),
                forbidLE_move_term_left_iff]))
          return true
        else
          return false
      else if hasFlagConstLE lhs then
        -- lhs is a plain flag term: move it directly
        evalTactic (← `(tactic| rw [forbidLE_move_term_left_iff]))
        return true
      else
        return false

/-- Drive `stepReduceDownwardFlagMul` to a fixpoint (bounded by `fuel`). If no
step ever made progress, fail with a diagnostic describing the goal shape;
otherwise stop once no further progress is possible. -/
private partial def runReduceDownwardFlagMul
    (fuel : Nat := 256) (steps : Nat := 0) : TacticM Unit := do
  if fuel = 0 then
    throwError "reduce_downward_flagmul: fuel exhausted"
  let progressed ← stepReduceDownwardFlagMul
  if progressed then
    runReduceDownwardFlagMul (fuel - 1) (steps + 1)
  else
    if steps = 0 then
      withMainContext do
        let goal ← getMainGoal
        let target ← goal.getType
        let args := target.getAppArgs
        if args.size < 2 then
          throwError m!"reduce_downward_flagmul: target has too few args: {target}"
        let lhs := args[args.size - 2]!.consumeMData
        let add? := getAddArgsLE? lhs
        let down? := stripDownwardLE? lhs
        let smulOnHead? := match add? with
          | some (h, _) =>
              match stripDownwardLE? h.consumeMData with
              | some inner => getSmulArgsLE? inner.consumeMData
              | none => none
          | none => none
        throwError m!"reduce_downward_flagmul made no progress. lhs={lhs}; addDetected={add?.isSome}; downwardDetected={down?.isSome}; smulOnHeadDetected={smulOnHead?.isSome}"
    else
      pure ()

/-- Repeatedly rewrite the left-hand side of a `forbidLE` goal whose summands
have the form `downward (c • (A * B))`, replacing each `A * B` with the
expansion supplied by the corresponding `flagMul_*` theorem and moving the
already-rewritten terms onto the right.

Before iterating, this tactic right-associates the sum with
`simp only [add_assoc]`. -/
elab "reduce_downward_flagmul" : tactic => do
  evalTactic (← `(tactic| try simp only [downward_add, add_assoc]))
  runReduceDownwardFlagMul

end FlagAlgebras.API
