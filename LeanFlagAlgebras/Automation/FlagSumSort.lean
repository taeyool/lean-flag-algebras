import Mathlib.Tactic
import Mathlib.Tactic.Conv

/-! # `flagsum_sort` / `flagsum_ac_sort` tactics: canonical ordering of additive expressions

Shared custom tactics that reorder the terms of a sum into a canonical order keyed by the
trailing numeric index of each base atom. `flagsum_sort`/`flagsum_sort_lhs`/`flagsum_sort_rhs`
normalize linear combinations (`coeff • base`), while the `flagsum_ac_sort*` family does
add-AC reordering only; `*_pipeline` variants bundle arithmetic-normalization simp passes.
Used to line up flag sums on both sides of (in)equalities so they can be compared term-by-term.
-/

open Lean Elab Tactic Meta

namespace FlagAlgebras.Automation

/-- Linear term represented as `(base, coeff)` meaning `coeff • base`. -/
abbrev LinTerm := Expr × Expr

/-! ## 1) Common Definitions -/

private def parseTrailingNat? (s : String) : Option Nat :=
  let revDigits := s.toList.reverse.takeWhile Char.isDigit
  if revDigits.isEmpty then
    none
  else
    (String.ofList revDigits.reverse).toNat?

private def baseIndexKey (e : Expr) : MetaM (Nat × String) := do
  let e := e.consumeMData
  let pp ← ppExpr e
  let keyStr := pp.pretty
  let idx?
    :=
      match e.getAppFn.consumeMData with
      | Expr.const nm _ => parseTrailingNat? nm.toString
      | _ => parseTrailingNat? keyStr
  pure (idx?.getD 1000000000, keyStr)

private def getBinaryOpArgs? (opName : Name) (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then none else some (args[args.size - 2]!, args[args.size - 1]!)

private def getAddArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HAdd.hAdd e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``Add.add e

private def getSubArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HSub.hSub e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``Sub.sub e

private def getSmulArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HSMul.hSMul e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``SMul.smul e

private def getUnaryOpArg? (opName : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.isEmpty then none else some args[args.size - 1]!

private def getNegArg? (e : Expr) : Option Expr :=
  getUnaryOpArg? ``Neg.neg e

private def insertSortedBy {α}
    (goesBefore : α → α → Bool)
    (item : α)
    (sorted : Array α)
    : Array α :=
  Id.run do
    let mut inserted := false
    let mut next : Array α := #[]
    for old in sorted do
      if !inserted && goesBefore item old then
        next := next.push item
        inserted := true
      next := next.push old
    if !inserted then
      next := next.push item
    return next

private def getEqSides (target : Expr) : TacticM (Expr × Expr) := do
  let t := target.consumeMData
  if !t.getAppFn.isConstOf ``Eq then
    throwError "normalize_flagsum: goal must be an equality"
  let args := t.getAppArgs
  if args.size != 3 then
    throwError "normalize_flagsum: malformed equality target"
  pure (args[1]!, args[2]!)

private def replaceGoalUsingLhsEq
    (goal : MVarId)
    (lhsSorted rhs hLhs : Expr)
    : TacticM Unit := do
  let newGoalType ← mkEq lhsSorted rhs
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType
  let proof ← mkEqTrans hLhs newGoal
  goal.assign proof
  replaceMainGoal [newGoal.mvarId!]

private def replaceGoalUsingRhsEq
    (goal : MVarId)
    (lhs rhsSorted hRhs : Expr)
    : TacticM Unit := do
  let newGoalType ← mkEq lhs rhsSorted
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType
  let proof ← mkEqTrans newGoal (← mkEqSymm hRhs)
  goal.assign proof
  replaceMainGoal [newGoal.mvarId!]

private def withTimer (label : String) (act : TacticM Unit) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  act
  let t1 ← IO.monoMsNow
  logInfo m!"[timer] {label}: {t1 - t0} ms"

/-! ## 2) Definitions for `sort` and `sort` Implementation -/

private def mkOneCoeff : TacticM Expr := do
  Lean.Elab.Term.elabTerm (← `(term| (1 : ℝ))) none

private partial def flattenLinearTerms (e : Expr) : TacticM (Array LinTerm) := do
  let e0 := e.consumeMData
  let e ←
    match e0 with
    | Expr.const .. =>
        match (← delta? e0) with
        | some e' => pure e'
        | none => pure e0
    | _ => pure e0
  if let some (a, b) := getAddArgs? e then
    return (← flattenLinearTerms a) ++ (← flattenLinearTerms b)
  if let some (a, b) := getSubArgs? e then
    let left ← flattenLinearTerms a
    let right ← flattenLinearTerms b
    let rightNeg ← right.mapM fun (base, coeff) => do
      let negCoeff ← mkAppM ``Neg.neg #[coeff]
      pure (base, negCoeff)
    return left ++ rightNeg
  if let some a := getNegArg? e then
    let terms ← flattenLinearTerms a
    let negTerms ← terms.mapM fun (base, coeff) => do
      let negCoeff ← mkAppM ``Neg.neg #[coeff]
      pure (base, negCoeff)
    return negTerms
  if let some (coeff, base) := getSmulArgs? e then
    return #[(base, coeff)]
  return #[(e, (← mkOneCoeff))]

private structure KeyedTerm where
  idx : Nat
  key : String
  base : Expr
  coeff : Expr

private def insertSortedByKey
    (item : KeyedTerm)
    (sorted : Array KeyedTerm)
    : Array KeyedTerm :=
  insertSortedBy
    (fun a b => a.idx < b.idx || (a.idx = b.idx && a.key < b.key))
    item
    sorted

private def sortLinearTermsByIndex (terms : Array LinTerm) : TacticM (Array LinTerm) := do
  let keyed ← terms.mapM fun (base, coeff) => do
    let (idx, key) ← baseIndexKey base
    pure ({ idx := idx, key := key, base := base, coeff := coeff } : KeyedTerm)
  let mut sorted : Array KeyedTerm := #[]
  for item in keyed do
    sorted := insertSortedByKey item sorted
  pure <| sorted.map fun t => (t.base, t.coeff)

private def rebuildLinearExpr (terms : Array LinTerm) : TacticM Expr := do
  let smulTerms ← terms.mapM fun (base, coeff) => mkAppM ``HSMul.hSMul #[coeff, base]
  match smulTerms.toList with
  | [] => throwError "rebuildLinearExpr: empty term list"
  | t :: ts => ts.foldlM (fun acc nxt => mkAppM ``HAdd.hAdd #[acc, nxt]) t

private def normalizeLinearExpr (e : Expr) : TacticM Expr := do
  let flat ← flattenLinearTerms e
  let sorted ← sortLinearTermsByIndex flat
  rebuildLinearExpr sorted

private def proveEqByAC (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  match lhs.consumeMData with
  | Expr.const nm _ =>
      let id := mkIdent nm
      evalTactic (← `(tactic| try (delta $id)))
  | _ => pure ()
  match rhs.consumeMData with
  | Expr.const nm _ =>
      let id := mkIdent nm
      evalTactic (← `(tactic| try (delta $id)))
  | _ => pure ()
  evalTactic (← `(tactic|
    (try dsimp;
     try (simp [sub_eq_add_neg, smul_eq_mul,
                one_smul, neg_one_smul, neg_smul,
                add_assoc, add_left_comm, add_comm]);
     first
      | ac_rfl
      | try abel_nf
      | try ring_nf)))
  let remaining ← getGoals
  if !remaining.isEmpty then
    throwError m!"proveEqByAC: failed to close normalization side-goal\noriginal lhs: {lhs}\nnormalized: {rhs}"
  setGoals savedGoals
  instantiateMVars mvar

/-- Debug helper: logs the normalized (index-sorted) forms of both sides of an equality
goal without changing the goal. -/
elab "preview_flagsum_nf" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (lhs, rhs) ← getEqSides target
    let lhsNorm ← normalizeLinearExpr lhs
    let rhsNorm ← normalizeLinearExpr rhs
    logInfo m!"[flagsum-nf] LHS: {lhsNorm}"
    logInfo m!"[flagsum-nf] RHS: {rhsNorm}"

/-- Shared implementation: normalizes the current conv focus. -/
private def sortNormalizeConv : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (focus, rhs) ← getEqSides target
    let focusSorted ← normalizeLinearExpr focus
    let h ← proveEqByAC focus focusSorted
    replaceGoalUsingLhsEq goal focusSorted rhs h

/-- Normalize the current conv focus. Use inside `conv_lhs`, `conv_rhs`, or any `conv` block. -/
elab "sort_here" : conv => sortNormalizeConv

/-- Sort only the left side. Works on any relation (=, ≤, <, …). -/
elab "flagsum_sort_lhs" : tactic => do
  evalTactic (← `(tactic| conv_lhs => sort_here))

/-- Sort only the right side. Works on any relation (=, ≤, <, …). -/
elab "flagsum_sort_rhs" : tactic => do
  evalTactic (← `(tactic| conv_rhs => sort_here))

/-- Sort both sides. Works on any relation (=, ≤, <, …). -/
elab "flagsum_sort" : tactic => do
  evalTactic (← `(tactic| flagsum_sort_lhs; flagsum_sort_rhs))

/-- `conv` entry: normalize the current focus (alias for `sort_here`). -/
elab "sort_at" : conv => sortNormalizeConv

/-- Timed `conv` entry for `sort_at` (logs elapsed ms). -/
elab "sort_at_timer" : conv => do
  withTimer "sort_at" sortNormalizeConv

/-! ## 3) Definitions for `ac_sort` and `ac_sort` Implementation -/

private partial def flattenAddTerms (e : Expr) : Array Expr :=
  let e := e.consumeMData
  match getAddArgs? e with
  | some (a, b) => (flattenAddTerms a) ++ (flattenAddTerms b)
  | none => #[e]

private def addTermKey (e : Expr) : MetaM (Nat × String) := do
  let e := e.consumeMData
  match getSmulArgs? e with
  | some (_, base) => baseIndexKey base
  | none => baseIndexKey e

private def sortAddTermsByKey (terms : Array Expr) : MetaM (Array Expr) := do
  let keyed ← terms.mapM fun t => do
    let (idx, key) ← addTermKey t
    pure (idx, key, t)
  let mut sorted : Array (Nat × String × Expr) := #[]
  for item in keyed do
    sorted := insertSortedBy
      (fun a b => a.1 < b.1 || (a.1 = b.1 && a.2.1 < b.2.1))
      item
      sorted
  pure <| sorted.map fun (_, _, t) => t

private partial def mkRightAssocAdd (terms : List Expr) : MetaM Expr := do
  match terms with
  | [] => throwError "mkRightAssocAdd: empty term list"
  | [t] => pure t
  | t :: ts => do
      let rest ← mkRightAssocAdd ts
      mkAppM ``HAdd.hAdd #[t, rest]

private def rebuildAddExprRightAssoc (terms : Array Expr) : MetaM Expr :=
  mkRightAssocAdd terms.toList

private def normalizeByAddPermutation (e : Expr) : MetaM Expr := do
  let terms := flattenAddTerms e
  let sorted ← sortAddTermsByKey terms
  rebuildAddExprRightAssoc sorted

private def proveEqByAddAC (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| first | ac_rfl | simp [add_assoc, add_left_comm, add_comm]))
  let remaining ← getGoals
  if !remaining.isEmpty then
    throwError m!"proveEqByAddAC: failed to close side-goal\noriginal lhs: {lhs}\nsorted lhs: {rhs}"
  setGoals savedGoals
  instantiateMVars mvar

/-- Shared implementation: normalizes the current conv focus using add-AC only. -/
private def acSortNormalizeConv : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (focus, rhs) ← getEqSides target
    let focusSorted ← normalizeByAddPermutation focus
    let h ← proveEqByAddAC focus focusSorted
    replaceGoalUsingLhsEq goal focusSorted rhs h

/-- Normalize the current conv focus using add-AC. Use inside `conv_lhs`, `conv_rhs`, etc. -/
elab "ac_sort_here" : conv => acSortNormalizeConv

/-- Swap-based sort on LHS. Works on any relation (=, ≤, <, …). -/
elab "ac_sort_lhs" : tactic => do
  evalTactic (← `(tactic| conv_lhs => ac_sort_here))

/-- Swap-based sort on RHS. Works on any relation (=, ≤, <, …). -/
elab "ac_sort_rhs" : tactic => do
  evalTactic (← `(tactic| conv_rhs => ac_sort_here))

/-- Swap-based sort on both sides. Works on any relation (=, ≤, <, …). -/
elab "ac_sort" : tactic => do
  evalTactic (← `(tactic| ac_sort_lhs; ac_sort_rhs))

/-- `conv` entry: normalize current focus using add-AC (alias for `ac_sort_here`). -/
elab "ac_sort_at" : conv => acSortNormalizeConv

/-- Timed `conv` entry for `ac_sort_at` (logs elapsed ms). -/
elab "ac_sort_at_timer" : conv => do
  withTimer "ac_sort_at" acSortNormalizeConv

/--
Utility `conv` entry around `ac_sort_at`:
`norm_num; simp; ac_sort_at; simp only [← add_assoc, ← add_smul]; norm_num`.

Use this inside `conv` when you want to normalize arithmetic first and then
perform add-AC sorting on the focused expression.
-/
elab "ac_sort_at_pipeline" : conv => do
  -- `maxSteps` is bumped well above the default (100000): the `add_assoc` re-association is
  -- roughly quadratic in the number of summands, so a long RHS sum (large SDP blocks) otherwise
  -- trips `simp`'s "maximum number of steps exceeded" guard. This is a limit, not a loop.
  evalTactic (← `(tactic|
    (try (simp (config := { maxSteps := 10000000 }) only
      [neg_add, neg_neg, sub_eq_add_neg, ← neg_smul, add_assoc, smul_smul]))))
  acSortNormalizeConv
  evalTactic (← `(tactic|
    (try (simp (config := { maxSteps := 10000000 }) only [← add_assoc, ← add_smul]);
     try norm_num)))

/--
Run the common pipeline on the left side of an equality goal:
`conv_lhs => ac_sort_at_pipeline`.
-/
elab "flagsum_ac_sort_lhs_pipeline" : tactic =>
  do
    evalTactic (← `(tactic|
      (conv_lhs =>
         ac_sort_at_pipeline)))

/--
Run the common pipeline on the right side of an equality goal:
`conv_rhs => ac_sort_at_pipeline`.
-/
elab "flagsum_ac_sort_rhs_pipeline" : tactic =>
  do
    evalTactic (← `(tactic|
      (conv_rhs =>
         ac_sort_at_pipeline)))

/--
Run the common pipeline on both sides of an equality goal.
-/
elab "flagsum_ac_sort_pipeline" : tactic =>
  do
    evalTactic (← `(tactic|
      flagsum_ac_sort_lhs_pipeline;
      flagsum_ac_sort_rhs_pipeline))

end FlagAlgebras.Automation
