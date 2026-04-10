import LeanFlagAlgebras.ErdosPentagon.FlagMul

open FlagAlgebras Forbid
open Lean Elab Tactic Meta

/-- Linear term represented as `(base, coeff)` meaning `coeff • base`. -/
abbrev LinTerm := Expr × Expr

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

private partial def flattenLinearTerms (e : Expr) : MetaM (Array LinTerm) := do
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
  if let some (coeff, base) := getSmulArgs? e then
    return #[(base, coeff)]
  throwError m!"flattenLinearTerms: expected a linear combination of smul terms, got: {e}"

private structure KeyedTerm where
  idx : Nat
  key : String
  base : Expr
  coeff : Expr

private def insertSortedByKey
    (item : KeyedTerm)
    (sorted : Array KeyedTerm)
    : Array KeyedTerm :=
  Id.run do
    let mut inserted := false
    let mut next : Array KeyedTerm := #[]
    for old in sorted do
      let goesBefore := item.idx < old.idx || (item.idx = old.idx && item.key < old.key)
      if !inserted && goesBefore then
        next := next.push item
        inserted := true
      next := next.push old
    if !inserted then
      next := next.push item
    return next

private def sortLinearTermsByIndex (terms : Array LinTerm) : MetaM (Array LinTerm) := do
  let keyed ← terms.mapM fun (base, coeff) => do
    let (idx, key) ← baseIndexKey base
    pure ({ idx := idx, key := key, base := base, coeff := coeff } : KeyedTerm)
  let mut sorted : Array KeyedTerm := #[]
  for item in keyed do
    sorted := insertSortedByKey item sorted
  pure <| sorted.map fun t => (t.base, t.coeff)

private def rebuildLinearExpr (terms : Array LinTerm) : MetaM Expr := do
  let smulTerms ← terms.mapM fun (base, coeff) => mkAppM ``HSMul.hSMul #[coeff, base]
  match smulTerms.toList with
  | [] => throwError "rebuildLinearExpr: empty term list"
  | t :: ts => ts.foldlM (fun acc nxt => mkAppM ``HAdd.hAdd #[acc, nxt]) t

private def normalizeLinearExpr (e : Expr) : MetaM Expr := do
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
     try (simp [sub_eq_add_neg, rat_smul_eq_real_smul, smul_eq_mul, add_assoc, add_left_comm, add_comm]);
     try ring_nf)))
  let remaining ← getGoals
  if !remaining.isEmpty then
    throwError "proveEqByAC: failed to close normalization side-goal"
  setGoals savedGoals
  instantiateMVars mvar

private def getEqSides (target : Expr) : TacticM (Expr × Expr) := do
  let t := target.consumeMData
  if !t.getAppFn.isConstOf ``Eq then
    throwError "normalize_flagsum: goal must be an equality"
  let args := t.getAppArgs
  if args.size != 3 then
    throwError "normalize_flagsum: malformed equality target"
  pure (args[1]!, args[2]!)

elab "preview_flagsum_nf" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let args := target.getAppArgs
    if args.size < 2 then
      throwError "preview_flagsum_nf: target is not a binary relation"
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    let lhsNorm ← normalizeLinearExpr lhs
    let rhsNorm ← normalizeLinearExpr rhs
    logInfo m!"[flagsum-nf] LHS: {lhsNorm}"
    logInfo m!"[flagsum-nf] RHS: {rhsNorm}"

/--
Sort only the left side of a linear FlagAlgebra sum equality by index:
1) flattening nested additions/subtractions,
2) sorting by trailing index in names like `..._i`.

No like-term coefficient collection is performed here.

It turns a goal `lhs = rhs` into `lhs_sorted = rhs`.
-/
elab "sort_flagsum_lhs" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (lhs, rhs) ← getEqSides target
    let lhsSorted ← normalizeLinearExpr lhs
    let hLhs ← proveEqByAC lhs lhsSorted

    let newGoalType ← mkEq lhsSorted rhs
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType

    let proof ← mkEqTrans hLhs newGoal
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]

/-- Sort only the right side by index: `lhs = rhs` becomes `lhs = rhs_sorted`. -/
elab "sort_flagsum_rhs" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (lhs, rhs) ← getEqSides target
    let rhsSorted ← normalizeLinearExpr rhs
    let hRhs ← proveEqByAC rhs rhsSorted

    let newGoalType ← mkEq lhs rhsSorted
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType

    let proof ← mkEqTrans newGoal (← mkEqSymm hRhs)
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]

/-- Sort both sides by index: `lhs = rhs` becomes `lhs_sorted = rhs_sorted`. -/
elab "sort_flagsum" : tactic =>
  do
    evalTactic (← `(tactic| sort_flagsum_lhs; sort_flagsum_rhs))

set_option maxHeartbeats 0
example :
    (24 / 625 : ℝ) • FlagAlgebra_5_0_0_0 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_1 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_2 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_3 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_4 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_6 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_7 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_8 +
    ((24 / 625 : ℝ) • FlagAlgebra_5_0_0_10 +
    (-(19 / 1500 : ℝ) • FlagAlgebra_5_0_0_10 +
    (-(19 / 1500 : ℝ) • FlagAlgebra_5_0_0_10 +
    ((38 / 1875 : ℝ) • FlagAlgebra_5_0_0_10 +
    ((191 / 18750 : ℝ) • FlagAlgebra_5_0_0_10 +
    ((191 / 18750 : ℝ) • FlagAlgebra_5_0_0_10 +
    (-(192 / 3125 : ℝ) • FlagAlgebra_5_0_0_8 +
    (10 : ℝ) • FlagAlgebra_5_0_0_11)))))))))))))) =
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_0 +
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_1 +
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_2 +
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_3 +
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_4 +
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_6 +
      (24 / 625 : ℝ) • FlagAlgebra_5_0_0_7 +
      (-(72 / 3125) : ℝ) • FlagAlgebra_5_0_0_8 +
      (1007 / 18750 : ℝ) • FlagAlgebra_5_0_0_10 +
      (10 : ℝ) • FlagAlgebra_5_0_0_11
  := by
  sort_flagsum_lhs
  simp only [add_assoc, ← add_smul]
  norm_num
