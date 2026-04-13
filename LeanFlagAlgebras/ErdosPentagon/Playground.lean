import LeanFlagAlgebras.ErdosPentagon.FlagMul
import Mathlib.Tactic.Conv

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

private def mkOneCoeffForBase (_base : Expr) : TacticM Expr := do
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
  return #[(e, (← mkOneCoeffForBase e))]

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
     try (simp [sub_eq_add_neg, rat_smul_eq_real_smul, smul_eq_mul,
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

private partial def flattenAddTerms (e : Expr) : Array Expr :=
  let e := e.consumeMData
  match getAddArgs? e with
  | some (a, b) => (flattenAddTerms a) ++ (flattenAddTerms b)
  | none => #[e]

private def splitSmulTerm? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  match getSmulArgs? e with
  | some (coeff, base) => some (coeff.consumeMData, base.consumeMData)
  | none => none

private def mkSmulTerm (coeff base : Expr) : MetaM Expr :=
  mkAppM ``HSMul.hSMul #[coeff, base]

private def collectAdjacentSortedTerms (terms : Array Expr) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for t in terms do
    if out.isEmpty then
      out := out.push t
    else
      let last := out[out.size - 1]!
      match splitSmulTerm? last, splitSmulTerm? t with
      | some (c₁, b₁), some (c₂, b₂) =>
          if b₁ == b₂ then
            let c ← mkAppM ``HAdd.hAdd #[c₁, c₂]
            let merged ← mkSmulTerm c b₁
            out := out.set! (out.size - 1) merged
          else
            out := out.push t
      | _, _ =>
          out := out.push t
  pure out

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
    let mut inserted := false
    let mut next : Array (Nat × String × Expr) := #[]
    for old in sorted do
      let itemIdx := item.1
      let itemKey := item.2.1
      let oldIdx := old.1
      let oldKey := old.2.1
      let goesBefore : Bool :=
        if itemIdx < oldIdx ∨ (itemIdx = oldIdx ∧ itemKey < oldKey) then true else false
      if !inserted && goesBefore then
        next := next.push item
        inserted := true
      next := next.push old
    if !inserted then
      next := next.push item
    sorted := next
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

private def normalizeBySortedAdjacentCollection (e : Expr) : MetaM Expr := do
  let terms := flattenAddTerms e
  let collected ← collectAdjacentSortedTerms terms
  rebuildAddExprRightAssoc collected

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

/--
Sort additive terms on the LHS by key using only add-commutativity/associativity
rewrites (`ac_rfl`), without coefficient algebra normalization.
-/
elab "sort_flagsum_lhs_by_swaps" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (lhs, rhs) ← getEqSides target
    let lhsSorted ← normalizeByAddPermutation lhs
    let hLhs ← proveEqByAddAC lhs lhsSorted

    let newGoalType ← mkEq lhsSorted rhs
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType
    let proof ← mkEqTrans hLhs newGoal
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]

/--
Collect adjacent like terms with a fast-path + legacy fallback.

Assumes additive terms are already sorted so equal bases are adjacent.
The fast-path tries direct head merging first, then falls back to the
same local rewrite pattern used by `collect_adjacent_flagsum`.
-/
syntax "collect_adjacent_sorted_flagsum_fast" : conv

macro_rules
  | `(conv| collect_adjacent_sorted_flagsum_fast) =>
      `(conv|
        repeat
          (first
            | (rw [collect_smul_same_head]; try norm_num)
            | (simp only [← add_assoc]
               try
                 (simp only [← neg_smul, ← add_smul]
                  norm_num)
               simp only [add_assoc]
               arg 2)))

/-- Tactic-mode wrapper: collect adjacent like terms on the goal LHS. -/
elab "collect_adjacent_sorted_flagsum_lhs" : tactic =>
  do
    evalTactic (← `(tactic| conv_lhs => collect_adjacent_sorted_flagsum_fast))

/-- `conv` entry for `sort_flagsum_lhs_by_swaps`. -/
elab "sort_flagsum_by_swaps_at" : conv =>
  do
    evalTactic (← `(tactic| sort_flagsum_lhs_by_swaps))

/-- Timed `conv` entry for `sort_flagsum_by_swaps_at` (logs elapsed ms). -/
elab "sort_flagsum_by_swaps_at_timer" : conv => do
  let t0 ← IO.monoMsNow
  evalTactic (← `(tactic| sort_flagsum_lhs_by_swaps))
  let t1 ← IO.monoMsNow
  logInfo m!"[timer] sort_flagsum_by_swaps_at: {t1 - t0} ms"

/-- `conv` entry for `collect_adjacent_sorted_flagsum_lhs`. -/
elab "collect_adjacent_sorted_flagsum_at" : conv =>
  do
    evalTactic (← `(conv| collect_adjacent_sorted_flagsum_fast))

/-- Timed `conv` entry for `collect_adjacent_sorted_flagsum_at` (logs elapsed ms). -/
elab "collect_adjacent_sorted_flagsum_at_timer" : conv => do
  let t0 ← IO.monoMsNow
  evalTactic (← `(conv| collect_adjacent_sorted_flagsum_fast))
  let t1 ← IO.monoMsNow
  logInfo m!"[timer] collect_adjacent_sorted_flagsum_at: {t1 - t0} ms"

/-- Backward-compatible typo alias for `sort_flagsum_by_swaps_at`. -/
elab "sort_flaghsum_by_swaps_at" : conv =>
  do
    evalTactic (← `(conv| sort_flagsum_by_swaps_at))

/--
`conv`-mode entry for `sort_flagsum_lhs`.

After navigating to a target subexpression with `conv`, run this to sort the
current focused expression by flag index.
-/
elab "sort_flagsum_at" : conv =>
  do
    evalTactic (← `(tactic| sort_flagsum_lhs))

/-- Backward-compatible alias for a common typo of `sort_flagsum_at`. -/
elab "sort_flaghsum_at" : conv =>
  do
    evalTactic (← `(conv| sort_flagsum_at))

set_option maxHeartbeats 0

/--
Collect adjacent like terms in a right-associated linear sum.

Use this inside `conv` via `collect_adjacent_flagsum` after focusing
on the subexpression you want to normalize.
-/
syntax "collect_adjacent_flagsum" : conv

macro_rules
  | `(conv| collect_adjacent_flagsum) =>
      `(conv|
        repeat
          (simp only [← add_assoc]
           try
             (simp only [← neg_smul, ← add_smul]
              norm_num)
           simp only [add_assoc]
           arg 2))

/-- Timed `conv` entry for `collect_adjacent_flagsum` (logs elapsed ms). -/
elab "collect_adjacent_flagsum_timer" : conv => do
  let t0 ← IO.monoMsNow
  evalTactic (← `(conv| collect_adjacent_flagsum))
  let t1 ← IO.monoMsNow
  logInfo m!"[timer] collect_adjacent_flagsum: {t1 - t0} ms"

-- NOTE:
-- A previous exploratory example using these tactics has been removed to keep
-- this module free of `sorry` so downstream imports can elaborate tactics.
