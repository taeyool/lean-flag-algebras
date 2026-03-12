import Mathlib.Tactic
import LeanFlagAlgebras.MantelTheorem.FlagDef
import LeanFlagAlgebras.MantelTheorem.FlagDensity
import LeanFlagAlgebras.FlagAlgebra.PositiveHom

open Lean Elab Tactic Meta

namespace MantelTheorem

/-- Find a constant name containing `FlagAlgebra_...` in an expression. -/
partial def findFlagAlgebraConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if nm.toString.contains "FlagAlgebra_" then some nm else none
  | .app f x =>
      match findFlagAlgebraConst? f with
      | some nm => some nm
      | none => findFlagAlgebraConst? x
  | .lam _ _ b _ => findFlagAlgebraConst? b
  | .forallE _ _ b _ => findFlagAlgebraConst? b
  | .letE _ _ v b _ =>
      match findFlagAlgebraConst? v with
      | some nm => some nm
      | none => findFlagAlgebraConst? b
  | .mdata _ b => findFlagAlgebraConst? b
  | .proj _ _ b => findFlagAlgebraConst? b
  | _ => none

/-- Parse `(n,k,m,i)` from names like `...FlagAlgebra_n_k_m_i`. -/
def parseFlagAlgebraIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
  let s := nm.toString
  let tail ← match s.splitOn "FlagAlgebra_" with
    | _ :: t :: _ => some t
    | _ => none
  let parts := tail.splitOn "_"
  let (nStr, kStr, mStr, iStr) ← match parts with
    | nStr :: kStr :: mStr :: iStr :: _ => some (nStr, kStr, mStr, iStr)
    | _ => none
  let n ← String.toNat? nStr
  let k ← String.toNat? kStr
  let m ← String.toNat? mStr
  let i ← String.toNat? iStr
  pure (n, k, m, i)

/-- Find a constant name containing `Flag_...` in an expression. -/
partial def findFlagConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
    if nm.toString.contains "Flag_" then some nm else none
  | .app f x =>
    match findFlagConst? f with
    | some nm => some nm
    | none => findFlagConst? x
  | .lam _ _ b _ => findFlagConst? b
  | .forallE _ _ b _ => findFlagConst? b
  | .letE _ _ v b _ =>
    match findFlagConst? v with
    | some nm => some nm
    | none => findFlagConst? b
  | .mdata _ b => findFlagConst? b
  | .proj _ _ b => findFlagConst? b
  | _ => none

/-- Parse `(n,k,m,i)` from names like `...Flag_n_k_m_i`. -/
def parseFlagIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
  let s := nm.toString
  let tail ← match s.splitOn "Flag_" with
    | _ :: t :: _ => some t
    | _ => none
  let parts := tail.splitOn "_"
  let (nStr, kStr, mStr, iStr) ← match parts with
    | nStr :: kStr :: mStr :: iStr :: _ => some (nStr, kStr, mStr, iStr)
    | _ => none
  let n ← String.toNat? nStr
  let k ← String.toNat? kStr
  let m ← String.toNat? mStr
  let i ← String.toNat? iStr
  pure (n, k, m, i)

/-
`prove_flag_expand_with_restriction N` proves goals of the form
`∀ (φ : PositiveHom σ), φ F_forbidden = 0 → φ F = (size N expansion of F without F_forbidden)`.

It introduces `φ` and the restriction hypothesis, expands `F` with
`unitVector_quot_eq_sum_density_mul_flagWithSize`, maps by `φ`, rewrites the
size-`N` flag universe, and then substitutes the forbidden term using the
hypothesis.
-/
syntax (name := flagExpandWithRestrictionTac) "prove_flag_expand_with_restriction " term : tactic

def runFlagExpandWithRestriction (N : TSyntax `term) : TacticM Unit :=
  withMainContext do
    let nExpr ← elabTerm N (some (mkConst ``Nat))
    let some nVal ← (Meta.evalNat nExpr).run
      | throwError "Could not evaluate N to a natural number in `prove_flag_expand_with_restriction`."

    evalTactic (← `(tactic| intro φ h))

    let goalTy ← (← getMainGoal).getType
    let some (_, lhs, _) := goalTy.eq?
      | throwError "Goal after intro must be an equality."

    let parsed : Option (Nat × Nat × Nat × Nat) :=
      match findFlagConst? lhs with
      | some flagConst => parseFlagIndices? flagConst
      | none =>
          match findFlagAlgebraConst? lhs with
          | some lhsConst => parseFlagAlgebraIndices? lhsConst
          | none => none
    let some (lhsN, kVal, mVal, iVal) := parsed
      | throwError "Could not find/parse `Flag_*` (or `FlagAlgebra_*`) indices in the target equality."

    let flagName : Name := Name.mkSimple s!"Flag_{lhsN}_{kVal}_{mVal}_{iVal}"
    let flagId : TSyntax `term := mkIdent flagName
    let lhsNStx : TSyntax `term := Syntax.mkNumLit (toString lhsN)
    let finFlagTerm ← `(term| ⟨$lhsNStx, $flagId⟩)
    let sigmaTerm : TSyntax `term ←
      if kVal = 0 && mVal = 0 then
        `(term| ∅ₜ)
      else
        pure <| mkIdent (Name.mkSimple s!"FlagType_{kVal}_{mVal}")

    let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
    let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
    let eqUnivId : TSyntax `ident := mkIdent eqUnivName
    let valEqId : TSyntax `ident := mkIdent valEqName

    evalTactic (← `(tactic|
      have hExp := FlagAlgebras.unitVector_quot_eq_sum_density_mul_flagWithSize (σ := $sigmaTerm) $finFlagTerm $N (by simp)))
    evalTactic (← `(tactic| have hφ := congrArg φ hExp))
    evalTactic (← `(tactic| rw [FlagAlgebras.PositiveHom.map_sum] at hφ))
    evalTactic (← `(tactic| rw [Finset.sum_eq_multiset_sum] at hφ))
    evalTactic (← `(tactic| have h_eq_univ := $eqUnivId))
    evalTactic (← `(tactic| have h_val_eq := $valEqId))
    evalTactic (← `(tactic| rw [← h_eq_univ, h_val_eq] at hφ))
    evalTactic (← `(tactic| simp only [Multiset.map_coe, List.map_cons, List.map_nil,
      Multiset.sum_coe, List.sum_cons, List.sum_nil] at hφ))
    evalTactic (← `(tactic| simp only [FlagAlgebras.PositiveHom.map_smul] at hφ))
    evalTactic (← `(tactic| rw [h] at hφ))
    evalTactic (← `(tactic| simp at hφ))
    evalTactic (← `(tactic| simpa [one_div, add_assoc] using hφ))

elab_rules : tactic
  | `(tactic| prove_flag_expand_with_restriction $N) =>
      runFlagExpandWithRestriction N

/-- Collect all constants containing `FlagAlgebra_...` in an expression tree. -/
partial def collectFlagAlgebraConsts (e : Expr) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .const nm _ =>
      if nm.toString.contains "FlagAlgebra_" then acc.push nm else acc
  | .app f x =>
      let acc' := collectFlagAlgebraConsts f acc
      collectFlagAlgebraConsts x acc'
  | .lam _ _ b _ => collectFlagAlgebraConsts b acc
  | .forallE _ _ b _ => collectFlagAlgebraConsts b acc
  | .letE _ _ v b _ =>
      let acc' := collectFlagAlgebraConsts v acc
      collectFlagAlgebraConsts b acc'
  | .mdata _ b => collectFlagAlgebraConsts b acc
  | .proj _ _ b => collectFlagAlgebraConsts b acc
  | _ => acc

/--
`prove_flag_expand N` proves goals of the form
`(one loaded flag algebra basis element) = (its size N expansion)`.

It automatically:
1) moves to `FlagVector` via `Quotient.sound`,
2) infers the LHS flag and applies `unitVector_eqv_densityFlagSum`,
3) unfolds `densityFlagSum`,
4) rewrites using generated `flagSet_{N}_{k}_{m}_eq_univ` and `flagSet_{N}_{k}_{m}_val_eq`,
5) closes by normalization (`ring_nf`), so RHS add-order differences are tolerated.
-/
syntax (name := flagUnitExpandTac) "prove_flag_expand " term : tactic

elab_rules : tactic
  | `(tactic| prove_flag_expand $N) => do
      withMainContext do
        if (← getGoals).isEmpty then
          pure ()

        let runIfGoals (stx : Syntax) : TacticM Unit := do
          unless (← getGoals).isEmpty do
            evalTactic stx

        let nExpr ← elabTerm N (some (mkConst ``Nat))
        let some nVal ← (Meta.evalNat nExpr).run
          | throwError "Could not evaluate N to a natural number in `prove_flag_expand`."

        let goalTy ← (← getMainGoal).getType
        let some (_, lhs, _) := goalTy.eq?
          | throwError "Goal must be an equality."

        let some lhsConst := findFlagAlgebraConst? lhs
          | throwError "Could not find a `FlagAlgebra_*` constant on the LHS."

        let some (lhsN, kVal, mVal, iVal) := parseFlagAlgebraIndices? lhsConst
          | throwError m!"Could not parse indices from LHS constant `{lhsConst}`."

        let flagName : Name := Name.mkSimple s!"Flag_{lhsN}_{kVal}_{mVal}_{iVal}"
        let flagId : TSyntax `term := mkIdent flagName
        let lhsNStx : TSyntax `term := Syntax.mkNumLit (toString lhsN)
        let finFlagTerm ← `(term| ⟨$lhsNStx, $flagId⟩)

        let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
        let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"

        runIfGoals (← `(tactic| apply Quotient.sound))
        runIfGoals (← `(tactic| dsimp))
        runIfGoals (← `(tactic|
          refine FlagAlgebras.flagVectorEqv.trans
            (FlagAlgebras.unitVector_eqv_densityFlagSum $finFlagTerm $N (by simp)) ?_))
        runIfGoals (← `(tactic| dsimp [FlagAlgebras.densityFlagSum]))

        let eqUnivId : TSyntax `ident := mkIdent eqUnivName
        let valEqId : TSyntax `ident := mkIdent valEqName
        runIfGoals (← `(tactic| have h_eq_univ := $eqUnivId))
        runIfGoals (← `(tactic| have h_val_eq := $valEqId))
        runIfGoals (← `(tactic| rw [Finset.sum_eq_multiset_sum, ← h_eq_univ]))
        runIfGoals (← `(tactic| simp [h_val_eq]))
        try
          runIfGoals (← `(tactic| ring_nf))
        catch _ =>
          pure ()
        try
          runIfGoals (← `(tactic| apply FlagAlgebras.flagVector_eq_eqv; ring_nf))
        catch _ =>
          pure ()
        try
          runIfGoals (← `(tactic| apply FlagAlgebras.flagVector_eq_eqv; simp [add_assoc, add_left_comm, add_comm]))
        catch _ =>
          pure ()

/--
`prove_flag_mul` proves goals of the shape
`(flag) * (flag) = (linear combination of flags)`.

It unfolds flag multiplication to a finite sum, rewrites by
`flagSet_{N}_{k}_{m}_eq_univ` and `flagSet_{N}_{k}_{m}_val_eq`, and closes by
algebraic normalization. The RHS add-order is handled up to associativity and
commutativity.
-/
syntax (name := flagMulTac) "prove_flag_mul" : tactic

elab_rules : tactic
  | `(tactic| prove_flag_mul) => do
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
        let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
        let eqUnivId : TSyntax `ident := mkIdent eqUnivName
        let valEqId : TSyntax `ident := mkIdent valEqName

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
          evalTactic (← `(tactic| apply flagVector_eq_eqv; ring_nf))
        catch _ =>
          pure ()
        try
          evalTactic (← `(tactic| apply flagVector_eq_eqv; simp [add_assoc, add_left_comm, add_comm]))
        catch _ =>
          pure ()

end MantelTheorem
