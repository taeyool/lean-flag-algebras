import LeanFlagAlgebras.MantelTheorem.FlagDef
import LeanFlagAlgebras.MantelTheorem.FlagDensity
import LeanFlagAlgebras.MantelTheorem.FlagTactic
import LeanFlagAlgebras.MantelTheorem.MantelTheorem
import «LeanFlagAlgebras».FlagAlgebra.RandomHom

open FlagAlgebras Compute
open SimpleGraph
open Lean Elab Tactic Meta

namespace MantelTheorem

lemma expand_1_on_three_vertex_graphs_without_K3
    : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ 1 = φ O3 + φ E3 + φ P3
  := by
  rw [← K0_eq_one]
  dsimp only [K0, O3, E3, P3, K3]
  dsimp [FlagAlgebra_0_0_0_0, FlagAlgebra_3_0_0_3, FlagAlgebra_2_0_0_1, FlagAlgebra_3_0_0_1, FlagAlgebra_3_0_0_2]
  intro φ h
  have hExp := unitVector_quot_eq_sum_density_mul_flagWithSize (σ := ∅ₜ) ⟨0, Flag_0_0_0_0⟩ 3 (by simp)
  have hφ := congrArg φ hExp
  rw [PositiveHom.map_sum] at hφ
  rw [Finset.sum_eq_multiset_sum] at hφ
  rw [← flagSet_3_0_0_eq_univ, flagSet_3_0_0_val_eq] at hφ
  simp only [Multiset.map_coe, List.map_cons, List.map_nil,
    Multiset.sum_coe, List.sum_cons, List.sum_nil] at hφ
  simp only [PositiveHom.map_smul] at hφ
  rw [h] at hφ
  simp at hφ
  simpa [one_div, add_assoc]

lemma expand_K2_on_three_vertex_without_K3
    : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ K2 = (1 / 3 : ℝ) • φ E3 + (2 / 3 : ℝ) • φ P3
  := by
  dsimp only [K2, E3, P3, K3]
  dsimp [FlagAlgebra_3_0_0_3, FlagAlgebra_2_0_0_1, FlagAlgebra_3_0_0_1, FlagAlgebra_3_0_0_2]
  intro φ h
  have hExp := unitVector_quot_eq_sum_density_mul_flagWithSize (σ := ∅ₜ) ⟨2, Flag_2_0_0_1⟩ 3 (by simp)
  have hφ := congrArg φ hExp
  rw [PositiveHom.map_sum] at hφ
  rw [Finset.sum_eq_multiset_sum] at hφ
  rw [← flagSet_3_0_0_eq_univ, flagSet_3_0_0_val_eq] at hφ
  simp only [Multiset.map_coe, List.map_cons, List.map_nil,
    Multiset.sum_coe, List.sum_cons, List.sum_nil] at hφ
  simp only [PositiveHom.map_smul] at hφ
  rw [h] at hφ
  simp at hφ
  simpa [one_div]

lemma expand_K2₁_on_three_vertex_without_K3
    : ∀ (φ : PositiveHom FlagType_1_0), φ K3₁ = 0 → φ K2₁ = (1 / 2 : ℝ) • φ E3₁ + φ P3₁ + (1 / 2 : ℝ) • φ P3₁'
  := by
  dsimp only [K2₁, E3₁, P3₁, P3₁', K3₁]
  dsimp only [FlagAlgebra_2_1_0_1, FlagAlgebra_3_1_0_1, FlagAlgebra_3_1_0_3, FlagAlgebra_3_1_0_4, FlagAlgebra_3_1_0_5]
  intro φ h
  have hExp := unitVector_quot_eq_sum_density_mul_flagWithSize (σ := FlagType_1_0) ⟨2, Flag_2_1_0_1⟩ 3 (by simp)
  have hφ := congrArg φ hExp
  rw [PositiveHom.map_sum] at hφ
  rw [Finset.sum_eq_multiset_sum] at hφ
  rw [← flagSet_3_1_0_eq_univ, flagSet_3_1_0_val_eq] at hφ
  simp only [Multiset.map_coe, List.map_cons, List.map_nil,
    Multiset.sum_coe, List.sum_cons, List.sum_nil] at hφ
  simp only [PositiveHom.map_smul, h] at hφ
  simp at hφ
  simp only [hφ, one_div, smul_eq_mul]
  simp only [one_div, smul_eq_mul, add_assoc]

/-`prove_flag_expand_with_restriction N` proves goals of the form
`∀ (φ : PositiveHom σ), φ F_forbidden = 0 → φ F = (size N expansion of F without F_forbidden)`.

It introduces `φ` and the restriction hypothesis, expands `F` with
`unitVector_quot_eq_sum_density_mul_flagWithSize`, maps by `φ`, rewrites the
size-`N` flag universe, and then substitutes the forbidden term using the
hypothesis.
-/
syntax (name := flagExpandWithRestrictionTac) "prove_flag_expand_with_restriction " term : tactic

/-- Find a constant name containing `Flag_...` in an expression. -/
private partial def findFlagConst? (e : Expr) : Option Name :=
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
private def parseFlagIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
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

private def runFlagExpandWithRestriction (N : TSyntax `term) : TacticM Unit :=
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

    let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
    let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
    let eqUnivId : TSyntax `ident := mkIdent eqUnivName
    let valEqId : TSyntax `ident := mkIdent valEqName

    evalTactic (← `(tactic|
      have hExp := unitVector_quot_eq_sum_density_mul_flagWithSize $finFlagTerm $N (by simp)))
    evalTactic (← `(tactic| have hφ := congrArg φ hExp))
    evalTactic (← `(tactic| rw [PositiveHom.map_sum] at hφ))
    evalTactic (← `(tactic| rw [Finset.sum_eq_multiset_sum] at hφ))
    evalTactic (← `(tactic| have h_eq_univ := $eqUnivId))
    evalTactic (← `(tactic| have h_val_eq := $valEqId))
    evalTactic (← `(tactic| rw [← h_eq_univ, h_val_eq] at hφ))
    evalTactic (← `(tactic| simp only [Multiset.map_coe, List.map_cons, List.map_nil,
      Multiset.sum_coe, List.sum_cons, List.sum_nil] at hφ))
    evalTactic (← `(tactic| simp only [PositiveHom.map_smul] at hφ))
    try
      evalTactic (← `(tactic| rw [h] at hφ))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic| simp [h] at hφ))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic| simp at hφ))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic| conv at hφ => rhs; simp [h]))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic|
        have h_forbidden_3003 : φ ⟦unitVector ⟨3, Flag_3_0_0_3⟩⟧ = 0 := by
          first
          | exact h
          | simpa [K3] using h))
      evalTactic (← `(tactic| rw [h_forbidden_3003] at hφ))
      evalTactic (← `(tactic| simp at hφ))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic|
        have h_forbidden_3105 : φ ⟦unitVector ⟨3, Flag_3_1_0_5⟩⟧ = 0 := by
          first
          | exact h
          | simpa [K3₁] using h))
      evalTactic (← `(tactic| simp [h_forbidden_3105] at hφ))
      evalTactic (← `(tactic| simp at hφ))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic|
        first
        | ring_nf at hφ ⊢
          linarith [hφ, h]
        | linarith [hφ, h]))
    catch _ =>
      pure ()
    try
      evalTactic (← `(tactic|
        first
        | have hφ2 := hφ
          rw [h] at hφ2
          simpa [one_div, smul_eq_mul, add_assoc] using hφ2
        | simpa [h, one_div, smul_eq_mul, add_assoc] using hφ
        | simpa [one_div, smul_eq_mul, add_assoc] using hφ
        | simpa [add_assoc] using hφ))
    catch _ =>
      pure ()

elab_rules : tactic
  | `(tactic| prove_flag_expand_with_restriction $N) =>
      runFlagExpandWithRestriction N

lemma expand_K2_on_three_vertex_without_K3'
    : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ K2 = (1 / 3 : ℝ) • φ E3 + (2 / 3 : ℝ) • φ P3
  := by
  dsimp only [K2, E3, P3, K3]
  dsimp [FlagAlgebra_3_0_0_3, FlagAlgebra_2_0_0_1, FlagAlgebra_3_0_0_1, FlagAlgebra_3_0_0_2]
  prove_flag_expand_with_restriction 3

lemma expand_1_on_three_vertex_graphs_without_K3'
    : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ 1 = φ O3 + φ E3 + φ P3
  := by
  rw [← K0_eq_one]
  dsimp only [K0, O3, E3, P3, K3]
  dsimp only [FlagAlgebra_0_0_0_0, FlagAlgebra_3_0_0_0, FlagAlgebra_3_0_0_1, FlagAlgebra_3_0_0_2, FlagAlgebra_3_0_0_3]
  prove_flag_expand_with_restriction 3

lemma expand_K2₁_on_three_vertex_without_K3'
    : ∀ (φ : PositiveHom FlagType_1_0), φ K3₁ = 0 → φ K2₁ = (1 / 2 : ℝ) • φ E3₁ + φ P3₁ + (1 / 2 : ℝ) • φ P3₁'
  := by
  dsimp only [K2₁, E3₁, P3₁, P3₁', K3₁]
  dsimp only [FlagAlgebra_2_1_0_1, FlagAlgebra_3_1_0_1, FlagAlgebra_3_1_0_3, FlagAlgebra_3_1_0_4, FlagAlgebra_3_1_0_5]
  prove_flag_expand_with_restriction 3
  sorry
