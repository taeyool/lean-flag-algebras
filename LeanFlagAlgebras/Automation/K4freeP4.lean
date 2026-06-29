import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Automation.Basic
import LeanFlagAlgebras.Automation.FlagMulReduce
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Automation.FlagSumSort

/-! # Automation.K4freeP4 — P₄ density bound in K₄-free graphs

Per-problem density-bound proof built on the Automation layer. The headline
result `K4_free_P4_density_upper_bound` shows that for K₄-free graphs the path
`P₄` (4-vertex path) density is at most `32/9`:

  `P4_density ≤ᵢ[K4.toFinFlag] (32 / 9 : ℝ) • (1 : FlagAlgebra ∅ₜ)`.

The proof assembles a sum-of-squares certificate from three squared flag
combinations `f₁, f₂, f₃` and discharges the resulting `inducedForbidLE` goal with the
Automation tactics (`reduce_downward_flagmul`, `expand_one_at`, `flag_nonneg`). It is
the `r = 3` instance of the more general `CompleteGraphFreeP4` result.
-/

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph

namespace K4freeP4

-- Locally generate the flags this example needs (formerly from the global
-- `Flags/FlagDef.lean`): the empty-typed underlying flags, the forbidden graph, and
-- the σ-typed pattern/host flags. Flag generation comes first, so the density and
-- multiplication theorem generators below resolve to these local constants.
generate_empty_typed_flags 3
generate_empty_typed_flags 4
generate_complete_graph 4 10
generate_flags 3 2 0
generate_flags 3 2 1
generate_flags 4 2 0
generate_flags 4 2 1

generate_forbid_density_theorems 4 K4
generate_flag_pair_density_theorems 3 4 2 0 K4
generate_forbid_mul_theorems 3 4 2 0 K4
generate_flag_pair_density_theorems 3 4 2 1 K4
generate_forbid_mul_theorems 3 4 2 1 K4

/-- The `P₄` (4-vertex path) density, expressed in the basis of 4-vertex graph
densities (the K₄ term `FlagAlgebra_4_0_0_10` is omitted because it vanishes for
K₄-free graphs). -/
noncomputable def P4_density : FlagAlgebra ∅ₜ :=
  1 • FlagAlgebra_4_0_0_6
  + 2 • FlagAlgebra_4_0_0_7
  + 4 • FlagAlgebra_4_0_0_8
  + 6 • FlagAlgebra_4_0_0_9

/-- First SOS certificate term: a σ₁-type (no-edge label) squared flag
combination, hence non-negative. -/
noncomputable def f₁ : FlagAlgebra ∅ₜ :=
  ⟦(2 • FlagAlgebra_3_2_0_0 - 1 • FlagAlgebra_3_2_0_3) ^ 2⟧₀

/-- Second SOS certificate term: a σ₂-type (edge label) squared flag
combination, hence non-negative. -/
noncomputable def f₂ : FlagAlgebra ∅ₜ :=
  ⟦(1 • FlagAlgebra_3_2_1_1 - 1 • FlagAlgebra_3_2_1_2) ^ 2⟧₀

/-- Third SOS certificate term: another σ₂-type squared flag combination, hence
non-negative. -/
noncomputable def f₃ : FlagAlgebra ∅ₜ :=
  ⟦(1 • FlagAlgebra_3_2_1_1 + 1 • FlagAlgebra_3_2_1_2 - 2 • FlagAlgebra_3_2_1_3) ^ 2⟧₀

/-- `f₁` is non-negative (a downward-projected square). -/
lemma f₁_nonneg : 0 ≤ f₁ := by
  dsimp only [f₁]
  rw [pow_two]
  exact square_downward_nonneg _

/-- `f₂` is non-negative (a downward-projected square). -/
lemma f₂_nonneg : 0 ≤ f₂ := by
  dsimp only [f₂]
  rw [pow_two]
  exact square_downward_nonneg _

/-- `f₃` is non-negative (a downward-projected square). -/
lemma f₃_nonneg : 0 ≤ f₃ := by
  dsimp only [f₃]
  rw [pow_two]
  exact square_downward_nonneg _

/-- **K₄-free `P₄` density bound.** In any K₄-free graph the `P₄` density is at
most `32/9`. Proved by adding the non-negative SOS terms `(8/9)·f₁ + 5·f₂ +
(35/9)·f₃` and reducing the resulting flag-algebra inequality with the Automation
tactics. -/
theorem K4_free_P4_density_upper_bound
    : P4_density ≤ᵢ[K4.toFinFlag] (32 / 9 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have h : P4_density ≤ᵢ[K4.toFinFlag]
      P4_density + (8 / 9 : ℝ) • f₁ + (5 : ℝ) • f₂ + (35 / 9 : ℝ) • f₃ := by
    apply inducedForbidLE_of_le
    have h₁ : 0 ≤ (8 / 9 : ℝ) • f₁ := nonneg_smul_nonneg_geq_zero (by norm_num) f₁_nonneg
    have h₂ : 0 ≤ (5 : ℝ) • f₂ := nonneg_smul_nonneg_geq_zero (by norm_num) f₂_nonneg
    have h₃ : 0 ≤ (35 / 9 : ℝ) • f₃ := nonneg_smul_nonneg_geq_zero (by norm_num) f₃_nonneg
    calc P4_density
        ≤ P4_density + (8 / 9 : ℝ) • f₁ := le_add_of_nonneg_right h₁
      _ ≤ P4_density + (8 / 9 : ℝ) • f₁ + (5 : ℝ) • f₂ := le_add_of_nonneg_right h₂
      _ ≤ P4_density + (8 / 9 : ℝ) • f₁ + (5 : ℝ) • f₂ + (35 / 9 : ℝ) • f₃ := le_add_of_nonneg_right h₃

  apply inducedForbidLE_trans h
  apply inducedForbidLE_trans_inducedForbidEq_right ?_  (inducedForbidEq_smul (inducedForbidEq_symm (one_inducedForbidEq_forbidExpand_one K4.toFinFlag 4)))

  dsimp [P4_density, f₁, f₂, f₃]
  simp only [pow_two, add_mul, mul_add, sub_mul, mul_sub, smul_mul_smul_comm]
  simp only [← downward_smul, smul_add, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [downward_add, downward_sub]
  simp only [sub_eq_add_neg, neg_add, neg_neg]
  simp only [add_assoc, ← downward_neg, ← neg_smul]
  reduce_downward_flagmul
  simp only [downward_add, downward_smul]
  simp [-one_smul]
  expand_one_at 4
  rw [← one_smul ℝ (FlagAlgebra_4_0_0_6)]
  flagsum_ac_sort_rhs_pipeline
  apply inducedForbidLE_of_le
  flag_nonneg

end K4freeP4
