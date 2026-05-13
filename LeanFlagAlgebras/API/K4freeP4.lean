import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.ReduceFlagMul
import LeanFlagAlgebras.Flags.Densities.MulLoader
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.Utils.SortTactic

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph

namespace K4freeP4

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_4_K4_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K4.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K4.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K4.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K4.json"

noncomputable def P4_density : FlagAlgebra ∅ₜ :=
  1 • FlagAlgebra_4_0_0_6
  + 2 • FlagAlgebra_4_0_0_7
  + 4 • FlagAlgebra_4_0_0_8
  + 6 • FlagAlgebra_4_0_0_9

noncomputable def f₁ : FlagAlgebra ∅ₜ :=
  ⟦(2 • FlagAlgebra_3_2_0_0 - 1 • FlagAlgebra_3_2_0_3) ^ 2⟧₀

noncomputable def f₂ : FlagAlgebra ∅ₜ :=
  ⟦(1 • FlagAlgebra_3_2_1_1 - 1 • FlagAlgebra_3_2_1_2) ^ 2⟧₀

noncomputable def f₃ : FlagAlgebra ∅ₜ :=
  ⟦(1 • FlagAlgebra_3_2_1_1 + 1 • FlagAlgebra_3_2_1_2 - 2 • FlagAlgebra_3_2_1_3) ^ 2⟧₀

lemma f₁_nonneg : 0 ≤ f₁ := by
  dsimp only [f₁]
  rw [pow_two]
  exact square_downward_nonneg _

lemma f₂_nonneg : 0 ≤ f₂ := by
  dsimp only [f₂]
  rw [pow_two]
  exact square_downward_nonneg _

lemma f₃_nonneg : 0 ≤ f₃ := by
  dsimp only [f₃]
  rw [pow_two]
  exact square_downward_nonneg _

generate_unitVector_lemmas 4 11

theorem K4_free_P4_density_upper_bound
    : P4_density ≤[K4.toFinFlag] (32 / 9 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have h : P4_density ≤[K4.toFinFlag]
      P4_density + (8 / 9 : ℝ) • f₁ + (5 : ℝ) • f₂ + (35 / 9 : ℝ) • f₃ := by
    apply forbidLE_of_le
    have h₁ : 0 ≤ (8 / 9 : ℝ) • f₁ := nonneg_smul_nonneg_geq_zero (by norm_num) f₁_nonneg
    have h₂ : 0 ≤ (5 : ℝ) • f₂ := nonneg_smul_nonneg_geq_zero (by norm_num) f₂_nonneg
    have h₃ : 0 ≤ (35 / 9 : ℝ) • f₃ := nonneg_smul_nonneg_geq_zero (by norm_num) f₃_nonneg
    calc P4_density
        ≤ P4_density + (8 / 9 : ℝ) • f₁ := le_add_of_nonneg_right h₁
      _ ≤ P4_density + (8 / 9 : ℝ) • f₁ + (5 : ℝ) • f₂ := le_add_of_nonneg_right h₂
      _ ≤ P4_density + (8 / 9 : ℝ) • f₁ + (5 : ℝ) • f₂ + (35 / 9 : ℝ) • f₃ := le_add_of_nonneg_right h₃

  apply forbidLE_trans h
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_expand K4.toFinFlag 4)))

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
  ac_sort_rhs_pipeline
  apply forbidLE_of_le
  flag_nonneg

end K4freeP4
