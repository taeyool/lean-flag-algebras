import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.ReduceFlagMul
import LeanFlagAlgebras.Flags.Densities.MulLoader
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.Utils.SortTactic

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph

namespace K4freeP4

load_k4_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_4_k4_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0.json"
load_k4_free_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1.json"
load_k4_free_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1.json"

#check flagMul_FlagAlgebra_3_2_0_0_FlagAlgebra_3_2_0_1
-- #check flagDensity₂_Flag_3_2_0_0_Flag_3_2_0_1_Flag_4_2_0_11

example : (FlagAlgebra_3_2_0_0 * FlagAlgebra_3_2_0_1 )=[K4.toFinFlag]
    (1 / 2) • FlagAlgebra_4_2_0_1 + (1 / 2) • FlagAlgebra_4_2_0_6
  := by
  apply forbidEq_trans
    (unitVector_quot_mul_forbidEq_sum K4.toFinFlag
      ⟨3, Flag_3_2_0_0⟩
      ⟨3, Flag_3_2_0_1⟩
      4
      (by rfl))
  rw [Finset.sum_eq_multiset_sum, ← flagSet_4_2_0_eq_univ]
  have hsetval := flagSet_4_2_0_val_eq
  simp [hsetval]
  sorry

noncomputable def P4_density : FlagAlgebra ∅ₜ :=
  1 • FlagAlgebra_4_0_0_0
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
  sorry

theorem K4_free_P4_density_upper_bound
    : P4_density ≤[K4.toFinFlag] (96 / 27 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have h : P4_density ≤[K4.toFinFlag] P4_density + f₁ + f₂ + f₃ := by
    sorry

  apply forbidLE_trans h
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_expand K4.toFinFlag 4)))

  dsimp [P4_density, f₁, f₂, f₃]
  simp only [pow_two, add_mul, mul_add, sub_mul, mul_sub, smul_mul_smul_comm]
  simp only [downward_add, downward_sub]
  norm_num

  expand_one_at 4
  sorry

end K4freeP4
