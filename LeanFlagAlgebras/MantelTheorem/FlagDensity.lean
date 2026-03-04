import «LeanFlagAlgebras».MantelTheorem.FlagDef
import «LeanFlagAlgebras».FlagAlgebra.Compute.FlagDensity

open FlagAlgebras
open FlagAlgebras.Compute

namespace MantelTheorem

/- single flag densities -/

@[simp]
theorem flagDensity_K2_O3
    : flagDensity₁ K2_flag O3_flag = 0
  := by
  dsimp [K2_flag, O3_flag, Flag_2_0_0_1, Flag_3_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
theorem flagDensity_K2_E3
    : flagDensity₁ K2_flag E3_flag = 1 / 3
  := by
  dsimp [K2_flag, E3_flag, Flag_2_0_0_1, Flag_3_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
theorem flagDensity_K2_P3
    : flagDensity₁ K2_flag P3_flag = 2 / 3
  := by
  dsimp [K2_flag, P3_flag, Flag_2_0_0_1, Flag_3_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
theorem flagDensity_K2_K3
    : flagDensity₁ K2_flag K3_flag = 1
  := by
  dsimp [K2_flag, K3_flag, Flag_2_0_0_1, Flag_3_0_0_3]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide


/- flag pair densities -/

@[simp]
theorem flagDensity_O2₁_O2₁_O3₁
    : flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1
  := by
  dsimp [O2₁_flag, O3₁_flag, Flag_2_1_0_0, Flag_3_1_0_0]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_O3₁
    : flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, O3₁_flag, Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_0]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_O3₁
    : flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0
  := by
  dsimp [K2₁_flag, O3₁_flag, Flag_2_1_0_1, Flag_3_1_0_0]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁
    : flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0
  := by
  dsimp [O2₁_flag, E3₁_flag, Flag_2_1_0_0, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁
    : flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2
  := by
  dsimp [O2₁_flag, K2₁_flag, E3₁_flag, Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁
    : flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0
  := by
  dsimp [K2₁_flag, E3₁_flag, Flag_2_1_0_1, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁'
    : flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1
  := by
  dsimp [O2₁_flag, E3₁'_flag, Flag_2_1_0_0, Flag_3_1_0_2]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁'
    : flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, E3₁'_flag, Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_2]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁'
    : flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  dsimp [K2₁_flag, E3₁'_flag, Flag_2_1_0_1, Flag_3_1_0_2]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁
    : flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0
  := by
  dsimp [O2₁_flag, P3₁_flag, Flag_2_1_0_0, Flag_3_1_0_3]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁
    : flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, P3₁_flag, Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_3]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁
    : flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1
  := by
  dsimp [K2₁_flag, P3₁_flag, Flag_2_1_0_1, Flag_3_1_0_3]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁'
    : flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0
  := by
  dsimp [O2₁_flag, P3₁'_flag, Flag_2_1_0_0, Flag_3_1_0_4]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁'
    : flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2
  := by
  dsimp [O2₁_flag, K2₁_flag, P3₁'_flag, Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_4]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁'
    : flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0
  := by
  dsimp [K2₁_flag, P3₁'_flag, Flag_2_1_0_1, Flag_3_1_0_4]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_K3₁
    : flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0
  := by
  dsimp [O2₁_flag, K3₁_flag, Flag_2_1_0_0, Flag_3_1_0_5]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_K3₁
    : flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, K3₁_flag, Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_5]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_K3₁
    : flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1
  := by
  dsimp [K2₁_flag, K3₁_flag, Flag_2_1_0_1, Flag_3_1_0_5]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

end MantelTheorem
