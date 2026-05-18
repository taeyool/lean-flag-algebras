import LeanFlagAlgebras.MantelTheorem.FlagDef
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity

/-! # Mantel's theorem: flag density tables

Pre-computed single-flag densities (`flagDensity₁`) and flag-pair densities
(`flagDensity₂`) for all the small flags appearing in the Mantel's theorem
proof. Every theorem is closed by `native_decide` and tagged `@[simp]` so the
later algebraic arguments can rewrite densities to concrete rational numbers
automatically. -/

open FlagAlgebras
open FlagAlgebras.Compute

namespace MantelTheorem

/- single flag densities -/

/- flagDensity₁ K0_flag K1_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_0_0_0_0_Flag_1_0_0_0
    : flagDensity₁ Flag_0_0_0_0 Flag_1_0_0_0 = 1
  := by
  dsimp [Flag_0_0_0_0, Flag_1_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K0_flag O3_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_0_0_0_0_Flag_3_0_0_0
    : flagDensity₁ Flag_0_0_0_0 Flag_3_0_0_0 = 1
  := by
  dsimp [Flag_0_0_0_0, Flag_3_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K0_flag E3_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_0_0_0_0_Flag_3_0_0_1
    : flagDensity₁ Flag_0_0_0_0 Flag_3_0_0_1 = 1
  := by
  dsimp [Flag_0_0_0_0, Flag_3_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K0_flag P3_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_0_0_0_0_Flag_3_0_0_2
    : flagDensity₁ Flag_0_0_0_0 Flag_3_0_0_2 = 1
  := by
  dsimp [Flag_0_0_0_0, Flag_3_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K0_flag K3_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_0_0_0_0_Flag_3_0_0_3
    : flagDensity₁ Flag_0_0_0_0 Flag_3_0_0_3 = 1
  := by
  dsimp [Flag_0_0_0_0, Flag_3_0_0_3]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K2_flag O3_flag = 0 -/
@[simp]
theorem flagDensity₁_Flag_2_0_0_1_Flag_3_0_0_0
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_0 = 0
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K2_flag E3_flag = 1 / 3 -/
@[simp]
theorem flagDensity₁_Flag_2_0_0_1_Flag_3_0_0_1
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_1 = 1 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K2_flag P3_flag = 2 / 3 -/
@[simp]
theorem flagDensity₁_Flag_2_0_0_1_Flag_3_0_0_2
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_2 = 2 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K2_flag K3_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_2_0_0_1_Flag_3_0_0_3
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_3 = 1
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_3]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/- flagDensity₁ K2₁_flag O3₁_flag = 0 -/
@[simp]
theorem flagDensity₁_Flag_2_1_0_1_Flag_3_1_0_0
    : flagDensity₁ Flag_2_1_0_1 Flag_3_1_0_0 = 0
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_0]
  rw [flagDensity₁_eq_sym2FlagDensity₁]
  native_decide

/- flagDensity₁ K2₁_flag E3₁_flag = 1 / 2 -/
@[simp]
theorem flagDensity₁_Flag_2_1_0_1_Flag_3_1_0_1
    : flagDensity₁ Flag_2_1_0_1 Flag_3_1_0_1 = 1 / 2
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_1]
  rw [flagDensity₁_eq_sym2FlagDensity₁]
  native_decide

/- flagDensity₁ K2₁_flag E3₁'_flag = 0 -/
@[simp]
theorem flagDensity₁_Flag_2_1_0_1_Flag_3_1_0_2
    : flagDensity₁ Flag_2_1_0_1 Flag_3_1_0_2 = 0
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_2]
  rw [flagDensity₁_eq_sym2FlagDensity₁]
  native_decide

/- flagDensity₁ K2₁_flag P3₁_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_2_1_0_1_Flag_3_1_0_3
    : flagDensity₁ Flag_2_1_0_1 Flag_3_1_0_3 = 1
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_3]
  rw [flagDensity₁_eq_sym2FlagDensity₁]
  native_decide

/- flagDensity₁ K2₁_flag P3₁'_flag = 1 / 2 -/
@[simp]
theorem flagDensity₁_Flag_2_1_0_1_Flag_3_1_0_4
    : flagDensity₁ Flag_2_1_0_1 Flag_3_1_0_4 = 1 / 2
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_4]
  rw [flagDensity₁_eq_sym2FlagDensity₁]
  native_decide

/- flagDensity₁ K2₁_flag K3₁_flag = 1 -/
@[simp]
theorem flagDensity₁_Flag_2_1_0_1_Flag_3_1_0_5
    : flagDensity₁ Flag_2_1_0_1 Flag_3_1_0_5 = 1
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_5]
  rw [flagDensity₁_eq_sym2FlagDensity₁]
  native_decide


/- flag pair densities -/

/- flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_0
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_0 = 1
  := by
  dsimp [Flag_2_1_0_0, Flag_3_1_0_0]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_0
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_0 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_0]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_1_Flag_2_1_0_1_Flag_3_1_0_0
    : flagDensity₂ Flag_2_1_0_1 Flag_2_1_0_1 Flag_3_1_0_0 = 0
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_0]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_1
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_1 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_1
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_1 = 1 / 2
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_1_Flag_2_1_0_1_Flag_3_1_0_1
    : flagDensity₂ Flag_2_1_0_1 Flag_2_1_0_1 Flag_3_1_0_1 = 0
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_2
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_2 = 1
  := by
  dsimp [Flag_2_1_0_0, Flag_3_1_0_2]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_2
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_2 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_2]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_1_Flag_2_1_0_1_Flag_3_1_0_2
    : flagDensity₂ Flag_2_1_0_1 Flag_2_1_0_1 Flag_3_1_0_2 = 0
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_2]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_3
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_3 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_3_1_0_3]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_3
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_3 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_3]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_1_Flag_2_1_0_1_Flag_3_1_0_3
    : flagDensity₂ Flag_2_1_0_1 Flag_2_1_0_1 Flag_3_1_0_3 = 1
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_3]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_4
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_4 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_3_1_0_4]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_4
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_4 = 1 / 2
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_4]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_1_Flag_2_1_0_1_Flag_3_1_0_4
    : flagDensity₂ Flag_2_1_0_1 Flag_2_1_0_1 Flag_3_1_0_4 = 0
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_4]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_5
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_5 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_3_1_0_5]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_5
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_5 = 0
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_5]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

/- flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1 -/
@[simp]
theorem flagDensity₂_Flag_2_1_0_1_Flag_2_1_0_1_Flag_3_1_0_5
    : flagDensity₂ Flag_2_1_0_1 Flag_2_1_0_1 Flag_3_1_0_5 = 1
  := by
  dsimp [Flag_2_1_0_1, Flag_3_1_0_5]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

end MantelTheorem
