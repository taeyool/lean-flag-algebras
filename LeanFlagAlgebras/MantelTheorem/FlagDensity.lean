import «LeanFlagAlgebras».MantelTheorem.FlagDefs
import «LeanFlagAlgebras».Compute.SubgraphListDensity

open FlagAlgebras
open LabeledSubgraph
open Classical
open Compute

namespace MantelTheorem

/- single flag densities -/

@[simp]
theorem flagDensity_K2_O3
    : flagDensity₁ K2_flag O3_flag = 0
  := by
  rw [← K2_eq, ← O3_eq, flagDensity₁_eq]
  native_decide

@[simp]
theorem flagDensity_K2_E3
    : flagDensity₁ K2_flag E3_flag = 1 / 3
  := by
  rw [← K2_eq, ← E3_eq, flagDensity₁_eq]
  native_decide

@[simp]
theorem flagDensity_K2_P3
    : flagDensity₁ K2_flag P3_flag = 2 / 3
  := by
  rw [← K2_eq, ← P3_eq, flagDensity₁_eq]
  native_decide

@[simp]
theorem flagDensity_K2_K3
    : flagDensity₁ K2_flag K3_flag = 1
  := by
  rw [← K2_eq, ← K3_eq, flagDensity₁_eq]
  native_decide


/- flag pair densities -/

@[simp]
theorem flagDensity_O2₁_O2₁_O3₁
    : flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1
  := by
  rw [← O2₁_eq, ← O3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_O3₁
    : flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← O3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_O3₁
    : flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0
  := by
  rw [← K2₁_eq, ← O3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁
    : flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0
  := by
  rw [← O2₁_eq, ← E3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁
    : flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← E3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁
    : flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0
  := by
  rw [← K2₁_eq, ← E3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁'
    : flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1
  := by
  rw [← O2₁_eq, ← E3₁'_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁'
    : flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← E3₁'_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁'
    : flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  rw [← K2₁_eq, ← E3₁'_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁
    : flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0
  := by
  rw [← O2₁_eq, ← P3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁
    : flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← P3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁
    : flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1
  := by
  rw [← K2₁_eq, ← P3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁'
    : flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0
  := by
  rw [← O2₁_eq, ← P3₁'_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁'
    : flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← P3₁'_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁'
    : flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0
  := by
  rw [← K2₁_eq, ← P3₁'_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_K3₁
    : flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0
  := by
  rw [← O2₁_eq, ← K3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_K3₁
    : flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← K3₁_eq, flagDensity₂_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_K3₁
    : flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1
  := by
  rw [← K2₁_eq, ← K3₁_eq, flagDensity₂_eq]
  native_decide

end MantelTheorem
