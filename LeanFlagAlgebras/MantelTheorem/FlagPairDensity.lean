import «LeanFlagAlgebras».SubflagDensity
import «LeanFlagAlgebras».MantelTheorem.FlagDefs

open FlagAlgebras

namespace MantelTheorem

/- the densities of each flag pair in O3₁ -/

@[simp]
theorem flagDensity_O2₁_O2₁_O3₁
    : flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_O3₁
    : flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_O3₁
    : flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0
  := by
  sorry

/- the densities of each flag pair in E3₁ -/

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁
    : flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁
    : flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁
    : flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0
  := by
  sorry

/- the densities of each flag pair in E3₁' -/

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁'
    : flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁'
    : flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁'
    : flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  sorry

/- the densities of each flag pair in P3₁ -/

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁
    : flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁
    : flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁
    : flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1
  := by
  sorry

/- the densities of each flag pair in P3₁' -/

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁'
    : flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁'
    : flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁'
    : flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0
  := by
  sorry

/- the densities of each flag pair in K3₁ -/

@[simp]
theorem flagDensity_O2₁_O2₁_K3₁
    : flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_K3₁
    : flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_K3₁
    : flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1
  := by
  sorry

end MantelTheorem
