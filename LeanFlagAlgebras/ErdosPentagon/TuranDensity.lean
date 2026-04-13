import LeanFlagAlgebras.ErdosPentagon.ErdosPentagon

open FlagAlgebras Forbid

namespace ErdosPentagon

theorem ErdosPentagon_upperBound
    : generalizedTuranDensity K3 C5 ≤ 24 / 625
  :=
  generalizedTuranDensity_le_of_forbidLE (by norm_num) ErdosPentagon_flagAlgebra

theorem generalizedExtremalNumber_K3_C5_lowerBound
    (n : ℕ)
    : generalizedExtremalNumber n K3 C5 / n.choose 5 ≥ 24 / 625
  := by
  sorry

theorem ErdosPentagon_lowerBound
    : generalizedTuranDensity K3 C5 ≥ 24 / 625
  := by
  sorry

theorem ErdosPentagon
    : generalizedTuranDensity K3 C5 = 24 / 625
  := by
  apply le_antisymm
  · exact ErdosPentagon_upperBound
  · exact ErdosPentagon_lowerBound

end ErdosPentagon
