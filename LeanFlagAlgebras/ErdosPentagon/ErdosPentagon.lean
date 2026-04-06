import LeanFlagAlgebras.ErdosPentagon.FlagDensity

open FlagAlgebras

namespace ErdosPentagon

example
    : flagQuadraticForm R_real Vᵣ ≥ 0
  :=
  flagQuadraticForm_nonneg R_real R_real_posSemidef Vᵣ

example
    : flagQuadraticForm R_real Vᵣ =[K3] sorry
  := by
  sorry

theorem ErdosPentagon
    : C5 ≤[K3] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end ErdosPentagon
