import LeanFlagAlgebras.ErdosPentagon.FlagMul

open FlagAlgebras

namespace ErdosPentagon

example
    : flagQuadraticForm R_real v₂ ≥ 0
  :=
  flagQuadraticForm_nonneg R_real R_real_posSemidef v₂

example
    : flagQuadraticForm R_real v₂ =[K3] sorry
  := by
  sorry

theorem ErdosPentagon
    : C5 ≤[K3] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end ErdosPentagon
