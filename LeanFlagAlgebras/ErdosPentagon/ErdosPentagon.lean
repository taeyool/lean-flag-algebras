import LeanFlagAlgebras.ErdosPentagon.FlagMul

open FlagAlgebras

namespace ErdosPentagon

example
    : flagQuadraticForm R_real v₂ ≥ 0
  :=
  flagQuadraticForm_nonneg R_real R_real_posSemidef v₂

example
    : flagQuadraticForm R_real Vᵣ =[K3]
        (1512 / 625 : ℝ) • FlagAlgebra_5_3_2_0
        - (380 / 625 : ℝ) • FlagAlgebra_5_3_2_1
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_2
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_3
        + (1512 / 625 : ℝ) • FlagAlgebra_5_3_2_4
        + (192 / 625 : ℝ) • FlagAlgebra_5_3_2_5
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_8
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_9
        - (380 / 625 : ℝ) • FlagAlgebra_5_3_2_10
        + (475 / 625 : ℝ) • FlagAlgebra_5_3_2_11
        + (475 / 625 : ℝ) • FlagAlgebra_5_3_2_12
        - (376 / 625 : ℝ) • FlagAlgebra_5_3_2_13
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_15
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_16
        - (2 / 625 : ℝ) • FlagAlgebra_5_3_2_29
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_30
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_31
        - (93 / 625 : ℝ) • FlagAlgebra_5_3_2_32
        - (93 / 625 : ℝ) • FlagAlgebra_5_3_2_33
        - (376 / 625 : ℝ) • FlagAlgebra_5_3_2_34
        - (2 / 625 : ℝ) • FlagAlgebra_5_3_2_53
        + (190 / 625 : ℝ) • FlagAlgebra_5_3_2_54
  := by sorry

theorem ErdosPentagon
    : C5 ≤[K3] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end ErdosPentagon
