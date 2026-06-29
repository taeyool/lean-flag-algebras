import LeanFlagAlgebras.MantelTheorem.FlagDensity
import LeanFlagAlgebras.Automation.FlagMulReduce

/-! # Mantel's theorem: flag products

Products in the flag algebra over the one-labelled-vertex type, expressing each
product of two `2`-vertex flags as a linear combination of `3`-vertex flags.
These identities feed the square-positivity (`O2₁ - K2₁`) argument used to prove
Mantel's theorem. Each proof is discharged by the `reduce_flagmul` tactic. -/

open FlagAlgebras

namespace MantelTheorem

/- O2₁ * O2₁ = O3₁ + E3₁' -/
theorem mul_FlagAlgebra_2_1_0_0_FlagAlgebra_2_1_0_0
    : FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_0 = FlagAlgebra_3_1_0_0 + FlagAlgebra_3_1_0_2
  := by
  reduce_flagmul

/- O2₁ * K2₁ = (1 / 2) • E3₁ + (1 / 2) • P3₁' -/
theorem mul_FlagAlgebra_2_1_0_0_FlagAlgebra_2_1_0_1
    : FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_1
        = (1 / 2 : ℝ) • FlagAlgebra_3_1_0_1 + (1 / 2 : ℝ) • FlagAlgebra_3_1_0_4
  := by
  reduce_flagmul

/- K2₁ * K2₁ = P3₁ + K3₁ -/
theorem mul_FlagAlgebra_2_1_0_1_FlagAlgebra_2_1_0_1
    : FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1 = FlagAlgebra_3_1_0_3 + FlagAlgebra_3_1_0_5
  := by
  reduce_flagmul

end MantelTheorem
