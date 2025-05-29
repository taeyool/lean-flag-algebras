import «LeanFlagAlgebras».FlagAlgebra
import «LeanFlagAlgebras».MantelTheorem.FlagPairDensity

open FlagAlgebras

namespace MantelTheorem

@[simp]
theorem mul_O2₁_O2₁
    : O2₁ * O2₁ = O3₁ + E3₁'
  := by
  sorry

@[simp]
theorem mul_O2₁_K2₁
    : O2₁ * K2₁ = (1 / 2 : ℝ) • E3₁ + (1 / 2 : ℝ) • P3₁'
  := by
  sorry

@[simp]
theorem mul_K2₁_K2₁
    : K2₁ * K2₁ = P3₁ + K3₁
  := by
  sorry

end MantelTheorem
