import «LeanFlagAlgebras».MantelTheorem.FlagTactic

open FlagAlgebras

namespace MantelTheorem

theorem mul_O2₁_O2₁ : O2₁ * O2₁ = O3₁ + E3₁'
  := by
  dsimp only [O2₁, O3₁, E3₁']
  prove_flag_mul

theorem mul_O2₁_K2₁ : O2₁ * K2₁ = (1 / 2 : ℝ) • E3₁ + (1 / 2 : ℝ) • P3₁'
  := by
  dsimp only [O2₁, K2₁, E3₁', P3₁']
  prove_flag_mul

theorem mul_K2₁_K2₁ : K2₁ * K2₁ = P3₁ + K3₁
  := by
  dsimp only [K2₁, P3₁, K3₁]
  prove_flag_mul

end MantelTheorem
