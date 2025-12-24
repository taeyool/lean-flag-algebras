import «LeanFlagAlgebras».MantelTheorem.FlagDensity
import «LeanFlagAlgebras».MantelTheorem.FlagIso

open FlagAlgebras

namespace MantelTheorem

theorem mul_O2₁_O2₁
    : O2₁ * O2₁ = O3₁ + E3₁'
  := by
  apply Quotient.sound
  simp [flagVector_mul_eq_nested_sum, flagMul, flagMulWithSize]
  rw [Finset.sum_eq_multiset_sum, ← singletonTypeThreeVertexFlagSet_eq_univ]
  simp [singletonTypeThreeVertexFlagSet_val_eq]

theorem mul_O2₁_K2₁
    : O2₁ * K2₁ = (1 / 2 : ℝ) • E3₁ + (1 / 2 : ℝ) • P3₁'
  := by
  apply Quotient.sound
  simp [flagVector_mul_eq_nested_sum, flagMul, flagMulWithSize]
  rw [Finset.sum_eq_multiset_sum, ← singletonTypeThreeVertexFlagSet_eq_univ]
  simp [singletonTypeThreeVertexFlagSet_val_eq]

theorem mul_K2₁_K2₁
    : K2₁ * K2₁ = P3₁ + K3₁
  := by
  apply Quotient.sound
  simp [flagVector_mul_eq_nested_sum, flagMul, flagMulWithSize]
  rw [Finset.sum_eq_multiset_sum, ← singletonTypeThreeVertexFlagSet_eq_univ]
  simp [singletonTypeThreeVertexFlagSet_val_eq]

end MantelTheorem
