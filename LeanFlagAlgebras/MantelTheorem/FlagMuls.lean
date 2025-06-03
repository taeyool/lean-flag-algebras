import «LeanFlagAlgebras».FlagAlgebra
import «LeanFlagAlgebras».MantelTheorem.FlagPairDensity

open FlagAlgebras

namespace MantelTheorem

theorem mul_O2₁_O2₁
    : O2₁ * O2₁ = O3₁ + E3₁'
  := by
  apply Quotient.sound; simp
  rw [flagVector_mul_def]
  simp
  dsimp [flagMul, flagMulWithSize]
  let set : Set (FlagWithSize Sₜ 3) := Set.univ
  have h_set : set = {O3₁_flag, E3₁_flag, E3₁'_flag, P3₁_flag, P3₁'_flag, K3₁_flag} := by sorry
  have sum_rel : ∑ G : FlagWithSize Sₜ 3, ↑(flagDensity₂ O2₁_flag O2₁_flag G) • unitVector ⟨3, G⟩ = ∑ G ∈ set, ↑(flagDensity₂ O2₁_flag O2₁_flag G) • unitVector ⟨3, G⟩ := by
    simp only [rat_smul_eq_real_smul]
    have : set.toFinset = Finset.univ := by sorry
    rw [this]
  have sum_eq : ∑ G : FlagWithSize Sₜ 3, ↑(flagDensity₂ O2₁_flag O2₁_flag G) • unitVector ⟨3, G⟩ = unitVector ⟨3, O3₁_flag⟩ + unitVector ⟨3, E3₁'_flag⟩ := by
    rw [sum_rel]
    sorry
  exact Quotient.exact (congrArg (Quotient.mk (flagVectorSetoid Sₜ)) sum_eq)

theorem mul_O2₁_K2₁
    : O2₁ * K2₁ = (1 / 2 : ℝ) • E3₁ + (1 / 2 : ℝ) • P3₁'
  := by
  sorry

theorem mul_K2₁_K2₁
    : K2₁ * K2₁ = P3₁ + K3₁
  := by
  sorry

end MantelTheorem
