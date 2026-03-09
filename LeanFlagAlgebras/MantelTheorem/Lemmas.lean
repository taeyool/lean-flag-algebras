import «LeanFlagAlgebras».MantelTheorem.FlagMul

open FlagAlgebras Compute

namespace MantelTheorem

lemma expand_K2_on_three_vertex_graphs
    : K2 = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3
  := by
  dsimp only [K2, E3, P3, K3]
  prove_flag_expand 3

example : FlagAlgebra_2_0_0_1 = (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + (1 : ℝ) • FlagAlgebra_3_0_0_3 + (0 : ℝ) • FlagAlgebra_3_0_0_0 + (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
  := by
  prove_flag_expand 3

example : K2₁ = (1 / 2 : ℝ) • E3₁ + P3₁ + (1 / 2 : ℝ) • P3₁' + K3₁
  := by
  dsimp only [K2₁, E3₁, P3₁, P3₁', K3₁]
  prove_flag_expand 3

lemma K0_eq_one
    : K0 = 1
  := by
  apply Quotient.sound
  show _ ∼v unitVector ⟨0, default⟩
  congr!
  exact Unique.uniq instUniqueFlagWithSize Flag_0_0_0_0

lemma expand_1_on_one_vertex_graphs
    : 1 = K1
  := by
  rw [← K0_eq_one]
  dsimp only [K0]
  prove_flag_expand 1

lemma expand_1_on_three_vertex_graphs
    : 1 = O3 + E3 + P3 + K3
  := by
  rw [← K0_eq_one]
  dsimp only [K0, O3, E3, P3, K3]
  prove_flag_expand 3

lemma K1₁_eq_one
    : K1₁ = 1
  := by
  apply Quotient.sound
  show _ ∼v unitVector ⟨1, default⟩
  congr!
  exact Unique.uniq instUniqueFlagWithSize Flag_1_1_0_0

lemma O2₁_minus_K2₁_square_downward
    : ⟦(O2₁ - K2₁) * (O2₁ - K2₁)⟧₀ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3
  := by
  calc
    _ = ⟦O2₁ * O2₁ - 2 • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := by congr; rw [two_smul]; ring
    _ = ⟦O2₁ * O2₁ - (2 : ℝ) • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := rfl
    _ = ⟦O3₁ + E3₁' - E3₁ - P3₁' + P3₁ + K3₁⟧₀ := by
        congr 1
        simp [mul_O2₁_O2₁, mul_O2₁_K2₁, mul_K2₁_K2₁]
        ring
    _ = ⟦O3₁⟧₀ + ⟦E3₁'⟧₀ - ⟦E3₁⟧₀ - ⟦P3₁'⟧₀ + ⟦P3₁⟧₀ + ⟦K3₁⟧₀ := by simp only [downward_add, downward_sub]
    _ = O3 - ((2 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • E3) - ((2 / 3 : ℝ) • P3 - (1 / 3 : ℝ) • P3) + K3 := by
        simp; ring
    _ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3 := by
        simp only [← sub_smul]
        norm_num

end MantelTheorem
