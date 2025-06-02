import «LeanFlagAlgebras».PositiveHom
import «LeanFlagAlgebras».MantelTheorem.Downward
import «LeanFlagAlgebras».MantelTheorem.FlagMuls

open FlagAlgebras

namespace MantelTheorem

/- proof of Mantel's theorem -/

lemma O2₁_minus_K2₁_square_downward
    : ⟦(O2₁ - K2₁) * (O2₁ - K2₁)⟧₀ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3
  := by
  calc
    _ = ⟦O2₁ * O2₁ - (O2₁ * K2₁ + O2₁ * K2₁) + K2₁ * K2₁⟧₀ := by congr; ring
    _ = ⟦O2₁ * O2₁ - 2 • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := by congr; ring
    _ = ⟦O2₁ * O2₁ - (2 : ℝ) • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := rfl
    _ = ⟦O3₁ + E3₁' - E3₁ - P3₁' + P3₁ + K3₁⟧₀ := by
        congr 1
        simp [mul_O2₁_O2₁, mul_O2₁_K2₁, mul_K2₁_K2₁]
        ring
    _ = ⟦O3₁⟧₀ + ⟦E3₁'⟧₀ - ⟦E3₁⟧₀ - ⟦P3₁'⟧₀ + ⟦P3₁⟧₀ + ⟦K3₁⟧₀ := by simp only [downward_add, downward_sub]
    _ = O3 - ((2 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • E3) - ((2 / 3 : ℝ) • P3 - (1 / 3 : ℝ) • P3) + K3 := by
        simp only [downward_O3₁, downward_E3₁', downward_E3₁, downward_P3₁', downward_P3₁,
          downward_K3₁]
        ring
    _ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3 := by
        simp only [← sub_smul]
        congr <;> norm_num

lemma expand_K2_on_3_vertex_graphs
    : K2 = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3
  := by
  sorry

lemma expand_1_on_3_vertex_graphs
    : 1 = O3 + E3 + P3 + K3
  := by
  sorry

theorem mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  rw [flag_sub_nonneg]
  sorry

end MantelTheorem
