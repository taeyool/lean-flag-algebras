import «LeanFlagAlgebras».FlagAlgebra.RandomHom
import «LeanFlagAlgebras».MantelTheorem.Lemmas

open FlagAlgebras

namespace MantelTheorem

theorem Goodman_theorem_on_Ramsey_multiplicity
    : O3 + K3 ≥ (1 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have h₀ : 0 ≤ (3 / 4 : ℝ) • O3 - (1 / 4 : ℝ) • E3 - (1 / 4 : ℝ) • P3 + (3 / 4 : ℝ) • K3 := by
    calc
      0 ≤ (3 / 4 : ℝ) • (O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3) := by
          apply nonneg_smul_nonneg_geq_zero (by grind)
          rw [← O2₁_minus_K2₁_square_downward]
          apply square_downward_nonneg
      _ = _ := by
          simp only [smul_add, smul_sub, smul_smul]
          norm_num
  calc
    _ ≥ (O3 + K3)
      - ((3 / 4 : ℝ) • O3 - (1 / 4 : ℝ) • E3 - (1 / 4 : ℝ) • P3 + (3 / 4 : ℝ) • K3) := by
      apply sub_le_self
      exact h₀
    _ = ((1 : ℝ) - (3 / 4 : ℝ)) • O3
        + (1 / 4 : ℝ) • E3
        + (1 / 4 : ℝ) • P3
        + ((1 : ℝ) - (3 / 4 : ℝ)) • K3 := by
        simp only [one_div, sub_smul, one_smul]
        ring
    _ = (1 / 4 : ℝ) • O3 + (1 / 4 : ℝ) • E3 + (1 / 4 : ℝ) • P3 + (1 / 4 : ℝ) • K3 := by
        norm_num
    _ = (1 / 4 : ℝ) • 1 := by
        rw [expand_1_on_three_vertex_graphs]
        norm_num

end MantelTheorem
