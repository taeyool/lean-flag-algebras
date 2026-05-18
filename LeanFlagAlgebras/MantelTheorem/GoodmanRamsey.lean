import LeanFlagAlgebras.MantelTheorem.Lemmas

/-! # Goodman's bound on Ramsey multiplicity

Uses the same square-positivity certificate as Mantel's theorem to prove
Goodman's lower bound on the combined density of monochromatic triangles:
`O3 + K3 ≥ (1/4)·1`, i.e. the total number of triangles plus independent
triples is at least a quarter of all triples. -/

open FlagAlgebras

namespace MantelTheorem

/-- Goodman's theorem on Ramsey multiplicity: the sum of the empty-triple
density `O3` and the triangle density `K3` is at least `1/4`. -/
theorem Goodman_theorem_on_Ramsey_multiplicity
    : O3 + K3 ≥ (1 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  dsimp only [O3, K3]
  have h₀ : 0 ≤ (3 / 4 : ℝ) • FlagAlgebra_3_0_0_0 - (1 / 4 : ℝ) • FlagAlgebra_3_0_0_1
      - (1 / 4 : ℝ) • FlagAlgebra_3_0_0_2 + (3 / 4 : ℝ) • FlagAlgebra_3_0_0_3 := by
    calc
      0 ≤ (3 / 4 : ℝ) • (FlagAlgebra_3_0_0_0 - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
          - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3) := by
          apply nonneg_smul_nonneg_geq_zero (by grind)
          rw [← FlagAlgebra_2_1_0_0_minus_FlagAlgebra_2_1_0_1_square_downward]
          apply square_downward_nonneg
      _ = _ := by
          simp only [smul_add, smul_sub, smul_smul]
          norm_num
  calc
    _ ≥ (FlagAlgebra_3_0_0_0 + FlagAlgebra_3_0_0_3)
      - ((3 / 4 : ℝ) • FlagAlgebra_3_0_0_0 - (1 / 4 : ℝ) • FlagAlgebra_3_0_0_1
      - (1 / 4 : ℝ) • FlagAlgebra_3_0_0_2 + (3 / 4 : ℝ) • FlagAlgebra_3_0_0_3) := by
      apply sub_le_self
      exact h₀
    _ = ((1 : ℝ) - (3 / 4 : ℝ)) • FlagAlgebra_3_0_0_0
      + (1 / 4 : ℝ) • FlagAlgebra_3_0_0_1
      + (1 / 4 : ℝ) • FlagAlgebra_3_0_0_2
      + ((1 : ℝ) - (3 / 4 : ℝ)) • FlagAlgebra_3_0_0_3 := by
        simp only [one_div, sub_smul, one_smul]
        ring
    _ = (1 / 4 : ℝ) • FlagAlgebra_3_0_0_0 + (1 / 4 : ℝ) • FlagAlgebra_3_0_0_1
      + (1 / 4 : ℝ) • FlagAlgebra_3_0_0_2 + (1 / 4 : ℝ) • FlagAlgebra_3_0_0_3 := by
        norm_num
    _ = (1 / 4 : ℝ) • 1 := by
        rw [expand_1_on_three_vertex_graphs]
        norm_num

end MantelTheorem
