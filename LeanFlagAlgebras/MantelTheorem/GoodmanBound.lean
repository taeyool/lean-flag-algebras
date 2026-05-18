import LeanFlagAlgebras.MantelTheorem.Lemmas

/-! # Goodman's bound on triangle density

Proves Goodman's lower bound relating triangle and edge density in the flag
algebra: `K3 ≥ K2·(2·K2 - 1)`. The argument expands `K2` on three vertices and
applies the Cauchy–Schwarz inequality to the labelled edge flag. -/

open FlagAlgebras

namespace MantelTheorem

/-- Goodman's bound on triangle density: the triangle density `K3` is at least
`K2·(2·K2 - 1)` where `K2` is the edge density. -/
theorem Goodman_bound_on_triangle_density
    : K3 ≥ K2 * (2 • K2 - 1)
  := by
  dsimp only [K2, K3]
  suffices h : FlagAlgebra_3_0_0_3 + FlagAlgebra_2_0_0_1
      ≥ 2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1) by {
    have : FlagAlgebra_2_0_0_1 * (2 • FlagAlgebra_2_0_0_1 - 1)
        = 2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1) - FlagAlgebra_2_0_0_1 := by ring
    rw [this]
    exact (OrderedSub.tsub_le_iff_right
      (2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1))
      FlagAlgebra_2_0_0_1
      FlagAlgebra_3_0_0_3).mpr h
  }
  have h₁ : FlagAlgebra_3_0_0_3 + FlagAlgebra_2_0_0_1
      = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + 2 • ⟦FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀ := by
    have hdown : ⟦FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀
        = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3 := by
      simp [mul_FlagAlgebra_2_1_0_1_FlagAlgebra_2_1_0_1,
        downward_add]
    calc
      FlagAlgebra_3_0_0_3 + FlagAlgebra_2_0_0_1
          = FlagAlgebra_3_0_0_3
            + ((1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
              + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3) := by
        rw [expand_K2_on_three_vertex_graphs]
      _ = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
          + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + 2 • FlagAlgebra_3_0_0_3 := by
        ring
      _ = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
          + (2 * (1 / 3 : ℝ)) • FlagAlgebra_3_0_0_2 + 2 • FlagAlgebra_3_0_0_3 := by
        congr 1; congr 1
        norm_num
      _ = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
          + 2 • (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + 2 • FlagAlgebra_3_0_0_3 := by
        congr 1; congr 1
        rw [←smul_smul]
        rfl
      _ = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
          + 2 • ((1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3) := by
        ring
      _ = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + 2 • ⟦FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀ := by
        simp [hdown]
  have h₂ : (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 ≥ 0 := by
    apply nonneg_smul_nonneg_geq_zero
    linarith
    apply flag_geq_zero _
  have h₃ : 2 • ⟦FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀
      ≥ 2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1) := by
    calc
      _ = 2 • ⟦FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀ * ⟦(1 : FlagAlgebra FlagType_1_0)⟧₀ := by
        simp [← K1₁_eq_one, ← expand_1_on_one_vertex_graphs]
      _ ≥ 2 • (⟦FlagAlgebra_2_1_0_1⟧₀ * ⟦FlagAlgebra_2_1_0_1⟧₀) := by
        simpa [mul_assoc] using
          (nsmul_le_nsmul_right (Cauchy_Schwarz_inequality_unit FlagAlgebra_2_1_0_1) 2)
      _ = 2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1) := by simp
  calc
    _ = (1 /3 : ℝ) • FlagAlgebra_3_0_0_1 + 2 • ⟦FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀ := by
        rw [h₁]
    _ ≥ 0 + 2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1) := by
        apply flag_add_le_add h₂ h₃
    _ = 2 • (FlagAlgebra_2_0_0_1 * FlagAlgebra_2_0_0_1) := by
        simp only [nsmul_eq_mul, Nat.cast_ofNat, zero_add]

end MantelTheorem
