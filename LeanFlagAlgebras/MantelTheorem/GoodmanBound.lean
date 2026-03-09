import «LeanFlagAlgebras».FlagAlgebra.RandomHom
import «LeanFlagAlgebras».MantelTheorem.Lemmas

open FlagAlgebras

namespace MantelTheorem

theorem Goodman_bound_on_triangle_density
    : K3 ≥ K2 * (2 • K2 - 1)
  := by
  suffices h : K3 + K2 ≥ 2 • (K2 * K2) by {
    have : K2 * (2 • K2 - 1) = 2 • (K2 * K2) - K2 := by ring
    rw [this]
    exact (OrderedSub.tsub_le_iff_right (2 • (K2 * K2)) K2 K3).mpr h
  }
  have h₁ : K3 + K2 = (1 / 3 : ℝ) • E3 + 2 • ⟦K2₁ * K2₁⟧₀ := by
    have hdown : ⟦K2₁ * K2₁⟧₀ = (1 / 3 : ℝ) • P3 + K3 := by
      simp [mul_K2₁_K2₁, P3₁, K3₁, downward_add]
    calc
      K3 + K2 = K3 + ((1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3) := by
        rw [expand_K2_on_three_vertex_graphs]
      _ = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + 2 • K3 := by
        ring
      _ = (1 / 3 : ℝ) • E3 + (2 * (1 / 3 : ℝ)) • P3 + 2 • K3 := by
        congr 1; congr 1
        norm_num
      _ = (1 / 3 : ℝ) • E3 + 2 • (1 / 3 : ℝ) • P3 + 2 • K3 := by
        congr 1; congr 1
        rw [←smul_smul]
        rfl
      _ = (1 / 3 : ℝ) • E3 + 2 • ((1 / 3 : ℝ) • P3 + K3) := by
        ring
      _ = (1 / 3 : ℝ) • E3 + 2 • ⟦K2₁ * K2₁⟧₀ := by
        simp [hdown]
  have h₂ : (1 / 3 : ℝ) • E3 ≥ 0 := by
    apply nonneg_smul_nonneg_geq_zero
    linarith
    apply flag_geq_zero _
  have h₃ : 2 • ⟦K2₁ * K2₁⟧₀ ≥ 2 • (K2 * K2) := by
    calc
      _ = 2 • ⟦K2₁ * K2₁⟧₀ * ⟦(1 : FlagAlgebra FlagType_1_0)⟧₀ := by
        simp [← K1₁_eq_one, ← expand_1_on_one_vertex_graphs]
      _ ≥ 2 • (⟦K2₁⟧₀ * ⟦K2₁⟧₀) := by
        simpa [mul_assoc] using (nsmul_le_nsmul_right (Cauchy_Schwarz_inequality_unit K2₁) 2)
      _ = 2 • (K2 * K2) := by simp
  calc
    _ = (1 /3 : ℝ) • E3 + 2 • ⟦K2₁ * K2₁⟧₀ := by
        rw [h₁]
    _ ≥ 0 + 2 • (K2 * K2) := by
        apply flag_add_le_add h₂ h₃
    _ = 2 • (K2 * K2) := by
        simp only [nsmul_eq_mul, Nat.cast_ofNat, zero_add]

end MantelTheorem
