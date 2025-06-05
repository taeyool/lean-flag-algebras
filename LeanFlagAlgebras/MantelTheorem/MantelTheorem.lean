import «LeanFlagAlgebras».PositiveHom
import «LeanFlagAlgebras».MantelTheorem.Downward
import «LeanFlagAlgebras».MantelTheorem.FlagMuls

open FlagAlgebras

namespace MantelTheorem

/- proof of Mantel's theorem -/

lemma expand_K2_on_3_vertex_graphs
    : K2 = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3
  := by
  apply Quotient.sound
  apply flagVectorEqv.trans (unitVector_eqv_densityFlagSum ⟨2, K2_flag⟩ 3 (by simp))
  dsimp [densityFlagSum]
  rw [Finset.sum_eq_multiset_sum, ← emptyTypeThreeVertexFlagSet_eq_univ]
  simp only [emptyTypeThreeVertexFlagSet, Multiset.map_coe, List.map_cons, List.map_nil,
    Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  apply flagVector_eq_eqv
  calc
    _ = (0 : ℝ) • unitVector ⟨3, O3_flag⟩ + ((1 / 3 : ℝ) • unitVector ⟨3, E3_flag⟩ +
        ((2 / 3 : ℝ) • unitVector ⟨3, P3_flag⟩ + (1 : ℝ) • unitVector ⟨3, K3_flag⟩)) := by
      congr <;> simp
    _ = _ := by simp only [add_assoc, zero_smul, zero_add, one_smul]

lemma expand_1_on_3_vertex_graphs
    : 1 = O3 + E3 + P3 + K3
  := by
  apply Quotient.sound
  apply flagVectorEqv.trans (one_vector_eqv_densityFlagSum 3 (by simp))
  dsimp [densityFlagSum]
  calc
    _ ∼v (∑ F' : FlagWithSize ∅ₜ 3, unitVector ⟨3, F'⟩) := by
      apply flagVectorEqv_sum; intros
      rw [finFlag_one_snd, flagDensity_empty]
      simp only [Rat.cast_one, one_smul]
      rfl
    _ ∼v _ := by
      rw [Finset.sum_eq_multiset_sum, ← emptyTypeThreeVertexFlagSet_eq_univ]
      simp only [emptyTypeThreeVertexFlagSet, Multiset.map_coe, List.map_cons, List.map_nil,
        Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
      apply flagVector_eq_eqv
      simp only [add_assoc]

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
        norm_num

theorem mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  have h₁ : K2 ≤ (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3 := by rw [expand_K2_on_3_vertex_graphs]
  have h₂ : 0 ≤ (1 / 3 : ℝ) • E3 := by
    apply nonneg_smul_nonneg_geq_zero (by simp)
    apply flag_geq_zero
  have h₃ : 0 ≤ (1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3 := by
    calc
      0 ≤ (1 / 2 : ℝ) • (O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3) := by
          apply nonneg_smul_nonneg_geq_zero (by simp)
          rw [← O2₁_minus_K2₁_square_downward]
          apply square_downward_geq_zero
      _ = _ := by
          simp only [smul_add, smul_sub, smul_smul]
          norm_num
  calc
    _ = K2 + 0 + 0 := by simp only [add_zero]
    _ ≤ ((1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3)
        + (1 / 3 : ℝ) • E3
        + ((1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3) :=
        flag_add_le_add (flag_add_le_add h₁ h₂) h₃
    _ = (1 / 2 : ℝ) • O3
        + ((1 / 3 : ℝ) + (1 / 3 : ℝ) - (1 / 6 : ℝ)) • E3
        + ((2 / 3 : ℝ) - (1 / 6 : ℝ)) • P3
        + (1 / 2 : ℝ) • K3 + K3 := by simp only [add_smul, sub_smul]; ring
    _ = (1 / 2 : ℝ) • O3 + (1 / 2 : ℝ) • E3 + (1 / 2 : ℝ) • P3 + (1 / 2 : ℝ) • K3 + K3 := by norm_num
    _ = (1 / 2 : ℝ) • 1 + K3 := by
        rw [expand_1_on_3_vertex_graphs]
        norm_num

end MantelTheorem
