import «LeanFlagAlgebras».MantelTheorem.FlagMul

open FlagAlgebras

namespace MantelTheorem

lemma expand_K2_on_3_vertex_graphs
    : K2 = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3
  := by
  apply Quotient.sound
  ring_nf
  apply flagVectorEqv.trans (unitVector_eqv_densityFlagSum ⟨2, K2_flag⟩ 3 (by simp))
  dsimp [densityFlagSum]
  rw [Finset.sum_eq_multiset_sum, ← flagSet_3_0_0_eq_univ]
  simp [flagSet_3_0_0_val_eq]
  rw [add_assoc]

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
      rw [Finset.sum_eq_multiset_sum, ← flagSet_3_0_0_eq_univ]
      simp [flagSet_3_0_0_val_eq]
      apply flagVector_eq_eqv
      simp only [add_assoc]

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
        simp [downward_3_1_0_0, downward_3_1_0_1, downward_3_1_0_2, downward_3_1_0_3, downward_3_1_0_4, downward_3_1_0_5]
        ring
    _ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3 := by
        simp only [← sub_smul]
        norm_num

end MantelTheorem
