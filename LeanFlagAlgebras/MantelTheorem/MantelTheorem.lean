import «LeanFlagAlgebras».PositiveHom
import «LeanFlagAlgebras».RandomHom
import «LeanFlagAlgebras».MantelTheorem.Downward
import «LeanFlagAlgebras».MantelTheorem.FlagMuls

open FlagAlgebras

namespace MantelTheorem

/- proof of Mantel's theorem -/

lemma expand_K2_on_3_vertex_graphs
    : K2 = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3
  := by
  apply Quotient.sound
  ring_nf
  apply flagVectorEqv.trans (unitVector_eqv_densityFlagSum ⟨2, K2_flag⟩ 3 (by simp))
  dsimp [densityFlagSum]
  rw [Finset.sum_eq_multiset_sum, ← emptyTypeThreeVertexFlagSet_eq_univ]
  simp [emptyTypeThreeVertexFlagSet_val_eq]
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
      rw [Finset.sum_eq_multiset_sum, ← emptyTypeThreeVertexFlagSet_eq_univ]
      simp [emptyTypeThreeVertexFlagSet_val_eq]
      apply flagVector_eq_eqv
      simp only [add_assoc]

lemma expand_1_on_one_vertex_graphs
    : 1 = K1
  := by
  apply Quotient.sound
  apply flagVectorEqv.trans (one_vector_eqv_densityFlagSum 1 (by simp))
  dsimp [densityFlagSum]
  rw [Finset.sum_eq_multiset_sum, ← emptyTypeOneVertexFlagSet_eq_univ]
  simp [emptyTypeOneVertexFlagSet_val_eq]
  rw [finFlag_one_snd, flagDensity_empty]
  simp only [Rat.cast_one, one_smul]
  rfl

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
  have h₂ : 0 ≤ (1 / 3 : ℝ) • E3 :=
    nonneg_smul_nonneg_geq_zero (by linarith) (flag_geq_zero _)
  have h₃ : 0 ≤ (1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3 := by
    calc
      0 ≤ (1 / 2 : ℝ) • (O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3) := by
          apply nonneg_smul_nonneg_geq_zero (by simp)
          rw [← O2₁_minus_K2₁_square_downward]
          apply square_downward_nonneg
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

instance {ℓ} (σ : FlagType (Fin ℓ)) : AddLeftMono (FlagAlgebra σ) :=
  ⟨fun _ _ _ h => flag_add_le_add (le_refl _) h⟩

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
        rw [expand_1_on_3_vertex_graphs]
        norm_num

theorem downward_zero_case {ℓ} {σ : FlagType (Fin ℓ)}
    (φ : PositiveHom ∅ₜ) (hφ : φ ⟨σ⟩₀ = 0)
    : ∀ f : FlagAlgebra σ, φ ⟦f⟧₀ = 0
  := by
  intro f
  rw [← Quotient.out_eq f, flagVector_eq_sum_unitVector f.out]
  rw [sum_quot, downward_sum, PositiveHom.map_sum]
  apply Finset.sum_eq_zero
  intro F _
  rw [smul_quot, downward_smul, PositiveHom.map_smul, mul_eq_zero]
  right
  dsimp only [downward, downwardFlagVectorQuot, downwardFlagVector, Quotient.lift_mk]
  rw [linearExtension_unitVector]
  dsimp only [downwardFlag]
  rw [rat_smul_eq_real_smul, smul_quot, PositiveHom.map_smul, mul_eq_zero]
  right
  apply positiveHom_unitVector_eq_zero φ (flagDensity₁_flagType_asEmptyType_pos F)
  exact hφ


theorem Cauchy_Schwarz_inequality {ℓ} {σ : FlagType (Fin ℓ)} (f g : FlagAlgebra σ)
    : ⟦f * f⟧₀ * ⟦g * g⟧₀ ≥ ⟦f * g⟧₀ * ⟦f * g⟧₀
  := by
  intro φ
  rw [PositiveHom.map_sub φ _ _, PositiveHom.map_mul φ _ _, PositiveHom.map_mul φ _ _]
  have : φ ⟨σ⟩₀ ≥ 0 := positiveHom_unitVector_ge_zero φ _
  rcases eq_or_lt_of_le this with hφ | hφ
  · have hφ_zero : ∀ k : FlagAlgebra σ, φ ⟦k⟧₀ = 0 := downward_zero_case φ (Eq.symm hφ)
    rw [hφ_zero (f * f), hφ_zero (g * g), hφ_zero (f * g)]
    simp only [mul_zero, sub_self, ge_iff_le, le_refl]
  . obtain ⟨ℙ, hℙ⟩ := exists_probMeasure_extend_emptyType_positiveHom hφ
    let hℙ₁ := hℙ (f * f)
    let hℙ₂ := hℙ (g * g)
    let hℙ₃ := hℙ (f * g)
    have hφ' : φ ⟦(1 : FlagAlgebra σ)⟧₀ > 0 := positiveHom_one_downward_pos hφ
    rw [eq_div_iff (ne_of_gt hφ')] at hℙ₁ hℙ₂ hℙ₃
    rw [← hℙ₁, ← hℙ₂, ← hℙ₃, ge_iff_le]
    rw [←mul_assoc _ _ (φ (downward 1)), ← mul_assoc _ _ (φ (downward 1))]
    rw [mul_assoc _ (φ (downward 1)) _, mul_assoc _ (φ (downward 1)) _]
    rw [mul_comm (φ (downward 1)) _, mul_comm (φ (downward 1)) _]
    rw [←mul_assoc _ _ (φ (downward 1)), ←mul_assoc _ _ (φ (downward 1))]
    rw [mul_assoc _ _ (φ (downward 1)), mul_assoc _ _ (φ (downward 1))]
    rw [←sub_mul]
    have hφ'' : φ ⟦(1 : FlagAlgebra σ)⟧₀ * φ ⟦(1 : FlagAlgebra σ)⟧₀ > 0 := by
      simp_all only [ge_iff_le, gt_iff_lt, mul_pos_iff_of_pos_left]
    rw [mul_nonneg_iff_of_pos_right hφ'']
    sorry


lemma one₁_eq_K1₁
    : (1 : FlagAlgebra Sₜ) = K1₁
  := by
  apply Quotient.sound
  have : (1 : FlagVector Sₜ) = unitVector ⟨1, (default : Flag Sₜ (Fin 1))⟩ := by rfl
  rw [this]
  congr!
  apply Quotient.sound
  have h_eq_bot_top : (⊥ : SimpleGraph (Fin 1)) = (⊤ : SimpleGraph (Fin 1)) := by
    ext x y
    simp only [SimpleGraph.bot_adj, SimpleGraph.top_adj, ne_eq]
    exact iff_of_false not_false (fun h => h (Subsingleton.elim x y))
  have : emptyLabeledGraph Sₜ = K1₁_labeledGraph := by
    simp [emptyLabeledGraph, Sₜ, singletonType, K1₁_labeledGraph, K1_graph]
    constructor
    . exact h_eq_bot_top
    . congr!
  rw [this]


theorem Cauchy_Schwarz_inequality_unit (f : FlagAlgebra Sₜ)
    : ⟦f * f⟧₀ ≥ ⟦f⟧₀ * ⟦f⟧₀
  := by
  have h₁ : ⟦f * f⟧₀ * ⟦(1 : FlagAlgebra Sₜ)⟧₀ ≥ ⟦f⟧₀ * ⟦f⟧₀ := by
    have := Cauchy_Schwarz_inequality f 1
    rwa [mul_one f, mul_one 1] at this
  have h₂ : ⟦(1 : FlagAlgebra Sₜ)⟧₀ = 1 := by
    rw [one₁_eq_K1₁]
    rw [downward_K1₁]
    rw [expand_1_on_one_vertex_graphs]
  rwa [h₂, mul_one] at h₁


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
      simp only [mul_K2₁_K2₁, downward_add, downward_P3₁, downward_K3₁]
    calc
      K3 + K2 = K3 + ((1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3) := by
        rw [expand_K2_on_3_vertex_graphs]
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
      _ ≥ 2 • (⟦K2₁⟧₀ * ⟦K2₁⟧₀) := nsmul_le_nsmul_right (Cauchy_Schwarz_inequality_unit K2₁) 2
      _ = 2 • (K2 * K2) := by simp only [downward_K2₁]
  calc
    _ = (1 /3 : ℝ) • E3 + 2 • ⟦K2₁ * K2₁⟧₀ := by
        rw [h₁]
    _ ≥ 0 + 2 • (K2 * K2) := by
        apply flag_add_le_add h₂ h₃
    _ = 2 • (K2 * K2) := by
        simp only [nsmul_eq_mul, Nat.cast_ofNat, zero_add]

end MantelTheorem
