import «LeanFlagAlgebras».FlagSequence

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open MeasureTheory

def flagType_asEmptyTypeFlag
    (σ : FlagType (Fin n₀))
    : Flag ∅ₜ (Fin n₀)
  :=
  let σ₀ : LabeledGraph ∅ₜ (Fin n₀) := {
    graph := σ
    type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj σ.Adj
  }
  ⟦σ₀⟧

noncomputable def flagType_asEmptyTypeAlgebra
    (σ : FlagType (Fin n₀))
    : FlagAlgebra ∅ₜ
  :=
  let σ₀_finFlag : FinFlag ∅ₜ := ⟨n₀, flagType_asEmptyTypeFlag σ⟩
  ⟦unitVector σ₀_finFlag⟧

notation "⟨" σ "⟩₀" => (flagType_asEmptyTypeAlgebra σ)

theorem flagDensity₁_flagType_asEmptyType
    (F : FinFlag σ)
    : flagDensity₁ (flagType_asEmptyTypeFlag σ) (unlabel F.2) > 0
  := by
  sorry

theorem exists_prob_measure_extend_emptyType_positiveHom
    (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ∃ (ℙ : Measure (PositiveHomSpace σ)), IsProbabilityMeasure ℙ ∧
      ∀ (f : FlagAlgebra σ), ∫ φ, (PositiveHomSpace.toPosHom φ) f ∂ℙ = (φ₀ ⟦f⟧₀) / (φ₀ ⟨σ⟩₀)
  := by
  sorry

theorem downward_preserve_semanticCone
    (f : FlagAlgebra σ) (hf : f ∈ semanticCone σ)
    : ⟦f⟧₀ ∈ semanticCone ∅ₜ
  := by
  intro φ₀
  have : φ₀ ⟨σ⟩₀ ≥ 0 := positiveHom_unitVector_ge_zero φ₀ _
  rcases eq_or_lt_of_le this with hφ₀ | hφ₀
  · have : φ₀ ⟦f⟧₀ = 0 := by
      rw [← Quotient.out_eq f, flagVector_eq_sum_unitVector f.out]
      rw [sum_quot, downward_sum, PositiveHom.map_sum]
      apply Finset.sum_eq_zero
      intro F _
      rw [smul_quot, downward_smul, PositiveHom.map_smul, mul_eq_zero]
      right
      dsimp only [downward, downwardFlagVectorQuot, downwardFlagVector, unitVector, Quotient.lift_mk]
      rw [linearExtension_single_one]
      dsimp only [downwardFlag]
      rw [rat_smul_eq_real_smul, smul_quot, PositiveHom.map_smul, mul_eq_zero]
      right
      apply positiveHom_unitVector_eq_zero φ₀ (flagDensity₁_flagType_asEmptyType F)
      exact Eq.symm hφ₀
    exact le_of_eq (Eq.symm this)
  · obtain ⟨ℙ, _, hℙ⟩ := exists_prob_measure_extend_emptyType_positiveHom φ₀ hφ₀
    specialize hℙ f
    rw [eq_div_iff (ne_of_gt hφ₀)] at hℙ
    rw [← hℙ, ge_iff_le, mul_nonneg_iff_left_nonneg_of_pos hφ₀]
    exact integral_nonneg fun φ ↦ hf (PositiveHomSpace.toPosHom φ)

theorem square_downward_geq_zero
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  := by
  simp only [ge_iff_le, le_def, sub_zero]
  apply downward_preserve_semanticCone
  intro φ
  rw [PositiveHom.map_mul]
  exact mul_self_nonneg (φ f)
