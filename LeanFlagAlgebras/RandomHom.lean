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

theorem flagDensity₁_flagType_asEmptyType_pos
    (F : FinFlag σ)
    : flagDensity₁ (flagType_asEmptyTypeFlag σ) (unlabel F.2) > 0
  := by
  dsimp only [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity]
  dsimp only [flagType_asEmptyTypeFlag, unlabel, subflagDensity, labeledSubgraphDensityLifted,
    labeledSubgraphDensity, Quotient.lift_mk]
  apply div_pos
  · simp only [Nat.cast_pos, labeledSubgraphCount]
    rw [Finset.card_pos]
    simp only [Finset.Nonempty, Set.mem_toFinset, Set.mem_setOf_eq]
    let G : LabeledSubgraph ∅ₜ (unlabeledGraph F.2.out) :=
      LabeledSubgraph.inducedLabeledSubgraph _ F.2.out.type_verts (by
        simp only [LabeledGraph.type_verts, unlabeledGraph, Set.image_univ, Matrix.range_empty,
          Set.empty_subset]
      )
    use G
    constructor
    · apply LabeledSubgraph.inducedLabeledSubgraph_isInduced
    · apply Nonempty.intro
      simp only [unlabeledGraph, LabeledSubgraph.inducedLabeledSubgraph, LabeledGraph.type_verts, inducedSubgraph, LabeledSubgraph.coe, G]
      exact {
        graph_iso := {
            toFun v := by
              have : ∃ i, F.2.out.type_embed i = v := by
                obtain ⟨val, property⟩ := v
                simp only
                simp_all only [Set.image_univ, Set.mem_range]
              exact this.choose
            invFun v := by
              simp only [Set.image_univ]
              exact Set.rangeFactorization F.2.out.type_embed v
            left_inv := by
              intro ⟨v, hv⟩
              simp only [eq_mpr_eq_cast, Set.image_univ, set_coe_cast, Set.rangeFactorization_coe]
              obtain ⟨i, hi⟩ : ∃ i, F.2.out.type_embed i = v := by
                obtain ⟨val, property⟩ := v
                simp_all only [Set.image_univ, Set.mem_range]
              subst hi
              simp only [EmbeddingLike.apply_eq_iff_eq, Classical.choose_eq]
            right_inv := by
              intro ⟨i, hi⟩
              simp only [eq_mpr_eq_cast, Set.image_univ, set_coe_cast, Set.rangeFactorization_coe, EmbeddingLike.apply_eq_iff_eq, Classical.choose_eq]
            map_rel_iff' := by
              intro ⟨v, hv⟩ ⟨w, hw⟩
              simp only [Set.image_univ, Equiv.coe_fn_mk, SimpleGraph.Subgraph.coe_adj]
              constructor
              · intro h
                constructor
                · simp only [Set.image_univ, Set.mem_range] at hv hw
                  obtain ⟨vi, hvi⟩ := hv
                  obtain ⟨wi, hwi⟩ := hw
                  subst hvi hwi
                  simp_all only [EmbeddingLike.apply_eq_iff_eq, Classical.choose_eq, SimpleGraph.Embedding.map_adj_iff]
                · constructor
                  · exact Set.mem_range_of_mem_image F.2.out.type_embed Set.univ hv
                  · exact Set.mem_range_of_mem_image F.2.out.type_embed Set.univ hw
              · intro ⟨h, ⟨vi, hvi⟩, ⟨wi, hwi⟩⟩
                subst hvi hwi
                simp_all only [SimpleGraph.Embedding.map_adj_iff, EmbeddingLike.apply_eq_iff_eq, Classical.choose_eq]
          }
        type_preserve := List.ofFn_inj.mp rfl
      }
  · simp only [emptyType_size, tsub_zero, Nat.cast_pos, LabeledGraph.size, Fintype.card_fin]
    have : F.1 ≥ n₀ := finFlag_size_ge_n₀ F
    exact Nat.choose_pos this

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
      apply positiveHom_unitVector_eq_zero φ₀ (flagDensity₁_flagType_asEmptyType_pos F)
      exact Eq.symm hφ₀
    exact le_of_eq (Eq.symm this)
  · obtain ⟨ℙ, _, hℙ⟩ := exists_prob_measure_extend_emptyType_positiveHom φ₀ hφ₀
    specialize hℙ f
    rw [eq_div_iff (ne_of_gt hφ₀)] at hℙ
    rw [← hℙ, ge_iff_le, mul_nonneg_iff_left_nonneg_of_pos hφ₀]
    exact integral_nonneg fun φ ↦ hf (PositiveHomSpace.toPosHom φ)

theorem square_downward_nonneg
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  := by
  simp only [ge_iff_le, le_def, sub_zero]
  apply downward_preserve_semanticCone
  intro φ
  rw [PositiveHom.map_mul]
  exact mul_self_nonneg (φ f)
