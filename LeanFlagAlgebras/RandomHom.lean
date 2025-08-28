import «LeanFlagAlgebras».FlagSequence

open FlagAlgebras
open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open MeasureTheory

def SimpleGraph.toEmptyTypeFlag
    (σ : FlagType (Fin n₀))
    : Flag ∅ₜ (Fin n₀)
  :=
  let σ₀ : LabeledGraph ∅ₜ (Fin n₀) := {
    graph := σ
    type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj σ.Adj
  }
  ⟦σ₀⟧

theorem flagType_asEmptyTypeFlag_eq
    (σ : FlagType (Fin n₀))
    : σ.toEmptyTypeFlag = unlabel (1 : FinFlag σ).2
  := by
  apply Quotient.sound
  apply Nonempty.intro
  exact {
    graph_iso := by
      show σ ≃g ⟦emptyLabeledGraph σ⟧.out.graph
      have : σ = (emptyLabeledGraph σ).graph := rfl
      nth_rw 1 [this]
      apply LabeledGraphIso.graph_iso
      symm
      apply Classical.choice
      show ⟦emptyLabeledGraph σ⟧.out ≈ emptyLabeledGraph σ
      apply Quotient.mk_out
    type_preserve := List.ofFn_inj.mp rfl
  }

noncomputable def flagType_asEmptyTypeAlgebra
    (σ : FlagType (Fin n₀))
    : FlagAlgebra ∅ₜ
  :=
  let σ₀_finFlag : FinFlag ∅ₜ := ⟨n₀, σ.toEmptyTypeFlag⟩
  ⟦unitVector σ₀_finFlag⟧

notation "⟨" σ "⟩₀" => (flagType_asEmptyTypeAlgebra σ)

theorem one_downward_eq
    : ⟦(1 : FlagAlgebra σ)⟧₀ = (downwardNormalizingFactor (emptyFlag σ) : ℝ) • ⟨σ⟩₀
  := by
  have : (1 : FlagAlgebra σ) = ⟦unitVector ⟨n₀, emptyFlag σ⟩⟧ := by rfl
  rw [this]
  dsimp only [downward, downwardFlagVectorQuot, downwardFlagVector, downwardFlag, Quotient.lift_mk]
  rw [linearExtension_unitVector, rat_smul_eq_real_smul, smul_quot]
  congr
  rw [flagType_asEmptyTypeFlag_eq]
  rfl

theorem flagDensity₁_flagType_asEmptyType_pos
    (F : FinFlag σ)
    : flagDensity₁ σ.toEmptyTypeFlag (unlabel F.2) > 0
  := by
  dsimp only [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity]
  dsimp only [SimpleGraph.toEmptyTypeFlag, unlabel, subflagDensity, labeledSubgraphDensityLifted,
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

-- instance : BorelSpace (FlagDensitySpace σ) :=
--   Subtype.borelSpace fun x ↦ x ∈ FlagDensitySpace σ

noncomputable def FinFlag.toMeasure
    (F : FinFlag ∅ₜ) (σ : FlagType (Fin n₀))
    : Measure (FlagDensitySpace σ)
  := by
  let S := { F' : LabeledSubgraph ∅ₜ F.2.out | F'.IsInduced ∧ Nonempty (F'.coe.graph ≃g σ)}.toFinset
  let f : LabeledSubgraph ∅ₜ F.2.out → FlagDensitySpace σ := fun F' ↦ {
      val := fun G ↦ flagDensity₁ (unlabel G.2) ⟦F'.coe⟧
      property := by
        intro G _
        simp only [Set.mem_Icc]
        rw [← Rat.cast_one]
        simp only [Rat.cast_nonneg, Rat.cast_le]
        constructor
        · exact flagListDensity₁_ge_zero (unlabel G.snd) ⟦F'.coe⟧
        · exact flagListDensity₁_le_one (unlabel G.snd) ⟦F'.coe⟧
    }
  exact ProbabilityTheory.uniformOn (f '' S)

theorem exists_labeledSubgraph_of_flagDensity_pos
    {F : FinFlag ∅ₜ} (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : ∃ F' : LabeledSubgraph ∅ₜ F.2.out, F'.IsInduced ∧ Nonempty (F'.coe.graph ≃g σ)
  := by
  dsimp only [flagDensity₁] at hF
  rw [← subflagDensity_eq_flagListDensity, ← Quotient.out_eq F.2] at hF
  dsimp only [SimpleGraph.toEmptyTypeFlag, subflagDensity, labeledSubgraphDensityLifted,
    labeledSubgraphDensity, Quotient.lift_mk] at hF
  rw [gt_iff_lt, div_pos_iff] at hF
  rcases hF with ⟨hF_num, hF_den⟩ | ⟨hF_num, hF_den⟩
  · dsimp only [labeledSubgraphCount] at hF_num
    simp only [Set.toFinset_setOf, Nat.cast_pos, Finset.card_pos] at hF_num
    obtain ⟨F', hF'⟩ := hF_num
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF'
    exact ⟨F', hF'.1, Nonempty.intro hF'.2.some.graph_iso⟩
  · linarith

theorem FinFlag.toMeasure_isProbabilityMeasure
    (F : FinFlag ∅ₜ) (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : IsProbabilityMeasure (F.toMeasure σ) := by
  apply ProbabilityTheory.uniformOn_isProbabilityMeasure
  · exact Set.toFinite _
  · simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.image_nonempty]
    exact exists_labeledSubgraph_of_flagDensity_pos hF

section

open Filter
open scoped Topology

theorem integral_flagDensitySpace_eq_flagVectorDensity_div
    (F : FinFlag σ) (G : FinFlag ∅ₜ) (hG : G.1 ≥ max F.1 n₀)
    : ∫ (a : FlagDensitySpace σ), a F ∂(G.toMeasure σ)
      = (downwardNormalizingFactor F.2 * flagDensity₁ (unlabel F.2) G.2) /
        (downwardNormalizingFactor (emptyFlag σ) * flagDensity₁ σ.toEmptyTypeFlag G.2)
  := by
  sorry

theorem tendsto_integral_flagDensitySpace_of_converge_flagSeq
    {s : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ} (hσ : φ ⟨σ⟩₀ > 0) (h : ConvergesTo s φ.coe)
    : ∀ (F : FinFlag σ), Tendsto (fun n ↦ ∫ (a : FlagDensitySpace σ), a F ∂((s n).toMeasure σ)) atTop
      (𝓝 ((φ ⟦⟦unitVector F⟧⟧₀) / (φ ⟦(1 : FlagAlgebra σ)⟧₀)))
  := by
  intro F
  obtain ⟨h_inc, h_lim⟩ := flagSeq_convergesTo_iff.mp h
  let f₁ : ℕ → ℝ := fun n ↦ ∫ (a : FlagDensitySpace σ), a F ∂((s n).toMeasure σ)
  let f₂ : ℕ → ℝ := fun n ↦ (downwardNormalizingFactor F.2 * flagDensity₁ (unlabel F.2) (s n).2) /
    (downwardNormalizingFactor (emptyFlag σ) * flagDensity₁ σ.toEmptyTypeFlag (s n).2)
  have h_eventually_eq : ∀ᶠ n in atTop, f₁ n = f₂ n := by
    rw [eventually_atTop]
    obtain ⟨N, hN⟩ := h_inc.eventually_ge (max F.1 n₀)
    use N
    intro n hn
    apply integral_flagDensitySpace_eq_flagVectorDensity_div F (s n) (hN n hn)
  rw [tendsto_congr' h_eventually_eq]
  apply Tendsto.div
  · dsimp [downward, downwardFlagVectorQuot]
    simp_rw [downwardFlagVector_unitVector]
    dsimp [downwardFlag]
    simp_rw [smul_quot, PositiveHom.map_smul]
    apply Tendsto.const_mul
    exact h_lim ⟨F.1, unlabel F.2⟩
  · rw [one_downward_eq, PositiveHom.map_smul]
    apply Tendsto.const_mul
    exact h_lim ⟨n₀, σ.toEmptyTypeFlag⟩
  · rw [one_downward_eq, PositiveHom.map_smul]
    apply mul_ne_zero
    · simp only [ne_eq, Rat.cast_eq_zero]
      apply ne_of_gt downwardNormalizingFactor_emptyFlag_pos
    · exact (ne_of_lt hσ).symm

theorem exists_prob_measure_extend_emptyType_positiveHom
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ∃ (ℙ : Measure (PositiveHomSpace σ)), IsProbabilityMeasure ℙ ∧
      ∀ (f : FlagAlgebra σ), ∫ φ, (PositiveHomSpace.toPosHom φ) f ∂ℙ = (φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀)
  := by
  obtain ⟨s, hs⟩ := positiveHom_as_flagSeq_limit φ₀
  sorry

end

theorem positiveHom_one_downward_pos
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0)
    : φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ > 0
  := by
  rw [one_downward_eq, PositiveHom.map_smul]
  apply mul_pos
  · simp only [Rat.cast_pos]
    exact downwardNormalizingFactor_emptyFlag_pos
  · exact hσ

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
      dsimp only [downward, downwardFlagVectorQuot, downwardFlagVector, Quotient.lift_mk]
      rw [linearExtension_unitVector]
      dsimp only [downwardFlag]
      rw [rat_smul_eq_real_smul, smul_quot, PositiveHom.map_smul, mul_eq_zero]
      right
      apply positiveHom_unitVector_eq_zero φ₀ (flagDensity₁_flagType_asEmptyType_pos F)
      exact Eq.symm hφ₀
    exact le_of_eq (Eq.symm this)
  · obtain ⟨ℙ, _, hℙ⟩ := exists_prob_measure_extend_emptyType_positiveHom hφ₀
    specialize hℙ f
    have hφ₀' : φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ > 0 := positiveHom_one_downward_pos hφ₀
    rw [eq_div_iff (ne_of_gt hφ₀')] at hℙ
    rw [← hℙ, ge_iff_le, mul_nonneg_iff_left_nonneg_of_pos hφ₀']
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
