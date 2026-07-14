import «LeanFlagAlgebras».FlagAlgebra.FlagSequence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! # Random homomorphism ensembles

The measure-theoretic semantics behind the `Forbid` layer's "almost surely" statements.
Given a base positive homomorphism `φ₀` on the empty-type algebra with `φ₀ ⟨σ⟩₀ > 0`, this
file constructs a probability measure `ℙ[φ₀]` on the space of positive homomorphisms of the
typed algebra whose integral recovers the normalized downward operator
`(φ₀ ⟦f⟧₀) / (φ₀ ⟦1⟧₀)` (Theorem 3.5).

The construction goes through: finite flags → PMFs on `FlagDensitySpace` (`FinFlag.toPMF`)
→ a sequence of probability measures along a convergent `FlagSeq` → a Prokhorov-compactness
limit measure whose support lies in the positive-homomorphism space. Downstream this yields
nonnegativity of squares (the Cauchy–Schwarz inequality for `⟦·⟧₀`), the engine for SDP-style
density bounds.
-/

open MeasureTheory

namespace FlagAlgebras

open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- The type graph `σ`, viewed as an untyped (empty-type) flag on its own vertices. -/
def _root_.SimpleGraph.toEmptyTypeFlag
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
    : σ.toEmptyTypeFlag = unlabel (emptyFlag σ)
  := by
  apply Quotient.sound
  apply Nonempty.intro
  rfl

/-- The empty-type flag algebra element `⟨σ⟩₀` representing the type graph `σ`; its value
under a base homomorphism `φ₀` is the density that controls whether the random extension
is well-defined (`φ₀ ⟨σ⟩₀ > 0`). -/
noncomputable def flagType_asEmptyTypeAlgebra
    (σ : FlagType (Fin n₀))
    : FlagAlgebra ∅ₜ
  :=
  let σ₀_finFlag : FinFlag ∅ₜ := ⟨n₀, σ.toEmptyTypeFlag⟩
  ⟦basisVector σ₀_finFlag⟧

-- Notation `⟨σ⟩₀` for the empty-type algebra element of the type graph `σ`.
notation "⟨" σ "⟩₀" => (flagType_asEmptyTypeAlgebra σ)

theorem one_downward_eq
    : ⟦(1 : FlagAlgebra σ)⟧₀ = (downwardNormalizingFactor (emptyFlag σ) : ℝ) • ⟨σ⟩₀
  := by
  have : (1 : FlagAlgebra σ) = ⟦basisVector ⟨n₀, emptyFlag σ⟩⟧ := by rfl
  rw [this]
  dsimp only [downward, downwardFlagVectorQuot, downwardFlagVector, downwardFlag, Quotient.lift_mk]
  rw [linearExtension_basisVector, rat_smul_eq_real_smul, smul_quot]
  congr

theorem flagDensity₁_flagType_asEmptyType_pos
    (F : FinFlag σ)
    : flagDensity₁ σ.toEmptyTypeFlag (unlabel F.2) > 0
  := by
  dsimp only [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity, ← Quotient.out_eq F.2]
  dsimp only [SimpleGraph.toEmptyTypeFlag, unlabel, unlabeledGraphQuot, Quotient.lift_mk,
    subflagDensity, labeledGraphDensityLifted, labeledGraphDensity]
  apply div_pos
  · simp only [Nat.cast_pos, labeledGraphCount]
    rw [Finset.card_pos]
    simp only [Finset.Nonempty, Set.mem_toFinset, Set.mem_setOf_eq]
    let G : LabeledSubgraph ∅ₜ (unlabeledGraph F.2.out) :=
      LabeledSubgraph.inducedLabeledSubgraph _ F.2.out.type_verts (by
        simp only [LabeledGraph.type_verts, unlabeledGraph, Set.image_univ, Matrix.range_empty,
          Set.empty_subset]
      )
    use G
    refine ⟨LabeledSubgraph.inducedLabeledSubgraph_isInduced _ _ _, Nonempty.intro ?_⟩
    simp only [unlabeledGraph, LabeledSubgraph.inducedLabeledSubgraph, LabeledGraph.type_verts,
      SimpleGraph.Subgraph.induce, LabeledSubgraph.coe, G]
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
              refine ⟨?_, ?_, ?_⟩
              · exact Set.mem_range_of_mem_image F.2.out.type_embed Set.univ hv
              · exact Set.mem_range_of_mem_image F.2.out.type_embed Set.univ hw
              · simp only [Set.image_univ, Set.mem_range] at hv hw
                obtain ⟨vi, hvi⟩ := hv
                obtain ⟨wi, hwi⟩ := hw
                subst hvi hwi
                simp_all only [EmbeddingLike.apply_eq_iff_eq, Classical.choose_eq, SimpleGraph.Embedding.map_adj_iff, SimpleGraph.Subgraph.top_adj]
            · rintro ⟨hmv, hmw, h⟩
              simp only [Set.mem_range] at hmv hmw
              obtain ⟨vi, hvi⟩ := hmv
              obtain ⟨wi, hwi⟩ := hmw
              subst hvi hwi
              simp_all only [SimpleGraph.Embedding.map_adj_iff, EmbeddingLike.apply_eq_iff_eq, Classical.choose_eq, SimpleGraph.Subgraph.top_adj]
        }
      type_preserve := List.ofFn_inj.mp rfl
    }
  · simp only [emptyType_size, tsub_zero, Nat.cast_pos, LabeledGraph.size, Fintype.card_fin]
    have : F.1 ≥ n₀ := finFlag_size_ge_n₀ F
    exact Nat.choose_pos this

theorem labelExtensions_nonempty
    {ℓ : ℕ} {F : FlagWithSize ∅ₜ ℓ} (hF : flagDensity₁ σ.toEmptyTypeFlag F > 0)
    : (labelExtensions F σ).Nonempty
  := by
  dsimp only [flagDensity₁] at hF
  rw [← subflagDensity_eq_flagListDensity, ← Quotient.out_eq F] at hF
  dsimp only [SimpleGraph.toEmptyTypeFlag, subflagDensity, labeledGraphDensityLifted,
    labeledGraphDensity, Quotient.lift_mk] at hF
  rw [gt_iff_lt, div_pos_iff] at hF
  rcases hF with ⟨hF_num, hF_den⟩ | ⟨hF_num, hF_den⟩
  · dsimp only [labeledGraphCount] at hF_num
    simp only [Set.toFinset_setOf, Nat.cast_pos, Finset.card_pos] at hF_num
    obtain ⟨G', hG'⟩ := hF_num
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG'
    obtain ⟨hG'_ind, ⟨hG'_iso⟩⟩ := hG'
    dsimp only [labelExtensions]
    let G : LabeledGraph σ (Fin ℓ) := {
      graph := F.out.graph
      type_embed := {
        toFun i := (hG'_iso.graph_iso.invFun i).val
        inj' := by
          intro i j hij
          simp only [LabeledSubgraph.coe_graph, Equiv.invFun_as_coe] at hij
          apply SetCoe.ext at hij
          exact RelIso.injective hG'_iso.graph_iso.symm hij
        map_rel_iff' := by
          intro i j
          simp only [LabeledSubgraph.coe_graph, Equiv.invFun_as_coe, Function.Embedding.coeFn_mk]
          constructor <;> intro h
          · rw [← RelIso.apply_symm_apply hG'_iso.graph_iso i, ← RelIso.apply_symm_apply hG'_iso.graph_iso j]
            rw [RelIso.map_rel_iff hG'_iso.graph_iso, LabeledSubgraph.coe_adj_iff]
            exact (SimpleGraph.Subgraph.IsInduced.adj hG'_ind).mpr h
          · apply SimpleGraph.Subgraph.Adj.adj_sub'
            rw [← LabeledSubgraph.coe_adj_iff, ← RelIso.map_rel_iff hG'_iso.graph_iso]
            rw [← RelIso.apply_symm_apply hG'_iso.graph_iso i, ← RelIso.apply_symm_apply hG'_iso.graph_iso j] at h
            exact h
      }
    }
    use ⟦G⟧
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Quotient.out_eq F]
    apply Quotient.sound
    calc
      _ ∼f unlabeledGraph G := by
        apply unlabeledGraph_iso
        exact flagEqv.refl G
      _ ∼f F.out := by
        apply Nonempty.intro
        dsimp only [LabeledSubgraph.coe_graph, Equiv.invFun_as_coe, unlabeledGraph, G]
        exact {
          graph_iso := SimpleGraph.Iso.refl
          type_preserve := List.ofFn_inj.mp rfl
        }
  · linarith

/-! ## From finite flags to PMFs on `FlagDensitySpace`

A large untyped flag `G` with `flagDensity₁ σ.toEmptyTypeFlag G > 0` is turned into a finite
probability distribution on `FlagDensitySpace σ`: pick a random labeling extension of `G`
weighted by its downward normalizing factor, then read off the resulting density vector.
-/

/-- Maps a sized typed flag to the density-space point recording its `flagDensity₁` against
every untyped flag. -/
noncomputable def funFromFlagWithSizeToFlagDensitySpace
    (σ : FlagType (Fin n₀)) (ℓ : ℕ)
    : FlagWithSize σ ℓ → FlagDensitySpace σ
  := fun F' ↦ {
    val := fun G' ↦ flagDensity₁ G'.2 F'
    property := by
      intro G' _
      simp only [Set.mem_Icc]
      rw [← Rat.cast_one]
      simp only [Rat.cast_nonneg, Rat.cast_le]
      constructor
      · exact flagListDensity₁_ge_zero G'.snd F'
      · exact flagListDensity₁_le_one G'.snd F'
  }

/-- The random-labeling distribution on `FlagDensitySpace σ` induced by an untyped finite
flag `F` of positive `σ`-density: a labeling extension is drawn with probability proportional
to its downward normalizing factor. -/
noncomputable def FinFlag.toPMF
    (F : FinFlag ∅ₜ) (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : PMF (FlagDensitySpace σ)
  := by
  let L := labelExtensions F.2 σ
  let f := funFromFlagWithSizeToFlagDensitySpace σ F.1
  let S : Finset (FlagDensitySpace σ) := (f '' L).toFinset
  let dnf_sum := fun a ↦ ∑ F' ∈ L with f F' = a, (downwardNormalizingFactor F' : ℝ)
  let dnf_total := ∑ F' ∈ L, (downwardNormalizingFactor F' : ℝ)
  let g : FlagDensitySpace σ → ENNReal := fun a ↦ if a ∈ S
    then ENNReal.ofReal (dnf_sum a / dnf_total)
    else 0
  have dnf_total_ne_zero : dnf_total ≠ 0 := by
    apply ne_of_gt
    apply Finset.sum_pos
    · intro F' hF'
      simp only [Rat.cast_pos]
      exact downwardNormalizingFactor_pos F'
    · exact labelExtensions_nonempty hF
  have g_nonneg : ∀ a ∈ S, 0 ≤ dnf_sum a / dnf_total := by
    intro a ha
    apply div_nonneg
    all_goals {
      apply Finset.sum_nonneg
      intros
      rw [Rat.cast_nonneg]
      exact downwardNormalizingFactor_nonneg _
    }
  have g_sum : ∑ a ∈ S, g a = 1 := by
    dsimp only [g]
    rw [← ENNReal.toReal_eq_one_iff]
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    have : (∑ a ∈ S, ENNReal.ofReal (dnf_sum a / dnf_total)).toReal =
            ∑ a ∈ S, dnf_sum a / dnf_total := by
      rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [ENNReal.toReal_ofReal (g_nonneg a ha)]
    rw [this]
    rw [← Finset.sum_div, div_eq_iff dnf_total_ne_zero, one_mul]
    dsimp only [S, dnf_sum, dnf_total]
    rw [Finset.sum_fiberwise_eq_sum_filter]
    congr 1
    ext F'
    constructor <;> intro hF'
    · simp only [Finset.mem_filter] at hF'
      exact hF'.1
    · simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.mem_image, Finset.mem_filter]
      constructor
      · exact hF'
      · use F'
  have g_other : ∀ a ∉ S, g a = 0 := by
    intro a ha
    simp only [g, if_neg ha]
  exact PMF.ofFinset g S g_sum g_other

theorem FinFlag.toPMF_support
    (F : FinFlag ∅ₜ) (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : (F.toPMF hF).support = (funFromFlagWithSizeToFlagDensitySpace σ F.1 '' labelExtensions F.2 σ).toFinset
  := by
  dsimp only [FinFlag.toPMF, PMF.support, PMF.ofFinset]
  ext a
  simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.mem_image, DFunLike.coe,
    Function.mem_support, Finset.coe_image, Set.mem_image, Finset.mem_coe, ite_eq_right_iff,
    ne_eq, ENNReal.ofReal_eq_zero, forall_exists_index, and_imp, not_forall, not_le]
  constructor
  · intro ⟨G, hG₁, hG₂, _⟩
    use G, hG₁, hG₂
  · intro ⟨G, hG₁, hG₂⟩
    use G, hG₁, hG₂
    apply div_pos
    · apply Finset.sum_pos'
      · intro G' hG'
        rw [Rat.cast_nonneg]
        exact downwardNormalizingFactor_nonneg G'
      · use G
        constructor
        · simp only [Finset.mem_filter, hG₁, hG₂, and_self]
        · rw [Rat.cast_pos]
          exact downwardNormalizingFactor_pos G
    · apply Finset.sum_pos'
      · intro G' hG'
        rw [Rat.cast_nonneg]
        exact downwardNormalizingFactor_nonneg G'
      · use G
        constructor
        · exact hG₁
        · rw [Rat.cast_pos]
          exact downwardNormalizingFactor_pos G

/-- The probability measure on `FlagDensitySpace σ` associated with `FinFlag.toPMF`. -/
noncomputable def FinFlag.toMeasure
    (F : FinFlag ∅ₜ) (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : Measure (FlagDensitySpace σ)
  :=
  (F.toPMF hF).toMeasure

instance FinFlag.toMeasure_isProbabilityMeasure
    (F : FinFlag ∅ₜ) (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : IsProbabilityMeasure (F.toMeasure hF)
  :=
  PMF.toMeasure.isProbabilityMeasure (F.toPMF hF)

noncomputable def FinFlag.toProbMeasure
    (F : FinFlag ∅ₜ) (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    : ProbabilityMeasure (FlagDensitySpace σ)
  :=
  ⟨F.toMeasure hF, FinFlag.toMeasure_isProbabilityMeasure F hF⟩

section

open Filter
open scoped Topology

lemma tsum_ite_eq_sum
    {α R : Type} [AddCommMonoid R] [TopologicalSpace R] (S : Finset α) (f : α → R)
    : (∑' a, if a ∈ S then f a else 0) = ∑ a ∈ S, f a
  := by
  classical
  have h : ∀ a ∉ S, (if a ∈ S then f a else 0) = 0 := by
    intro a ha
    simp [ha]
  simpa using (tsum_eq_sum (s:=S) (f:=fun a => if a ∈ S then f a else 0) h)

/-- Core identity: the expected `F`-density under `G.toMeasure` equals the downward density
ratio `(dnf F · dens(unlabel F, G)) / (dnf σ · dens(σ, G))`. This is what makes the random
ensemble compute the normalized downward operator. -/
theorem integral_flagDensitySpace_eq_flagVectorDensity_div
    {F : FinFlag σ} {G : FinFlag ∅ₜ}
    (hG : flagDensity₁ σ.toEmptyTypeFlag G.2 > 0) (hG_size : G.1 ≥ max F.1 n₀)
    : ∫ (a : FlagDensitySpace σ), a F ∂(G.toMeasure hG)
      = (downwardNormalizingFactor F.2 * flagDensity₁ (unlabel F.2) G.2) /
        (downwardNormalizingFactor (emptyFlag σ) * flagDensity₁ σ.toEmptyTypeFlag G.2)
  := by
  dsimp only [FinFlag.toMeasure]
  have ha_integrable : Integrable (fun a ↦ a F) (G.toPMF hG).toMeasure := by
    have ha_bdd : ∀ᵐ (a : FlagDensitySpace σ) ∂(G.toPMF hG).toMeasure, ‖a F‖ ≤ 1 := by
      apply ae_of_all (G.toPMF hG).toMeasure
      intro a
      simp only [Real.norm_eq_abs]
      exact flagDensitySpace_abs_le_one a F
    apply Integrable.of_bound
    · apply Measurable.aestronglyMeasurable
      apply Measurable.eval
      exact Measurable.of_comap_le fun s a ↦ a
    · exact ha_bdd
  rw [PMF.integral_eq_tsum _ _ ha_integrable]
  dsimp only [FinFlag.toPMF]
  simp only [PMF.ofFinset_apply, smul_eq_mul]
  simp_rw [apply_ite ENNReal.toReal]
  conv =>
    lhs; congr; ext a; lhs; arg 2
    rw [ENNReal.toReal_ofReal (by apply div_nonneg; all_goals {
      apply Finset.sum_nonneg
      intros
      rw [Rat.cast_nonneg]
      exact downwardNormalizingFactor_nonneg _
    })]
  simp only [ENNReal.toReal_zero, ite_mul, zero_mul]
  let L := labelExtensions G.2 σ
  let g := funFromFlagWithSizeToFlagDensitySpace σ G.1
  let dnf_sum := fun a ↦ ∑ G' ∈ L with g G' = a, (downwardNormalizingFactor G' : ℝ)
  let dnf_total := ∑ F' ∈ L, (downwardNormalizingFactor F' : ℝ)
  calc
    _ = ∑ a ∈ (g '' L).toFinset, dnf_sum a / dnf_total * a F := by
      nth_rw 2 [← tsum_ite_eq_sum]
      congr!
    _ = ∑ G' ∈ L, (downwardNormalizingFactor G' : ℝ) * (g G') F / dnf_total := by
      rw [Set.toFinset_image, Finset.toFinset_coe]
      apply Finset.sum_image'
      intro G' hG'
      rw [mul_comm, mul_div, ← Finset.sum_div]
      congr
      rw [mul_comm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro G'' hG''
      simp only [Finset.mem_filter] at hG''
      rw [hG''.2]
    _ = _ := ?_
  rw [← Rat.cast_mul, mul_comm]
  rw [flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions _ _ (le_of_max_le_left hG_size)]
  simp only [Rat.cast_sum, Rat.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro G' hG'
  have h_nonzero₁ : dnf_total ≠ 0 := by
    apply ne_of_gt <| Finset.sum_pos _ (labelExtensions_nonempty hG)
    intro G'' hG''
    simp only [Rat.cast_pos]
    exact downwardNormalizingFactor_pos G''
  have h_nonzero₂ : (downwardNormalizingFactor (emptyFlag σ) : ℝ) * (flagDensity₁ (SimpleGraph.toEmptyTypeFlag σ) G.2 : ℝ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Rat.cast_eq_zero, not_or]
    constructor <;> apply ne_of_gt
    · exact downwardNormalizingFactor_emptyFlag_pos
    · exact hG
  have : g G' F = flagDensity₁ F.2 G' := rfl
  rw [this, div_eq_div_iff h_nonzero₁ h_nonzero₂]
  congr 1
  · rw [mul_comm]
  · rw [← Rat.cast_mul, mul_comm, flagType_asEmptyTypeFlag_eq]
    rw [flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions _ _ (le_of_max_le_right hG_size)]
    simp_rw [Rat.cast_sum, flagDensity_empty, one_mul]
    rfl

/-! ## Passing to the limit along a convergent flag sequence -/

/-- The sequence `n ↦ 𝔼[ a F ]` of expected `F`-densities along the measures of a flag
sequence `s`. -/
noncomputable def integralFlagDensitySpaceSeq
    {s : FlagSeq ∅ₜ} (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0) (F : FinFlag σ)
    : ℕ → ℝ
  :=
  fun n ↦ ∫ (a : FlagDensitySpace σ), a F ∂((s n).toMeasure (hs n))

/- Lemma 3.11 -/
/-- Lemma 3.11: along a flag sequence converging to `φ`, the expected `F`-densities tend to
the normalized downward value `(φ ⟦⟦basisVector F⟧⟧₀) / (φ ⟦1⟧₀)`. -/
theorem tendsto_integral_flagDensitySpace_of_converge_flagSeq
    {s : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ} (hσ : φ ⟨σ⟩₀ > 0)
    (hs_conv : ConvergesTo s φ.coe) (hs_den : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    : ∀ (F : FinFlag σ), Tendsto (integralFlagDensitySpaceSeq hs_den F) atTop
      (𝓝 ((φ ⟦⟦basisVector F⟧⟧₀) / (φ ⟦(1 : FlagAlgebra σ)⟧₀)))
  := by
  intro F
  obtain ⟨h_inc, h_lim⟩ := flagSeq_convergesTo_iff.mp hs_conv
  let f : ℕ → ℝ := fun n ↦ (downwardNormalizingFactor F.2 * flagDensity₁ (unlabel F.2) (s n).2) /
    (downwardNormalizingFactor (emptyFlag σ) * flagDensity₁ σ.toEmptyTypeFlag (s n).2)
  have h_eventually_eq : ∀ᶠ n in atTop, integralFlagDensitySpaceSeq hs_den F n = f n := by
    rw [eventually_atTop]
    obtain ⟨N, hN⟩ := h_inc.eventually_ge (max F.1 n₀)
    use N
    intro n hn
    exact integral_flagDensitySpace_eq_flagVectorDensity_div (hs_den n) (hN n hn)
  rw [tendsto_congr' h_eventually_eq]
  apply Tendsto.div
  · dsimp only [downward, downwardFlagVectorQuot, Quotient.lift_mk]
    simp_rw [downwardFlagVector_basisVector]
    dsimp only [downwardFlag, rat_smul_eq_real_smul]
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

theorem eventually_flagDensity_pos_of_converge_flagSeq
    {s : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ} (hσ : φ ⟨σ⟩₀ > 0) (h : ConvergesTo s φ.coe)
    : ∀ᶠ n in atTop, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0
  := by
  obtain ⟨h_inc, h_lim⟩ := flagSeq_convergesTo_iff.mp h
  specialize h_lim ⟨n₀, σ.toEmptyTypeFlag⟩
  apply Tendsto.eventually_const_lt hσ at h_lim
  dsimp only [flagDensitySeq] at h_lim
  simp_all only [Rat.cast_pos]

lemma tendsto_comp_of_strictMono
    {r : ℝ} {s : ℕ → ℝ} {ϕ : ℕ → ℕ} (hϕ : StrictMono ϕ) (h_lim : Tendsto s atTop (𝓝 r))
    : Tendsto (s ∘ ϕ) atTop (𝓝 r)
  := by
  exact h_lim.comp (StrictMono.tendsto_atTop hϕ)

lemma convergesTo_comp_of_strictMono
    {s : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ} {ϕ : ℕ → ℕ} (hϕ : StrictMono ϕ)
    (h : ConvergesTo s φ.coe)
    : ConvergesTo (s ∘ ϕ) φ.coe
  := by
  rw [flagSeq_convergesTo_iff] at *
  obtain ⟨h_inc, h_lim⟩ := h
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply h_inc
    exact hϕ (lt_add_one n)
  · intro F
    exact tendsto_comp_of_strictMono hϕ (h_lim F)

/-- For any `φ` with `φ ⟨σ⟩₀ > 0`, there is a flag sequence converging to `φ` whose every
term has positive `σ`-density (so its measures are defined). -/
theorem exists_converge_flagSeq_with_flagDensity_pos
    {φ : PositiveHom ∅ₜ} (hσ : φ ⟨σ⟩₀ > 0)
    : ∃ (s : FlagSeq ∅ₜ), ConvergesTo s φ.coe ∧ ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0
  := by
  obtain ⟨s, hs_conv⟩ := positiveHom_as_flagSeq_limit φ
  have h_eventually := eventually_flagDensity_pos_of_converge_flagSeq hσ hs_conv
  rw [eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  let ϕ : ℕ → ℕ := fun n ↦ N + n
  have hϕ : StrictMono ϕ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.lt_add_one (N + n)
  use s ∘ ϕ
  constructor
  · exact convergesTo_comp_of_strictMono hϕ hs_conv
  · intro n
    exact hN (N + n) (Nat.le_add_right N n)

instance : TopologicalSpace (Measure (FlagDensitySpace σ))
  :=
  Preorder.topology (Measure (FlagDensitySpace σ))

/-! ## Prokhorov compactness and the limit measure -/

/-- The sequence of probability measures on `FlagDensitySpace σ` induced by a flag sequence. -/
noncomputable def FlagSeq.toProbMeasureSeq
    (s : FlagSeq ∅ₜ) (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    : ℕ → ProbabilityMeasure (FlagDensitySpace σ)
  :=
  fun n ↦ (s n).toProbMeasure (hs n)

noncomputable instance : MetricSpace (ProbabilityMeasure (FlagDensitySpace σ)) :=
  TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure ↑(FlagDensitySpace σ))

/-- Prokhorov tightness: the space of probability measures on the compact `FlagDensitySpace σ`
is sequentially compact, so every measure sequence has a weakly convergent subsequence. -/
theorem flagDensitySpace_probMeasure_isSeqCompact
    : IsSeqCompact (Set.univ : Set (ProbabilityMeasure (FlagDensitySpace σ)))
  := by
  let S : Set (ProbabilityMeasure (FlagDensitySpace σ)) := Set.univ
  show IsSeqCompact S
  have hS_closure : S = closure S := by
    simp only [isClosed_univ, IsClosed.closure_eq, S]
  rw [hS_closure]
  apply IsCompact.isSeqCompact
  exact isCompact_closure_of_isTightMeasureSet IsTightMeasureSet.of_compactSpace

theorem exists_convergent_subseq_probMeasure_of_flagSeq
    {s : FlagSeq ∅ₜ} (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    : ∃ (ϕ : ℕ → ℕ) (ℙ : ProbabilityMeasure (FlagDensitySpace σ)),
      StrictMono ϕ ∧ Tendsto (s.toProbMeasureSeq hs ∘ ϕ) atTop (𝓝 ℙ)
  := by
  have := @flagDensitySpace_probMeasure_isSeqCompact _ σ
  specialize @this (s.toProbMeasureSeq hs) (fun n ↦ trivial)
  obtain ⟨ℙ, _, ϕ, _⟩ := this
  use ϕ, ℙ

/-- Combines convergence and tightness: there is a flag sequence converging to `φ` whose
probability measures weakly converge to some limit measure `ℙ`. -/
theorem exists_converge_flagSeq_and_probMeasure_tendsto
    {φ : PositiveHom ∅ₜ} (hσ : φ ⟨σ⟩₀ > 0)
    : ∃ (s : FlagSeq ∅ₜ) (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
      (ℙ : ProbabilityMeasure (FlagDensitySpace σ)),
      ConvergesTo s φ.coe ∧ Tendsto (s.toProbMeasureSeq hs) atTop (𝓝 ℙ)
  := by
  obtain ⟨s, hs_conv, hs_den⟩ := exists_converge_flagSeq_with_flagDensity_pos hσ
  obtain ⟨ϕ, ℙ, hϕ, hℙ⟩ := exists_convergent_subseq_probMeasure_of_flagSeq hs_den
  use s ∘ ϕ, fun n ↦ hs_den (ϕ n), ℙ
  constructor
  · exact convergesTo_comp_of_strictMono hϕ hs_conv
  · exact hℙ

/-! ## Measurability and the support of the limit measure

These lemmas establish that the defining relations of a positive homomorphism (linearity
`zeroSpaceProp`, normalization `oneProp`, multiplicativity `mulProp`) cut out measurable sets,
and that each holds almost surely under the limit measure — so the limit is supported on the
positive-homomorphism space.
-/

/-- Evaluation of a density-space point at a fixed flag `F` is measurable. -/
lemma flagDensitySpace_eval_measurable
    (F : FinFlag σ)
    : Measurable fun a : FlagDensitySpace σ ↦ a F
  := by
  apply Measurable.eval
  exact Measurable.of_comap_le fun s a ↦ a

lemma flagDensitySpace_sum_measurable
    {F : FinFlag σ} {ℓ : ℕ}
    : Measurable fun (a : FlagDensitySpace σ) ↦ ∑ G, ↑(flagDensity₁ F.2 G) * a ⟨ℓ, G⟩
  := by
  apply Finset.measurable_sum Finset.univ
  intro G _
  apply Measurable.mul
  · exact measurable_const
  · exact flagDensitySpace_eval_measurable _

lemma flagDensitySpace_eq_sum_measurableSet
    {F : FinFlag σ} {ℓ : ℕ}
    : MeasurableSet {a : FlagDensitySpace σ | a F = ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G * a ⟨ℓ, G⟩}
  :=
  measurableSet_eq_fun (flagDensitySpace_eval_measurable _) flagDensitySpace_sum_measurable

lemma zeroSpaceProp_measurableSet
    : MeasurableSet {a : FlagDensitySpace σ | zeroSpaceProp ⇑a}
  := by
  rw [zeroSpacePropSet_eq_iInter]
  iterate 3 (apply MeasurableSet.iInter; intro)
  exact flagDensitySpace_eq_sum_measurableSet

lemma oneProp_measurableSet
    : MeasurableSet {a : FlagDensitySpace σ | oneProp ⇑a}
  := by
  apply measurableSet_eq_fun
  · exact flagDensitySpace_eval_measurable _
  · exact measurable_const

lemma flagDensitySpace_mul_eq_sum_measurableSet
    {F₁ F₂ : FinFlag σ}
    : MeasurableSet {a : FlagDensitySpace σ | a F₁ * a F₂ = ∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩}
  := by
  apply measurableSet_eq_fun
  · apply Measurable.mul <;> exact flagDensitySpace_eval_measurable _
  · apply Finset.measurable_sum Finset.univ
    intro G _
    apply Measurable.mul
    · exact measurable_const
    · exact flagDensitySpace_eval_measurable _

lemma mulProp_measurableSet
    : MeasurableSet {a : FlagDensitySpace σ | mulProp ⇑a}
  := by
  rw [mulPropSet_eq_iInter]
  iterate 2 (apply MeasurableSet.iInter; intro)
  exact flagDensitySpace_mul_eq_sum_measurableSet

lemma prob_inter_eq_one_of_prob_eq_one
    {α : Type} [MeasurableSpace α] {ℙ : ProbabilityMeasure α} {A B : Set α}
    (hA_measurable : MeasurableSet A) (hB_measurable : MeasurableSet B)
    (hA : ℙ A = 1) (hB : ℙ B = 1)
    : ℙ (A ∩ B) = 1
  := by
  obtain ⟨μ, hμ⟩ := ℙ
  simp_all only [ProbabilityMeasure.mk_apply, ENNReal.toNNReal_eq_one_iff]
  rw [← prob_compl_eq_zero_iff (by measurability), Set.compl_inter]
  apply measure_union_null
  · exact (prob_compl_eq_zero_iff hA_measurable).mpr hA
  · exact (prob_compl_eq_zero_iff hB_measurable).mpr hB

lemma prob_iInter_eq_one_of_all_prob_eq_one
    {α ι : Type} [MeasurableSpace α] [Countable ι] {ℙ : ProbabilityMeasure α} {A : ι → Set α}
    (hA_measurable : ∀ i, MeasurableSet (A i)) (hA : ∀ i, ℙ (A i) = 1)
    : ℙ (⋂ i, A i) = 1
  := by
  obtain ⟨μ, hμ⟩ := ℙ
  simp_all only [ProbabilityMeasure.mk_apply, ENNReal.toNNReal_eq_one_iff]
  rw [← prob_compl_eq_zero_iff (MeasurableSet.iInter hA_measurable), Set.compl_iInter]
  apply measure_iUnion_null
  intro i
  exact (prob_compl_eq_zero_iff (hA_measurable i)).mpr (hA i)

lemma ae_zero_of_integral_eq_zero
    {α : Type} [MeasurableSpace α] {ℙ : ProbabilityMeasure α}
    {f : α → ℝ} (fpos : ∀ a, 0 ≤ f a) (hf_measurable : Measurable f)
    (hf_integrable : Integrable f ℙ) (hf : ∫ a, f a ∂ℙ = 0)
    : ℙ {a | f a = 0} = 1
  := by
  obtain ⟨μ, hμ⟩ := ℙ
  simp_all only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.mk_apply]
  rw [ENNReal.toNNReal_eq_one_iff, ← mem_ae_iff_prob_eq_one]
  show f =ᶠ[ae μ] 0
  rw [← integral_eq_zero_iff_of_nonneg fpos hf_integrable]
  · exact hf
  · exact measurableSet_eq_fun hf_measurable measurable_const

lemma abs_measurable
    {α : Type} [MeasurableSpace α] {f : α → ℝ}
    (hf_measurable : Measurable f)
    : Measurable fun a ↦ |f a|
  :=
  Measurable.sup hf_measurable (Measurable.neg hf_measurable)

lemma flagDensitySpace_sub_sum_abs_measurable
    {F : FinFlag σ} {ℓ : ℕ}
    : Measurable fun (a : FlagDensitySpace σ) ↦ |a F - ∑ G, ↑(flagDensity₁ F.2 G) * a ⟨ℓ, G⟩|
  := by
  apply abs_measurable
  exact Measurable.sub (flagDensitySpace_eval_measurable _) flagDensitySpace_sum_measurable

lemma flagDensitySpace_sub_sum_abs_bounded
    (a : FlagDensitySpace σ) (F : FinFlag σ) (ℓ : ℕ)
    : |a F - ∑ G, (flagDensity₁ F.2 G : ℝ) * a ⟨ℓ, G⟩| ≤ 1 + Fintype.card (FlagWithSize σ ℓ)
  := by
  calc
    _ ≤ |a F| + |∑ G, (flagDensity₁ F.2 G : ℝ) * a ⟨ℓ, G⟩| := abs_sub _ _
    _ ≤ 1 + Fintype.card (FlagWithSize σ ℓ) := by
      apply add_le_add (flagDensitySpace_abs_le_one a F)
      calc
        _ ≤ ∑ (G : FlagWithSize σ ℓ), |(flagDensity₁ F.2 G : ℝ) * a ⟨ℓ, G⟩| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ (G : FlagWithSize σ ℓ), 1 := by
          apply Finset.sum_le_sum
          intro G _
          rw [abs_mul, ← one_mul 1]
          apply mul_le_mul _ _ (abs_nonneg _) (by norm_num)
          · rw [abs_le]
            constructor
            · calc
                -1 ≤ 0 := by norm_num
                _ ≤ (flagDensity₁ F.2 G : ℝ) := by
                  rw [Rat.cast_nonneg]
                  exact flagListDensity₁_ge_zero F.2 G
            · rw [← Rat.cast_one, Rat.cast_le]
              exact flagListDensity₁_le_one F.2 G
          · exact flagDensitySpace_abs_le_one a ⟨ℓ, G⟩
        _ = Fintype.card (FlagWithSize σ ℓ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma flagDensitySpace_sub_sum_abs_integrable
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)} {F : FinFlag σ} {ℓ : ℕ}
    : Integrable (fun (a : FlagDensitySpace σ) ↦ |a F - ∑ G, (flagDensity₁ F.2 G : ℝ) * a ⟨ℓ, G⟩|) ℙ
  := by
  have h_bound : ∀ᵐ (a : FlagDensitySpace σ) ∂ℙ.val,
      ‖|a F - ∑ G, (flagDensity₁ F.2 G : ℝ) * a ⟨ℓ, G⟩|‖ ≤ 1 + Fintype.card (FlagWithSize σ ℓ) := by
    simp only [Real.norm_eq_abs, abs_abs, ProbabilityMeasure.val_eq_to_measure]
    apply ae_of_all ℙ.val
    intro a
    exact flagDensitySpace_sub_sum_abs_bounded a F ℓ
  have : IsFiniteMeasure ℙ.val := by
    obtain ⟨μ, hμ⟩ := ℙ
    simp_all only [Real.norm_eq_abs, abs_abs]
    exact CompactSpace.isFiniteMeasure
  exact Integrable.of_bound (Measurable.aestronglyMeasurable flagDensitySpace_sub_sum_abs_measurable)
    ((1 : ℝ) + Fintype.card (FlagWithSize σ ℓ)) h_bound

lemma flagDensitySpace_one_sub_one_measurable
    : Measurable fun (a : FlagDensitySpace σ) ↦ |a 1 - 1|
  := by
  apply abs_measurable
  exact Measurable.sub (flagDensitySpace_eval_measurable _) measurable_const

lemma flagDensitySpace_one_sub_one_bounded
    (a : FlagDensitySpace σ)
    : |a 1 - 1| ≤ 2
  := by
  calc
    _ ≤ |a 1| + |1| := abs_sub _ _
    _ ≤ 1 + |1| := by
      apply add_le_add (flagDensitySpace_abs_le_one a 1) (by rfl)
    _ = 2 := by norm_num

lemma flagDensitySpace_one_sub_one_integrable
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)}
    : Integrable (fun (a : FlagDensitySpace σ) ↦ |a 1 - 1|) ℙ
  := by
  have h_bound : ∀ᵐ (a : FlagDensitySpace σ) ∂ℙ.val,
      ‖|a 1 - 1|‖ ≤ 2 := by
    simp only [Real.norm_eq_abs, abs_abs, ProbabilityMeasure.val_eq_to_measure]
    apply ae_of_all ℙ.val
    intro a
    exact flagDensitySpace_one_sub_one_bounded a
  have : IsFiniteMeasure ℙ.val := by
    obtain ⟨μ, hμ⟩ := ℙ
    simp_all only [Real.norm_eq_abs, abs_abs]
    exact CompactSpace.isFiniteMeasure
  exact Integrable.of_bound (Measurable.aestronglyMeasurable flagDensitySpace_one_sub_one_measurable)
    (2 : ℝ) h_bound

lemma flagDensitySpace_mul_sub_sum_abs_measurable
    {F₁ F₂ : FinFlag σ}
    : Measurable fun (a : FlagDensitySpace σ) ↦
      |a F₁ * a F₂ - ∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩|
  := by
  apply abs_measurable
  exact Measurable.sub
    (Measurable.mul (flagDensitySpace_eval_measurable _) (flagDensitySpace_eval_measurable _))
    (Finset.measurable_sum Finset.univ fun G _ ↦
      Measurable.mul measurable_const (flagDensitySpace_eval_measurable _))

lemma flagDensitySpace_mul_sub_sum_abs_bounded
    (a : FlagDensitySpace σ) (F₁ F₂ : FinFlag σ)
    : |a F₁ * a F₂ - ∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩| ≤
      1 + Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀))
  := by
  calc
    _ ≤ |a F₁ * a F₂| + |∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩| := abs_sub _ _
    _ ≤ 1 + Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀)) := by
      apply add_le_add
      · rw [abs_mul, ← one_mul 1]
        exact mul_le_mul (flagDensitySpace_abs_le_one a F₁) (flagDensitySpace_abs_le_one a F₂) (abs_nonneg _) (by norm_num)
      calc
        _ ≤ ∑ (G : FlagWithSize σ (F₁.1 + F₂.1 - n₀)), |flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ (G : FlagWithSize σ (F₁.1 + F₂.1 - n₀)), 1 := by
          apply Finset.sum_le_sum
          intro G _
          rw [abs_mul, ← one_mul 1]
          apply mul_le_mul _ _ (abs_nonneg _) (by norm_num)
          · rw [abs_le]
            constructor
            · calc
                -1 ≤ 0 := by norm_num
                _ ≤ (flagDensity₂ F₁.2 F₂.2 G : ℝ) := by
                  rw [Rat.cast_nonneg]
                  exact flagListDensity₂_ge_zero F₁.2 F₂.2 G
            · rw [← Rat.cast_one, Rat.cast_le]
              exact flagListDensity₂_le_one F₁.2 F₂.2 G
          · exact flagDensitySpace_abs_le_one a ⟨F₁.1 + F₂.1 - n₀, G⟩
        _ = Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma flagDensitySpace_mul_sub_sum_abs_integrable
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)} {F₁ F₂ : FinFlag σ}
    : Integrable (fun (a : FlagDensitySpace σ) ↦
      |a F₁ * a F₂ - ∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩|) ℙ
  := by
  have h_bound : ∀ᵐ (a : FlagDensitySpace σ) ∂ℙ.val,
      ‖|a F₁ * a F₂ - ∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩|‖ ≤
      1 + Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀)) := by
    simp only [Real.norm_eq_abs, abs_abs, ProbabilityMeasure.val_eq_to_measure]
    apply ae_of_all ℙ.val
    intro a
    exact flagDensitySpace_mul_sub_sum_abs_bounded a F₁ F₂
  have : IsFiniteMeasure ℙ.val := by
    obtain ⟨μ, hμ⟩ := ℙ
    simp_all only [Real.norm_eq_abs, abs_abs]
    exact CompactSpace.isFiniteMeasure
  exact Integrable.of_bound (Measurable.aestronglyMeasurable flagDensitySpace_mul_sub_sum_abs_measurable)
    ((1 : ℝ) + Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀))) h_bound

/-- Evaluation at `F` as a bounded continuous function, the test functions used with weak
convergence of probability measures. -/
def FinFlag.toBoundedContinuousFun
    (F : FinFlag σ)
    : BoundedContinuousFunction (FlagDensitySpace σ) ℝ
  := {
    toFun := fun a ↦ a F
    continuous_toFun := by
      rw [continuous_iff_seqContinuous]
      intro s a hs_lim
      rw [tendsto_subtype_rng, tendsto_pi_nhds] at hs_lim
      exact hs_lim F
    map_bounded' := by
      use 1
      intro a b
      apply Real.dist_le_of_mem_Icc_01
      · exact flagDensitySpace_mem_Icc_zero_one a F
      · exact flagDensitySpace_mem_Icc_zero_one b F
  }

/-- The limit measure assigns probability 1 to the set where the linearity relation
(`zeroSpaceProp`) holds. -/
theorem zeroSpacePropSet_prob_eq_one
    {s : FlagSeq ∅ₜ}
    (hs_inc : Increases s) (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)} (hs_tendsto : Tendsto (s.toProbMeasureSeq hs) atTop (𝓝 ℙ))
    : ℙ {a | zeroSpaceProp a} = 1
  := by
  rw [zeroSpacePropSet_eq_iInter]
  apply prob_iInter_eq_one_of_all_prob_eq_one <;> intro F
  · exact MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦
    flagDensitySpace_eq_sum_measurableSet
  apply prob_iInter_eq_one_of_all_prob_eq_one <;> intro ℓ
  · exact MeasurableSet.iInter fun _ ↦ flagDensitySpace_eq_sum_measurableSet
  rw [Set.iInter_setOf]
  by_cases hℓ : F.1 ≤ ℓ
  · simp_all only [forall_const]
    conv =>
      lhs; rhs; rhs; ext a
      rw [← sub_eq_zero, ← abs_eq_zero]
    apply ae_zero_of_integral_eq_zero (fun a ↦ abs_nonneg _) flagDensitySpace_sub_sum_abs_measurable flagDensitySpace_sub_sum_abs_integrable
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hs_tendsto
    let f : BoundedContinuousFunction (FlagDensitySpace σ) ℝ := {
      toFun := fun a ↦ |a F - ∑ G, (flagDensity₁ F.2 G : ℝ) * a ⟨ℓ, G⟩|
      continuous_toFun := by
        apply Continuous.comp' continuous_abs
        apply Continuous.sub F.toBoundedContinuousFun.continuous_toFun
        apply continuous_finset_sum Finset.univ
        intro G _
        apply Continuous.mul continuous_const
        exact (FinFlag.toBoundedContinuousFun ⟨ℓ, G⟩).continuous_toFun
      map_bounded' := by
        use 1 + Fintype.card (FlagWithSize σ ℓ)
        intro a b
        rw [← sub_zero (1 + Fintype.card (FlagWithSize σ ℓ) : ℝ)]
        apply Real.dist_le_of_mem_Icc <;> simp only [Set.mem_Icc, abs_nonneg, true_and]
        · exact flagDensitySpace_sub_sum_abs_bounded a F ℓ
        · exact flagDensitySpace_sub_sum_abs_bounded b F ℓ
    }
    specialize hs_tendsto f
    apply tendsto_nhds_unique hs_tendsto
    apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ ℓ
    intro n hn
    have fpos : 0 ≤ f := fun a ↦ abs_nonneg _
    have hf_integrable : Integrable f (s.toProbMeasureSeq hs n) :=
      BoundedContinuousFunction.integrable _ f
    rw [integral_eq_zero_iff_of_nonneg (by exact fpos) hf_integrable]
    dsimp only [FlagSeq.toProbMeasureSeq, FinFlag.toProbMeasure, FinFlag.toMeasure,
      ProbabilityMeasure.coe_mk, EventuallyEq, Filter.Eventually]
    simp_rw [mem_ae_iff]
    rw [PMF.toMeasure_apply_eq_zero_iff _ (by
      exact MeasurableSet.compl (measurableSet_eq_fun flagDensitySpace_sub_sum_abs_measurable measurable_zero)
    )]
    rw [Set.disjoint_left]
    intro a ha_support
    simp only [Set.compl_setOf, Pi.zero_apply, Set.mem_setOf_eq, Decidable.not_not]
    rw [FinFlag.toPMF_support] at ha_support
    simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image,
      Set.mem_image, Finset.mem_coe] at ha_support
    obtain ⟨G, _, hG⟩ := ha_support
    subst hG
    dsimp only [DFunLike.coe, funFromFlagWithSizeToFlagDensitySpace, f]
    simp only [← Rat.cast_mul, ← Rat.cast_sum, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_eq_zero]
    rw [abs_eq_zero, sub_eq_zero]
    apply density_chain_rule₁₁ ℓ F.2 G (finFlag_size_ge_n₀ F) hℓ
    calc
      ℓ ≤ n := hn
      _ ≤ (s n).1 :=
        hs_inc.id_le n
  · simp_all only [not_le, isEmpty_Prop, IsEmpty.forall_iff, Set.setOf_true,
    ProbabilityMeasure.coeFn_univ]

/-- The limit measure assigns probability 1 to the set where the normalization relation
(`oneProp`, `a 1 = 1`) holds. -/
theorem onePropSet_prob_eq_one
    {s : FlagSeq ∅ₜ} (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)} (hs_tendsto : Tendsto (s.toProbMeasureSeq hs) atTop (𝓝 ℙ))
    : ℙ {a | oneProp a} = 1
  := by
  dsimp only [oneProp]
  conv =>
    lhs; rhs; rhs; ext a
    rw [← sub_eq_zero, ← abs_eq_zero]
  apply ae_zero_of_integral_eq_zero (fun a ↦ abs_nonneg _) flagDensitySpace_one_sub_one_measurable flagDensitySpace_one_sub_one_integrable
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hs_tendsto
  let f : BoundedContinuousFunction (FlagDensitySpace σ) ℝ := {
    toFun := fun a ↦ |a 1 - 1|
    continuous_toFun := by
      apply Continuous.comp' continuous_abs
      apply Continuous.sub
      · exact (FinFlag.toBoundedContinuousFun _).continuous_toFun
      · exact continuous_const
    map_bounded' := by
      use 2
      intro a b
      rw [← sub_zero 2]
      apply Real.dist_le_of_mem_Icc <;> simp only [Set.mem_Icc, abs_nonneg, true_and]
      · exact flagDensitySpace_one_sub_one_bounded a
      · exact flagDensitySpace_one_sub_one_bounded b
  }
  specialize hs_tendsto f
  apply tendsto_nhds_unique hs_tendsto
  apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ 0
  intro n hn
  have fpos : 0 ≤ f := fun a ↦ abs_nonneg _
  have hf_integrable : Integrable f (s.toProbMeasureSeq hs n) :=
    BoundedContinuousFunction.integrable _ f
  rw [integral_eq_zero_iff_of_nonneg (by exact fpos) hf_integrable]
  dsimp only [FlagSeq.toProbMeasureSeq, FinFlag.toProbMeasure, FinFlag.toMeasure,
    ProbabilityMeasure.coe_mk, EventuallyEq, Filter.Eventually]
  simp_rw [mem_ae_iff]
  rw [PMF.toMeasure_apply_eq_zero_iff _ (by
    exact MeasurableSet.compl (measurableSet_eq_fun (abs_measurable (Measurable.sub (flagDensitySpace_eval_measurable _) measurable_const)) measurable_zero)
  )]
  rw [Set.disjoint_left]
  intro a ha_support
  simp only [Set.compl_setOf, Pi.zero_apply, Set.mem_setOf_eq, Decidable.not_not]
  rw [FinFlag.toPMF_support] at ha_support
  simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image,
    Set.mem_image, Finset.mem_coe] at ha_support
  obtain ⟨G, _, hG⟩ := ha_support
  subst hG
  dsimp only [DFunLike.coe, funFromFlagWithSizeToFlagDensitySpace, f]
  rw [flagDensity_one]
  norm_num

/-- The limit measure assigns probability 1 to the set where the multiplicativity relation
(`mulProp`) holds; this is the deep step, using the chain rule and a `c/n` density estimate. -/
theorem mulPropSet_prob_eq_one
    {s : FlagSeq ∅ₜ}
    (hs_inc : Increases s) (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)} (hs_tendsto : Tendsto (s.toProbMeasureSeq hs) atTop (𝓝 ℙ))
    : ℙ {a | mulProp a} = 1
  := by
  rw [mulPropSet_eq_iInter]
  apply prob_iInter_eq_one_of_all_prob_eq_one <;> intro F₁
  · apply MeasurableSet.iInter; intro F₂
    exact flagDensitySpace_mul_eq_sum_measurableSet
  apply prob_iInter_eq_one_of_all_prob_eq_one <;> intro F₂
  · exact flagDensitySpace_mul_eq_sum_measurableSet
  conv =>
    lhs; rhs; rhs; ext a
    rw [← sub_eq_zero, ← abs_eq_zero]
  apply ae_zero_of_integral_eq_zero (fun a ↦ abs_nonneg _) flagDensitySpace_mul_sub_sum_abs_measurable flagDensitySpace_mul_sub_sum_abs_integrable
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hs_tendsto
  let f : BoundedContinuousFunction (FlagDensitySpace σ) ℝ := {
    toFun := fun a ↦ |a F₁ * a F₂ - ∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀), flagDensity₂ F₁.2 F₂.2 G * a ⟨F₁.1 + F₂.1 - n₀, G⟩|
    continuous_toFun := by
      apply Continuous.comp' continuous_abs
      apply Continuous.sub
      · apply Continuous.mul
        · exact (FinFlag.toBoundedContinuousFun F₁).continuous_toFun
        · exact (FinFlag.toBoundedContinuousFun F₂).continuous_toFun
      · apply continuous_finset_sum Finset.univ
        intro G _
        apply Continuous.mul continuous_const
        exact (FinFlag.toBoundedContinuousFun ⟨F₁.1 + F₂.1 - n₀, G⟩).continuous_toFun
    map_bounded' := by
      use 1 + Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀))
      intro a b
      rw [← sub_zero (1 + Fintype.card (FlagWithSize σ (F₁.1 + F₂.1 - n₀)) : ℝ)]
      apply Real.dist_le_of_mem_Icc <;> simp only [Set.mem_Icc, abs_nonneg, true_and]
      · exact flagDensitySpace_mul_sub_sum_abs_bounded a F₁ F₂
      · exact flagDensitySpace_mul_sub_sum_abs_bounded b F₁ F₂
  }
  specialize hs_tendsto f
  apply tendsto_nhds_unique hs_tendsto
  obtain ⟨c, cpos, hc⟩ := flagListDensity₂_prod_approx F₁.2 F₂.2
  have h₀ : Tendsto (fun (n : ℕ) ↦ (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h₁ : Tendsto (fun (n : ℕ) ↦ ((c : ℝ) / n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  apply Tendsto.squeeze' h₀ h₁
  · apply Eventually.of_forall
    intro n
    apply integral_nonneg
    intro n
    simp only [Pi.zero_apply, DFunLike.coe, abs_nonneg, f]
  · rw [eventually_atTop]
    have ⟨N, hN⟩ := Increases.eventually_ge hs_inc (F₁.1 + F₂.1 - n₀)
    use max N 1
    intro n hn
    have : (c / n : ℝ) = ∫ (a : FlagDensitySpace σ), (c / n : ℝ) ∂((s n).toProbMeasure (hs n)) := by
      rw [MeasureTheory.integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [this]
    apply integral_mono_of_nonneg
    · apply Eventually.of_forall
      intro a
      simp only [Pi.zero_apply, DFunLike.coe, abs_nonneg, f]
    · exact integrable_const _
    dsimp only [FlagSeq.toProbMeasureSeq, FinFlag.toProbMeasure, FinFlag.toMeasure,
      ProbabilityMeasure.coe_mk, EventuallyLE, Filter.Eventually]
    simp_rw [mem_ae_iff, Set.compl_setOf, not_le]
    rw [PMF.toMeasure_apply_eq_zero_iff _ (by
      exact measurableSet_lt measurable_const flagDensitySpace_mul_sub_sum_abs_measurable
    )]
    rw [Set.disjoint_left]
    intro a ha_support
    simp only [Set.mem_setOf_eq, not_lt]
    rw [FinFlag.toPMF_support] at ha_support
    simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image,
      Set.mem_image, Finset.mem_coe] at ha_support
    obtain ⟨G, _, hG⟩ := ha_support
    subst hG
    dsimp only [DFunLike.coe, funFromFlagWithSizeToFlagDensitySpace, f]
    simp only [← Rat.cast_mul, ← Rat.cast_sum, ← Rat.cast_sub, ← Rat.cast_abs]
    have : (n : ℝ) = ((n : ℚ) : ℝ) := rfl
    rw [this, ← Rat.cast_div, Rat.cast_le, abs_sub_comm]
    rw [← density_chain_rule₂₁ _ _ _ _ (finFlag_size_ge_n₀ F₁) (finFlag_size_ge_n₀ F₂) le_tsub_add (hN n (le_of_max_le_left hn))]
    calc
      _ ≤ c / G.out.size := hc G
      _ ≤ c / n := by
        apply div_le_div₀ cpos (by rfl) (Nat.cast_pos'.mpr (le_of_max_le_right hn))
        simp only [LabeledGraph.size, Fintype.card_fin]
        rw [Nat.cast_le]
        exact hs_inc.id_le n

/-- The limit measure is concentrated on the positive-homomorphism space: combining the three
defining relations, `ℙ (PositiveHomSpace σ) = 1`. -/
theorem flagSeq_limit_measure_support_positiveHomSpace
    {s : FlagSeq ∅ₜ}
    (hs_inc : Increases s) (hs_den : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    {ℙ : ProbabilityMeasure (FlagDensitySpace σ)} (hs_tendsto : Tendsto (s.toProbMeasureSeq hs_den) atTop (𝓝 ℙ))
    : ℙ (PositiveHomSpace σ) = 1
  := by
  rw [positiveHomSpace_eq]
  apply prob_inter_eq_one_of_prob_eq_one
  · exact zeroSpaceProp_measurableSet
  · apply MeasurableSet.inter
    · exact oneProp_measurableSet
    · exact mulProp_measurableSet
  · exact zeroSpacePropSet_prob_eq_one hs_inc hs_den hs_tendsto
  · apply prob_inter_eq_one_of_prob_eq_one
    · exact oneProp_measurableSet
    · exact mulProp_measurableSet
    · exact onePropSet_prob_eq_one hs_den hs_tendsto
    · exact mulPropSet_prob_eq_one hs_inc hs_den hs_tendsto

/- Theorem 3.5, existence -/
/-- Theorem 3.5 (existence): for a base homomorphism `φ₀` with `φ₀ ⟨σ⟩₀ > 0`, there is a
probability measure on `PositiveHomSpace σ` whose expectation of `f` equals the normalized
downward value `(φ₀ ⟦f⟧₀) / (φ₀ ⟦1⟧₀)`. This is the random extension of `φ₀`. -/
theorem exists_probMeasure_extend_emptyType_positiveHom
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ∃ (ℙ : ProbabilityMeasure (PositiveHomSpace σ)),
      ∀ (f : FlagAlgebra σ), ∫ φ, (PositiveHomSpace.toPosHom φ) f ∂ℙ = (φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀)
  := by
  obtain ⟨s, hs_den, ℙ, hs_conv, hℙ⟩ := exists_converge_flagSeq_and_probMeasure_tendsto hσ
  let ℙ' : ProbabilityMeasure (PositiveHomSpace σ) := {
    val := Measure.comap Subtype.val ℙ
    property := {
      measure_univ := by
        rw [Measure.comap_apply]
        · have : (1 : ENNReal) = ((1 : NNReal) : ENNReal) := rfl
          rw [this, ← flagSeq_limit_measure_support_positiveHomSpace hs_conv.1 hs_den hℙ]
          simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq,
            ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        · exact Subtype.val_injective
        · intro S hS
          exact MeasurableSet.subtype_image positiveHomSpace_measurable hS
        · exact MeasurableSet.univ
    }
  }
  use ℙ'
  intro f
  rcases Quotient.exists_rep f with ⟨frep, rfl⟩
  rw [flagVector_eq_sum_basisVector frep]
  simp_rw [sum_quot, downward_sum, PositiveHom.map_sum, Finset.sum_div]
  have : ∀ F ∈ frep.support, Integrable (fun φ ↦ (PositiveHomSpace.toPosHom φ) ⟦frep F • basisVector F⟧) ℙ' := by
    intro F hF
    constructor
    · apply Measurable.aestronglyMeasurable
      apply Measurable.eval
      rw [measurable_pi_iff]
      intro g
      rcases Quotient.exists_rep g with ⟨grep, rfl⟩
      rw [flagVector_eq_sum_basisVector grep]
      simp_rw [sum_quot, PositiveHom.map_sum]
      apply Finset.measurable_sum grep.support
      intro G hG
      simp_rw [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector]
      apply Measurable.const_mul
      apply Measurable.comp (flagDensitySpace_eval_measurable G) measurable_subtype_coe
    · apply @HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (abs (frep F))
      apply Eventually.of_forall
      intro φ
      rw [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector, mul_comm]
      simp only [norm_mul, Real.norm_eq_abs]
      apply mul_le_of_le_one_left (abs_nonneg (frep F))
      have hφ := flagDensitySpace_mem_Icc_zero_one φ F
      simp only [Set.mem_Icc] at hφ
      rw [abs_le]
      constructor <;> linarith
  rw [integral_finset_sum frep.support this]
  apply Finset.sum_congr rfl
  intro F hF
  simp_rw [smul_quot, downward_smul, PositiveHom.map_smul, ← mul_div, integral_const_mul]
  congr
  have hℙF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hℙ F.toBoundedContinuousFun
  have h' := tendsto_integral_flagDensitySpace_of_converge_flagSeq hσ hs_conv hs_den F
  rw [← tendsto_nhds_unique hℙF h']
  simp_rw [PositiveHomSpace.toPosHom_basisVector]
  dsimp only [ProbabilityMeasure.coe_mk, ℙ']
  rw [integral_subtype_comap (@positiveHomSpace_measurable _ σ) (fun a ↦ a F)]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  dsimp only [Filter.Eventually]
  simp_rw [← Decidable.or_iff_not_imp_left]
  rw [mem_ae_iff_prob_eq_one₀ (by
    apply NullMeasurableSet.of_compl
    apply NullMeasurableSet.of_null
    rw [Set.setOf_or, Set.compl_union]
    apply measure_inter_null_of_null_left
    apply (prob_compl_eq_zero_iff positiveHomSpace_measurable).mpr
    rw [← ENNReal.toNNReal_eq_one_iff]
    exact flagSeq_limit_measure_support_positiveHomSpace hs_conv.1 hs_den hℙ
  )]
  rw [← ENNReal.toNNReal_eq_one_iff]
  show ℙ {x | x ∈ PositiveHomSpace σ ∨ x F = 0} = 1
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one ℙ _
  · rw [← flagSeq_limit_measure_support_positiveHomSpace hs_conv.1 hs_den hℙ]
    exact ProbabilityMeasure.apply_mono ℙ Set.subset_union_left

/-- The chosen random-extension probability measure `ℙ[φ₀]` of a base homomorphism `φ₀`. -/
noncomputable def probMeasure_extend_emptyType_positiveHom
    (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ProbabilityMeasure (PositiveHomSpace σ)
  :=
  Classical.choose (exists_probMeasure_extend_emptyType_positiveHom (σ := σ) hσ)

-- Notation `ℙ[φ₀]` for the random extension measure of `φ₀` (positivity proved by `assumption`).
notation "ℙ[" φ₀ "]" =>
  probMeasure_extend_emptyType_positiveHom φ₀ (by assumption)

/-- Defining property of `ℙ[φ₀]`: integrating `φ ↦ φ f` recovers `(φ₀ ⟦f⟧₀) / (φ₀ ⟦1⟧₀)`. -/
theorem probMeasure_extend_emptyType_positiveHom_spec
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ∀ (f : FlagAlgebra σ),
  ∫ (φ : PositiveHomSpace σ), φ f ∂(ℙ[φ₀]) = (φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀)
  :=
  Classical.choose_spec (exists_probMeasure_extend_emptyType_positiveHom (σ := σ) hσ)

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

theorem downward_zero_at_hom
    (φ : PositiveHom ∅ₜ) (hφ : φ ⟨σ⟩₀ = 0)
    : ∀ f : FlagAlgebra σ, φ ⟦f⟧₀ = 0
  := by
  intro f
  rw [← Quotient.out_eq f, flagVector_eq_sum_basisVector f.out]
  rw [sum_quot, downward_sum, PositiveHom.map_sum]
  apply Finset.sum_eq_zero
  intro F _
  rw [smul_quot, downward_smul, PositiveHom.map_smul, mul_eq_zero]
  right
  dsimp only [downward, downwardFlagVectorQuot, downwardFlagVector, Quotient.lift_mk]
  rw [linearExtension_basisVector]
  dsimp only [downwardFlag]
  rw [rat_smul_eq_real_smul, smul_quot, PositiveHom.map_smul, mul_eq_zero]
  right
  apply positiveHom_basisVector_eq_zero φ (flagDensity₁_flagType_asEmptyType_pos F)
  exact hφ

/-- The downward operator preserves the semantic cone: if `f ≥ 0` semantically in the typed
algebra then `⟦f⟧₀ ≥ 0` in the empty-type algebra. Proved via the random extension measure. -/
theorem downward_preserve_semanticCone
    (f : FlagAlgebra σ) (hf : f ∈ semanticCone σ)
    : ⟦f⟧₀ ∈ semanticCone ∅ₜ
  := by
  intro φ₀
  have : φ₀ ⟨σ⟩₀ ≥ 0 := positiveHom_basisVector_ge_zero φ₀ _
  rcases eq_or_lt_of_le this with hφ₀ | hφ₀
  · have : φ₀ ⟦f⟧₀ = 0 := downward_zero_at_hom φ₀ (Eq.symm hφ₀) f
    exact le_of_eq (Eq.symm this)
  · obtain ⟨ℙ, hℙ⟩ := exists_probMeasure_extend_emptyType_positiveHom hφ₀
    specialize hℙ f
    have hφ₀' : φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ > 0 := positiveHom_one_downward_pos hφ₀
    rw [eq_div_iff (ne_of_gt hφ₀')] at hℙ
    rw [← hℙ, ge_iff_le, mul_nonneg_iff_left_nonneg_of_pos hφ₀']
    exact integral_nonneg fun φ ↦ hf (PositiveHomSpace.toPosHom φ)

/-- The downward image of a square is nonnegative: `⟦f * f⟧₀ ≥ 0`. -/
theorem square_downward_nonneg
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  := by
  simp only [ge_iff_le, le_def, sub_zero]
  apply downward_preserve_semanticCone
  intro φ
  rw [PositiveHom.map_mul]
  exact mul_self_nonneg (φ f)

/-- Cauchy–Schwarz for the downward operator: `⟦f*f⟧₀ · ⟦g*g⟧₀ ≥ ⟦f*g⟧₀ · ⟦f*g⟧₀`. The key
inequality powering SDP-style flag-algebra density bounds (aliased `Cauchy_Schwarz_inequality`). -/
theorem square_downward_mul_ge_mul_downward_square
    (f g : FlagAlgebra σ)
    : ⟦f * f⟧₀ * ⟦g * g⟧₀ ≥ ⟦f * g⟧₀ * ⟦f * g⟧₀
  := by
  intro φ
  rw [PositiveHom.map_sub φ _ _, PositiveHom.map_mul φ _ _, PositiveHom.map_mul φ _ _]
  have : φ ⟨σ⟩₀ ≥ 0 := positiveHom_basisVector_ge_zero φ _
  rcases eq_or_lt_of_le this with hφ | hφ
  · have hφ_zero : ∀ k : FlagAlgebra σ, φ ⟦k⟧₀ = 0 := downward_zero_at_hom φ (Eq.symm hφ)
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
    rw [sub_nonneg]

    let F_func := fun (ψ : PositiveHomSpace σ) ↦ (PositiveHomSpace.toPosHom ψ) f
    let G_func := fun (ψ : PositiveHomSpace σ) ↦ (PositiveHomSpace.toPosHom ψ) g

    have hF_sq : ∀ ψ, F_func ψ ^ 2 = (PositiveHomSpace.toPosHom ψ) (f * f) := by
      intro ψ
      simp only [F_func, sq, PositiveHom.map_mul]
    have hG_sq : ∀ ψ, G_func ψ ^ 2 = (PositiveHomSpace.toPosHom ψ) (g * g) := by
      intro ψ
      simp only [G_func, sq, PositiveHom.map_mul]
    have hFG : ∀ ψ, F_func ψ * G_func ψ = (PositiveHomSpace.toPosHom ψ) (f * g) := by
      intro ψ
      simp only [F_func, G_func, PositiveHom.map_mul]

    rw [integral_congr_ae (Filter.Eventually.of_forall fun ψ => (hF_sq ψ).symm)]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ψ => (hG_sq ψ).symm)]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ψ => (hFG ψ).symm)]

    have h_eval_eq : ∀ k : FlagAlgebra σ,
                       (fun ψ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom ψ) k)
                       = (fun ψ => ∑ F ∈ k.out.support, k.out F * ψ.val F) := by
      intro k
      funext ψ
      conv_lhs =>
        rw [← Quotient.out_eq k, flagVector_eq_sum_basisVector k.out]
        rw [sum_quot, PositiveHom.map_sum]
        simp only [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector]
    have h_F_eq : F_func = (fun ψ => ∑ F ∈ f.out.support, f.out F * ψ.val F) := by
      dsimp [F_func]
      exact h_eval_eq f
    have h_G_eq : G_func = (fun ψ => ∑ F ∈ g.out.support, g.out F * ψ.val F) := by
      dsimp [G_func]
      exact h_eval_eq g

    have h_cont_toPosHom : Continuous (fun (ψ : PositiveHomSpace σ)
                                        => (PositiveHomSpace.toPosHom ψ : FlagAlgebra σ → ℝ)) := by
      apply continuous_pi
      intro k
      have h_cont_sum : Continuous (fun ψ : PositiveHomSpace σ => ∑ F ∈ k.out.support, k.out F * ψ.val F) := by
        apply continuous_finset_sum
        intro F hF
        exact Continuous.mul continuous_const ((FinFlag.continuous F).comp continuous_subtype_val)
      simpa [h_eval_eq] using h_cont_sum

    have h_cont_F : Continuous F_func := (continuous_apply f).comp h_cont_toPosHom
    have h_cont_G : Continuous G_func := (continuous_apply g).comp h_cont_toPosHom

    have h_eval_bdd (k : FlagAlgebra σ) :
            ∃ C, ∀ ψ, |(fun ψ' : PositiveHomSpace σ => (PositiveHomSpace.toPosHom ψ') k) ψ| ≤ C := by
      rw [h_eval_eq k]
      refine ⟨∑ F : k.out.support, |k.out F|, ?_⟩
      intro ψ
      have hψ_abs : ∀ F, |ψ.val F| ≤ 1 := fun F => flagDensitySpace_abs_le_one ψ.val F
      simp only [Finset.univ_eq_attach, ge_iff_le]
      calc
        |∑ F ∈ k.out.support, k.out F * ψ.val F|
        _  ≤ ∑ F ∈ k.out.support, |k.out F * ψ.val F| :=
                Finset.abs_sum_le_sum_abs _ _
        _ = ∑ F ∈ k.out.support, |k.out F| * |ψ.val F| := by
                simp [abs_mul]
        _ ≤ ∑ F ∈ k.out.support, |k.out F| * 1 := by
                apply Finset.sum_le_sum
                intro F hF
                have := hψ_abs F
                exact mul_le_mul_of_nonneg_left this (by simp)
        _ = ∑ F ∈ k.out.support, |k.out F| := by
                simp only [mul_one]
        _ = _ := by
                rw [Finset.sum_attach (s := k.out.support) (f := fun F => |k.out F|)]
    have h_mem_F : MemLp F_func (ENNReal.ofReal 2) ℙ := by
      have : ∃ C, ∀ ψ, ‖F_func ψ‖ ≤ C := by
        dsimp [F_func]
        exact h_eval_bdd f
      obtain ⟨C, hC⟩ := this
      exact MemLp.of_bound h_cont_F.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    have h_mem_G : MemLp G_func (ENNReal.ofReal 2) ℙ := by
      have : ∃ C, ∀ ψ, ‖G_func ψ‖ ≤ C := by
        dsimp [G_func]
        exact h_eval_bdd g
      obtain ⟨C, hC⟩ := this
      exact MemLp.of_bound h_cont_G.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

    have h_CS := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two h_mem_F h_mem_G
    simp only [Real.norm_eq_abs] at h_CS

    calc
      _ = (∫ x, F_func x * G_func x ∂ℙ)^2 :=
            Eq.symm (pow_two (∫ (x : ↑(PositiveHomSpace σ)), F_func x * G_func x ∂↑ℙ))
      _ = |∫ x, F_func x * G_func x ∂ℙ|^2 :=
            (sq_abs _).symm
      _ ≤ (∫ x, |F_func x * G_func x| ∂ℙ)^2 :=
            pow_le_pow_left₀
              (abs_nonneg _)
              (abs_integral_le_integral_abs (f := fun x => F_func x * G_func x) (μ := ℙ)) 2
      _ = (∫ x, |F_func x| * |G_func x| ∂ℙ)^2 := by
            simp only [abs_mul]
      _ ≤ ((∫ x, |F_func x|^2 ∂ℙ)^((1:ℝ) / 2) * (∫ x, |G_func x|^2 ∂ℙ)^((1:ℝ)/2))^2 := by
            apply pow_le_pow_left₀
            . exact integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            . simpa [Real.rpow_two] using h_CS
      _ = ((∫ x, |F_func x|^2 ∂ℙ)^((1:ℝ)/2))^2 * ((∫ x, |G_func x|^2 ∂ℙ)^((1:ℝ)/2))^2 := by
            rw [mul_pow]
      _ = (∫ x, |F_func x|^2 ∂ℙ) * (∫ x, |G_func x|^2 ∂ℙ) := by
            have hF_nonneg : 0 ≤ ∫ x, |F_func x|^2 ∂ℙ := by
              exact integral_nonneg (fun x => sq_nonneg _)
            have hG_nonneg : 0 ≤ ∫ x, |G_func x|^2 ∂ℙ := by
              exact integral_nonneg (fun x => sq_nonneg _)
            have hF : ((∫ x, |F_func x|^2 ∂ℙ)^((1:ℝ)/2))^2 = ∫ x, |F_func x|^2 ∂ℙ := by
              calc
                _ = (∫ x, |F_func x|^2 ∂ℙ) ^ (((1:ℝ)/2) * (2:ℝ)) := by
                        simpa using (Real.rpow_mul hF_nonneg ((1:ℝ)/2) (2:ℝ)).symm
                _ = (∫ x, |F_func x|^2 ∂ℙ) ^ (1:ℝ) := by
                        norm_num
                _ = ∫ x, |F_func x|^2 ∂ℙ := by
                        simp only [sq_abs, Real.rpow_one]
            have hG : ((∫ x, |G_func x|^2 ∂ℙ)^((1:ℝ)/2))^2 = ∫ x, |G_func x|^2 ∂ℙ := by
              calc
                _ = (∫ x, |G_func x|^2 ∂ℙ) ^ (((1:ℝ)/2) * (2:ℝ)) := by
                        simpa using (Real.rpow_mul hG_nonneg ((1:ℝ)/2) (2:ℝ)).symm
                _ = (∫ x, |G_func x|^2 ∂ℙ) ^ (1:ℝ) := by
                        norm_num
                _ = ∫ x, |G_func x|^2 ∂ℙ := by
                        simp
            have hF' : ((∫ x, F_func x ^ 2 ∂ℙ) ^ (2⁻¹:ℝ)) ^ 2 = ∫ x, F_func x ^ 2 ∂ℙ := by
              simpa [sq_abs, one_div] using hF
            have hG' : ((∫ x, G_func x ^ 2 ∂ℙ) ^ (2⁻¹:ℝ)) ^ 2 = ∫ x, G_func x ^ 2 ∂ℙ := by
              simpa [sq_abs, one_div] using hG
            simp only [sq_abs, one_div, hF', hG']
      _ = _ := by
            simp only [sq_abs]

alias Cauchy_Schwarz_inequality := square_downward_mul_ge_mul_downward_square

/-- Cauchy–Schwarz against the unit: `⟦f*f⟧₀ · ⟦1⟧₀ ≥ ⟦f⟧₀ · ⟦f⟧₀` (aliased
`Cauchy_Schwarz_inequality_unit`). -/
theorem square_downward_mul_one_downward_ge_downward_square
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ * ⟦(1 : FlagAlgebra σ)⟧₀ ≥ ⟦f⟧₀ * ⟦f⟧₀
  := by
  have := Cauchy_Schwarz_inequality f 1
  rwa [mul_one f, mul_one 1] at this

alias Cauchy_Schwarz_inequality_unit := square_downward_mul_one_downward_ge_downward_square

end FlagAlgebras
