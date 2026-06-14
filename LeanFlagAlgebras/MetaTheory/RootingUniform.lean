import LeanFlagAlgebras.FlagAlgebra.RandomHom

/-! # The σ-rooting measure as a uniform distribution over rootings

Two facts identifying the σ-rooting probability measure `FinFlag.toProbMeasure` of an unlabelled
flag `F` with the (downward-normalizing-factor-weighted) uniform distribution over the σ-rootings
(label extensions) of `F`.  Together they let the capstone turn `planted_mass` — an
embedding-count ratio — into a measure lower bound:

* `toProbMeasure_apply_eq_dnf_ratio` (R1) expresses the measure of any set `A` as the ratio
  `(∑ over label extensions whose density profile lands in A, dnf) / (∑ over all label extensions, dnf)`.
* `sum_isomorphismCount_labelExtensions` (R2) identifies the total `isomorphismCount` mass over the
  label extensions with the number of σ-labellings of the underlying graph — the count of
  σ-rootings of the host graph, expressed concretely as a finite `Finset.filter` cardinality.

The first is a direct unfolding of `FinFlag.toPMF` (a `PMF.ofFinset`) through the measure it induces;
the second is a re-grouping of the `labelExtensions` classes that mirrors the partition used in
`isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledGraphCount`, specialised
to drop the `labeledGraphCount` weight.
-/

open MeasureTheory

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## R1 — the rooting measure as a dnf-ratio over labellings -/

/-- The pointwise value of `FinFlag.toPMF`, unfolded from its `PMF.ofFinset` definition. -/
private theorem toPMF_apply_val (F : FinFlag ∅ₜ)
    (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0) (a : FlagDensitySpace σ) :
    (F.toPMF hF) a =
      (if a ∈ ((funFromFlagWithSizeToFlagDensitySpace σ F.1 '' labelExtensions F.2 σ).toFinset)
       then ENNReal.ofReal
              ((∑ F' ∈ (labelExtensions F.2 σ)
                  with funFromFlagWithSizeToFlagDensitySpace σ F.1 F' = a,
                  (downwardNormalizingFactor F' : ℝ))
               / (∑ F' ∈ labelExtensions F.2 σ, (downwardNormalizingFactor F' : ℝ)))
       else 0) := by
  unfold FinFlag.toPMF
  rw [PMF.ofFinset_apply]

private theorem dnf_sum_nonneg (F : FinFlag ∅ₜ) (a : FlagDensitySpace σ) :
    0 ≤ ∑ F' ∈ (labelExtensions F.2 σ)
          with funFromFlagWithSizeToFlagDensitySpace σ F.1 F' = a,
          (downwardNormalizingFactor F' : ℝ) := by
  apply Finset.sum_nonneg
  intros
  rw [Rat.cast_nonneg]
  exact downwardNormalizingFactor_nonneg _

private theorem dnf_total_nonneg (F : FinFlag ∅ₜ) :
    0 ≤ ∑ F' ∈ labelExtensions F.2 σ, (downwardNormalizingFactor F' : ℝ) := by
  apply Finset.sum_nonneg
  intros
  rw [Rat.cast_nonneg]
  exact downwardNormalizingFactor_nonneg _

/-- **(R1)** The σ-rooting measure of a set `A` of density profiles is the ratio of the total
downward-normalizing-factor weight of the label extensions whose profile lands in `A` to the total
weight of all label extensions.  This holds for *every* set `A` (no measurability hypothesis),
since `FinFlag.toPMF` is finitely supported. -/
theorem toProbMeasure_apply_eq_dnf_ratio (F : FinFlag ∅ₜ)
    (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0) (A : Set (FlagDensitySpace σ)) :
    ((F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A).toReal
      = (∑ F' ∈ (labelExtensions F.2 σ).filter
            (fun F' => funFromFlagWithSizeToFlagDensitySpace σ F.1 F' ∈ A),
          (downwardNormalizingFactor F' : ℝ))
        / (∑ F' ∈ labelExtensions F.2 σ, (downwardNormalizingFactor F' : ℝ)) := by
  set L := labelExtensions F.2 σ with hL
  set f := funFromFlagWithSizeToFlagDensitySpace σ F.1 with hf
  set S : Finset (FlagDensitySpace σ) := (f '' L).toFinset with hS
  -- 1. the measure of `A` is the `tsum` of the indicator of the PMF
  have h1 : (F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A
      = ∑' x, A.indicator (F.toPMF hF) x :=
    PMF.toMeasure_apply_eq_tsum (F.toPMF hF) A
  -- 2. the PMF is supported on `S`, so the `tsum` is a finite sum over `S`
  have h2 : (∑' x, A.indicator (F.toPMF hF) x)
      = ∑ x ∈ S, A.indicator (F.toPMF hF) x := by
    apply tsum_eq_sum
    intro x hx
    rw [Set.indicator_apply]
    split
    · have hsupp := FinFlag.toPMF_support F hF
      have hzero : (F.toPMF hF) x = 0 := by
        by_contra hne
        have hmem : x ∈ (F.toPMF hF).support := hne
        rw [hsupp] at hmem
        exact hx hmem
      rw [hzero]
    · rfl
  rw [h1, h2]
  -- 3. push `.toReal` through the finite `ENNReal` sum
  rw [ENNReal.toReal_sum (by
    intro x hx
    rw [Set.indicator_apply]
    split
    · rw [toPMF_apply_val, if_pos hx]; exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top)]
  -- 4. evaluate each term: on `S`, the indicator's `toReal` is the dnf-ratio (or `0`)
  have h4 : ∀ x ∈ S, (A.indicator (F.toPMF hF) x).toReal
      = if x ∈ A
        then (∑ F' ∈ L with f F' = x, (downwardNormalizingFactor F' : ℝ))
              / (∑ F' ∈ L, (downwardNormalizingFactor F' : ℝ))
        else 0 := by
    intro x hx
    rw [Set.indicator_apply]
    split
    · rw [toPMF_apply_val, if_pos hx, ENNReal.toReal_ofReal]
      exact div_nonneg (dnf_sum_nonneg F x) (dnf_total_nonneg F)
    · simp
  rw [Finset.sum_congr rfl h4]
  -- 5. factor out the common denominator and regroup the numerator fibrewise
  rw [← Finset.sum_filter, ← Finset.sum_div]
  congr 1
  have hmaps : ∀ F' ∈ L.filter (fun F' => f F' ∈ A), f F' ∈ S.filter (· ∈ A) := by
    intro F' hF'
    simp only [Finset.mem_filter] at hF' ⊢
    refine ⟨?_, hF'.2⟩
    rw [hS, Set.mem_toFinset]
    exact ⟨F', hF'.1, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun F' => (downwardNormalizingFactor F' : ℝ))]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply Finset.sum_congr
  · ext F'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hLm, hfx⟩
      exact ⟨⟨hLm, by rw [hfx]; exact hx.2⟩, hfx⟩
    · rintro ⟨⟨hLm, _⟩, hfx⟩
      exact ⟨hLm, hfx⟩
  · intros; rfl

/-! ## R2 — total `isomorphismCount` mass equals the number of σ-rootings -/

/-- **(R2), fixed-representative form.** For a fixed unlabelled labelled-graph `F'` on `Fin ℓ'`, the
total `isomorphismCount` mass over the σ-label-extensions of `⟦F'⟧` equals the number of
σ-labellings `H` on the *same* underlying graph `F'.graph`.  The `labelExtensions` classes partition
the labellings of `F'.graph` into flag-isomorphism classes, so summing the class sizes telescopes to
the whole set's cardinality. -/
theorem sum_isomorphismCount_labelExtensions_fixed (ℓ' : ℕ) (F' : LabeledGraph ∅ₜ (Fin ℓ')) :
    ∑ G ∈ labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ, isomorphismCount G.out
      = (Finset.univ.filter (fun H : LabeledGraph σ (Fin ℓ') => H.graph = F'.graph)).card := by
  let S_F' : Finset (LabeledGraph σ (Fin ℓ')) := {G | G.graph = F'.graph}.toFinset
  calc
    ∑ G ∈ labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ, isomorphismCount G.out
      = ∑ G ∈ labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ, {H ∈ S_F' | ⟦H⟧ = G}.card := by
        apply Finset.sum_congr rfl
        intro G hGF'
        rcases Quotient.exists_rep G with ⟨G, rfl⟩
        dsimp only [labelExtensions] at hGF'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hGF'
        rw [unlabel_eq_iff_unlabeledGraph_eqv] at hGF'
        have hG_iso : (⟦G⟧ : FlagWithSize σ ℓ').out ∼f G := by
          show ⟦G⟧.out ≈ G
          exact Quotient.eq_mk_iff_out.mp rfl
        rw [isomorphismCount_respect_eqv hG_iso]
        dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
        let G' : LabeledGraph σ (Fin ℓ') := {
          graph := F'.graph
          type_embed := {
            toFun := hGF'.some.graph_iso ∘ G.type_embed
            inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
            map_rel_iff' := by
              intro a b
              simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
              rw [type_embed_Adj_iff G]
              exact SimpleGraph.Iso.map_adj_iff (Nonempty.some hGF').graph_iso
          }
        }
        have hGG'_iso : G ∼f G' := by
          apply Nonempty.intro
          exact {
            graph_iso := by dsimp only [G']; exact hGF'.some.graph_iso
            type_preserve := by
              simp only [id_eq, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, G']
          }
        calc
          _ = {H | G'.graph = H.graph ∧ G' ∼f H}.toFinset.card := by
            have := isomorphismCount_respect_eqv hGG'_iso
            dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph] at this
            rw [this]; congr!
          _ = {H ∈ S_F' | ⟦H⟧ = ⟦G⟧}.card := by
            congr
            ext H
            simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S_F']
            constructor
            · intro ⟨h_graph_eq, h_iso⟩
              dsimp only [G'] at h_graph_eq
              rw [h_graph_eq]
              simp only [Quotient.eq, true_and]
              exact h_iso.symm.trans hGG'_iso.symm
            · intro ⟨h_graph_eq, h_iso⟩
              simp only [Quotient.eq] at h_iso
              constructor
              · dsimp only [G']; rw [h_graph_eq]
              · exact hGG'_iso.symm.trans h_iso.symm
    _ = ∑ G ∈ S_F', (1 : ℕ) := by
        have h_quot_labelExt : ∀ G ∈ S_F', ⟦G⟧ ∈ labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ := by
          intro G hG
          simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S_F'] at hG
          simp only [labelExtensions, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [unlabel_eq_iff_unlabeledGraph_eqv]
          apply Nonempty.intro
          exact {
            graph_iso := by dsimp only [unlabeledGraph]; rw [hG]
            type_preserve := List.ofFn_inj.mp rfl
          }
        rw [← Finset.sum_fiberwise_of_maps_to h_quot_labelExt (fun _ => (1 : ℕ))]
        apply Finset.sum_congr rfl
        intro G _
        rw [Finset.card_eq_sum_ones]
    _ = (Finset.univ.filter (fun H : LabeledGraph σ (Fin ℓ') => H.graph = F'.graph)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
        congr 1
        ext H
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S_F']

/-- **(R2).** For an unlabelled finite flag `F`, the total `isomorphismCount` mass over its
σ-label-extensions equals the number of σ-labellings `H` on the canonical representative graph
`(Quotient.out F.2).graph` — i.e. the number of σ-rootings of `F`'s underlying graph, given
concretely as a finite `Finset.filter` cardinality. -/
theorem sum_isomorphismCount_labelExtensions (F : FinFlag ∅ₜ) :
    ∑ G ∈ labelExtensions F.2 σ, isomorphismCount G.out
      = (Finset.univ.filter
          (fun H : LabeledGraph σ (Fin F.1) => H.graph = (Quotient.out F.2).graph)).card := by
  have h := sum_isomorphismCount_labelExtensions_fixed (σ := σ) F.1 (Quotient.out F.2)
  rw [Quotient.out_eq F.2] at h
  exact h

end FlagAlgebras.MetaTheory
