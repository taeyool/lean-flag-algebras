import «LeanFlagAlgebras».FlagAlgebra
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Cast.Field

open FlagAlgebras
open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/- Downward operator from σ-type to the empty type -/

def emptyType : FlagType (Fin 0) := SimpleGraph.emptyGraph (Fin 0)

notation "∅ₜ" => emptyType

@[simp]
theorem emptyType_size : ∅ₜ.size = 0 := by
  dsimp [emptyType, FlagType.size]
  simp only [Fintype.card_eq_zero]

def isoLabeledGraphSetWithSameGraph
    (G : LabeledGraph σ (Fin n)) : Set (LabeledGraph σ (Fin n))
  :=
  { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H }

noncomputable instance (G : LabeledGraph σ (Fin n)) : Fintype (isoLabeledGraphSetWithSameGraph G)
  :=
  Fintype.ofFinite (isoLabeledGraphSetWithSameGraph G)

noncomputable def isomorphismCount
    (G : LabeledGraph σ (Fin n)) : ℕ
  :=
  (isoLabeledGraphSetWithSameGraph G).toFinset.card

noncomputable def downwardNormalizingFactor_labeledGraph
    (G : LabeledGraph σ (Fin n)) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - n₀).factorial
  isomorphismCount G / num_of_all_injections

def funBetweenIsoLabeledGraphSetWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (φ : G ≃f G')
    : isoLabeledGraphSetWithSameGraph G → isoLabeledGraphSetWithSameGraph G'
  := by
  intro ⟨H, ⟨hGH_graph, hGH_iso⟩⟩
  let H' : LabeledGraph σ (Fin n) := {
    graph := G'.graph
    type_embed := {
      toFun := φ.graph_iso ∘ H.type_embed
      inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
      map_rel_iff' := by
        intro a b
        simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
        constructor
        · intro h
          rw [type_embed_Adj_iff H]
          nth_rw 1 [← hGH_graph]
          exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h
        · intro h
          rw [SimpleGraph.Iso.map_adj_iff φ.graph_iso, hGH_graph, ← type_embed_Adj_iff H]
          exact h
    }
  }
  have hG'H'_graph : G'.graph = H'.graph := rfl
  let φH : H.graph ≃g H'.graph := by
    rw [← hGH_graph, ← hG'H'_graph]
    exact φ.graph_iso
  let ψ : G ≃f H := hGH_iso.some
  have hH' : G'.graph = H'.graph ∧ G' ∼f H' := by
    constructor
    · rfl
    · apply Nonempty.intro
      exact {
        graph_iso := (φ.graph_iso.symm.trans ψ.graph_iso).trans φH
        type_preserve := by
          simp only [SimpleGraph.Iso.coe_comp]
          rw [← φ.type_preserve]
          calc
            _ = ⇑φH ∘ ⇑ψ.graph_iso ∘ (⇑φ.graph_iso.symm ∘ ⇑φ.graph_iso) ∘ ⇑G.type_embed := rfl
            _ = ⇑φH ∘ ⇑ψ.graph_iso ∘ ⇑G.type_embed := by ext; simp
            _ = ⇑φ.graph_iso ∘ ⇑ψ.graph_iso ∘ ⇑G.type_embed := by
              congr! 1
              show φH.toFun = φ.graph_iso
              dsimp [φH]
              funext x
              congr
              · rw [hGH_graph]
              · rw [hGH_graph]
              · simp only [cast_heq]
            _ = ⇑H'.type_embed := by
              rw [ψ.type_preserve]
              rfl
      }
  exact ⟨H', hH'⟩

lemma comp_funBetweenIsoLabeledGraphSetWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (φ : G ≃f G')
    : ∀ H, (funBetweenIsoLabeledGraphSetWithSameGraph φ.symm) ((funBetweenIsoLabeledGraphSetWithSameGraph φ) H) = H
  := by
  intro ⟨H, ⟨hGH_graph, hGH_iso⟩⟩
  unfold funBetweenIsoLabeledGraphSetWithSameGraph
  split
  rename_i h H_1 hGH_graph_1 hGH_iso_1 heq
  simp_all only [Subtype.mk.injEq]
  subst heq
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  congr!
  calc
    _ = (⇑φ.graph_iso.symm ∘ ⇑φ.graph_iso) ∘ ⇑H.type_embed := rfl
    _ = ⇑H.type_embed := by ext; simp only [Function.comp_apply, RelIso.symm_apply_apply]
    _ = H.2.1.toFun := rfl

def isoSetOfIsoLabeledGraphWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (φ : G ≃f G')
    : isoLabeledGraphSetWithSameGraph G ≃ isoLabeledGraphSetWithSameGraph G' where
  toFun := funBetweenIsoLabeledGraphSetWithSameGraph φ
  invFun := funBetweenIsoLabeledGraphSetWithSameGraph φ.symm
  left_inv := comp_funBetweenIsoLabeledGraphSetWithSameGraph φ
  right_inv := comp_funBetweenIsoLabeledGraphSetWithSameGraph φ.symm

lemma isomorphismCount_respect_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : isomorphismCount G = isomorphismCount G'
  := by
  dsimp [isomorphismCount]
  simp only [Set.toFinset_card, Fintype.card_congr (isoSetOfIsoLabeledGraphWithSameGraph h.some)]

lemma downwardNormalizingFactor_labeledGraph_respect_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : downwardNormalizingFactor_labeledGraph G = downwardNormalizingFactor_labeledGraph G'
  := by
  dsimp [downwardNormalizingFactor_labeledGraph]
  rw [isomorphismCount_respect_eqv h]

noncomputable def downwardNormalizingFactor
    : Flag σ (Fin n) → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ (Fin n) => downwardNormalizingFactor_labeledGraph G)
  intro G G' G_eqv
  exact downwardNormalizingFactor_labeledGraph_respect_eqv G_eqv

theorem downwardNormalizingFactor_pos
    (F : Flag σ (Fin n))
    : downwardNormalizingFactor F > 0
  := by
  rw [← Quotient.out_eq F]
  dsimp only [downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph, Quotient.lift_mk]
  apply div_pos
  · simp only [Nat.cast_pos]
    dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
    rw [Finset.card_pos]
    use F.out
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
    apply flagEqv.refl
  · simp only [Nat.cast_pos, Nat.div_pos_iff]
    constructor
    · exact Nat.factorial_pos (n - n₀)
    · apply Nat.factorial_le
      exact Nat.sub_le n n₀

theorem downwardNormalizingFactor_nonneg
    (F : Flag σ (Fin n))
    : downwardNormalizingFactor F ≥ 0
  :=
  le_of_lt (downwardNormalizingFactor_pos F)

theorem downwardNormalizingFactor_emptyFlag_pos
    : downwardNormalizingFactor (emptyFlag σ) > 0
  := by
  dsimp only [emptyFlag, downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph, Quotient.lift_mk]
  simp only [tsub_self, Nat.factorial_zero, Nat.div_one]
  apply div_pos <;> simp only [Nat.cast_pos]
  · dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
    rw [Set.toFinset_setOf, Finset.card_pos]
    use emptyLabeledGraph σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply flagEqv.refl
  · exact Nat.factorial_pos n₀

def unlabeledGraph {V : Type} (G : LabeledGraph σ V) : LabeledGraph ∅ₜ V where
  graph := G.graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.graph.Adj

theorem unlabeledGraph_iso
    (G G' : LabeledGraph σ V) (h : G ∼f G')
    : unlabeledGraph G ∼f unlabeledGraph G'
  := by
  let φ : G ≃f G' := h.some
  apply Nonempty.intro
  exact {
    graph_iso := φ.graph_iso
    type_preserve := List.ofFn_inj.mp rfl
  }

def unlabeledGraphQuot {V : Type} (G : LabeledGraph σ V) : Flag ∅ₜ V :=
  ⟦unlabeledGraph G⟧

theorem unlabeledGraphQuot_respect_eqv
    {G G' : LabeledGraph σ V} (h : G ∼f G')
    : unlabeledGraphQuot G = unlabeledGraphQuot G'
  :=
  Quotient.sound (unlabeledGraph_iso G G' h)

noncomputable def unlabel {V : Type}
    : Flag σ V → Flag ∅ₜ V
  := by
  apply Quot.lift (fun G : LabeledGraph σ V => unlabeledGraphQuot G)
  intro G G' G_eqv
  exact unlabeledGraphQuot_respect_eqv G_eqv

noncomputable def downwardFlag (F : Flag σ (Fin n)) : FlagVector ∅ₜ :=
  downwardNormalizingFactor F • unitVector ⟨n, unlabel F⟩

noncomputable def downwardFlagVector : FlagVector σ → FlagVector ∅ₜ :=
  linearExtension (fun F : FinFlag σ => downwardFlag F.2)

noncomputable def downwardFlagVectorQuot (f : FlagVector σ) : FlagAlgebra ∅ₜ :=
  ⟦downwardFlagVector f⟧

lemma downwardFlagVector_zero
    : downwardFlagVector (0 : FlagVector σ) = 0
  := by
  simp only [downwardFlagVector, linearExtension_zero]

lemma downwardFlagVector_unitVector
    (F : FinFlag σ)
    : downwardFlagVector (unitVector F) = downwardFlag F.2
  := by
  simp only [downwardFlagVector, linearExtension_unitVector]

lemma downwardFlagVector_add
    (f f' : FlagVector σ)
    : downwardFlagVector (f + f') = downwardFlagVector f + downwardFlagVector f'
  := by
  simp only [downwardFlagVector, linearExtension_add]

lemma downwardFlagVector_sum
    (s : Finset ι) (c : ι → FlagVector σ)
    : downwardFlagVector (∑ i ∈ s, c i) = ∑ i ∈ s, downwardFlagVector (c i)
  := by
  simp only [downwardFlagVector, linearExtension_sum]

lemma downwardFlagVector_neg
    (f : FlagVector σ)
    : downwardFlagVector (-f) = -downwardFlagVector f
  := by
  simp only [downwardFlagVector, linearExtension_neg]

lemma downwardFlagVector_sub
    (f f' : FlagVector σ)
    : downwardFlagVector (f - f') = downwardFlagVector f - downwardFlagVector f'
  := by
  simp only [downwardFlagVector, linearExtension_sub]

lemma downwardFlagVector_smul
    (f : FlagVector σ) (r : ℝ)
    : downwardFlagVector (r • f) = r • downwardFlagVector f
  := by
  simp only [downwardFlagVector, linearExtension_smul]

noncomputable def labelExtensions
    {ℓ : ℕ} (F : FlagWithSize ∅ₜ ℓ) (σ : FlagType (Fin n₀))
    : Finset (FlagWithSize σ ℓ)
  :=
  { G : FlagWithSize σ ℓ | unlabel G = F }

set_option maxHeartbeats 500000 in
lemma flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions
    {ℓ ℓ' : ℕ} (F : FlagWithSize σ ℓ) (F' : FlagWithSize ∅ₜ ℓ') (hℓ : ℓ ≤ ℓ')
    : flagDensity₁ (unlabel F) F' * downwardNormalizingFactor F =
      ∑ G ∈ labelExtensions F' σ, flagDensity₁ F G * downwardNormalizingFactor G
  := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep F
  have hF_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) F = ℓ := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  let Fu := unlabeledGraph F
  have hFu_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) Fu = ℓ := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  have graph_eq_Fu_F : Fu.graph = F.graph := by simp only [unlabeledGraph, Fu]
  obtain ⟨F', rfl⟩ := Quotient.exists_rep F'
  have hF'_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) F' = ℓ' := by
        simp only [LabeledGraph.size, Fintype.card_fin]
  have n₀_le_ℓ : n₀ ≤ ℓ := by
    have := F.type_size_le_size
    simp_all only [FlagType.size, Fintype.card_fin, LabeledGraph.size]
  have n₀_le_ℓ' : n₀ ≤ ℓ' := Nat.le_trans n₀_le_ℓ hℓ

  conv =>
    lhs
    dsimp only [flagDensity₁, downwardNormalizingFactor]
    rw [← subflagDensity_eq_flagListDensity]
    dsimp only [subflagDensity, unlabel, unlabeledGraphQuot, labeledSubgraphDensityLifted, Quotient.lift_mk]

  let Ω := { (w, θ) : (Set (Fin ℓ')) × (Fin n₀ → Fin ℓ') | Function.Injective θ ∧ w.toFinset.card = ℓ ∧ Set.range θ ⊆ w }
  let inj_map := {θ : Fin n₀ → Fin ℓ' | Function.Injective θ}.toFinset
  have inj_map_card : inj_map.card = ℓ'.factorial / (ℓ' - n₀).factorial := by
    simp only [Set.toFinset_card, inj_map]
    have := @Fintype.card_embedding_eq (Fin n₀) (Fin ℓ') _ _ _
    simp only [Fintype.card_fin] at this
    rw [Nat.descFactorial_eq_div n₀_le_ℓ'] at this
    rw [← this]
    apply Finset.card_eq_of_equiv
    refine Equiv.ofBijective ?_ ?_
    · intro ⟨⟨θ, hθ⟩, _⟩
      use ⟨θ, hθ⟩
      simp only [Finset.mem_univ]
    · constructor
      · intro ⟨⟨θ, hθ⟩, _⟩ ⟨⟨θ', hθ'⟩, _⟩ h_eq
        simp_all only [Fintype.card_embedding_eq, Fintype.card_fin, Subtype.mk.injEq,
          Function.Embedding.mk.injEq, Set.coe_setOf, Set.mem_setOf_eq]
      · intro ⟨⟨θ, hθ⟩, _⟩
        use ⟨⟨θ, by simp only [Set.mem_setOf_eq]; exact hθ⟩, by simp only [Set.coe_setOf, Set.mem_setOf_eq, Finset.mem_univ]⟩
  let left_vtx (θ : Fin n₀ → Fin ℓ') := Finset.univ \ (Set.range θ).toFinset
  have card_eq : Ω.toFinset.card = Fintype.card (Σ θ : inj_map, combinations (left_vtx θ) (ℓ - n₀)) := by
    apply Finset.card_eq_of_equiv
    apply Equiv.ofBijective _ _
    · intro ⟨⟨w, θ⟩, hΩ⟩
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, Ω] at hΩ
      have hθ : θ ∈ inj_map := by
        simp_all only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, inj_map]
      have hw : w.toFinset \ (Set.range θ).toFinset ∈ combinations (left_vtx θ) (ℓ - n₀) := by
        simp only [combinations, Set.toFinset_range, Finset.mem_filter,
          Finset.mem_powerset, left_vtx]
        constructor
        · apply Finset.sdiff_subset_sdiff <;> simp only [Finset.subset_univ, subset_refl]
        · rw [Finset.card_sdiff (by simp_all only [Set.subset_toFinset, Finset.coe_image, Finset.coe_univ, Set.image_univ])]
          rw [hΩ.2.1, Finset.card_image_of_injective (Finset.univ) hΩ.1]
          simp only [Finset.card_univ, Fintype.card_fin]
      use ⟨⟨θ, hθ⟩, ⟨w.toFinset \ (Set.range θ).toFinset, hw⟩⟩
      simp only [Finset.mem_univ]
    · constructor
      · intro ⟨⟨w, θ⟩, hΩ⟩ ⟨⟨w', θ'⟩, hΩ'⟩ h_eq
        simp_all only [Subtype.mk.injEq, Prod.mk.injEq, Sigma.mk.injEq]
        obtain ⟨hθ, hw⟩ := h_eq
        simp only [and_true]
        have : w.toFinset = w'.toFinset := by
          apply eq_of_heq
          subst hθ
          simp_all only [heq_eq_eq, Subtype.mk.injEq]
          simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, Ω] at hΩ hΩ'
          rw [← Finset.sdiff_union_inter w.toFinset (Set.range θ).toFinset, ← Finset.sdiff_union_inter w'.toFinset (Set.range θ).toFinset, hw]
          have hw : w.toFinset ∩ (Set.range θ).toFinset = (Set.range θ).toFinset := by
            simp_all only [Set.image_univ, Set.toFinset_range, Finset.inter_eq_right, Set.subset_toFinset, Finset.coe_image, Finset.coe_univ]
          have hw' : w'.toFinset ∩ (Set.range θ).toFinset = (Set.range θ).toFinset := by
            simp_all only [Set.image_univ, Set.toFinset_range, Finset.inter_eq_right, Set.subset_toFinset, Finset.coe_image, Finset.coe_univ]
          rw [hw, hw']
        exact Set.toFinset_inj.mp this
      · intro ⟨⟨⟨θ, hθ⟩, ⟨w, hw⟩⟩, h⟩
        simp only [combinations, Finset.mem_filter, Finset.mem_powerset] at hw
        have w_disj : Disjoint w (Finset.image θ Finset.univ) := by
          simp only [Set.toFinset_range, left_vtx] at hw
          rw [Finset.disjoint_left]
          intro x hx
          exact (Finset.mem_sdiff.mp (hw.1 hx)).2
        use ⟨⟨w.toSet ∪ (Set.image θ Set.univ), θ⟩, by
          simp only [Set.image_univ, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, Ω]
          simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, inj_map] at hθ
          constructor <;> try constructor
          · exact hθ
          · simp only [Set.toFinset_union, Finset.toFinset_coe, Set.toFinset_range]
            rw [Finset.card_union_of_disjoint w_disj]
            rw [hw.2, Finset.card_image_of_injective (Finset.univ) hθ, Finset.card_univ, Fintype.card_fin]
            apply Nat.sub_add_cancel
            simp_all only [LabeledGraph.size, Fintype.card_fin, Finset.mem_univ]
          · simp only [Set.subset_union_right]⟩
        simp only [Set.image_univ, Set.toFinset_union, Finset.toFinset_coe, Set.toFinset_range,
          Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
        exact Finset.union_sdiff_cancel_right w_disj
  have hΩ_card : Ω.toFinset.card = inj_map.card * (ℓ' - n₀).choose (ℓ - n₀) := by
    rw [card_eq, Fintype.card_sigma]
    have : ∀ θ : inj_map, (combinations (left_vtx θ) (ℓ - n₀)).card = (ℓ' - n₀).choose (ℓ - n₀) := by
      intro ⟨θ, hθ⟩
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, inj_map] at hθ
      rw [comb_card]; congr
      rw [Finset.card_sdiff (by simp only [Finset.subset_univ])]; congr
      have := Finset.card_image_of_injective (Finset.univ) hθ
      simp_all only [Set.toFinset_range, Finset.card_univ, Fintype.card_fin]
    simp_all only [Fintype.card_coe, Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
  rw [inj_map_card] at hΩ_card

  let A : Finset Ω := { w | by
    obtain ⟨⟨w, θ⟩, h⟩ := w
    let G := (F'.graph.induce w)
    let θ : Fin n₀ → w := fun i ↦ ⟨θ i, h.2.2 (Set.mem_range_self i)⟩
    have hθ_inj : Function.Injective θ := by
      intro a b h_eq
      simp only [Subtype.mk.injEq, θ] at h_eq
      exact h.1 h_eq
    exact if hθ_model : ∀ {a b : Fin n₀}, G.Adj (θ a) (θ b) ↔ σ.Adj a b
      then Nonempty (⟨G, by exact { toEmbedding := ⟨θ, hθ_inj⟩, map_rel_iff' := hθ_model }⟩ ≃f F)
      else false
    }

  have P₁ : labeledSubgraphDensity Fu F' * downwardNormalizingFactor_labeledGraph F = A.card / Ω.toFinset.card := by
    dsimp only [labeledSubgraphDensity, downwardNormalizingFactor_labeledGraph]
    rw [div_mul_div_comm]
    congr
    · rw [← Nat.cast_mul, Nat.cast_inj, mul_comm]
      dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph, labeledSubgraphCount]
      rw [← Finset.card_product]
      apply Finset.card_eq_of_equiv
      apply Equiv.ofBijective _ _
      · intro ⟨⟨H, G⟩, h⟩
        simp only [Set.toFinset_setOf, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
        let iso_Fu_G := (Classical.choice h.2.2).symm
        have iso_F_H := h.1.2
        simp only [flagEqv] at iso_F_H
        let iso_H_F := (Classical.choice iso_F_H).symm
        let iso_G_Fu := Classical.choice h.2.2
        -- let θ : Fin n₀ → Fin ℓ' := fun i ↦ iso_Fu_G.graph_iso.toFun (iso_H_F.graph_iso.toFun (H.type_embed.toFun i))
        let θ : Fin n₀ → Fin ℓ' := fun i ↦ iso_Fu_G.graph_iso.toFun (F.type_embed.toFun i)
        use ⟨⟨G.subgraph.verts, θ⟩, by
          simp only [Set.mem_setOf_eq, Ω]
          constructor <;> try constructor
          · intro u v h_eq
            simp [θ] at h_eq
            apply Subtype.ext at h_eq
            simp_all only [EmbeddingLike.apply_eq_iff_eq]
          · have : G.size = ℓ := by
              rw [← hFu_size, Eq.comm]
              have := @labeledGraphIso_size_eq _ _ _ _ _ _ _ _ _ _ iso_Fu_G
              exact this
            simp_all only [Set.toFinset_card, Fintype.card_ofFinset, LabeledSubgraph.size]
          · intro w hw
            obtain ⟨w', hw'⟩ := hw
            subst hw'
            simp only [LabeledSubgraph.coe_graph, Function.Embedding.toFun_eq_coe,
              RelEmbedding.coe_toEmbedding, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
              Subtype.coe_prop, θ]⟩
        simp only [SimpleGraph.comap_adj, Function.Embedding.subtype_apply, Bool.false_eq_true,
          dite_else_false, Finset.mem_filter, Finset.mem_univ, true_and, A]
        have hθ_model : ∀ {a b : Fin n₀}, F'.graph.Adj (θ a) (θ b) ↔ σ.Adj a b := by
          intro a b
          have ha := congrFun iso_H_F.type_preserve a
          have hb := congrFun iso_H_F.type_preserve b
          simp only [Function.comp_apply] at ha hb
          rw [type_embed_Adj_iff F]
          have : ∀ u v : Fin ℓ, Fu.graph.Adj u v ↔ F.graph.Adj u v := by
            exact fun u v ↦ SimpleGraph.adj_congr_of_sym2 Fu.graph rfl
          rw [← this, ← iso_Fu_G.graph_iso.map_adj_iff]
          have ha_in_G : θ a ∈ G.subgraph.verts := by
            simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
              Subtype.coe_prop, θ]
          have hb_in_G : θ b ∈ G.subgraph.verts := by
            simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
              Subtype.coe_prop, θ]
          constructor
          · intro hF'_adj
            have := h.2.1 ha_in_G hb_in_G hF'_adj
            simp only [LabeledSubgraph.coe_graph, Function.Embedding.toFun_eq_coe,
              RelEmbedding.coe_toEmbedding, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, θ] at this
            simp_all only [LabeledSubgraph.coe_graph, Subtype.coe_prop, SimpleGraph.Subgraph.coe_adj, θ]
          · intro hG_adj
            simp only [LabeledSubgraph.coe_graph, Function.Embedding.toFun_eq_coe,
              RelEmbedding.coe_toEmbedding, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, θ]
            exact
              SimpleGraph.Subgraph.Adj.adj_sub' G.subgraph
                (iso_Fu_G.graph_iso (F.type_embed a))
                (iso_Fu_G.graph_iso (F.type_embed b)) hG_adj
            -- rw [ha, hb]
            -- exact
            --   SimpleGraph.Subgraph.Adj.adj_sub' G.subgraph
            --     (iso_Fu_G.graph_iso (F.type_embed a))
            --     (iso_Fu_G.graph_iso (F.type_embed b)) hG_adj
        use hθ_model
        apply Nonempty.intro
        refine { graph_iso := ?_, type_preserve := ?_ }
        · simp only
          -- sorry
          have : G.coe.graph = SimpleGraph.induce G.subgraph.verts F'.graph := by
            ext u v
            simp only [LabeledSubgraph.coe_graph, SimpleGraph.Subgraph.coe_adj,
              SimpleGraph.comap_adj, Function.Embedding.subtype_apply]
            constructor
            · exact fun h_adj ↦ SimpleGraph.Subgraph.Adj.adj_sub' G.subgraph u v h_adj
            · exact fun h_adj ↦ (SimpleGraph.Subgraph.IsInduced.adj h.2.1).mpr h_adj
          rw [← this, ← graph_eq_Fu_F]
          exact iso_G_Fu.graph_iso
        · ext k
          simp only [LabeledSubgraph.coe_graph, eq_mpr_eq_cast, cast_eq, id_eq, RelEmbedding.coe_mk,
            Function.Embedding.coeFn_mk, Function.comp_apply]
          sorry
      · constructor
        · intro ⟨⟨H, G⟩, h⟩  ⟨⟨H', G'⟩, h'⟩ h_eq
          simp only [Set.toFinset_setOf, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h h'
          simp at h_eq
          simp only [Subtype.mk.injEq, Prod.mk.injEq]
          constructor
          · apply LabeledGraph.ext _ _
            · sorry
            · sorry
          · apply labeledSubgraph_eq_from_subgraph_eq
            exact inducedSubgraph_eq_verts h.2.1 h'.2.1 h_eq.1
        · intro ⟨⟨⟨w, θ⟩, hΩ⟩, hA⟩
          simp only [Set.mem_setOf_eq, Ω] at hΩ
          obtain ⟨hθ_inj, hw_card, hw⟩ := hΩ
          simp only [Bool.false_eq_true, dite_else_false, Finset.mem_filter, Finset.mem_univ, true_and, A] at hA
          obtain ⟨hθ, iso_H_F⟩ := hA
          let iso_H_F := Classical.choice iso_H_F
          let w_equiv : w ≃ Fin ℓ := by exact (isoFromFinToFiniteSet w hw_card).symm
          let H := labeledGraphFromVertexIso (labeledGraphIso_extract_graph iso_H_F) w_equiv
          let G := LabeledSubgraph.inducedLabeledSubgraph F' w (by
            intro x hx
            simp only [LabeledGraph.type_verts, Set.image_univ, Matrix.range_empty, Set.mem_empty_iff_false] at hx)
          use ⟨⟨H, G⟩, by
            simp only [Set.toFinset_setOf, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor <;> constructor
            · dsimp [H, labeledGraphFromVertexIso]
              sorry
            · sorry
            · simp only [LabeledSubgraph.inducedLabeledSubgraph_isInduced, G]
            · apply Nonempty.intro
              refine { graph_iso := ?_, type_preserve := ?_ }
              · simp only [LabeledSubgraph.coe_graph, G]
                sorry
              · ext k
                exact Fin.elim0 k⟩
          simp only [LabeledSubgraph.inducedLabeledSubgraph_verts, Subtype.mk.injEq, Prod.mk.injEq, true_and, G]
          sorry
    · simp only [emptyType_size, tsub_zero]
      rw [hF'_size, hFu_size, hΩ_card]
      have lhs : ↑(ℓ'.choose ℓ) * ↑(ℓ.factorial / (ℓ - n₀).factorial) = (ℓ'.factorial / ((ℓ' - ℓ).factorial * (ℓ - n₀).factorial) : ℚ) := by
        rw [Nat.choose_eq_factorial_div_factorial hℓ]
        rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hℓ) (by
          simp only [Nat.cast_mul, ne_eq, mul_eq_zero, Rat.natCast_eq_zero, not_or]
          constructor <;> simp only [Nat.factorial_ne_zero, not_false_eq_true]),
          Nat.cast_mul]
        rw [Nat.cast_div (by apply Nat.factorial_dvd_factorial; omega) (by
          simp only [ne_eq, Rat.natCast_eq_zero, Nat.factorial_ne_zero, not_false_eq_true])]
        field_simp
        rw [mul_assoc, mul_assoc]
      have rhs : ↑(ℓ'.factorial / (ℓ' - n₀).factorial * (ℓ' - n₀).choose (ℓ - n₀)) = (ℓ'.factorial / ((ℓ' - ℓ).factorial * (ℓ - n₀).factorial) : ℚ) := by
        rw [Nat.cast_mul, Nat.cast_div (by apply Nat.factorial_dvd_factorial; omega) (by
          simp only [ne_eq, Rat.natCast_eq_zero, Nat.factorial_ne_zero, not_false_eq_true])]
        rw [Nat.choose_eq_factorial_div_factorial (by omega)]
        rw [Nat.sub_sub, Nat.add_sub_of_le n₀_le_ℓ]
        rw [Nat.cast_div (by
          have div := @Nat.factorial_mul_factorial_dvd_factorial (ℓ'-n₀) (ℓ' - ℓ) (by omega)
          have : (ℓ' - n₀ - (ℓ' - ℓ)) = ℓ - n₀ := by omega
          rwa [mul_comm, this] at div) (by
          simp only [Nat.cast_mul, ne_eq, mul_eq_zero, Rat.natCast_eq_zero, not_or]
          constructor <;> simp only [Nat.factorial_ne_zero, not_false_eq_true])]
        field_simp; left
        rw [mul_comm]
      rw [lhs, rhs]
  rw [P₁]

  let Gs : Finset (LabeledGraph σ (Fin ℓ')) := (labelExtensions ⟦F'⟧ σ).image (fun G ↦ by exact G.out)
  have sum_eq : ∑ G ∈ labelExtensions ⟦F'⟧ σ, flagDensity₁ ⟦F⟧ G * downwardNormalizingFactor G = (∑ G' ∈ Gs, (labeledSubgraphCount F G' * isomorphismCount G')) / Ω.toFinset.card := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_bij
            (fun G _ ↦ G.out)
            (by simp only [Finset.mem_image, Quotient.out_inj, exists_eq_right, imp_self, implies_true, Gs])
            (by simp only [Quotient.out_inj, imp_self, implies_true])
    · intro G' hG'
      simp [Gs] at hG'
      obtain ⟨G, hG⟩ := hG'
      use G
    · intro G hG
      obtain ⟨G, rfl⟩ := Quotient.exists_rep G
      have hG_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) G = ℓ' := by
        simp only [LabeledGraph.size, Fintype.card_fin]
      dsimp only [flagDensity₁, downwardNormalizingFactor]
      rw [← subflagDensity_eq_flagListDensity]
      dsimp only [subflagDensity, unlabel, unlabeledGraphQuot, labeledSubgraphDensityLifted, Quotient.lift_mk]
      simp only [labeledSubgraphDensity, FlagType.size, Fintype.card_fin, downwardNormalizingFactor_labeledGraph]
      field_simp
      rw [mul_comm] at hΩ_card
      rw [hG_size, hF_size, ← Nat.cast_mul, ← Nat.cast_mul, ← hΩ_card]
      simp only [Nat.cast_mul, Set.toFinset_card, Fintype.card_ofFinset]
      have density_eq :  labeledSubgraphCount F G = labeledSubgraphCount F (@Quotient.mk (LabeledGraph σ (Fin ℓ')) (labeledGraphSetoid σ (Fin ℓ')) G).out := by
        have : G ≃f (@Quotient.mk (LabeledGraph σ (Fin ℓ')) (labeledGraphSetoid σ (Fin ℓ')) G).out := by
          dsimp [Quotient.mk, labeledGraphSetoid, flagEqv]
          -- rw [Quotient.out_eq]
          -- exact flagEqv.refl
          sorry

        sorry
      have iso_eq : isomorphismCount G = isomorphismCount (@Quotient.mk (LabeledGraph σ (Fin ℓ')) (labeledGraphSetoid σ (Fin ℓ')) G).out := by
        sorry
      rw [density_eq, iso_eq]
  rw [sum_eq]
  congr

  sorry

lemma downwardFlag_eqv_sum_flagDensity_smul_downwardFlag
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : downwardFlag F.2 ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardFlag G
  := by
  calc
    _ = (downwardNormalizingFactor F.2) • unitVector ⟨F.1, unlabel F.2⟩ := rfl
    _ ∼v (downwardNormalizingFactor F.2) • densityFlagSum ⟨F.1, unlabel F.2⟩ ℓ := by
      apply flagVectorEqv_smul
      exact unitVector_eqv_densityFlagSum _ ℓ hℓ
    _ ∼v (downwardNormalizingFactor F.2) • (∑ G : FlagWithSize ∅ₜ ℓ, flagDensity₁ (unlabel F.2) G • unitVector ⟨ℓ, G⟩) := by
      apply flagVectorEqv_smul
      rfl
    _ ∼v ∑ G : FlagWithSize ∅ₜ ℓ, ∑ G' ∈ labelExtensions G σ,
          flagDensity₁ F.2 G' • downwardNormalizingFactor G' • unitVector ⟨ℓ, G⟩ := by
      rw [Finset.smul_sum]
      apply flagVectorEqv_sum
      intro G _
      rw [smul_smul, mul_comm, flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions _ _ hℓ]
      simp only [rat_smul_eq_real_smul, Rat.cast_sum, Rat.cast_mul]
      rw [sum_smul]
      apply flagVectorEqv_sum
      intro G' _
      rw [smul_smul]
    _ ∼v ∑ G : FlagWithSize ∅ₜ ℓ, ∑ G' ∈ Finset.filter (fun G' ↦ unlabel G' = G) Finset.univ,
          flagDensity₁ F.2 G' • downwardNormalizingFactor G' • unitVector ⟨ℓ, unlabel G'⟩ := by
      apply flagVectorEqv_sum
      intro G _
      apply flagVectorEqv_sum
      intro G' hG'
      iterate 2 (apply flagVectorEqv_smul)
      dsimp [labelExtensions] at hG'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG'
      rw [hG']
    _ ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardNormalizingFactor G • unitVector ⟨ℓ, unlabel G⟩ := by
      rw [Finset.sum_fiberwise _ (fun G => unlabel G)]
    _ ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardFlag G := by
      apply flagVectorEqv_sum
      intro G _
      rfl

lemma downwardFlagVector_zeroElement_zeroSpace
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : downwardFlagVector (zeroElement F ℓ) ∈ ZeroSpace ∅ₜ
  := by
  dsimp [downwardFlagVector]
  let S : Finset (FinFlag σ) := (Finset.univ : Finset (FlagWithSize σ ℓ)).map {
    toFun := fun F' => ⟨ℓ, F'⟩
    inj' := fun F₁' F₂' h => by injection h
  }
  have h_supp : (zeroElement F ℓ).support ⊆ S ∪ {F} := by
    dsimp [zeroElement]
    calc
      _ ⊆ (unitVector F).support ∪ (densityFlagSum F ℓ).support := Finsupp.support_sub
      _ ⊆ S ∪ {F} := by
        rw [Finset.union_comm]
        apply Finset.union_subset_union
        · dsimp [densityFlagSum]
          apply Finset.Subset.trans Finsupp.support_finset_sum
          apply Finset.biUnion_subset.mpr
          intro G _
          apply Finset.Subset.trans Finsupp.support_smul
          simp only [unitVector_support, Finset.singleton_subset_iff, Finset.mem_map,
            Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, exists_apply_eq_apply, S]
        · simp only [unitVector_support, subset_refl]
  have h_supp_outside : ∀ G ∈ S ∪ {F},
    G ∉ (zeroElement F ℓ).support → (zeroElement F ℓ) G • downwardFlag G.2 = 0 := by
    intro G _ hG
    simp only [smul_eq_zero]; left
    exact Finsupp.notMem_support_iff.mp hG
  rw [linearExtension, Finset.sum_subset h_supp h_supp_outside]
  have hF_iff : F ∈ S ↔ F.1 = ℓ := by
    constructor
    · intro hF
      simp_all only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, S]
      obtain ⟨G, hG⟩ := hF
      subst hG
      simp_all only
    · intro hF
      subst hF
      simp only [Finset.mem_map, Finset.mem_univ, true_and, S]
      exact exists_apply_eq_apply _ F.2
  have h₁ : ∀ G ∈ S, G ≠ F → (zeroElement F ℓ) G = -(flagDensity₁ F.2 G.2) := by
    intro G hG h_G_neq_F
    simp only [zeroElement, densityFlagSum]
    rw [Finsupp.sub_apply, Finset.sum_apply', unitVector_apply_other F G h_G_neq_F.symm]
    simp only [zero_sub, neg_inj]
    have h_Gℓ : G.1 = ℓ := by
      simp_all only [Finset.mem_map, Finset.mem_univ, true_and, S]
      obtain ⟨w, h⟩ := hG
      subst h
      simp only [Function.Embedding.coeFn_mk]
    subst h_Gℓ
    rw [Finset.sum_eq_single_of_mem G.2]
    · simp only [Sigma.eta, rat_smul_eq_real_smul, Finsupp.coe_smul, Pi.smul_apply,
        unitVector_apply_self, smul_eq_mul, mul_one]
    · simp only [Finset.mem_univ]
    · intro G' _ hG'
      rw [Finsupp.smul_apply, unitVector_apply_other, smul_zero]
      contrapose! hG'
      simp only [ne_eq] at *
      rw [Sigma.ext_iff] at hG'
      simp only [heq_eq_eq, true_and] at hG'
      exact hG'
  have h₂ : (zeroElement F ℓ) F = if F ∈ S then 0 else 1 := by
    dsimp [zeroElement, densityFlagSum]
    simp only [unitVector_apply_self]
    rw [Finset.sum_apply']
    split
    next h =>
      rw [hF_iff] at h
      subst h
      rw [Finset.sum_eq_single_of_mem F.2]
      · simp only [flagDensity_self, Rat.cast_one, Sigma.eta, one_smul, unitVector_apply_self, sub_self]
      · simp only [Finset.mem_univ]
      · intro G _ hG
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero, Rat.cast_eq_zero]
        left
        exact flagDensity_other hG.symm
    next h =>
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, sub_eq_self]
      apply Finset.sum_eq_zero
      intro G _
      simp only [mul_eq_zero]
      right
      apply unitVector_apply_other_size
      symm; simp only
      rw [ne_eq, ← hF_iff]
      exact h
  have h₃ : ∑ G ∈ S ∪ {F}, (zeroElement F ℓ) G • downwardFlag G.2 =
      downwardFlag F.2 - ∑ G ∈ S, (flagDensity₁ F.snd G.snd) • downwardFlag G.2 := by
    by_cases hF : F ∈ S
    · have hF_S : S ∪ {F} = (S \ {F}) ∪ {F} := Eq.symm Finset.sdiff_union_self_eq_union
      have hF_S' : S = (S \ {F}) ∪ {F} := by
        rw [← hF_S, Finset.left_eq_union]
        simp only [Finset.singleton_subset_iff, hF]
      have h_disjoint : Disjoint (S \ {F}) {F} := Finset.sdiff_disjoint
      have h₂' : (zeroElement F ℓ) F = 1 - flagDensity₁ F.2 F.2 := by
        rw [h₂]
        simp only [hF, reduceIte, flagDensity_self, Rat.cast_one, sub_self]
      rw [hF_S, Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm, h₂', sub_smul, one_smul, sub_add]
      congr
      nth_rw 2 [hF_S']
      rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro G hG
      have h_G_S : G ∈ S := by
        have : S \ {F} ⊆ S := Finset.sdiff_subset
        exact this hG
      have h_G_neq_F : G ≠ F := by
        intro h; subst h
        revert hG
        simp only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, imp_self]
      rw [h₁ G h_G_S h_G_neq_F]
      simp only [neg_smul, neg_neg, rat_smul_eq_real_smul]
    · have h_disjoint : Disjoint S {F} := Finset.disjoint_singleton_right.mpr hF
      have h₁' : ∀ G ∈ S, (zeroElement F ℓ) G = -(flagDensity₁ F.2 G.2) := by
        intro G hG
        have h_G_neq_F : G ≠ F := ne_of_mem_of_not_mem hG hF
        exact h₁ G hG h_G_neq_F
      have h₂' : (zeroElement F ℓ) F = 1 := by
        rw [h₂]
        exact if_neg hF
      rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm, h₂', one_smul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro G hG
      rw [h₁' G hG]
      simp only [neg_smul, rat_smul_eq_real_smul]
  have h₄ : ∑ G ∈ S, (flagDensity₁ F.snd G.snd) • downwardFlag G.2 =
    ∑ G' : FlagWithSize σ ℓ, flagDensity₁ F.2 G' • downwardFlag G' := by
    simp only [Function.Embedding.coeFn_mk, Finset.sum_map, S]
  rw [h₃, h₄]
  exact downwardFlag_eqv_sum_flagDensity_smul_downwardFlag F ℓ hℓ

lemma downwardFlagVector_zeroSpace
    (f : FlagVector σ) (f_zero : f ∈ ZeroSpace σ)
    : downwardFlagVector f ∈ ZeroSpace ∅ₜ
  := by
  have ⟨I, hI, c, v, hv_zero, hf⟩ := zeroSpace_eq_sum_spanElement f f_zero
  rw [hf, downwardFlagVector_sum]
  apply zeroSpace_closed_under_sum
  intro i _
  rw [downwardFlagVector_smul]
  apply zeroSpace_closed_under_smul
  have ⟨F, ℓ, hℓ, hvi⟩ := hv_zero i
  rw [hvi]
  exact downwardFlagVector_zeroElement_zeroSpace F ℓ hℓ

lemma downwardFlagVectorQuot_zero
    : downwardFlagVectorQuot (0 : FlagVector σ) = 0
  := by
  apply Quotient.sound
  show downwardFlagVector (0 : FlagVector σ) - 0 ∈ ZeroSpace ∅ₜ
  rw [downwardFlagVector_zero, sub_self]
  simp only [Submodule.zero_mem]

lemma downwardFlagVectorQuot_add
    (f f' : FlagVector σ)
    : downwardFlagVectorQuot (f + f') = downwardFlagVectorQuot f + downwardFlagVectorQuot f'
  := by
  apply Quotient.sound
  show downwardFlagVector (f + f') - (downwardFlagVector f + downwardFlagVector f') ∈ ZeroSpace ∅ₜ
  rw [← downwardFlagVector_add, sub_self]
  simp only [Submodule.zero_mem]

lemma downwardFlagVectorQuot_neg
    (f : FlagVector σ)
    : downwardFlagVectorQuot (-f) = -(downwardFlagVectorQuot f)
  := by
  apply Quotient.sound
  simp only [neg_smul, one_smul]
  rw [downwardFlagVector_neg]

lemma downwardFlagVectorQuot_smul
    (f : FlagVector σ) (r : ℝ)
    : downwardFlagVectorQuot (r • f) = r • downwardFlagVectorQuot f
  := by
  apply Quotient.sound
  rw [downwardFlagVector_smul]

lemma downwardFlagVectorQuot_respect_eqv
    {f f' : FlagVector σ} (h : f ∼v f')
    : downwardFlagVectorQuot f = downwardFlagVectorQuot f'
  := by
  apply Quotient.sound
  show downwardFlagVector f - downwardFlagVector f' ∈ ZeroSpace ∅ₜ
  rw [← downwardFlagVector_sub]
  exact downwardFlagVector_zeroSpace (f - f') h

noncomputable def downward
    : FlagAlgebra σ → FlagAlgebra ∅ₜ
  := by
  apply Quot.lift (fun g : FlagVector σ => downwardFlagVectorQuot g)
  intro f f' f_eqv
  exact downwardFlagVectorQuot_respect_eqv f_eqv

notation "⟦" f "⟧₀" => (downward f)

theorem downward_zero
    : ⟦(0 : FlagAlgebra σ)⟧₀ = 0
  := by
  exact downwardFlagVectorQuot_zero

theorem downward_add
    (f f' : FlagAlgebra σ)
    : ⟦f + f'⟧₀ = ⟦f⟧₀ + ⟦f'⟧₀
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq f']
  apply downwardFlagVectorQuot_add

theorem downward_sum
    {ι : Type*} (s : Finset ι) (c : ι → FlagAlgebra σ)
    : ⟦∑ i ∈ s, c i⟧₀ = ∑ i ∈ s, ⟦c i⟧₀
  := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, downward_zero]
  · intro r R hr ih
    simp only [Finset.sum_insert hr, downward_add, ih]

theorem downward_neg
    (f : FlagAlgebra σ)
    : ⟦-f⟧₀ = -⟦f⟧₀
  := by
  rw [← Quotient.out_eq f, ← neg_quot]
  apply downwardFlagVectorQuot_neg

theorem downward_sub
    (f f' : FlagAlgebra σ)
    : ⟦f - f'⟧₀ = ⟦f⟧₀ - ⟦f'⟧₀
  := by
  simp only [sub_eq_add_neg, downward_add, downward_neg]

theorem downward_smul
    (f : FlagAlgebra σ) (r : ℝ)
    : ⟦r • f⟧₀ = r • ⟦f⟧₀
  := by
  rw [← Quotient.out_eq f, ← smul_quot]
  apply downwardFlagVectorQuot_smul
