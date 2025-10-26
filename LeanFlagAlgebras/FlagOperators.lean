import «LeanFlagAlgebras».FlagAlgebra
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Cast.Field

open FlagAlgebras
open LabeledSubgraph
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

lemma fun_eq_of_comp_eq_left
    {α β γ : Type} {g g' : α → β} {f : β → γ} (hf : Function.Injective f) (h : f ∘ g = f ∘ g')
    : g = g'
  := by
  funext x
  have : f (g x) = f (g' x) := by
    show (f ∘ g) x = (f ∘ g') x
    rw [h]
  exact hf this

theorem isomorphismCount_eq_of_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : isomorphismCount G = isomorphismCount G'
  := by
  dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
  apply Finset.card_eq_of_equiv
  apply Equiv.ofBijective _ _
  · intro ⟨H, hH⟩
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at *
    let φGG' := h.some.graph_iso
    let φGH := hH.2.some.graph_iso
    use {
      graph := G'.graph
      type_embed := {
        toFun := φGG' ∘ φGH ∘ φGG'.symm ∘ G'.type_embed
        inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
        map_rel_iff' := by
          intro a b
          simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
          rw [SimpleGraph.Iso.map_adj_iff φGG']
          simp_rw [hH.1]
          rw [SimpleGraph.Iso.map_adj_iff φGH, SimpleGraph.Iso.map_adj_iff φGG'.symm]
          exact SimpleGraph.Embedding.map_adj_iff G'.type_embed
      }
    }
    simp only [true_and]
    apply Nonempty.intro
    exact {
      graph_iso := by
        apply φGG'.symm.trans
        apply φGH.trans
        simp_rw [← hH.1]
        exact φGG'
      type_preserve := by
        ext v
        simp only [eq_mpr_eq_cast, id_eq, SimpleGraph.Iso.coe_comp, Function.comp_apply,
          RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
        congr 3
        · exact hH.1.symm
        · rw [hH.1]
        · exact cast_heq _ _
    }
  · constructor
    · intro ⟨H₁, hH₁⟩ ⟨H₂, hH₂⟩ h_eq
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hH₁ hH₂
      have hH_graph_eq : H₁.graph = H₂.graph := by rw [← hH₁.1, hH₂.1]
      simp only [eq_mpr_eq_cast, cast_inj, Subtype.mk.injEq, LabeledGraph.mk.injEq,
        heq_eq_eq, RelEmbedding.mk.injEq, Function.Embedding.mk.injEq, true_and] at h_eq
      apply fun_eq_of_comp_eq_left (RelIso.injective _) at h_eq
      have hGG'_type_preserve := h.some.symm.type_preserve
      dsimp only [LabeledGraphIso.symm] at hGG'_type_preserve
      rw [hGG'_type_preserve] at h_eq
      rw [hH₁.2.some.type_preserve, hH₂.2.some.type_preserve] at h_eq
      simp only [Subtype.mk.injEq]
      ext a b
      · rw [hH_graph_eq]
      · apply heq_of_cast_eq ?_ ?_
        · rw [hH_graph_eq]
        · ext v
          congr 1
          calc
            _ = H₁.type_embed v := by
              congr
              · rw [hH_graph_eq]
              · rw [hH_graph_eq]
              · exact cast_heq _ _
            _ = H₂.type_embed v := by rw [h_eq]
    · intro ⟨H', hH'⟩
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hH'
      rcases hH' with ⟨hH'_graph_eq, hH'_iso⟩
      simp only [eq_mpr_eq_cast, Subtype.exists, Set.toFinset_setOf, Finset.mem_filter,
        Finset.mem_univ, true_and]
      let φGG' := h.some.graph_iso
      let φG'H' := hH'_iso.some.graph_iso
      let H : LabeledGraph σ (Fin n) := {
        graph := G.graph
        type_embed := {
          toFun := φGG'.symm ∘ H'.type_embed
          inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
          map_rel_iff' := by
            intro a b
            simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
            rw [type_embed_Adj_iff H']
            simp_rw [← hH'_graph_eq]
            rw [SimpleGraph.Iso.map_adj_iff φGG'.symm]
        }
      }
      have hH_graph_eq : G.graph = H.graph := by dsimp only [H]
      let hH_iso : G ∼f H := Nonempty.intro {
        graph_iso := by
          apply φGG'.trans
          apply φG'H'.trans
          simp_rw [← hH'_graph_eq]
          exact φGG'.symm
        type_preserve := by
          simp only [H, eq_mpr_eq_cast, SimpleGraph.Iso.coe_comp,
            RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
          ext v
          simp only [Function.comp_apply]
          congr 2
          · rw [hH'_graph_eq]
          · rw [hH'_graph_eq]
          · exact cast_heq _ _
          · rw [← hH'_iso.some.type_preserve, ← h.some.type_preserve]
            rfl
      }
      use H, ⟨hH_graph_eq, hH_iso⟩
      rw [cast_eq_iff_heq]
      refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
      · intro
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
      · ext a b
        · simp only [hH'_graph_eq]
        · simp only
          apply heq_of_cast_eq ?_ ?_
          · rw [hH'_graph_eq]
          · ext v
            congr 1
            let φGH := hH_iso.some.graph_iso
            let K : LabeledGraph σ (Fin n) := {
              graph := G'.graph
              type_embed := {
                toFun := φGG' ∘ φGH ∘ φGG'.symm ∘ G'.type_embed
                inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
                map_rel_iff' := by
                  intro a b
                  simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
                  rw [SimpleGraph.Iso.map_adj_iff φGG']
                  simp_rw [hH_graph_eq]
                  rw [SimpleGraph.Iso.map_adj_iff φGH, SimpleGraph.Iso.map_adj_iff φGG'.symm]
                  exact SimpleGraph.Embedding.map_adj_iff G'.type_embed
              }
            }
            calc
              _ = K.type_embed v := by
                congr
                · simp only [hH'_graph_eq, K]
                · simp only [hH'_graph_eq, K]
                · simp only [cast_heq_iff_heq, heq_eq_eq, RelEmbedding.mk.injEq,
                  Function.Embedding.mk.injEq, K]
                  rfl
              _ = H'.type_embed v := by
                simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, K]
                have := h.some.symm.type_preserve
                dsimp only [LabeledGraphIso.symm] at this
                rw [this, hH_iso.some.type_preserve]
                simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
                  Function.comp_apply, RelIso.apply_symm_apply, H]

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
    {G G' : LabeledGraph σ V} (h : G ∼f G')
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
  Quotient.sound (unlabeledGraph_iso h)

noncomputable def unlabel {V : Type}
    : Flag σ V → Flag ∅ₜ V
  := by
  apply Quot.lift (fun G : LabeledGraph σ V => unlabeledGraphQuot G)
  intro G G' G_eqv
  exact unlabeledGraphQuot_respect_eqv G_eqv

theorem unlabel_eq_iff_unlabeledGraph_eqv
    {F : LabeledGraph σ V} {G : LabeledGraph ∅ₜ V}
    : unlabel ⟦F⟧ = ⟦G⟧ ↔ unlabeledGraph F ∼f G
  := by
  constructor <;> intro h
  · simp only [unlabel, unlabeledGraphQuot, Quotient.lift_mk] at h
    exact Quotient.exact h
  · exact Quotient.sound h

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

def injectiveMapSet
    (n₀ ℓ ℓ' : ℕ)
    : Set ((Set (Fin ℓ')) × (Fin n₀ → Fin ℓ'))
  :=
  { (w, θ) : (Set (Fin ℓ')) × (Fin n₀ → Fin ℓ') |
    Function.Injective θ ∧ w.toFinset.card = ℓ ∧ Set.range θ ⊆ w }

def isoInjectiveMapSet'''
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : Set (injectiveMapSet n₀ ℓ ℓ')
  :=
  { w | by
    obtain ⟨⟨w, θ⟩, h⟩ := w
    let G := F'.graph.induce w
    let θ : Fin n₀ → w := fun i ↦ ⟨θ i, h.2.2 (Set.mem_range_self i)⟩
    have hθ_inj : Function.Injective θ := by
      intro a b h_eq
      simp only [Subtype.mk.injEq, θ] at h_eq
      exact h.1 h_eq
    exact if hθ_model : ∀ {a b : Fin n₀}, G.Adj (θ a) (θ b) ↔ σ.Adj a b
      then Nonempty (⟨G, { toEmbedding := ⟨θ, hθ_inj⟩, map_rel_iff' := hθ_model }⟩ ≃f F)
      else false
  }

def isoInjectiveMapSet''
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : Set (Σ (W : Set (Fin ℓ')), (Fin n₀ → W))
  :=
  { ⟨W, θ⟩ | Function.Injective θ ∧ W.toFinset.card = ℓ ∧
    ∀ {a b : Fin n₀}, F'.graph.Adj (θ a) (θ b) ↔ σ.Adj a b ∧
    ∃ (φ : (inducedSubgraph F'.graph W).coe ≃g F.graph), φ ∘ θ = F.type_embed }

def isoInjectiveMapSet
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : Set ((Set (Fin ℓ')) × (Fin n₀ → Fin ℓ'))
  :=
  { (W, θ) : (Set (Fin ℓ')) × (Fin n₀ → Fin ℓ') |
    Function.Injective θ ∧ W.toFinset.card = ℓ ∧
    (∀ {a b : Fin n₀}, F'.graph.Adj (θ a) (θ b) ↔ σ.Adj a b) ∧
    (∃ (h_range : Set.range θ ⊆ W) (φ : (inducedSubgraph F'.graph W).coe ≃g F.graph),
      φ ∘ (fun i ↦ ⟨θ i, h_range (Set.mem_range_self i)⟩) = F.type_embed) }

def isoInjectiveMapSet'
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : Set (injectiveMapSet n₀ ℓ ℓ')
  :=
  { w | by
    obtain ⟨⟨w, θ⟩, h⟩ := w
    simp [injectiveMapSet] at h
    exact if hθ_model : ∀ {a b : Fin n₀}, F'.graph.Adj (θ a) (θ b) ↔ σ.Adj a b
      then Nonempty (⟨(F'.graph.induce w : SimpleGraph w),
                      { toEmbedding := ⟨fun i => ⟨θ i, h.2.2 (Set.mem_range_self i)⟩,
                                        by intro a b h_eq;
                                           simp only [Subtype.mk.injEq] at h_eq;
                                           exact h.1 h_eq⟩,
                        map_rel_iff' := hθ_model }⟩ ≃f F)
      else false
  }

-- Not needed anymore
theorem injectiveMapSet_card
    {n₀ ℓ ℓ' : ℕ} (hℓ : n₀ ≤ ℓ) (hℓ' : ℓ ≤ ℓ')
    : (injectiveMapSet n₀ ℓ ℓ').toFinset.card = ℓ'.factorial / ((ℓ' - ℓ).factorial * (ℓ - n₀).factorial)
  := by
  let Ω := injectiveMapSet n₀ ℓ ℓ'
  have n₀_le_ℓ' : n₀ ≤ ℓ' := Nat.le_trans hℓ hℓ'
  let inj_map := {θ : Fin n₀ → Fin ℓ' | Function.Injective θ}.toFinset
  have inj_map_card : inj_map.card = ℓ'.factorial / (ℓ' - n₀).factorial := by
    simp only [Set.toFinset_card, inj_map]
    have : Fintype.card (Fin n₀ ↪ Fin ℓ') = ℓ'.factorial / (ℓ' - n₀).factorial := by
      simp only [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_eq_div n₀_le_ℓ'
    rw [← this]
    apply Finset.card_eq_of_equiv
    apply Equiv.ofBijective _ _
    · exact fun ⟨⟨θ, hθ⟩, _⟩ ↦ ⟨⟨θ, hθ⟩, by simp only [Finset.mem_univ]⟩
    · constructor
      · intro ⟨⟨θ, hθ⟩, _⟩ ⟨⟨θ', hθ'⟩, _⟩ h_eq
        simp_all only [Fintype.card_embedding_eq, Fintype.card_fin, Subtype.mk.injEq,
          Function.Embedding.mk.injEq, Set.coe_setOf, Set.mem_setOf_eq]
      · intro ⟨⟨θ, hθ⟩, _⟩
        use ⟨⟨θ, by simp only [Set.mem_setOf_eq]; exact hθ⟩, by simp only [Set.coe_setOf, Set.mem_setOf_eq, Finset.mem_univ]⟩
  let left_vtx (θ : Fin n₀ → Fin ℓ') := Finset.univ \ (Set.range θ).toFinset
  have Ω_card : Ω.toFinset.card = Fintype.card (Σ θ : inj_map, combinations (left_vtx θ) (ℓ - n₀)) := by
    apply Finset.card_eq_of_equiv
    apply Equiv.ofBijective _ _
    · intro ⟨⟨w, θ⟩, hΩ⟩
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, Ω, injectiveMapSet] at hΩ
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
          simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, Ω, injectiveMapSet] at hΩ hΩ'
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
          simp only [Set.image_univ, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, Ω, injectiveMapSet]
          simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, inj_map] at hθ
          constructor <;> try constructor
          · exact hθ
          · simp only [Set.toFinset_union, Finset.toFinset_coe, Set.toFinset_range]
            rw [Finset.card_union_of_disjoint w_disj]
            rw [hw.2, Finset.card_image_of_injective (Finset.univ) hθ, Finset.card_univ, Fintype.card_fin]
            apply Nat.sub_add_cancel
            simp_all only [Finset.mem_univ]
          · simp only [Set.subset_union_right]⟩
        simp only [Set.image_univ, Set.toFinset_union, Finset.toFinset_coe, Set.toFinset_range,
          Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
        exact Finset.union_sdiff_cancel_right w_disj
  rw [Ω_card, Fintype.card_sigma]
  have inj_comb_card : ∀ θ : inj_map, (combinations (left_vtx θ) (ℓ - n₀)).card = (ℓ' - n₀).choose (ℓ - n₀) := by
    intro ⟨θ, hθ⟩
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, inj_map] at hθ
    rw [comb_card]; congr
    rw [Finset.card_sdiff (by simp only [Finset.subset_univ])]; congr
    simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fintype.card_sigma,
      Finset.univ_eq_attach, Fintype.card_coe, Finset.card_univ, Fintype.card_fin]
    simp_all only [Set.toFinset_range, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  simp_all only [Fintype.card_coe, Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
  rw [Nat.choose_eq_factorial_div_factorial (by omega), Nat.sub_sub_sub_cancel_right hℓ]
  have : (ℓ - n₀).factorial * (ℓ' - ℓ).factorial ∣ (ℓ' - n₀).factorial := by
    rw [← Nat.dvd_div_iff_mul_dvd]
    · have : ℓ - n₀ = (ℓ' - n₀) - (ℓ' - ℓ) := by omega
      rw [this, ← Nat.descFactorial_eq_div (by omega)]
      exact Nat.factorial_dvd_descFactorial (ℓ' - n₀) (ℓ' - ℓ)
    · exact Nat.factorial_dvd_factorial (by omega)
  rw [← Nat.mul_div_assoc _ this, Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.sub_le ℓ' n₀)), mul_comm]

theorem isoInjectiveMapSet_card_eq_isomorphismCount_mul_labeledSubgraphCount
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ')) (hℓ : ℓ ≤ ℓ')
    : (isoInjectiveMapSet F F').toFinset.card = isomorphismCount F * labeledSubgraphCount (unlabeledGraph F) F'
  := by
  have hF_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) F = ℓ := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  let Fu := unlabeledGraph F
  have hFu_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) Fu = ℓ := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  have graph_eq_Fu_F : Fu.graph = F.graph := by simp only [unlabeledGraph, Fu]
  have hF'_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) F' = ℓ' := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  have n₀_le_ℓ : n₀ ≤ ℓ := by
    have := F.type_size_le_size
    simp_all only [FlagType.size, Fintype.card_fin, LabeledGraph.size]
  have n₀_le_ℓ' : n₀ ≤ ℓ' := Nat.le_trans n₀_le_ℓ hℓ

  have tttttttttttt : (isoInjectiveMapSet F F').toFinset.card = (isoInjectiveMapSet''' F F').toFinset.card := sorry
  rw [tttttttttttt]

  symm
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
      simp only [injectiveMapSet, Set.mem_setOf_eq]
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
    simp only [isoInjectiveMapSet''', SimpleGraph.comap_adj, Function.Embedding.subtype_apply, Bool.false_eq_true,
      dite_else_false]
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
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
      simp only [injectiveMapSet, Set.mem_setOf_eq] at hΩ
      obtain ⟨hθ_inj, hw_card, hw⟩ := hΩ
      simp only [isoInjectiveMapSet''', Bool.false_eq_true, dite_else_false] at hA
      simp only [SimpleGraph.comap_adj, Function.Embedding.subtype_apply, Set.toFinset_setOf,
        Finset.mem_filter, Finset.mem_univ, true_and] at hA
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

theorem unlabeledGraphEq
    {ℓ : ℕ} {G₁ G₂ : LabeledGraph σ (Fin ℓ)} (h : G₁.graph = G₂.graph)
    : unlabeledGraph G₁ = unlabeledGraph G₂
  := by
  simp only [unlabeledGraph, LabeledGraph.mk.injEq, h, true_and]
  refine heq_of_eq_cast ?_ ?_
  · rw [h]
  . ext t
    exact Fin.elim0 t

theorem isoInjectiveMapSet_card_eq_isomorphismCount_mul_labeledSubgraphCount'
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ')) (hℓ : ℓ ≤ ℓ')
    : (isoInjectiveMapSet F F').toFinset.card = isomorphismCount F * labeledSubgraphCount (unlabeledGraph F) F'
  := by
  let S₁ : Set ((LabeledGraph σ (Fin ℓ)) × LabeledSubgraph ∅ₜ F') :=
    { (G, G') | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧ G'.IsInduced ∧ Nonempty (G'.coe ≃f (unlabeledGraph F))}
  let S₂ : Set ((LabeledGraph σ (Fin ℓ)) × Set (Fin ℓ')) :=
    { (G, W) | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧
       Nonempty ((inducedSubgraph F'.graph W).coe ≃g F.graph) }

  -- Maybe S₂' is right.
  -- let S₂' : Set ((LabeledGraph σ (Fin ℓ)) × Set (Fin ℓ')) :=
  --   { (G, W) | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧
  --      Nonempty ((inducedSubgraph F'.graph W).coe ≃g G.graph) }

  let S₃ : Set ((LabeledGraph σ (Fin ℓ)) × Set (Fin ℓ')) :=
    { (G, W) |
      G.graph = F.graph ∧
      (∃ (φ : Nonempty (F ≃f G)) (ψ : Nonempty ((inducedSubgraph F'.graph W).coe ≃g F.graph))
      (ϕ : (inducedSubgraph F'.graph W).coe ≃g G.graph), ϕ = φ.some.graph_iso ∘ ψ.some) }
  let S₄ : Set (Set (Fin ℓ') × (Fin n₀ → Fin ℓ')) := isoInjectiveMapSet F F'

  have h_S₁_iso_S₂ : S₁ ≃ S₂ :=
    let f_S₁_S₂ : S₁ → S₂ := by
      intro ⟨⟨G, G'⟩, hG_graph_eq, hG_iso_F, hG'_ind, hG'_iso_Fu⟩
      refine ⟨⟨G, G'.subgraph.verts⟩, hG_graph_eq, hG_iso_F, ?_⟩
      apply Nonempty.intro
      let φ := hG'_iso_Fu.some.graph_iso
      rw [inducedLabeledSubgraph_eq hG'_ind] at φ
      simp only [inducedLabeledSubgraph, coe_graph, unlabeledGraph] at φ
      exact φ
    have h_f_S₁_S₂_inj : Function.Injective f_S₁_S₂ := by
      intro ⟨⟨G₁, G₁'⟩, hG₁_graph_eq, hG₁_iso_F, hG₁'_ind, hG₁'_iso⟩ ⟨⟨G₂, G₂'⟩, hG₂_graph_eq, hG₂_iso_F, hG₂'_ind, hG₂'_iso⟩ h_eq
      simp [Subtype.mk.injEq, f_S₁_S₂] at h_eq
      obtain ⟨hG_eq, hW_eq⟩ := h_eq
      subst hG_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      have hG₁'G₂'_subgraph_eq : G₁'.subgraph = G₂'.subgraph := by
        rw [inducedLabeledSubgraph_eq hG₁'_ind, inducedLabeledSubgraph_eq hG₂'_ind]
        simp only [inducedLabeledSubgraph, hW_eq]
      exact labeledSubgraph_eq_from_subgraph_eq hG₁'G₂'_subgraph_eq
    have h_f_S₁_S₂_surj : Function.Surjective f_S₁_S₂ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hF'_ind_iso_F⟩
      have hW : F'.type_verts ⊆ W := by
        intro t ht
        simp only [LabeledGraph.type_verts, Set.image_univ, Matrix.range_empty,
          Set.mem_empty_iff_false] at ht
      use ⟨⟨G, inducedLabeledSubgraph F' W hW⟩, hG_graph_eq, hG_iso_F, ?_, ?_⟩
      · simp only [inducedLabeledSubgraph_verts, f_S₁_S₂]
      · simp only [inducedLabeledSubgraph_isInduced]
      · apply Nonempty.intro
        exact {
          graph_iso := by
            simp only [inducedLabeledSubgraph, coe_graph, unlabeledGraph]
            exact hF'_ind_iso_F.some
          type_preserve := by
            ext k
            exact Fin.elim0 k
        }
    Equiv.ofBijective f_S₁_S₂ ⟨h_f_S₁_S₂_inj, h_f_S₁_S₂_surj⟩
  have h_S₂_iso_S₃ : S₂ ≃ S₃ :=
    let f_S₂_S₃ : S₂ → S₃ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hF'_ind_iso_F⟩
      refine ⟨⟨G, W⟩, hG_graph_eq, ?_⟩
      let φ := hG_iso_F.some
      let ψ := hF'_ind_iso_F.some
      let ϕ := φ.graph_iso.comp ψ
      refine ⟨hG_iso_F, hF'_ind_iso_F, ϕ, ?_⟩
      simp only [SimpleGraph.Iso.coe_comp, ϕ, φ, ψ]
    have h_f_S₂_S₃_inj : Function.Injective f_S₂_S₃ := by
      intro ⟨⟨G₁, W₁⟩, hG₁_graph_eq, hG₁_iso_F, hF'_ind_iso_F₁⟩ ⟨⟨G₂, W₂⟩, hG₂_graph_eq, hG₂_iso_F, hF'_ind_iso_F₂⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_S₂_S₃] at h_eq
      simp_all only
    have h_f_S₂_S₃_surj : Function.Surjective f_S₂_S₃ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, h_exists⟩
      obtain ⟨φ, ψ, ϕ, h_eq⟩ := h_exists
      refine ⟨⟨⟨G, W⟩, hG_graph_eq, ?_⟩, ?_⟩
      · constructor
        · exact φ
        · exact ψ
      · simp only [f_S₂_S₃]
    Equiv.ofBijective f_S₂_S₃ ⟨h_f_S₂_S₃_inj, h_f_S₂_S₃_surj⟩
  have h_S₃_iso_S₄ : S₃ ≃ S₄ :=
    let f_S₃_S₄ : S₃ → S₄ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, h⟩
      sorry
    have h_f_S₃_S₄_inj : Function.Injective f_S₃_S₄ := by
      sorry
    have h_f_S₃_S₄_surj : Function.Surjective f_S₃_S₄ := by
      sorry
    Equiv.ofBijective f_S₃_S₄ ⟨h_f_S₃_S₄_inj, h_f_S₃_S₄_surj⟩

  -- New Definition -----------------------------------------

  let S₂ : Set ((LabeledGraph σ (Fin ℓ)) × Set (Fin ℓ')) :=
    { ⟨G, W⟩ | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧
      ∃ (h : F'.type_verts ⊆ W), Nonempty ((inducedLabeledSubgraph F' W h).coe ≃f (unlabeledGraph F)) }
  let S₃ : Set ((LabeledGraph σ (Fin ℓ)) × Set (Fin ℓ')) :=
    { ⟨G, W⟩ | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧
      ∃ (h : F'.type_verts ⊆ W), Nonempty ((inducedLabeledSubgraph F' W h).coe ≃f (unlabeledGraph G)) }
  let S₄ : Set (Set (Fin ℓ') × (Fin n₀ → Fin ℓ')) := isoInjectiveMapSet F F'

  have h_S₁_iso_S₂ : S₁ ≃ S₂ :=
    let f_S₁_S₂ : S₁ → S₂ := by
      intro ⟨⟨G, G'⟩, hG_graph_eq, hG_iso_F, hG'_ind, hG'_iso_Fu⟩
      refine ⟨⟨G, G'.subgraph.verts⟩, hG_graph_eq, hG_iso_F, ?_, ?_⟩
      · exact labeledSubgraph_contain_type_verts F' G'
      · rw [← inducedLabeledSubgraph_eq hG'_ind]
        exact hG'_iso_Fu
    have h_f_S₁_S₂_inj : Function.Injective f_S₁_S₂ := by
      intro ⟨⟨G₁, G₁'⟩, hG₁_graph_eq, hG₁_iso_F, hG₁'_ind, hG₁'_iso⟩ ⟨⟨G₂, G₂'⟩, hG₂_graph_eq, hG₂_iso_F, hG₂'_ind, hG₂'_iso⟩ h_eq
      simp [Subtype.mk.injEq, f_S₁_S₂] at h_eq
      obtain ⟨hG_eq, hW_eq⟩ := h_eq
      subst hG_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      have hG₁'G₂'_subgraph_eq : G₁'.subgraph = G₂'.subgraph := by
        rw [inducedLabeledSubgraph_eq hG₁'_ind, inducedLabeledSubgraph_eq hG₂'_ind]
        simp only [inducedLabeledSubgraph, hW_eq]
      exact labeledSubgraph_eq_from_subgraph_eq hG₁'G₂'_subgraph_eq
    have h_f_S₁_S₂_surj : Function.Surjective f_S₁_S₂ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hW, hG_ind_iso⟩
      use ⟨⟨G, inducedLabeledSubgraph F' W hW⟩, hG_graph_eq, hG_iso_F, inducedLabeledSubgraph_isInduced F' W hW, hG_ind_iso⟩
      simp only [inducedLabeledSubgraph_verts, f_S₁_S₂]
    Equiv.ofBijective f_S₁_S₂ ⟨h_f_S₁_S₂_inj, h_f_S₁_S₂_surj⟩

  have h_S₂_iso_S₃ : S₂ ≃ S₃ :=
    let f_S₂_S₃ : S₂ → S₃ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hGW⟩
      refine ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, ?_, ?_⟩
      · simp only [LabeledGraph.type_verts, Set.image_univ, Matrix.range_empty, Set.empty_subset]
      . apply Nonempty.intro
        rw [unlabeledGraphEq hG_graph_eq]
        exact hGW.2.some
    have h_f_S₂_S₃_inj : Function.Injective f_S₂_S₃ := by
      intro ⟨⟨G₁, W₁⟩, hG₁_graph_eq, hG₁_iso_F, hG₁W⟩ ⟨⟨G₂, W₂⟩, hG₂_graph_eq, hG₂_iso_F, hG₂W⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_S₂_S₃] at h_eq
      simp_all only
    have h_f_S₂_S₃_surj : Function.Surjective f_S₂_S₃ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hGW⟩
      use ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, ?_, ?_⟩
      · simp only [LabeledGraph.type_verts, Set.image_univ, Matrix.range_empty, Set.empty_subset]
      · apply Nonempty.intro
        rw [← unlabeledGraphEq hG_graph_eq]
        exact hGW.2.some
    Equiv.ofBijective f_S₂_S₃ ⟨h_f_S₂_S₃_inj, h_f_S₂_S₃_surj⟩

  have h_S₃_iso_S₄ : S₃ ≃ S₄ :=
    let f_S₃_S₄ : S₃ → S₄ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hF_iso_G, hGW⟩
      let φF_G := hF_iso_G.some.graph_iso
      let φF'_ind := hGW.2.some.symm.graph_iso
      simp [inducedLabeledSubgraph, unlabeledGraph] at φF'_ind
      let θ : Fin n₀ → Fin ℓ' := fun i ↦ φF'_ind (G.type_embed i)
      have hθ_inj : Function.Injective θ := by
        intro a b h_eq
        apply Subtype.ext at h_eq
        simp_all only [EmbeddingLike.apply_eq_iff_eq]
      have hθ_range : Set.range θ ⊆ W := by
        intro y ⟨x, hx_eq⟩
        rw [← hx_eq]
        simp only [θ, Subtype.coe_prop]
      refine ⟨⟨W, θ⟩, hθ_inj, ?_, ?_, ?_⟩
      · have h_card_eq := SimpleGraph.Iso.card_eq φF'_ind
        simp only [Fintype.card_fin, inducedSubgraph] at h_card_eq
        rw [h_card_eq]
        simp only [Set.toFinset_card, Fintype.card_ofFinset]
      · intro a b
        constructor
        · intro hF'_adj
          sorry
          -- have hF'_ind_adj := (inducedLabeledSubgraph_isInduced F' W hW)
          --   (Subtype.coe_prop (φF'_ind (φF_G (F.type_embed a))))
          --   (Subtype.coe_prop (φF'_ind (φF_G (F.type_embed b)))) hF'_adj
          -- have hG_adj := (SimpleGraph.Iso.map_adj_iff φF'_ind.symm).mpr hF'_ind_adj
          -- simp only [RelIso.symm_apply_apply] at hG_adj
          -- rw [SimpleGraph.Iso.map_adj_iff φF_G, ← type_embed_Adj_iff F] at hG_adj
          -- exact hG_adj
        · intro hσ_adj
          sorry
          -- suffices (inducedLabeledSubgraph F' W hW).subgraph.Adj (θ a) (θ b) by
          --   exact
          --     SimpleGraph.Subgraph.Adj.adj_sub' (inducedLabeledSubgraph F' W hW).subgraph
          --       (φF'_ind (φF_G (F.type_embed a))) (φF'_ind (φF_G (F.type_embed b))) this
          -- rw [type_embed_Adj_iff F, ← SimpleGraph.Iso.map_adj_iff φF_G] at hσ_adj
          -- have hG_adj := (SimpleGraph.Iso.map_adj_iff φF'_ind).mpr hσ_adj
          -- exact hG_adj
      · sorry
    have h_f_S₃_S₄_inj : Function.Injective f_S₃_S₄ := by
      intro ⟨⟨G₁, W₁⟩, hG₁_graph_eq, hG₁_iso_F, hG₁W⟩ ⟨⟨G₂, W₂⟩, hG₂_graph_eq, hG₂_iso_F, hG₂W⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_S₃_S₄] at h_eq
      obtain ⟨hW_eq, hθ_eq⟩ := h_eq
      simp only [hW_eq, Subtype.mk.injEq, Prod.mk.injEq, and_true]
      have hG₁_graph_eq_G₂ : G₁.graph = G₂.graph := by rw [hG₁_graph_eq, hG₂_graph_eq]
      ext a b
      · rw [hG₁_graph_eq_G₂]
      · sorry
    have h_f_S₃_S₄_surj : Function.Surjective f_S₃_S₄ := by
      intro ⟨⟨W, θ⟩, hθ_inj, hW_card, hθ_adj_iff, hθ_range, hW_ind_iso, hθ_comp_eq⟩
      let G : LabeledGraph σ (Fin ℓ) := {
        graph := F.graph
        type_embed := {
          toFun := fun i ↦ hW_ind_iso ⟨(θ i),
            by apply hθ_range; simp only [Set.mem_range, exists_apply_eq_apply]⟩,
          inj' := by
            intro a b h_eq
            simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at h_eq
            exact hθ_inj h_eq,
          map_rel_iff' := by
            intro a b
            simp only [Function.Embedding.coeFn_mk]
            have ha := congrFun hθ_comp_eq a
            have hb := congrFun hθ_comp_eq b
            simp only [Function.comp_apply] at ha hb
            rw [ha, hb]
            exact SimpleGraph.Embedding.map_adj_iff F.type_embed }
      }
      refine ⟨⟨⟨G, W⟩, ?_⟩, ?_⟩
      · simp [S₃, G]
        sorry
      · simp [f_S₃_S₄]
        split
        rename_i G' W' hG_eq_F hF_iso_G hW' h_eq
        obtain ⟨hW', hF'_ind_iso_F⟩ := hW'
        simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq] at h_eq
        obtain ⟨hG_eq, hW_eq⟩ := h_eq
        subst hG_eq hW_eq
        simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        ext t
        congr
        have hθv := congrFun hθ_comp_eq t
        simp only [Function.comp_apply] at hθv
        sorry
    Equiv.ofBijective f_S₃_S₄ ⟨h_f_S₃_S₄_inj, h_f_S₃_S₄_surj⟩

  have h_S₂_iso_S₄ : S₂ ≃ S₄ :=
    let f_S₂_S₄ : S₂ → S₄ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hGW⟩
      have hW : F'.type_verts ⊆ W := hGW.1
      have hF'_ind_iso : Nonempty ((inducedLabeledSubgraph F' W hW).coe ≃f (unlabeledGraph F)) := hGW.2
      let φG_F := hG_iso_F.some.symm.graph_iso
      let φF'_ind := hF'_ind_iso.some.symm.graph_iso
      dsimp only [unlabeledGraph, coe_graph] at φF'_ind
      let φG_ind : G.graph ≃g (inducedLabeledSubgraph F' W hW).coe.graph := φF'_ind.comp φG_F

      let θ : Fin n₀ → Fin ℓ' := fun i ↦ (φF'_ind (φG_F (G.type_embed i))).val
      have hθ_inj : Function.Injective θ := by
        intro a b h_eq
        simp only [Subtype.coe_inj, θ] at h_eq
        have h_inj : Function.Injective (φF'_ind ∘ φG_F) := by
          apply Function.Injective.comp
          · exact φF'_ind.injective
          · exact φG_F.injective
        exact G.type_embed.injective (h_inj h_eq)
      have hθ_range : Set.range θ ⊆ W := by
        intro y ⟨x, hx_eq⟩
        rw [← hx_eq]
        simp only [θ, Subtype.coe_prop]
      refine ⟨⟨W, θ⟩, hθ_inj, ?_, ?_, ?_⟩
      · have h_card_eq := SimpleGraph.Iso.card_eq φF'_ind
        simp only [Fintype.card_fin, inducedLabeledSubgraph_verts] at h_card_eq
        rw [h_card_eq]
        simp only [Set.toFinset_card, Fintype.card_ofFinset]
      · intro a b
        constructor
        · intro hF'_adj
          have hF'_ind_adj := (inducedLabeledSubgraph_isInduced F' W hW)
            (Subtype.coe_prop (φF'_ind (φG_F (G.type_embed a))))
            (Subtype.coe_prop (φF'_ind (φG_F (G.type_embed b)))) hF'_adj
          have hG_adj : G.graph.Adj
            (φG_ind.symm ((φF'_ind (φG_F (G.type_embed a)))))
            (φG_ind.symm (φF'_ind (φG_F (G.type_embed b))))
            := (SimpleGraph.Iso.map_adj_iff φG_ind.symm).mpr hF'_ind_adj
          simp only [coe_graph, RelIso.symm_trans_apply, RelIso.symm_apply_apply,
            SimpleGraph.Embedding.map_adj_iff, φG_ind] at hG_adj
          exact hG_adj
        · intro hσ_adj
          suffices (inducedLabeledSubgraph F' W hW).subgraph.Adj (θ a) (θ b) by
            exact
              SimpleGraph.Subgraph.Adj.adj_sub' (inducedLabeledSubgraph F' W hW).subgraph
                (φF'_ind (φG_F (G.type_embed a))) (φF'_ind (φG_F (G.type_embed b))) this
          have hF_adj : F.graph.Adj (φF'_ind.symm (φF'_ind (φG_F (G.type_embed a)))) (φF'_ind.symm (φF'_ind (φG_F (G.type_embed b)))) := by
            simp only [RelIso.symm_apply_apply]
            have ha := congrFun hG_iso_F.some.symm.type_preserve a
            have hb := congrFun hG_iso_F.some.symm.type_preserve b
            simp only [Function.comp_apply] at ha hb
            simp only [φG_F]
            rw [ha, hb]
            exact (type_embed_Adj_iff F a b).mp hσ_adj
          exact (SimpleGraph.Iso.map_adj_iff φF'_ind.symm).mp hF_adj
      · use hθ_range
        use φF'_ind.symm
        ext t
        rw [← congrFun hG_iso_F.some.symm.type_preserve t]
        apply Fin.val_eq_of_eq
        simp only [Subtype.coe_eta, Function.comp_apply, θ, φG_F]
        exact RelIso.symm_apply_apply φF'_ind (hG_iso_F.some.symm.graph_iso (G.type_embed t))
    have h_f_S₂_S₄_inj : Function.Injective f_S₂_S₄ := by
      intro ⟨⟨G₁, W₁⟩, hG₁_graph_eq, hG₁_iso_F, hG₁W⟩ ⟨⟨G₂, W₂⟩, hG₂_graph_eq, hG₂_iso_F, hG₂W⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_S₂_S₄] at h_eq
      obtain ⟨hW_eq, hθ_eq⟩ := h_eq
      have hW₁ := hG₁W.1
      have hF'_ind_G := hG₁W.2.some
      have := unlabeledGraphEq hG₁_graph_eq
      rw [← this] at hF'_ind_G

      have hW₂ := hG₂W.1
      simp only [hW_eq, Subtype.mk.injEq, Prod.mk.injEq, and_true]
      ext a b
      · rw [hG₁_graph_eq, hG₂_graph_eq]
      · apply heq_of_cast_eq ?_ ?_
        · rw [hG₁_graph_eq, hG₂_graph_eq]
        · ext v
          have hv_eq := congrFun hθ_eq v
          have hG₁_v := congrFun hG₁_iso_F.some.type_preserve v
          have hG₂_v := congrFun hG₂_iso_F.some.type_preserve v
          simp only [Function.comp_apply] at hG₁_v hG₂_v
          have hG₁_v_eq : (hG₁_iso_F.some.symm.graph_iso (hG₁_iso_F.some.graph_iso (F.type_embed v))) = F.type_embed v := by
            exact (RelIso.eq_symm_apply hG₁_iso_F.some.symm.graph_iso).mp rfl
          have hG₂_v_eq : (hG₂_iso_F.some.symm.graph_iso (hG₂_iso_F.some.graph_iso (F.type_embed v))) = F.type_embed v := by
            exact (RelIso.eq_symm_apply hG₂_iso_F.some.symm.graph_iso).mp rfl
          rw [← hG₁_v, ← hG₂_v, hG₁_v_eq, hG₂_v_eq] at hv_eq
          subst hW_eq
          rw [Fin.val_eq_val]
          calc
            _ = G₁.type_embed v := by
              congr
              · rw [hG₁_graph_eq, hG₂_graph_eq]
              · rw [hG₁_graph_eq, hG₂_graph_eq]
              · exact cast_heq _ _
            _ = hG₁_iso_F.some.graph_iso (F.type_embed v) := Eq.symm hG₁_v
            _ = hG₂_iso_F.some.graph_iso (F.type_embed v) := by
              sorry
            _ = G₂.type_embed v := hG₂_v
    have h_f_S₂_S₄_surj : Function.Surjective f_S₂_S₄ := by
      intro ⟨⟨W, θ⟩, hθ_inj, hW_card, hθ_adj_iff, hθ_range, hW_ind_iso, hθ_comp_eq⟩
      let G : LabeledGraph σ (Fin ℓ) := {
        graph := F.graph
        type_embed := {
          toFun := fun i ↦ hW_ind_iso ⟨(θ i),
            by apply hθ_range; simp only [Set.mem_range, exists_apply_eq_apply]⟩,
          inj' := by
            intro a b h_eq
            simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at h_eq
            exact hθ_inj h_eq,
          map_rel_iff' := by
            intro a b
            simp only [Function.Embedding.coeFn_mk]
            have ha := congrFun hθ_comp_eq a
            have hb := congrFun hθ_comp_eq b
            simp only [Function.comp_apply] at ha hb
            rw [ha, hb]
            exact SimpleGraph.Embedding.map_adj_iff F.type_embed }
      }
      refine ⟨⟨⟨G, W⟩, ?_⟩, ?_⟩
      · simp only [Set.mem_setOf_eq, true_and, S₂, G]
        constructor
        · apply Nonempty.intro
          exact {
            graph_iso := by
              simp only
              exact SimpleGraph.Iso.refl
            type_preserve := by
              ext t
              simp only [id_eq, Function.comp_apply, RelIso.refl_apply, RelEmbedding.coe_mk,
                Function.Embedding.coeFn_mk]
              rw [← congrFun hθ_comp_eq t]
              simp only [Function.comp_apply]
          }
        · simp only [LabeledGraph.type_verts, Set.image_univ, Matrix.range_empty, Set.empty_subset,
          exists_true_left]
          apply Nonempty.intro
          exact {
            graph_iso := by
              simp only [inducedLabeledSubgraph, coe_graph, unlabeledGraph]
              exact hW_ind_iso
            type_preserve := by
              ext t
              exact Fin.elim0 t
          }
      · simp only [f_S₂_S₄]
        split
        rename_i G' W' hG_eq_F hF_iso_G hW' h_eq
        obtain ⟨hW', hF'_ind_iso_F⟩ := hW'
        simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq] at h_eq
        obtain ⟨hG_eq, hW_eq⟩ := h_eq
        simp only [hW_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
        ext v
        have : G.type_embed v = G'.type_embed v := by
          rw [hG_eq]
        dsimp [G] at this
        sorry
    Equiv.ofBijective f_S₂_S₄ ⟨h_f_S₂_S₄_inj, h_f_S₂_S₄_surj⟩

  have hS₁_card : S₁.toFinset.card = isomorphismCount F * labeledSubgraphCount (unlabeledGraph F) F' := by
    dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph, labeledSubgraphCount]
    rw [← Finset.card_product]
    simp only [Set.toFinset_setOf]
    apply Finset.card_eq_of_equiv
    apply Equiv.ofBijective _ _
    · intro ⟨⟨G, G'⟩, h⟩
      use ⟨G, G'⟩
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S₁] at h
      simp_all only [flagEqv, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, and_self]
    · constructor
      · intro ⟨⟨G₁, G₁'⟩, h₁⟩ ⟨⟨G₂, G₂'⟩, h₂⟩ h_eq
        simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
      · intro ⟨⟨G, G'⟩, h⟩
        use ⟨⟨G, G'⟩, by
          simp_all only [flagEqv, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.toFinset_setOf, and_self, S₁]⟩
  rw [← hS₁_card]

  have h_S₁_iso_S₄ : S₁ ≃ S₄ := by
    calc
      S₁ ≃ S₂ := h_S₁_iso_S₂
      _ ≃ S₄ := h_S₂_iso_S₄
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S₁]
  simp only [Set.coe_setOf, S₁, S₄] at h_S₁_iso_S₄
  exact h_S₁_iso_S₄.symm

theorem isoInjectiveMapSet_card_eq_sum_labeledSubgraphCount_of_same_graph
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : (isoInjectiveMapSet F F').toFinset.card = ∑ G with G.graph = F'.graph, labeledSubgraphCount F G
  := by
  dsimp only [labeledSubgraphCount]
  rw [← Finset.card_sigma]

  let S₁ : Set ((G : LabeledGraph σ (Fin ℓ')) × LabeledSubgraph σ G) :=
    ({G | G.graph = F'.graph}.sigma fun G ↦ {G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f F)}.toFinset)
  let S₂ : Set ((G : LabeledGraph σ (Fin ℓ')) × LabeledSubgraph σ G) :=
    { ⟨G, G'⟩ | G.graph = F'.graph ∧ G'.IsInduced ∧ Nonempty (G'.coe ≃f F) }
  let S₃ : Set (LabeledGraph σ (Fin ℓ') × Set (Fin ℓ')) :=
    { ⟨G, W⟩ | G.graph = F'.graph ∧
      ∃ (h : G.type_verts ⊆ W), Nonempty ((inducedLabeledSubgraph G W h).coe ≃f F) }
  let S₄ : Set (Set (Fin ℓ') × (Fin n₀ → Fin ℓ')) := isoInjectiveMapSet F F'

  have h_S₁_eq_S₂ : S₁ = S₂ := by
    ext ⟨G, G'⟩
    simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_sigma_iff, Set.mem_setOf_eq, S₁, S₂]

  have h_S₂_iso_S₃ : S₂ ≃ S₃ :=
    let f_S₂_S₃ : S₂ → S₃ := by
      intro ⟨⟨G, G'⟩, hG_graph_eq, hG'_ind, hG'_iso⟩
      refine ⟨⟨G, G'.subgraph.verts⟩, hG_graph_eq, ?_, ?_⟩
      · exact labeledSubgraph_contain_type_verts G G'
      · rw [← inducedLabeledSubgraph_eq hG'_ind]
        exact hG'_iso
    have h_f_S₂_S₃_inj : Function.Injective f_S₂_S₃ := by
      intro ⟨⟨G₁, G₁'⟩, hG₁_graph_eq, hG₁'_ind, hG₁'_iso⟩ ⟨⟨G₂, G₂'⟩, hG₂_graph_eq, hG₂'_ind, hG₂'_iso⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_S₂_S₃] at h_eq
      obtain ⟨hG_eq, hW_eq⟩ := h_eq
      subst hG_eq
      simp only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
      have hG₁'G₂'_subgraph_eq : G₁'.subgraph = G₂'.subgraph := by
        rw [inducedLabeledSubgraph_eq hG₁'_ind, inducedLabeledSubgraph_eq hG₂'_ind]
        simp only [inducedLabeledSubgraph, hW_eq]
      exact labeledSubgraph_eq_from_subgraph_eq hG₁'G₂'_subgraph_eq
    have h_f_S₂_S₃_surj : Function.Surjective f_S₂_S₃ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hW, hG_ind_iso⟩
      use ⟨⟨G, inducedLabeledSubgraph G W hW⟩, hG_graph_eq, inducedLabeledSubgraph_isInduced G W hW, hG_ind_iso⟩
      simp only [inducedLabeledSubgraph_verts, f_S₂_S₃]
    Equiv.ofBijective f_S₂_S₃ ⟨h_f_S₂_S₃_inj, h_f_S₂_S₃_surj⟩

  have h_S₃_iso_S₄ : S₃ ≃ S₄ :=
    let f_S₃_S₄ : S₃ → S₄ := by
      intro ⟨⟨G, W⟩, hG_graph_eq, hGW⟩
      have hW : G.type_verts ⊆ W := hGW.1
      have hG_ind_iso : Nonempty ((inducedLabeledSubgraph G W hW).coe ≃f F) := hGW.2
      let φG_ind := hG_ind_iso.some.symm.graph_iso
      let θ : Fin n₀ → Fin ℓ' := fun i ↦ (φG_ind (F.type_embed i)).val
      have hθ_inj : Function.Injective θ := by
        intro a b h_eq
        simp only [coe_graph, θ, Subtype.coe_inj] at h_eq
        have h_inj : Function.Injective (φG_ind ∘ F.type_embed) := by
          apply Function.Injective.comp
          · exact RelIso.injective φG_ind
          · exact RelEmbedding.injective F.type_embed
        exact h_inj h_eq
      have hθ_range : Set.range θ ⊆ W := by
        intro y ⟨x, hx_eq⟩
        rw [← hx_eq]
        simp only [θ, coe_graph, Subtype.coe_prop]
      refine ⟨⟨W, θ⟩, hθ_inj, ?_, ?_, ?_⟩
      · have h_card_eq := SimpleGraph.Iso.card_eq φG_ind
        simp only [Fintype.card_fin, inducedLabeledSubgraph_verts] at h_card_eq
        rw [h_card_eq]
        simp only [Set.toFinset_card, Fintype.card_ofFinset]
      · intro a b
        rw [← hG_graph_eq]
        simp only [θ]
        show G.graph.Adj ((φG_ind ∘ F.type_embed) a) ((φG_ind ∘ F.type_embed) b) ↔ σ.Adj a b
        rw [hG_ind_iso.some.symm.type_preserve]
        simp only [inducedLabeledSubgraph, coe_graph, coe_type_embed, RelEmbedding.coe_mk,
          Function.Embedding.coeFn_mk, SimpleGraph.Embedding.map_adj_iff]
      · have h_type_eq : (inducedLabeledSubgraph G W hW).coe.graph = (inducedSubgraph F'.graph W).coe := by
          rw [← hG_graph_eq]
          simp only [inducedLabeledSubgraph, coe_graph]
        let φG_ind_inv : (inducedSubgraph F'.graph W).coe ≃g F.graph := by
          rw [← h_type_eq]
          exact hG_ind_iso.some.graph_iso
        have h_φG_ind_inv_comp : φG_ind_inv ∘ φG_ind = id := by
          ext v
          simp only [coe_graph, eq_mpr_eq_cast, φG_ind_inv, φG_ind, Function.comp_apply, id_eq, Fin.val_eq_val]
          calc
            _ = hG_ind_iso.some.graph_iso (hG_ind_iso.some.symm.graph_iso v) := by
              have : (inducedSubgraph F'.graph W).coe = (inducedLabeledSubgraph G W hW).coe.graph := by
                rw [← hG_graph_eq]
                simp only [inducedLabeledSubgraph, coe_graph]
              congr 2
              · rw [this]
              · exact cast_heq _ _
            _ = v := by simp only [coe_graph, LabeledGraphIso.symm, RelIso.apply_symm_apply]
        use hθ_range, φG_ind_inv
        simp only [coe_graph, Subtype.coe_eta, θ]
        show (φG_ind_inv ∘ φG_ind) ∘ F.type_embed = F.type_embed
        rw [h_φG_ind_inv_comp, Function.id_comp]
    have h_f_S₃_S₄_inj : Function.Injective f_S₃_S₄ := by
      intro ⟨⟨G₁, W₁⟩, hG₁_graph_eq, hW₁, hG₁_iso⟩ ⟨⟨G₂, W₂⟩, hG₂_graph_eq, hW₂, hG₂_iso⟩ h_eq
      simp only [coe_graph, Subtype.mk.injEq, Prod.mk.injEq, f_S₃_S₄] at h_eq
      obtain ⟨hW_eq, hθ_eq⟩ := h_eq
      have hG_graph_eq : G₁.graph = G₂.graph := by rw [hG₁_graph_eq, ← hG₂_graph_eq]
      simp only [hW_eq, Subtype.mk.injEq, Prod.mk.injEq, and_true]
      ext a b
      · rw [hG_graph_eq]
      · apply heq_of_cast_eq ?_ ?_
        · rw [hG_graph_eq]
        · ext v
          rw [Fin.val_eq_val]
          calc
            _ = G₁.type_embed v := by
              congr
              · rw [hG_graph_eq]
              · rw [hG_graph_eq]
              · exact cast_heq _ _
            _ = (inducedLabeledSubgraph G₁ W₁ hW₁).coe.type_embed v := by congr
            _ = hG₁_iso.some.symm.graph_iso (F.type_embed v) := by
              rw [← hG₁_iso.some.symm.type_preserve]
              congr
            _ = (fun i ↦ ↑(hG₁_iso.some.symm.graph_iso (F.type_embed i))) v := rfl
            _ = hG₂_iso.some.symm.graph_iso (F.type_embed v) := by rw [hθ_eq]
            _ = (inducedLabeledSubgraph G₂ W₂ hW₂).coe.type_embed v := by
              rw [← hG₂_iso.some.symm.type_preserve]
              congr
            _ = G₂.type_embed v := by congr
    have h_f_S₃_S₄_surj : Function.Surjective f_S₃_S₄ := by
      intro ⟨⟨W, θ⟩, hθ_inj, hW_card, hθ_adj_iff, hθ_range, hW_ind_iso, hθ_comp_eq⟩
      let G : LabeledGraph σ (Fin ℓ') := {
        graph := F'.graph
        type_embed := { toFun := θ, inj' := hθ_inj, map_rel_iff' := hθ_adj_iff }
      }
      refine ⟨⟨(G, W), ?_⟩, ?_⟩
      · simp only [Set.mem_setOf_eq, S₃]
        constructor
        · simp only [G]
        · refine ⟨?_, ?_⟩
          · simp only [LabeledGraph.type_verts, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
            Set.image_univ, hθ_range, G]
          · exact Nonempty.intro { graph_iso := hW_ind_iso, type_preserve := hθ_comp_eq }
      · simp only [coe_graph, f_S₃_S₄]
        split
        rename_i hGW G' W' hG'_graph_eq hW' h_eq
        obtain ⟨hW, hW_iso⟩ := hW'
        simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq] at h_eq
        obtain ⟨hG_eq, hW_eq⟩ := h_eq
        subst hG_eq hW_eq
        simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        ext v
        rw [Fin.val_eq_val]
        show (hW_iso.some.symm.graph_iso ∘ F.type_embed) v = θ v
        rw [hW_iso.some.symm.type_preserve]
        simp only [inducedLabeledSubgraph, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
          coe_graph, coe_type_embed, G]
    Equiv.ofBijective f_S₃_S₄ ⟨h_f_S₃_S₄_inj, h_f_S₃_S₄_surj⟩

  have h_S₁_iso_S₄ : S₁ ≃ S₄ := by
    calc
      S₁ ≃ S₂ := by rw [h_S₁_eq_S₂]
      _ ≃ S₃ := h_S₂_iso_S₃
      _ ≃ S₄ := h_S₃_iso_S₄
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset, Set.toFinset_setOf, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, S₁,
    S₄] at h_S₁_iso_S₄
  exact h_S₁_iso_S₄.symm

theorem isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledSubgraphCount
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : (isoInjectiveMapSet F F').toFinset.card = ∑ G ∈ labelExtensions ⟦F'⟧ σ, isomorphismCount G.out * labeledSubgraphCount F G.out
  := by
  let S_F' : Finset (LabeledGraph σ (Fin ℓ')) := {G | G.graph = F'.graph}.toFinset
  rw [isoInjectiveMapSet_card_eq_sum_labeledSubgraphCount_of_same_graph F F']
  symm
  calc
    _ = ∑ G ∈ labelExtensions ⟦F'⟧ σ, {H ∈ S_F' | ⟦H⟧ = G}.card * labeledSubgraphCount F G.out := by
      apply Finset.sum_congr rfl
      intro G hGF'
      rcases Quotient.exists_rep G with ⟨G, rfl⟩
      dsimp only [labelExtensions] at hGF'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hGF'
      rw [unlabel_eq_iff_unlabeledGraph_eqv] at hGF'
      congr
      have hG_iso : (⟦G⟧ : FlagWithSize σ ℓ').out ∼f G := by
        show ⟦G⟧.out ≈ G
        exact Quotient.eq_mk_iff_out.mp rfl
      rw [isomorphismCount_eq_of_eqv hG_iso]
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
          graph_iso := by
            dsimp only [G']
            exact hGF'.some.graph_iso
          type_preserve := by
            simp only [id_eq, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, G']
        }
      calc
        _ = {H | G'.graph = H.graph ∧ G' ∼f H}.toFinset.card := by
          have := isomorphismCount_eq_of_eqv hGG'_iso
          dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph] at this
          rw [this]
          congr!
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
            · dsimp only [G']
              rw [h_graph_eq]
            · exact hGG'_iso.symm.trans h_iso.symm
    _ = ∑ G ∈ labelExtensions ⟦F'⟧ σ, ∑ G' ∈ S_F' with ⟦G'⟧ = G, labeledSubgraphCount F (⟦G'⟧ : FlagWithSize σ ℓ').out := by
      apply Finset.sum_congr rfl
      intro G _
      rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      apply Finset.sum_congr rfl
      intro G' hG'
      simp only [Finset.mem_filter] at hG'
      rw [hG'.2]
    _ = ∑ G ∈ S_F', labeledSubgraphCount F (⟦G⟧ : FlagWithSize σ ℓ').out := by
      have h_quot_labelExt : ∀ G ∈ S_F', ⟦G⟧ ∈ labelExtensions ⟦F'⟧ σ := by
        intro G hG
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S_F'] at hG
        simp only [labelExtensions, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [unlabel_eq_iff_unlabeledGraph_eqv]
        apply Nonempty.intro
        exact {
          graph_iso := by
            dsimp only [unlabeledGraph]
            rw [hG]
          type_preserve := List.ofFn_inj.mp rfl
        }
      have := @Finset.sum_fiberwise_of_maps_to _ _ _ _ _ _ _ (fun G ↦ ⟦G⟧) h_quot_labelExt (fun G ↦ labeledSubgraphCount F (⟦G⟧ : FlagWithSize σ ℓ').out)
      rw [← this]
      congr!
    _ = ∑ G ∈ S_F', labeledSubgraphCount F G := by
      apply Finset.sum_congr rfl
      intro G _
      apply labeledSubgraphCount_respect_eqv
      · apply Classical.choice
        show ⟦G⟧.out ≈ G
        exact Quotient.eq_mk_iff_out.mp rfl
      · exact LabeledGraphIso.refl
    _ = ∑ G with G.graph = F'.graph, labeledSubgraphCount F G := by
      simp only [Set.toFinset_setOf, S_F']

theorem flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions
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
  obtain ⟨F', rfl⟩ := Quotient.exists_rep F'
  have hF'_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) F' = ℓ' := by
        simp only [LabeledGraph.size, Fintype.card_fin]
  have n₀_le_ℓ : n₀ ≤ ℓ := by
    have := F.type_size_le_size
    simp_all only [FlagType.size, Fintype.card_fin, LabeledGraph.size]

  let A := (isoInjectiveMapSet F F').toFinset
  let ω := ℓ'.factorial / ((ℓ' - ℓ).factorial * (ℓ - n₀).factorial)
  conv =>
    lhs
    dsimp only [flagDensity₁, downwardNormalizingFactor]
    rw [← subflagDensity_eq_flagListDensity]
    dsimp only [subflagDensity, unlabel, unlabeledGraphQuot, labeledSubgraphDensityLifted, Quotient.lift_mk]

  have lhs : labeledSubgraphDensity Fu F' * downwardNormalizingFactor_labeledGraph F = A.card / ω := by
    dsimp only [labeledSubgraphDensity, downwardNormalizingFactor_labeledGraph]
    rw [div_mul_div_comm]
    congr
    · rw [← Nat.cast_mul, Nat.cast_inj, mul_comm]
      rw [isoInjectiveMapSet_card_eq_isomorphismCount_mul_labeledSubgraphCount F F' hℓ]
    · simp only [emptyType_size, tsub_zero, ← Nat.cast_mul, Nat.cast_inj]
      rw [hF'_size, hFu_size, Nat.choose_eq_factorial_div_factorial hℓ]
      have : ℓ.factorial ∣ ℓ'.factorial / (ℓ' - ℓ).factorial := by
        rw [← Nat.descFactorial_eq_div hℓ]
        exact Nat.factorial_dvd_descFactorial ℓ' ℓ
      rw [mul_comm ℓ.factorial, ← Nat.div_div_eq_div_mul, ← Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.sub_le ℓ n₀)), Nat.div_mul_cancel this, Nat.div_div_eq_div_mul]

  have rhs : ∑ G ∈ labelExtensions ⟦F'⟧ σ, flagDensity₁ ⟦F⟧ G * downwardNormalizingFactor G = A.card / ω := by
    rw [isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledSubgraphCount F F']
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro G hG
    rcases Quotient.exists_rep G with ⟨G, rfl⟩
    simp only [labelExtensions, unlabel, unlabeledGraphQuot, Finset.mem_filter, Finset.mem_univ,
      Quotient.lift_mk, true_and] at hG
    dsimp only [flagDensity₁, downwardNormalizingFactor]
    rw [← subflagDensity_eq_flagListDensity]
    dsimp only [subflagDensity, unlabel, unlabeledGraphQuot, labeledSubgraphDensityLifted, Quotient.lift_mk]
    simp only [labeledSubgraphDensity, FlagType.size, Fintype.card_fin, downwardNormalizingFactor_labeledGraph]
    field_simp
    have hG_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) G = ℓ' := by
      simp only [LabeledGraph.size, Fintype.card_fin]
    rw [hG_size, hF_size, ← Nat.cast_mul, ← Nat.cast_mul]
    congr
    · rw [Nat.cast_mul, mul_comm]
      let φG : G ≃f ⟦G⟧.out := by
        apply Classical.choice
        show G ≈ ⟦G⟧.out
        exact Quotient.mk_eq_iff_out.mp rfl
      congr 1 <;> simp only [Rat.natCast_inj]
      · exact isomorphismCount_eq_of_eqv (Nonempty.intro φG)
      · exact labeledSubgraphCount_respect_eqv φG LabeledGraphIso.refl
    · rw [Nat.choose_eq_factorial_div_factorial (by omega), Nat.sub_sub_sub_cancel_right n₀_le_ℓ]
      have h₁ : (ℓ - n₀).factorial * (ℓ' - ℓ).factorial ∣ (ℓ' - n₀).factorial := by
        rw [← Nat.dvd_div_iff_mul_dvd]
        · have : ℓ - n₀ = (ℓ' - n₀) - (ℓ' - ℓ) := by omega
          rw [this, ← Nat.descFactorial_eq_div (by omega)]
          exact Nat.factorial_dvd_descFactorial (ℓ' - n₀) (ℓ' - ℓ)
        · exact Nat.factorial_dvd_factorial (by omega)
      have h₂ : (ℓ' - n₀).factorial ∣ ℓ'.factorial := Nat.factorial_dvd_factorial (by omega)
      rw [← Nat.mul_div_right_comm h₁, Nat.mul_div_cancel' h₂, Nat.mul_comm]

  rw [lhs, rhs]

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
