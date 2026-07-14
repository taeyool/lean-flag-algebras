import «LeanFlagAlgebras».FlagAlgebra.FlagAlgebra
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Cast.Field

/-! # The unlabeling (`downward`) operator on the flag algebra

The central construction here is `downward : FlagAlgebra σ → FlagAlgebra ∅ₜ`
(notation `⟦·⟧₀`), the averaging operator that forgets the `σ`-labelling of a
flag by averaging over all ways to place the labels. It is built from
`unlabel` (drop the type embedding of a single flag) together with the
combinatorial weight `downwardNormalizingFactor`. The bulk of the file proves
the counting identity relating injective label-placements to subgraph counts
(`isoInjectiveMapSet_*`), from which `flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions`
follows; this gives that `downward` is well defined on the zero space and hence
a linear map, together with its algebra-compatibility lemmas (`downward_add`,
`downward_smul`, …) and the fact that it is the identity on the empty type.
-/

namespace FlagAlgebras

open LabeledSubgraph
open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/- Downward operator from σ-type to the empty type -/

/-- The empty flag type: no labelled vertices. Flags of this type are just
(unlabelled) graphs, so `FlagAlgebra ∅ₜ` is where density bounds live.
Notation: `∅ₜ`. -/
def emptyType : FlagType (Fin 0) := SimpleGraph.emptyGraph (Fin 0)

notation "∅ₜ" => emptyType

@[simp]
theorem emptyType_size : ∅ₜ.size = 0 := by
  dsimp only [emptyType, SimpleGraph.emptyGraph_eq_bot, FlagType.size]
  simp only [Fintype.card_eq_zero]

def isoLabeledGraphSetWithSameGraph
    (G : LabeledGraph σ (Fin n)) : Set (LabeledGraph σ (Fin n))
  :=
  { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H }

noncomputable instance (G : LabeledGraph σ (Fin n)) : Fintype (isoLabeledGraphSetWithSameGraph G)
  :=
  Fintype.ofFinite (isoLabeledGraphSetWithSameGraph G)

/-- The number of labelled graphs on the same underlying graph as `G` that are
flag-isomorphic to `G`; i.e. how many distinct label placements realise `G`. -/
noncomputable def isomorphismCount
    (G : LabeledGraph σ (Fin n)) : ℕ
  :=
  (isoLabeledGraphSetWithSameGraph G).toFinset.card

/-- The combinatorial weight of `G` used by the unlabeling operator: the
fraction of label placements (injections of the `n₀` labels into `n` vertices)
that realise `G`, i.e. `isomorphismCount G` over the number of all such
injections. -/
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
              dsimp only [eq_mpr_eq_cast, cast_eq, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, φH]
              funext x
              congr 1
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
  dsimp only [isomorphismCount]
  simp only [Set.toFinset_card, Fintype.card_congr (isoSetOfIsoLabeledGraphWithSameGraph h.some)]

lemma downwardNormalizingFactor_labeledGraph_respect_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : downwardNormalizingFactor_labeledGraph G = downwardNormalizingFactor_labeledGraph G'
  := by
  dsimp only [downwardNormalizingFactor_labeledGraph]
  rw [isomorphismCount_respect_eqv h]

/-- The unlabeling weight, lifted to flags (isomorphism classes); the weight by
which `unlabel F` is scaled when forgetting the labels of the flag `F`. -/
noncomputable def downwardNormalizingFactor
    : Flag σ (Fin n) → ℚ :=
  Quotient.lift (fun G : LabeledGraph σ (Fin n) => downwardNormalizingFactor_labeledGraph G)
    fun _ _ G_eqv => downwardNormalizingFactor_labeledGraph_respect_eqv G_eqv

/-- The unlabeling weight is strictly positive. -/
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

/-- Forget the type embedding of a labelled graph, producing the same
underlying graph as a `∅ₜ`-labelled (unlabelled) graph. -/
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

/-- `unlabel` on flags: forget the `σ`-labelling of a flag, yielding the
underlying graph as a `∅ₜ`-flag. The single-flag core of the `downward`
operator. -/
noncomputable def unlabel {V : Type}
    : Flag σ V → Flag ∅ₜ V :=
  Quotient.lift (fun G : LabeledGraph σ V => unlabeledGraphQuot G)
    fun _ _ G_eqv => unlabeledGraphQuot_respect_eqv G_eqv

theorem unlabel_eq_iff_unlabeledGraph_eqv
    {F : LabeledGraph σ V} {G : LabeledGraph ∅ₜ V}
    : unlabel ⟦F⟧ = ⟦G⟧ ↔ unlabeledGraph F ∼f G
  := by
  constructor <;> intro h
  · simp only [unlabel, unlabeledGraphQuot, Quotient.lift_mk] at h
    exact Quotient.exact h
  · exact Quotient.sound h

/-- The image of a single flag `F` under unlabeling: the unlabelled flag
`unlabel F` scaled by its combinatorial weight `downwardNormalizingFactor F`. -/
noncomputable def downwardFlag (F : Flag σ (Fin n)) : FlagVector ∅ₜ :=
  downwardNormalizingFactor F • basisVector ⟨n, unlabel F⟩

/-- `downwardFlag` extended linearly to flag vectors. -/
noncomputable def downwardFlagVector : FlagVector σ → FlagVector ∅ₜ :=
  linearExtension (fun F : FinFlag σ => downwardFlag F.2)

noncomputable def downwardFlagVectorQuot (f : FlagVector σ) : FlagAlgebra ∅ₜ :=
  ⟦downwardFlagVector f⟧

lemma downwardFlagVector_zero
    : downwardFlagVector (0 : FlagVector σ) = 0
  := by
  simp only [downwardFlagVector, linearExtension_zero]

lemma downwardFlagVector_basisVector
    (F : FinFlag σ)
    : downwardFlagVector (basisVector F) = downwardFlag F.2
  := by
  simp only [downwardFlagVector, linearExtension_basisVector]

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

/-- All `σ`-labelled flags of size `ℓ` whose unlabeling is the given
unlabelled flag `F`; i.e. the ways to add a `σ`-labelling back onto `F`. -/
noncomputable def labelExtensions
    {ℓ : ℕ} (F : FlagWithSize ∅ₜ ℓ) (σ : FlagType (Fin n₀))
    : Finset (FlagWithSize σ ℓ)
  :=
  { G : FlagWithSize σ ℓ | unlabel G = F }

/-- Pairs `(W, θ)` of a vertex subset `W` of `F'` and a label assignment
`θ : Fin n₀ → Fin ℓ'` that embed the labelled flag `F` into the unlabelled flag
`F'` as an induced subgraph. The common bridge object: its cardinality is
counted two ways to relate unlabeling weights to subgraph densities. -/
def isoInjectiveMapSet
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : Set ((Set (Fin ℓ')) × (Fin n₀ → Fin ℓ'))
  :=
  { (W, θ) : (Set (Fin ℓ')) × (Fin n₀ → Fin ℓ') |
    Function.Injective θ ∧ W.toFinset.card = ℓ ∧
    (∀ {a b : Fin n₀}, F'.graph.Adj (θ a) (θ b) ↔ σ.Adj a b) ∧
    (∃ (h_range : Set.range θ ⊆ W) (φ : ((⊤ : F'.graph.Subgraph).induce W).coe ≃g F.graph),
      φ ∘ (fun i ↦ ⟨θ i, h_range (Set.mem_range_self i)⟩) = F.type_embed) }

/-- First count of the bridge set: `|isoInjectiveMapSet F F'|` equals the number
of label placements of `F` times the number of induced copies of the
unlabelled `F` inside `F'`. -/
theorem isoInjectiveMapSet_card_eq_isomorphismCount_mul_labeledGraphCount
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : (isoInjectiveMapSet F F').toFinset.card = isomorphismCount F * labeledGraphCount (unlabeledGraph F) F'
  := by
  let S₁ : Set ((LabeledGraph σ (Fin ℓ)) × LabeledSubgraph ∅ₜ F') :=
    { (G, G') | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧ G'.IsInduced ∧ Nonempty (G'.coe ≃f (unlabeledGraph F))}
  let S₂ : Set ((LabeledGraph σ (Fin ℓ)) × Set (Fin ℓ')) :=
    { (G, W) | G.graph = F.graph ∧ Nonempty (F ≃f G) ∧
       Nonempty (((⊤ : F'.graph.Subgraph).induce W).coe ≃g F.graph) }
  let S₃ : Set (Set (Fin ℓ') × (Fin n₀ → Fin ℓ')) := isoInjectiveMapSet F F'

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
      intro ⟨⟨G, W⟩, hG_graph_eq, hG_iso_F, hF'_ind_iso_G⟩
      let φ := hG_iso_F.some.graph_iso
      let ψ := hF'_ind_iso_G.some
      let θ : Fin n₀ → Fin ℓ' := fun i ↦ ((ψ.symm (G.type_embed i)))
      have hθ_inj : Function.Injective θ := by
        intro a b h_eq
        apply Subtype.ext at h_eq
        simp_all only [EmbeddingLike.apply_eq_iff_eq]
      have hθ_range : Set.range θ ⊆ W := by
        intro y ⟨x, hx_eq⟩
        rw [← hx_eq]
        simp only [θ, Subtype.coe_prop]
      refine ⟨⟨W, θ⟩, hθ_inj, ?_, ?_, ?_⟩
      · have h_card_eq := SimpleGraph.Iso.card_eq ψ
        simp only [Fintype.card_fin, SimpleGraph.Subgraph.induce_verts] at h_card_eq
        rw [← h_card_eq]
        simp only [Set.toFinset_card, Fintype.card_ofFinset]
      · intro a b
        have ha : θ a ∈ W := by simp_all only [SimpleGraph.Subgraph.induce_verts, Subtype.coe_prop, θ]
        have hb : θ b ∈ W := by simp_all only [SimpleGraph.Subgraph.induce_verts, Subtype.coe_prop, θ]
        calc
          _ ↔ ((⊤ : F'.graph.Subgraph).induce W).Adj (θ a) (θ b) := by simp_all only [Subtype.coe_prop, SimpleGraph.Subgraph.induce_top_isInduced, SimpleGraph.Subgraph.IsInduced.adj, θ, ψ]
          _ ↔ F.graph.Adj (ψ ⟨θ a, ha⟩) (ψ ⟨θ b, hb⟩) := Iff.symm ψ.map_rel_iff'
          _ ↔ F.graph.Adj (G.type_embed a) (G.type_embed b) := by simp only [Subtype.coe_eta, RelIso.apply_symm_apply, θ]
          _ ↔ G.graph.Adj (G.type_embed a) (G.type_embed b) := by rw [← hG_graph_eq]
          _ ↔ σ.Adj a b := SimpleGraph.Embedding.map_adj_iff G.type_embed
      · use hθ_range
        let φ' : ((⊤ : F'.graph.Subgraph).induce W).coe ≃g F.graph := {
          toFun := fun x ↦ φ.symm.toFun (ψ.toFun x)
          invFun := fun x ↦ ψ.symm.toFun (φ.toFun x)
          left_inv := by
            intro _
            simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, RelIso.apply_symm_apply,
              RelIso.symm_apply_apply]
          right_inv := by
            intro _
            simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, RelIso.apply_symm_apply,
              RelIso.symm_apply_apply]
          map_rel_iff' := by
            intro a b
            simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Equiv.coe_fn_mk,
              SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.induce_top_isInduced,
              SimpleGraph.Subgraph.IsInduced.adj]
            calc
              _ ↔ G.graph.Adj (ψ a) (ψ b) := SimpleGraph.Iso.map_adj_iff φ.symm
              _ ↔ F.graph.Adj (ψ a) (ψ b) := by rw [hG_graph_eq]
              _ ↔ F'.graph.Adj a b := by
                constructor
                · intro hF_adj
                  exact SimpleGraph.Subgraph.Adj.adj_sub' ((⊤ : F'.graph.Subgraph).induce W) a b ((SimpleGraph.Iso.map_adj_iff ψ).mp hF_adj)
                · intro hF'_adj
                  refine (SimpleGraph.Iso.map_adj_iff ψ).mpr ?_
                  simp_all only [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.induce_top_isInduced,
                    SimpleGraph.Subgraph.IsInduced.adj, θ, ψ] }
        use φ'
        ext t
        rw [← congrFun hG_iso_F.some.symm.type_preserve t]
        simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
          Subtype.coe_eta, Function.comp_apply, RelIso.apply_symm_apply, θ, φ', φ]
        rfl
    have h_f_S₂_S₃_inj : Function.Injective f_S₂_S₃ := by
      intro ⟨⟨G₁, W₁⟩, hG₁_graph_eq, hG₁_iso_F, hF'_ind_iso_G₁⟩ ⟨⟨G₂, W₂⟩, hG₂_graph_eq, hG₂_iso_F, hF'_ind_iso_G₂⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_S₂_S₃] at h_eq
      obtain ⟨hW_eq, hθ_eq⟩ := h_eq
      subst hW_eq
      let ψ₁ := hF'_ind_iso_G₁.some
      let ψ₂ := hF'_ind_iso_G₂.some
      have hψ_eq : ψ₁ = ψ₂ := rfl
      simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
      ext a b
      · rw [hG₁_graph_eq, hG₂_graph_eq]
      · apply heq_of_cast_eq ?_ ?_
        · rw [hG₁_graph_eq, hG₂_graph_eq]
        · ext v
          rw [Fin.val_eq_val]
          calc
            _ = G₁.type_embed v := by
              congr 1
              · rw [hG₁_graph_eq, hG₂_graph_eq]
              · rw [hG₁_graph_eq, hG₂_graph_eq]
              · exact cast_heq _ _
            _ = G₂.type_embed v := by
              have : ψ₁.symm (G₁.type_embed v) = ψ₂.symm (G₂.type_embed v) := by
                have := congrFun hθ_eq v
                dsimp only [ψ₁, ψ₂]
                apply Subtype.ext at this
                exact this
              rw [← hψ_eq] at this
              exact (RelIso.injective ψ₁.symm) this
    have h_f_S₂_S₃_surj : Function.Surjective f_S₂_S₃ := by
      intro ⟨⟨W, θ⟩, hθ_inj, hW_card, hθ_adj_iff, hθ_range, hW_ind_iso, hθ_comp_eq⟩
      have ψ_cand : Nonempty (((⊤ : F'.graph.Subgraph).induce W).coe ≃g F.graph) := Nonempty.intro hW_ind_iso
      let ψ := ψ_cand.some
      let φ := ψ ∘ hW_ind_iso.symm
      let G : LabeledGraph σ (Fin ℓ) := {
        graph := F.graph
        type_embed := {
          toFun := fun i ↦ φ (F.type_embed i)
          inj' := by
            intro a b h_eq
            simp only at h_eq
            rw [← congrFun hθ_comp_eq a, ← congrFun hθ_comp_eq b] at h_eq
            simp only [Function.comp_apply, RelIso.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, φ] at h_eq
            exact hθ_inj h_eq
          map_rel_iff' := by
            intro a b
            have ha : θ a ∈ W := hθ_range (Set.mem_range_self a)
            have hb : θ b ∈ W := hθ_range (Set.mem_range_self b)
            simp only [Function.Embedding.coeFn_mk]
            calc
              _ ↔ F.graph.Adj (φ (hW_ind_iso ⟨θ a, ha⟩)) (φ (hW_ind_iso ⟨θ b, hb⟩)) := by rw [← congrFun hθ_comp_eq a, ← congrFun hθ_comp_eq b]; rfl
              _ ↔  F.graph.Adj (ψ ⟨θ a, ha⟩) (ψ ⟨θ b, hb⟩) := by simp only [Function.comp_apply, RelIso.symm_apply_apply, φ]
              _ ↔ ((⊤ : F'.graph.Subgraph).induce W).Adj (θ a) (θ b) := ψ.map_rel_iff'
              _ ↔ F'.graph.Adj (θ a) (θ b) := by
                constructor
                · exact fun h_adj ↦ SimpleGraph.Subgraph.Adj.adj_sub h_adj
                · exact fun h_adj ↦ (SimpleGraph.Subgraph.induce_top_isInduced F'.graph W) ha hb h_adj
              _ ↔ _ := hθ_adj_iff }
      }
      refine ⟨⟨⟨G, W⟩, ?_⟩, ?_⟩
      · simp only [Set.mem_setOf_eq, true_and, S₂, G]
        constructor
        · apply Nonempty.intro
          exact {
            graph_iso := by
              simp only
              exact {
                toFun := ψ ∘ hW_ind_iso.symm
                invFun := hW_ind_iso ∘ ψ.symm
                left_inv := by
                  intro _
                  simp only [Function.comp_apply, RelIso.symm_apply_apply, RelIso.apply_symm_apply]
                right_inv := by
                  intro _
                  simp only [Function.comp_apply, RelIso.symm_apply_apply, RelIso.apply_symm_apply]
                map_rel_iff' := by
                  intro a b
                  simp only [Equiv.coe_fn_mk, Function.comp_apply]
                  calc
                    _ ↔ ((⊤ : F'.graph.Subgraph).induce W).Adj (hW_ind_iso.symm a) (hW_ind_iso.symm b) := ψ.map_rel_iff'
                    _ ↔ _ := by
                      constructor
                      · exact fun h_adj ↦ (hW_ind_iso.symm.map_adj_iff).mp h_adj
                      · exact fun h_adj ↦ (hW_ind_iso.symm.map_adj_iff).mpr h_adj }
            type_preserve := by
              ext t
              simp only [Function.comp_apply, id_eq, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
                RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, φ] }
        · exact Nonempty.intro hW_ind_iso
      · simp only [f_S₂_S₃]
        split
        rename_i G' W' hG_eq_F hF_iso_G hF'_ind_iso_G h_eq
        simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq] at h_eq
        obtain ⟨hG_eq, hW_eq⟩ := h_eq
        subst hW_eq hG_eq
        simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Subtype.mk.injEq,
          Prod.mk.injEq, true_and, G]
        ext t
        have ht : θ t ∈ ((⊤ : F'.graph.Subgraph).induce W).verts := by
          simp only [SimpleGraph.Subgraph.induce_verts]
          exact hθ_range (Set.mem_range_self t)
        have hθ_comp_eq : hW_ind_iso ⟨θ t, ht⟩ = F.type_embed t := by
          rw [← congrFun hθ_comp_eq t]
          simp only [Function.comp_apply]
        simp only [Function.comp_apply, φ]
        rw [Fin.val_eq_val, ← hθ_comp_eq, RelIso.symm_apply_apply, RelIso.symm_apply_apply]

    Equiv.ofBijective f_S₂_S₃ ⟨h_f_S₂_S₃_inj, h_f_S₂_S₃_surj⟩

  have hS₁_card : S₁.toFinset.card = isomorphismCount F * labeledGraphCount (unlabeledGraph F) F' := by
    dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph, labeledGraphCount]
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

  have h_S₁_iso_S₃ : S₁ ≃ S₃ := by
    calc
      S₁ ≃ S₂ := h_S₁_iso_S₂
      _ ≃ S₃ := h_S₂_iso_S₃
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S₁]
  simp only [Set.coe_setOf, S₁, S₃] at h_S₁_iso_S₃
  exact h_S₁_iso_S₃.symm

/-- Second count of the bridge set: summing, over all labelled graphs on `F'`'s
underlying graph, the number of induced copies of `F`. -/
theorem isoInjectiveMapSet_card_eq_sum_labeledGraphCount_of_same_graph
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : (isoInjectiveMapSet F F').toFinset.card = ∑ G with G.graph = F'.graph, labeledGraphCount F G
  := by
  dsimp only [labeledGraphCount]
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
      · have h_type_eq : (inducedLabeledSubgraph G W hW).coe.graph = ((⊤ : F'.graph.Subgraph).induce W).coe := by
          rw [← hG_graph_eq]
          simp only [inducedLabeledSubgraph, coe_graph]
        let φG_ind_inv : ((⊤ : F'.graph.Subgraph).induce W).coe ≃g F.graph := by
          rw [← h_type_eq]
          exact hG_ind_iso.some.graph_iso
        have h_φG_ind_inv_comp : φG_ind_inv ∘ φG_ind = id := by
          ext v
          simp only [coe_graph, eq_mpr_eq_cast, φG_ind_inv, φG_ind, Function.comp_apply, id_eq, Fin.val_eq_val]
          calc
            _ = hG_ind_iso.some.graph_iso (hG_ind_iso.some.symm.graph_iso v) := by
              have : ((⊤ : F'.graph.Subgraph).induce W).coe = (inducedLabeledSubgraph G W hW).coe.graph := by
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
              congr 1
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

/-- The bridge-set count grouped by label-extension flag: summing over the
re-labellings of `F'`, weight by label-placement count times induced-copy
count of `F`. The form used to compare unlabeling weights and densities. -/
theorem isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledGraphCount
    {ℓ ℓ' : ℕ} (F : LabeledGraph σ (Fin ℓ)) (F' : LabeledGraph ∅ₜ (Fin ℓ'))
    : (isoInjectiveMapSet F F').toFinset.card = ∑ G ∈ labelExtensions ⟦F'⟧ σ, isomorphismCount G.out * labeledGraphCount F G.out
  := by
  let S_F' : Finset (LabeledGraph σ (Fin ℓ')) := {G | G.graph = F'.graph}.toFinset
  rw [isoInjectiveMapSet_card_eq_sum_labeledGraphCount_of_same_graph F F']
  symm
  calc
    _ = ∑ G ∈ labelExtensions ⟦F'⟧ σ, {H ∈ S_F' | ⟦H⟧ = G}.card * labeledGraphCount F G.out := by
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
          graph_iso := by
            dsimp only [G']
            exact hGF'.some.graph_iso
          type_preserve := by
            simp only [id_eq, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, G']
        }
      calc
        _ = {H | G'.graph = H.graph ∧ G' ∼f H}.toFinset.card := by
          have := isomorphismCount_respect_eqv hGG'_iso
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
    _ = ∑ G ∈ labelExtensions ⟦F'⟧ σ, ∑ G' ∈ S_F' with ⟦G'⟧ = G, labeledGraphCount F (⟦G'⟧ : FlagWithSize σ ℓ').out := by
      apply Finset.sum_congr rfl
      intro G _
      rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      apply Finset.sum_congr rfl
      intro G' hG'
      simp only [Finset.mem_filter] at hG'
      rw [hG'.2]
    _ = ∑ G ∈ S_F', labeledGraphCount F (⟦G⟧ : FlagWithSize σ ℓ').out := by
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
      have := @Finset.sum_fiberwise_of_maps_to _ _ _ _ _ _ _ (fun G ↦ ⟦G⟧) h_quot_labelExt (fun G ↦ labeledGraphCount F (⟦G⟧ : FlagWithSize σ ℓ').out)
      rw [← this]
      congr!
    _ = ∑ G ∈ S_F', labeledGraphCount F G := by
      apply Finset.sum_congr rfl
      intro G _
      apply labeledGraphCount_respect_eqv
      · apply Classical.choice
        show ⟦G⟧.out ≈ G
        exact Quotient.eq_mk_iff_out.mp rfl
      · exact LabeledGraphIso.refl
    _ = ∑ G with G.graph = F'.graph, labeledGraphCount F G := by
      simp only [Set.toFinset_setOf, S_F']

/-- Key identity for `downward`'s well-definedness: the density of `unlabel F`
in `F'` times `F`'s unlabeling weight equals the sum over all relabellings `G`
of `F'` of the density of `F` in `G` times `G`'s weight. -/
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
    dsimp only [subflagDensity, unlabel, unlabeledGraphQuot, labeledGraphDensityLifted, Quotient.lift_mk]

  have lhs : labeledGraphDensity Fu F' * downwardNormalizingFactor_labeledGraph F = A.card / ω := by
    dsimp only [labeledGraphDensity, downwardNormalizingFactor_labeledGraph]
    rw [div_mul_div_comm]
    congr
    · rw [← Nat.cast_mul, Nat.cast_inj, mul_comm]
      rw [isoInjectiveMapSet_card_eq_isomorphismCount_mul_labeledGraphCount F F']
    · simp only [emptyType_size, tsub_zero, ← Nat.cast_mul, Nat.cast_inj]
      rw [hF'_size, hFu_size, Nat.choose_eq_factorial_div_factorial hℓ]
      have : ℓ.factorial ∣ ℓ'.factorial / (ℓ' - ℓ).factorial := by
        rw [← Nat.descFactorial_eq_div hℓ]
        exact Nat.factorial_dvd_descFactorial ℓ' ℓ
      rw [mul_comm ℓ.factorial, ← Nat.div_div_eq_div_mul, ← Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.sub_le ℓ n₀)), Nat.div_mul_cancel this, Nat.div_div_eq_div_mul]

  have rhs : ∑ G ∈ labelExtensions ⟦F'⟧ σ, flagDensity₁ ⟦F⟧ G * downwardNormalizingFactor G = A.card / ω := by
    rw [isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledGraphCount F F']
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro G hG
    rcases Quotient.exists_rep G with ⟨G, rfl⟩
    simp only [labelExtensions, unlabel, unlabeledGraphQuot, Finset.mem_filter, Finset.mem_univ,
      Quotient.lift_mk, true_and] at hG
    dsimp only [flagDensity₁, downwardNormalizingFactor]
    rw [← subflagDensity_eq_flagListDensity]
    dsimp only [subflagDensity, unlabel, unlabeledGraphQuot, labeledGraphDensityLifted, Quotient.lift_mk]
    simp only [labeledGraphDensity, FlagType.size, Fintype.card_fin, downwardNormalizingFactor_labeledGraph]
    field_simp
    have hG_size : @LabeledGraph.size _ _ _ _ (fun a b ↦ propDecidable (a = b)) G = ℓ' := by
      simp only [LabeledGraph.size, Fintype.card_fin]
    rw [hG_size, hF_size, ← Nat.cast_mul, ← Nat.cast_mul]
    congr 1
    · rw [mul_comm]
      let φG : G ≃f ⟦G⟧.out := by
        apply Classical.choice
        show G ≈ ⟦G⟧.out
        exact Quotient.mk_eq_iff_out.mp rfl
      congr 2
      · exact isomorphismCount_respect_eqv (Nonempty.intro φG)
      · exact labeledGraphCount_respect_eqv φG LabeledGraphIso.refl
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
    _ = (downwardNormalizingFactor F.2) • basisVector ⟨F.1, unlabel F.2⟩ := rfl
    _ ∼v (downwardNormalizingFactor F.2) • flagExpansion ⟨F.1, unlabel F.2⟩ ℓ := by
      apply flagVectorEqv_smul
      exact basisVector_eqv_flagExpansion _ ℓ hℓ
    _ ∼v (downwardNormalizingFactor F.2) • (∑ G : FlagWithSize ∅ₜ ℓ, flagDensity₁ (unlabel F.2) G • basisVector ⟨ℓ, G⟩) := by
      apply flagVectorEqv_smul
      rfl
    _ ∼v ∑ G : FlagWithSize ∅ₜ ℓ, ∑ G' ∈ labelExtensions G σ,
          flagDensity₁ F.2 G' • downwardNormalizingFactor G' • basisVector ⟨ℓ, G⟩ := by
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
          flagDensity₁ F.2 G' • downwardNormalizingFactor G' • basisVector ⟨ℓ, unlabel G'⟩ := by
      apply flagVectorEqv_sum
      intro G _
      apply flagVectorEqv_sum
      intro G' hG'
      iterate 2 (apply flagVectorEqv_smul)
      dsimp only [labelExtensions] at hG'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG'
      rw [hG']
    _ ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardNormalizingFactor G • basisVector ⟨ℓ, unlabel G⟩ := by
      rw [Finset.sum_fiberwise _ (fun G => unlabel G)]
    _ ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardFlag G := by
      apply flagVectorEqv_sum
      intro G _
      rfl

lemma downwardFlagVector_zeroElement_zeroSpace
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : downwardFlagVector (zeroElement F ℓ) ∈ ZeroSpace ∅ₜ
  := by
  dsimp only [downwardFlagVector]
  let S : Finset (FinFlag σ) := (Finset.univ : Finset (FlagWithSize σ ℓ)).map {
    toFun := fun F' => ⟨ℓ, F'⟩
    inj' := fun F₁' F₂' h => by injection h
  }
  have h_supp : (zeroElement F ℓ).support ⊆ S ∪ {F} := by
    dsimp only [zeroElement]
    calc
      _ ⊆ (basisVector F).support ∪ (flagExpansion F ℓ).support := Finsupp.support_sub
      _ ⊆ S ∪ {F} := by
        rw [Finset.union_comm]
        apply Finset.union_subset_union
        · dsimp only [flagExpansion, rat_smul_eq_real_smul]
          apply Finset.Subset.trans Finsupp.support_finset_sum
          apply Finset.biUnion_subset.mpr
          intro G _
          apply Finset.Subset.trans Finsupp.support_smul
          simp only [basisVector_support, Finset.singleton_subset_iff, Finset.mem_map,
            Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, exists_apply_eq_apply, S]
        · simp only [basisVector_support, subset_refl]
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
    simp only [zeroElement, flagExpansion]
    rw [Finsupp.sub_apply, Finset.sum_apply', basisVector_apply_other F G h_G_neq_F.symm]
    simp only [zero_sub, neg_inj]
    have h_Gℓ : G.1 = ℓ := by
      simp_all only [Finset.mem_map, Finset.mem_univ, true_and, S]
      obtain ⟨w, h⟩ := hG
      subst h
      simp only [Function.Embedding.coeFn_mk]
    subst h_Gℓ
    rw [Finset.sum_eq_single_of_mem G.2]
    · simp only [Sigma.eta, rat_smul_eq_real_smul, Finsupp.coe_smul, Pi.smul_apply,
        basisVector_apply_self, smul_eq_mul, mul_one]
    · simp only [Finset.mem_univ]
    · intro G' _ hG'
      rw [Finsupp.smul_apply, basisVector_apply_other, smul_zero]
      contrapose! hG'
      simp only [ne_eq] at *
      rw [Sigma.ext_iff] at hG'
      simp only [heq_eq_eq, true_and] at hG'
      exact hG'
  have h₂ : (zeroElement F ℓ) F = if F ∈ S then 0 else 1 := by
    dsimp only [zeroElement, flagExpansion, rat_smul_eq_real_smul, Finsupp.coe_sub, Pi.sub_apply]
    simp only [basisVector_apply_self]
    rw [Finset.sum_apply']
    split
    next h =>
      rw [hF_iff] at h
      subst h
      rw [Finset.sum_eq_single_of_mem F.2]
      · simp only [flagDensity_self, Rat.cast_one, Sigma.eta, one_smul, basisVector_apply_self, sub_self]
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
      apply basisVector_apply_other_size
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

/-- `downwardFlagVector` maps the zero space into the zero space; this is what
makes `downward` well defined on the quotient flag algebra. -/
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

/-- The unlabeling / averaging operator `FlagAlgebra σ → FlagAlgebra ∅ₜ`:
forget the labels of every flag, averaging by the unlabeling weights. The main
construction of this file; notation `⟦f⟧₀`. -/
noncomputable def downward
    : FlagAlgebra σ → FlagAlgebra ∅ₜ :=
  Quotient.lift (fun g : FlagVector σ => downwardFlagVectorQuot g)
    fun _ _ f_eqv => downwardFlagVectorQuot_respect_eqv f_eqv

notation "⟦" f "⟧₀" => (downward f)

theorem downward_zero
    : ⟦(0 : FlagAlgebra σ)⟧₀ = 0
  := by
  exact downwardFlagVectorQuot_zero

/-- `downward` is additive. -/
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

/-- `downward` commutes with scalar multiplication; together with
`downward_add` this makes it ℝ-linear. -/
theorem downward_smul
    (f : FlagAlgebra σ) (r : ℝ)
    : ⟦r • f⟧₀ = r • ⟦f⟧₀
  := by
  rw [← Quotient.out_eq f, ← smul_quot]
  apply downwardFlagVectorQuot_smul

theorem downward_nsmul
    (f : FlagAlgebra σ) (n : ℕ)
    : ⟦n • f⟧₀ = n • ⟦f⟧₀
  := by
  simp only [← Nat.cast_smul_eq_nsmul ℝ]
  exact downward_smul f n

theorem unlabel_emptyType
    {V : Type} (F : Flag ∅ₜ V)
    : unlabel F = F
  := by
  rcases Quot.exists_rep F with ⟨F, rfl⟩
  apply Quotient.sound
  simp [unlabeledGraph]
  exact Nonempty.intro {
    graph_iso := SimpleGraph.Iso.refl
    type_preserve := List.ofFn_inj.mp rfl
  }

theorem isomorphismCount_emptyType
    (G : LabeledGraph ∅ₜ (Fin n₀))
    : isomorphismCount G = 1
  := by
  simp [isomorphismCount]
  refine Fintype.card_eq_one_iff.mpr ?_
  refine ⟨⟨G, by exact ⟨rfl, ⟨LabeledGraphIso.refl⟩⟩⟩, ?_⟩
  rintro ⟨H, hH⟩
  rcases hH with ⟨hGraph, hIso⟩
  congr
  rcases G with ⟨Ggraph, Gembed⟩
  rcases H with ⟨Hgraph, Hembed⟩
  subst hGraph
  simp
  ext t
  exact Fin.elim0 t

theorem downwardNormalizingFactor_emptyType
    (F : FlagWithSize ∅ₜ n₀)
    : downwardNormalizingFactor F = 1
  := by
  rcases Quot.exists_rep F with ⟨F, rfl⟩
  show downwardNormalizingFactor_labeledGraph F = 1
  simp [downwardNormalizingFactor_labeledGraph]
  rw [div_self (by simp [Nat.cast_eq_zero, Nat.factorial_ne_zero]), div_one, Rat.natCast_eq_one_iff]
  exact isomorphismCount_emptyType F

/-- On the empty type there is nothing to unlabel: `downward` is the identity
on `FlagAlgebra ∅ₜ`. -/
theorem downward_emptyType
    (f : FlagAlgebra ∅ₜ) : ⟦f⟧₀ = f
  := by
  rcases Quot.exists_rep f with ⟨f, rfl⟩
  apply Quotient.sound
  rw [flagVector_eq_sum_basisVector f]
  simp [downwardFlagVector_sum, downwardFlagVector_smul, downwardFlagVector_basisVector]
  apply flagVector_eq_eqv
  congr!
  simp [downwardFlag, unlabel_emptyType, downwardNormalizingFactor_emptyType]

end FlagAlgebras
