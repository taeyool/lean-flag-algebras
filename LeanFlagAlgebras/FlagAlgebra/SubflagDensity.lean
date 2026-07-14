import «LeanFlagAlgebras».FlagAlgebra.FlagDef
import Mathlib.Algebra.Order.Field.Rat

/-! # Subflag Density

This file defines the density of a single subflag inside another flag, the
typed analogue of subgraph density used to build the flag algebra `A^σ`.
`labeledGraphCount`/`labeledGraphDensity` count and normalize the
type-preserving induced copies of `H` inside a labeled graph `G`; these are
shown invariant under labeled-graph isomorphism and then lifted through the
`Flag` quotient to `subflagDensity : Flag σ V → Flag σ W → ℚ`. Boundary facts
(`subflagDensity_empty`, `subflagDensity_self`, `subflagDensity_other`) pin
down its values on the empty flag, on itself, and on non-isomorphic flags.
Builds on `FlagAlgebra.FlagDef`; consumed by the list-density development. -/

namespace FlagAlgebras

open LabeledSubgraph
open Classical

variable {T : Type} [Fintype T]
variable {σ : FlagType T}
variable {U : Type} [Fintype U]
variable {V : Type} [Fintype V]
variable {W : Type} [Fintype W]
variable {Z : Type} [Fintype Z]

/-- Number of induced labeled subgraphs of `G` that are isomorphic (as
labeled graphs) to `H`; the unnormalized subflag count. -/
noncomputable def labeledGraphCount
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℕ
  :=
  let p (G' : LabeledSubgraph σ G) : Prop := G'.IsInduced ∧ Nonempty (G'.coe ≃f H)
  let S := { G' : LabeledSubgraph σ G | p G' }
  S.toFinset.card

/-- Density of `H` in `G`: `labeledGraphCount` divided by the number of
ways to choose the non-type vertices of an `H`-sized induced subgraph. -/
noncomputable def labeledGraphDensity
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℚ
  :=
  let labeledSubgraph_cnt := labeledGraphCount H G
  let num_of_all_induced_subgraph := (G.size - σ.size).choose (H.size - σ.size)
  labeledSubgraph_cnt / num_of_all_induced_subgraph

/-- `H₀` and `H₁` correspond under the labeled-graph isomorphism `φ`
(same vertex set and adjacency, transported by `φ`). -/
def relOfLabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁) : Prop
  :=
  relOfSubgraph φ.graph_iso H₀.subgraph H₁.subgraph

omit [Fintype T] [Fintype V] [Fintype W] in
lemma relOfLabeledSubgraph_symm
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} {φ : G₀ ≃f G₁}
    {H₀ : LabeledSubgraph σ G₀} {H₁ : LabeledSubgraph σ G₁}
    (h_rel : relOfLabeledSubgraph φ H₀ H₁)
    : (relOfLabeledSubgraph φ.symm H₁ H₀)
  := by
  let ⟨h_vert, h_adj⟩ := h_rel
  have h_vert' : H₀.subgraph.verts = φ.graph_iso.symm '' H₁.subgraph.verts := by
    rw [h_vert]
    ext1 u
    simp only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
  have h_adj' : ∀ (u v : W),
                  H₀.subgraph.Adj (φ.graph_iso.symm u) (φ.graph_iso.symm v) ↔ H₁.subgraph.Adj u v
    := by
    intro u v
    have h_uv := h_adj (φ.graph_iso.symm u) (φ.graph_iso.symm v)
    rw [←h_uv]
    simp only [RelIso.apply_symm_apply]
  exact ⟨h_vert', h_adj'⟩

/-- `p₀` and `p₁` agree on every pair of subgraphs related by `φ`; the
hypothesis needed to transport counts across an isomorphism. -/
def relOfPredOnLabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
  :=
  ∀ (H₀: LabeledSubgraph σ G₀) (H₁: LabeledSubgraph σ G₁),
    (relOfLabeledSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

/-- Predicate on subgraphs of `G`: "this subgraph is labeled-isomorphic to
`H`". The defining property counted by `labeledGraphCount`. -/
def predIsoLabeledH
    (H : LabeledGraph σ U) (G : LabeledGraph σ W)
    : LabeledSubgraph σ G → Prop
  := fun G' ↦ Nonempty (G'.coe ≃f H)

omit [Fintype T] [Fintype U] [Fintype V] [Fintype W] [Fintype Z] in
lemma predIsoLabeledH_related_support
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    (G₀' : LabeledSubgraph σ G₀) (G₁' : LabeledSubgraph σ G₁)
    (h_rel : relOfLabeledSubgraph φ G₀' G₁')
    : predIsoLabeledH H₀ G₀ G₀' → predIsoLabeledH H₁ G₁ G₁'
  := by
  intro h
  let ⟨h_vert, h_adj⟩ := h_rel
  let f_ζ : G₀'.subgraph.verts → G₁'.subgraph.verts := by
    intro v
    use φ.graph_iso v
    rw [h_vert]
    simp only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, Subtype.coe_prop]
  have h_ζ_bij : Function.Bijective f_ζ := by
    constructor
    · intro v₀ v₁ h_eq
      simp only [f_ζ, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
      exact SetCoe.ext h_eq
    · intro w
      use ⟨(φ.graph_iso.symm w), by
        obtain ⟨_, h⟩ := w; obtain ⟨_, h', rfl⟩ := h_vert ▸ h
        simp only [h', RelIso.symm_apply_apply]⟩
      dsimp only [f_ζ]
      simp only [RelIso.apply_symm_apply, Subtype.coe_eta]
  let ζ := Equiv.ofBijective f_ζ h_ζ_bij
  have h_ζ_adj : ∀ {v₀ v₁ : ↑G₀'.subgraph.verts}, G₁'.coe.graph.Adj (ζ v₀) (ζ v₁) ↔ G₀'.coe.graph.Adj v₀ v₁
    := by
    intro v₀ v₁
    exact h_adj v₀ v₁
  have h_emb : ∀ t : T, ζ (G₀'.type_embed t) = G₁'.type_embed t := by
    intro t
    have h_type_preserve := congr_fun φ.type_preserve t
    rw [Function.comp_apply, ← (G₀'.embed_eq t), ← (G₁'.embed_eq t)] at h_type_preserve
    exact SetCoe.ext h_type_preserve
  let iso_G₀'_G₁' : G₀'.coe ≃f G₁'.coe := ⟨⟨ζ, h_ζ_adj⟩, funext h_emb⟩
  let iso_G₀'_H₀ : G₀'.coe ≃f H₀ := Classical.choice h
  exact Nonempty.intro ((iso_G₀'_G₁'.symm.trans iso_G₀'_H₀).trans ψ)

omit [Fintype T] [Fintype V] [Fintype W] [Fintype U] [Fintype Z] in
lemma predIsoLabeledH_related
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : relOfPredOnLabeledSubgraph φ (predIsoLabeledH H₀ G₀) (predIsoLabeledH H₁ G₁)
  := by
  rintro G₀' G₁' h_rel
  constructor
  . exact predIsoLabeledH_related_support φ ψ G₀' G₁' h_rel
  . exact predIsoLabeledH_related_support φ.symm ψ.symm G₁' G₀' (relOfLabeledSubgraph_symm h_rel)

omit [Fintype T] [Fintype U] [Fintype V] in
lemma predIsoLabeledH_related_ind
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁)
    (h_rel : relOfLabeledSubgraph φ H₀ H₁)
    (h_ind₀ : H₀.IsInduced)
    : H₁.IsInduced
  := by
  intro u h_u v h_v h_uv
  let ⟨h_vert, h_adj⟩ := h_rel
  rw [h_vert] at h_u h_v
  obtain ⟨u', h_u', rfl⟩ := h_u
  obtain ⟨v', h_v', rfl⟩ := h_v
  have h_u'_v' : G₀.graph.Adj u' v' := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_uv
  exact (h_adj u' v').mpr (h_ind₀ h_u' h_v' h_u'_v')

/-- The image of a subgraph `H₀` of `G₀` under the isomorphism `φ`, taken as
an induced subgraph of `G₁`; transports subgraphs across `φ`. -/
def inducedLabeledSubgraphByIso
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : LabeledSubgraph σ G₁
  :=
  inducedLabeledSubgraph
    G₁ (φ.graph_iso '' H₀.subgraph.verts) (labeledGraphIso_preserve_type_verts φ H₀)

omit [Fintype T] [Fintype V] [Fintype W] in
lemma inducedLabeledSubgraphByIso_isInduced
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : (inducedLabeledSubgraphByIso φ H₀).IsInduced
  :=
  inducedLabeledSubgraph_isInduced
    G₁
    (φ.graph_iso '' H₀.subgraph.verts)
    (labeledGraphIso_preserve_type_verts φ H₀)

omit [Fintype T] [Fintype V] [Fintype W] in
lemma inducedLabeledSubgraph_related
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.IsInduced)
    : relOfLabeledSubgraph φ H₀ (inducedLabeledSubgraphByIso φ H₀)
  :=
  induce_top_related φ.graph_iso H₀.subgraph h_ind₀

omit [Fintype T] [Fintype V] in
theorem embed_heq_of_subgraph_eq
    {σ : FlagType T} {G : SimpleGraph V}
    {H H' : G.Subgraph} {H_emb : σ ↪g H.coe} {H'_emb : σ ↪g H'.coe}
    (h : H = H') (h_fun_eq : ∀ t : T, (H_emb t : V) = (H'_emb t : V))
    : HEq H_emb H'_emb
  := by
  subst h
  apply heq_of_eq
  ext t
  exact h_fun_eq t

omit [Fintype T] [Fintype V] in
theorem type_embed_heq_of_subgraph_eq
    {σ : FlagType T} {G : LabeledGraph σ V} {H H' : LabeledSubgraph σ G}
    (H_eq_H' : H.subgraph = H'.subgraph)
    : HEq H.type_embed H'.type_embed
  := by
  have h_embed_eq : ∀ t : T, (H.type_embed t : V) = (H'.type_embed t : V) := by
    intro t
    rw [H.embed_eq t, H'.embed_eq t]
  exact embed_heq_of_subgraph_eq H_eq_H' h_embed_eq

omit [Fintype T] [Fintype U] in
/-- Two labeled subgraphs are equal once their underlying subgraphs agree
(the type embedding is then forced). A frequently used extensionality. -/
lemma labeledSubgraph_eq_from_subgraph_eq
    {σ : FlagType T} {G : LabeledGraph σ U} {H₀ H₁ : LabeledSubgraph σ G}
    (h_subgraph_eq : H₀.subgraph = H₁.subgraph) : H₀ = H₁
  :=
  LabeledSubgraph.ext h_subgraph_eq (type_embed_heq_of_subgraph_eq h_subgraph_eq)

omit [Fintype T] [Fintype V] [Fintype W] in
lemma H_eq_reverseinduced_induced_H
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.IsInduced)
    : H₀ = (inducedLabeledSubgraphByIso φ.symm (inducedLabeledSubgraphByIso φ H₀))
  := by
  let H₀' := inducedLabeledSubgraphByIso φ.symm (inducedLabeledSubgraphByIso φ H₀)
  have h : H₀.subgraph.verts = ⇑φ.symm.graph_iso '' (⇑φ.graph_iso '' H₀.subgraph.verts) := by
    rw [Set.LeftInvOn.image_image]
    intro v _
    exact φ.graph_iso.left_inv v
  have h_eq : H₀.subgraph = H₀'.subgraph := by
    dsimp only [H₀', inducedLabeledSubgraphByIso, inducedLabeledSubgraph]
    simp only [SimpleGraph.Subgraph.induce_verts, ←h]
    exact (h_ind₀.induce_top_verts).symm
  exact labeledSubgraph_eq_from_subgraph_eq h_eq

/-- The bijection between induced subgraphs of `G₀` satisfying `p₀` and those
of `G₁` satisfying `p₁`, given that `φ` relates `p₀` to `p₁`; the core of the
isomorphism-invariance of subgraph counts. -/
def isoSetOfInducedLabeledSubgraph
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
    (h_rel : relOfPredOnLabeledSubgraph φ p₀ p₁)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
      ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  :=
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  let f : S₀ → S₁ := by
    intro ⟨H₀, h_ind₀, h_p₀⟩
    let H₁ := inducedLabeledSubgraphByIso φ H₀
    let h_ind₁ : H₁.IsInduced := inducedLabeledSubgraphByIso_isInduced φ H₀
    have : relOfLabeledSubgraph φ H₀ H₁ := inducedLabeledSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv : S₁ → S₀ := by
    intro ⟨H₁, h_ind₁, h_p₁⟩
    let H₀ := inducedLabeledSubgraphByIso φ.symm H₁
    let h_ind₀ : H₀.IsInduced := inducedLabeledSubgraphByIso_isInduced φ.symm H₁
    have : relOfLabeledSubgraph φ.symm H₁ H₀ := inducedLabeledSubgraph_related φ.symm H₁ h_ind₁
    have : relOfLabeledSubgraph φ H₀ H₁ := relOfLabeledSubgraph_symm this
    have h_p₀ : p₀ H₀ := (h_rel H₀ H₁ this).mpr h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f := by
    constructor <;> rintro ⟨H, h_ind, h_p⟩ <;> simp only [f, f_inv, Subtype.mk.injEq] <;> symm
    · exact H_eq_reverseinduced_induced_H φ H h_ind
    · exact H_eq_reverseinduced_induced_H φ.symm H h_ind
  ⟨f, f_inv, f_bij.1, f_bij.2⟩

def isoSetOfInducedLabeledSubgraphFromIsoGH
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ predIsoLabeledH H₀ G₀ G' }
      ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ predIsoLabeledH H₁ G₁ G' }
  :=
  isoSetOfInducedLabeledSubgraph φ
    (predIsoLabeledH H₀ G₀)
    (predIsoLabeledH H₁ G₁)
    (predIsoLabeledH_related φ ψ)

omit [Fintype W] [Fintype Z] in
lemma labeledGraphCount_respect_eqv
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : labeledGraphCount H₀ G₀ = labeledGraphCount H₁ G₁
  := by
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₀) }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₁) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedLabeledSubgraphFromIsoGH φ ψ
  show S₀.toFinset.card = S₁.toFinset.card
  have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp_all only [Set.toFinset_card]

/-- Subgraph density is invariant under labeled-graph isomorphism in both
arguments; the well-definedness fact enabling the `Flag`-quotient lift. -/
lemma labeledGraphDensity_respect_eqv
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : labeledGraphDensity H₀ G₀ = labeledGraphDensity H₁ G₁
  := by
  dsimp only [labeledGraphDensity]
  have h_count : labeledGraphCount H₀ G₀ = labeledGraphCount H₁ G₁ := labeledGraphCount_respect_eqv φ ψ
  have h_H_size : H₀.size = H₁.size := labeledGraphIso_size_eq H₀ H₁ ψ
  have h_G_size : G₀.size = G₁.size := labeledGraphIso_size_eq G₀ G₁ φ
  rw [h_count, h_H_size, h_G_size]

/-- `labeledGraphDensity H` lifted through the `Flag` quotient in its
second (host) argument. -/
noncomputable def labeledGraphDensityLifted
    (H : LabeledGraph σ V) : Flag σ W → ℚ :=
  Quotient.lift (fun G : LabeledGraph σ W ↦ labeledGraphDensity H G)
    fun _ _ G_eqv => labeledGraphDensity_respect_eqv (Classical.choice G_eqv) LabeledGraphIso.refl

lemma labeledGraphDensityLifted_respect_eqv
    {H₀ : LabeledGraph σ U} {H₁ : LabeledGraph σ V} (ψ : H₀ ≃f H₁) (G : Flag σ W)
    : labeledGraphDensityLifted H₀ G = labeledGraphDensityLifted H₁ G
  := by
  dsimp only [labeledGraphDensityLifted]
  congr
  ext
  exact labeledGraphDensity_respect_eqv LabeledGraphIso.refl ψ

/-- The density of one flag inside another: `labeledGraphDensity` fully
lifted to the `Flag` quotient in both arguments. This is the headline
definition of the file. -/
noncomputable def subflagDensity
    : Flag σ V → Flag σ W → ℚ :=
  Quotient.lift labeledGraphDensityLifted
    fun H H' h_eqv => funext fun G => labeledGraphDensityLifted_respect_eqv (Classical.choice h_eqv) G

omit [Fintype T] [Fintype U] in
lemma bot_labeledSubgraph_iso_emptyLabeledGraph
    (G : LabeledGraph σ U) : Nonempty (G.bottom.coe ≃f emptyLabeledGraph σ)
  :=
  let f : G.bottom.subgraph.verts ≃ T := G.iso_type_G.symm
  have h_adj : ∀ {u v : G.bottom.subgraph.verts},
                 (emptyLabeledGraph σ).graph.Adj (f u) (f v) ↔ G.bottom.subgraph.coe.Adj u v
    := by
    intro u v
    dsimp only [LabeledGraph.bottom, emptyLabeledGraph, SimpleGraph.Subgraph.coe_adj]
    rw [iso_type_Adj_iff G u v]
    simp only [Subtype.coe_prop, true_and]
  let f_iso : (G.bottom).subgraph.coe ≃g (emptyLabeledGraph σ).graph := ⟨f, h_adj⟩
  have h_emb : ∀ t : T, f_iso (G.bottom.coe.type_embed t) = (emptyLabeledGraph σ).type_embed t :=
    fun _ ↦ G.iso_type_G.symm_apply_eq.mpr rfl
  ⟨f_iso, funext h_emb⟩

omit [Fintype T] [Fintype U] in
lemma labeledSubgraph_eq_bot_iff_iso_emptyLabeledGraph
    {G : LabeledGraph σ U} {H : LabeledSubgraph σ G}
    : H = G.bottom ↔ Nonempty (H.coe ≃f (emptyLabeledGraph σ))
  := by
  refine ⟨fun h_eq ↦ h_eq ▸ bot_labeledSubgraph_iso_emptyLabeledGraph G, ?_⟩
  rintro ⟨⟨iso_H_T, h_iso_adj⟩, h_type_embed⟩
  apply labeledSubgraph_eq_from_subgraph_eq
  have h_type_embed_comp_iso_H_T : ∀ u : H.subgraph.verts, H.type_embed (iso_H_T u) = u.val := by
    intro u
    have h₀ : iso_H_T (H.type_embed (iso_H_T u)) = iso_H_T u := congrFun h_type_embed (iso_H_T u)
    exact congr_arg Subtype.val (iso_H_T.injective h₀)
  dsimp [LabeledGraph.bottom]
  have H_verts_iff_type_verts : ∀ u : U, u ∈ H.subgraph.verts ↔ u ∈ G.type_verts := by
    intro u
    constructor
    · intro h_u
      let u' : H.subgraph.verts := ⟨u, h_u⟩
      have h₀ : H.type_embed (iso_H_T u') = u := h_type_embed_comp_iso_H_T u'
      rw [←h₀, H.embed_eq]
      exact G.type_verts_contain (iso_H_T u')
    · apply labeledSubgraph_contain_type_verts
  ext u v <;> try exact H_verts_iff_type_verts u
  simp only [←H_verts_iff_type_verts]
  constructor
  · intro h_uv
    have h_u : u ∈ H.subgraph.verts := H.subgraph.edge_vert h_uv
    have h_v : v ∈ H.subgraph.verts := H.subgraph.edge_vert h_uv.symm
    exact ⟨h_u, h_v, h_uv.adj_sub⟩
  · rintro ⟨h_u, h_v, h_uv_G⟩
    let u' : H.subgraph.verts := ⟨u, h_u⟩
    let v' : H.subgraph.verts := ⟨v, h_v⟩
    have h₀ : (emptyLabeledGraph σ).graph.Adj (iso_H_T u') (iso_H_T v') ↔ H.subgraph.Adj u' v' :=
      h_iso_adj
    rw [←h₀]
    simp only [emptyLabeledGraph, type_embed_Adj_iff G (iso_H_T u') (iso_H_T v'), ← H.embed_eq,
      h_type_embed_comp_iso_H_T]
    exact h_uv_G


lemma labeledGraphCount_empty
    {σ : FlagType T} (G : LabeledGraph σ U)
    : labeledGraphCount (emptyLabeledGraph σ) G = ((G.size - σ.size).choose ((emptyLabeledGraph σ).size - σ.size))
  := by
  dsimp [LabeledGraph.size]
  have h_σ_size : Fintype.card T = σ.size := by rfl
  rw [h_σ_size]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f (emptyLabeledGraph σ)) }
  let S₁ := { G' : LabeledSubgraph σ G | G' = G.bottom }
  simp only [labeledGraphCount, le_refl,tsub_eq_zero_of_le, Nat.choose_zero_right]
  show S₀.toFinset.card = 1
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    simp only [Set.mem_setOf_eq, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff, S₀, S₁]
    rw [←labeledSubgraph_eq_bot_iff_iso_emptyLabeledGraph]
    refine ⟨And.right, ?_⟩
    rintro rfl; exact ⟨LabeledGraph.bottom_isInduced G, rfl⟩
  simp only [h_S₀_S₁, Set.setOf_eq_eq_singleton, Set.toFinset_singleton, Finset.card_singleton, S₁]

lemma labeledGraphDensity_empty
    {σ : FlagType T} (G : LabeledGraph σ U)
    : labeledGraphDensity (emptyLabeledGraph σ) G = 1
  := by
  simp only [labeledGraphDensity, labeledGraphCount_empty G]
  refine (div_eq_one_iff_eq ?_).mpr rfl
  dsimp only [LabeledGraph.size]
  have : Fintype.card T = σ.size := by rfl
  simp only [this, le_rfl, tsub_eq_zero_of_le, Nat.choose_zero_right]
  simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true]

/-- The empty flag has density `1` in every flag (it always occurs). -/
lemma subflagDensity_empty
    {σ : FlagType T} (G : Flag σ U)
    : subflagDensity (emptyFlag σ) G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact labeledGraphDensity_empty Grep

omit [Fintype T] in
lemma induced_full_labeledSubgraph_eq_top
    {σ : FlagType T} {G₀ G₁ : LabeledGraph σ U} {G' : LabeledSubgraph σ G₀}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃f G₁) → G' = G₀.top
  := by
  intro ⟨h_ind_G', ⟨f_G'_G₁, _⟩⟩
  let f_U_G'_vertex : U ≃ G'.subgraph.verts := f_G'_G₁.toEquiv.symm
  apply labeledSubgraph_eq_from_subgraph_eq
  dsimp [LabeledGraph.top]
  ext u v
  · simp only [SimpleGraph.Subgraph.verts_top, Set.mem_univ, iff_true]
    exact iso_subset_of_finset_is_full f_U_G'_vertex u
  · have h_u := iso_subset_of_finset_is_full f_U_G'_vertex u
    have h_v := iso_subset_of_finset_is_full f_U_G'_vertex v
    exact ⟨SimpleGraph.Subgraph.Adj.adj_sub, h_ind_G' h_u h_v⟩

omit [Fintype T] [Fintype U] in
lemma top_labeledSubgraph_iso_G
    {σ : FlagType T} {G : LabeledGraph σ U}
    : Nonempty (G.top.coe ≃f G)
  := by
  let graph_iso : G.top.subgraph.coe ≃g G.graph := {
    toFun := (↑)
    invFun := fun u ↦ ⟨u, Set.mem_univ u⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦rfl
    map_rel_iff' := by rfl
  }
  exact Nonempty.intro ⟨graph_iso, rfl⟩

lemma labeledGraphCount_self
    {σ : FlagType T} (G : LabeledGraph σ U)
    : labeledGraphCount G G = 1
  := by
  dsimp [labeledGraphCount]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f G) }
  let S₁ := { G' : LabeledSubgraph σ G | G' = G.top }
  show S₀.toFinset.card = 1
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    simp only [Set.mem_setOf_eq, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff, S₀, S₁]
    refine ⟨induced_full_labeledSubgraph_eq_top, ?_⟩
    rintro rfl
    exact ⟨LabeledGraph.top_isInduced G, top_labeledSubgraph_iso_G⟩
  simp only [h_S₀_S₁, Set.setOf_eq_eq_singleton, Set.toFinset_singleton, Finset.card_singleton, S₁]

lemma labeledGraphDensity_self
    (G : LabeledGraph σ V) : labeledGraphDensity G G = 1
  := by
  simp only [labeledGraphDensity, Nat.choose_self, Nat.cast_one, div_one, Nat.cast_eq_one]
  exact labeledGraphCount_self G

/-- A flag has density `1` in itself. -/
lemma subflagDensity_self
    (G : Flag σ V) : subflagDensity G G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact labeledGraphDensity_self Grep

lemma labeledGraphCount_other
    {G₀ G₁ : LabeledGraph σ U} (h_not_iso : IsEmpty (G₀ ≃f G₁))
    : labeledGraphCount G₀ G₁ = 0
  := by
  let S := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f G₀) }
  show S.toFinset.card = 0
  suffices h_S_empty : S = ∅ by simp only [h_S_empty, Set.toFinset_empty, Finset.card_empty]
  rw [← Set.subset_empty_iff]
  intro G' ⟨h_G'_ind, h_G'_iso_G₀⟩
  have h_G'_eq_G₁_top := induced_full_labeledSubgraph_eq_top ⟨h_G'_ind, h_G'_iso_G₀⟩
  have h_G₁_top_iso_G₁ : Nonempty (G₁.top.coe ≃f G₁) := top_labeledSubgraph_iso_G
  rw [←h_G'_eq_G₁_top] at h_G₁_top_iso_G₁
  let f_G₀_G₁ : G₀ ≃f G₁ := h_G'_iso_G₀.some.symm.trans h_G₁_top_iso_G₁.some
  exact h_not_iso.elim f_G₀_G₁

lemma labeledGraphDensity_other
    {G₀ G₁ : LabeledGraph σ U} (h_not_iso : IsEmpty (G₀ ≃f G₁))
    : labeledGraphDensity G₀ G₁ = 0
  := by
  dsimp only [labeledGraphDensity]
  rw [labeledGraphCount_other h_not_iso]
  simp only [Nat.cast_zero, zero_div]

/-- Two distinct flags of the same size have density `0` in each other. -/
lemma subflagDensity_other
    {G₀ G₁ : Flag σ V} (h_neq : G₀ ≠ G₁)
    : subflagDensity G₀ G₁ = 0
  := by
  rcases Quotient.exists_rep G₀ with ⟨Grep₀, rfl⟩
  rcases Quotient.exists_rep G₁ with ⟨Grep₁, rfl⟩
  apply labeledGraphDensity_other
  rw [← not_nonempty_iff]
  exact fun h_iso ↦ h_neq <| Quotient.sound h_iso

end FlagAlgebras
