import «LeanFlagAlgebras».SubgraphUtil
import «LeanFlagAlgebras».FlagDef
import Mathlib.Tactic.Linarith.Frontend

open FlagAlgebras
open LabeledSubgraph
open Classical

variable {T : Type} [Fintype T] [DecidableEq T]
variable {σ : FlagType T}
variable {U : Type} [Fintype U] [DecidableEq U]
variable {V : Type} [Fintype V] [DecidableEq V]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {Z : Type} [Fintype Z] [DecidableEq Z]


noncomputable def labeledSubgraphCount
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℕ
  :=
  let p (G' : LabeledSubgraph σ G) : Prop := G'.IsInduced ∧ Nonempty (G'.coe ≃f H)
  let S := { G' : LabeledSubgraph σ G | p G' }
  S.toFinset.card

noncomputable def labeledSubgraphDensity
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℚ
  :=
  let labeledSubgraph_cnt := labeledSubgraphCount H G
  let num_of_all_induced_subgraph := (G.size - σ.size).choose (H.size - σ.size)
  labeledSubgraph_cnt / num_of_all_induced_subgraph

def relOfLabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁) : Prop
  :=
  relOfSubgraph φ.graph_iso H₀.subgraph H₁.subgraph


omit [Fintype T] [DecidableEq T]
     [Fintype V] [DecidableEq V]
     [Fintype W] [DecidableEq W] in
lemma relOfLabeledSubgraph_symm
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁) :
    (relOfLabeledSubgraph φ H₀ H₁) → (relOfLabeledSubgraph φ.symm H₁ H₀)
  := by
  intro ⟨h_vert, h_adj⟩
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
    simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, RelIso.apply_symm_apply]
  exact ⟨h_vert', h_adj'⟩

def relOfPredOnLabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
  :=
  ∀ (H₀: LabeledSubgraph σ G₀) (H₁: LabeledSubgraph σ G₁),
    (relOfLabeledSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def predIsoLabeledH
    (H : LabeledGraph σ U) (G : LabeledGraph σ W)
    : LabeledSubgraph σ G → Prop
  := fun G' ↦ Nonempty (G'.coe ≃f H)

omit [Fintype T] [DecidableEq T]
     [Fintype U] [DecidableEq U]
     [Fintype V] [DecidableEq V]
     [Fintype W] [DecidableEq W]
     [Fintype Z] [DecidableEq Z] in
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
      use ⟨(φ.graph_iso.symm w), by aesop⟩
      dsimp [f_ζ]
      simp only [RelIso.apply_symm_apply, Subtype.coe_eta]
  let ζ := Equiv.ofBijective f_ζ h_ζ_bij
  have h_ζ_adj : ∀ {v₀ v₁ : ↑G₀'.subgraph.verts}, G₁'.coe.graph.Adj (ζ v₀) (ζ v₁) ↔ G₀'.coe.graph.Adj v₀ v₁
    := by
    intro v₀ v₁
    dsimp [ζ]
    exact h_adj v₀ v₁
  have h_emb : ∀ t : T, ζ (G₀'.type_embed t) = G₁'.type_embed t := by
    intro t
    dsimp [ζ]
    have h_type_preserve := congr_fun φ.type_preserve t
    rw [Function.comp_apply, ← (G₀'.embed_eq t), ← (G₁'.embed_eq t)] at h_type_preserve
    exact SetCoe.ext h_type_preserve
  let iso_G₀'_G₁' : G₀'.coe ≃f G₁'.coe := ⟨⟨ζ, h_ζ_adj⟩, funext h_emb⟩
  let iso_G₀'_H₀ : G₀'.coe ≃f H₀ := Classical.choice h
  exact Nonempty.intro ((iso_G₀'_G₁'.symm.trans iso_G₀'_H₀).trans ψ)

omit [Fintype T] [DecidableEq T]
     [Fintype V] [DecidableEq V]
     [Fintype W] [DecidableEq W]
     [Fintype U] [DecidableEq U]
     [Fintype Z] [DecidableEq Z] in
lemma predIsoLabeledH_related
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : relOfPredOnLabeledSubgraph φ (predIsoLabeledH H₀ G₀) (predIsoLabeledH H₁ G₁)
  := by
  dsimp [predIsoLabeledH, relOfPredOnLabeledSubgraph]
  rintro G₀' G₁' h_rel
  constructor
  . exact predIsoLabeledH_related_support φ ψ G₀' G₁' h_rel
  . exact predIsoLabeledH_related_support φ.symm ψ.symm G₁' G₀' (relOfLabeledSubgraph_symm φ G₀' G₁' h_rel)

omit [Fintype T] [DecidableEq T]
     [Fintype V] [DecidableEq V]
     [Fintype W] [DecidableEq W] in
lemma labeledGraphIso_preserve_type_verts
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : G₁.type_verts ⊆ ⇑φ.graph_iso '' H₀.subgraph.verts
  := by
  intro t
  simp only [LabeledGraph.type_verts, Set.image_univ, Set.mem_range, Set.mem_image, forall_exists_index]
  intro u h_u
  use G₀.type_embed u
  constructor
  · rw [← H₀.embed_eq u]
    simp only [Subtype.coe_prop]
  · rw [←h_u, ← φ.type_preserve]
    simp only [Function.comp_apply]

def inducedLabeledSubgraphByIso
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : LabeledSubgraph σ G₁
  :=
  inducedLabeledSubgraph
    G₁ (φ.graph_iso '' H₀.subgraph.verts) (labeledGraphIso_preserve_type_verts φ H₀)

omit [Fintype T] [DecidableEq T]
     [Fintype V] [DecidableEq V]
     [Fintype W] [DecidableEq W] in
lemma inducedLabeledSubgraphByIso_isInduced
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : (inducedLabeledSubgraphByIso φ H₀).IsInduced
  :=
  inducedLabeledSubgraph_isInduced
    G₁
    (φ.graph_iso '' H₀.subgraph.verts)
    (labeledGraphIso_preserve_type_verts φ H₀)


omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype  W] [DecidableEq W] in
lemma inducedLabeledSubgraph_related
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.IsInduced)
    : relOfLabeledSubgraph φ H₀ (inducedLabeledSubgraphByIso φ H₀)
  := by
  dsimp [relOfLabeledSubgraph, inducedLabeledSubgraph]
  apply inducedSubgraph_related φ.graph_iso H₀.subgraph h_ind₀

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] in
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

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] in
theorem type_embed_heq_of_subgraph_eq
    {σ : FlagType T} {G : LabeledGraph σ V} {H H' : LabeledSubgraph σ G}
    (H_eq_H' : H.subgraph = H'.subgraph)
    : HEq H.type_embed H'.type_embed
  := by
  have h_embed_eq : ∀ t : T, (H.type_embed t : V) = (H'.type_embed t : V) := by
    intro t
    rw [H.embed_eq t, H'.embed_eq t]
  exact embed_heq_of_subgraph_eq H_eq_H' h_embed_eq

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
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
    dsimp [H₀',inducedLabeledSubgraphByIso, inducedLabeledSubgraph]
    simp only [inducedSubgraph_verts, ←h]
    exact inducedSubgraph_eq h_ind₀
  exact LabeledSubgraph.ext h_eq (type_embed_heq_of_subgraph_eq h_eq)

noncomputable def isoSetOfInducedLabeledSubgraph
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
    (h_rel : relOfPredOnLabeledSubgraph φ p₀ p₁)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
      ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  :=
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  let f : S₀ → S₁ := by
    intro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
    let H₁ := inducedLabeledSubgraphByIso φ H₀
    let h_ind₁ : H₁.IsInduced := inducedLabeledSubgraphByIso_isInduced φ H₀
    have : relOfLabeledSubgraph φ H₀ H₁ := inducedLabeledSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv : S₁ → S₀ := by
    intro ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
    let H₀ := inducedLabeledSubgraphByIso φ.symm H₁
    let h_ind₀ : H₀.IsInduced := inducedLabeledSubgraphByIso_isInduced φ.symm H₁
    have : relOfLabeledSubgraph φ.symm H₁ H₀ := inducedLabeledSubgraph_related φ.symm H₁ h_ind₁
    have : relOfLabeledSubgraph φ H₀ H₁ := relOfLabeledSubgraph_symm φ.symm H₁ H₀ this
    have h_p₀ : p₀ H₀ := (h_rel H₀ H₁ this).mpr h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv]
      simp only [Subtype.mk.injEq]; symm
      exact H_eq_reverseinduced_induced_H φ H₀ h_ind₀
    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv]
      simp only [Subtype.mk.injEq]; symm
      exact H_eq_reverseinduced_induced_H φ.symm H₁ h_ind₁
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedLabeledSubgraphFromIsoHG
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₀) }
      ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₁) }
  := by
  let iso :=
    isoSetOfInducedLabeledSubgraph φ
      (predIsoLabeledH H₀ G₀)
      (predIsoLabeledH H₁ G₁)
      (predIsoLabeledH_related φ ψ)
  dsimp [predIsoLabeledH, relOfPredOnLabeledSubgraph] at iso
  exact iso

omit [DecidableEq T] in
lemma labeledSubgraphDensity_respect_eqv
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    {H₀ : LabeledGraph σ W} {H₁ : LabeledGraph σ Z} (ψ : H₀ ≃f H₁)
    : labeledSubgraphDensity H₀ G₀ = labeledSubgraphDensity H₁ G₁
  := by
  dsimp [labeledSubgraphDensity]
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₀) }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₁) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedLabeledSubgraphFromIsoHG φ ψ
  have h_count : labeledSubgraphCount H₀ G₀ = labeledSubgraphCount H₁ G₁ := by
    dsimp only [labeledSubgraphCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  have h_H_size : H₀.size = H₁.size := labeledGraphIso_size_eq H₀ H₁ ψ
  have h_G_size : G₀.size = G₁.size := labeledGraphIso_size_eq G₀ G₁ φ
  rw [h_count, h_H_size, h_G_size]


noncomputable def labeledSubgraphDensityLifted
    (H : LabeledGraph σ V) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ W => labeledSubgraphDensity H G)
  intro _ _ G_eqv
  exact labeledSubgraphDensity_respect_eqv (Classical.choice G_eqv) LabeledGraphIso.refl


omit [DecidableEq T] in
lemma labeledSubgraphDensityLifted_respect_eqv
    {H₀ : LabeledGraph σ U} {H₁ : LabeledGraph σ V} (ψ : H₀ ≃f H₁) (G : Flag σ W)
    : labeledSubgraphDensityLifted H₀ G = labeledSubgraphDensityLifted H₁ G
  := by
  dsimp [labeledSubgraphDensityLifted, labeledSubgraphDensity]
  congr
  ext Grep
  let S₀ := { G' : LabeledSubgraph σ Grep | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₀) }
  let S₁ := { G' : LabeledSubgraph σ Grep | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₁) }
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedLabeledSubgraphFromIsoHG LabeledGraphIso.refl ψ
  have h_count : labeledSubgraphCount H₀ Grep = labeledSubgraphCount H₁ Grep := by
    dsimp only [labeledSubgraphCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  have h_H_size : H₀.size = H₁.size := labeledGraphIso_size_eq H₀ H₁ ψ
  rw [h_count, h_H_size]

noncomputable def subflagDensity
    : Flag σ V → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphDensityLifted
  intro H H' h_eqv
  ext G
  exact labeledSubgraphDensityLifted_respect_eqv (Classical.choice h_eqv) G


omit [Fintype T] [DecidableEq T] [DecidableEq U] in
lemma induced_full_labeledSubgraph_eq_top
    {σ : FlagType T} {G₀ G₁ : LabeledGraph σ U} {G' : LabeledSubgraph σ G₀}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃f G₁) → G' = G₀.top
  := by
  intro ⟨h_ind_G', ⟨f_G'_G₁, _⟩⟩
  let f_U_G'_vertex : U ≃ G'.subgraph.verts := f_G'_G₁.toEquiv.symm
  have G'_eq_top : G'.subgraph = G₀.top.subgraph := by
    dsimp [LabeledGraph.top]
    ext u v
    · simp only [SimpleGraph.Subgraph.verts_top, Set.mem_univ, iff_true]
      exact iso_subset_of_finset_is_full f_U_G'_vertex u
    · have h_u := iso_subset_of_finset_is_full f_U_G'_vertex u
      have h_v := iso_subset_of_finset_is_full f_U_G'_vertex v
      constructor
      · intro h_uv; exact SimpleGraph.Subgraph.Adj.adj_sub h_uv
      · intro h_uv; exact h_ind_G' h_u h_v h_uv
  refine LabeledSubgraph.ext ?subgraph ?type_embed
  · exact G'_eq_top
  · exact type_embed_heq_of_subgraph_eq G'_eq_top

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] in
lemma labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph
    {G : LabeledGraph σ V} {H : LabeledSubgraph σ G}
    : H = G.bottom ↔ H.IsInduced ∧ Nonempty (H.coe ≃f (emptyLabeledGraph σ)) := by
  constructor
  · intro h_eq
    subst h_eq
    constructor
    · intro u v hu hv h_adj
      dsimp [LabeledGraph.bottom] at *
      exact ⟨hu, hv, h_adj⟩
    · let f : (G.bottom).subgraph.verts ≃ T := by
        dsimp [LabeledGraph.bottom]
        exact id G.iso_type_G.symm
      have f_adj : ∀ {u v : ↑(G.bottom).subgraph.verts},
  (emptyLabeledGraph σ).graph.Adj (f u) (f v) ↔ (G.bottom).subgraph.coe.Adj u v := by
        intro u v
        dsimp [LabeledGraph.bottom, emptyLabeledGraph]
        constructor
        · intro T_adj
          have G_adj := (iso_type_Adj_iff G u v).mp T_adj
          exact ⟨u.property, ⟨v.property, G_adj⟩⟩
        · intro ⟨_, _, G_adj⟩
          exact (iso_type_Adj_iff G u v).mpr G_adj
      let f_iso : (G.bottom).subgraph.coe ≃g (emptyLabeledGraph σ).graph := ⟨f, f_adj⟩
      have h_emb : ∀ t : T, f_iso ((G.bottom).coe.type_embed t) = (emptyLabeledGraph σ).type_embed t := by
        intro t
        dsimp [LabeledGraph.bottom, emptyLabeledGraph, f_iso, f]
        exact (Equiv.symm_apply_eq G.iso_type_G).mpr rfl
      exact ⟨f_iso, funext h_emb⟩
  · intro ⟨H_ind, H_iso⟩
    obtain ⟨⟨iso_H_T, iso_adj⟩, type_embed⟩ := H_iso
    have h_type_embed : ∀ t : T, iso_H_T (H.type_embed t) = t := by
      intro t
      exact congrFun type_embed t
    have graph_eq_H_G : H.subgraph = (G.bottom).subgraph := by
      dsimp [LabeledGraph.bottom] at *
      have H_verts_iff_type_verts : ∀ w : V, w ∈ H.subgraph.verts ↔ w ∈ G.type_verts := by
        intro w
        constructor
        · intro hw
          let t := iso_H_T ⟨w, hw⟩
          have h_embed_t : H.type_embed t = w := by
            have ht := h_type_embed t
            dsimp [t] at *
            exact congr_arg Subtype.val (iso_H_T.injective ht)
          rw [← h_embed_t, H.embed_eq]
          exact LabeledGraph.type_verts_contain G t
        · intro hw
          obtain ⟨t, _, h_t⟩ := hw
          rw [← h_t, ← H.embed_eq]
          exact Subtype.coe_prop (H.type_embed t)
      ext u v
      · rw [H_verts_iff_type_verts]
      · simp only
        constructor
        · intro H_uv
          have hu : u ∈ G.type_verts := (H_verts_iff_type_verts u).mp (H.subgraph.edge_vert H_uv)
          have hv : v ∈ G.type_verts := (H_verts_iff_type_verts v).mp (H.subgraph.edge_vert H_uv.symm)
          have h_adj : G.graph.Adj u v := SimpleGraph.Subgraph.Adj.adj_sub H_uv
          exact ⟨hu, hv, h_adj⟩
        · intro ⟨hu, hv, h_adj⟩
          have hu' : u ∈ H.subgraph.verts := (H_verts_iff_type_verts u).mpr hu
          have hv' : v ∈ H.subgraph.verts := (H_verts_iff_type_verts v).mpr hv
          exact H_ind hu' hv' h_adj
    refine LabeledSubgraph.ext ?subgraph ?type_embed
    · exact graph_eq_H_G
    · exact type_embed_heq_of_subgraph_eq graph_eq_H_G

lemma labeledSubgraphCount_empty
    {σ : FlagType T} (G : LabeledGraph σ V) : labeledSubgraphCount (emptyLabeledGraph σ) G = ((G.size - σ.size).choose ((emptyLabeledGraph σ).size - σ.size))
  := by
  dsimp only [LabeledGraph.size]
  have : Fintype.card T = σ.size := by rfl
  rw [this]; simp
  simp [labeledSubgraphCount]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f (emptyLabeledGraph σ)) }
  let S₁ := { G' : LabeledSubgraph σ G | G' = G.bottom }
  have h_S₀_S₁' : S₀ ≃ S₁ := by
    let f : S₀ → S₁ := by
      dsimp [S₀, S₁]
      intro ⟨G', h_G'⟩
      have h_eq : G' = G.bottom := labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph.mpr h_G'
      exact ⟨G', h_eq⟩
    have f_inj : Function.Injective f := by
      intro ⟨G₁', h₁⟩ ⟨G₂', h₂⟩ h_eq
      simp_all only [id_eq, Subtype.mk.injEq, f]
    have f_surj : Function.Surjective f := by
      intro ⟨G', h_G'⟩
      dsimp [S₁] at h_G'
      subst h_G'
      have h_bottom : G.bottom ∈ S₀ := labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph.mp rfl
      exact ⟨⟨G.bottom, h_bottom⟩, rfl⟩
    exact Equiv.ofBijective f ⟨f_inj, f_surj⟩
  have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_S₀_S₁'
  have h_finset_eq_fintype : (Finset.filter (fun x : LabeledSubgraph σ G ↦ x.IsInduced ∧ Nonempty (x.coe ≃f (emptyLabeledGraph σ))) Finset.univ).card = Fintype.card S₀ := by
    rw [← Set.toFinset_card]
    simp_all only [Set.toFinset_setOf, S₀]
  rw [h_finset_eq_fintype, card_eq]
  simp_all only [Set.setOf_eq_eq_singleton, Fintype.card_unique, S₁]

lemma labeledSubgraphDensity_empty
    (G : LabeledGraph σ V) : labeledSubgraphDensity (emptyLabeledGraph σ) G = 1
  := by
  simp [labeledSubgraphDensity]
  rw [labeledSubgraphCount_empty G]
  have : ((G.size - σ.size).choose ((emptyLabeledGraph σ).size - σ.size) : ℚ) ≠ 0 := by
    dsimp only [emptyLabeledGraph, LabeledGraph.size]
    have : Fintype.card T = σ.size := by rfl
    rw [this]
    simp only [le_refl, tsub_eq_zero_of_le, Nat.choose_zero_right]
    simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true]
  exact (div_eq_one_iff_eq this).mpr rfl

lemma subflagDensity_empty
    (G : Flag σ V) : subflagDensity (emptyFlag σ) G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  dsimp [emptyFlag]
  subst hGrep
  dsimp [subflagDensity, labeledSubgraphDensityLifted]
  exact labeledSubgraphDensity_empty Grep

omit [DecidableEq T] in
lemma labeledSubgraphCount_self
    (G : LabeledGraph σ V) : labeledSubgraphCount G G = 1
  := by
  simp [labeledSubgraphCount]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f G) }
  let S₁ : Finset (LabeledSubgraph σ G) := { G.top }
  have h_S₀_S₁ : S₀ ≃ S₁ := by
    let f : S₀ → S₁ := by
      dsimp [S₀, S₁]
      intro ⟨G', h_G'⟩
      rw [← induced_full_labeledSubgraph_eq_top h_G']
      exact ⟨G', by simp only [Finset.mem_singleton]⟩
    let f_inj : Function.Injective f := by
      intro G₁ G₂ _
      have h₁ := induced_full_labeledSubgraph_eq_top G₁.property
      have h₂ := induced_full_labeledSubgraph_eq_top G₂.property
      rw [← h₂] at h₁
      exact SetCoe.ext h₁
    let f_surj : Function.Surjective f := by
      intro ⟨G', h_G'⟩
      dsimp [S₁] at h_G'
      rw [Finset.mem_singleton] at h_G'
      subst h_G'
      have h_G_top : G.top ∈ S₀ := by
        constructor
        · exact G.top_isInduced
        · let g : G.top.subgraph.verts ≃ V := by
            dsimp [LabeledGraph.top]
            exact Equiv.Set.univ V
          have g_adj : ∀ {w₀ w₁ : G.top.subgraph.verts}, G.graph.Adj (g w₀) (g w₁) ↔ G.top.subgraph.Adj w₀ w₁ := by
            intro u v
            dsimp [LabeledGraph.top]
            exact Eq.to_iff rfl
          let g_iso : G.top.subgraph.coe ≃g G.graph := ⟨g, g_adj⟩
          have h_emb : ∀ t : T, g ((G.top).type_embed t) = G.type_embed t := by
            intro t; rfl
          exact ⟨g_iso, funext h_emb⟩
      use ⟨G.top, h_G_top⟩
      dsimp [f]
    exact Equiv.ofBijective f ⟨f_inj, f_surj⟩
  have card_eq : Fintype.card S₀ = S₁.card := Fintype.card_congr h_S₀_S₁
  have h_finset_eq_fintype : (Finset.filter (fun x : LabeledSubgraph σ G ↦ x.IsInduced ∧ Nonempty (x.coe ≃f G)) Finset.univ).card = Fintype.card S₀ := by
    rw [← Set.toFinset_card]
    simp_all only [Set.toFinset_setOf, S₀]
  rw [h_finset_eq_fintype, card_eq]
  rfl

omit [DecidableEq T] in
lemma labeledSubgraphDensity_self
    (G : LabeledGraph σ V) : labeledSubgraphDensity G G = 1
  := by
  simp [labeledSubgraphDensity]
  exact labeledSubgraphCount_self G

omit [DecidableEq T] in
lemma subflagDensity_self
    (G : Flag σ V) : subflagDensity G G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  dsimp [subflagDensity, labeledSubgraphDensityLifted]
  subst hGrep
  dsimp [labeledSubgraphDensityLifted]
  exact labeledSubgraphDensity_self Grep

omit [DecidableEq T] in
lemma subgraphCount_other
    {G₀ G₁ : LabeledGraph σ V} (h_neq : IsEmpty (G₀ ≃f G₁)) : labeledSubgraphCount G₀ G₁ = 0
  := by
  simp [labeledSubgraphCount]
  rw [← not_nonempty_iff] at h_neq
  let S := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f G₀) }
  have h_S : S ⊆ ∅ := by
    intro G' ⟨h_ind_G', h_iso_G'⟩
    have f_iso_G₀_G' := h_iso_G'.some.symm
    have f_iso_G'_G₁ : G'.coe ≃f G₁ := by
      have : G' = G₁.top := induced_full_labeledSubgraph_eq_top ⟨h_ind_G', h_iso_G'⟩
      let g : (G₁.top).coe ≃f G₁ := by
        let graph_iso : (G₁.top).subgraph.coe ≃g G₁.graph := by
          dsimp [LabeledGraph.top]
          let f : (G₁.top).subgraph.verts → V := by
            dsimp [LabeledGraph.top]
            exact fun v ↦ v.val
          have h_bij : Function.Bijective f := by
            constructor
            · intro v₁ v₂ h_eq
              dsimp [f] at h_eq
              exact SetCoe.ext h_eq
            · intro v
              exact CanLift.prf v trivial
          have h_adj : ∀ {w₀ w₁ : (G₁.top).subgraph.verts}, G₁.graph.Adj (f w₀) (f w₁) ↔ (G₁.top).subgraph.Adj w₀ w₁ := by
            intro u v
            simp only [id_eq, LabeledGraph.top, SimpleGraph.Subgraph.top_adj, f]
          let h_iso := Equiv.ofBijective f h_bij
          exact ⟨h_iso, h_adj⟩
        have h_emb : ∀ t : T, graph_iso ((G₁.top).type_embed t) = G₁.type_embed t := by
          intro t
          exact rfl
        exact ⟨graph_iso, funext h_emb⟩
      rwa [← this] at g
    have f_iso_G₀_G₁ := f_iso_G₀_G'.trans f_iso_G'_G₁
    exact h_neq ⟨f_iso_G₀_G₁⟩
  rw [Set.subset_empty_iff] at h_S
  rw [← Finset.card_eq_zero]
  calc
    _ = Fintype.card S := Eq.symm
        (Fintype.card_ofFinset (Finset.filter (Membership.mem S) Finset.univ)
          (Subtype.fintype.proof_1 (Membership.mem S)))
    _ = 0 := by
      simp_all only [not_nonempty_iff, Fintype.card_ofIsEmpty, S]

example (S : Finset V) (h : Fintype.card S = 0) : S = ∅ := by
  simp_all only [Fintype.card_coe, Finset.card_eq_zero]

omit [DecidableEq T] in
lemma labeledSubgraphDensity_other
    {G₀ G₁ : LabeledGraph σ V} (h_neq : IsEmpty (G₀ ≃f G₁)) : labeledSubgraphDensity G₀ G₁ = 0
  := by
  dsimp [labeledSubgraphDensity]
  have := subgraphCount_other h_neq
  simp_all only [Nat.cast_zero, zero_div]

omit [DecidableEq T] in
lemma subflagDensity_other
    {G₀ G₁ : Flag σ V} (h_neq : G₀ ≠ G₁) : subflagDensity G₀ G₁ = 0
  := by
  rcases Quotient.exists_rep G₀ with ⟨Grep₀, hGrep₀⟩
  rcases Quotient.exists_rep G₁ with ⟨Grep₁, hGrep₁⟩
  rw [← hGrep₀, ← hGrep₁]
  have h_neq' : IsEmpty (Grep₀ ≃f Grep₁) := by
    rw [← not_nonempty_iff]
    intro h_iso
    have h_eq : G₀ = G₁ := by
      rw [← hGrep₀, ← hGrep₁]
      exact Quotient.sound h_iso
    exact h_neq h_eq
  apply labeledSubgraphDensity_other h_neq'
