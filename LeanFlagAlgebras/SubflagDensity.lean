import «LeanFlagAlgebras».FlagDef
import Mathlib.Tactic.Linarith.Frontend

open FlagAlgebras
open Classical

variable {T : Type} [Fintype T] [DecidableEq T] {σ : FlagType T}
  {V W U: Type}
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  [Fintype U] [DecidableEq U]

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

def relOflabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁) : Prop
  :=
  H₁.subgraph.verts = φ.graph_iso '' H₀.subgraph.verts
  ∧ ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso.toFun u) (φ.graph_iso.toFun v)

def relOfPredOnlabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
  := ∀ (H₀: LabeledSubgraph σ G₀) (H₁: LabeledSubgraph σ G₁), (relOflabeledSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def predIsolabeledH
    (H : LabeledGraph σ U) (G : LabeledGraph σ W)
    : LabeledSubgraph σ G → Prop
  := fun G' ↦ Nonempty (G'.coe ≃f H)

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype  W] [DecidableEq W] [Fintype U] [DecidableEq U] in
lemma predIsolabeledH_related_support
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁)
    (h_vert : H₁.subgraph.verts = ⇑φ.graph_iso '' H₀.subgraph.verts)
    (h_adj : ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
    (h : Nonempty (H₀.coe ≃f H))
  : Nonempty (H₁.coe ≃f H) := by
  have iso_H₀_H₁ : Nonempty (H₀.coe ≃f H₁.coe) := by
    apply Nonempty.intro
    let ψ : H₀.subgraph.verts → H₁.subgraph.verts := by
      intro v
      use φ.graph_iso v
      simp_all only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, Subtype.coe_prop]
    have hψ : Function.Bijective ψ := by
      constructor
      · intro v₀ v₁ h_eq
        simp only [ψ, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact SetCoe.ext h_eq
      · intro w
        use ⟨(φ.graph_iso.symm w), by aesop⟩
        simp_all only [ψ, RelIso.apply_symm_apply]
    let ψ' := Equiv.ofBijective ψ hψ
    have hψ' : ∀ {v₀ v₁ : ↑H₀.subgraph.verts}, H₁.coe.graph.Adj (ψ' v₀) (ψ' v₁) ↔ H₀.coe.graph.Adj v₀ v₁ := by
      intro v₀ v₁
      dsimp [ψ']
      rw [← eq_iff_iff]
      exact (h_adj v₀ v₁).symm
    have h_emb : ∀ t : T, ψ' (H₀.type_embed t) = H₁.type_embed t := by
      intro t
      dsimp [ψ', ψ]
      have h_type_preserve := congr_fun φ.type_preserve t
      rw [Function.comp_apply] at h_type_preserve
      rw [← (H₀.embed_eq t), ← (H₁.embed_eq t)] at h_type_preserve
      exact SetCoe.ext h_type_preserve
    exact ⟨⟨ψ', hψ'⟩, funext h_emb⟩
  let iso_H₀_H := Classical.choice h
  let iso_H₀_H₁ := Classical.choice iso_H₀_H₁
  let iso_H₁_H := iso_H₀_H₁.symm.trans iso_H₀_H
  exact Nonempty.intro iso_H₁_H

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype  W] [DecidableEq W] [Fintype U] [DecidableEq U] in
lemma predIsolabeldH_related
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : relOfPredOnlabeledSubgraph φ (predIsolabeledH H G₀) (predIsolabeledH H G₁)
  := by
  dsimp [predIsolabeledH, relOfPredOnlabeledSubgraph, relOflabeledSubgraph]
  rintro H₀ H₁ ⟨h_vert, h_adj⟩
  constructor
  · intro f_iso
    exact predIsolabeledH_related_support φ H H₀ H₁ h_vert h_adj f_iso
  · intro f_iso
    have h_vert' : H₀.subgraph.verts = φ.graph_iso.symm '' H₁.subgraph.verts := by
      rw [h_vert]
      ext1 x
      simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
    have h_adj' : ∀ (u v : W), H₁.subgraph.Adj u v = H₀.subgraph.Adj (φ.graph_iso.symm u) (φ.graph_iso.symm v) := by
      intro u v
      have h_uv := h_adj (φ.graph_iso.symm u) (φ.graph_iso.symm v)
      rw [h_uv]
      simp only [RelIso.apply_symm_apply]
    exact predIsolabeledH_related_support φ.symm H H₁ H₀ h_vert' h_adj' f_iso

def inducedlabeledSubgraph
    {σ : FlagType T} (G : LabeledGraph σ V) (S : Set V) (hS : ∀ t : T, G.type_embed t ∈ S) : {G' : LabeledSubgraph σ G // G'.IsInduced}
  :=
  let G' : LabeledSubgraph σ G := {
    subgraph := {
      verts := S
      Adj := fun (u v : V) ↦ G.graph.Adj u v ∧ u ∈ S ∧ v ∈ S
      adj_sub := by
        intro v w h
        simp_all only [Set.mem_union, Set.mem_setOf_eq]
      edge_vert := by
        intro v w h
        simp_all only
      symm := by
        intro v w H
        simp_all only [and_self, and_true]
        exact G.graph.symm H.1
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, hS t⟩
      inj' := by
        intro t₁ t₂ h
        simp at h
        exact h
      map_rel_iff' := by
        intro t₁ t₂
        simp; intro _
        exact ⟨hS t₁, hS t₂⟩
    }
    embed_eq := by
      intro t; simp
  }
  let h_induced : G'.IsInduced := by
    intro v w hv hw hvw
    simp_all [Set.mem_union, Set.mem_setOf_eq]
  ⟨G', h_induced⟩

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma inducedlabeledSubgraph_type_embed_mem
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : ∀ (t : T), G₁.type_embed t ∈ ⇑φ.graph_iso '' H₀.subgraph.verts
  := by
  intro t
  simp_all only [Set.mem_image]
  use G₀.type_embed t
  constructor
  · have : H₀.type_embed t = G₀.type_embed t := H₀.embed_eq t
    rw [←this]
    simp
  · rw [←φ.type_preserve]; simp

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype  W] [DecidableEq W] in
lemma inducedlabeledSubgraph_related
    {σ : FlagType T } {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.subgraph.IsInduced)
    : relOflabeledSubgraph φ H₀ (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ H₀))
  := by
  dsimp [relOflabeledSubgraph, inducedlabeledSubgraph]; simp
  intro u v
  constructor
  · intro h_uv
    constructor
    · have : G₀.graph.Adj u v := SimpleGraph.Subgraph.Adj.adj_sub h_uv
      exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mpr this
    · exact ⟨H₀.subgraph.edge_vert h_uv, H₀.subgraph.edge_vert h_uv.symm⟩
  · intro ⟨h_G₁uv, ⟨h_u, h_v⟩⟩
    have h_G₀uv : G₀.graph.Adj u v := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_G₁uv
    apply h_ind₀ h_u h_v h_G₀uv

omit [Fintype V] [DecidableEq V] in
theorem inducedGraph_eq
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph}
  (h_verts : H.verts = H'.verts) (h_adj : ∀ u v : V, H.Adj u v = H'.Adj u v)
  : H = H' := by
  ext u v
  · exact Eq.to_iff (congrFun h_verts u)
  · exact Eq.to_iff (h_adj u v)

theorem graph_eq
  {P Q : Type} (h : P = Q)
  : SimpleGraph P = SimpleGraph Q := by
  subst h; rfl

omit [Fintype V] [DecidableEq V] in
theorem coe_eq
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph} (h : H = H') (h' : ↑H'.verts = ↑H.verts)
  : H.coe = cast (graph_eq h') H'.coe := by
  subst h; rfl

omit [Fintype V] [DecidableEq V] in
theorem embed_val_eq
  {T : Type} {σ : FlagType T}
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph}
  (G_emb : σ ↪g G) (H_emb : σ ↪g H.coe) (H'_emb : σ ↪g H'.coe)
  (h : H = H') (h' : ↑H'.verts = ↑H.verts)
  (h'' : ∀ t : T, H_emb t = G_emb t)
  (h''' : ∀ t : T, H'_emb t = G_emb t)
  : ∀ t : T, H_emb t = cast h' (H'_emb t) := by
  intro t
  subst h
  simp_all only [cast_eq]
  ext; rw [h'' t, h''' t]

omit [Fintype V] [DecidableEq V] in
theorem embed_eq
  {T : Type} {σ : FlagType T}
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph}
  (H_emb : σ ↪g H.coe) (H'_emb : σ ↪g H'.coe)
  (h : H = H') (h' : ↑H'.verts = ↑H.verts)
  (h'' : H.coe = cast (graph_eq h') H'.coe)
  (h''' : ∀ t : T, H_emb t = cast h' (H'_emb t))
  : HEq H_emb H'_emb := by
  subst h
  apply heq_of_eq
  ext t; simp_all only [cast_eq]

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype   W] [DecidableEq W] in
lemma H_eq_reverseinduced_induced_H
  {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.IsInduced)
  : H₀ = (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' ((inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ H₀)).1).subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ.symm ((inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ H₀)).1))).1 := by
  dsimp [inducedlabeledSubgraph]
  have h : H₀.subgraph.verts = ⇑φ.symm.graph_iso '' (⇑φ.graph_iso '' H₀.subgraph.verts) := by
    rw [Set.LeftInvOn.image_image]
    intro v _
    exact φ.graph_iso.left_inv v
  let f_H := inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ H₀)
  let f_inv_f_H := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' (f_H.1).subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ.symm (f_H.1))).1
  have h_verts : H₀.subgraph.verts = f_inv_f_H.subgraph.verts := by
    dsimp [f_inv_f_H, inducedlabeledSubgraph]
    exact h
  have h_adj : ∀ (u v : V), H₀.subgraph.Adj u v = f_inv_f_H.subgraph.Adj u v := by
    intro u v
    dsimp [f_inv_f_H, f_H, inducedlabeledSubgraph]
    simp; constructor
    · intro h_adj
      constructor
      · exact SimpleGraph.Subgraph.Adj.adj_sub h_adj
      · constructor
        · use u; exact ⟨H₀.subgraph.edge_vert h_adj, φ.graph_iso.left_inv u⟩
        · use v; exact ⟨H₀.subgraph.edge_vert h_adj.symm, φ.graph_iso.left_inv v⟩
    · intro ⟨h_adj, ⟨h_u, h_v⟩⟩
      obtain ⟨u', ⟨h_u', huu'⟩⟩ := h_u
      obtain ⟨v', ⟨h_v', hvv'⟩⟩ := h_v
      have h_u_eq : u = u' := by
        rw [←huu']
        exact φ.graph_iso.left_inv' u'
      have h_v_eq : v = v' := by
        rw [←hvv']
        exact φ.graph_iso.left_inv' v'
      subst h_u_eq h_v_eq
      exact h_ind₀ h_u' h_v' h_adj
  have inducedGraph_test := inducedGraph_eq h_verts h_adj
  refine LabeledSubgraph.ext ?subgraph ?type_embed
  · exact inducedGraph_test
  · simp
    have type_eq : (f_inv_f_H.subgraph.verts : Type) = (H₀.subgraph.verts : Type) := congrArg Set.Elem (id (Eq.symm h))
    have coe_eq := coe_eq inducedGraph_test type_eq
    have h_H₀_embed := H₀.embed_eq
    have h_f_inv_f_H_embed := f_inv_f_H.embed_eq
    have emb_eq : ∀ t : T, H₀.type_embed t = cast type_eq (f_inv_f_H.type_embed t) := by
      intro t
      exact
        embed_val_eq G₀.type_embed H₀.type_embed f_inv_f_H.type_embed inducedGraph_test type_eq
          h_H₀_embed h_f_inv_f_H_embed t
    have HEq := embed_eq H₀.type_embed f_inv_f_H.type_embed inducedGraph_test type_eq coe_eq emb_eq
    exact HEq

noncomputable def isoSetOfInducedlabeledSubgraph
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
    (h_rel : relOfPredOnlabeledSubgraph φ p₀ p₁) (h_rel_inv : relOfPredOnlabeledSubgraph φ.symm p₁ p₀)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' } ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  :=
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  let f : S₀ → S₁ := by
    intro s₀
    dsimp [S₀] at s₀
    let ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
    let H₁ := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ H₀)).1
    let h_ind₁ : H₁.IsInduced := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ H₀)).2
    have : relOflabeledSubgraph φ H₀ H₁ := inducedlabeledSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let H₀ := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ.symm H₁)).1
    let h_ind₀ : H₀.IsInduced := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts) (inducedlabeledSubgraph_type_embed_mem φ.symm H₁)).2
    have : relOflabeledSubgraph φ.symm H₁ H₀ := inducedlabeledSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv]
      simp;symm
      exact H_eq_reverseinduced_induced_H φ H₀ h_ind₀
    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv]
      simp; symm
      exact H_eq_reverseinduced_induced_H φ.symm H₁ h_ind₁
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedlabeledSubgraphIsoH
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) } ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  := by
  let iso := isoSetOfInducedlabeledSubgraph φ
    (predIsolabeledH H G₀)
    (predIsolabeledH H G₁)
    (predIsolabeldH_related φ H)
    (predIsolabeldH_related φ.symm H)
  dsimp [predIsolabeledH, relOfPredOnlabeledSubgraph] at iso
  exact iso

omit [DecidableEq T] in
lemma labeledSubgraphDensity_respects_eqv_on_G
    (H : LabeledGraph σ U) {G₀ G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    : labeledSubgraphDensity H G₀ = labeledSubgraphDensity H G₁
  := by
  dsimp [labeledSubgraphDensity]
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedlabeledSubgraphIsoH φ H
  have h_count : labeledSubgraphCount H G₀ = labeledSubgraphCount H G₁ := by
    dsimp only [labeledSubgraphCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  rw [h_count]
  rfl

noncomputable def labeledSubgraphDensityLifted
    (H : LabeledGraph σ V) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ W => labeledSubgraphDensity H G)
  intro _ _ G_eqv
  exact labeledSubgraphDensity_respects_eqv_on_G H (Classical.choice G_eqv)

noncomputable def isoSetOfInducedlabeledSubgraphInG
    {H₀ : LabeledGraph σ V} {H₁ : LabeledGraph σ W} (φ : H₀ ≃f H₁) (G : LabeledGraph σ U)
    : {G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₀)}
      ≃
      {G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₁)}
  := by
  let h : ∀ G' : LabeledSubgraph σ G, Nonempty (G'.coe ≃f H₀) ↔ Nonempty (G'.coe ≃f H₁) := by
    intro G'
    constructor
    · intro ⟨h_iso₀, h_emb₀⟩
      let h_iso₁ : G'.coe.graph ≃g H₁.graph := φ.graph_iso.comp h_iso₀
      have h_emb₀ : h_iso₁ ∘ G'.coe.type_embed = H₁.type_embed := by
        ext t
        rw [←φ.type_preserve, ←h_emb₀]
        dsimp [h_iso₁]
      exact ⟨h_iso₁, h_emb₀⟩
    · intro ⟨h_iso₁, h_emb₁⟩
      let h_iso₀ : G'.coe.graph ≃g H₀.graph := φ.symm.graph_iso.comp h_iso₁
      have h_emb₁ : h_iso₀ ∘ G'.coe.type_embed = H₀.type_embed := by
        ext t
        rw [←φ.symm.type_preserve, ←h_emb₁]
        dsimp [h_iso₀]
      exact ⟨h_iso₀, h_emb₁⟩
  have : {G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₀)} = {G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H₁)} :=
    Set.sep_ext_iff.mpr fun x _ ↦ h x
  exact Equiv.setCongr this

omit [DecidableEq T] in
lemma labeledSubgraphDensityLifted_respects_eqv
    (H H' : LabeledGraph σ V) (φ : H ≃f H') (G : Flag σ W)
    : labeledSubgraphDensityLifted H G = labeledSubgraphDensityLifted H' G
  := by
  dsimp [labeledSubgraphDensityLifted, labeledSubgraphDensity]
  congr
  ext Grep
  let S₀ := { G' : LabeledSubgraph σ Grep | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let S₁ := { G' : LabeledSubgraph σ Grep | G'.IsInduced ∧ Nonempty (G'.coe ≃f H') }
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedlabeledSubgraphInG φ Grep
  have h_count : labeledSubgraphCount H Grep = labeledSubgraphCount H' Grep := by
    dsimp only [labeledSubgraphCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  rw [h_count]
  rfl

noncomputable def subflagDensity
    : Flag σ V → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphDensityLifted
  intro H H' H_eqv
  ext G
  exact labeledSubgraphDensityLifted_respects_eqv H H' (Classical.choice H_eqv) G

omit [DecidableEq V] in
lemma iso_subset_of_finset_is_full
    {S : Set V} (f_iso : V ≃ ↑S) (u : V) : u ∈ S
  := by
  classical
  by_contra h_contra
  have h_card : Fintype.card S < Fintype.card V :=  Fintype.card_subtype_lt h_contra
  have h_card' : Fintype.card V = Fintype.card S := Fintype.card_congr f_iso
  simp_all only [lt_self_iff_false]

omit [Fintype T] [DecidableEq T] [DecidableEq V] in
lemma induced_full_labeledsubgraph_eq_top
    {G₀ G₁ : LabeledGraph σ V} {G' : LabeledSubgraph σ G₀}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃f G₁) → G' = G₀.top
  := by
  intro ⟨h_ind_G', h_iso_G'⟩
  have ⟨graph_iso, _⟩ := h_iso_G'
  let f_iso_vertex : V ≃ G'.subgraph.verts := graph_iso.toEquiv.symm
  have G'_eq_top : G'.subgraph = (G₀.top).subgraph := by
    dsimp [LabeledGraph.top]
    ext u v
    · simp; exact iso_subset_of_finset_is_full f_iso_vertex u
    · simp
      have h_u := iso_subset_of_finset_is_full f_iso_vertex u
      have h_v := iso_subset_of_finset_is_full f_iso_vertex v
      constructor
      · exact fun a ↦ SimpleGraph.Subgraph.Adj.adj_sub a
      · exact fun a ↦ h_ind_G' h_u h_v a
  refine LabeledSubgraph.ext ?subgraph ?type_embed
  · exact G'_eq_top
  · have verts_eq : (G₀.top).subgraph.verts = G'.subgraph.verts := by
      dsimp [LabeledGraph.top]
      ext u
      have := iso_subset_of_finset_is_full f_iso_vertex u
      exact (iff_true_right this).mpr trivial
    have type_eq : ((G₀.top).subgraph.verts : Type) = (G'.subgraph.verts : Type) := congrArg Set.Elem verts_eq
    have coe_eq := coe_eq G'_eq_top type_eq
    have h_G'_embed := G'.embed_eq
    have h_top_embed := (G₀.top).embed_eq
    have emb_eq : ∀ t : T, G'.type_embed t = cast type_eq ((G₀.top).type_embed t) := by
      intro t
      exact embed_val_eq G₀.type_embed G'.type_embed (G₀.top).type_embed G'_eq_top type_eq h_G'_embed h_top_embed t
    exact embed_eq G'.type_embed (G₀.top).type_embed G'_eq_top type_eq coe_eq emb_eq

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] in
lemma labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph
    {G : LabeledGraph σ V} {H : LabeledSubgraph σ G}
    : H = G.bottom ↔ H.IsInduced ∧ Nonempty (H.coe ≃f (emptyLabeledGraph σ)) := by
  let iso_T_G := G.iso_type_G
  constructor
  · intro h_eq
    subst h_eq
    constructor
    · intro u v hu hv h_adj
      dsimp [LabeledGraph.bottom] at *
      exact ⟨hu, ⟨hv, h_adj⟩⟩
    · let f : (G.bottom).subgraph.verts ≃ T := by
        dsimp [LabeledGraph.bottom]
        exact id iso_T_G.symm
      have f_adj : ∀ {u v : ↑(G.bottom).subgraph.verts},
  (emptyLabeledGraph σ).graph.Adj (f u) (f v) ↔ (G.bottom).subgraph.coe.Adj u v := by
        intro u v
        dsimp [LabeledGraph.bottom, emptyLabeledGraph]
        constructor
        · intro T_adj
          dsimp [LabeledGraph.bottom] at u v f
          have G_adj : G.graph.Adj u v := by
            let u_t := iso_T_G.symm u
            let v_t := iso_T_G.symm v
            have h_ut : u = iso_T_G u_t := Eq.symm (Equiv.apply_symm_apply iso_T_G u)
            have h_ut' : u_t = iso_T_G.symm u := rfl
            have h_vt : v = iso_T_G v_t := Eq.symm (Equiv.apply_symm_apply iso_T_G v)
            have h_vt' : v_t = iso_T_G.symm v := rfl
            dsimp [f] at T_adj
            rw [← h_ut', ← h_vt'] at T_adj
            have := (type_embed_Adj_iff G u_t v_t).mp T_adj
            rw [h_ut, h_vt]
            dsimp [iso_T_G]
            exact this
          exact ⟨u.property, ⟨v.property, G_adj⟩⟩
        · intro ⟨_, ⟨_, G_adj⟩⟩
          dsimp [f]
          let u_t := iso_T_G.symm u
          let v_t := iso_T_G.symm v
          have h_ut : u = iso_T_G u_t := Eq.symm (Equiv.apply_symm_apply iso_T_G u)
          have h_vt : v = iso_T_G v_t := Eq.symm (Equiv.apply_symm_apply iso_T_G v)
          rw [h_ut, h_vt]
          rw [iso_T_G.symm_apply_apply, iso_T_G.symm_apply_apply]
          apply (type_embed_Adj_iff G u_t v_t).mpr
          dsimp [iso_T_G] at h_ut h_vt
          rw [h_ut, h_vt] at G_adj
          exact G_adj
      let f_iso : (G.bottom).subgraph.coe ≃g (emptyLabeledGraph σ).graph := ⟨f, f_adj⟩
      have h_emb : ∀ t : T, f_iso ((G.bottom).coe.type_embed t) = (emptyLabeledGraph σ).type_embed t := by
        intro t
        dsimp [LabeledGraph.bottom, emptyLabeledGraph, f_iso, f]
        exact (Equiv.symm_apply_eq iso_T_G).mpr rfl
      exact ⟨f_iso, funext h_emb⟩
  · intro ⟨H_ind, H_iso⟩
    obtain ⟨graph_iso, type_embed⟩ := H_iso
    obtain ⟨iso_H_T, iso_adj⟩ := graph_iso
    have h_type_embed : ∀ t : T, iso_H_T (H.type_embed t) = t := by
      intro t
      have := congrFun type_embed t
      simp only [Function.comp_apply] at this
      exact this
    dsimp [LabeledGraph.bottom] at *
    have graph_eq_H_G : H.subgraph = (G.bottom).subgraph := by
      dsimp [LabeledGraph.bottom] at *
      simp at *
      ext u v
      · simp; constructor
        · intro hu
          let t := iso_H_T ⟨u, hu⟩
          have h_embed_t : H.type_embed t = u := by
            have ht := h_type_embed t
            dsimp [t] at *
            have := iso_H_T.injective ht
            simp_all only
          rw [← h_embed_t, H.embed_eq]
          unfold LabeledGraph.type_verts
          exact Set.mem_image_of_mem (⇑G.type_embed) trivial
        · intro hu
          unfold LabeledGraph.type_verts at hu
          simp at hu
          obtain ⟨t, h_t⟩ := hu
          rw [← h_t, ← H.embed_eq]
          exact Subtype.coe_prop (H.type_embed t)
      · simp; constructor
        · intro H_uv
          have hu : u ∈ H.subgraph.verts := H.subgraph.edge_vert H_uv
          let t₁ := iso_H_T ⟨u, hu⟩
          have h_embed_t₁ : H.type_embed t₁ = u := by
            have ht₁ := h_type_embed t₁
            dsimp [t₁] at *
            have := iso_H_T.injective ht₁
            simp_all only
          have h_t₁ : iso_H_T ⟨u, hu⟩ = t₁ := by
            simp only [h_embed_t₁]
          have hv : v ∈ H.subgraph.verts := H.subgraph.edge_vert H_uv.symm
          let t₂ := iso_H_T ⟨v, hv⟩
          have h_embed_t₂ : H.type_embed t₂ = v := by
            have ht₂ := h_type_embed t₂
            dsimp [t₂] at *
            have := iso_H_T.injective ht₂
            simp_all only
          have h_t₂ : iso_H_T ⟨v, hv⟩ = t₂ := by
            simp only [h_embed_t₂]
          have h_uv : H.coe.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩ := H_uv
          have flag_adj := (iso_adj u hu v hv).mpr h_uv
          have G_adj := (type_embed_Adj_iff G (iso_H_T ⟨u, hu⟩) (iso_H_T ⟨v, hv⟩)).mp flag_adj
          rw [h_t₁, h_t₂] at G_adj
          have hu' : u ∈ G.type_verts := by
            unfold LabeledGraph.type_verts
            rw [← h_embed_t₁, H.embed_eq]
            exact Set.mem_image_of_mem G.type_embed (Set.mem_univ t₁)
          have hv' : v ∈ G.type_verts := by
            unfold LabeledGraph.type_verts
            rw [← h_embed_t₂, H.embed_eq]
            exact Set.mem_image_of_mem G.type_embed (Set.mem_univ t₂)
          have h_adj : G.graph.Adj u v := SimpleGraph.Subgraph.Adj.adj_sub H_uv
          exact ⟨hu', ⟨hv', h_adj⟩⟩
        · intro ⟨hu, ⟨hv, h_adj⟩⟩
          have hu' : u ∈ H.subgraph.verts := by
            unfold LabeledGraph.type_verts at hu
            simp at hu
            obtain ⟨t, h_t⟩ := hu
            rw [← h_t, ← H.embed_eq]
            exact Subtype.coe_prop (H.type_embed t)
          have hv' : v ∈ H.subgraph.verts := by
            unfold LabeledGraph.type_verts at hv
            simp at hv
            obtain ⟨t, h_t⟩ := hv
            rw [← h_t, ← H.embed_eq]
            exact Subtype.coe_prop (H.type_embed t)
          exact H_ind hu' hv' h_adj
    refine LabeledSubgraph.ext ?subgraph ?type_embed
    · exact graph_eq_H_G
    · have verts_eq : ↑(G.bottom).subgraph.verts = ↑H.subgraph.verts := congrArg SimpleGraph.Subgraph.verts (id (Eq.symm graph_eq_H_G))
      have type_eq : ((G.bottom).subgraph.verts : Type) = (H.subgraph.verts : Type) := congrArg Set.Elem verts_eq
      have coe_eq := coe_eq graph_eq_H_G type_eq
      have h_G'_embed := H.embed_eq
      have h_top_embed := (G.bottom).embed_eq
      have emb_eq : ∀ t : T, H.type_embed t = cast type_eq ((G.bottom).type_embed t) := by
        intro t
        exact embed_val_eq G.type_embed H.type_embed (G.bottom).type_embed graph_eq_H_G type_eq h_G'_embed h_top_embed t
      exact embed_eq H.type_embed (G.bottom).type_embed graph_eq_H_G type_eq coe_eq emb_eq

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
      rw [← induced_full_labeledsubgraph_eq_top h_G']
      exact ⟨G', by simp only [Finset.mem_singleton]⟩
    let f_inj : Function.Injective f := by
      intro G₁ G₂ _
      have h₁ := induced_full_labeledsubgraph_eq_top G₁.property
      have h₂ := induced_full_labeledsubgraph_eq_top G₂.property
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
      have : G' = G₁.top := induced_full_labeledsubgraph_eq_top ⟨h_ind_G', h_iso_G'⟩
      let g : (G₁.top).coe ≃f G₁ := by
        let graph_iso : (G₁.top).subgraph.coe ≃g G₁.graph := by
          dsimp [LabeledGraph.top]
          simp [SimpleGraph.Subgraph.coe]
          let f : (G₁.top).subgraph.verts → V := by
            dsimp [LabeledGraph.top]
            intro v
            exact v.val
          have h_bij : Function.Bijective f := by
            constructor
            · intro v₁ v₂ h_eq
              dsimp [f] at h_eq
              exact SetCoe.ext h_eq
            · intro v
              exact CanLift.prf v trivial
          have h_iso : ∀ {w₀ w₁ : (G₁.top).subgraph.verts}, G₁.graph.Adj (f w₀) (f w₁) ↔ (G₁.top).subgraph.Adj w₀ w₁ := by
            intro u v
            simp [LabeledGraph.top, f]
          let f_equiv := Equiv.ofBijective f h_bij
          exact ⟨f_equiv, h_iso⟩
        have h_emb : ∀ t : T, graph_iso ((G₁.top).type_embed t) = G₁.type_embed t := by
          intro t
          exact rfl
        exact ⟨graph_iso, funext h_emb⟩
      rw [← this] at g
      exact g
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
