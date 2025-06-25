import «LeanFlagAlgebras».SubflagDensity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

open FlagAlgebras
open Classical

variable {T : Type} [Fintype T] [DecidableEq T] {σ : FlagType T}
  {t : ℕ}
  {Vl : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl]
  {Vl' : Fin t → Type} [FintypeList Vl'] [DecidableEqList Vl']
  {V : Type} [Fintype V] [DecidableEq V]
  {W : Type} [Fintype W] [DecidableEq W]
  {U : Type} [Fintype U] [DecidableEq U]
  {U₁ : Type} [Fintype U₁] [DecidableEq U₁]
  {U₂ : Type} [Fintype U₂] [DecidableEq U₂]
  {U₃ : Type} [Fintype U₃] [DecidableEq U₃]

def labeledSubgraphListSet
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
  : Set (∀ (_ : Fin t), LabeledSubgraph σ G) :=
  let ind (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (Gl i).IsInduced
  let p₁ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)
  let p₂ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅
  { Gl | ind Gl ∧ p₁ Gl ∧ p₂ Gl }

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℕ
  :=
  have : Fintype (labeledSubgraphListSet Hl G) := Fintype.ofFinite _
  (labeledSubgraphListSet Hl G).toFinset.card

def multinomialCoefficient
    (r_list : Fin t → ℕ) (n : ℕ) : ℕ
  :=
  let r_sum := ∑ i : Fin t, r_list i
  if _ : n ≥ r_sum then
    Nat.factorial n / ((∏ i : Fin t, Nat.factorial (r_list i)) * Nat.factorial (n - r_sum))
  else 0

noncomputable def labeledSubgraphListDensity
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list := fun (i : Fin t) => (Hl i).size - σ.size
  labeledSubgraphListCount Hl G / multinomialCoefficient r_list (G.size - σ.size)

def relOflabeledSubgraphList
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (H₁ : ∀ (_ : Fin t), LabeledSubgraph σ G₁) : Prop
  := ∀ (i : Fin t), (H₁ i).subgraph.verts = φ.graph_iso '' (H₀ i).subgraph.verts
    ∧ ∀ (u v : V), (H₀ i).subgraph.Adj u v ↔ (H₁ i).subgraph.Adj (φ.graph_iso u) (φ.graph_iso v)

def relOfPredOnlabeledSubgraphList
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : (∀ (_ : Fin t), LabeledSubgraph σ G₀) → Prop)
    (p₁ : (∀ (_ : Fin t), LabeledSubgraph σ G₁) → Prop)
  := ∀ (H₀: ∀ (_ : Fin t), LabeledSubgraph σ G₀) (H₁: ∀ (_ : Fin t), LabeledSubgraph σ G₁), (relOflabeledSubgraphList φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def predIsoLabeledHl
    {σ : FlagType T} (G : LabeledGraph σ V)
    (Hl : LabeledGraphList σ t Vl)
    : (∀ (_ : Fin t), LabeledSubgraph σ G) → Prop
  := fun Gl ↦ (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅)

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma predIsoLabeledH_related_ind
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁)
    (h_vert : H₁.subgraph.verts = ⇑φ.graph_iso '' H₀.subgraph.verts)
    (h_adj : ∀ (u v : V), H₀.subgraph.Adj u v ↔ H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
    (h_ind₀ : H₀.IsInduced)
  : H₁.IsInduced := by
  intro u v h_u h_v h_uv
  rw [h_vert] at h_u h_v
  simp [Set.mem_image] at h_u h_v
  obtain ⟨u', ⟨h_u', h_uu'⟩⟩ := h_u
  obtain ⟨v', ⟨h_v', h_vv'⟩⟩ := h_v
  subst h_vv' h_uu'
  have h_uv' : G₀.graph.Adj (u') (v') := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_uv
  exact (h_adj u' v').mp (h_ind₀ h_u' h_v' h_uv')

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype U] [DecidableEq U] in
lemma predIsoLabeledH_related_iso  -- Same as predIsolabeledH_related_support
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁)
    (h_vert : H₁.subgraph.verts = ⇑φ.graph_iso '' H₀.subgraph.verts)
    (h_adj : ∀ (u v : V), H₀.subgraph.Adj u v ↔ H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
    (h_iso₀ : Nonempty (H₀.coe ≃f H))
  : Nonempty (H₁.coe ≃f H) := by
  have h := predIsolabeldH_related φ (H₀).coe
  dsimp [relOfPredOnlabeledSubgraph, relOflabeledSubgraph, predIsolabeledH] at h
  simp at h
  have iso_refl : Nonempty ((H₀).coe ≃f (H₀).coe) := by
    have : (H₀).coe ≃f (H₀).coe := LabeledGraphIso.refl
    exact Nonempty.intro this
  have iso_H₁_H₀ := (h H₀ H₁ h_vert h_adj).mp iso_refl
  let H₀_H := Classical.choice h_iso₀
  let H₁_H₀ := Classical.choice iso_H₁_H₀
  have h_iso₁ : H₁.coe ≃f H := H₁_H₀.trans H₀_H
  exact Nonempty.intro h_iso₁

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma predIsoLabeledHl_related_indep
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (Hl₁ : ∀ (_ : Fin t), LabeledSubgraph σ G₁)
    (v_rel :  ∀ (i : Fin t), (Hl₁ i).subgraph.verts = ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts)
    : ∀ (i j : Fin t), (((Hl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Hl₀ j).subgraph.verts \ G₀.type_verts) = ∅) →
      (((Hl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Hl₁ j).subgraph.verts \ G₁.type_verts) = ∅) := by
  intro i j h_empty
  by_contra h_nonempty
  push_neg at h_nonempty
  have h_nomempty_exists : ∃ w : W, w ∈ ((Hl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Hl₁ j).subgraph.verts \ G₁.type_verts) := h_nonempty
  obtain ⟨w, ⟨h_wi₁, h_wj₁⟩⟩ := h_nomempty_exists
  have h_w : ∀ (k : Fin t), w ∈ (Hl₁ k).subgraph.verts → φ.symm.graph_iso w ∈ (Hl₀ k).subgraph.verts := by
    intro k h_wk₁
    rw [v_rel k] at h_wk₁
    rw [Set.mem_image] at h_wk₁
    obtain ⟨w', ⟨h_wk₀, h_ww'⟩⟩ := h_wk₁
    rw [← h_ww']
    have := φ.graph_iso.left_inv' w'
    exact Set.mem_of_eq_of_mem this h_wk₀
  have h_w' : w ∉ G₁.type_verts → φ.symm.graph_iso w ∉ G₀.type_verts := by
    intro h_wk₁
    by_contra h_w'
    have : w ∈ G₁.type_verts := by
      have : ∃ t : T, φ.symm.graph_iso w = G₀.type_embed t := by
        unfold LabeledGraph.type_verts at h_w'
        obtain ⟨t, h_t⟩ := h_w'
        use t
        simp_all only [Set.mem_univ]
      obtain ⟨t, h_t⟩ := this
      rw [← φ.symm.type_preserve] at h_t
      simp at h_t
      rw [h_t]
      unfold LabeledGraph.type_verts
      exact Set.mem_image_of_mem (⇑G₁.type_embed) trivial
    exact h_wk₁ this
  have h_wi₀ : φ.symm.graph_iso w ∈ ((Hl₀ i).subgraph.verts \ G₀.type_verts) := Set.mem_diff_of_mem (h_w i h_wi₁.left) (h_w' h_wi₁.right)
  have h_wj₀ : φ.symm.graph_iso w ∈ ((Hl₀ j).subgraph.verts \ G₀.type_verts) := Set.mem_diff_of_mem (h_w j h_wj₁.left) (h_w' h_wj₁.right)
  have h_w_ij : φ.symm.graph_iso w ∈ ((Hl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Hl₀ j).subgraph.verts \ G₀.type_verts) := Set.mem_inter h_wi₀ h_wj₀
  simp_all only [Set.mem_empty_iff_false]

 omit [Fintype T] [DecidableEq T] [FintypeList Vl] [DecidableEqList Vl] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma predIsoLabeledHl_related
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (Hl : LabeledGraphList σ t Vl)
    : relOfPredOnlabeledSubgraphList φ
    (predIsoLabeledHl G₀ Hl) (predIsoLabeledHl G₁ Hl)
  := by
  dsimp [predIsoLabeledHl, relOfPredOnlabeledSubgraphList, relOflabeledSubgraph]
  intro Hl₀ Hl₁ h_rel
  dsimp [relOflabeledSubgraphList] at h_rel
  constructor
  · intro ⟨h_ind₀, ⟨h_1₀, h_2₀⟩⟩
    have h_ind₁ : ∀ (i : Fin t), (Hl₁ i).IsInduced := by
      intro i
      have ⟨h_vert, h_adj⟩ := h_rel i
      dsimp [LabeledSubgraph.IsInduced]
      intro u v h_u h_v h_uv
      apply predIsoLabeledH_related_ind φ (Hl₀ i) (Hl₁ i) h_vert h_adj (h_ind₀ i) h_u h_v h_uv
    have h_1₁ : ∀ (i : Fin t), Nonempty ((Hl₁ i).coe ≃f Hl i) := by
      intro i
      have ⟨h_vert, h_adj⟩ := h_rel i
      exact predIsoLabeledH_related_iso φ (Hl i) (Hl₀ i) (Hl₁ i) h_vert h_adj (h_1₀ i)
    have h_2₁ : ∀ (i j : Fin t), i ≠ j → ((Hl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Hl₁ j).subgraph.verts \ G₁.type_verts) = ∅ := by
      intro i j h_ij
      have h_empty_i := (h_2₀ i j h_ij)
      have v_rel : ∀ (i : Fin t), (Hl₁ i).subgraph.verts = φ.graph_iso '' (Hl₀ i).subgraph.verts := fun i ↦ (h_rel i).1
      exact (predIsoLabeledHl_related_indep φ Hl₀ Hl₁ v_rel) i j h_empty_i
    exact ⟨h_ind₁, ⟨h_1₁, h_2₁⟩⟩
  · intro ⟨h_ind₁, ⟨h_1₁, h_2₁⟩⟩
    have v_rels : ∀ (i : Fin t), (Hl₀ i).subgraph.verts = φ.symm.graph_iso '' (Hl₁ i).subgraph.verts := by
      intro i
      have ⟨v_rel, _⟩ := h_rel i
      rw [v_rel]
      ext v; simp
      constructor
      · intro h_v
        use v
        exact ⟨h_v, φ.graph_iso.left_inv v⟩
      · intro h_v
        obtain ⟨v', ⟨h_v', h_vv'⟩⟩ := h_v
        have : v = v' := by
          rw [←h_vv']
          exact φ.graph_iso.left_inv v'
        exact Set.mem_of_eq_of_mem this h_v'
    have e_rels : ∀ (i : Fin t), ∀ (u v : W), (Hl₁ i).subgraph.Adj u v ↔ (Hl₀ i).subgraph.Adj (φ.symm.graph_iso u) (φ.symm.graph_iso v) := by
      intro i u v
      have ⟨_, e_rel⟩ := h_rel i
      have h_u : φ.graph_iso (φ.symm.graph_iso u) = u := φ.symm.graph_iso.left_inv u
      have h_v : φ.graph_iso (φ.symm.graph_iso v) = v := φ.symm.graph_iso.left_inv v
      have := e_rel (φ.symm.graph_iso u) (φ.symm.graph_iso v)
      rw [h_u, h_v] at this
      exact this.symm
    have h_ind₀ : ∀ (i : Fin t), (Hl₀ i).IsInduced := by
      intro i
      have v_rel := v_rels i
      have e_rel := e_rels i
      dsimp [LabeledSubgraph.IsInduced]
      intro u v h_u h_v h_uv
      apply predIsoLabeledH_related_ind φ.symm (Hl₁ i) (Hl₀ i) v_rel e_rel (h_ind₁ i) h_u h_v h_uv
    have h_1₀ : ∀ (i : Fin t), Nonempty ((Hl₀ i).coe ≃f Hl i) := by
      intro i
      have v_rel' := v_rels i
      have e_rel' := e_rels i
      exact predIsoLabeledH_related_iso φ.symm (Hl i) (Hl₁ i) (Hl₀ i) v_rel' e_rel' (h_1₁ i)
    have h_2₀ : ∀ (i j : Fin t), i ≠ j → ((Hl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Hl₀ j).subgraph.verts \ G₀.type_verts) = ∅ := by
      intro i j h_ij
      exact predIsoLabeledHl_related_indep φ.symm Hl₁ Hl₀ v_rels i j (h_2₁ i j h_ij)
    exact ⟨h_ind₀, ⟨h_1₀, h_2₀⟩⟩

def inducedlabeledSubgraphList
    {σ : FlagType T} (G : LabeledGraph σ V)
    (Sl : ∀ (_ : Fin t), Set V)
    (hSl : ∀ i : Fin t, ∀ t : T, G.type_embed t ∈ Sl i)
    : {Gl' : ∀ (_ : Fin t), LabeledSubgraph σ G // ∀ i, (Gl' i).subgraph.IsInduced}
  := by
  let Gl' : ∀ (_ : Fin t), LabeledSubgraph σ G := fun i ↦
    inducedlabeledSubgraph G (Sl i) (hSl i)
  let h_ind : ∀ i : Fin t, (Gl' i).subgraph.IsInduced := by
    intro i
    dsimp [Gl']
    exact (inducedlabeledSubgraph G (Sl i) (hSl i)).2
  exact ⟨Gl', h_ind⟩

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma inducedlabeledSubgraphList_type_embed_mem
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    : ∀ (i : Fin t), ∀ (t : T), G₁.type_embed t ∈ ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts
  := by
  intro i
  exact inducedlabeledSubgraph_type_embed_mem φ (Hl₀ i)

omit [Fintype T] [DecidableEq T] [FintypeList Vl] [DecidableEqList Vl] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma inducedlabeledSubgraphList_related
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (h_ind₀ : ∀ i, (Hl₀ i).subgraph.IsInduced)
    : relOflabeledSubgraphList φ Hl₀
      (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ Hl₀))
  := by
  dsimp [relOflabeledSubgraphList, inducedlabeledSubgraphList, inducedlabeledSubgraph]
  simp
  intro i u v
  constructor
  · intro h_uv
    constructor
    · exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mpr (SimpleGraph.Subgraph.Adj.adj_sub h_uv)
    · exact ⟨(Hl₀ i).subgraph.edge_vert h_uv, (Hl₀ i).subgraph.edge_vert h_uv.symm⟩
  · intro ⟨h_G₁uv, ⟨h_G₀u, h_G₀v⟩⟩
    have h_G₀uv : G₀.graph.Adj u v := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_G₁uv
    apply (h_ind₀ i) h_G₀u h_G₀v h_G₀uv

omit [Fintype T] [DecidableEq T] [FintypeList Vl] [DecidableEqList Vl] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma Hl_eq_reverseinduced_induced_Hl
  {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
  (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀) (h_ind₀ : ∀ i, (Hl₀ i).subgraph.IsInduced)
  : Hl₀ = (inducedlabeledSubgraphList G₀ (fun i => φ.symm.graph_iso '' ((inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ Hl₀)).1 i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ.symm (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ Hl₀)).1)).1 := by
  funext i
  exact H_eq_reverseinduced_induced_H φ (Hl₀ i) (h_ind₀ i)

noncomputable def isoSetOfInducedlabeledSubgraphList
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : (∀ (_ : Fin t), LabeledSubgraph σ G₀) → Prop)
    (p₁ : (∀ (_ : Fin t), LabeledSubgraph σ G₁) → Prop)
    (h_rel : relOfPredOnlabeledSubgraphList φ p₀ p₁)
    (h_rel_inv : relOfPredOnlabeledSubgraphList φ.symm p₁ p₀)
    : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G₀ | (∀ (i : Fin t), (Gl i).IsInduced) ∧ p₀ Gl } ≃ { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G₁ | (∀ (i : Fin t), (Gl i).IsInduced) ∧ p₁ Gl }
  :=
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G₀ | (∀ (i : Fin t), (Gl i).IsInduced) ∧ p₀ Gl }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G₁ | (∀ (i : Fin t), (Gl i).IsInduced) ∧ p₁ Gl }
  let f : S₀ → S₁ := by
    intro s₀
    dsimp [S₀] at s₀
    let ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
    let Hl₁ := (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ Hl₀)).1
    let h_ind₁ : ∀ i, (Hl₁ i).subgraph.IsInduced := (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ Hl₀)).2
    have : relOflabeledSubgraphList φ Hl₀ Hl₁ := inducedlabeledSubgraphList_related φ Hl₀ h_ind₀
    have h_p₁ : p₁ Hl₁ := (h_rel Hl₀ Hl₁ this).mp h_p₀
    exact ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv : S₁ → S₀ := by
    intro s₁
    dsimp [S₁] at s₁
    let ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let Hl₀ := (inducedlabeledSubgraphList G₀ (fun i => φ.symm.graph_iso '' (Hl₁ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ.symm Hl₁)).1
    let h_ind₀ : ∀ i, (Hl₀ i).subgraph.IsInduced := (inducedlabeledSubgraphList G₀ (fun i => φ.symm.graph_iso '' (Hl₁ i).subgraph.verts) (inducedlabeledSubgraphList_type_embed_mem φ.symm Hl₁)).2
    have : relOflabeledSubgraphList φ.symm Hl₁ Hl₀ := inducedlabeledSubgraphList_related φ.symm Hl₁ h_ind₁
    have h_p₀ : p₀ Hl₀ := (h_rel_inv Hl₁ Hl₀ this).mp h_p₁
    exact ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv]
      simp;symm
      exact Hl_eq_reverseinduced_induced_Hl φ Hl₀ h_ind₀
    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv]
      simp; symm
      exact Hl_eq_reverseinduced_induced_Hl φ.symm Hl₁ h_ind₁
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedlabeledSubgraphListIsoHl
    {G : LabeledGraph σ V} {G' : LabeledGraph σ W} (φ : G ≃f G')
    (Hl : LabeledGraphList σ t Vl)
    : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) }
    ≃ { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G' | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G'.type_verts) ∩ ((Gl j).subgraph.verts \ G'.type_verts) = ∅) }
  := by
  let iso := isoSetOfInducedlabeledSubgraphList φ
    (predIsoLabeledHl G Hl)
    (predIsoLabeledHl G' Hl)
    (predIsoLabeledHl_related φ Hl)
    (predIsoLabeledHl_related φ.symm Hl)
  dsimp only [predIsoLabeledHl, relOfPredOnlabeledSubgraphList] at iso
  simp only [Set.coe_setOf]
  simp only [and_self_left] at iso
  exact iso

omit [DecidableEq T] in
lemma labeledSubgraphListDensity_respects_eqv_on_G
    (Hl : LabeledGraphList σ t Vl) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphListDensity Hl G = labeledSubgraphListDensity Hl G'
  := by
  dsimp [labeledSubgraphListDensity]
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G' | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G'.type_verts) ∩ ((Gl j).subgraph.verts \ G'.type_verts) = ∅) }
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedlabeledSubgraphListIsoHl φ Hl
  have h_count : labeledSubgraphListCount Hl G = labeledSubgraphListCount Hl G' := by
    dsimp only [labeledSubgraphListCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  rw [h_count]
  rfl

noncomputable def labeledSubgraphListDensityLifted
    (Hl : LabeledGraphList σ t Vl) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G => labeledSubgraphListDensity Hl G)
  intro _ _ h_eqv
  exact labeledSubgraphListDensity_respects_eqv_on_G Hl (Classical.choice h_eqv)

noncomputable def isoSetOfInducedlabeledSubgraph_eqv
    {Hl Hl' : LabeledGraphList σ t Vl} (φ : ∀ (i : Fin t), Hl i ≃f Hl' i)
    (G : LabeledGraph σ W)
    : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) } ≃
      { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl' i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) }
  := by
  let h : ∀ (G' : LabeledSubgraph σ G) (i : Fin t), Nonempty (G'.coe ≃f Hl i) ↔ Nonempty (G'.coe ≃f Hl' i) := by
    intro G' i
    constructor
    · intro h_iso₀
      let h_iso₀ := Classical.choice h_iso₀
      let h_iso₁ : G'.coe ≃f (Hl' i) := h_iso₀.trans (φ i)
      exact Nonempty.intro h_iso₁
    · intro h_iso₁
      let h_iso₁ := Classical.choice h_iso₁
      let h_iso₀ : G'.coe ≃f (Hl i) := h_iso₁.trans (φ i).symm
      exact Nonempty.intro h_iso₀
  have : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) } = { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl' i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) } :=
    Set.sep_ext_iff.mpr (fun x _ ↦
      Iff.intro
        (fun ⟨h_iso, h_indep⟩ ↦ ⟨fun i ↦ (h (x i) i).mp (h_iso i) , h_indep⟩)
        (fun ⟨h_iso, h_indep⟩ ↦ ⟨fun i ↦ (h (x i) i).mpr (h_iso i) , h_indep⟩))
  exact Equiv.setCongr this

omit [DecidableEq T] in
lemma labeledSubgraphListDensityLifted_respects_eqv
    (Hl Hl' : LabeledGraphList σ t Vl) (φ : ∀ (i : Fin t), Hl i ≃f Hl' i) (G : Flag σ W)
    : labeledSubgraphListDensityLifted Hl G = labeledSubgraphListDensityLifted Hl' G
  := by
  dsimp [labeledSubgraphListDensityLifted, labeledSubgraphListDensity]
  congr
  ext Grep
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ Grep | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ Grep.type_verts) ∩ ((Gl j).subgraph.verts \ Grep.type_verts) = ∅) }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ Grep | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl' i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ Grep.type_verts) ∩ ((Gl j).subgraph.verts \ Grep.type_verts) = ∅) }
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedlabeledSubgraph_eqv φ Grep
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  have h_count : labeledSubgraphListCount Hl Grep = labeledSubgraphListCount Hl' Grep := by
    dsimp only [labeledSubgraphListCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  rw [h_count]; rfl

noncomputable def quotLabeledSubgraphListDensity
    : QuotLabeledGraphList σ t Vl → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphListDensityLifted
  intro Hl Hl' Hl_eqv
  ext G
  have φ : ∀ (i : Fin t), Hl i ≃f Hl' i := by
    intro i
    exact Classical.choice (Hl_eqv i)
  exact labeledSubgraphListDensityLifted_respects_eqv Hl Hl' φ G

omit [DecidableEq T] in
lemma quotLabeledSubgraphListDensity_respects_eqv
    (Hl Hl' : LabeledGraphList σ t Vl) (h : Hl ∼fl Hl') (G : Flag σ W)
    : quotLabeledSubgraphListDensity ⟦Hl⟧ G = quotLabeledSubgraphListDensity ⟦Hl'⟧ G
  := by
  apply labeledSubgraphListDensityLifted_respects_eqv
  intro i
  exact Classical.choice (h i)

noncomputable def flagListDensity
    : FlagList σ t Vl → Flag σ W → ℚ
  :=
  fun Fl => quotLabeledSubgraphListDensity Fl.coe

omit [DecidableEq T] in
theorem flagListDensity_HEq_eq
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_HEq : HEq Fl Fl') (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity Fl' G
  := by
  subst h_Vl_eq
  have h_Fl_eq : Fl = Fl' := by simp_all only [heq_eq_eq]
  subst h_Fl_eq
  dsimp [flagListDensity, quotLabeledSubgraphListDensity, eqv_QuotLabeledGraphList_FlagList]
  dsimp [labeledSubgraphListDensityLifted, labeledSubgraphListDensity]
  congr!

omit [DecidableEq T] in
theorem subflagDensity_eq_flagListDensity
    {σ : FlagType T} (F : Flag σ U) (G : Flag σ W)
    : subflagDensity F G = flagListDensity (flagToList F) G
  := by
  rcases Quotient.exists_rep F with ⟨Frep, hFrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  have h_count : labeledSubgraphCount Frep Grep = labeledSubgraphListCount (fun (_ : Fin 1) => Frep) Grep := by
    dsimp [labeledSubgraphCount, labeledSubgraphListCount]
    apply Finset.card_bij
    · intro H hH
      simp at hH
      show (fun (_ : Fin 1) => H) ∈ _
      simp [Set.toFinset_setOf, labeledSubgraphListSet]
      constructor
      · exact hH.1
      · constructor
        · exact hH.2
        · intro i j hij
          have : i = j := by
            rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
          contradiction
    · intro H _ H' _ h_eq
      calc
        H = (fun (_ : Fin 1) => H) 0 := by simp
        _ = (fun (_ : Fin 1) => H') 0 := by rw [h_eq]
        _ = H' := by simp
    · intro Hl _
      use Hl 0
      simp_all [labeledSubgraphListSet]
      ext1 i
      rw [Fin.fin_one_eq_zero i]
  calc
    subflagDensity F G = labeledSubgraphDensity Frep Grep := by
      subst hFrep hGrep
      rfl
    _ = labeledSubgraphListDensity (fun (_ : Fin 1) => Frep) Grep := by
      dsimp [labeledSubgraphDensity, labeledSubgraphListDensity]
      rw [← h_count]
      congr
      dsimp [multinomialCoefficient]
      rw [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Finset.prod_singleton]
      split
      · rw [Nat.choose_eq_factorial_div_factorial (by assumption)]
      · rw [Nat.choose_eq_zero_of_lt (by linarith)]
    _ = quotLabeledSubgraphListDensity [F]ᶠ.coe G := by
      have : [F]ᶠ.coe = ⟦fun (_ : Fin 1) => Frep⟧ := by
        dsimp [eqv_QuotLabeledGraphList_FlagList]
        apply Quotient.sound
        intro i
        simp [flagToList, ← hFrep]
        apply Quotient.mk_out Frep
      rw [this, ← hGrep]
      rfl
    _ = flagListDensity [F]ᶠ G := rfl

noncomputable def flagDensity₁ (F : Flag σ U) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F]ᶠ G

noncomputable def flagDensity₂ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂]ᶠ G

noncomputable def flagDensity₃ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (F₃ : Flag σ U₃) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂, F₃]ᶠ G

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagListDensity
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity Fl G = flagListDensity (QuotLabeledGraphList.coe ⟦Fl⟧) ⟦G⟧
  := by
  show quotLabeledSubgraphListDensity ⟦Fl⟧ ⟦G⟧ = flagListDensity (QuotLabeledGraphList.coe ⟦Fl⟧) ⟦G⟧
  dsimp [flagListDensity, eqv_QuotLabeledGraphList_FlagList]
  apply quotLabeledSubgraphListDensity_respects_eqv
  calc
    Fl ∼fl (fun i => ⟦Fl⟧.out i) := (Quotient.mk_out Fl).symm
    _ ∼fl (fun i => ⟦⟦Fl⟧.out i⟧.out) := by
      dsimp [flagListEqv]
      intro i
      exact (Quotient.mk_out (⟦Fl⟧.out i)).symm

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagDensity₁
    (F : LabeledGraph σ U) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity [F]ᵍ G = flagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  rw [labeledSubgraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_singleton]
  simp [flagDensity₁]

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagDensity₂
    (F₁ : LabeledGraph σ U₁) (F₂ : LabeledGraph σ U₂) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity [F₁, F₂]ᵍ G = flagDensity₂ ⟦F₁⟧ ⟦F₂⟧ ⟦G⟧
  := by
  rw [labeledSubgraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_pair]
  simp [flagDensity₂]

theorem flagDensity_empty
    (F : Flag σ W) : flagDensity₁ (emptyFlag σ) F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity (emptyFlag σ) F]
  exact subflagDensity_empty F

omit [DecidableEq T] in
theorem flagDensity_self
    (F : Flag σ W) : flagDensity₁ F F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F]
  exact subflagDensity_self F

omit [DecidableEq T] in
theorem flagDensity_other
    {F F' : Flag σ W} (h_neq : F ≠ F') : flagDensity₁ F F' = 0
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F']
  apply  subflagDensity_other h_neq

omit [DecidableEq T] in
theorem flagDensity_permute
    (Fl : FlagList σ t Vl) (G : Flag σ W) (π : Perm t)
    : flagListDensity Fl G = flagListDensity (Fl.permute π) G
  := by
  dsimp [flagListDensity, quotLabeledSubgraphListDensity]
  congr; ext Grep
  dsimp [labeledSubgraphListCount]
  let S₀ := labeledSubgraphListSet (fun i => Quotient.out (Fl i)) Grep
  let S₁ := labeledSubgraphListSet (fun i => Quotient.out (Fl (π i))) Grep
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    dsimp [S₀, S₁]
    let f : S₀ → S₁ := by
      intro s₀
      dsimp [S₀, labeledSubgraphListSet] at s₀
      let ⟨Hl₀, h_ind₀, h_p₀⟩ := s₀
      let Hl₁ : Fin t → LabeledSubgraph σ Grep := by
        intro i
        exact Hl₀ (π i)
      let h_ind₁ : ∀ (i : Fin t), (Hl₁ i).subgraph.IsInduced := by
        intro i
        exact @h_ind₀ (π i)
      let h_p₁ : (∀ (i : Fin t), Nonempty ((Hl₁ i).coe ≃f Quotient.out (Fl (π i)))) ∧
                  ∀ (i j : Fin t), ¬i = j → (Hl₁ i).subgraph.verts \ Grep.type_verts ∩ ((Hl₁ j).subgraph.verts \ Grep.type_verts) = ∅ := by
        simp_all only [implies_true, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, and_self]
      exact ⟨Hl₁, h_ind₁, h_p₁⟩
    have h_inj_f : Function.Injective f := by
      intro s₀ s₁ h_eq
      simp [f] at h_eq
      obtain ⟨Hl₀, h_ind₀, h_p₀⟩ := s₀
      obtain ⟨Hl₁, h_ind₁, h_p₁⟩ := s₁
      simp_all only [Subtype.mk.injEq]
      funext i
      have : Hl₀ (π (π.invFun i)) = Hl₁ (π (π.invFun i)) := congrFun h_eq (π.invFun i)
      simp_all only [Equiv.invFun_as_coe, Equiv.apply_symm_apply]
    have h_surj_f : Function.Surjective f := by
      intro s₂
      obtain ⟨Hl₂, h_ind₂, h_p₂⟩ := s₂
      let Hl₀ : Fin t → LabeledSubgraph σ Grep := by
        intro i
        exact Hl₂ (π.invFun i)
      let h_ind₀ : ∀ (i : Fin t), (Hl₀ i).subgraph.IsInduced := by
        intro i
        exact @h_ind₂ (π.invFun i)
      let h_p₀ : (∀ (i : Fin t), Nonempty ((Hl₀ i).coe ≃f Quotient.out (Fl i))) ∧ ∀ (i j : Fin t), ¬i = j → (Hl₀ i).subgraph.verts \ Grep.type_verts ∩ ((Hl₀ j).subgraph.verts \ Grep.type_verts) = ∅ := by
        constructor
        · intro i
          dsimp [Hl₀]
          have : Nonempty ((Hl₀ i).coe ≃f Quotient.out (Fl i)) := by
            have h_eq : π (π.invFun i) = i := by apply Equiv.apply_symm_apply
            have : Nonempty ((Hl₂ (π.invFun i)).coe ≃f Quotient.out (Fl (π (π.invFun i)))) := h_p₂.1 (π.invFun i)
            rw [h_eq] at this
            exact this
          exact this
        · intro i j h_ij
          simp_all only [ne_eq, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true]
      use ⟨Hl₀, h_ind₀, h_p₀⟩
      dsimp [f]
      simp_all only [Equiv.invFun_as_coe, Equiv.symm_apply_apply, Hl₀]
    exact Equiv.ofBijective f ⟨h_inj_f, h_surj_f⟩
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  have h_count : labeledSubgraphListCount (fun i => Quotient.out (Fl.permute π i)) Grep = labeledSubgraphListCount (fun i => Quotient.out (Fl i)) Grep := by
    dsimp only [labeledSubgraphListCount]
    show S₁.toFinset.card = S₀.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  have h_coeff : multinomialCoefficient (fun i ↦ (Quotient.out (Fl i)).size - σ.size) (Grep.size - σ.size) = multinomialCoefficient (fun i ↦ (Quotient.out (Fl.permute π i)).size - σ.size) (Grep.size - σ.size) := by
    dsimp [multinomialCoefficient]; simp
    have sum_sizes_perm_eq : ∑ i : Fin t, ((Quotient.out (Fl i)).size - σ.size) = ∑ i : Fin t, ((Quotient.out (Fl.permute π i)).size - σ.size) := by
      apply Finset.sum_bij (fun i _ => π.invFun i) (by simp) (by simp)
      · intro i _
        use π i
        simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply, Finset.mem_univ, exists_const]
      · intro i _
        have : i = π (π.invFun i) := (Equiv.symm_apply_eq π).mp rfl
        dsimp [FlagList.permute]
        have : (Quotient.out (Fl i)).size = (Quotient.out (Fl.permute π (π.invFun i))).size := by
          have h_Fl_size_eq : ∀ (j : Fin t), (Quotient.out (Fl.permute π j)).size = (Quotient.out (Fl (π j))).size := by
            intro j
            rfl
          rw [h_Fl_size_eq (π.invFun i), ← this]
        rw [this]; rfl
    have prod_factorials_perm_eq : ∏ i : Fin t, ((Quotient.out (Fl i)).size - σ.size).factorial = ∏ i : Fin t, ((Quotient.out (Fl.permute π i)).size - σ.size).factorial := by
      apply Finset.prod_bij (fun i _ => π.invFun i) (by simp) (by simp)
      · intro i _
        use π i
        simp_all only [Finset.mem_univ, Equiv.invFun_as_coe, Equiv.symm_apply_apply, exists_const]
      · intro i _
        have : i = π (π.invFun i) := (Equiv.symm_apply_eq π).mp rfl
        have : (Quotient.out (Fl i)).size = (Quotient.out (Fl.permute π (π.invFun i))).size := by
          have h_Fl_size_eq : ∀ (j : Fin t), (Quotient.out (Fl.permute π j)).size = (Quotient.out (Fl (π j))).size := by
            intro j
            rfl
          rw [h_Fl_size_eq (π.invFun i), ← this]
        rw [this]
    rw [sum_sizes_perm_eq, prod_factorials_perm_eq]
  dsimp [labeledSubgraphListDensity]
  rw [h_count, h_coeff]

instance {V W : Type} [Fintype V] [Fintype W]
    : FintypeList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance {V W : Type} [DecidableEq V] [DecidableEq W]
    : DecidableEqList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance {V W U : Type} [Fintype V] [Fintype W] [Fintype U]
    : FintypeList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

instance {V W U : Type} [DecidableEq V] [DecidableEq W] [DecidableEq U]
    : DecidableEqList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

omit [DecidableEq T] in
theorem flagPairDensity_comm
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₂ F₁ F₂ G = flagDensity₂ F₂ F₁ G
  := by
  let Fl₁ := [F₁, F₂]ᶠ
  let Fl₂ := [F₂, F₁]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  let π : Perm 2 := by
    let f : Fin 2 → Fin 2 := fun i => match i with | 0 => 1 | 1 => 0
    refine ⟨f, f, ?_, ?_⟩
    · intro i; match i with | 0 => simp | 1 => simp
    · intro i; match i with | 0 => simp | 1 => simp
  rw [flagDensity_permute Fl₁ G π]
  have h_Vl_eq : (fun (i : Fin 2) => match i with | 0 => U₂ | 1 => U₁)
      = (listTypePermute (fun (i : Fin 2) => match i with | 0 => U₁ | 1 => U₂) π) := by
    ext i; split <;> rfl
  have h_Fl_eq : ∀ (i : Fin 2), (Fl₁.permute π) i = cast (Flag.type_eq h_Vl_eq i) (Fl₂ i) := by
    intro i
    split <;> (simp_all only [cast_eq, π, Fl₁, Fl₂]; rfl)
  refine flagListDensity_HEq_eq h_Vl_eq ?_ G
  exact flagList_HEq h_Vl_eq h_Fl_eq

omit [DecidableEq T] in
theorem flagTripleDensity_comm
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (F₃ : Flag σ U₃) (G : Flag σ W)
    : flagDensity₃ F₁ F₂ F₃ G = flagDensity₃ F₂ F₃ F₁ G
  := by
  let Fl₁ := [F₁, F₂, F₃]ᶠ
  let Fl₂ := [F₂, F₃, F₁]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  let π : Perm 3 := by
    let f : Fin 3 → Fin 3 := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
    let f_inv : Fin 3 → Fin 3 := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
    refine ⟨f, f_inv, ?_, ?_⟩
    · intro i; match i with | 0 => simp | 1 => simp | 2 => simp
    · intro i; match i with | 0 => simp | 1 => simp | 2 => simp
  rw [flagDensity_permute Fl₁ G π]
  have h_Vl_eq : (fun (i : Fin 3) => match i with | 0 => U₂ | 1 => U₃ | 2 => U₁)
      = (listTypePermute (fun (i : Fin 3) => match i with | 0 => U₁ | 1 => U₂ | 2 => U₃) π) := by
    ext i; split <;> rfl
  have h_Fl_eq : ∀ (i : Fin 3), (Fl₁.permute π) i = cast (Flag.type_eq h_Vl_eq i) (Fl₂ i) := by
    intro i
    split <;> (simp_all only [cast_eq, π, Fl₁, Fl₂]; rfl)
  refine flagListDensity_HEq_eq h_Vl_eq ?_ G
  exact flagList_HEq h_Vl_eq h_Fl_eq

theorem flagDensity_insert_empty
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity (Fl.insert (emptyFlag σ)) G
  := by
  dsimp [flagListDensity, quotLabeledSubgraphListDensity]
  congr; ext Grep
  let S₀ := labeledSubgraphListSet (fun i => Quotient.out (Fl i)) Grep
  let S₁ := labeledSubgraphListSet (fun i => Quotient.out (Fl.insert (emptyFlag σ) i)) Grep
  let h_S₀ : Fintype S₀ := Fintype.ofFinite S₀
  let h_S₁ : Fintype S₁ := Fintype.ofFinite S₁
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    dsimp [S₀, S₁]
    let f : S₀ → S₁ := by
      intro s₀
      dsimp [S₀, labeledSubgraphListSet] at s₀
      let ⟨Hl₀, h_ind₀, h_p₀⟩ := s₀
      let Hl₁ : Fin (t + 1) → LabeledSubgraph σ Grep := by
        intro i
        if h : i.val < t then
          exact Hl₀ ⟨i.val, h⟩
        else
          exact Grep.bottom
      let h_ind₁ : ∀ (i : Fin (t + 1)), (Hl₁ i).subgraph.IsInduced := by
        intro i
        dsimp [Hl₁]
        split
        next hi =>
          exact h_ind₀ ⟨i, hi⟩
        next _ =>
          exact Grep.bottom_isInduced
      let h_p₁ : (∀ (i : Fin (t + 1)), Nonempty ((Hl₁ i).coe ≃f Quotient.out (Fl.insert (emptyFlag σ) i))) ∧
                  ∀ (i j : Fin (t + 1)), i ≠ j → (Hl₁ i).subgraph.verts \ Grep.type_verts ∩ ((Hl₁ j).subgraph.verts \ Grep.type_verts) = ∅ := by
        constructor
        · intro i
          apply Nonempty.intro; symm
          dsimp [FlagList.insert]
          split
          next hi =>
            dsimp [Hl₁]
            have empty_equiv := (@labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph T σ W Grep Grep.bottom).1
            simp only [true_implies] at empty_equiv
            have empty_iso := Classical.choice empty_equiv.2
            have h_Hl₁ : (if h : ↑i < t then Hl₀ ⟨↑i, h⟩ else Grep.bottom) = Grep.bottom := by
              simp_all only [lt_self_iff_false, ↓reduceDIte]
            rw [h_Hl₁]
            have insert_iso := (Classical.choice (insert_new_flag_cast_iso Fl (emptyFlag σ) hi)).symm
            have quotient_iso : Quotient.out (emptyFlag σ) ≃f emptyLabeledGraph σ := Classical.choice (Quotient.mk_out (emptyLabeledGraph σ))
            exact (insert_iso.trans quotient_iso).trans empty_iso.symm
          next hi =>
            have hi_lt : i.val < t := by
              have := i.isLt
              rw [← Nat.succ_le_iff] at this
              simp at this
              exact Nat.lt_of_le_of_ne this hi
            let i' : Fin t := ⟨i.val, hi_lt⟩
            dsimp [Hl₁]
            have h_Hl₁ :  (if h : ↑i < t then Hl₀ ⟨↑i, h⟩ else Grep.bottom) = Hl₀ ⟨↑i, hi_lt⟩ := by
              simp [hi_lt]
            rw [h_Hl₁]
            have iso_from_existing := Classical.choice (h_p₀.1 i')
            dsimp [i'] at iso_from_existing
            have perserv_iso := Classical.choice (insert_preserves_existing_flags Fl (emptyFlag σ) hi)
            exact (iso_from_existing.trans perserv_iso).symm
        · intro i j h_ij
          dsimp [Hl₁]
          split <;> split
          next h1 h2 =>
            let i' : Fin t := ⟨i, h1⟩
            let j' : Fin t := ⟨j, h2⟩
            have h_ij' : i' ≠ j' := by
              dsimp [i', j']
              intro h_eq
              have h_val_eq : i.val = j.val := by
                simp_all only [Fin.mk.injEq]
              have h_fin_eq : i = j := Fin.ext h_val_eq
              exact h_ij h_fin_eq
            exact h_p₀.2 i' j' h_ij'
          next h1 h2 =>
            ext x
            simp_all only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_false_eq_true, and_true, and_imp]
            intro _ hx
            exact hx
          next h1 h2 =>
            rw [Set.inter_comm]
            ext x
            simp_all only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_false_eq_true, and_true, and_imp]
            intro _ hx
            exact hx
          next h1 h2 =>
            ext x
            simp_all only [Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, Decidable.not_not]
            simp only [Set.inter_self, Set.mem_diff, not_and]
            exact fun x hx ↦ hx x
      exact ⟨Hl₁, h_ind₁, h_p₁⟩
    let f_inv : S₁ → S₀ := by
      intro s₁
      dsimp [S₁, labeledSubgraphListSet] at s₁
      let ⟨Hl₁, h_ind₁, h_p₁⟩ := s₁
      let Hl₀ : Fin t → LabeledSubgraph σ Grep := by
        intro i
        exact Hl₁ i
      let h_ind₀ : ∀ (i : Fin t), (Hl₀ i).subgraph.IsInduced := by
        intro i
        exact h_ind₁ i
      let h_p₀ : (∀ (i : Fin t), Nonempty ((Hl₀ i).coe ≃f Quotient.out (Fl i))) ∧
                  ∀ (i j : Fin t), i ≠ j → (Hl₀ i).subgraph.verts \ Grep.type_verts ∩ ((Hl₀ j).subgraph.verts \ Grep.type_verts) = ∅ := by
        constructor
        · intro i
          have hi : i.val ≠ t := i.isLt.ne
          apply Nonempty.intro
          dsimp [Hl₀]
          let h_iso := Classical.choice (h_p₁.1 i)
          have h_iso' := (Classical.choice (insert_preserves_existing_flags_coe Fl (emptyFlag σ) hi)).symm
          exact h_iso.trans h_iso'
        · intro i j a
          simp_all only [Fin.coe_eq_castSucc, Fin.castSucc_inj, not_false_eq_true]
      exact ⟨Hl₀, h_ind₀, h_p₀⟩
    let f_bij : Function.Bijective f := by
      have h_leftinv : Function.LeftInverse f_inv f := by
        rintro ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩
        dsimp [f, f_inv]
        simp only [Subtype.mk.injEq]
        funext i
        split
        next hi =>
          have : i % (t + 1) = i := by
            simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
            exact Nat.lt_succ_of_lt i.isLt
          have fin_eq : ⟨↑i % (t + 1), hi⟩ = i := by
            apply Fin.ext
            exact this
          rw [fin_eq]
        next hi =>
          simp_all only [ne_eq, not_lt]
          have : i % (t + 1) = i := by
            simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
            exact Nat.lt_add_right 1 i.isLt
          rw [this] at hi
          exact absurd i.isLt (not_lt.mpr hi)
      have h_rightinv : Function.RightInverse f_inv f := by
        rintro ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
        dsimp [f, f_inv]
        simp only [Subtype.mk.injEq]
        funext i
        split
        next _ =>
          simp_all only [Fin.cast_val_eq_self]
        next hi =>
          have hi : ↑i = t := Nat.eq_of_lt_succ_of_not_lt i.isLt hi
          have iso_exist := Classical.choice (h_p₁.1 i)
          dsimp [FlagList.insert] at iso_exist
          have h_Fl : (if hi : ↑i = t then cast (flag_listTypeInsert_eq hi) (emptyFlag σ) else cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi))) = cast (flag_listTypeInsert_eq hi) (emptyFlag σ) := by
            simp_all only [↓reduceDIte]
          rw [h_Fl] at iso_exist
          have Hl₁_iso : Quotient.out (emptyFlag σ) ≃f (Hl₁ i).coe := (iso_exist.trans (Classical.choice (insert_new_flag_cast_iso Fl (emptyFlag σ) hi)).symm).symm
          have quotient_iso : Quotient.out (emptyFlag σ) ≃f emptyLabeledGraph σ := Classical.choice (Quotient.mk_out (emptyLabeledGraph σ))
          have h_iso := Hl₁_iso.symm.trans quotient_iso
          symm; apply (@labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph T σ W Grep (Hl₁ i)).2 ⟨h_ind₁ i, Nonempty.intro h_iso⟩
      exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
    exact Equiv.ofBijective f f_bij
  dsimp [labeledSubgraphListDensity]
  let h_count : labeledSubgraphListCount (fun i => Quotient.out (Fl.insert (emptyFlag σ) i)) Grep = labeledSubgraphListCount (fun i => Quotient.out (Fl i)) Grep := by
    dsimp only [labeledSubgraphListCount]
    show S₁.toFinset.card = S₀.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card]
  have h_coeff : multinomialCoefficient (fun i ↦ (Quotient.out (Fl i)).size - σ.size) (Grep.size - σ.size) = multinomialCoefficient (fun i ↦ (Quotient.out (Fl.insert (emptyFlag σ) i)).size - σ.size) (Grep.size - σ.size) := by
    dsimp [multinomialCoefficient]; simp
    have sum_sizes_perm_eq : ∑ i : Fin t, ((Quotient.out (Fl i)).size - σ.size) = ∑ i : Fin (t + 1), ((Quotient.out (Fl.insert (emptyFlag σ) i)).size - σ.size) := by
      symm
      rw [Finset.sum_fin_eq_sum_range]
      rw [Finset.sum_range_succ]
      have sum_insert_empty_eq_original : (∑ x ∈ Finset.range t, if h : x < t + 1 then (Quotient.out (Fl.insert (emptyFlag σ) ⟨x, h⟩)).size - σ.size else 0) = ∑ x ∈ Finset.range t, if h : x < t then (Quotient.out (Fl ⟨x, h⟩)).size - σ.size else 0 := by
        apply Finset.sum_bij (fun i _ => if _ : i < t then i else 0)
        · intro i hi
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi j hj h
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi
          use i
          use hi
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi
          split
          next hi_1 h =>
            let h' : (if _ : i < t then i else 0) = i := by
              simp_all only [Finset.mem_range, ↓reduceDIte]
            rw [h']
            split
            · let i : Fin (t + 1) := ⟨i, h⟩
              have hi : i.val ≠ t := by
                simp_all only [Finset.mem_range, ne_eq]
                apply Aesop.BuiltinRules.not_intro
                intro a
                subst a
                simp_all only [lt_self_iff_false]
              have := cast_preserves_flag_size' Fl (emptyFlag σ) hi
              congr!
              exact id (Eq.symm this)
            · have : i < t := by
                simp_all only [not_lt]
                split at h'
                next h_2 => simp_all only [Finset.mem_range]
                next h_2 =>
                  subst h'
                  simp_all only [Finset.mem_range]
              simp_all only [not_true_eq_false]
          next hi_1 h =>
            simp_all only [Finset.mem_range, not_lt]
            have hi' : t < i := by
              simp_all only [Finset.mem_range]
              exact h
            exact False.elim (lt_asymm hi hi')
      split
      next h1 =>
        rw [Finset.sum_fin_eq_sum_range, sum_insert_empty_eq_original, add_right_eq_self]
        dsimp [FlagList.insert, emptyFlag, emptyLabeledGraph]
        split
        next h2 =>
          let i : Fin (t + 1) := ⟨t, h1⟩
          have hi : i.val = t := h2
          exact Eq.symm (Nat.eq_sub_of_add_eq' (cast_preserves_flag_size Fl (emptyFlag σ) hi))
        next h2 =>
          exact False.elim (h2 rfl)
      next h1 =>
        rw [add_zero]
        rw [Finset.sum_fin_eq_sum_range, sum_insert_empty_eq_original]
    have prod_factorials_perm_eq : ∏ i : Fin t, ((Quotient.out (Fl i)).size - σ.size).factorial = ∏ i : Fin (t + 1), ((Quotient.out (Fl.insert (emptyFlag σ) i)).size - σ.size).factorial := by
      symm
      rw [Finset.prod_fin_eq_prod_range]
      rw [Finset.prod_range_succ]
      have prod_insert_empty_eq_original : (∏ x ∈ Finset.range t, if h : x < t + 1 then ((Quotient.out (Fl.insert (emptyFlag σ) ⟨x, h⟩)).size - σ.size).factorial else 1) = ∏ x ∈ Finset.range t, if h : x < t then ((Quotient.out (Fl ⟨x, h⟩)).size - σ.size).factorial else 1 := by
        apply Finset.prod_bij (fun i _ => if _ : i < t then i else 0)
        · intro i hi
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi j hj h
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi
          use i
          use hi
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi
          split
          next hi_1 h =>
            let h' : (if _ : i < t then i else 0) = i := by
              simp_all only [Finset.mem_range, ↓reduceDIte]
            rw [h']
            split
            · let i : Fin (t + 1) := ⟨i, h⟩
              have hi : i.val ≠ t := by
                simp_all only [Finset.mem_range, ne_eq]
                apply Aesop.BuiltinRules.not_intro
                intro a
                subst a
                simp_all only [lt_self_iff_false]
              have := cast_preserves_flag_size' Fl (emptyFlag σ) hi
              congr!
              exact id (Eq.symm this)
            · have : i < t := by
                simp_all only [not_lt]
                split at h'
                next h_2 => simp_all only [Finset.mem_range]
                next h_2 =>
                  subst h'
                  simp_all only [Finset.mem_range]
              simp_all only [not_true_eq_false]
          next hi_1 h =>
            simp_all only [Finset.mem_range, not_lt]
            have hi' : t < i := by
              simp_all only [Finset.mem_range]
              exact h
            exact False.elim (lt_asymm hi hi')
      split
      next h1 =>
        rw [Finset.prod_fin_eq_prod_range, prod_insert_empty_eq_original]
        dsimp [FlagList.insert]
        split
        next h2 =>
          let i : Fin (t + 1) := ⟨t, h1⟩
          have hi : i.val = t := h2
          simp only [eq_comm]
          rw [← cast_preserves_flag_size Fl (emptyFlag σ) hi]
          have h_empty_size : (Quotient.out (emptyFlag σ)).size = σ.size := by
            simp [emptyFlag, LabeledGraph.size]
            exact rfl
          rw [h_empty_size]
          simp_all only [le_refl, tsub_eq_zero_of_le, Nat.factorial_zero, mul_one]
        next h2 =>
          exact False.elim (h2 rfl)
      next h1 =>
        rw [mul_one]
        rw [Finset.prod_fin_eq_prod_range, prod_insert_empty_eq_original]
    rw [sum_sizes_perm_eq, prod_factorials_perm_eq]
  rw [h_count, h_coeff]

theorem flagPairDensity_empty
    (F : Flag σ U) (G : Flag σ W)
    : flagDensity₂ (emptyFlag σ) F G = flagDensity₁ F G
  := by
  rw [flagPairDensity_comm]
  let Fl₁ := [F, emptyFlag σ]ᶠ
  let Fl₂ := [F]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  have h_insert : flagListDensity (Fl₂.insert (emptyFlag σ)) G = flagListDensity Fl₁ G := by
    have h_Vl_eq : (fun (i : Fin 2) => match i with | 0 => U | 1 => T) = (listTypeInsert (fun _ => U) T)
      := by
      ext i; split <;> rfl
    have h_Fl_eq : ∀ (i : Fin 2), (Fl₂.insert (emptyFlag σ)) i = cast (Flag.type_eq h_Vl_eq i) (Fl₁ i)
      := by
      intro i
      split <;> (simp_all only [cast_eq, Fl₁, Fl₂]; rfl)
    refine flagListDensity_HEq_eq h_Vl_eq ?_ G
    exact flagList_HEq h_Vl_eq h_Fl_eq
  rw [← h_insert]
  exact (flagDensity_insert_empty Fl₂ G).symm

theorem flagPairDensity_empty'
    (F : Flag σ U) (G : Flag σ W)
    : flagDensity₂ F (emptyFlag σ) G = flagDensity₁ F G
  := by
  rw [flagPairDensity_comm]
  exact flagPairDensity_empty F G

theorem flagTripleDensity_empty
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₃ (emptyFlag σ) F₁ F₂ G = flagDensity₂ F₁ F₂ G
  := by
  rw [flagTripleDensity_comm]
  let Fl₁ := [F₁, F₂, emptyFlag σ]ᶠ
  let Fl₂ := [F₁, F₂]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  have h_insert : flagListDensity (Fl₂.insert (emptyFlag σ)) G = flagListDensity Fl₁ G := by
    have h_Vl_eq : (fun (i : Fin 3) => match i with | 0 => U₁ | 1 => U₂ | 2 => T)
        = (listTypeInsert (fun (i : Fin 2) => match i with | 0 => U₁ | 1 => U₂) T)
      := by
      ext i; split <;> rfl
    have h_Fl_eq : ∀ (i : Fin 3), (Fl₂.insert (emptyFlag σ)) i = cast (Flag.type_eq h_Vl_eq i) (Fl₁ i)
      := by
      intro i
      split <;> (simp_all only [cast_eq, Fl₁, Fl₂]; rfl)
    refine flagListDensity_HEq_eq h_Vl_eq ?_ G
    exact flagList_HEq h_Vl_eq h_Fl_eq
  rw [← h_insert]
  exact (flagDensity_insert_empty Fl₂ G).symm

theorem flagTripleDensity_empty'
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₃ F₁ F₂ (emptyFlag σ) G = flagDensity₂ F₁ F₂ G
  := by
  rw [← flagTripleDensity_comm]
  exact flagTripleDensity_empty F₁ F₂ G

/- Chain rules -/

variable {ℓ₀ : ℕ} {σ : FlagType (Fin ℓ₀)}

theorem flagTripleDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (F₃ : Flag σ (Fin ℓ₃)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : flagDensity₃ F₁ F₂ F₃ G = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ F₁ F₂ G' * flagDensity₂ G' F₃ G
  := by
  sorry

theorem flagPairDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' ≤ ℓ)
    : flagDensity₂ F₁ F₂ G
      = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ F₁ F₂ G' * flagDensity₁ G' G
  := by
  rw [← flagTripleDensity_empty', flagTripleDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty']

theorem flagPairDensity_eq_sum_density_prods'
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ' : ℓ₁ ≤ ℓ') (hℓ : ℓ' + ℓ₂ ≤ ℓ + ℓ₀)
    : flagDensity₂ F₁ F₂ G
      = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₁ F₁ G' * flagDensity₂ G' F₂ G
  := by
  rw [← flagTripleDensity_empty, flagTripleDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty]

theorem flagDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ' : ℓ₁ ≤ ℓ') (hℓ : ℓ' ≤ ℓ)
    : flagDensity₁ F₁ G = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₁ F₁ G' * flagDensity₁ G' G
  := by
  rw [← flagPairDensity_empty, flagPairDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty]

alias density_chain_rule₁₁ := flagDensity_eq_sum_density_prods
alias density_chain_rule₁₂ := flagPairDensity_eq_sum_density_prods'
alias density_chain_rule₂₁ := flagPairDensity_eq_sum_density_prods
alias density_chain_rule₂₂ := flagTripleDensity_eq_sum_density_prods
