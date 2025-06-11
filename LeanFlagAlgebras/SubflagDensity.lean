import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

open FlagAlgebras

variable {T : Type} [FintypeExist T] [DecidableEqExist T] {σ : FlagType T}

section

variable {V W U: Type}
  [FintypeExist V] [DecidableEqExist V]
  [FintypeExist W] [DecidableEqExist W]
  [FintypeExist U] [DecidableEqExist U]

noncomputable def labeledSubgraphCount
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℕ
  :=
  let p (G' : LabeledSubgraph σ G) : Prop := G'.IsInduced ∧ Nonempty (G'.coe ≃f H)
  let S := { G' : LabeledSubgraph σ G | p G' }
  have : FintypeExist S := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S) }
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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist  W] [DecidableEqExist W] [FintypeExist U] [DecidableEqExist U] in
lemma predIsolabeledH_related_support
  {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
  (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁)
  (h_vert : H₁.subgraph.verts = ⇑φ.graph_iso '' H₀.subgraph.verts)
  (h_adj : ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
  (h : Nonempty (H₀.coe ≃f H))
  : Nonempty (H₁.coe ≃f H) := by
    obtain ⟨⟨f₀, h_iso₀⟩, h_emb₀⟩ := h
    let f₁_toFun (w : H₁.subgraph.verts) : U := f₀ (H₀.subgraph.vert (φ.graph_iso.symm ↑w) (by aesop))
    have h_bij₁ : Function.Bijective f₁_toFun := by
      dsimp [Function.Bijective, f₁_toFun]
      constructor
      · intro w₀ w₁ h_eq
        simp_all only [eq_iff_iff, Subtype.forall, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
        obtain ⟨_, property₀⟩ := w₀
        obtain ⟨_, property₁⟩ := w₁
        simp_all only
      · intro u
        let w : H₁.subgraph.verts := H₁.subgraph.vert (φ.graph_iso (f₀.symm u)) (by aesop)
        use w
        simp_all only [eq_iff_iff, LabeledSubgraph.coe_graph, LabeledSubgraph.coe_type_embed, RelIso.symm_apply_apply,
          Subtype.coe_eta, RelIso.apply_symm_apply]
        exact Equiv.apply_symm_apply f₀ u
    have h_iso₁ : ∀ {w₀ w₁ : H₁.subgraph.verts}, H.graph.Adj (f₁_toFun w₀) (f₁_toFun w₁) ↔ H₁.subgraph.Adj w₀ w₁ := by
      intro w₀ w₁; dsimp [f₁_toFun]
      simp_all only [eq_iff_iff, LabeledSubgraph.coe, Subtype.forall, Multiset.bijective_iff_map_univ_eq_univ, f₁_toFun]
      obtain ⟨w₀, property₀⟩ := w₀
      obtain ⟨w₁, _⟩ := w₁
      simp_all only [SimpleGraph.Subgraph.coe_adj, RelIso.coe_fn_mk, Set.mem_image, RelIso.apply_symm_apply]
    let f₁ : H₁.subgraph.verts ≃ U := Equiv.ofBijective f₁_toFun h_bij₁
    let f₁_iso : H₁.subgraph.coe ≃g H.graph := ⟨f₁, h_iso₁⟩
    have h_emb₁ : ∀ t : T, f₁_iso (H₁.coe.type_embed t) = H.type_embed t := by
      intro t
      dsimp [f₁_iso, f₁]
      have h_eq : f₁_toFun (H₁.type_embed t) = f₀.toFun (H₀.type_embed t) := by
        have h_t : H₁.type_embed t = φ.graph_iso (H₀.type_embed t) := by
          simp_all only [eq_iff_iff, LabeledSubgraph.coe_graph, RelIso.coe_fn_mk, LabeledSubgraph.coe_type_embed]
          rw [H₀.embed_eq t, H₁.embed_eq t]
          have := φ.type_preserve
          exact congrFun (id (Eq.symm this)) t
        have tmp : f₁_toFun (H₁.type_embed t) = f₁_toFun (H₁.subgraph.vert (φ.graph_iso (H₀.type_embed t)) (by aesop)) := by
          dsimp [f₁_toFun]
          simp_all only [eq_iff_iff, LabeledSubgraph.coe_graph, RelIso.coe_fn_mk, LabeledSubgraph.coe_type_embed,
            RelIso.symm_apply_apply, Subtype.coe_eta]
        rw [tmp]
        simp_all only [eq_iff_iff, LabeledSubgraph.coe_graph, RelIso.coe_fn_mk, LabeledSubgraph.coe_type_embed,
          RelIso.symm_apply_apply, Subtype.coe_eta, Equiv.toFun_as_coe, f₁_toFun]
      rw [h_eq]
      have temp := congr_fun h_emb₀ t
      rw [←temp]; simp
    exact ⟨⟨f₁, h_iso₁⟩, funext h_emb₁⟩

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist  W] [DecidableEqExist W] [FintypeExist U] [DecidableEqExist U] in
lemma predIsolabeldH_related
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : relOfPredOnlabeledSubgraph φ (predIsolabeledH H G₀) (predIsolabeledH H G₁)
  := by
    dsimp [predIsolabeledH, relOfPredOnlabeledSubgraph, relOflabeledSubgraph]
    rintro H₀ H₁ ⟨h_vert, h_adj⟩
    constructor
    · intro f_iso
      have : ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v) := by
        intro u v
        simp_all only [eq_iff_iff, implies_true, and_self]
      exact predIsolabeledH_related_support φ H H₀ H₁ h_vert this f_iso
    · intro f_iso
      have h_vert' : H₀.subgraph.verts = φ.graph_iso.symm '' H₁.subgraph.verts := by
        rw [h_vert]
        simp_all only [eq_iff_iff]
        ext1 x
        simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
      have h_adj_emb : ∀ (u v : W), H₁.subgraph.Adj u v = H₀.subgraph.Adj (φ.graph_iso.symm u) (φ.graph_iso.symm v) := by
        intro u v
        have h_uv := (h_adj (φ.graph_iso.symm u) (φ.graph_iso.symm v))
        rw [h_uv]
        simp
      have : ∀ (u v : W), H₁.subgraph.Adj u v = H₀.subgraph.Adj (φ.symm.graph_iso u) (φ.symm.graph_iso v) := by
        intro u v
        exact (h_adj_emb u v)
      exact predIsolabeledH_related_support φ.symm H H₁ H₀ h_vert' this f_iso

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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist  W] [DecidableEqExist W] in
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

theorem graph_eq
  {P Q : Type} (h : P = Q)
  : SimpleGraph P = SimpleGraph Q := by
  subst h
  rfl

omit [FintypeExist V] [DecidableEqExist V] in
theorem inducedGraph_eq
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph}
  (h_verts : H.verts = H'.verts) (h_adj : ∀ u v : V, H.Adj u v = H'.Adj u v)
  : H = H' := by
  ext u v
  · exact Eq.to_iff (congrFun h_verts u)
  · exact Eq.to_iff (h_adj u v)

omit [FintypeExist V] [DecidableEqExist V] in
theorem coe_eq
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph} (h : H = H') (h' : ↑H'.verts = ↑H.verts)
  : H.coe = cast (graph_eq h') H'.coe := by
  subst h
  dsimp [SimpleGraph.Subgraph.coe]

omit [FintypeExist V] [DecidableEqExist V] in
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
  obtain ⟨h₁, h₂⟩ := H_emb
  obtain ⟨h₃, h₄⟩ := H'_emb
  obtain ⟨h₆, h₇⟩ := G_emb
  have h₅ : h₁ = h₃ := by
    refine Function.Embedding.ext_iff.mpr ?_
    intro t
    simp_all only [RelEmbedding.coe_mk]
    simp_all only [SimpleGraph.Subgraph.coe_adj, implies_true]
    ext1
    simp_all only
  subst h₅
  simp_all only [RelEmbedding.coe_mk]

omit [FintypeExist V] [DecidableEqExist V] in
theorem embed_eq
  {T : Type} {σ : FlagType T}
  {G : SimpleGraph V} {H : G.Subgraph} {H' : G.Subgraph}
  (H_emb : σ ↪g H.coe) (H'_emb : σ ↪g H'.coe)
  (h : H = H') (h' : ↑H'.verts = ↑H.verts)
  (h'' : H.coe = cast (graph_eq h') H'.coe)
  (h''' : ∀ t : T, H_emb t = cast h' (H'_emb t))
  : HEq H_emb H'_emb := by
  have test : H_emb = cast (by
    have h_embedding_eq : (σ ↪g H.coe) = (σ ↪g cast (graph_eq h') H'.coe) := by
      congr
    subst h
    simp_all only [cast_eq])
    H'_emb := by
    subst h
    simp_all only [cast_eq]
    ext1 x
    simp_all only [cast_eq]
  subst h
  subst test
  rfl

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist   W] [DecidableEqExist W] in
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

omit [DecidableEqExist T] in
lemma labeledSubgraphDensity_respects_eqv_on_G
    (H : LabeledGraph σ U) {G₀ G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    : labeledSubgraphDensity H G₀ = labeledSubgraphDensity H G₁
  := by
  dsimp [labeledSubgraphDensity]
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedlabeledSubgraphIsoH φ H
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  have hS₁ : FintypeExist S₁ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₁) }
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

omit [DecidableEqExist T] in
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
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  have hS₁ : FintypeExist S₁ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₁) }
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

omit [DecidableEqExist V] in
lemma iso_subset_of_finset_is_full
    {S : Set V} (f_iso : V ≃ ↑S) (u : V) : u ∈ S
  := by
  by_contra h_contra
  have h_dec : DecidablePred (Membership.mem S) := by
    intro v
    exact Classical.propDecidable (v ∈ S)
  have h_card : Fintype.card S < Fintype.card V :=
    @Fintype.card_subtype_lt _ _ _ h_dec u h_contra
  have h_card' : Fintype.card V = Fintype.card S := by
    rw [Fintype.card_congr f_iso]
  simp_all

omit [DecidableEqExist V] [FintypeExist V] in
lemma iso_to_subset_mem
    {A : Type} [FintypeExist A] {S : Set V} (f_iso : A ≃ ↑S) (a : A) : (f_iso a).val ∈ S
  := by
  simp

def labeledSubgraph_top
    {σ : FlagType T} (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  let top : LabeledSubgraph σ G := {
    subgraph := {
      verts := Set.univ
      Adj := fun u v => G.graph.Adj u v
      adj_sub := by simp [SimpleGraph.Adj]
      edge_vert := by simp
      symm := by simp [SimpleGraph.symm]
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, by simp⟩
      inj' := by
        intro t₁ t₂ h
        simp at h
        exact h
      map_rel_iff' := by
        intro t₁ t₂
        simp
    }
    embed_eq := by
      intro t; simp
  }
  top

omit [FintypeExist T] [DecidableEqExist T] [DecidableEqExist V] in
lemma induced_full_labeledsubgraph_eq_top
    {G₀ G₁ : LabeledGraph σ V} {G' : LabeledSubgraph σ G₀}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃f G₁) → G' = labeledSubgraph_top G₀
  := by
  intro ⟨h_ind_G', h_iso_G'⟩
  have ⟨graph_iso, _⟩ := h_iso_G'
  let f_iso_vertex : V ≃ G'.subgraph.verts := graph_iso.toEquiv.symm
  have G'_eq_top : G'.subgraph = (labeledSubgraph_top G₀).subgraph := by
    unfold labeledSubgraph_top
    simp; ext u v
    · simp; exact iso_subset_of_finset_is_full f_iso_vertex u
    · simp
      have h_u := iso_subset_of_finset_is_full f_iso_vertex u
      have h_v := iso_subset_of_finset_is_full f_iso_vertex v
      constructor
      · exact fun a ↦ SimpleGraph.Subgraph.Adj.adj_sub a
      · exact fun a ↦ h_ind_G' h_u h_v a
  refine LabeledSubgraph.ext ?subgraph ?type_embed
  · exact G'_eq_top
  · have verts_eq : (labeledSubgraph_top G₀).subgraph.verts = G'.subgraph.verts := by
      unfold labeledSubgraph_top
      simp; ext u
      have := iso_subset_of_finset_is_full f_iso_vertex u
      exact (iff_true_right this).mpr trivial
    have type_eq : ((labeledSubgraph_top G₀).subgraph.verts : Type) = (G'.subgraph.verts : Type) := congrArg Set.Elem verts_eq
    have coe_eq := coe_eq G'_eq_top type_eq
    have h_G'_embed := G'.embed_eq
    have h_top_embed := (labeledSubgraph_top G₀).embed_eq
    have emb_eq : ∀ t : T, G'.type_embed t = cast type_eq ((labeledSubgraph_top G₀).type_embed t) := by
      intro t
      exact embed_val_eq G₀.type_embed G'.type_embed (labeledSubgraph_top G₀).type_embed G'_eq_top type_eq h_G'_embed h_top_embed t
    exact embed_eq G'.type_embed (labeledSubgraph_top G₀).type_embed G'_eq_top type_eq coe_eq emb_eq

def labeledSubgraph_bottom
    {σ : FlagType T} (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  let bottom : LabeledSubgraph σ G := {
    subgraph := {
      verts := G.type_verts
      Adj := fun u v => u ∈ G.type_verts ∧ v ∈ G.type_verts ∧ G.graph.Adj u v
      adj_sub := by simp [SimpleGraph.Adj]
      edge_vert := by
        intro u v ⟨hu, _⟩
        exact hu
      symm := by
        intro u v ⟨hu, ⟨hv, h_uv⟩⟩
        exact ⟨hv, ⟨hu, h_uv.symm⟩⟩
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, by unfold LabeledGraph.type_verts; simp⟩
      inj' := by
        intro t₁ t₂ h
        simp at h
        exact h
      map_rel_iff' := by
        intro t₁ t₂; simp
        constructor
        · intro ⟨_, ⟨_, h_adj⟩⟩
          exact h_adj
        · intro h_adj
          have ht₁: G.type_embed t₁ ∈ G.type_verts := by
            unfold LabeledGraph.type_verts
            exact Set.mem_image_of_mem G.type_embed (Set.mem_univ t₁)
          have ht₂: G.type_embed t₂ ∈ G.type_verts := by
            unfold LabeledGraph.type_verts
            exact Set.mem_image_of_mem G.type_embed (Set.mem_univ t₂)
          exact ⟨ht₁, ⟨ht₂, h_adj⟩⟩
    }
    embed_eq := by
      intro t; simp
  }
  bottom

noncomputable def type_iso
    {σ : FlagType T} (G : LabeledGraph σ V)
    : T ≃ G.type_verts  := by
  let f : T → G.type_verts := by
    intro t
    use G.type_embed t
    unfold LabeledGraph.type_verts
    exact Set.mem_image_of_mem (⇑G.type_embed) (Set.mem_univ t)
  have h_bij : Function.Bijective f := by
    constructor
    · intro t₁ t₂ h_eq
      dsimp [f] at h_eq
      simp at h_eq
      exact h_eq
    · intro u
      unfold LabeledGraph.type_verts at u
      obtain ⟨t, h_t⟩ := u
      simp_all only [Subtype.mk.injEq, f]
      simp_all only [Set.image_univ, Set.mem_range]
  let f_bij : T ≃ G.type_verts := Equiv.ofBijective f h_bij
  exact f_bij

lemma labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph
    {G : LabeledGraph σ V} {H : LabeledSubgraph σ G}
    : H = labeledSubgraph_bottom G ↔ H.IsInduced ∧ Nonempty (H.coe ≃f (emptyLabeledGraph σ)) := by
  let iso_T_G := type_iso G
  constructor
  · intro h_eq
    subst h_eq
    constructor
    · intro u v hu hv h_adj
      dsimp [labeledSubgraph_bottom] at *
      exact ⟨hu, ⟨hv, h_adj⟩⟩
    · let f : (labeledSubgraph_bottom G).subgraph.verts ≃ T := by
        dsimp [labeledSubgraph_bottom]
        exact id iso_T_G.symm
      have f_adj : ∀ {u v : ↑(labeledSubgraph_bottom G).subgraph.verts},
  (emptyLabeledGraph σ).graph.Adj (f u) (f v) ↔ (labeledSubgraph_bottom G).subgraph.coe.Adj u v := by
        intro u v
        dsimp [labeledSubgraph_bottom, emptyLabeledGraph]
        constructor
        · intro T_adj
          dsimp [labeledSubgraph_bottom] at u v f
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
            dsimp [iso_T_G, type_iso]
            exact this
          exact ⟨u.property, ⟨v.property, G_adj⟩⟩
        · intro ⟨hu, ⟨hv, G_adj⟩⟩
          dsimp [f]
          let u_t := iso_T_G.symm u
          let v_t := iso_T_G.symm v
          have h_ut : u = iso_T_G u_t := Eq.symm (Equiv.apply_symm_apply iso_T_G u)
          have h_vt : v = iso_T_G v_t := Eq.symm (Equiv.apply_symm_apply iso_T_G v)
          rw [h_ut, h_vt]
          rw [iso_T_G.symm_apply_apply, iso_T_G.symm_apply_apply]
          apply (type_embed_Adj_iff G u_t v_t).mpr
          dsimp [iso_T_G, type_iso] at h_ut h_vt
          rw [h_ut, h_vt] at G_adj
          exact G_adj
      let f_iso : (labeledSubgraph_bottom G).subgraph.coe ≃g (emptyLabeledGraph σ).graph := ⟨f, f_adj⟩
      have h_emb : ∀ t : T, f_iso ((labeledSubgraph_bottom G).coe.type_embed t) = (emptyLabeledGraph σ).type_embed t := by
        intro t
        dsimp [labeledSubgraph_bottom, emptyLabeledGraph, f_iso, f]
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
    let iso_H_G := iso_H_T.trans (id iso_T_G)
    dsimp [labeledSubgraph_bottom] at *
    have graph_eq_H_G : H.subgraph = (labeledSubgraph_bottom G).subgraph := by
      dsimp [labeledSubgraph_bottom] at *
      simp at *
      ext u v
      · simp; constructor
        · intro hu
          dsimp [emptyLabeledGraph] at type_embed
          let t := iso_H_T ⟨u, hu⟩
          have h_embed_t: H.type_embed t = u := by
            have ht := h_type_embed t
            dsimp [t] at *
            have := iso_H_T.injective ht
            simp_all only
          rw [H.embed_eq] at h_embed_t
          rw [← h_embed_t]
          unfold LabeledGraph.type_verts
          exact Set.mem_image_of_mem (⇑G.type_embed) trivial
        · intro hu
          sorry
      · simp; constructor
        · intro H_uv
          have hu : u ∈ H.subgraph.verts := H.subgraph.edge_vert H_uv
          have hv : v ∈ H.subgraph.verts := H.subgraph.edge_vert H_uv.symm
          have h_uv : H.coe.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩ := H_uv
          have := (iso_adj u hu v hv).mpr h_uv
          dsimp [emptyLabeledGraph] at this
          have := (type_embed_Adj_iff G (iso_H_T ⟨u, hu⟩) (iso_H_T ⟨v, hv⟩)).mp this
          sorry
        · intro ⟨hu, ⟨hv, h_adj⟩⟩
          sorry
    refine LabeledSubgraph.ext ?subgraph ?type_embed
    · exact graph_eq_H_G
    · have verts_eq : ↑(labeledSubgraph_bottom G).subgraph.verts = ↑H.subgraph.verts := congrArg SimpleGraph.Subgraph.verts (id (Eq.symm graph_eq_H_G))
      have type_eq : ((labeledSubgraph_bottom G).subgraph.verts : Type) = (H.subgraph.verts : Type) := congrArg Set.Elem verts_eq
      have coe_eq := coe_eq graph_eq_H_G type_eq
      have h_G'_embed := H.embed_eq
      have h_top_embed := (labeledSubgraph_bottom G).embed_eq
      have emb_eq : ∀ t : T, H.type_embed t = cast type_eq ((labeledSubgraph_bottom G).type_embed t) := by
        intro t
        exact embed_val_eq G.type_embed H.type_embed (labeledSubgraph_bottom G).type_embed graph_eq_H_G type_eq h_G'_embed h_top_embed t
      exact embed_eq H.type_embed (labeledSubgraph_bottom G).type_embed graph_eq_H_G type_eq coe_eq emb_eq

lemma labeledSubgraphCount_empty
    {σ : FlagType T} (G : LabeledGraph σ V) : labeledSubgraphCount (emptyLabeledGraph σ) G = ((G.size - σ.size).choose ((emptyLabeledGraph σ).size - σ.size))
  := by
  dsimp only [LabeledGraph.size]
  have : Fintype.card T = σ.size := by rfl
  rw [this]; simp
  simp [labeledSubgraphCount]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f (emptyLabeledGraph σ)) }
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  let S₁ := { G' : LabeledSubgraph σ G | G' = labeledSubgraph_bottom G }
  have hS₁ : FintypeExist S₁ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₁) }
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    constructor
    · intro h
      dsimp [S₀] at h
      rw [← labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph] at h
      exact h
    · intro h
      simp [S₁] at h
      constructor
      · subst h
        intro u v hu hv h_adj
        unfold labeledSubgraph_bottom at *
        simp at *
        exact ⟨hu, ⟨hv, h_adj⟩⟩
      · exact (labeledSubgraph_eq_empty_labeledSubgraph_iff_iso_empty_graph.mp h).2
  show Fintype.card S₀ = 1
  have : Fintype.card S₁ = 1 := by
    simp_all only [Set.setOf_eq_eq_singleton, Fintype.card_unique, S₀, S₁]
  rw [← this]
  exact Fintype.card_congr' (congrArg Set.Elem h_S₀_S₁)

example (a : ℚ) (h : a ≠ 0) : a / a = 1 := by
  exact (div_eq_one_iff_eq h).mpr rfl

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

omit [DecidableEqExist T] in
lemma labeledSubgraphCount_self
    (G : LabeledGraph σ V) : labeledSubgraphCount G G = 1
  := by
  simp [labeledSubgraphCount]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f G) }
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  let top : LabeledSubgraph σ G := {
    subgraph := {
      verts := Set.univ
      Adj := fun u v => G.graph.Adj u v
      adj_sub := by simp [SimpleGraph.Adj]
      edge_vert := by simp
      symm := by simp [SimpleGraph.symm]
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, by simp⟩
      inj' := by
        intro t₁ t₂ h
        simp at h
        exact h
      map_rel_iff' := by
        intro t₁ t₂
        simp
    }
    embed_eq := by
      intro t; simp
  }
  let S₁ : Finset (LabeledSubgraph σ G) := { top }
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    dsimp [S₀, S₁]; simp
    constructor
    · intro ⟨G'_ind, G'_iso⟩
      obtain ⟨graph_iso, type_embed⟩ := G'_iso
      obtain ⟨iso_verts, iso_adj⟩ := graph_iso
      have G'_eq_top : G'.subgraph = top.subgraph := by
        ext u v
        · simp; exact iso_subset_of_finset_is_full (id iso_verts.symm) u
        · have h_u := iso_subset_of_finset_is_full (id iso_verts.symm) u
          have h_v := iso_subset_of_finset_is_full (id iso_verts.symm) v
          constructor
          · exact fun a ↦ SimpleGraph.Subgraph.Adj.adj_sub a
          · exact fun a ↦ G'_ind h_u h_v a
      refine LabeledSubgraph.ext ?subgraph ?type_embed
      · exact G'_eq_top
      · have verts_eq : ↑top.subgraph.verts = ↑G'.subgraph.verts := congrArg SimpleGraph.Subgraph.verts (id (Eq.symm G'_eq_top))
        have type_eq : (top.subgraph.verts : Type) = (G'.subgraph.verts : Type) := congrArg Set.Elem verts_eq
        have coe_eq := coe_eq G'_eq_top type_eq
        have h_G'_embed := G'.embed_eq
        have h_top_embed := top.embed_eq
        have emb_eq : ∀ t : T, G'.type_embed t = cast type_eq (top.type_embed t) := by
          intro t
          exact embed_val_eq G.type_embed G'.type_embed top.type_embed G'_eq_top type_eq h_G'_embed h_top_embed t
        exact embed_eq G'.type_embed top.type_embed G'_eq_top type_eq coe_eq emb_eq
    · intro h
      constructor
      · subst h; intro; simp
      · rw [h]
        dsimp [top]
        let f (v : top.subgraph.verts) : V := v
        have h_bij : Function.Bijective f := by
          constructor
          · intro v₁ v₂ h_eq
            dsimp [f] at h_eq
            exact SetCoe.ext h_eq
          · intro v
            exact CanLift.prf v trivial
        have h_iso : ∀ {w₀ w₁ : top.subgraph.verts}, G.graph.Adj (f w₀) (f w₁) ↔ top.subgraph.Adj w₀ w₁ := by
          simp
        let f₁ : top.subgraph.verts ≃ V := Equiv.ofBijective f h_bij
        let f₁_iso : top.subgraph.coe ≃g G.graph := ⟨f₁, h_iso⟩
        have h_emb₁ : ∀ t : T, f₁_iso (top.coe.type_embed t) = G.type_embed t := by
          dsimp [f₁_iso, f₁]; simp
        exact ⟨f₁_iso, funext h_emb₁⟩
  have : Fintype.card S₀ = Fintype.card S₁ := Eq.symm (Fintype.card_congr' (congrArg Subtype (id (Eq.symm h_S₀_S₁))))
  dsimp [S₀] at this
  rw [this]

omit [DecidableEqExist T] in
lemma labeledSubgraphDensity_self
    (G : LabeledGraph σ V) : labeledSubgraphDensity G G = 1
  := by
  simp [labeledSubgraphDensity]
  exact labeledSubgraphCount_self G

omit [DecidableEqExist T] in
lemma subflagDensity_self
    (G : Flag σ V) : subflagDensity G G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  dsimp [subflagDensity, labeledSubgraphDensityLifted]
  subst hGrep
  dsimp [labeledSubgraphDensityLifted]
  exact labeledSubgraphDensity_self Grep

omit [DecidableEqExist T] in
lemma subgraphCount_other
    {G₀ G₁ : LabeledGraph σ V} (h_neq : IsEmpty (G₀ ≃f G₁)) : labeledSubgraphCount G₀ G₁ = 0
  := by
  simp [labeledSubgraphCount]
  rw [← not_nonempty_iff] at h_neq
  let S := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f G₀) }
  have hS : FintypeExist S := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S) }
  have h_S : S ⊆ ∅ := by
    intro G' ⟨h_ind_G', h_iso_G'⟩
    have f_iso_G₀_G' := h_iso_G'.some.symm
    have f_iso_G'_G₁ : G'.coe ≃f G₁ := by
      have : G' = labeledSubgraph_top G₁ := induced_full_labeledsubgraph_eq_top ⟨h_ind_G', h_iso_G'⟩
      let g : (labeledSubgraph_top G₁).coe ≃f G₁ := by
        let graph_iso : (labeledSubgraph_top G₁).subgraph.coe ≃g G₁.graph := by
          dsimp [labeledSubgraph_top]
          simp [SimpleGraph.Subgraph.coe]
          let f : (labeledSubgraph_top G₁).subgraph.verts → V := by
            dsimp [labeledSubgraph_top]
            intro v
            exact v.val
          have h_bij : Function.Bijective f := by
            constructor
            · intro v₁ v₂ h_eq
              dsimp [f] at h_eq
              exact SetCoe.ext h_eq
            · intro v
              exact CanLift.prf v trivial
          have h_iso : ∀ {w₀ w₁ : (labeledSubgraph_top G₁).subgraph.verts}, G₁.graph.Adj (f w₀) (f w₁) ↔ (labeledSubgraph_top G₁).subgraph.Adj w₀ w₁ := by
            intro u v
            simp [labeledSubgraph_top, f]
          let f_equiv := Equiv.ofBijective f h_bij
          exact ⟨f_equiv, h_iso⟩
        have h_emb : ∀ t : T, graph_iso ((labeledSubgraph_top G₁).type_embed t) = G₁.type_embed t := by
          intro t
          exact rfl
        exact ⟨graph_iso, funext h_emb⟩
      rw [← this] at g
      exact g
    have f_iso_G₀_G₁ := f_iso_G₀_G'.trans f_iso_G'_G₁
    exact h_neq ⟨f_iso_G₀_G₁⟩
  show Fintype.card S = 0
  simp_all only [not_nonempty_iff, Set.subset_empty_iff, Fintype.card_ofIsEmpty]

omit [DecidableEqExist T] in
lemma labeledSubgraphDensity_other
    {G₀ G₁ : LabeledGraph σ V} (h_neq : IsEmpty (G₀ ≃f G₁)) : labeledSubgraphDensity G₀ G₁ = 0
  := by
  dsimp [labeledSubgraphDensity]
  have := subgraphCount_other h_neq
  simp_all only [Nat.cast_zero, zero_div]

omit [DecidableEqExist T] in
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

end

section

variable {t : ℕ}
  {Vl : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl]
  {Vl' : Fin t → Type} [FintypeList Vl'] [DecidableEqList Vl']
  {V : Type} [FintypeExist V] [DecidableEqExist V]
  {W : Type} [FintypeExist W] [DecidableEqExist W]
  {U : Type} [FintypeExist U] [DecidableEqExist U]
  {U₁ : Type} [FintypeExist U₁] [DecidableEqExist U₁]
  {U₂ : Type} [FintypeExist U₂] [DecidableEqExist U₂]
  {U₃ : Type} [FintypeExist U₃] [DecidableEqExist U₃]

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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] [FintypeExist U] [DecidableEqExist U] in
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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
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

 omit [FintypeExist T] [DecidableEqExist T] [FintypeList Vl] [DecidableEqList Vl] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
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

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
lemma inducedlabeledSubgraphList_type_embed_mem
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    : ∀ (i : Fin t), ∀ (t : T), G₁.type_embed t ∈ ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts
  := by
  intro i
  exact inducedlabeledSubgraph_type_embed_mem φ (Hl₀ i)

omit [FintypeExist T] [DecidableEqExist T] [FintypeList Vl] [DecidableEqList Vl] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
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

omit [FintypeExist T] [DecidableEqExist T] [FintypeList Vl] [DecidableEqList Vl] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
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
  simp
  simp at iso
  exact iso

omit [DecidableEqExist T] in
lemma labeledSubgraphListDensity_respects_eqv_on_G
    (Hl : LabeledGraphList σ t Vl) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphListDensity Hl G = labeledSubgraphListDensity Hl G'
  := by
  dsimp [labeledSubgraphListDensity]
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅) }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G' | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G'.type_verts) ∩ ((Gl j).subgraph.verts \ G'.type_verts) = ∅) }
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  have hS₁ : FintypeExist S₁ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₁) }
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

omit [DecidableEqExist T] in
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
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  have hS₁ : FintypeExist S₁ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₁) }
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

omit [DecidableEqExist T] in
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

omit [DecidableEqExist T] in
theorem flagListDensity_HEq_eq
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_HEq : HEq Fl Fl') (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity Fl' G
  := by
  subst h_Vl_eq
  have h_Fl_eq : Fl = Fl' := by simp_all only [heq_eq_eq]
  subst h_Fl_eq
  rfl

omit [DecidableEqExist T] in
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

omit [DecidableEqExist T] in
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

omit [DecidableEqExist T] in
theorem labeledSubgraphListDensity_eq_flagDensity₁
    (F : LabeledGraph σ U) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity [F]ᵍ G = flagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  rw [labeledSubgraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_singleton]
  simp [flagDensity₁]

omit [DecidableEqExist T] in
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

omit [DecidableEqExist T] in
theorem flagDensity_self
    (F : Flag σ W) : flagDensity₁ F F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F]
  exact subflagDensity_self F

omit [DecidableEqExist T] in
theorem flagDensity_other
    {F F' : Flag σ W} (h_neq : F ≠ F') : flagDensity₁ F F' = 0
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F']
  apply  subflagDensity_other h_neq

theorem flagDensity_permute
    (Fl : FlagList σ t Vl) (G : Flag σ W) (π : Perm t)
    : flagListDensity Fl G = flagListDensity (Fl.permute π) G
  := by
  dsimp [flagListDensity, quotLabeledSubgraphListDensity]
  congr
  ext Grep
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ Grep | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Quotient.out (Fl i))) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ Grep.type_verts) ∩ ((Gl j).subgraph.verts \ Grep.type_verts) = ∅) }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ Grep | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Quotient.out (Fl.permute π i))) ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ Grep.type_verts) ∩ ((Gl j).subgraph.verts \ Grep.type_verts) = ∅) }
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    let φ : ∀ (i : Fin t), (Quotient.out (Fl i) : LabeledGraph σ (Vl i)) ≃f (Quotient.out (Fl.permute π i) : LabeledGraph σ (Vl (π i))) := by
      intro i
      -- Use the fact that Fl.permute π i = Fl (π i) and construct the equivalence
      have h_eq : Fl.permute π i = Fl (π i) := rfl
      rw [h_eq]
      sorry
    -- exact isoSetOfInducedlabeledSubgraph_eqv φ Grep
    sorry
  have hS₀ : FintypeExist S₀ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₀) }
  have hS₁ : FintypeExist S₁ := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S₁) }
  sorry

instance {V W : Type} [FintypeExist V] [FintypeExist W]
    : FintypeList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance {V W : Type} [DecidableEqExist V] [DecidableEqExist W]
    : DecidableEqList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance {V W U : Type} [FintypeExist V] [FintypeExist W] [FintypeExist U]
    : FintypeList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

instance {V W U : Type} [DecidableEqExist V] [DecidableEqExist W] [DecidableEqExist U]
    : DecidableEqList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

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
  :=
  sorry

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

end
