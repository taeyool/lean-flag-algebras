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
  ∧ (∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso.toFun u) (φ.graph_iso.toFun v))
  ∧ (∀ (t : T), H₀.type_embed t = φ.symm.graph_iso (H₁.type_embed t))

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
  (h_adj : ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v) ∧ ∀ (t : T), ↑(H₀.type_embed t) = φ.symm.graph_iso ↑(H₁.type_embed t))
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
      obtain ⟨w₁, property₁⟩ := w₁
      simp
      constructor
      · intro h_adj₀
        simp_all only [RelIso.coe_fn_mk, Set.mem_image, RelIso.apply_symm_apply]
      · intro h_adj₁
        simp_all only [RelIso.coe_fn_mk, Set.mem_image, RelIso.apply_symm_apply]
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
    rintro H₀ H₁ ⟨h_vert, ⟨h_adj, h_emb⟩⟩
    constructor
    · intro f_iso
      have : ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v) ∧ ∀ (t : T), ↑(H₀.type_embed t) = φ.symm.graph_iso ↑(H₁.type_embed t) := by
        intro u v
        simp_all only [eq_iff_iff, implies_true, and_self]
      exact predIsolabeledH_related_support φ H H₀ H₁ h_vert this f_iso
    · intro f_iso
      have h_vert' : H₀.subgraph.verts = φ.graph_iso.symm '' H₁.subgraph.verts := by
        rw [h_vert]
        simp_all only [eq_iff_iff]
        ext1 x
        simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
      have h_adj_emb : ∀ (u v : W), H₁.subgraph.Adj u v = H₀.subgraph.Adj (φ.graph_iso.symm u) (φ.graph_iso.symm v) ∧ ∀ (t: T), (H₁.type_embed t) = φ.graph_iso (H₀.type_embed t):= by
        intro u v
        constructor
        · have h_uv := (h_adj (φ.graph_iso.symm u) (φ.graph_iso.symm v))
          rw [h_uv]
          simp
        · intro t
          have h_t := h_emb t
          rw [h_t]
          rw [H₁.embed_eq t]
          have := φ.graph_iso.symm.left_inv (G₁.type_embed t)
          rw [←this]
          exact congrArg (⇑φ.graph_iso.symm.symm) (congrArg (⇑φ.graph_iso.symm) (id (Eq.symm this)))
      have : ∀ (u v : W), H₁.subgraph.Adj u v = H₀.subgraph.Adj (φ.symm.graph_iso u) (φ.symm.graph_iso v) ∧ ∀ (t : T), ↑(H₁.type_embed t) = φ.symm.symm.graph_iso ↑(H₀.type_embed t) := by
        intro u v
        constructor
        · exact (h_adj_emb u v).1
        · intro t
          rw [(h_adj_emb u v).2 t]
          rfl
      exact predIsolabeledH_related_support φ.symm H H₁ H₀ h_vert' this f_iso

omit [FintypeExist T] [DecidableEqExist T] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
lemma relOfTypeVertex
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    {t : T} {v : V} (h_G₁t : G₁.type_embed t = φ.graph_iso v) (H₀ : LabeledSubgraph σ G₀)
    : ∃ (G₀t : V) (G₁t : W) (H₀t : V), G₁t = φ.graph_iso G₀t ∧ v = G₀t ∧ H₀t = G₀t ∧ v ∈ H₀.subgraph.verts
    := by
    let G₀t := G₀.type_embed t
    let G₁t := G₁.type_embed t
    let H₀t := H₀.type_embed t
    have h_eq : G₁t = φ.graph_iso G₀t := by
      dsimp [G₀t, G₁t]
      rw [←φ.type_preserve]
      rfl
    have h_eq' : v = G₀t := by
      have : φ.graph_iso v = φ.graph_iso G₀t := by
        dsimp [G₁t] at h_eq
        rw [h_G₁t] at h_eq
        exact h_eq
      simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, EmbeddingLike.apply_eq_iff_eq, G₀t, G₁t]
    have h_eq'' : H₀t = G₀t := by
      dsimp [H₀t]
      rw [H₀.embed_eq t]
    have h_vert : v ∈ H₀.subgraph.verts := by
      rw [h_eq', ←h_eq'']
      simp
    use G₀t, G₁t, H₀t

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
        simp_all
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
lemma inducerdlabeledSubgraph_support
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
    : relOflabeledSubgraph φ H₀ (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀))
  := by
  dsimp [relOflabeledSubgraph, inducedlabeledSubgraph]; simp
  constructor
  · intro u v
    constructor
    · intro h_uv
      constructor
      · have : G₀.graph.Adj u v := SimpleGraph.Subgraph.Adj.adj_sub h_uv
        exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mpr this
      · exact ⟨H₀.subgraph.edge_vert h_uv, H₀.subgraph.edge_vert h_uv.symm⟩
    · intro ⟨h_G₁uv, ⟨h_u, h_v⟩⟩
      have h_G₀uv : G₀.graph.Adj u v := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_G₁uv
      apply h_ind₀ h_u h_v h_G₀uv
  · intro t
    rw [H₀.embed_eq t]
    rw [←φ.symm.type_preserve]
    simp

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
    simp_all only [cast_eq]
  ) H'_emb := by
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
  : H₀ = (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' ((inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)).1).subgraph.verts) (inducerdlabeledSubgraph_support φ.symm ((inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)).1))).1 := by
  dsimp [inducedlabeledSubgraph]
  have h : H₀.subgraph.verts = ⇑φ.symm.graph_iso '' (⇑φ.graph_iso '' H₀.subgraph.verts) := by
      ext v; constructor
      · intro h
        simp_all only [Set.mem_image, exists_exists_and_eq_and]
        use v
        exact ⟨h, φ.graph_iso.left_inv v⟩
      · intro h
        simp_all only [Set.mem_image, exists_exists_and_eq_and]
        obtain ⟨w, ⟨h1, h2⟩⟩ := h
        have := φ.graph_iso.left_inv w
        rw [←h2]
        rw [←this] at h1
        exact h1
  let f_H := inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)
  let f_inv_f_H := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' (f_H.1).subgraph.verts) (inducerdlabeledSubgraph_support φ.symm (f_H.1))).1

  have h_verts_eq : H₀.subgraph.verts = f_inv_f_H.subgraph.verts := by
    dsimp [f_inv_f_H, inducedlabeledSubgraph]
    exact h
  have h_adj : ∀ (u v : V), H₀.subgraph.Adj u v = f_inv_f_H.subgraph.Adj u v := by
    intro u v
    dsimp [f_inv_f_H, f_H, inducedlabeledSubgraph]
    rw [eq_iff_iff]; constructor
    · intro h_adj
      constructor
      · exact SimpleGraph.Subgraph.Adj.adj_sub h_adj
      · simp; constructor
        · use u
          exact ⟨H₀.subgraph.edge_vert h_adj, φ.graph_iso.left_inv u⟩
        · use v
          exact ⟨H₀.subgraph.edge_vert h_adj.symm, φ.graph_iso.left_inv v⟩
    · intro ⟨h_adj, ⟨h_u, h_v⟩⟩
      rw [←h] at h_u h_v
      exact h_ind₀ h_u h_v h_adj
  have inducedGraph_test := inducedGraph_eq h_verts_eq h_adj
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
    let H₁ := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)).1
    let h_ind₁ : H₁.IsInduced := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)).2
    have : relOflabeledSubgraph φ H₀ H₁ := inducedlabeledSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let H₀ := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts) (inducerdlabeledSubgraph_support φ.symm H₁)).1
    let h_ind₀ : H₀.IsInduced := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts) (inducerdlabeledSubgraph_support φ.symm H₁)).2
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

#check heq_eq_eq

example {α : Type} {a b : α} (h : a = b) : HEq a b := by
  have h' : HEq a b := by
    exact heq_of_eq h
  exact h'

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

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℕ
  :=
  let ind (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (Gl i).IsInduced
  let p₁ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)
  let p₂ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅
  let S := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | ind Gl ∧ p₁ Gl ∧ p₂ Gl }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card

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
  := fun Gl ↦ (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅)

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
lemma predIsoLabeledH_related_iso
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁)
    (h_vert : H₁.subgraph.verts = ⇑φ.graph_iso '' H₀.subgraph.verts)
    (h_adj : ∀ (u v : V), H₀.subgraph.Adj u v ↔ H₁.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
    (h_emb : ∀ (t : T), (H₀.type_embed t) = φ.symm.graph_iso (H₁.type_embed t))
    (h_iso₀ : Nonempty (H₀.coe ≃f H))
  : Nonempty (H₁.coe ≃f H) := by
  have h := predIsolabeldH_related φ (H₀).coe
  dsimp [relOfPredOnlabeledSubgraph, relOflabeledSubgraph, predIsolabeledH] at h
  simp at h
  have iso_refl : Nonempty ((H₀).coe ≃f (H₀).coe) := by
    have : (H₀).coe ≃f (H₀).coe := LabeledGraphIso.refl
    exact Nonempty.intro this
  have iso_H₁_H₀ := (h H₀ H₁ h_vert h_adj h_emb).mp iso_refl
  let H₀_H := Classical.choice h_iso₀
  let H₁_H₀ := Classical.choice iso_H₁_H₀
  have h_iso₁ : H₁.coe ≃f H := H₁_H₀.trans H₀_H
  exact Nonempty.intro h_iso₁

lemma predIsoLabeledH_related_indep
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    (H₀i : LabeledSubgraph σ G₀) (H₀j : LabeledSubgraph σ G₀)
    (H₁i : LabeledSubgraph σ G₁) (H₁j : LabeledSubgraph σ G₁)
    (h_vert_i : H₁i.subgraph.verts = ⇑φ.graph_iso '' H₀i.subgraph.verts)
    (h_adj_i : ∀ (u v : V), H₀i.subgraph.Adj u v ↔ H₁i.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
    (h_emb_i : ∀ (t : T), (H₀i.type_embed t) = φ.symm.graph_iso (H₁i.type_embed t))
    (h_vert_j : H₁j.subgraph.verts = ⇑φ.graph_iso '' H₀j.subgraph.verts)
    (h_adj_j : ∀ (u v : V), H₀j.subgraph.Adj u v ↔ H₁j.subgraph.Adj (φ.graph_iso u) (φ.graph_iso v))
    (h_emb_j : ∀ (t : T), (H₀j.type_embed t) = φ.symm.graph_iso (H₁j.type_embed t))
    (h_indep₀ : H₀i.subgraph.verts ∩ H₀j.subgraph.verts = ∅)
  : H₁i.subgraph.verts ∩ H₁j.subgraph.verts = ∅ := by sorry

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
    have h_emb₀ : ∀ (i : Fin t) (t : T), ((Hl₀ i).type_embed t) = φ.symm.graph_iso ((Hl₁ i).type_embed t) := by
        intro i t
        rw [(Hl₀ i).embed_eq t, (Hl₁ i).embed_eq t, ← φ.type_preserve]
        exact id (Eq.symm (φ.symm.graph_iso.right_inv' (G₀.type_embed t)))
    have h_ind₁ : ∀ (i : Fin t), (Hl₁ i).IsInduced := by
      intro i
      have ⟨h_vert, h_adj⟩ := h_rel i
      dsimp [LabeledSubgraph.IsInduced]
      intro u v h_u h_v h_uv
      apply predIsoLabeledH_related_ind φ (Hl₀ i) (Hl₁ i) h_vert h_adj (h_ind₀ i) h_u h_v h_uv
    have h_1₁ : ∀ (i : Fin t), Nonempty ((Hl₁ i).coe ≃f Hl i) := by
      intro i
      have ⟨h_vert, h_adj⟩ := h_rel i
      have h_emb := h_emb₀ i
      exact predIsoLabeledH_related_iso φ (Hl i) (Hl₀ i) (Hl₁ i) h_vert h_adj h_emb (h_1₀ i)
    have h_2₁ : ∀ (i j : Fin t), i ≠ j → (Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts = ∅ := by
      intro i j h_ij
      have h_empty_i := (h_2₀ i j h_ij)
      have h_empty : φ.graph_iso '' ((Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts) = ∅ := Set.image_eq_empty.mpr (h_2₀ i j h_ij)
      by_contra h_nonempty
      push_neg at h_nonempty
      have h_nomempty_exists : ∃ w : W, w ∈ (Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts := h_nonempty
      obtain ⟨w, ⟨h_wi₁, h_wj₁⟩⟩ := h_nomempty_exists
      have h_w : ∀ (k : Fin t), w ∈ (Hl₁ k).subgraph.verts → φ.symm.graph_iso w ∈ (Hl₀ k).subgraph.verts := by
        intro k h_wk₁
        let ⟨v_rel, e_rel⟩ := h_rel k
        rw [v_rel] at h_wk₁
        simp_all only [Set.mem_image]
        obtain ⟨w', ⟨h_wk₀, h_ww'⟩⟩ := h_wk₁
        have h_ww' : w' = φ.symm.graph_iso w := by
          rw [← h_ww']
          exact id (Eq.symm (φ.graph_iso.left_inv' w'))
        rw [h_ww'] at h_wk₀
        exact h_wk₀
      have h_wi₀ : φ.symm.graph_iso w ∈ (Hl₀ i).subgraph.verts := h_w i h_wi₁
      have h_wj₀ : φ.symm.graph_iso w ∈ (Hl₀ j).subgraph.verts := h_w j h_wj₁
      have h_w_ij : φ.symm.graph_iso w ∈ (Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts := Set.mem_inter h_wi₀ h_wj₀
      simp_all only [Set.mem_empty_iff_false]
    exact ⟨h_ind₁, ⟨h_1₁, h_2₁⟩⟩
  · intro ⟨h_ind₁, ⟨h_1₁, h_2₁⟩⟩
    have h_ind₀ : ∀ (i : Fin t), (Hl₀ i).IsInduced := by
      intro i
      have ⟨v_rel, e_rel⟩ := h_rel i
      have v_rel' : (Hl₀ i).subgraph.verts = φ.symm.graph_iso '' (Hl₁ i).subgraph.verts := by
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
      have e_rel' : ∀ (u v : W), (Hl₁ i).subgraph.Adj u v ↔ (Hl₀ i).subgraph.Adj (φ.symm.graph_iso u) (φ.symm.graph_iso v) := by
        intro u v
        have h_u : φ.graph_iso (φ.symm.graph_iso u) = u := φ.symm.graph_iso.left_inv u
        have h_v : φ.graph_iso (φ.symm.graph_iso v) = v := φ.symm.graph_iso.left_inv v
        have := e_rel (φ.symm.graph_iso u) (φ.symm.graph_iso v)
        rw [h_u, h_v] at this
        exact this.symm
      dsimp [LabeledSubgraph.IsInduced]
      intro u v h_u h_v h_uv
      apply predIsoLabeledH_related_ind φ.symm (Hl₁ i) (Hl₀ i) v_rel' e_rel' (h_ind₁ i) h_u h_v h_uv
    have h_1₀ : ∀ (i : Fin t), Nonempty ((Hl₀ i).coe ≃f Hl i) := by
      intro i
      have ⟨v_rel, e_rel⟩ := h_rel i
      have v_rel' : (Hl₀ i).subgraph.verts = φ.symm.graph_iso '' (Hl₁ i).subgraph.verts := by
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
      have e_rel' : ∀ (u v : W), (Hl₁ i).subgraph.Adj u v ↔ (Hl₀ i).subgraph.Adj (φ.symm.graph_iso u) (φ.symm.graph_iso v) := by
        intro u v
        have h_u : φ.graph_iso (φ.symm.graph_iso u) = u := φ.symm.graph_iso.left_inv u
        have h_v : φ.graph_iso (φ.symm.graph_iso v) = v := φ.symm.graph_iso.left_inv v
        have := e_rel (φ.symm.graph_iso u) (φ.symm.graph_iso v)
        rw [h_u, h_v] at this
        exact this.symm
      have h_emb : ∀ (t : T), ((Hl₁ i).type_embed t) = φ.graph_iso ((Hl₀ i).type_embed t) := by
        intro t
        rw [(Hl₁ i).embed_eq t, (Hl₀ i).embed_eq t, ← φ.symm.type_preserve]
        exact id (Eq.symm (φ.graph_iso.right_inv' (G₁.type_embed t)))
      exact predIsoLabeledH_related_iso φ.symm (Hl i) (Hl₁ i) (Hl₀ i) v_rel' e_rel' h_emb (h_1₁ i)
    have h_2₀ : ∀ (i j : Fin t), i ≠ j → (Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts = ∅ := by
      intro i j h_ij
      have h_empty₁ := (h_2₁ i j h_ij)
      by_contra h_nonempty
      push_neg at h_nonempty
      have h_nomempty_exists : ∃ v : V, v ∈ (Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts := h_nonempty
      obtain ⟨v, ⟨h_vi₀, h_vj₀⟩⟩ := h_nomempty_exists
      have ⟨v_rel_i, e_rel_i⟩ := h_rel i
      have ⟨v_rel_j, e_rel_j⟩ := h_rel j
      have v_rel_i' : (Hl₀ i).subgraph.verts = φ.symm.graph_iso '' (Hl₁ i).subgraph.verts := by
        rw [v_rel_i]
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
      have v_rel_j' : (Hl₀ j).subgraph.verts = φ.symm.graph_iso '' (Hl₁ j).subgraph.verts := by
        rw [v_rel_j]
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
      have h_v_i : φ.graph_iso v ∈ (Hl₁ i).subgraph.verts := by
        rw [v_rel_i'] at h_vi₀
        rw [Set.mem_image] at h_vi₀
        obtain ⟨v', ⟨h_v_i', h_vv'⟩⟩ := h_vi₀
        rw [← h_vv']
        have := φ.symm.graph_iso.left_inv' v'
        exact Set.mem_of_eq_of_mem this h_v_i'
      have h_v_j : φ.graph_iso v ∈ (Hl₁ j).subgraph.verts := by
        rw [v_rel_j'] at h_vj₀
        rw [Set.mem_image] at h_vj₀
        obtain ⟨v', ⟨h_v_j', h_vv'⟩⟩ := h_vj₀
        rw [← h_vv']
        have := φ.symm.graph_iso.left_inv' v'
        exact Set.mem_of_eq_of_mem this h_v_j'
      have h_v_ij : φ.graph_iso v ∈ (Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts := Set.mem_inter h_v_i h_v_j
      have h_contra : φ.graph_iso v ∉ (Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts := by
        rw [h_empty₁]
        exact Set.not_mem_empty (φ.graph_iso v)
      contradiction
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
lemma inducedlabeledSubgraphList_support
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W}
    (φ : G₀ ≃f G₁) (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    : ∀ (i : Fin t), ∀ (t : T), G₁.type_embed t ∈ ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts
  := by
  intro i t
  simp_all only [Set.mem_image]
  use (Hl₀ i).type_embed t
  constructor
  · simp
  · rw [←φ.type_preserve]; simp
    exact (Hl₀ i).embed_eq t

omit [FintypeExist T] [DecidableEqExist T] [FintypeList Vl] [DecidableEqList Vl] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
lemma inducedlabeledSubgraphList_related
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (h_ind₀ : ∀ i, (Hl₀ i).subgraph.IsInduced)
    : relOflabeledSubgraphList φ Hl₀
      (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_support φ Hl₀))
  := by
  dsimp [relOflabeledSubgraphList, inducedlabeledSubgraphList]
  intro i
  constructor
  · dsimp [inducedlabeledSubgraph]
  · intro u v
    constructor
    · intro h_uv
      constructor
      · have : G₀.graph.Adj u v := SimpleGraph.Subgraph.Adj.adj_sub h_uv
        exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mpr this
      · constructor
        · use u; simp
          exact (Hl₀ i).subgraph.edge_vert h_uv
        · use v; simp
          exact (Hl₀ i).subgraph.edge_vert h_uv.symm
    · dsimp [inducedlabeledSubgraph]
      intro ⟨h_G₁uv, ⟨h_G₁u, h_G₁v⟩⟩
      have h_G₀uv : G₀.graph.Adj u v := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_G₁uv
      have h_G₀u : u ∈ (Hl₀ i).subgraph.verts := by
        simp_all only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
      have h_G₀v : v ∈ (Hl₀ i).subgraph.verts := by
        simp_all only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
      apply (h_ind₀ i) h_G₀u h_G₀v h_G₀uv

omit [FintypeExist T] [DecidableEqExist T] [FintypeList Vl] [DecidableEqList Vl] [FintypeExist V] [DecidableEqExist V] [FintypeExist W] [DecidableEqExist W] in
lemma Hl_eq_reverseinduced_induced_Hl
  {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
  (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀) (h_ind₀ : ∀ i, (Hl₀ i).subgraph.IsInduced)
  : Hl₀ = (inducedlabeledSubgraphList G₀ (fun i => φ.symm.graph_iso '' ((inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_support φ Hl₀)).1 i).subgraph.verts) (inducedlabeledSubgraphList_support φ.symm (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_support φ Hl₀)).1)).1 := by
  dsimp [inducedlabeledSubgraphList]
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
    let Hl₁ := (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_support φ Hl₀)).1
    let h_ind₁ : ∀ i, (Hl₁ i).subgraph.IsInduced := (inducedlabeledSubgraphList G₁ (fun i => φ.graph_iso '' (Hl₀ i).subgraph.verts) (inducedlabeledSubgraphList_support φ Hl₀)).2
    have : relOflabeledSubgraphList φ Hl₀ Hl₁ :=
      inducedlabeledSubgraphList_related φ Hl₀ h_ind₀
    have h_p₁ : p₁ Hl₁ := (h_rel Hl₀ Hl₁ this).mp h_p₀
    exact ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv : S₁ → S₀ := by
    intro s₁
    dsimp [S₁] at s₁
    let ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let Hl₀ := (inducedlabeledSubgraphList G₀ (fun i => φ.symm.graph_iso '' (Hl₁ i).subgraph.verts) (inducedlabeledSubgraphList_support φ.symm Hl₁)).1
    let h_ind₀ : ∀ i, (Hl₀ i).subgraph.IsInduced := (inducedlabeledSubgraphList G₀ (fun i => φ.symm.graph_iso '' (Hl₁ i).subgraph.verts) (inducedlabeledSubgraphList_support φ.symm Hl₁)).2
    have : relOflabeledSubgraphList φ.symm Hl₁ Hl₀ :=
      inducedlabeledSubgraphList_related φ.symm Hl₁ h_ind₁
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
    : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
    ≃ { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G' | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
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
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G' | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
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
    : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) } ≃
      { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl' i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
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
  have : { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) } = { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl' i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) } :=
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
  let S₀ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ Grep | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
  let S₁ := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ Grep | (∀ (i : Fin t), (Gl i).IsInduced) ∧ (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl' i)) ∧ (∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅) }
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

noncomputable def flagListDensity
    : FlagList σ t Vl → Flag σ W → ℚ
  :=
  fun Fl => quotLabeledSubgraphListDensity Fl.coe

theorem flagListDensity_HEq_eq
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_HEq : HEq Fl Fl') (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity Fl' G
  := by
  subst h_Vl_eq
  have h_Fl_eq : Fl = Fl' := by simp_all only [heq_eq_eq]
  subst h_Fl_eq
  rfl

example (F : Flag σ U) (G : Flag σ W)
    : subflagDensity F G = flagListDensity [F]ᶠ G
  := by
  rcases Quotient.exists_rep F with ⟨Frep, hFrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  have h_count : labeledSubgraphCount Frep Grep = labeledSubgraphListCount (fun (_ : Fin 1) => Frep) Grep := by
    dsimp [labeledSubgraphCount, labeledSubgraphListCount]
    apply Finset.card_bij
    · intro H hH
      simp at hH
      show (fun (_ : Fin 1) => H) ∈ _
      simp [Set.toFinset_setOf]
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
      simp_all
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

theorem flagDensity_self
    (F : Flag σ W) : flagDensity₁ F F = 1
  :=
  sorry

theorem flagDensity_other
    {F F' : Flag σ W} (h_neq : F ≠ F') : flagDensity₁ F F' = 0
  :=
  sorry

theorem flagDensity_permute
    (Fl : FlagList σ t Vl) (G : Flag σ W) (π : Perm t)
    : flagListDensity Fl G = flagListDensity (Fl.permute π) G
  :=
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
