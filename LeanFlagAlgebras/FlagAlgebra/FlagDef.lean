import «LeanFlagAlgebras».Utils.SubgraphUtil

/-! # Flag Algebra: Core Definitions

This file defines the foundational objects of Razborov's flag algebras: a
`FlagType` (the type `σ` describing the labeled "root"), a `LabeledGraph`
(a graph together with an embedding of `σ`), `LabeledSubgraph`, isomorphism of
labeled graphs (`≃f`), and the resulting `Flag σ V` as the quotient of labeled
graphs by isomorphism. It also builds list-indexed bundles (`FlagList`,
`LabeledGraphList`) together with the type-level `insert`/`permute` operations
needed to talk about tuples of flags.

It sits above `GraphAlgebra`/`SubgraphUtil` (plain subgraph densities) and below
`FlagAlgebra.lean`, which forms the real algebra `A^σ` out of these flags. -/

open Classical

/-- Demote an index `i : Fin (t + 1)` that is not the last position (`i ≠ t`)
down to `Fin t`, keeping its underlying value. Used to index into the original
list when reasoning about `listTypeInsert`. -/
def Fin.coe {t : ℕ} (i : Fin (t + 1)) (hi : i.val ≠ t) : Fin t
  :=
  ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.is_lt) hi⟩

namespace FlagAlgebras

variable {T : Type} [Fintype T]

/-- The "type" `σ` of a flag: a simple graph on the label set `T`, identifying
the distinguished labeled vertices that every flag of type `σ` must carry. -/
abbrev FlagType := SimpleGraph

/-- The number of labeled vertices in a type `σ`, i.e. `Fintype.card T`. -/
noncomputable def FlagType.size (_ : FlagType T) : ℕ
  :=
  Fintype.card T

/-- A `σ`-flag carrier: a simple graph on `V` together with an induced-graph
embedding of the type `σ`, distinguishing the labeled vertices. The basic
object whose isomorphism classes form `Flag σ V`. -/
@[ext]
structure LabeledGraph (σ : FlagType T) (V : Type) where
  graph : SimpleGraph V
  type_embed : σ ↪g graph

/-- The set of labeled vertices of `G`: the image of the type embedding. -/
def LabeledGraph.type_verts (G : LabeledGraph σ V) : Set V :=
  G.type_embed '' Set.univ

omit [Fintype T] in
lemma LabeledGraph.mem_type_verts {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} {v : V} :
    v ∈ G.type_verts ↔ ∃ t, G.type_embed t = v := by
  simp only [type_verts, Set.image_univ, Set.mem_range]

noncomputable instance {σ : FlagType T} (G : LabeledGraph σ V) :
    Fintype G.type_verts :=
  Set.univ.fintypeImage G.type_embed

lemma LabeledGraph.type_verts_card_eq {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
  : Fintype.card G.type_verts = σ.size := by
  dsimp [LabeledGraph.type_verts, FlagType.size]
  rw [Set.univ.card_image_of_injective G.type_embed.injective]
  exact (set_fintype_card_eq_univ_iff Set.univ).mpr rfl

omit [Fintype T] in
lemma LabeledGraph.type_verts_contain {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (t : T)
  : G.type_embed t ∈ G.type_verts :=
  LabeledGraph.mem_type_verts.mpr ⟨t, rfl⟩

/-- The canonical equivalence between the label set `T` and `G`'s labeled
vertices, induced by the type embedding. -/
noncomputable def LabeledGraph.iso_type_G
     {σ : FlagType T} (G : LabeledGraph σ V) : T ≃ G.type_verts := by
  let f : T → G.type_verts := by
    intro t
    use G.type_embed t
    rw [mem_type_verts]
    use t
  have h_bij : Function.Bijective f := by
    constructor
    · intro t₁ t₂ h_eq
      dsimp [f] at h_eq
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
      exact h_eq
    · intro u
      unfold LabeledGraph.type_verts at u
      obtain ⟨t, h_t⟩ := u
      simp only [Subtype.mk.injEq, f]
      simp only [Set.image_univ, Set.mem_range] at h_t
      exact h_t
  exact Equiv.ofBijective f h_bij

omit [Fintype T] in
lemma iso_type_G_eq_type_embed
    {σ : FlagType T} (G : LabeledGraph σ U) (t : T)
    : G.iso_type_G t = G.type_embed t
  :=
  rfl

noncomputable instance labeledGraphFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (LabeledGraph σ V)
  :=
  let f : LabeledGraph σ V → SimpleGraph V × (T → V) :=
    fun ⟨G, embed⟩ ↦ (G, embed.toFun)
  have f_inj : Function.Injective f := by
    rintro ⟨G, φ⟩ ⟨G', φ'⟩ h_eq
    obtain ⟨rfl, right⟩ := Prod.mk.injEq _ _ _ _ ▸ h_eq
    congr
    exact DFunLike.coe_fn_eq.mp right
  Fintype.ofInjective f f_inj

/-- The number of vertices of a labeled graph, i.e. `Fintype.card V`. -/
noncomputable def LabeledGraph.size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (_ : LabeledGraph σ V) : ℕ
  :=
  Fintype.card V

lemma LabeledGraph.type_size_le_size {σ : FlagType T} {V : Type} [Fintype V] (G : LabeledGraph σ V)
    : σ.size ≤ G.size
  := by
  rw [← G.type_verts_card_eq]
  exact set_fintype_card_le_univ G.type_verts

omit [Fintype T] in
/-- The type embedding is an *induced* embedding: two labels are adjacent in
`σ` iff their images are adjacent in `G`. -/
theorem type_embed_Adj_iff
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (u v : T)
    : σ.Adj u v ↔ G.graph.Adj (G.type_embed u) (G.type_embed v)
  :=
  (SimpleGraph.Embedding.map_adj_iff G.type_embed).symm

omit [Fintype T] in
theorem iso_type_Adj_iff
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (u v : G.type_verts)
    : σ.Adj (G.iso_type_G.symm u) (G.iso_type_G.symm v) ↔ G.graph.Adj u v := by
  let u_t := G.iso_type_G.symm u
  have h_ut : G.iso_type_G u_t = u := G.iso_type_G.apply_symm_apply u
  let v_t := G.iso_type_G.symm v
  have h_vt : G.iso_type_G v_t = v := G.iso_type_G.apply_symm_apply v
  rw [type_embed_Adj_iff G u_t v_t, ← h_ut, ← h_vt]
  rfl


/-- The trivial flag of type `σ`: the graph is `σ` itself on the label set `T`,
with the identity type embedding. This is the multiplicative unit flag. -/
def emptyLabeledGraph (σ : FlagType T) : LabeledGraph σ T
  :=
  ⟨σ, SimpleGraph.Embedding.refl⟩

/-- A subgraph of a labeled graph `G` that still contains all of `G`'s labeled
vertices and embeds `σ` compatibly with `G`'s type embedding. Used to talk
about sub-flags and induced densities. -/
@[ext]
structure LabeledSubgraph (σ : FlagType T) {V : Type} (G : LabeledGraph σ V) where
  subgraph : G.graph.Subgraph
  type_embed : σ ↪g subgraph.coe
  embed_eq : ∀ (t : T), type_embed t = G.type_embed t

/-- The full labeled subgraph of `G` (all vertices and edges of `G`). -/
def LabeledGraph.top (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  {
    subgraph := ⊤
    type_embed := {
      toFun t := ⟨G.type_embed t, trivial⟩
      inj' := by
        intro t₁ t₂ h_eq
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact h_eq
      map_rel_iff' := by
        intro t₁ t₂
        simp only [SimpleGraph.Subgraph.top_adj, Function.Embedding.coeFn_mk,
          SimpleGraph.Subgraph.coe_adj, SimpleGraph.Embedding.map_adj_iff]
    }
    embed_eq := by
      intro t
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  }

lemma LabeledGraph.top_isInduced (G : LabeledGraph σ V)
  : G.top.subgraph.IsInduced := fun _ _ _ _ ↦ id

/-- The minimal labeled subgraph of `G`: exactly the labeled vertices and the
edges of `G` between them. -/
def LabeledGraph.bottom (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  {
    subgraph := {
      verts := G.type_verts
      Adj := fun u v => u ∈ G.type_verts ∧ v ∈ G.type_verts ∧ G.graph.Adj u v
      adj_sub := by tauto
      edge_vert := by tauto
      symm := by tauto
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, G.type_verts_contain t⟩
      inj' := by
        intro t₁ t₂ h_eq
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact h_eq
      map_rel_iff' := by
        simp only [Function.Embedding.coeFn_mk, SimpleGraph.Subgraph.coe_adj,
          SimpleGraph.Embedding.map_adj_iff, G.type_verts_contain, true_and, implies_true]
    }
    embed_eq := by
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, implies_true]
  }

lemma LabeledGraph.bottom_isInduced (G : LabeledGraph σ V)
  : G.bottom.subgraph.IsInduced := by tauto

namespace LabeledSubgraph

/-- `H` is an induced labeled subgraph: its edges are exactly those of `G`
between its vertices. -/
def IsInduced {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : Prop
  :=
  H.subgraph.IsInduced

noncomputable def size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : ℕ
  :=
  Fintype.card H.subgraph.verts

/-- View a labeled subgraph `H` as a `LabeledGraph` in its own right, on the
vertex type `H.subgraph.verts`. -/
@[simps]
def coe {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G)
    : LabeledGraph σ H.subgraph.verts where
  graph := H.subgraph.coe
  type_embed := H.type_embed

omit [Fintype T] in
theorem coe_adj_iff
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) (u v : H.subgraph.verts)
    : H.coe.graph.Adj u v ↔ H.subgraph.Adj u.val v.val
  :=
  rfl.to_iff

omit [Fintype T] in
lemma coe_type_verts_eq
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G)
    : H.coe.type_verts = G.type_verts := by
  dsimp [LabeledGraph.type_verts, LabeledSubgraph.coe]
  ext u
  simp only [Set.image_univ, Set.mem_image, Set.mem_range, exists_exists_eq_and, H.embed_eq]

noncomputable instance labeledSubgraphFintype
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (G : LabeledGraph σ V)
    : Fintype (LabeledSubgraph σ G)
  :=
  let f : LabeledSubgraph σ G → G.graph.Subgraph × (T → V) :=
    fun ⟨G', embed, _⟩ ↦ (G', fun t ↦ embed.toFun t)
  have f_inj : Function.Injective f := by
    rintro ⟨G, φ, embed_eq⟩ ⟨G', φ', embed_eq'⟩ h_eq
    obtain ⟨rfl, _⟩ := Prod.mk.injEq _ _ _ _ ▸ h_eq
    simp only [mk.injEq, true_and, heq_eq_eq]
    ext x; simp only [embed_eq, embed_eq']
  Fintype.ofInjective f f_inj

omit [Fintype T] in
theorem labeledSubgraph_contain_type_verts
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (H : LabeledSubgraph σ G)
    : G.type_verts ⊆ H.subgraph.verts
  := by
  intro v hv
  obtain ⟨t, rfl⟩ := LabeledGraph.mem_type_verts.mp hv
  exact H.embed_eq t ▸ Subtype.coe_prop _

/-- The labeled subgraph of `G` induced on a vertex set `S` that contains all
labeled vertices. The canonical way to cut out a sub-flag on a chosen set. -/
def inducedLabeledSubgraph
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : LabeledSubgraph σ G where
  subgraph := (⊤ : G.graph.Subgraph).induce S
  type_embed := {
    toFun := by
      intro t
      exact ⟨G.type_embed t, h (LabeledGraph.type_verts_contain _ _)⟩
    inj' := by
      intro t u h_tu
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_tu
      exact h_tu
    map_rel_iff' := by
      intro a b
      simp only [Function.Embedding.coeFn_mk, SimpleGraph.Subgraph.coe_adj,
        SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj,
        SimpleGraph.Embedding.map_adj_iff]
      refine ⟨fun h' => h'.2.2, fun h' => ⟨?_, ?_, h'⟩⟩ <;>
        exact h (LabeledGraph.type_verts_contain _ _)
  }
  embed_eq := by
    intro; simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_verts
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).subgraph.verts = S
  := by
  simp only [inducedLabeledSubgraph, SimpleGraph.Subgraph.induce_verts]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).size = Fintype.card S
  := by
  dsimp [LabeledSubgraph.size]
  rw [inducedLabeledSubgraph_verts G S h]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_isInduced
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).IsInduced
  :=
  SimpleGraph.Subgraph.induce_top_isInduced G.graph S

omit [Fintype T] in
theorem inducedLabeledSubgraph_eq
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} {H : LabeledSubgraph σ G} (h_H_ind : H.IsInduced)
    : H = inducedLabeledSubgraph G H.subgraph.verts (labeledSubgraph_contain_type_verts G H)
  := by
  dsimp [inducedLabeledSubgraph]
  congr!
  . exact (h_H_ind.induce_top_verts).symm
  . simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, H.embed_eq]

omit [Fintype T] in
theorem isInduced_exist_induce_set
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) (h_ind : H.IsInduced)
    : ∃ (S : Set V) (h : G.type_verts ⊆ S), inducedLabeledSubgraph G S h = H
  := by
  let S := H.subgraph.verts
  have h : G.type_verts ⊆ S := labeledSubgraph_contain_type_verts G H
  use S, h
  dsimp [inducedLabeledSubgraph]
  have hH_graph : (⊤ : G.graph.Subgraph).induce S = H.subgraph := h_ind.induce_top_verts
  congr
  · funext t
    congr
    exact (H.embed_eq t).symm
  all_goals apply proof_irrel_heq

end LabeledSubgraph

/-- An isomorphism of labeled graphs: a graph isomorphism that maps the labeled
vertices of `G` to those of `G'` respecting the type embeddings. Written
`G ≃f G'`. Flags are isomorphism classes under this relation. -/
@[ext]
structure LabeledGraphIso {σ : FlagType T} {V W : Type}
  (G : LabeledGraph σ V) (G' : LabeledGraph σ W) where
  graph_iso : G.graph ≃g G'.graph
  type_preserve : graph_iso ∘ G.type_embed = G'.type_embed

-- `G ≃f G'` : `G` and `G'` are isomorphic as labeled graphs.
infixl:50 " ≃f " => LabeledGraphIso

def labeledGraphIso_extract_graph
    {σ : FlagType T} {V W : Type} {G : LabeledGraph σ V} {G' : LabeledGraph σ W}
    (_ : G ≃f G') : LabeledGraph σ V := G

omit [Fintype T] in
theorem labeledGraphIso_size_eq
    {σ : FlagType T} {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : LabeledGraph σ V) (G' : LabeledGraph σ W) (h_iso : G ≃f G')
    : G.size = G'.size
  := by
  dsimp [LabeledGraph.size]
  rw [Fintype.card_congr h_iso.graph_iso.toEquiv]

namespace LabeledGraphIso

variable {T : Type} [Fintype T] {σ : FlagType T}
variable {V W U : Type}
variable {G : LabeledGraph σ V} {G' : LabeledGraph σ W} {G'' : LabeledGraph σ U}

/-- Reflexivity of labeled-graph isomorphism. -/
@[refl]
def refl : G ≃f G where
  graph_iso := by rfl
  type_preserve := by ext t; rw [Function.comp_apply, RelIso.refl_apply]

/-- Symmetry of labeled-graph isomorphism. -/
@[symm]
def symm (h : G ≃f G') : G' ≃f G where
  graph_iso := h.graph_iso.symm
  type_preserve := by
    ext t
    rw [←h.type_preserve]
    simp only [Function.comp_apply, RelIso.symm_apply_apply]

/-- Transitivity of labeled-graph isomorphism. -/
def trans (h : G ≃f G') (h' : G' ≃f G'') : G ≃f G'' where
  graph_iso := RelIso.trans h.graph_iso h'.graph_iso
  type_preserve := by
    rw [← h'.type_preserve, ← h.type_preserve]
    simp only [SimpleGraph.Iso.coe_comp]
    exact rfl

def labeledSubgraphIso_cast
    {σ : FlagType T} {G : LabeledGraph σ V} {F : LabeledGraph σ U} {F₁ F₂ : LabeledSubgraph σ G}
    (h_eq : F₁ = F₂) (h_iso : F₁.coe ≃f F) : F₂.coe ≃f F := by
  rw [h_eq] at h_iso
  exact h_iso

def labeledSubgraphIso_eq
  {G : LabeledGraph σ V} {F F' : LabeledSubgraph σ G} (h : F = F') : F.coe ≃f F'.coe := h ▸ LabeledGraphIso.refl

end LabeledGraphIso

/-- Transport a labeled graph along a vertex-set bijection `V ≃ W`, yielding an
isomorphic labeled graph on `W`. -/
def labeledGraphFromVertexIso
  (G : LabeledGraph σ V) (f_iso : V ≃ W) : LabeledGraph σ W
  := {
    graph := SimpleGraph.map f_iso.toEmbedding G.graph
    type_embed := G.type_embed.trans (SimpleGraph.Iso.map f_iso G.graph)
  }

noncomputable def labeledGraphFromVertexIso_iso
  (G : LabeledGraph σ V) (f_iso : V ≃ W) : G ≃f labeledGraphFromVertexIso G f_iso
  := {
    graph_iso := SimpleGraph.Iso.map f_iso G.graph
    type_preserve := by rfl
  }

omit [Fintype T] in
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

omit [Fintype T] in
lemma labeledGraphIso_preserve_type_verts_strict
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    : G₁.type_verts = ⇑φ.graph_iso '' G₀.type_verts
  := by
  dsimp [LabeledGraph.type_verts]
  ext u
  simp only [Set.image_univ, Set.mem_range, Set.mem_image, exists_exists_eq_and]
  constructor <;> {
    intro ⟨t, h⟩
    use t
    have := (funext_iff.mp φ.type_preserve) t
    simp only [Function.comp_apply] at this
    exact this ▸ h
  }

def labeledGraphIso_inducedLabeledSubgraph_from_labeledGraphEmbedding
    {σ : FlagType T} {V W : Type}
    {H : LabeledGraph σ V} {G : LabeledGraph σ W} {G₀ : LabeledSubgraph σ G}
    (h_G₀_ind : G₀.IsInduced) (φ : H ≃f G₀.coe) (V₀ : Set V) (W₀ : Set W) (h : ⇑φ.graph_iso '' V₀ = W₀)
    : (LabeledSubgraph.inducedLabeledSubgraph H (V₀ ∪ H.type_verts) Set.subset_union_right).coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph G (W₀ ∪ G.type_verts) Set.subset_union_right).coe
  :=
  let H' := LabeledSubgraph.inducedLabeledSubgraph H (V₀ ∪ H.type_verts) Set.subset_union_right
  let G' := LabeledSubgraph.inducedLabeledSubgraph G (W₀ ∪ G.type_verts) Set.subset_union_right
  have h_H'_verts : H'.subgraph.verts = V₀ ∪ H.type_verts :=
    LabeledSubgraph.inducedLabeledSubgraph_verts H (V₀ ∪ H.type_verts) Set.subset_union_right
  have h_G'_verts : G'.subgraph.verts = W₀ ∪ G.type_verts :=
    LabeledSubgraph.inducedLabeledSubgraph_verts G (W₀ ∪ G.type_verts) Set.subset_union_right
  have h_image_V₀_type_verts_eq_W₀_type_verts : ⇑φ.graph_iso '' (V₀ ∪ H.type_verts) = W₀ ∪ G.type_verts := by
    calc
      Subtype.val '' (⇑φ.graph_iso '' (V₀ ∪ H.type_verts))
        = (Subtype.val '' (⇑φ.graph_iso '' V₀)) ∪ (Subtype.val '' (⇑φ.graph_iso '' H.type_verts)) := by
          simp only [LabeledSubgraph.coe_graph, Set.image_union]
      _ = W₀ ∪ G.type_verts := by
          rw [h]
          rw [←LabeledSubgraph.coe_type_verts_eq G₀]
          suffices (⇑φ.graph_iso '' H.type_verts) = G₀.coe.type_verts by rw [this]
          rw [labeledGraphIso_preserve_type_verts_strict φ]
  have h_W₀_type_verts_subseteq_G₀_verts : W₀ ∪ G.type_verts ⊆ G₀.subgraph.verts := by
    have h_G_type_verts_subseteq_G₀_type_verts : G.type_verts ⊆ G₀.subgraph.verts :=
      LabeledSubgraph.labeledSubgraph_contain_type_verts G G₀
    have h_W₀_subseteq_G₀_verts : W₀ ⊆ G₀.subgraph.verts := by
      rw [←h]
      suffices ⇑φ.graph_iso '' V₀ ⊆ (Set.univ : Set ↑G₀.subgraph.verts) by {
        simp only [LabeledSubgraph.coe_graph, Set.image_subset_iff, Subtype.coe_preimage_self, this]
      }
      simp only [LabeledSubgraph.coe_graph, Set.subset_univ]
    simp only [Set.union_subset_iff, and_self,
      h_W₀_subseteq_G₀_verts, h_G_type_verts_subseteq_G₀_type_verts]
  let graph_iso : H'.coe.graph ≃g G'.coe.graph := {
    toFun := fun u : ↑H'.subgraph.verts =>
      have h_φ_u : ↑(φ.graph_iso.toFun ↑u) ∈ G'.subgraph.verts := by
        rw [h_G'_verts, ←h_image_V₀_type_verts_eq_W₀_type_verts]
        simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
            Set.mem_image, Set.mem_union, exists_exists_and_eq_and]
        use ↑u
        suffices ↑u ∈ V₀ ∪ H.type_verts by simp only [and_true]; exact this
        rw [←h_H'_verts]
        simp_all only [LabeledSubgraph.coe_graph, Subtype.coe_prop]
      ⟨φ.graph_iso.toFun u.val, h_φ_u⟩
    invFun := fun v : ↑G'.subgraph.verts =>
      have h_v : ↑v ∈ G₀.subgraph.verts := by
        have : ↑v ∈ W₀ ∪ G.type_verts := by simp only [Subtype.coe_prop]
        exact h_W₀_type_verts_subseteq_G₀_verts this
      have h_φ_inv_v : φ.graph_iso.invFun ⟨↑v, h_v⟩ ∈ H'.subgraph.verts := by
        rw [h_H'_verts]
        simp only [LabeledSubgraph.coe_graph, Equiv.invFun_as_coe]
        rw [←Set.mem_image_equiv]
        suffices (Subtype.val ⟨↑v, h_v⟩) ∈ Subtype.val '' (⇑φ.graph_iso.toEquiv '' (V₀ ∪ H.type_verts)) by {
          have h' := @Set.InjOn.mem_image_iff _ _
                        Set.univ
                        (⇑φ.graph_iso.toEquiv '' (V₀ ∪ H.type_verts))
                        (Subtype.val : ↑G₀.subgraph.verts → W) ⟨↑v, h_v⟩
                        (by simp only [Subtype.forall, Subtype.mk.injEq, implies_true, Set.injOn_of_eq_iff_eq])
                        (by simp only [LabeledSubgraph.coe_graph, RelIso.coe_fn_toEquiv, Set.subset_univ])
                        (by simp only [Set.mem_univ])
          rw [←h']
          exact this
        }
        simp only [LabeledSubgraph.coe_graph, RelIso.coe_fn_toEquiv,
          h_image_V₀_type_verts_eq_W₀_type_verts, Subtype.coe_prop]
      ⟨φ.graph_iso.invFun ⟨v.val, h_v⟩, h_φ_inv_v⟩
    left_inv := by
      intro u
      simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
        Subtype.coe_eta, Equiv.invFun_as_coe]
      suffices φ.graph_iso.symm (φ.graph_iso ↑u) = u.val by exact SetCoe.ext this
      simp only [LabeledSubgraph.coe_graph, RelIso.symm_apply_apply]
    right_inv := by
      intro v
      simp only [LabeledSubgraph.coe_graph, Equiv.invFun_as_coe, Equiv.toFun_as_coe,
        Equiv.apply_symm_apply, Subtype.coe_eta]
    map_rel_iff' := by
      intros u v
      simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
        Equiv.invFun_as_coe, Equiv.coe_fn_mk, SimpleGraph.Subgraph.coe_adj]
      dsimp [G',H',LabeledSubgraph.inducedLabeledSubgraph, SimpleGraph.Subgraph.induce]
      simp only [SimpleGraph.Subgraph.top_adj]
      have := @φ.graph_iso.map_rel_iff _ _ _ _ u.val v.val
      rw [←this, ←h_image_V₀_type_verts_eq_W₀_type_verts]
      simp only [LabeledSubgraph.coe_graph, Set.mem_image, Set.mem_union,
        exists_exists_and_eq_and, SimpleGraph.Subgraph.coe_adj,
        Subtype.coe_prop, true_and]
      constructor
      . intro ⟨_, _, h_adj⟩
        rw [h_G₀_ind.adj]
        exact h_adj
      . intro h_adj
        exact ⟨⟨↑u, by show ↑u ∈ V₀ ∪ H.type_verts; rw [←h_H'_verts]; simp only [Subtype.coe_prop], by rfl⟩,
          ⟨↑v, by show ↑v ∈ V₀ ∪ H.type_verts; rw [←h_H'_verts]; simp only [Subtype.coe_prop], by rfl⟩,
          by simp_all only [LabeledSubgraph.coe_graph, SimpleGraph.Subgraph.coe_adj, true_iff, G₀.subgraph.adj_sub]⟩
  }
  have h_type_preserve : graph_iso ∘ H'.coe.type_embed = G'.coe.type_embed := by
    ext u
    dsimp [graph_iso]
    rw [H'.embed_eq u, G'.embed_eq]
    calc
      ↑(φ.graph_iso (H.type_embed u))
      _  = ↑((φ.graph_iso ∘ H.type_embed) u) := by simp only [LabeledSubgraph.coe_graph, Function.comp_apply]
      _  = ↑(G.type_embed u) := by rw [φ.type_preserve]; simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.coe_type_embed, G₀.embed_eq]
      _ = G.type_embed u := by rfl

  { graph_iso := graph_iso, type_preserve := h_type_preserve }

/-- Suggestion: Use `Inhabited` instead of `Nonempty`. -/
def flagEqv {σ : FlagType T} (G G' : LabeledGraph σ V) : Prop
  :=
  Nonempty (G ≃f G')

infixl:50 " ∼f " => flagEqv

omit [Fintype T] in
theorem flagEqv.refl {σ : FlagType T} (G : LabeledGraph σ V)
    : G ∼f G
  :=
  Nonempty.intro LabeledGraphIso.refl

omit [Fintype T] in
theorem flagEqv.symm {σ : FlagType T}
    : ∀ {G G' : LabeledGraph σ V}, G ∼f G' → G' ∼f G
  := by
  intro G G' h
  have G_iso : G ≃f G' := Classical.choice h
  exact Nonempty.intro G_iso.symm

omit [Fintype T] in
theorem flagEqv.trans {σ : FlagType T}
    : ∀ {G G' G'' : LabeledGraph σ V}, G ∼f G' → G' ∼f G'' → G ∼f G''
  := by
  intro G G' G'' h h'
  have G_iso : G ≃f G' := Classical.choice h
  have G'_iso : G' ≃f G'' := Classical.choice h'
  exact Nonempty.intro (G_iso.trans G'_iso)

instance : Trans (@flagEqv T V σ) (@flagEqv T V σ) (@flagEqv T V σ) where
  trans := flagEqv.trans

/-- The setoid on labeled graphs given by labeled-graph isomorphism `∼f`;
its quotient is `Flag σ V`. -/
instance labeledGraphSetoid (σ : FlagType T) (V : Type)
    : Setoid (LabeledGraph σ V)
  where
    r     := flagEqv
    iseqv := {
      refl  := flagEqv.refl,
      symm  := flagEqv.symm,
      trans := flagEqv.trans
    }

/-- A flag of type `σ` on vertex type `V`: an isomorphism class of labeled
graphs. The basic element from which the flag algebra is built. -/
def Flag (σ : FlagType T) (V : Type) : Type :=
  Quotient (labeledGraphSetoid σ V)

noncomputable instance FlagFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (Flag σ V)
  :=
  Quotient.fintype (labeledGraphSetoid σ V)

theorem Flag.type_eq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} (h_Vl_eq : Vl' = Vl) (i : Fin t)
    : Flag σ (Vl' i) = Flag σ (Vl i) := by
  rw [h_Vl_eq]

omit [Fintype T] in
/-- Isomorphic labeled graphs have equal flag (quotient) representatives. -/
theorem flagEqv.sound {σ : FlagType T} {V : Type} {G G' : LabeledGraph σ V} (h : G ∼f G')
    : (⟦G⟧ : Flag σ V) = (⟦G'⟧ : Flag σ V)
  :=
  Quotient.sound h

/-- The flag of the trivial labeled graph (the type `σ` itself); the unit. -/
def emptyFlag (σ : FlagType T) : Flag σ T
  :=
  ⟦emptyLabeledGraph σ⟧

/-- A canonical representative of `G`'s flag on `Fin ℓ` (where `ℓ` is the
number of vertices), obtained via a canonical graph quotient. Lets flags on
arbitrary `ℓ`-element vertex types be compared on a fixed carrier. -/
noncomputable def getCanonicalFlag
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph σ V) (h_V_size : Fintype.card V = ℓ)
    : Flag σ (Fin ℓ)
  :=
  let ⟨Q, iso⟩ := getCanonicalQuotSimpleGraph G.graph h_V_size
  let G' : LabeledGraph σ (Fin ℓ) := {
    graph := Q.out
    type_embed := G.type_embed.trans iso.symm
  }
  ⟦G'⟧

noncomputable def getCanonicalFlag_iso
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph σ V) (h_V_size : Fintype.card V = ℓ)
    : (getCanonicalFlag G h_V_size).out ≃f G
  := by
  dsimp [getCanonicalFlag]
  let ⟨Q, iso⟩ := getCanonicalQuotSimpleGraph G.graph h_V_size
  let G' : LabeledGraph σ (Fin ℓ) := {
    graph := Q.out
    type_embed := G.type_embed.trans iso.symm
  }
  let φ : G' ≃f G := {
    graph_iso := iso
    type_preserve := by
      dsimp [G']
      funext x
      simp only [Function.comp_apply, RelIso.apply_symm_apply iso]
  }
  let φ' : ⟦G'⟧.out ≃f G' := Nonempty.some ((@Quotient.eq_mk_iff_out _ _ ⟦G'⟧ G').mp rfl)
  exact φ'.trans φ

omit [Fintype T] in
lemma cancel_getCanonicalFlag_iso'
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    {G : LabeledGraph σ V} (G₀ G₁ : LabeledSubgraph σ G) (U₀ U₁ : Set V)
    (h_V_size₀ : Fintype.card ↑G₀.subgraph.verts = ℓ) (h_V_size₁ : Fintype.card ↑G₁.subgraph.verts = ℓ)
    (h_U₀ : U₀ ⊆ G₀.subgraph.verts) (h_U₁ : U₁ ⊆ G₁.subgraph.verts)
    (h_G₀_eq_G₁ : G₀ = G₁)
    (h_image₀_eq_image₁ : ⇑(getCanonicalFlag_iso G₀.coe h_V_size₀).graph_iso.symm '' {x : G₀.subgraph.verts | ↑x ∈ U₀}
                          =
                          ⇑(getCanonicalFlag_iso G₁.coe h_V_size₁).graph_iso.symm '' {x : G₁.subgraph.verts | ↑x ∈ U₁})
    : U₀ ⊆ U₁ := by
  intro x₀ h_x₀_in_U₀
  have h_x₀_in_G₀ : x₀ ∈ G₀.subgraph.verts := h_U₀ h_x₀_in_U₀
  let y := (getCanonicalFlag_iso G₀.coe h_V_size₀).graph_iso.symm ⟨x₀, h_x₀_in_G₀⟩
  have h₀ : y ∈ ⇑(getCanonicalFlag_iso G₁.coe h_V_size₁).graph_iso.symm '' {x : G₁.subgraph.verts | ↑x ∈ U₁} := by
    rw [←h_image₀_eq_image₁]
    dsimp [y]
    simp only [Set.mem_image, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, h_x₀_in_U₀]
  simp only [LabeledSubgraph.coe_graph, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left] at h₀
  obtain ⟨x₁, h_x₁_in_U₁, _, h_y_eq⟩ := h₀
  have : x₀ = x₁ := by
    subst h_G₀_eq_G₁
    simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, y]
  rw [this]
  exact h_x₁_in_U₁

omit [Fintype T] in
lemma cancel_getCanonicalFlag_iso
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    {G : LabeledGraph σ V} (G₀ G₁ : LabeledSubgraph σ G) (U₀ U₁ : Set V)
    (h_V_size₀ : Fintype.card ↑G₀.subgraph.verts = ℓ) (h_V_size₁ : Fintype.card ↑G₁.subgraph.verts = ℓ)
    (h_U₀ : U₀ ⊆ G₀.subgraph.verts) (h_U₁ : U₁ ⊆ G₁.subgraph.verts)
    (h_G₀_eq_G₁ : G₀ = G₁)
    (h_image₀_eq_image₁ : ⇑(getCanonicalFlag_iso G₀.coe h_V_size₀).graph_iso.symm '' {x : G₀.subgraph.verts | ↑x ∈ U₀}
                          =
                          ⇑(getCanonicalFlag_iso G₁.coe h_V_size₁).graph_iso.symm '' {x : G₁.subgraph.verts | ↑x ∈ U₁})
    : U₀ = U₁ :=
  have h_subset₀ : U₀ ⊆ U₁ :=
    cancel_getCanonicalFlag_iso' G₀ G₁ U₀ U₁ h_V_size₀ h_V_size₁ h_U₀ h_U₁ h_G₀_eq_G₁ h_image₀_eq_image₁
  have h_subset₁ : U₁ ⊆ U₀ :=
    cancel_getCanonicalFlag_iso' G₁ G₀ U₁ U₀ h_V_size₁ h_V_size₀ h_U₁ h_U₀ (Eq.symm h_G₀_eq_G₁) (Eq.symm h_image₀_eq_image₁)
  Set.Subset.antisymm h_subset₀ h_subset₁

/- FlagList -/

/-! ## Flag lists

Tuples of flags indexed by `Fin t` over a family of vertex types `Vl`, together
with the per-index `Fintype`/`DecidableEq` bookkeeping and operations to
`insert`/`permute` entries. Used to state multi-flag densities. -/

/-- Per-index `Fintype` data for a family of vertex types `Vl : Fin t → Type`. -/
class FintypeList {t : ℕ} (Vl : Fin t → Type) where
  fintype_all : ∀ (i : Fin t), Fintype (Vl i)

/-- Per-index `DecidableEq` data for a family of vertex types `Vl`. -/
class DecidableEqList {t : ℕ} (Vl : Fin t → Type) where
  decidable_eq_all : ∀ (i : Fin t), DecidableEq (Vl i)

noncomputable instance fintype_V {t : ℕ} (Vl : Fin t → Type) [FintypeList Vl] (i : Fin t) : Fintype (Vl i)
  :=
  FintypeList.fintype_all i

noncomputable instance decidable_eq_V {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (i : Fin t) : DecidableEq (Vl i)
  :=
  DecidableEqList.decidable_eq_all i

/-- A `t`-tuple of labeled graphs, the `i`-th living on vertex type `Vl i`. -/
abbrev LabeledGraphList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) := ∀ (i : Fin t), LabeledGraph σ (Vl i)

def labeledGraphToList
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
    : LabeledGraphList σ 1 (fun _ => V)
  :=
  fun _ => G

def labeledGraphPairToList
    {σ : FlagType T} {U V : Type} (G₀ : LabeledGraph σ U) (G₁ : LabeledGraph σ V)
    : LabeledGraphList σ 2 (fun i => match i with | 0 => U | 1 => V)
  :=
  fun i => match i with | 0 => G₀ | 1 => G₁

def labeledGraphTripleToList
    {σ : FlagType T} {U V W : Type} (G₀ : LabeledGraph σ U) (G₁ : LabeledGraph σ V) (G₂ : LabeledGraph σ W)
    : LabeledGraphList σ 3 (fun i => match i with | 0 => U | 1 => V | 2 => W)
  :=
  fun i => match i with | 0 => G₀ | 1 => G₁ | 2 => G₂

notation "[" G "]ᵍ" => (labeledGraphToList G)
notation "[" G₀ "," G₁ "]ᵍ" => (labeledGraphPairToList G₀ G₁)
notation "[" G₀ "," G₁ "," G₂ "]ᵍ" => (labeledGraphTripleToList G₀ G₁ G₂)

/-- Two labeled-graph lists are equivalent (`∼fl`) when they agree entrywise up
to labeled-graph isomorphism. -/
def flagListEqv {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Gl Gl' : LabeledGraphList σ t Vl) : Prop
  :=
  ∀ (i : Fin t), Gl i ∼f Gl' i

infixl:50 " ∼fl " => flagListEqv

omit [Fintype T] in
theorem flagListEqv.refl {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Gl : LabeledGraphList σ t Vl)
    : Gl ∼fl Gl
  :=
  fun i => flagEqv.refl (Gl i)

omit [Fintype T] in
theorem flagListEqv.symm {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    : ∀ {Gl Gl' : LabeledGraphList σ t Vl}, Gl ∼fl Gl' → Gl' ∼fl Gl
  :=
  fun h i => flagEqv.symm (h i)

omit [Fintype T] in
theorem flagListEqv.trans {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    : ∀ {Gl Gl' Gl'' : LabeledGraphList σ t Vl}, Gl ∼fl Gl' → Gl' ∼fl Gl'' → Gl ∼fl Gl''
  :=
  fun h h' i => flagEqv.trans (h i) (h' i)

instance : Trans (@flagListEqv T σ t Vl) (@flagListEqv T σ t Vl) (@flagListEqv T σ t Vl) where
  trans := flagListEqv.trans

/-- The setoid on labeled-graph lists given by entrywise isomorphism `∼fl`. -/
instance labeledGraphListSetoid (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type)
    : Setoid (LabeledGraphList σ t Vl)
  where
    r     := flagListEqv
    iseqv := {
      refl  := flagListEqv.refl,
      symm  := flagListEqv.symm,
      trans := flagListEqv.trans
    }

/-- The quotient of labeled-graph lists by entrywise isomorphism. -/
def QuotLabeledGraphList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) : Type :=
  Quotient (labeledGraphListSetoid σ t Vl)

/-- A `t`-tuple of flags, the `i`-th on vertex type `Vl i`. Equivalent to
`QuotLabeledGraphList` (see `eqv_QuotLabeledGraphList_FlagList`). -/
abbrev FlagList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) := ∀ (i : Fin t), Flag σ (Vl i)

theorem FlagList.type_eq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} (h_Vl_eq : Vl' = Vl)
    : FlagList σ t Vl' = FlagList σ t Vl := by
  rw [h_Vl_eq]

theorem flagList_HEq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_Fl_eq : ∀ (i : Fin t), Fl i = cast (Flag.type_eq h_Vl_eq i) (Fl' i))
    : HEq Fl Fl' := by
  have h_Fl_cast : Fl = cast (FlagList.type_eq h_Vl_eq) Fl' := by
    subst h_Vl_eq
    rw [cast_eq]
    ext1 i
    exact h_Fl_eq i
  subst h_Vl_eq h_Fl_cast
  exact HEq.refl Fl

def flagToList {σ : FlagType T} {V : Type} (F : Flag σ V)
    : FlagList σ 1 (fun _ => V)
  :=
  fun _ => F

def flagPairToList {σ : FlagType T} {V W : Type} (F : Flag σ V) (G : Flag σ W)
    : FlagList σ 2 (fun i => match i with | 0 => V | 1 => W)
  :=
  fun i => match i with | 0 => F | 1 => G

def flagTripleToList {σ : FlagType T} {V W U : Type} (F : Flag σ V) (G : Flag σ W) (H : Flag σ U)
    : FlagList σ 3 (fun i => match i with | 0 => V | 1 => W | 2 => U)
  :=
  fun i => match i with | 0 => F | 1 => G | 2 => H

notation "[" F "]ᶠ" => (flagToList F)
notation "[" F "," G "]ᶠ" => (flagPairToList F G)
notation "[" F "," G "," H "]ᶠ" => (flagTripleToList F G H)

instance fintypeSingletonList {V : Type} [Fintype V]
    : FintypeList (fun (_ : Fin 1) => V)
  :=
  { fintype_all := fun _ ↦ inferInstance }

instance decidableEqSingletonList {V : Type} [DecidableEq V]
    : DecidableEqList (fun (_ : Fin 1) => V)
  :=
  { decidable_eq_all := fun _ ↦ inferInstance }

instance fintypePairList {V W : Type} [Fintype V] [Fintype W]
    : FintypeList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance decidableEqPairList {V W : Type} [DecidableEq V] [DecidableEq W]
    : DecidableEqList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance fintypeTripleList {V W U : Type} [Fintype V] [Fintype W] [Fintype U]
    : FintypeList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

instance decidableEqTripleList {V W U : Type} [DecidableEq V] [DecidableEq W] [DecidableEq U]
    : DecidableEqList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

/-- The equivalence identifying a quotient of labeled-graph lists with a list
of flags: quotients commute with the `Fin t`-indexed product. -/
noncomputable instance eqv_QuotLabeledGraphList_FlagList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type)
    : QuotLabeledGraphList σ t Vl ≃ FlagList σ t Vl where
  toFun := fun Gl (i : Fin t) => ⟦Gl.out i⟧
  invFun := fun Fl => ⟦fun (i : Fin t) => (Fl i).out⟧
  left_inv Gl := by
    rw [← Gl.out_eq]
    apply Quotient.sound
    intro i
    simp only [Quotient.out_eq]
    exact Quotient.mk_out (Gl.out i)
  right_inv Fl := by
    simp only; ext i
    refine (Fl i).out_eq ▸ Quotient.sound (flagEqv.trans ?_ (flagEqv.refl (Quotient.out (Fl i))))
    show _ ∼f Quotient.out (Fl i)
    have : ⟦fun i ↦ Quotient.out (Fl i)⟧.out ∼fl (fun i ↦ Quotient.out (Fl i)) :=
      Quotient.mk_out fun i ↦ (Fl i).out
    exact this i

@[simp]
noncomputable def QuotLabeledGraphList.coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Fl : QuotLabeledGraphList σ t Vl)
    : FlagList σ t Vl
  :=
  (eqv_QuotLabeledGraphList_FlagList σ t Vl).toFun Fl

@[simp]
noncomputable def FlagList.coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Fl : FlagList σ t Vl)
    : QuotLabeledGraphList σ t Vl
  :=
  (eqv_QuotLabeledGraphList_FlagList σ t Vl).invFun Fl

omit [Fintype T] in
theorem list_quot_eq_quot_list_singleton
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
    : ⟦[G]ᵍ⟧ = [⟦G⟧]ᶠ.coe
  :=
  Quotient.sound fun _ ↦ flagEqv.symm (Quotient.mk_out G)

omit [Fintype T] in
theorem list_quot_eq_quot_list_pair
    {σ : FlagType T} {V W : Type} (G : LabeledGraph σ V) (G' : LabeledGraph σ W)
    : ⟦[G, G']ᵍ⟧ = [⟦G⟧, ⟦G'⟧]ᶠ.coe
  :=
  Quotient.sound fun i ↦ match i with
  | 0 => flagEqv.symm (Quotient.mk_out G)
  | 1 => flagEqv.symm (Quotient.mk_out G')

omit [Fintype T] in
theorem list_quot_eq_quot_list_triple
    {σ : FlagType T} {V W U : Type} (G : LabeledGraph σ V) (G' : LabeledGraph σ W) (G'' : LabeledGraph σ U)
    : ⟦[G, G', G'']ᵍ⟧ = [⟦G⟧, ⟦G'⟧, ⟦G''⟧]ᶠ.coe
  :=
  Quotient.sound fun i ↦ match i with
  | 0 => flagEqv.symm (Quotient.mk_out G)
  | 1 => flagEqv.symm (Quotient.mk_out G')
  | 2 => flagEqv.symm (Quotient.mk_out G'')

/- FlagList.insert -/

/-- Extend the vertex-type family `Vl : Fin t → Type` by appending `W` at the
last index, giving `Fin (t + 1) → Type`. The type-level counterpart of
`FlagList.insert`. -/
def listTypeInsert {t : ℕ} (Vl : Fin t → Type) (W : Type)
    : Fin (t + 1) → Type
  :=
  fun i => if h : i.val = t then W else Vl (i.coe h)

theorem listTypeInsert_eq {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val = t)
    : W = listTypeInsert Vl W i
  := by
  simp only [listTypeInsert, hi, ↓reduceDIte]

theorem listTypeInsert_eq' {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Vl (i.coe hi) = listTypeInsert Vl W i
  := by
  simp only [listTypeInsert, hi, ↓reduceDIte]

noncomputable instance fintypeListInsert
    {t : ℕ} (Vl : Fin t → Type) (W : Type) [Fintype W] [FintypeList Vl]
    : @FintypeList (t + 1) (listTypeInsert Vl W) where
  fintype_all i := if h : i.val = t
    then (by rw [← listTypeInsert_eq h]; infer_instance)
    else (by rw [← listTypeInsert_eq' h]; infer_instance)

noncomputable instance decidableEqListInsert
    {t : ℕ} (Vl : Fin t → Type) (W : Type) [DecidableEq W] [DecidableEqList Vl]
    : @DecidableEqList (t + 1) (listTypeInsert Vl W) where
  decidable_eq_all i := if h : i.val = t
    then (by rw [← listTypeInsert_eq h]; infer_instance)
    else (by rw [← listTypeInsert_eq' h]; infer_instance)

omit [Fintype T] in
theorem flag_listTypeInsert_eq {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val = t)
    : Flag σ W = Flag σ (listTypeInsert Vl W i)
  := by
  rw [← listTypeInsert_eq hi]

omit [Fintype T] in
theorem flag_listTypeInsert_eq' {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Flag σ (Vl (i.coe hi)) = Flag σ (listTypeInsert Vl W i)
  := by
  rw [← listTypeInsert_eq' hi]

/-- Append a flag `F` (on `W`) to the end of a flag list `Fl`, producing a
list of length `t + 1`. -/
def FlagList.insert {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    : FlagList σ (t + 1) (listTypeInsert Vl W)
  :=
  fun i => if hi : i.val = t
    then (cast (flag_listTypeInsert_eq hi) F)
    else (cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi)))

omit [Fintype T] in
theorem flaglist_heq_of_idx_eq {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {Fl : FlagList σ t Vl}
    {i i' : Fin t} (h : i = i')
    : HEq (Fl i) (Fl i') := by
  subst h; rfl

noncomputable def flag_heq_to_iso {σ : FlagType T} {W : Type} {V : Type}
    {F₁ : Flag σ W} {F₂ : Flag σ V} (type_eq : W = V) (hHEq : HEq F₁ F₂)
    : F₁.out ≃f F₂.out := by
  subst type_eq hHEq
  rfl

omit [Fintype T] in
theorem insert_new_flag_cast_iso {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (_ : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val = t)
    : Nonempty (F.out ≃f (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F).out) :=
  Nonempty.intro <| flag_heq_to_iso (listTypeInsert_eq hi) (cast_heq _ _).symm

omit [Fintype T] in
theorem insert_preserves_existing_flags {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (_ : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Nonempty ((Fl (i.coe hi)).out ≃f (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))).out) :=
  Nonempty.intro <| flag_heq_to_iso (listTypeInsert_eq' hi) (cast_heq _ _).symm

omit [Fintype T] in
theorem insert_preserves_existing_flags_coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin t} (hi₀ : i.val ≠ t)
    : Nonempty ((Fl i).out ≃f (Fl.insert F i.castSucc).out) := by
  dsimp [FlagList.insert]
  split
  next hi' =>
    have : i % (t + 1) = i := by rw [Nat.mod_succ_eq_iff_lt]; omega
    exact (hi₀ (this ▸ hi')).elim
  next hi =>
    have hi' : i.castSucc.val ≠ t := hi
    let cast_iso := Classical.choice (insert_preserves_existing_flags Fl F hi')
    have idx_heq : HEq (Fl i) (Fl (i.castSucc.coe hi)) := flaglist_heq_of_idx_eq rfl
    exact Nonempty.intro <| (flag_heq_to_iso rfl idx_heq).trans cast_iso

omit [Fintype T] in
theorem cast_preserves_flag_size {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    [FintypeList Vl] [DecidableEqList Vl] [Fintype W] [DecidableEq W]
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val = t)
    : F.out.size = (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F).out.size
  := labeledGraphIso_size_eq F.out
                             (cast (flag_listTypeInsert_eq hi) F).out
                             (Classical.choice (insert_new_flag_cast_iso Fl F hi))

omit [Fintype T] in
theorem cast_preserves_flag_size' {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    [FintypeList Vl] [DecidableEqList Vl] [Fintype W] [DecidableEq W]
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : (Fl (i.coe hi)).out.size = (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))).out.size
  := labeledGraphIso_size_eq (Fl (i.coe hi)).out
                             (cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi))).out
                             (Classical.choice (insert_preserves_existing_flags Fl F hi))


/- FlagList.permute -/

/-- A permutation of `t` indices, used to reorder flag lists. -/
abbrev Perm (t : ℕ) := Fin t ≃ Fin t

/-- Reorder a vertex-type family by a permutation `π`: `i ↦ Vl (π i)`. -/
def listTypePermute {t : ℕ} (Vl : Fin t → Type) (π : Perm t)
    : Fin t → Type
  :=
  fun i => Vl (π i)

noncomputable instance fintypeListPermute
    {t : ℕ} (Vl : Fin t → Type) [FintypeList Vl] (π : Perm t)
    : @FintypeList t (listTypePermute Vl π) where
  fintype_all i := by
    dsimp [listTypePermute]
    infer_instance

noncomputable instance decidableEqListPermute
    {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (π : Perm t)
    : @DecidableEqList t (listTypePermute Vl π) where
  decidable_eq_all i := by
    infer_instance

/-- Reorder a flag list by a permutation `π`: `i ↦ Fl (π i)`. -/
def FlagList.permute {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    (Fl : FlagList σ t Vl) (π : Perm t)
    : FlagList σ t (listTypePermute Vl π)
  :=
  fun i => Fl (π i)

end FlagAlgebras
