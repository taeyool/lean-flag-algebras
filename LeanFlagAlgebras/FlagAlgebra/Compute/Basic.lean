import «LeanFlagAlgebras».FlagAlgebra.FlagOperators
import Mathlib.Data.Fintype.Perm

/-! # Computable flag/graph representations

Computable counterparts of the abstract `LabeledGraph`/`Flag` definitions, used by the loader
macros to build flag data at elaboration time. Graphs are encoded by an explicit edge
`Finset (Sym2 (Fin n))` (`Sym2Graph`, `Sym2LabeledGraph`) rather than an opaque adjacency
relation, making `Fintype`/`DecidableEq`/`Decidable` instances and the flag-isomorphism quotient
(`Sym2EmptyTypedFlag`, `Sym2Flag`) effectively computable. Round-trip lemmas (`toLabeledGraph`
↔ `toSym2Graph`, `toFlag` ↔ `toSym2Flag`) certify these mirror the abstract types faithfully.
-/

namespace FlagAlgebras.Compute

open SimpleGraph

instance
    {V : Type*} [DecidableEq V] [Fintype V]
    {W : Type*} [DecidableEq W] [Fintype W] :
    Fintype (V ↪ W) where
  elems := ((@Finset.univ (V → W)).filterMap fun f ↦
    if h : Function.Injective f
    then Option.some ⟨f, h⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.toFun, e.inj'

instance
    {V : Type*} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
    Fintype (G₁ ↪g G₂) where
  elems := ((@Finset.univ (V ↪ W)).filterMap fun e ↦
    if h : ∀ u v, G₂.Adj (e u) (e v) ↔ G₁.Adj u v
    then Option.some ⟨e, h _ _⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.toEmbedding, fun _ _ ↦ e.map_rel_iff

instance
    {V : Type} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
    Fintype (G₁ ≃g G₂) where
  elems := ((@Finset.univ (V ≃ W)).filterMap fun e ↦
      if h : ∀ u v, G₂.Adj (e u) (e v) ↔ G₁.Adj u v
      then Option.some ⟨e, h _ _⟩
      else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.toEquiv, fun _ _ ↦ e.map_rel_iff

instance
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V] (G : LabeledGraph σ V) [DecidableRel G.graph.Adj]
    {W : Type} [DecidableEq W] [Fintype W] (G' : LabeledGraph σ W) [DecidableRel G'.graph.Adj] :
    Fintype (G ≃f G') where
  elems := ((@Finset.univ (G.graph ≃g G'.graph)).filterMap fun e ↦
    if h : e.toFun ∘ G.type_embed = G'.type_embed
    then Option.some ⟨e, h⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Finset.mem_filterMap, Finset.mem_univ,
      Option.dite_none_right_eq_some, Option.some.injEq, true_and]
    use e.graph_iso, e.type_preserve

instance
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V] (G : LabeledGraph σ V) [DecidableRel G.graph.Adj]
    {W : Type} [DecidableEq W] [Fintype W] (G' : LabeledGraph σ W) [DecidableRel G'.graph.Adj] :
    Decidable (Nonempty (G ≃f G'))
  := by
  rw [← exists_true_iff_nonempty]
  exact Fintype.decidableExistsFintype

instance
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V]
    (G G' : LabeledGraph σ V) [DecidableRel G.graph.Adj] [DecidableRel G'.graph.Adj] :
    Decidable (G ∼f G')
  := by
  rw [flagEqv]
  infer_instance

/- Empty-typed flags --/

/-! ## Empty-typed flags -/

/-- Computable encoding of a simple graph on `Fin n`: an explicit set of non-loop edges. -/
@[ext]
structure Sym2Graph (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  edges_valid : ∀ e ∈ edges, ¬e.IsDiag

/-- Decodes a `Sym2Graph` to the abstract empty-type `LabeledGraph`. -/
def Sym2Graph.toLabeledGraph
    {n : ℕ} (G : Sym2Graph n) : LabeledGraph ∅ₜ (Fin n)
  :=
  ⟨fromEdgeSet (SetLike.coe G.edges), RelEmbedding.ofIsEmpty _ _⟩

theorem Sym2Graph.toLabeledGraph_injective
    {n : ℕ} (G₁ G₂ : Sym2Graph n)
    (h : G₁.toLabeledGraph = G₂.toLabeledGraph) :
    G₁ = G₂
  := by
  simp only [Sym2Graph.toLabeledGraph, LabeledGraph.mk.injEq] at h
  obtain ⟨h_graph, _⟩ := h
  ext e
  have h : (fromEdgeSet G₁.edges).edgeSet = SetLike.coe G₁.edges := by
    simp only [edgeSet_fromEdgeSet, sdiff_eq_left]
    refine Set.disjoint_left.mpr ?_
    intro e' he'
    simp only [Sym2.mem_diagSet_iff_isDiag]
    exact G₁.edges_valid e' he'
  simp only [h_graph, edgeSet_fromEdgeSet] at h
  have h_edges : SetLike.coe G₁.edges = SetLike.coe G₂.edges := by
    rw [← h]
    simp only [sdiff_eq_left]
    refine Set.disjoint_left.mpr ?_
    intro e' he'
    simp only [Sym2.mem_diagSet_iff_isDiag]
    exact G₂.edges_valid e' he'
  exact Eq.to_iff (congrFun h_edges e)

theorem Sym2Graph.toLabeledGraph_adj_iff
  {n : ℕ} (G : Sym2Graph n) (u v : Fin n) :
  G.toLabeledGraph.graph.Adj u v ↔ Sym2.mk (u, v) ∈ G.edges
  := by
  simp [Sym2Graph.toLabeledGraph, fromEdgeSet]
  intro h
  exact G.edges_valid (Sym2.mk (u, v)) h

instance
    {n : ℕ} :
    Fintype (Sym2Graph n) where
  elems := ((@Finset.univ (Finset (Sym2 (Fin n)))).filterMap fun edges ↦
    if h : ∀ e ∈ edges, ¬e.IsDiag
    then Option.some ⟨edges, h⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.edges, e.edges_valid

instance
  {n : ℕ} (G : Sym2Graph n) :
    DecidableRel G.toLabeledGraph.graph.Adj
  := by
  intro a b
  rw [G.toLabeledGraph_adj_iff]
  exact Finset.decidableMem s(a, b) G.edges

/-- Encodes an abstract empty-type `LabeledGraph` back into a computable `Sym2Graph`. -/
noncomputable def _root_.FlagAlgebras.LabeledGraph.toSym2Graph
  {n : ℕ} (G : LabeledGraph ∅ₜ (Fin n)) : Sym2Graph n where
  edges := by
    have : Fintype G.graph.edgeSet := Fintype.ofFinite G.graph.edgeSet
    exact (SimpleGraph.edgeSet G.graph).toFinset
  edges_valid := by
    intro e he
    simp at he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G.graph he

theorem _root_.FlagAlgebras.LabeledGraph.toSym2Graph_toLabeledGraph_eq
  {n : ℕ} (G : LabeledGraph ∅ₜ (Fin n)) :
    G.toSym2Graph.toLabeledGraph = G
  := by
  simp only [Sym2Graph.toLabeledGraph, LabeledGraph.toSym2Graph]
  congr!
  · simp only [Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
  · rename_i h
    rw [h, heq_eq_eq]
    ext v
    exact Fin.elim0 v

theorem Sym2Graph.toLabeledGraph_toSym2Graph_eq
  {n : ℕ} (G : Sym2Graph n) :
    G.toLabeledGraph.toSym2Graph = G
  := by
  simp only [Sym2Graph.toLabeledGraph, LabeledGraph.toSym2Graph]
  congr
  simp only [edgeSet_fromEdgeSet, Set.toFinset_diff, Finset.toFinset_coe, sdiff_eq_left]
  refine Finset.disjoint_left.mpr ?_
  intro e he
  simp only [Set.mem_toFinset, Sym2.mem_diagSet_iff_isDiag]
  exact G.edges_valid e he

/-- Flag-equivalence of computable graphs: their decoded labeled graphs are flag-isomorphic. -/
def Sym2GraphEqv {n : ℕ} (G G' : Sym2Graph n) : Prop :=
  G.toLabeledGraph ∼f G'.toLabeledGraph

-- Notation `G ∼sf G'` for computable flag-equivalence of `Sym2Graph`s.
infixl:50 " ∼sf " => Sym2GraphEqv

instance
    {n : ℕ} (G G' : Sym2Graph n) :
    Decidable (G ∼sf G')
  := by
  rw [Sym2GraphEqv]
  infer_instance

theorem sym2Graph_card_edges_eq_of_eqv
    {n : ℕ} {G G' : Sym2Graph n} (h : G ∼sf G') :
    G.edges.card = G'.edges.card
  := by
  simp [Sym2GraphEqv, Sym2Graph.toLabeledGraph] at h
  have φ := h.some.graph_iso
  simp at φ
  have hG : (fromEdgeSet (SetLike.coe G.edges)).edgeFinset = G.edges := by
    ext e
    simp only [edgeFinset, edgeSet_fromEdgeSet, Set.mem_toFinset]
    constructor
    · intro he
      exact he.1
    · intro he
      exact ⟨he, by
        intro hdiag
        exact (G.edges_valid e he) (by simpa [Sym2.mem_diagSet_iff_isDiag] using hdiag)⟩
  have hG' : (fromEdgeSet (SetLike.coe G'.edges)).edgeFinset = G'.edges := by
    ext e
    simp only [edgeFinset, edgeSet_fromEdgeSet, Set.mem_toFinset]
    constructor
    · intro he
      exact he.1
    · intro he
      exact ⟨he, by
        intro hdiag
        exact (G'.edges_valid e he) (by simpa [Sym2.mem_diagSet_iff_isDiag] using hdiag)⟩
  calc
    G.edges.card = (fromEdgeSet (SetLike.coe G.edges)).edgeFinset.card := by rw [hG]
    _ = (fromEdgeSet (SetLike.coe G'.edges)).edgeFinset.card := φ.card_edgeFinset_eq
    _ = G'.edges.card := by rw [hG']

theorem Sym2GraphEqv.refl (G : Sym2Graph n) : G ∼sf G :=
  flagEqv.refl _

theorem Sym2GraphEqv.symm {G G' : Sym2Graph n} (h : G ∼sf G') : G' ∼sf G :=
  flagEqv.symm h

theorem Sym2GraphEqv.trans {G G' G'' : Sym2Graph n} (h₁ : G ∼sf G') (h₂ : G' ∼sf G'') : G ∼sf G'' :=
  flagEqv.trans h₁ h₂

/-- The setoid on `Sym2Graph n` given by computable flag-equivalence. -/
instance Sym2GraphSetoid (n : ℕ) : Setoid (Sym2Graph n) where
  r     := Sym2GraphEqv
  iseqv := {
    refl  := Sym2GraphEqv.refl,
    symm  := Sym2GraphEqv.symm,
    trans := Sym2GraphEqv.trans
  }

/-- Computable counterpart of `Flag ∅ₜ (Fin n)`: the quotient of `Sym2Graph n` by
flag-equivalence, with effective `Fintype`/`DecidableEq` instances. -/
def Sym2EmptyTypedFlag (n : ℕ) : Type :=
  Quotient (Sym2GraphSetoid n)

instance
    {n : ℕ} :
    Fintype (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.fintype _ _ (Sym2GraphSetoid n) ?_
  intro G G'
  show Decidable (G ∼sf G')
  infer_instance

instance
    {n : ℕ} :
    DecidableEq (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  show Decidable (G ∼sf G')
  infer_instance

def Sym2Graph.toFlag
    {n : ℕ} (G : Sym2Graph n) : Flag ∅ₜ (Fin n)
  :=
  ⟦G.toLabeledGraph⟧

theorem Sym2Graph.toFlag_respect_eqv
    {n : ℕ} (G G' : Sym2Graph n) (h : G ∼sf G') :
    G.toFlag = G'.toFlag
  :=
  Quotient.sound h

/-- Decodes a computable empty-typed flag to the abstract `Flag ∅ₜ (Fin n)`. -/
def Sym2EmptyTypedFlag.toFlag
    {n : ℕ} (F : Sym2EmptyTypedFlag n) : Flag ∅ₜ (Fin n)
  :=
  Quotient.lift Sym2Graph.toFlag Sym2Graph.toFlag_respect_eqv F

theorem Sym2EmptyTypedFlag.toFlag_injective
    {n : ℕ} (F F' : Sym2EmptyTypedFlag n) (h : F.toFlag = F'.toFlag) :
    F = F'
  := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  rcases Quotient.exists_rep F' with ⟨G', rfl⟩
  apply Quotient.sound
  dsimp [Sym2EmptyTypedFlag.toFlag, Sym2Graph.toFlag] at h
  have h' : G.toLabeledGraph ∼f G'.toLabeledGraph := Quotient.exact h
  exact h'

noncomputable def _root_.FlagAlgebras.LabeledGraph.toSym2EmptyTypedFlag
    {n : ℕ} (G : LabeledGraph ∅ₜ (Fin n)) : Sym2EmptyTypedFlag n
  :=
  ⟦G.toSym2Graph⟧

theorem _root_.FlagAlgebras.LabeledGraph.toSym2EmptyTypedFlag_respect_eqv
    {n : ℕ} (G G' : LabeledGraph ∅ₜ (Fin n)) (h : G ∼f G') :
    G.toSym2EmptyTypedFlag = G'.toSym2EmptyTypedFlag
  := by
  dsimp only [LabeledGraph.toSym2EmptyTypedFlag]
  apply Quotient.sound
  show G.toSym2Graph ∼sf G'.toSym2Graph
  dsimp only [Sym2GraphEqv]
  rw [G.toSym2Graph_toLabeledGraph_eq, G'.toSym2Graph_toLabeledGraph_eq]
  exact h

/-- Encodes an abstract `Flag ∅ₜ (Fin n)` into the computable empty-typed flag quotient. -/
noncomputable def _root_.FlagAlgebras.Flag.toSym2EmptyTypedFlag
    {n : ℕ} (F : Flag ∅ₜ (Fin n)) : Sym2EmptyTypedFlag n
  :=
  Quotient.lift LabeledGraph.toSym2EmptyTypedFlag LabeledGraph.toSym2EmptyTypedFlag_respect_eqv F

/-- Round-trip: encoding then decoding an empty-typed flag is the identity. -/
theorem _root_.FlagAlgebras.Flag.toSym2EmptyTypedFlag_toFlag_eq
    {n : ℕ} (F : Flag ∅ₜ (Fin n)) :
    F.toSym2EmptyTypedFlag.toFlag = F
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  apply Quotient.sound
  rw [F.toSym2Graph_toLabeledGraph_eq]

/- Non-empty-typed flags --/

/-! ## Non-empty-typed flags -/

/-- Computable encoding of a flag type `σ` on `Fin k`.

This is the same edge-set representation as `Sym2Graph`; the separate name records that the
graph is being used as the type of a flag. -/
abbrev Sym2FlagType (k : ℕ) := Sym2Graph k

namespace Sym2FlagType

@[ext]
theorem ext {k : ℕ} {σ τ : Sym2FlagType k} (h : σ.edges = τ.edges) : σ = τ :=
  Sym2Graph.ext h

/-- Decodes a `Sym2FlagType` to the abstract `FlagType (Fin k)`. -/
def toFlagType {k : ℕ} (σ : Sym2FlagType k) : FlagType (Fin k)
  :=
  fromEdgeSet (SetLike.coe σ.edges)

theorem toFlagType_adj_iff
  {k : ℕ} (σ : Sym2FlagType k) (u v : Fin k) :
  σ.toFlagType.Adj u v ↔ Sym2.mk (u, v) ∈ σ.edges
  := by
  simp [Sym2FlagType.toFlagType]
  intro h
  exact σ.edges_valid (Sym2.mk (u, v)) h

end Sym2FlagType

/-- Computable encoding of a `σ`-typed labeled graph on `Fin n`: an edge set together with a
graph embedding of the (decoded) type `σ` into it. -/
@[ext]
structure Sym2LabeledGraph {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  edges_valid : ∀ e ∈ edges, ¬e.IsDiag
  type_embed : (fromEdgeSet (SetLike.coe σ.edges)) ↪g (fromEdgeSet (SetLike.coe edges))

def Sym2LabeledGraph.type_verts
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Finset (Fin n)
  := by
  have : DecidablePred (Membership.mem (G.type_embed '' Set.univ)) := by
    intro i
    simp only [Set.image_univ, Set.mem_range]
    exact Fintype.decidableExistsFintype
  have : Fintype (G.type_embed '' Set.univ) := setFintype _
  exact (G.type_embed '' Set.univ).toFinset

theorem Sym2LabeledGraph.mem_type_verts
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) (t : Fin k) :
    G.type_embed t ∈ G.type_verts
  := by
  simp [type_verts]

/-- Decodes a `Sym2LabeledGraph` to the abstract `σ`-typed `LabeledGraph`. -/
def Sym2LabeledGraph.toLabeledGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : LabeledGraph (fromEdgeSet (SetLike.coe σ.edges)) (Fin n)
  :=
  ⟨fromEdgeSet (SetLike.coe G.edges), G.type_embed⟩

theorem Sym2LabeledGraph.toLabeledGraph_type_embed_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) (t : Fin k) :
    G.toLabeledGraph.type_embed t = G.type_embed t
  := by
  simp [Sym2LabeledGraph.toLabeledGraph]

theorem Sym2LabeledGraph.toLabeledGraph_type_verts_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    G.toLabeledGraph.type_verts = G.type_verts
  := by
  simp [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.type_verts, Sym2LabeledGraph.type_verts]

theorem Sym2LabeledGraph.toLabeledGraph_injective
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G₁ G₂ : Sym2LabeledGraph σ n)
    (h : G₁.toLabeledGraph = G₂.toLabeledGraph) :
    G₁ = G₂
  := by
  simp only [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.mk.injEq] at h
  obtain ⟨h_graph, h_type_embed⟩ := h
  ext e
  · have h : (fromEdgeSet G₁.edges).edgeSet = SetLike.coe G₁.edges := by
      simp only [edgeSet_fromEdgeSet, sdiff_eq_left]
      refine Set.disjoint_left.mpr ?_
      intro e' he'
      simp only [Sym2.mem_diagSet_iff_isDiag]
      exact G₁.edges_valid e' he'
    simp only [h_graph, edgeSet_fromEdgeSet] at h
    have h_edges : SetLike.coe G₁.edges = SetLike.coe G₂.edges := by
      rw [← h]
      simp only [sdiff_eq_left]
      refine Set.disjoint_left.mpr ?_
      intro e' he'
      simp only [Sym2.mem_diagSet_iff_isDiag]
      exact G₂.edges_valid e' he'
    exact Eq.to_iff (congrFun h_edges e)
  · exact h_type_embed

theorem Sym2LabeledGraph.toLabeledGraph_adj_iff
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) (u v : Fin n) :
    G.toLabeledGraph.graph.Adj u v ↔ Sym2.mk (u, v) ∈ G.edges
  := by
  simp [Sym2LabeledGraph.toLabeledGraph, fromEdgeSet]
  intro h
  exact G.edges_valid (Sym2.mk (u, v)) h

instance
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    Fintype (Sym2LabeledGraph σ n) where
  elems :=
    let S := (@Finset.univ (Finset (Sym2 (Fin n)))).sigma (fun E ↦ (@Finset.univ ((fromEdgeSet (SetLike.coe σ.edges)) ↪g fromEdgeSet (SetLike.coe E)) _))
    S.filterMap (fun ⟨E, emb⟩ ↦
      if hE : ∀ e ∈ E, ¬e.IsDiag
      then .some ⟨E, hE, emb⟩
      else .none) (by grind)
  complete e := by
    rcases e with ⟨E, hE, emb⟩
    simp_all

instance
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    DecidableRel G.toLabeledGraph.graph.Adj
  := by
  intro a b
  rw [G.toLabeledGraph_adj_iff]
  exact Finset.decidableMem s(a, b) G.edges

/-- Encodes an abstract `σ`-typed `LabeledGraph` back into a computable `Sym2LabeledGraph`. -/
noncomputable def _root_.FlagAlgebras.LabeledGraph.toSym2LabeledGraph
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
  (G : LabeledGraph (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) (Fin n)) : Sym2LabeledGraph σ n where
  edges := by
    have : Fintype G.graph.edgeSet := Fintype.ofFinite G.graph.edgeSet
    exact (SimpleGraph.edgeSet G.graph).toFinset
  edges_valid := by
    intro e he
    simp at he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G.graph he
  type_embed := by
    simp
    exact G.type_embed

theorem _root_.FlagAlgebras.LabeledGraph.toSym2LabeledGraph_toLabeledGraph_eq
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
  (G : LabeledGraph (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) (Fin n)) :
    G.toSym2LabeledGraph.toLabeledGraph = G
  := by
  simp only [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.toSym2LabeledGraph]
  congr
  · simp only [Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
  · simp only [eq_mpr_eq_cast, cast_heq]

theorem Sym2LabeledGraph.toLabeledGraph_toSym2LabeledGraph_eq
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    G.toLabeledGraph.toSym2LabeledGraph = G
  := by
  simp only [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.toSym2LabeledGraph]
  congr
  · simp only [edgeSet_fromEdgeSet, Set.toFinset_diff, Finset.toFinset_coe, sdiff_eq_left]
    refine Finset.disjoint_left.mpr ?_
    intro e he
    simp only [Set.mem_toFinset, Sym2.mem_diagSet_iff_isDiag]
    exact G.edges_valid e he
  · exact proof_irrel_heq _ _
  · simp only [eq_mpr_eq_cast, cast_heq]

/-- Flag-equivalence of computable `σ`-typed labeled graphs (via their decoded forms). -/
def sym2LabeledGraphEqv
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G G' : Sym2LabeledGraph σ n) : Prop
  :=
  G.toLabeledGraph ∼f G'.toLabeledGraph

-- Notation `G ∼sf G'` reused for computable flag-equivalence of `Sym2LabeledGraph`s.
infixl:50 " ∼sf " => sym2LabeledGraphEqv

instance
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G G' : Sym2LabeledGraph σ n) :
    Decidable (G ∼sf G')
  := by
  dsimp [sym2LabeledGraphEqv]
  infer_instance

theorem sym2LabeledGraph_card_edges_eq_of_eqv
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G G' : Sym2LabeledGraph σ n} (h : G ∼sf G') :
    G.edges.card = G'.edges.card
  := by
  simp [sym2LabeledGraphEqv, Sym2LabeledGraph.toLabeledGraph] at h
  have φ := h.some.graph_iso
  simp at φ
  have hG : (fromEdgeSet (SetLike.coe G.edges)).edgeFinset = G.edges := by
    ext e
    simp only [edgeFinset, edgeSet_fromEdgeSet, Set.mem_toFinset]
    constructor
    · intro he
      exact he.1
    · intro he
      exact ⟨he, by
        intro hdiag
        exact (G.edges_valid e he) (by simpa [Sym2.mem_diagSet_iff_isDiag] using hdiag)⟩
  have hG' : (fromEdgeSet (SetLike.coe G'.edges)).edgeFinset = G'.edges := by
    ext e
    simp only [edgeFinset, edgeSet_fromEdgeSet, Set.mem_toFinset]
    constructor
    · intro he
      exact he.1
    · intro he
      exact ⟨he, by
        intro hdiag
        exact (G'.edges_valid e he) (by simpa [Sym2.mem_diagSet_iff_isDiag] using hdiag)⟩
  calc
    G.edges.card = (fromEdgeSet (SetLike.coe G.edges)).edgeFinset.card := by rw [hG]
    _ = (fromEdgeSet (SetLike.coe G'.edges)).edgeFinset.card := φ.card_edgeFinset_eq
    _ = G'.edges.card := by rw [hG']

theorem sym2LabeledGraphEqv.refl
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    G ∼sf G
  :=
  flagEqv.refl _

theorem sym2LabeledGraphEqv.symm
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G G' : Sym2LabeledGraph σ n}
    (h : G ∼sf G') :
    G' ∼sf G
  :=
  flagEqv.symm h

theorem sym2LabeledGraphEqv.trans
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G G' G'' : Sym2LabeledGraph σ n}
    (h₁ : G ∼sf G') (h₂ : G' ∼sf G'') :
    G ∼sf G''
  :=
  flagEqv.trans h₁ h₂

/-- The setoid on `Sym2LabeledGraph σ n` given by computable flag-equivalence. -/
instance sym2LabeledGraphSetoid
  {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    Setoid (Sym2LabeledGraph σ n)
  where
    r     := sym2LabeledGraphEqv
    iseqv := {
      refl  := sym2LabeledGraphEqv.refl,
      symm  := sym2LabeledGraphEqv.symm,
      trans := sym2LabeledGraphEqv.trans
    }

/-- Computable counterpart of `Flag σ (Fin n)`: the quotient of `Sym2LabeledGraph σ n` by
flag-equivalence, with effective `Fintype`/`DecidableEq` instances. -/
def Sym2Flag {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) : Type :=
  Quotient (sym2LabeledGraphSetoid σ n)

instance
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    Fintype (Sym2Flag σ n)
  := by
  refine @Quotient.fintype _ _ (sym2LabeledGraphSetoid σ n) ?_
  intro G G'
  show Decidable (G ∼sf G')
  infer_instance

instance
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    DecidableEq (Sym2Flag σ n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  show Decidable (G ∼sf G')
  infer_instance

def Sym2LabeledGraph.toFlag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Flag (fromEdgeSet (SetLike.coe σ.edges)) (Fin n)
  :=
  ⟦G.toLabeledGraph⟧

theorem Sym2LabeledGraph.toFlag_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G G' : Sym2LabeledGraph σ n) (h : G ∼sf G') :
    G.toFlag = G'.toFlag
  :=
  Quotient.sound h

/-- Decodes a computable `Sym2Flag` to the abstract `Flag σ (Fin n)`. -/
def Sym2Flag.toFlag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : Sym2Flag σ n) :
    Flag (fromEdgeSet (SetLike.coe σ.edges)) (Fin n)
  :=
  Quotient.lift Sym2LabeledGraph.toFlag Sym2LabeledGraph.toFlag_respect_eqv G

theorem Sym2Flag.toFlag_injective
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (F F' : Sym2Flag σ n) (h : F.toFlag = F'.toFlag) :
    F = F'
  := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  rcases Quotient.exists_rep F' with ⟨G', rfl⟩
  apply Quotient.sound
  dsimp [Sym2Flag.toFlag, Sym2LabeledGraph.toFlag] at h
  have h' : G.toLabeledGraph ∼f G'.toLabeledGraph := Quotient.exact h
  exact h'

noncomputable def _root_.FlagAlgebras.LabeledGraph.toSym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledGraph (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) (Fin n)) : Sym2Flag σ n
  :=
  ⟦G.toSym2LabeledGraph⟧

theorem _root_.FlagAlgebras.LabeledGraph.toSym2Flag_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G G' : LabeledGraph (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) (Fin n)) (h : G ∼f G') :
    G.toSym2Flag = G'.toSym2Flag
  := by
  dsimp only [LabeledGraph.toSym2Flag]
  apply Quotient.sound
  show G.toSym2LabeledGraph ∼sf G'.toSym2LabeledGraph
  dsimp only [sym2LabeledGraphEqv]
  rw [G.toSym2LabeledGraph_toLabeledGraph_eq, G'.toSym2LabeledGraph_toLabeledGraph_eq]
  exact h

/-- Encodes an abstract `Flag σ (Fin n)` into the computable `Sym2Flag` quotient. -/
noncomputable def _root_.FlagAlgebras.Flag.toSym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (F : Flag (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) (Fin n)) : Sym2Flag σ n
  :=
  Quotient.lift LabeledGraph.toSym2Flag LabeledGraph.toSym2Flag_respect_eqv F

/-- Round-trip: encoding an abstract `Flag σ` then decoding is the identity. -/
theorem _root_.FlagAlgebras.Flag.toSym2Flag_toFlag_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (F : Flag (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) (Fin n)) :
    F.toSym2Flag.toFlag = F
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  apply Quotient.sound
  rw [F.toSym2LabeledGraph_toLabeledGraph_eq]

/-- Round-trip: decoding a computable `Sym2Flag` then re-encoding is the identity. -/
theorem Sym2Flag.toFlag_toSym2Flag_eq
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (F : Sym2Flag σ n) :
    F.toFlag.toSym2Flag = F
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  apply Quotient.sound
  rw [F.toLabeledGraph_toSym2LabeledGraph_eq]

-- theorem Sym2Flag.toFlag_univ_eq_univ
--   {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
--     Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } (Finset.univ : Finset (Sym2Flag σ n))
--   = (Finset.univ : Finset (Flag (fromEdgeSet (SetLike.coe σ.edges)) (Fin n)))
--   := by
--   ext F
--   simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, iff_true]
--   use F.toSym2Flag
--   exact Flag.toSym2Flag_toFlag_eq F

end FlagAlgebras.Compute
