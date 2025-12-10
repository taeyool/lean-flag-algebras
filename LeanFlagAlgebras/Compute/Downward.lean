import «LeanFlagAlgebras».FlagOperators
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Perm

namespace Compute

open FlagAlgebras

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

instance aaaa
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V] (G : LabeledGraph σ V) [DecidableRel G.graph.Adj]
    {W : Type} [DecidableEq W] [Fintype W] (G' : LabeledGraph σ W) [DecidableRel G'.graph.Adj] :
    Decidable (Nonempty (G ≃f G'))
  := by
  rw [← exists_true_iff_nonempty]
  exact Fintype.decidableExistsFintype

@[ext]
structure LabeledSym2Graph {T : Type} (σ : FlagType T) (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  edges_valid : ∀ e ∈ edges, ¬e.IsDiag
  type_embed : σ ↪g (SimpleGraph.fromEdgeSet edges.toSet)

def LabeledSym2Graph.type_verts
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n) : Finset (Fin n)
  := by
  have : DecidablePred (Membership.mem (G.type_embed '' Set.univ)) := by
    intro i
    simp only [Set.image_univ, Set.mem_range]
    exact Fintype.decidableExistsFintype
  have : Fintype (G.type_embed '' Set.univ) := setFintype _
  exact (G.type_embed '' Set.univ).toFinset

theorem LabeledSym2Graph.mem_type_verts
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n) (t : T) :
    G.type_embed t ∈ G.type_verts
  := by
  simp [type_verts]

def LabeledSym2Graph.toLabeledGraph
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : LabeledSym2Graph σ n) : LabeledGraph σ (Fin n)
  :=
  ⟨SimpleGraph.fromEdgeSet G.edges.toSet, G.type_embed⟩

theorem LabeledSym2Graph.toLabeledGraph_injective
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G₁ G₂ : LabeledSym2Graph σ n)
    (h : G₁.toLabeledGraph = G₂.toLabeledGraph) :
    G₁ = G₂
  := by
  simp only [LabeledSym2Graph.toLabeledGraph, LabeledGraph.mk.injEq] at h
  obtain ⟨h_graph, h_type_embed⟩ := h
  ext e
  · have h : (SimpleGraph.fromEdgeSet G₁.edges).edgeSet = G₁.edges.toSet := by
      simp only [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
      refine Set.disjoint_left.mpr ?_
      intro e' he'
      simp only [Set.mem_setOf_eq]
      exact G₁.edges_valid e' he'
    simp only [h_graph, SimpleGraph.edgeSet_fromEdgeSet] at h
    have h_edges : G₁.edges.toSet = G₂.edges.toSet := by
      rw [← h]
      simp only [sdiff_eq_left]
      refine Set.disjoint_left.mpr ?_
      intro e' he'
      simp only [Set.mem_setOf_eq]
      exact G₂.edges_valid e' he'
    exact Eq.to_iff (congrFun h_edges e)
  · exact h_type_embed

theorem LabeledSym2Graph.toLabeledGraph_adj_iff
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : LabeledSym2Graph σ n) (u v : Fin n) :
    G.toLabeledGraph.graph.Adj u v ↔ Sym2.mk (u, v) ∈ G.edges
  := by
  simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet]
  intro h
  exact G.edges_valid (Sym2.mk (u, v)) h

end Compute

namespace FlagAlgebras
open Compute

noncomputable def LabeledGraph.toLabeledSym2Graph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledGraph σ (Fin n)) : LabeledSym2Graph σ n where
  edges := by
    have : Fintype G.graph.edgeSet := Fintype.ofFinite G.graph.edgeSet
    exact (SimpleGraph.edgeSet G.graph).toFinset
  edges_valid := by
    intro e he
    simp only [Set.mem_toFinset] at he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G.graph he
  type_embed := by
    simp only [Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
    exact G.type_embed

theorem LabeledGraph.toLabeledSym2Graph_toLabeledGraph_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledGraph σ (Fin n)) :
    G.toLabeledSym2Graph.toLabeledGraph = G
  := by
  simp only [LabeledSym2Graph.toLabeledGraph, LabeledGraph.toLabeledSym2Graph]
  congr
  · simp only [Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
  · simp only [eq_mpr_eq_cast, cast_heq]

end FlagAlgebras

namespace Compute
open FlagAlgebras

theorem LabeledSym2Graph.toLabeledGraph_toLabeledSym2Graph_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    G.toLabeledGraph.toLabeledSym2Graph = G
  := by
  simp only [LabeledSym2Graph.toLabeledGraph, LabeledGraph.toLabeledSym2Graph]
  congr
  · simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.toFinset_diff, Finset.toFinset_coe,
    Set.toFinset_setOf, sdiff_eq_left]
    refine Finset.disjoint_left.mpr ?_
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact G.edges_valid e he
  · exact proof_irrel_heq _ _
  · simp only [eq_mpr_eq_cast, cast_heq]

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ} :
    Fintype (LabeledSym2Graph σ n) where
  elems :=
    let S := (@Finset.univ (Finset (Sym2 (Fin n)))).sigma (fun E ↦ (@Finset.univ (σ ↪g SimpleGraph.fromEdgeSet E.toSet) _))
    S.filterMap (fun ⟨E, emb⟩ ↦
      if hE : ∀ e ∈ E, ¬e.IsDiag
      then .some ⟨E, hE, emb⟩
      else .none) (by grind)
  complete e := by
    rcases e with ⟨E, hE, emb⟩
    simp_all

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    DecidablePred fun (H : LabeledSym2Graph σ n) ↦ G.edges = H.edges ∧ G.toLabeledGraph ∼f H.toLabeledGraph
  := by
  intro H
  simp only
  refine @instDecidableAnd _ _ _ ?_
  refine @aaaa T _ σ (Fin n) _ _ _ ?_ (Fin n) _ _ _ ?_
  · intro a b
    rw [LabeledSym2Graph.toLabeledGraph_adj_iff]
    exact Finset.decidableMem s(a, b) G.edges
  · intro a b
    rw [LabeledSym2Graph.toLabeledGraph_adj_iff]
    exact Finset.decidableMem s(a, b) H.edges

def isoLabeledSym2GraphSetWithSameGraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) : Finset (LabeledSym2Graph σ n)
  :=
  { H : LabeledSym2Graph σ n | G.edges = H.edges ∧ G.toLabeledGraph ∼f H.toLabeledGraph }

def isomorphismCount_labeledSym2Graph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) : ℕ
  :=
  (isoLabeledSym2GraphSetWithSameGraph G).card

def downwardNormalizingFactor_labeledSym2Graph
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - n₀).factorial
  isomorphismCount_labeledSym2Graph G / num_of_all_injections

theorem isomorphismCount_eq
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    isomorphismCount G.toLabeledGraph = isomorphismCount_labeledSym2Graph G
  := by
  dsimp only [isomorphismCount, isomorphismCount_labeledSym2Graph]
  symm
  apply Finset.card_nbij LabeledSym2Graph.toLabeledGraph
  · intro G' hG'
    simp [isoLabeledSym2GraphSetWithSameGraph] at hG'
    obtain ⟨h_edges, h_iso⟩ := hG'
    simp only [isoLabeledGraphSetWithSameGraph, Set.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · simp only [LabeledSym2Graph.toLabeledGraph, h_edges]
    · exact h_iso
  · intro G₁ _ G₂ _ h_eq
    exact LabeledSym2Graph.toLabeledGraph_injective G₁ G₂ h_eq
  · intro G' hG'
    simp only [isoLabeledGraphSetWithSameGraph, Set.coe_toFinset, Set.mem_setOf_eq] at hG'
    obtain ⟨h_graph, h_iso⟩ := hG'
    simp [isoLabeledSym2GraphSetWithSameGraph]
    use G'.toLabeledSym2Graph
    rw [LabeledGraph.toLabeledSym2Graph_toLabeledGraph_eq G']
    simp only [and_true, h_iso]
    simp only [LabeledGraph.toLabeledSym2Graph, Lean.Elab.WF.paramLet, eq_mpr_eq_cast]
    simp [LabeledSym2Graph.toLabeledGraph] at h_graph
    ext e
    simp only [Set.mem_toFinset]
    rw [← h_graph]
    simp
    exact fun h ↦ G.edges_valid e h

theorem downwardNormalizingFactor_labeledGraph_eq
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    downwardNormalizingFactor_labeledGraph G.toLabeledGraph = downwardNormalizingFactor_labeledSym2Graph G
  := by
  dsimp only [downwardNormalizingFactor_labeledGraph, downwardNormalizingFactor_labeledSym2Graph]
  congr
  exact isomorphismCount_eq G

abbrev LabeledSym2GraphList
    {T : Type} (σ : FlagType T) (t : ℕ) (Vl : Fin t → ℕ)
  := ∀ (i : Fin t), LabeledSym2Graph σ (Vl i)

def labeledSym2GraphToList
    {T : Type} {σ : FlagType T} {n : ℕ} (G : LabeledSym2Graph σ n)
    : LabeledSym2GraphList σ 1 (fun _ ↦ n)
  :=
  fun _ ↦ G

def labeledSym2GraphPairToList
    {T : Type} {σ : FlagType T} {n₀ n₁ : ℕ} (G₀ : LabeledSym2Graph σ n₀) (G₁ : LabeledSym2Graph σ n₁)
    : LabeledSym2GraphList σ 2 (fun i ↦ match i with | 0 => n₀ | 1 => n₁)
  :=
  fun i ↦ match i with | 0 => G₀ | 1 => G₁

def LabeledSym2GraphList.toLabeledGraphList
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {t : ℕ} {Vl : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) : LabeledGraphList σ t (fun i ↦ Fin (Vl i))
  :=
  fun i ↦ (Hl i).toLabeledGraph

theorem labeledGraphToList_toLabeledGraphList_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n)
    : labeledGraphToList G.toLabeledGraph = (labeledSym2GraphToList G).toLabeledGraphList
  :=
  rfl

lemma labeledGraphList_fin2_type_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n₀ n₁ : ℕ} :
    LabeledGraphList σ 2 (fun (i : Fin 2) ↦ Fin (match i with | 0 => n₀ | 1 => n₁))
    = LabeledGraphList σ 2 (fun (i : Fin 2) ↦ match i with | 0 => Fin n₀ | 1 => Fin n₁)
  := by
  congr
  exact List.ofFn_inj.mp rfl

theorem labeledGraphPairToList_toLabeledGraphList_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n₀ n₁ : ℕ}
    (G₀ : LabeledSym2Graph σ n₀) (G₁ : LabeledSym2Graph σ n₁)
    : labeledGraphPairToList G₀.toLabeledGraph G₁.toLabeledGraph
      = cast labeledGraphList_fin2_type_eq (labeledSym2GraphPairToList G₀ G₁).toLabeledGraphList
  := by
  sorry

@[ext]
structure LabeledSym2InducedSubgraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} (G : LabeledSym2Graph σ n) where
  verts : Finset (Fin n)
  verts_subset : G.type_verts ⊆ verts

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    Fintype (LabeledSym2InducedSubgraph G) where
  elems := (@Finset.univ (Finset (Fin n))).filterMap (fun V ↦
    if hV : G.type_verts ⊆ V
    then .some ⟨V, hV⟩
    else .none) (by grind)
  complete H := by
    simp
    use H.verts
    simp only [exists_prop, and_true]
    exact H.verts_subset

def LabeledSym2InducedSubgraph.edges
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) : Finset (Sym2 (Fin n))
  :=
  G.edges.filter (fun e ↦ ∀ v ∈ e, v ∈ H.verts)

theorem LabeledSym2InducedSubgraph.edges_valid
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) :
    ∀ e ∈ H.edges, ¬e.IsDiag
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact G.edges_valid e he.1

theorem LabeledSym2InducedSubgraph.edges_subset
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) :
    H.edges ⊆ G.edges
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact he.1

def LabeledSym2InducedSubgraph.toLabeledSubraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) : LabeledSubgraph σ G.toLabeledGraph where
  subgraph := {
    verts := H.verts
    Adj := fun u v ↦ Sym2.mk (u, v) ∈ H.edges
    adj_sub := by
      intro u v huv
      simp [LabeledSym2Graph.toLabeledGraph]
      constructor
      · exact H.edges_subset huv
      · exact G.edges_valid (Sym2.mk (u, v)) (H.edges_subset huv)
    edge_vert := by
      intro u v huv
      simp [edges] at huv
      exact huv.2.1
    symm := by
      intro u v huv
      rw [Sym2.eq_swap]
      exact huv
  }
  type_embed := {
    toFun := by
      simp only [Finset.coe_sort_coe]
      intro i
      exact ⟨G.type_embed i, H.verts_subset (G.mem_type_verts i)⟩
    inj' := by
      intro a b hab
      simp at hab
      exact hab
    map_rel_iff' := by
      intro a b
      simp [edges]
      constructor
      · intro ⟨h, _, _⟩
        rw [← G.type_embed.map_rel_iff]
        simp
        refine ⟨h, ?_⟩
        intro hab
        apply G.edges_valid (Sym2.mk (G.type_embed a, G.type_embed b)) h
        exact Sym2.mk_isDiag_iff.mpr (congrArg (G.type_embed) hab)
      · intro h
        constructor
        · rw [← G.type_embed.map_rel_iff] at h
          simp at h
          exact h.1
        · exact ⟨H.verts_subset (G.mem_type_verts a), H.verts_subset (G.mem_type_verts b)⟩
  }
  embed_eq := by simp [LabeledSym2Graph.toLabeledGraph]

theorem LabeledSym2InducedSubgraph.toLabeledSubraph_isInduced
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) :
    H.toLabeledSubraph.IsInduced
  := by
  intro u hu v hv h_adj
  simp [toLabeledSubraph, edges, LabeledSym2Graph.toLabeledGraph] at *
  exact ⟨h_adj.1, hu, hv⟩

abbrev LabeledSym2InducedSubgraphList
    (t : ℕ) {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n)
  := Fin t → LabeledSym2InducedSubgraph G

def predDisjointLabeledSym2InducedSubgraphList
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} (Hl : LabeledSym2InducedSubgraphList t G) : Prop
  :=
  ∀ (i j : Fin t), i ≠ j → ((Hl i).verts \ G.type_verts) ∩ ((Hl j).verts \ G.type_verts) = ∅

def predIsoLabeledSym2Hl
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} {Vl  : Fin t → ℕ} (Hl : LabeledSym2GraphList σ t Vl)
    : LabeledSym2InducedSubgraphList t G → Prop
  := fun Gl ↦
      (∀ (i : Fin t), Nonempty ((Gl i).toLabeledSubraph.coe ≃f (Hl i).toLabeledGraph))
      ∧ predDisjointLabeledSym2InducedSubgraphList Gl

instance
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : LabeledSym2Graph σ n} {Vl  : Fin t → ℕ} (Hl : LabeledSym2GraphList σ t Vl) :
    DecidablePred (fun (Gl : LabeledSym2InducedSubgraphList t G) ↦ predIsoLabeledSym2Hl Hl Gl)
  := fun Gl ↦ by
  refine @instDecidableAnd _ _ ?_ ?_
  · refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    simp only
    have : Fintype (Gl i).toLabeledSubraph.subgraph.verts := by
      simp [LabeledSym2InducedSubgraph.toLabeledSubraph]
      exact (Gl i).verts.fintypeCoeSort
    have : DecidableRel (Gl i).toLabeledSubraph.coe.graph.Adj := by
      simp [LabeledSym2InducedSubgraph.toLabeledSubraph, SimpleGraph.Subgraph.coe]
      intro ⟨a, ha⟩ ⟨b, hb⟩
      exact Finset.decidableMem s(a, b) (Gl i).edges
    have : DecidableRel (Hl i).toLabeledGraph.graph.Adj := by
      intro a b
      simp [LabeledSym2Graph.toLabeledGraph]
      exact instDecidableAnd
    infer_instance
  · simp [predDisjointLabeledSym2InducedSubgraphList]
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro j
    exact instDecidableForall

def finsetOfLabeledSym2InducedSubgraphListIsoHl
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledSym2Graph σ n) {Vl  : Fin t → ℕ} (Hl : LabeledSym2GraphList σ t Vl)
    : Finset (LabeledSym2InducedSubgraphList t G)
  :=
  { Gl | predIsoLabeledSym2Hl Hl Gl }

def labeledSym2InducedSubgraphListCount
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) : ℕ
  :=
  (finsetOfLabeledSym2InducedSubgraphListIsoHl G Hl).card

theorem labeledSubgraphListCount_eq
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) :
    labeledSubgraphListCount Hl.toLabeledGraphList G.toLabeledGraph =
    labeledSym2InducedSubgraphListCount Hl G
  := by
  sorry

def labeledSym2InducedSubgraphListDensity
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) : ℚ
  :=
  let r_list (i : Fin t) := Vl i - Fintype.card T
  labeledSym2InducedSubgraphListCount Hl G / multinomialCoefficient r_list (n - Fintype.card T)

instance
    {t : ℕ} {Vl  : Fin t → ℕ} :
    FintypeList fun i ↦ Fin (Vl i)
  := by
  refine { fintype_all := ?_ }
  intro i
  exact Fin.fintype (Vl i)

instance
    {t : ℕ} {Vl  : Fin t → ℕ} :
    DecidableEqList fun i ↦ Fin (Vl i)
  := by
  refine { decidable_eq_all := ?_ }
  intro i
  exact instDecidableEqFin (Vl i)

theorem labeledSubgraphListDensity_eq
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) :
    labeledSubgraphListDensity Hl.toLabeledGraphList G.toLabeledGraph =
    labeledSym2InducedSubgraphListDensity Hl G
  := by
  dsimp only [labeledSubgraphListDensity, labeledSym2InducedSubgraphListDensity]
  congr!
  · exact labeledSubgraphListCount_eq Hl G
  · simp only [LabeledGraph.size, Fintype.card_fin]
  · simp only [LabeledGraph.size, Fintype.card_fin]

end Compute
