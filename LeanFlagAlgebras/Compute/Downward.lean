import «LeanFlagAlgebras».FlagOperators
import «LeanFlagAlgebras».MantelTheorem.FlagDefs
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

@[ext]
structure LabeledSym2Graph {T : Type} (σ : FlagType T) (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  edges_valid : ∀ e ∈ edges, ¬e.IsDiag
  type_embed : σ ↪g (SimpleGraph.fromEdgeSet edges.toSet)

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

end Compute

namespace FlagAlgebras
open Compute

noncomputable def LabeledGraph.toLabeledSym2Graph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
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
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
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
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
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

#eval (@Finset.univ (Perm 3)).card

theorem LabeledSym2Graph_eqv_iff
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G G' : LabeledSym2Graph σ n) :
    (G.toLabeledGraph ∼f G'.toLabeledGraph) ↔
    ∃ (φ : Perm n), G.edges.image (Sym2.map φ) = G'.edges ∧ φ ∘ G.type_embed = G'.type_embed
  := by
  constructor <;> intro h
  · rcases h with ⟨φ, hφ⟩
    use φ
    constructor
    · ext e'
      constructor <;> intro he'
      · simp only [EquivLike.coe_coe, Finset.mem_image] at he'
        rcases he' with ⟨e, he, heq⟩
        subst heq
        have he_vaild : ¬e.IsDiag := G.edges_valid e he
        rcases e with ⟨u, v⟩
        simp_all only [Sym2.isDiag_iff_proj_eq, Sym2.map_pair_eq]
        have hG_uv : G.toLabeledGraph.graph.Adj u v := by
          simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet]
          exact ⟨he, he_vaild⟩
        have hG'_uv : G'.toLabeledGraph.graph.Adj (φ u) (φ v) :=
          (SimpleGraph.Iso.map_adj_iff φ).mpr hG_uv
        simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet] at hG'_uv
        exact hG'_uv.1
      · simp only [EquivLike.coe_coe, Finset.mem_image]
        rcases e' with ⟨u', v'⟩
        have hG'_u'v' : G'.toLabeledGraph.graph.Adj u' v' := by
          simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet]
          exact ⟨he', G'.edges_valid _ he'⟩
        have hG_uv : G.toLabeledGraph.graph.Adj (φ.symm u') (φ.symm v') :=
          (SimpleGraph.Iso.map_adj_iff φ.symm).mpr hG'_u'v'
        simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet] at hG_uv
        use Sym2.mk (φ.symm u', φ.symm v')
        simp_all only [Sym2.map_pair_eq, RelIso.apply_symm_apply, and_self]
    · exact hφ
  · obtain ⟨φ, h_edges, h_type_embed⟩ := h
    apply Nonempty.intro
    exact {
      graph_iso := {
        toFun := φ
        invFun := φ.symm
        left_inv := Equiv.leftInverse_symm φ
        right_inv := Equiv.rightInverse_symm φ
        map_rel_iff' := by
          intro a b
          simp only [Equiv.coe_fn_mk]
          constructor <;> intro h
          · simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet] at *
            obtain ⟨he, hab_neq⟩ := h
            rw [← h_edges] at he
            simp only [Finset.mem_image] at he
            rcases he with ⟨e, he, heq⟩
            have he_ab : e = Sym2.mk (a, b) := by
              rcases e with ⟨u, v⟩
              aesop
            subst he_ab
            exact ⟨he, hab_neq⟩
          · simp [LabeledSym2Graph.toLabeledGraph, SimpleGraph.fromEdgeSet] at *
            obtain ⟨he, hab_neq⟩ := h
            rw [← h_edges]
            simp only [Finset.mem_image]
            constructor
            · use Sym2.mk (a, b)
              simp only [he, Sym2.map_pair_eq, and_self]
            · exact hab_neq
      }
      type_preserve := h_type_embed
    }

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    DecidablePred fun (H : LabeledSym2Graph σ n) ↦ G.edges = H.edges ∧ G.toLabeledGraph ∼f H.toLabeledGraph
  := by
  intro H
  simp only
  refine @instDecidableAnd _ _ _ ?_
  rw [LabeledSym2Graph_eqv_iff]
  exact Fintype.decidableExistsFintype

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

/- Example -/

section

open MantelTheorem

instance : DecidableRel Sₜ.Adj := by
  intro a b
  exact .isFalse (by aesop)

def K3₁_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun x ↦ match x with
      | 0 => 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

#eval isomorphismCount_labeledSym2Graph K3₁_labeledSym2Graph

example : isomorphismCount K3₁_labeledSym2Graph.toLabeledGraph = 3 := by
  rw [isomorphismCount_eq]
  native_decide

#eval downwardNormalizingFactor_labeledSym2Graph K3₁_labeledSym2Graph

example : downwardNormalizingFactor_labeledGraph K3₁_labeledSym2Graph.toLabeledGraph = 1 := by
  rw [downwardNormalizingFactor_labeledGraph_eq]
  native_decide

end

end Compute
