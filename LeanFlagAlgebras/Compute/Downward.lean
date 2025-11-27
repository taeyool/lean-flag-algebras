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

structure LabeledSym2Graph {T : Type} (σ : FlagType T) (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  edges_valid : ∀ e ∈ edges, ¬e.IsDiag
  type_embed : σ ↪g (SimpleGraph.fromEdgeSet edges.toSet)

def LabeledSym2Graph.toLabeledGraph
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : LabeledSym2Graph σ n) : LabeledGraph σ (Fin n)
  :=
  ⟨SimpleGraph.fromEdgeSet G.edges.toSet, G.type_embed⟩

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
  sorry

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

def isomorphismCount'
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) : ℕ
  :=
  (isoLabeledSym2GraphSetWithSameGraph G).card

theorem isomorphismCount_eq
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    isomorphismCount G.toLabeledGraph = isomorphismCount' G
  := by
  sorry

def singletonType : FlagType (Fin 1) := SimpleGraph.emptyGraph (Fin 1)

alias Sₜ := singletonType

instance : DecidableRel Sₜ.Adj := by
  simp [DecidableRel]
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

#eval! isomorphismCount' K3₁_labeledSym2Graph

end Compute
