import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # Independent blow-ups (paper §5)

The independent blow-up `G^{\mathbf m}` replaces each vertex `v` of `G` by an independent
clone class of size `m v`, joining the clone classes of `v` and `w` completely whenever
`vw ∈ E(G)` (`def:independent-blow-up`).  We model the vertex set as the sigma type
`Σ v, Fin (m v)` and put `⟨v,i⟩ ∼ ⟨w,j⟩` iff `v ∼ w` in `G` (which is automatically
irreflexive: clones of one vertex are never adjacent).

This file currently contains the construction and its basic combinatorics, including the
fact that blow-ups preserve `K_r`-freeness (the engine behind `cor:clique-free`).  The
quantitative density estimates (`lem:planted-mass`, `lem:planted-estimate`) and the
root-plantability theorem live in later files and build on this construction.
-/

namespace FlagAlgebras.MetaTheory

open SimpleGraph

variable {V : Type*}

/-- The **independent blow-up** `G^{\mathbf m}`: vertex set `Σ v, Fin (m v)`, with two
vertices adjacent iff their base vertices are adjacent in `G`.  Clones of a single vertex
(same base, `G`-non-adjacent to itself) are non-adjacent, i.e. each clone class is an
independent set. -/
def independentBlowup (G : SimpleGraph V) (m : V → ℕ) :
    SimpleGraph (Σ v : V, Fin (m v)) where
  Adj p q := G.Adj p.1 q.1
  symm _ _ h := G.symm h
  loopless p h := G.loopless p.1 h

@[simp]
lemma independentBlowup_adj (G : SimpleGraph V) (m : V → ℕ) (p q : Σ v : V, Fin (m v)) :
    (independentBlowup G m).Adj p q ↔ G.Adj p.1 q.1 := Iff.rfl

/-- The projection `⟨v,i⟩ ↦ v` from the blow-up to `G` is a graph homomorphism. -/
def blowupProj (G : SimpleGraph V) (m : V → ℕ) : independentBlowup G m →g G where
  toFun := Sigma.fst
  map_rel' h := h

/-- On any clique of the blow-up the projection is injective: two adjacent vertices have
adjacent (hence distinct) base vertices, so a clique meets each clone class at most once. -/
lemma blowup_clique_projInjOn (G : SimpleGraph V) (m : V → ℕ)
    {s : Set (Σ v : V, Fin (m v))} (hs : (independentBlowup G m).IsClique s) :
    Set.InjOn Sigma.fst s := by
  intro p hp q hq hpq
  by_contra hne
  have hadj : G.Adj p.1 q.1 := hs hp hq hne
  rw [hpq] at hadj
  exact G.loopless _ hadj

/-- **Blow-ups preserve `K_r`-freeness** (the combinatorial core of `cor:clique-free`): a
clique of the blow-up projects, injectively, to a clique of the same size in `G`. -/
theorem cliqueFree_independentBlowup [DecidableEq V] (G : SimpleGraph V) (m : V → ℕ)
    {r : ℕ} (hG : G.CliqueFree r) : (independentBlowup G m).CliqueFree r := by
  intro s hs
  refine hG (s.image Sigma.fst) ⟨?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    have hpq : p ≠ q := fun h => hab (by rw [h])
    exact hs.isClique hp hq hpq
  · rw [Finset.card_image_of_injOn (blowup_clique_projInjOn G m hs.isClique), hs.card_eq]

end FlagAlgebras.MetaTheory
