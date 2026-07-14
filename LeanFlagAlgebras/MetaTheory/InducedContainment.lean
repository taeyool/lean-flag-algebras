import LeanFlagAlgebras.MetaTheory.LabeledCount
import LeanFlagAlgebras.FlagAlgebra.FlagOperators

/-! # From positive flag density to induced-subgraph containment

Infrastructure for §5 of `MetaTheory/paper.tex` (no direct paper counterpart): the containment
bridge feeding the `K_r`-free heredity step (`forbiddenFree_of_mem` in `GraphClassConstraint`).

Two bridging theorems linking a positive labeled flag density to a concrete
induced-subgraph containment witness.

* `exists_inducing_subset_of_flagDensity₁_ne_zero` turns a nonzero density
  `flagDensity₁ ⟦H⟧ ⟦G⟧ ≠ 0` into an actual vertex subset `S ⊇` the roots of
  `G` whose induced labeled subgraph is isomorphic to `H`.
* `exists_graph_embedding_of_flagDensity₁_ne_zero` specialises this to the
  empty type, extracting a *graph embedding* `D.graph ↪g H.graph` from a
  nonzero density of the unlabelled graph `D` in `H`.  This is exactly the
  fact a downstream `K_r`-free instance feeds into
  `SimpleGraph.CliqueFree.comap`.
-/

open FlagAlgebras LabeledSubgraph
open Classical

namespace FlagAlgebras.MetaTheory

open SimpleGraph

variable {T : Type} [Fintype T] {σ : FlagType T}
variable {V : Type} {G : LabeledGraph σ V}

/-- The canonical embedding of the induced labeled subgraph on `S` (viewed as a
graph in its own right) back into the host graph `G.graph`.  The underlying map
is the subtype value `Subtype.val`, and adjacency is preserved both ways since
both endpoints lie in `S`. -/
private def inducedCoeEmbedding (S : Set V) (h : G.type_verts ⊆ S) :
    (inducedLabeledSubgraph G S h).coe.graph ↪g G.graph where
  toFun := fun u => u.val
  inj' := by
    intro u v huv
    exact Subtype.ext huv
  map_rel_iff' := by
    intro u v
    show G.graph.Adj u.val v.val ↔ (inducedLabeledSubgraph G S h).coe.graph.Adj u v
    rw [LabeledSubgraph.coe_adj_iff]
    show G.graph.Adj u.val v.val ↔ ((⊤ : G.graph.Subgraph).induce S).Adj u.val v.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    constructor
    · intro ha
      refine ⟨?_, ?_, ha⟩
      · have := u.property
        simpa only [inducedLabeledSubgraph_verts] using this
      · have := v.property
        simpa only [inducedLabeledSubgraph_verts] using this
    · intro ha
      exact ha.2.2

/-- **Positive density yields an inducing vertex subset.**  If the labeled flag
density of `Hrep` in `Grep` is nonzero, there is a vertex subset `S` of `Grep`
containing all of `Grep`'s roots whose induced labeled subgraph is isomorphic to
`Hrep`. -/
theorem exists_inducing_subset_of_flagDensity₁_ne_zero {n₀ : ℕ} {σ' : FlagType (Fin n₀)}
    {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (Hrep : LabeledGraph σ' U) (Grep : LabeledGraph σ' W)
    (h : flagDensity₁ (⟦Hrep⟧ : Flag σ' U) (⟦Grep⟧ : Flag σ' W) ≠ 0) :
    ∃ (S : Finset W) (hroot : Grep.type_verts ⊆ (↑S : Set W)),
      Nonempty ((inducedLabeledSubgraph Grep (↑S) hroot).coe ≃f Hrep) := by
  rw [flagDensity₁_eq_subset_count_div] at h
  have hcard : (Finset.univ.filter (fun S : Finset W =>
          ∃ (h : Grep.type_verts ⊆ (↑S : Set W)),
            Nonempty ((inducedLabeledSubgraph Grep (↑S) h).coe ≃f Hrep))).card ≠ 0 := by
    intro hc
    apply h
    rw [hc]
    simp
  have hne := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  obtain ⟨S, hS⟩ := hne
  rw [Finset.mem_filter] at hS
  obtain ⟨_, hroot, hiso⟩ := hS
  exact ⟨S, hroot, hiso⟩

/-- **Positive density yields a graph embedding.**  Specialising to the empty
type: if the density of the unlabelled graph `D` in `H` is nonzero, then
`D.graph` embeds into `H.graph`.  This is the only fact needed to transport
`K_r`-freeness along the embedding via `SimpleGraph.CliqueFree.comap`. -/
theorem exists_graph_embedding_of_flagDensity₁_ne_zero {M N : ℕ}
    (D : LabeledGraph (∅ₜ : FlagType (Fin 0)) (Fin M)) (H : LabeledGraph (∅ₜ : FlagType (Fin 0)) (Fin N))
    (h : flagDensity₁ (⟦D⟧ : Flag ∅ₜ (Fin M)) (⟦H⟧ : Flag ∅ₜ (Fin N)) ≠ 0) :
    Nonempty (D.graph ↪g H.graph) := by
  obtain ⟨S, hroot, ⟨φ⟩⟩ := exists_inducing_subset_of_flagDensity₁_ne_zero D H h
  -- The labeled iso gives a graph iso of the induced subgraph onto `D.graph`.
  let ψ : (inducedLabeledSubgraph H (↑S) hroot).coe.graph ≃g D.graph := φ.graph_iso
  -- Compose `D.graph ≃g induced.coe.graph ↪g H.graph`.
  exact ⟨(inducedCoeEmbedding (↑S) hroot).comp ψ.symm.toEmbedding⟩

end FlagAlgebras.MetaTheory
