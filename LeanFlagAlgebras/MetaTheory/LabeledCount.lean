import LeanFlagAlgebras.MetaTheory.DensityBridge

/-! # Labeled graph count as a vertex-subset count

Infrastructure for §5 `lem:planted-estimate` of `MetaTheory/paper.tex` (no direct paper
counterpart): it recasts flag density as a subset-sampling probability, the form the planted
blow-up estimate samples against.

This file relates the abstract `labeledGraphCount H G` (the number of induced
labeled subgraphs of `G` that are isomorphic to `H`) to a concrete count of
vertex subsets of `G`: those subsets `S` that contain all of `G`'s roots and
whose induced labeled subgraph is isomorphic to `H`.  The bijection sends an
induced labeled subgraph to its (finite) vertex set, and its inverse cuts out
the induced labeled subgraph on a chosen subset. -/

open Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open LabeledSubgraph

variable {T : Type} [Fintype T] {σ : FlagType T}
variable {V : Type} [Fintype V] [DecidableEq V] {U : Type}

omit [Fintype T] [Fintype V] [DecidableEq V] in
/-- `inducedLabeledSubgraph` depends only on the vertex set `S`, not on the
proof that `S` contains the roots. -/
private theorem inducedLabeledSubgraph_congr (G : LabeledGraph σ V)
    {S₁ S₂ : Set V} (hS : S₁ = S₂)
    (h₁ : G.type_verts ⊆ S₁) (h₂ : G.type_verts ⊆ S₂) :
    inducedLabeledSubgraph G S₁ h₁ = inducedLabeledSubgraph G S₂ h₂ := by
  subst hS; rfl

/-- `labeledGraphCount H G` (the number of induced labelled subgraphs of `G`
isomorphic to `H`) equals the number of vertex subsets `S ⊇` the roots whose
induced labelled subgraph is `≃f H`. -/
theorem labeledGraphCount_eq_subset_count (H : LabeledGraph σ U) (G : LabeledGraph σ V) :
    labeledGraphCount H G =
      (Finset.univ.filter (fun S : Finset V =>
        ∃ (h : G.type_verts ⊆ (↑S : Set V)),
          Nonempty ((LabeledSubgraph.inducedLabeledSubgraph G (↑S) h).coe ≃f H))).card := by
  -- Unfold `labeledGraphCount` to a `Set.toFinset.card`.
  show (({ G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }).toFinset).card = _
  refine Finset.card_bij
    (i := fun G' _ => G'.subgraph.verts.toFinset)
    ?hi ?inj ?surj
  · -- maps into the filter set
    intro G' hG'
    rw [Set.mem_toFinset] at hG'
    obtain ⟨hind, hiso⟩ := hG'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- `↑(G'.subgraph.verts.toFinset) = G'.subgraph.verts`
    have hcoe : (↑(G'.subgraph.verts.toFinset) : Set V) = G'.subgraph.verts :=
      Set.coe_toFinset _
    -- roots are contained in the verts
    have hsub : G.type_verts ⊆ (↑(G'.subgraph.verts.toFinset) : Set V) := by
      rw [hcoe]; exact labeledSubgraph_contain_type_verts G G'
    refine ⟨hsub, ?_⟩
    -- the induced subgraph on `verts` is `G'` itself
    have heq : inducedLabeledSubgraph G (↑(G'.subgraph.verts.toFinset) : Set V) hsub = G' := by
      rw [inducedLabeledSubgraph_congr G hcoe hsub (labeledSubgraph_contain_type_verts G G')]
      exact (inducedLabeledSubgraph_eq hind).symm
    rw [heq]; exact hiso
  · -- injective
    intro G'₁ h₁ G'₂ h₂ hverts
    rw [Set.mem_toFinset] at h₁ h₂
    have hv : G'₁.subgraph.verts = G'₂.subgraph.verts := by
      have := congrArg (fun (s : Finset V) => (↑s : Set V)) hverts
      simpa only [Set.coe_toFinset] using this
    rw [inducedLabeledSubgraph_eq h₁.1, inducedLabeledSubgraph_eq h₂.1]
    exact inducedLabeledSubgraph_congr G hv _ _
  · -- surjective
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨_, h, hiso⟩ := hS
    refine ⟨inducedLabeledSubgraph G (↑S : Set V) h, ?_, ?_⟩
    · rw [Set.mem_toFinset]
      exact ⟨inducedLabeledSubgraph_isInduced G _ h, hiso⟩
    · -- `i` of this subgraph is `S`
      simp only [inducedLabeledSubgraph_verts G _ h, Finset.toFinset_coe]

/-- **Flag density as a subset-sampling probability**: the density of `H` in `G` is the
fraction of `(|H|−k)`-vertex subsets (together with the roots) that induce a copy of `H`.
This is the form the planted blow-up estimate samples against. -/
theorem flagDensity₁_eq_subset_count_div {n₀ : ℕ} {σ' : FlagType (Fin n₀)}
    {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (Hrep : LabeledGraph σ' U) (Grep : LabeledGraph σ' W) :
    flagDensity₁ (⟦Hrep⟧ : Flag σ' U) (⟦Grep⟧ : Flag σ' W)
      = ((Finset.univ.filter (fun S : Finset W =>
          ∃ (h : Grep.type_verts ⊆ (↑S : Set W)),
            Nonempty ((inducedLabeledSubgraph Grep (↑S) h).coe ≃f Hrep))).card : ℚ)
        / ((Grep.size - σ'.size).choose (Hrep.size - σ'.size)) := by
  rw [flagDensity₁_eq_count_div, labeledGraphCount_eq_subset_count]

end FlagAlgebras.MetaTheory
