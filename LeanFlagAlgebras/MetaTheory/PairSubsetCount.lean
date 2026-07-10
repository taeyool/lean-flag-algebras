import LeanFlagAlgebras.MetaTheory.LabeledCount
import Mathlib.Tactic.FinCases

/-! # Pair-flag density as a vertex-subset-pair count

The two-flag analogue of `MetaTheory/LabeledCount.lean` (infrastructure for the `φ_W`
construction in `MetaTheory/GraphonHom.lean`; no direct `paper.tex` display).  The pair
density `flagDensity₂ F₁ F₂ G` is by definition the list density of `[F₁, F₂]` in `G`: the
number of pairs of induced labelled subgraphs of `G`, isomorphic to `F₁` and `F₂` respectively
and disjoint outside the roots, normalised by the multinomial coefficient counting the ways to
place the two sets of non-root vertices.  This file recasts it as a concrete count over
**pairs of vertex subsets**:

* `flagDensity₂_eq_count_div` — the pair density as
  `labeledGraphListCount [F₁rep, F₂rep] G / multinomialCoefficient ![|F₁|−k, |F₂|−k] (|G|−k)`
  (the two-flag analogue of `DensityBridge.flagDensity₁_eq_count_div`).
* `labeledGraphListCount_pair_eq_subset_count` — the list count as the number of pairs
  `(S₁, S₂)` of vertex subsets, each containing the roots, disjoint outside them, whose
  induced labelled subgraphs are isomorphic to the two prescribed flags (the two-flag
  analogue of `LabeledCount.labeledGraphCount_eq_subset_count`; the bijection sends a
  subgraph pair to its pair of vertex sets).
* `flagDensity₂_eq_subset_count_div` — the composition of the two.

The proofs mirror the singleton case: `labeledGraphPairToList` packages the two
representatives as a `LabeledGraphList` over `Fin 2`, and the bijection argument of
`labeledGraphCount_eq_subset_count` runs coordinatewise.
-/

open Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open LabeledSubgraph

variable {n₀ : ℕ} {σ' : FlagType (Fin n₀)}
variable {U₁ U₂ W : Type}
variable [Fintype U₁] [Fintype U₂] [Fintype W]
variable [DecidableEq U₁] [DecidableEq U₂] [DecidableEq W]

/-- The filter condition of the subset-pair count: both subsets contain the roots, they are
disjoint outside the roots, and each induces a labelled subgraph isomorphic to the
corresponding flag representative. -/
def IsInducedPairOn (F₁rep : LabeledGraph σ' U₁) (F₂rep : LabeledGraph σ' U₂)
    (Grep : LabeledGraph σ' W) (P : Finset W × Finset W) : Prop :=
  ((↑P.1 \ Grep.type_verts) ∩ (↑P.2 \ Grep.type_verts) = (∅ : Set W))
  ∧ (∃ (h : Grep.type_verts ⊆ (↑P.1 : Set W)),
      Nonempty ((inducedLabeledSubgraph Grep (↑P.1) h).coe ≃f F₁rep))
  ∧ (∃ (h : Grep.type_verts ⊆ (↑P.2 : Set W)),
      Nonempty ((inducedLabeledSubgraph Grep (↑P.2) h).coe ≃f F₂rep))

/-- **Pair density as a card ratio** (the two-flag analogue of
`flagDensity₁_eq_count_div`): the pair density of `F₁, F₂` in `G` is the count of realizing
disjoint subgraph pairs over the multinomial coefficient.

Proof route: unfold `flagDensity₂ = flagListDensity [·,·]ᶠ` through
`quotLabeledGraphListDensity`/`labeledGraphListDensityLifted` down to
`labeledGraphListDensity (labeledGraphPairToList F₁rep F₂rep) Grep`, transporting the chosen
`Quotient.out` representatives via the isomorphism-invariance of the list count
(`SubflagListDensity`, the `h_count` invariance used around its line 305 and the
`labeledGraphPairToList` plumbing around line 547).  The `r_list` of the pair list is
`![F₁rep.size − σ'.size, F₂rep.size − σ'.size]`. -/
theorem flagDensity₂_eq_count_div
    (F₁rep : LabeledGraph σ' U₁) (F₂rep : LabeledGraph σ' U₂) (Grep : LabeledGraph σ' W) :
    flagDensity₂ (⟦F₁rep⟧ : Flag σ' U₁) (⟦F₂rep⟧ : Flag σ' U₂) (⟦Grep⟧ : Flag σ' W)
      = (labeledGraphListCount (labeledGraphPairToList F₁rep F₂rep) Grep : ℚ)
        / (multinomialCoefficient
            ![F₁rep.size - σ'.size, F₂rep.size - σ'.size] (Grep.size - σ'.size)) := by
  rw [← labeledGraphListDensity_eq_flagDensity₂]
  unfold labeledGraphListDensity
  congr 2

omit [Fintype U₁] [Fintype U₂] [DecidableEq U₁] [DecidableEq U₂] [Fintype W] [DecidableEq W] in
/-- `inducedLabeledSubgraph` depends only on the vertex set `S`, not on the
proof that `S` contains the roots (private copy of `LabeledCount.inducedLabeledSubgraph_congr`,
inaccessible here since that lemma is private to its file). -/
private theorem inducedLabeledSubgraph_congr' (G : LabeledGraph σ' W)
    {S₁ S₂ : Set W} (hS : S₁ = S₂)
    (h₁ : G.type_verts ⊆ S₁) (h₂ : G.type_verts ⊆ S₂) :
    inducedLabeledSubgraph G S₁ h₁ = inducedLabeledSubgraph G S₂ h₂ := by
  subst hS; rfl

omit [Fintype U₁] [Fintype U₂] [DecidableEq U₁] [DecidableEq U₂] in
/-- **The pair list count as a subset-pair count** (the two-flag analogue of
`labeledGraphCount_eq_subset_count`): realizing subgraph pairs correspond bijectively to
pairs of vertex subsets, via `Gl ↦ ((Gl 0).subgraph.verts.toFinset, (Gl 1).subgraph.verts.toFinset)`,
with inverse cutting out the induced labelled subgraphs (`inducedLabeledSubgraph`).
Disjointness-outside-roots of the list (`predDisjointLabeledSubgraphList`) matches the
disjointness clause of `IsInducedPairOn` coordinatewise. -/
theorem labeledGraphListCount_pair_eq_subset_count
    (F₁rep : LabeledGraph σ' U₁) (F₂rep : LabeledGraph σ' U₂) (Grep : LabeledGraph σ' W) :
    labeledGraphListCount (labeledGraphPairToList F₁rep F₂rep) Grep
      = (Finset.univ.filter
          (fun P : Finset W × Finset W => IsInducedPairOn F₁rep F₂rep Grep P)).card := by
  unfold labeledGraphListCount
  letI hFT : Fintype (setOfLabeledSubgraphListIsoHl Grep (labeledGraphPairToList F₁rep F₂rep)) :=
    Fintype.ofFinite _
  refine Finset.card_bij
    (i := fun Gl _ => ((Gl 0).subgraph.verts.toFinset, (Gl 1).subgraph.verts.toFinset))
    ?hi ?inj ?surj
  · -- maps into the filter set
    intro Gl hGl
    rw [Set.mem_toFinset] at hGl
    obtain ⟨hind, hiso, hdisj⟩ := hGl
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcoe0 : (↑((Gl 0).subgraph.verts.toFinset) : Set W) = (Gl 0).subgraph.verts :=
      Set.coe_toFinset _
    have hcoe1 : (↑((Gl 1).subgraph.verts.toFinset) : Set W) = (Gl 1).subgraph.verts :=
      Set.coe_toFinset _
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoe0, hcoe1]
      exact hdisj 0 1 (by decide)
    · have hsub : Grep.type_verts ⊆ (↑((Gl 0).subgraph.verts.toFinset) : Set W) := by
        rw [hcoe0]; exact labeledSubgraph_contain_type_verts Grep (Gl 0)
      refine ⟨hsub, ?_⟩
      have heq : inducedLabeledSubgraph Grep (↑((Gl 0).subgraph.verts.toFinset) : Set W) hsub
          = Gl 0 := by
        rw [inducedLabeledSubgraph_congr' Grep hcoe0 hsub
          (labeledSubgraph_contain_type_verts Grep (Gl 0))]
        exact (inducedLabeledSubgraph_eq (hind 0)).symm
      rw [heq]; exact hiso 0
    · have hsub : Grep.type_verts ⊆ (↑((Gl 1).subgraph.verts.toFinset) : Set W) := by
        rw [hcoe1]; exact labeledSubgraph_contain_type_verts Grep (Gl 1)
      refine ⟨hsub, ?_⟩
      have heq : inducedLabeledSubgraph Grep (↑((Gl 1).subgraph.verts.toFinset) : Set W) hsub
          = Gl 1 := by
        rw [inducedLabeledSubgraph_congr' Grep hcoe1 hsub
          (labeledSubgraph_contain_type_verts Grep (Gl 1))]
        exact (inducedLabeledSubgraph_eq (hind 1)).symm
      rw [heq]; exact hiso 1
  · -- injective
    intro Gl₁ hm₁ Gl₂ hm₂ heq
    rw [Set.mem_toFinset] at hm₁ hm₂
    obtain ⟨hind₁, _⟩ := hm₁
    obtain ⟨hind₂, _⟩ := hm₂
    have h0 : (Gl₁ 0).subgraph.verts.toFinset = (Gl₂ 0).subgraph.verts.toFinset :=
      congrArg Prod.fst heq
    have h1 : (Gl₁ 1).subgraph.verts.toFinset = (Gl₂ 1).subgraph.verts.toFinset :=
      congrArg Prod.snd heq
    funext i
    fin_cases i
    · have hv : (Gl₁ 0).subgraph.verts = (Gl₂ 0).subgraph.verts := by
        have := congrArg (fun (s : Finset W) => (↑s : Set W)) h0
        simpa only [Set.coe_toFinset] using this
      show Gl₁ 0 = Gl₂ 0
      rw [inducedLabeledSubgraph_eq (hind₁ 0), inducedLabeledSubgraph_eq (hind₂ 0)]
      exact inducedLabeledSubgraph_congr' Grep hv _ _
    · have hv : (Gl₁ 1).subgraph.verts = (Gl₂ 1).subgraph.verts := by
        have := congrArg (fun (s : Finset W) => (↑s : Set W)) h1
        simpa only [Set.coe_toFinset] using this
      show Gl₁ 1 = Gl₂ 1
      rw [inducedLabeledSubgraph_eq (hind₁ 1), inducedLabeledSubgraph_eq (hind₂ 1)]
      exact inducedLabeledSubgraph_congr' Grep hv _ _
  · -- surjective
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨-, hdisj, ⟨h1, hiso1⟩, ⟨h2, hiso2⟩⟩ := hP
    set A := inducedLabeledSubgraph Grep (↑P.1 : Set W) h1 with hA
    set B := inducedLabeledSubgraph Grep (↑P.2 : Set W) h2 with hB
    refine ⟨![A, B], ?_, ?_⟩
    · rw [Set.mem_toFinset]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · exact inducedLabeledSubgraph_isInduced Grep _ h1
        · exact inducedLabeledSubgraph_isInduced Grep _ h2
      · intro i
        fin_cases i
        · exact hiso1
        · exact hiso2
      · intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
          | exact absurd rfl hij
          | (show (A.subgraph.verts \ Grep.type_verts) ∩ (B.subgraph.verts \ Grep.type_verts) = ∅
             rw [inducedLabeledSubgraph_verts Grep (↑P.1 : Set W) h1,
               inducedLabeledSubgraph_verts Grep (↑P.2 : Set W) h2]
             exact hdisj)
          | (show (B.subgraph.verts \ Grep.type_verts) ∩ (A.subgraph.verts \ Grep.type_verts) = ∅
             rw [inducedLabeledSubgraph_verts Grep (↑P.1 : Set W) h1,
               inducedLabeledSubgraph_verts Grep (↑P.2 : Set W) h2]
             rw [Set.inter_comm]
             exact hdisj)
    · show ((![A, B] 0).subgraph.verts.toFinset, (![A, B] 1).subgraph.verts.toFinset) = P
      show (A.subgraph.verts.toFinset, B.subgraph.verts.toFinset) = P
      rw [inducedLabeledSubgraph_verts Grep (↑P.1 : Set W) h1,
        inducedLabeledSubgraph_verts Grep (↑P.2 : Set W) h2]
      simp only [Finset.toFinset_coe]

/-- **Pair-flag density as a subset-pair-sampling ratio**: the density of `(F₁, F₂)` in `G`
is the number of realizing subset pairs over the multinomial coefficient. -/
theorem flagDensity₂_eq_subset_count_div
    (F₁rep : LabeledGraph σ' U₁) (F₂rep : LabeledGraph σ' U₂) (Grep : LabeledGraph σ' W) :
    flagDensity₂ (⟦F₁rep⟧ : Flag σ' U₁) (⟦F₂rep⟧ : Flag σ' U₂) (⟦Grep⟧ : Flag σ' W)
      = ((Finset.univ.filter
          (fun P : Finset W × Finset W => IsInducedPairOn F₁rep F₂rep Grep P)).card : ℚ)
        / (multinomialCoefficient
            ![F₁rep.size - σ'.size, F₂rep.size - σ'.size] (Grep.size - σ'.size)) := by
  rw [flagDensity₂_eq_count_div, labeledGraphListCount_pair_eq_subset_count]

end FlagAlgebras.MetaTheory
