import «LeanFlagAlgebras».SubflagDensity
import «LeanFlagAlgebras».MantelTheorem.FlagIso

open FlagAlgebras
open LabeledSubgraph

namespace MantelTheorem

/- single flag densities -/

lemma labeledSubgraphListSet_K2_O3
    : labeledSubgraphListSet (labeledGraphToList K2_labeledGraph) O3_labeledGraph = ∅
  := by
  sorry

@[simp]
theorem flagDensity_K2_O3
    : flagDensity₁ K2_flag O3_flag = 0
  := by
  dsimp [K2_flag, O3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  dsimp [labeledSubgraphListDensity]
  simp only [emptyType_size, tsub_zero]
  let num := labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) O3_labeledGraph
  let denom := multinomialCoefficient (fun i ↦ (labeledGraphToList K2_labeledGraph i).size) O3_labeledGraph.size
  show (num : ℚ) / (denom : ℚ) = 0
  have h₁ : num = 0 := by
    dsimp [num, labeledSubgraphListCount]
    simp only [labeledSubgraphListSet_K2_O3, Set.toFinset_empty, Finset.card_empty]
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  rfl

def inducedLabeledSubgraph_emptyType
    {V : Type} (G : LabeledGraph ∅ₜ V) (S : Set V)
    : LabeledSubgraph ∅ₜ G
  :=
  have h : G.type_verts ⊆ S := by simp [LabeledGraph.type_verts]
  inducedLabeledSubgraph G S h

theorem inducedLabeledSubgraph_emptyType_cases
    (G : LabeledGraph ∅ₜ (Fin 3)) (H : LabeledSubgraph ∅ₜ G) (h_ind : H.IsInduced) (h_size : H.size = 2)
    : H = inducedLabeledSubgraph_emptyType G {0, 1} ∨
      H = inducedLabeledSubgraph_emptyType G {0, 2} ∨
      H = inducedLabeledSubgraph_emptyType G {1, 2}
  := by
  have h := IsInduced_exist_induce_set H h_ind
  rcases h with ⟨S, hS, hH⟩
  sorry

def labeledSubgraph_K2_E3 : LabeledSubgraph ∅ₜ E3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType E3_labeledGraph {0, 1}

lemma labeledSubgraphListSet_K2_E3
    : labeledSubgraphListSet (labeledGraphToList K2_labeledGraph) E3_labeledGraph =
      {fun _ => labeledSubgraph_K2_E3}
  := by
  dsimp [labeledSubgraphListSet, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨h₁, h₂, h₃⟩
    funext i
    rw [Fin.fin_one_eq_zero i]
    specialize @h₁ 0
    specialize @h₂ 0
    sorry
  · sorry

@[simp]
theorem flagDensity_K2_E3
    : flagDensity₁ K2_flag E3_flag = 1 / 3
  := by
  dsimp [K2_flag, E3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  dsimp [labeledSubgraphListDensity]
  simp only [emptyType_size, tsub_zero]
  let num := labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) E3_labeledGraph
  let denom := multinomialCoefficient (fun i ↦ (labeledGraphToList K2_labeledGraph i).size) O3_labeledGraph.size
  show (num : ℚ) / (denom : ℚ) = 1 / 3
  have h₁ : num = 1 := by
    dsimp [num, labeledSubgraphListCount]
    simp only [labeledSubgraphListSet_K2_E3, Set.toFinset_singleton, Finset.card_singleton]
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  rfl

@[simp]
theorem flagDensity_K2_P3
    : flagDensity₁ K2_flag P3_flag = 2 / 3
  := by
  sorry

@[simp]
theorem flagDensity_K2_K3
    : flagDensity₁ K2_flag K3_flag = 1
  := by
  sorry

/- flag pair densities -/

@[simp]
theorem flagDensity_O2₁_O2₁_O3₁
    : flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_O3₁
    : flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_O3₁
    : flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁
    : flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁
    : flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁
    : flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁'
    : flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁'
    : flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁'
    : flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁
    : flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁
    : flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁
    : flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁'
    : flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁'
    : flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁'
    : flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_O2₁_K3₁
    : flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_O2₁_K2₁_K3₁
    : flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0
  := by
  sorry

@[simp]
theorem flagDensity_K2₁_K2₁_K3₁
    : flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1
  := by
  sorry

end MantelTheorem
