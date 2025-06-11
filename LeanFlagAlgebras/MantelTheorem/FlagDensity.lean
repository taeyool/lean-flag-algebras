import «LeanFlagAlgebras».SubflagDensity
import «LeanFlagAlgebras».MantelTheorem.FlagIso

open FlagAlgebras
open LabeledSubgraph
open Classical

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

lemma set_fin3_card_eq_2
    (S : Set (Fin 3)) (hS_card : Fintype.card S = 2)
    : S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2}
  := by
  rw [← Set.toFinset_card, Finset.card_eq_two] at hS_card
  obtain ⟨x, y, h₁, h₂⟩ := hS_card
  match x, y with
  | 0, 0 => contradiction
  | 0, 1 => left; exact Set.toFinset_inj.mp h₂
  | 0, 2 => right; left; exact Set.toFinset_inj.mp h₂
  | 1, 0 => left; rw [Set.pair_comm 0 1]; exact Set.toFinset_inj.mp h₂
  | 1, 1 => contradiction
  | 1, 2 => right; right; exact Set.toFinset_inj.mp h₂
  | 2, 0 => right; left; rw [Set.pair_comm 0 2]; exact Set.toFinset_inj.mp h₂
  | 2, 1 => right; right; rw [Set.pair_comm 1 2]; exact Set.toFinset_inj.mp h₂
  | 2, 2 => contradiction

theorem inducedLabeledSubgraph_emptyType_size_2
    {G : LabeledGraph ∅ₜ (Fin 3)} (H : LabeledSubgraph ∅ₜ G) (h_ind : H.IsInduced) (h_size : H.size = 2)
    : H = inducedLabeledSubgraph_emptyType G {0, 1} ∨
      H = inducedLabeledSubgraph_emptyType G {0, 2} ∨
      H = inducedLabeledSubgraph_emptyType G {1, 2}
  := by
  classical
  have h := IsInduced_exist_induce_set H h_ind
  rcases h with ⟨S, h_type_S, hH⟩
  have hS_card : Fintype.card S = 2 := by
    rw [← inducedLabeledSubgraph_size G S h_type_S, hH, h_size]
  rcases set_fin3_card_eq_2 S hS_card with hS | hS | hS
  · left
    rw [inducedLabeledSubgraph_emptyType, ← hH, ← hS]
  · right; left
    rw [inducedLabeledSubgraph_emptyType, ← hH, ← hS]
  · right; right
    rw [inducedLabeledSubgraph_emptyType, ← hH, ← hS]

def labeledSubgraph_K2_E3 : LabeledSubgraph ∅ₜ E3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType E3_labeledGraph {0, 1}

-- theorem coe_adj_iff
--     {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) (u v : H.subgraph.verts)
--     : H.coe.graph.Adj u v ↔ H.subgraph.Adj u.val v.val
--   :=
--   Eq.to_iff rfl

lemma labeledSubgraphListSet_K2_E3
    : labeledSubgraphListSet (labeledGraphToList K2_labeledGraph) E3_labeledGraph =
      {fun _ => labeledSubgraph_K2_E3}
  := by
  dsimp [labeledSubgraphListSet, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨h_ind, h_iso, _⟩
    funext i
    rw [Fin.fin_one_eq_zero i]
    specialize @h_ind 0
    specialize @h_iso 0
    let φ := h_iso.some
    have h_size : (Hl 0).size = 2 := by
      calc
        _ = K2_labeledGraph.size := labeledGraphIso_size_eq (Hl 0).coe K2_labeledGraph φ
        _ = 2 := K2_labeledGraph_size
    rcases inducedLabeledSubgraph_emptyType_size_2 (Hl 0) h_ind h_size with h | h | h
    · simp only [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, labeledSubgraph_K2_E3]
    · have : (Hl 0).subgraph.Adj 0 2 := by
        have : (Hl 0).subgraph.verts = {0, 2} := by simp [h, inducedLabeledSubgraph_emptyType]
        -- rw [← φ.graph_iso.map_adj_iff]
        rw [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, E3_labeledGraph] at φ
        simp at φ
        sorry
      have : ¬ (Hl 0).subgraph.Adj 0 2 := by
        simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, E3_labeledGraph]
      contradiction
    · sorry
  · sorry

@[simp]
theorem flagDensity_K2_E3
    : flagDensity₁ K2_flag E3_flag = 1 / 3
  := by
  dsimp [K2_flag, E3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  dsimp [labeledSubgraphListDensity]
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
