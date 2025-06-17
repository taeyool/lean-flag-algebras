import «LeanFlagAlgebras».SubflagDensity
import «LeanFlagAlgebras».MantelTheorem.FlagIso

open FlagAlgebras
open LabeledSubgraph
open Classical

namespace MantelTheorem

def inducedLabeledSubgraph_emptyType
    {V : Type} (G : LabeledGraph ∅ₜ V) (S : Set V)
    : LabeledSubgraph ∅ₜ G
  :=
  have h : G.type_verts ⊆ S := by simp [LabeledGraph.type_verts]
  inducedLabeledSubgraph G S h

theorem inducedLabeledSubgraph_emptyType_isInduced
    {V : Type} (G : LabeledGraph ∅ₜ V) (S : Set V)
    : (inducedLabeledSubgraph_emptyType G S).IsInduced
  := by
  simp [inducedLabeledSubgraph_emptyType]

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
  have h := isInduced_exist_induce_set H h_ind
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


/- single flag densities -/

lemma labeledSubgraphListSet_K2_O3
    : labeledSubgraphListSet (labeledGraphToList K2_labeledGraph) O3_labeledGraph = ∅
  := by
  dsimp [labeledSubgraphListSet, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Classical.not_imp]
  push_neg
  intro h_ind h_iso
  specialize @h_ind 0
  specialize h_iso 0
  let φ := h_iso.some
  have h_rel := @RelIso.map_rel_iff' _ _ _ _ φ.graph_iso
  dsimp [K2_labeledGraph] at h_rel
  have h_size : (Hl 0).size = 2 := by
    calc
      _ = K2_labeledGraph.size := labeledGraphIso_size_eq (Hl 0).coe K2_labeledGraph φ
      _ = 2 := K2_labeledGraph_size
  rcases inducedLabeledSubgraph_emptyType_size_2 (Hl 0) h_ind h_size with h | h | h
  · simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, O3_labeledGraph] at h_rel
    specialize h_rel 0 (by simp) 1 (by simp)
    simp [K2_graph] at h_rel
  · simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, O3_labeledGraph] at h_rel
    specialize h_rel 0 (by simp) 2 (by simp)
    simp [K2_graph] at h_rel
  · simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, O3_labeledGraph] at h_rel
    specialize h_rel 1 (by simp) 2 (by simp)
    simp [K2_graph] at h_rel

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
        have h_0 : 0 ∈ (Hl 0).subgraph.verts := by simp [h, inducedLabeledSubgraph_emptyType]
        have h_2 : 2 ∈ (Hl 0).subgraph.verts := by simp [h, inducedLabeledSubgraph_emptyType]
        rw [← LabeledSubgraph.coe_adj_iff (Hl 0) ⟨0, h_0⟩ ⟨2, h_2⟩]
        rw [← φ.graph_iso.map_adj_iff]
        simp [K2_labeledGraph, K2_graph]
      have : ¬ (Hl 0).subgraph.Adj 0 2 := by
        simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, E3_labeledGraph]
      contradiction
    · have : (Hl 0).subgraph.Adj 1 2 := by
        have h_1 : 1 ∈ (Hl 0).subgraph.verts := by simp [h, inducedLabeledSubgraph_emptyType]
        have h_2 : 2 ∈ (Hl 0).subgraph.verts := by simp [h, inducedLabeledSubgraph_emptyType]
        rw [← LabeledSubgraph.coe_adj_iff (Hl 0) ⟨1, h_1⟩ ⟨2, h_2⟩]
        rw [← φ.graph_iso.map_adj_iff]
        simp [K2_labeledGraph, K2_graph]
      have : ¬ (Hl 0).subgraph.Adj 1 2 := by
        simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, E3_labeledGraph]
      contradiction
  · intro h
    have h₀ : Hl 0 = labeledSubgraph_K2_E3 := by rw [h]
    repeat' constructor
    · intro i
      rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_E3]
      apply inducedLabeledSubgraph_emptyType_isInduced
    · intro i
      rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_E3]
      apply Nonempty.intro
      dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, E3_labeledGraph, K2_labeledGraph, coe]
      have h_card : Fintype.card (@Set.Elem (Fin 3) {0, 1}) = Fintype.card (Fin 2) := rfl
      have φ := Fintype.equivOfCardEq h_card
      exact {
        graph_iso := {
          toFun := φ.toFun
          invFun := φ.invFun
          left_inv := φ.left_inv
          right_inv := φ.right_inv
          map_rel_iff' := by
            simp; intro i hi j hj
            rcases hi with hi | hi <;> rcases hj with hj | hj
            <;> (subst hi hj; simp [K2_graph])
        }
        type_preserve := by
          funext i
          exact False.elim (Nat.not_succ_le_zero i.1 i.2)
      }
    · intro i j
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      simp only [not_true_eq_false, false_implies]

lemma labeledSubgraphListCount_K2_E3
    : labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) E3_labeledGraph = 1
  := by
  dsimp [labeledSubgraphListCount, labeledGraphToList]
  simp only [labeledSubgraphListSet_K2_E3, Set.toFinset_singleton, Finset.card_singleton]

@[simp]
theorem flagDensity_K2_E3
    : flagDensity₁ K2_flag E3_flag = 1 / 3
  := by
  dsimp [K2_flag, E3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) E3_labeledGraph
  let denom := multinomialCoefficient (fun i ↦ (labeledGraphToList K2_labeledGraph i).size) E3_labeledGraph.size
  show (num : ℚ) / (denom : ℚ) = 1 / 3
  have h₁ : num = 1 := by
    dsimp [num, labeledSubgraphListCount]
    exact labeledSubgraphListCount_K2_E3
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  rfl

def labeledSubgraph_K2_P3 : LabeledSubgraph ∅ₜ P3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType P3_labeledGraph {0, 1}

def labeledSubgraph_K2_P3' : LabeledSubgraph ∅ₜ P3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType P3_labeledGraph {0, 2}

lemma labeledSubgraphListSet_K2_P3
    : labeledSubgraphListSet (labeledGraphToList K2_labeledGraph) P3_labeledGraph =
      {fun _ => labeledSubgraph_K2_P3, fun _ => labeledSubgraph_K2_P3'}
  := by
  dsimp [labeledSubgraphListSet, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨h_ind, h_iso, _⟩
    specialize @h_ind 0
    specialize @h_iso 0
    let φ := h_iso.some
    have h_size : (Hl 0).size = 2 := by
      calc
        _ = K2_labeledGraph.size := labeledGraphIso_size_eq (Hl 0).coe K2_labeledGraph φ
        _ = 2 := K2_labeledGraph_size
    rcases inducedLabeledSubgraph_emptyType_size_2 (Hl 0) h_ind h_size with h | h | h
    <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    · left
      funext i
      simp only [Fin.fin_one_eq_zero i, h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, labeledSubgraph_K2_P3]
    · right
      funext i
      simp only [Fin.fin_one_eq_zero i, h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, labeledSubgraph_K2_P3']
    · have : (Hl 0).subgraph.Adj 1 2 := by
        have h_1 : 1 ∈ (Hl 0).subgraph.verts := by simp [h, inducedLabeledSubgraph_emptyType]
        have h_2 : 2 ∈ (Hl 0).subgraph.verts := by simp [h, inducedLabeledSubgraph_emptyType]
        rw [← LabeledSubgraph.coe_adj_iff (Hl 0) ⟨1, h_1⟩ ⟨2, h_2⟩]
        rw [← φ.graph_iso.map_adj_iff]
        simp [K2_labeledGraph, K2_graph]
      have : ¬ (Hl 0).subgraph.Adj 1 2 := by
        simp [h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, P3_labeledGraph]
      contradiction
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h₀ | h₀
    · repeat' constructor
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_P3]
        apply inducedLabeledSubgraph_emptyType_isInduced
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_P3]
        apply Nonempty.intro
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, P3_labeledGraph, K2_labeledGraph, coe]
        have h_card : Fintype.card (@Set.Elem (Fin 3) {0, 1}) = Fintype.card (Fin 2) := rfl
        have φ := Fintype.equivOfCardEq h_card
        exact {
          graph_iso := {
            toFun := φ.toFun
            invFun := φ.invFun
            left_inv := φ.left_inv
            right_inv := φ.right_inv
            map_rel_iff' := by
              simp; intro i hi j hj
              rcases hi with hi | hi <;> rcases hj with hj | hj
              <;> (subst hi hj; simp [K2_graph])
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      · intro i j
        rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
        simp only [not_true_eq_false, false_implies]
    · repeat' constructor
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_P3']
        apply inducedLabeledSubgraph_emptyType_isInduced
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_P3']
        apply Nonempty.intro
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph, P3_labeledGraph, K2_labeledGraph, coe]
        have h_card : Fintype.card (@Set.Elem (Fin 3) {0, 2}) = Fintype.card (Fin 2) := rfl
        have φ := Fintype.equivOfCardEq h_card
        exact {
          graph_iso := {
            toFun := φ.toFun
            invFun := φ.invFun
            left_inv := φ.left_inv
            right_inv := φ.right_inv
            map_rel_iff' := by
              simp; intro i hi j hj
              rcases hi with hi | hi <;> rcases hj with hj | hj
              <;> (subst hi hj; simp [K2_graph])
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      · intro i j
        rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
        simp only [not_true_eq_false, false_implies]

lemma labeledSubgraphListCount_K2_P3
    : labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) P3_labeledGraph = 2
  := by
  dsimp [labeledSubgraphListCount]
  refine Finset.card_eq_two.mpr ?_
  use fun _ => labeledSubgraph_K2_P3, fun _ => labeledSubgraph_K2_P3'
  constructor
  · refine Function.ne_iff.mpr ⟨0, ?_⟩
    dsimp [labeledSubgraph_K2_P3, labeledSubgraph_K2_P3', inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph]
    intro h
    simp only [mk.injEq, SimpleGraph.Subgraph.mk.injEq] at h
    obtain ⟨⟨h_verts, _⟩, _⟩ := h
    have : (1 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by
      rw [← h_verts]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
    contradiction
  · dsimp [labeledSubgraphListSet_K2_P3]
    simp only [labeledSubgraphListSet_K2_P3, Set.toFinset_insert, Set.toFinset_singleton]

@[simp]
theorem flagDensity_K2_P3
    : flagDensity₁ K2_flag P3_flag = 2 / 3
  := by
  dsimp [K2_flag, P3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) P3_labeledGraph
  let denom := multinomialCoefficient (fun i ↦ (labeledGraphToList K2_labeledGraph i).size) P3_labeledGraph.size
  show (num : ℚ) / (denom : ℚ) = 2 / 3
  have h₁ : num = 2 := by
    dsimp [num]
    exact labeledSubgraphListCount_K2_P3
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  rfl

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
