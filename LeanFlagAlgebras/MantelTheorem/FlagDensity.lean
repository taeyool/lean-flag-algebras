import «LeanFlagAlgebras».SubflagListDensity
import «LeanFlagAlgebras».MantelTheorem.FlagIso
import «LeanFlagAlgebras».Compute.Downward

open FlagAlgebras
open LabeledSubgraph
open Classical
open Compute

namespace MantelTheorem

def inducedLabeledSubgraph_emptyType
    {V : Type} (G : LabeledGraph ∅ₜ V) (S : Set V)
    : LabeledSubgraph ∅ₜ G
  :=
  have h : G.type_verts ⊆ S := by simp [LabeledGraph.type_verts]
  inducedLabeledSubgraph G S h

theorem inducedLabeledSubgraph_emptyType_verts
    {V : Type} (G : LabeledGraph ∅ₜ V) (S : Set V)
    : (inducedLabeledSubgraph_emptyType G S).subgraph.verts = S
  :=
  rfl

theorem inducedLabeledSubgraph_emptyType_isInduced
    {V : Type} (G : LabeledGraph ∅ₜ V) (S : Set V)
    : (inducedLabeledSubgraph_emptyType G S).IsInduced
  := by
  simp only [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph_isInduced]

theorem labeledSubgraph_emptyType_neq
    {V : Type} (G : LabeledGraph ∅ₜ V) (H H' : LabeledSubgraph ∅ₜ G)
    (h_verts_neq : H.subgraph.verts ≠ H'.subgraph.verts)
    : H ≠ H'
  := by
  intro h
  subst h
  contradiction

def inducedLabeledSubgraph_singletonType
    {V : Type} (G : LabeledGraph Sₜ V) (S : Set V) (h : G.type_embed 0 ∈ S)
    : LabeledSubgraph Sₜ G
  := by
  refine inducedLabeledSubgraph G S ?_
  dsimp [LabeledGraph.type_verts]
  have : @Set.univ (Fin 1) = {0} := by
    ext i
    simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
    rw [Fin.fin_one_eq_zero i]
  rw [this]
  simp only [Set.image_singleton, Set.singleton_subset_iff]
  exact h

theorem inducedLabeledSubgraph_singletonType_verts
    {V : Type} (G : LabeledGraph Sₜ V) (S : Set V) (h : G.type_embed 0 ∈ S)
    : (inducedLabeledSubgraph_singletonType G S h).subgraph.verts = S
  :=
  rfl

theorem inducedLabeledSubgraph_singletonType_isInduced
    {V : Type} (G : LabeledGraph Sₜ V) (S : Set V) (h : G.type_embed 0 ∈ S)
    : (inducedLabeledSubgraph_singletonType G S h).IsInduced
  := by
  simp only [inducedLabeledSubgraph_singletonType, inducedLabeledSubgraph_isInduced]

theorem labeledSubgraph_singletonType_neq
    {V : Type} (G : LabeledGraph Sₜ V) (H H' : LabeledSubgraph Sₜ G)
    (h_verts_neq : H.subgraph.verts ≠ H'.subgraph.verts)
    : H ≠ H'
  := by
  intro h
  subst h
  contradiction

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

theorem inducedLabeledSubgraph_singletonType_size_2
    {G : LabeledGraph Sₜ (Fin 3)} (H : LabeledSubgraph Sₜ G) (h_ind : H.IsInduced)
    (h_size : H.size = 2)
    : (∃ h : G.type_embed 0 ∈ {0, 1}, H = inducedLabeledSubgraph_singletonType G {0, 1} h) ∨
      (∃ h : G.type_embed 0 ∈ {0, 2}, H = inducedLabeledSubgraph_singletonType G {0, 2} h) ∨
      (∃ h : G.type_embed 0 ∈ {1, 2}, H = inducedLabeledSubgraph_singletonType G {1, 2} h)
  := by
  have h := isInduced_exist_induce_set H h_ind
  rcases h with ⟨S, h_type_S, hH⟩
  have hS_card : Fintype.card S = 2 := by
    rw [← inducedLabeledSubgraph_size G S h_type_S, hH, h_size]
  dsimp [LabeledGraph.type_verts] at h_type_S
  have : @Set.univ (Fin 1) = {0} := by
    ext i
    simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
    rw [Fin.fin_one_eq_zero i]
  rw [this] at h_type_S
  simp only [Set.image_singleton, Set.singleton_subset_iff] at h_type_S
  rcases set_fin3_card_eq_2 S hS_card with hS | hS | hS
  <;> subst hS
  · left
    use h_type_S
    rw [inducedLabeledSubgraph_singletonType, ← hH]
  · right; left
    use h_type_S
    rw [inducedLabeledSubgraph_singletonType, ← hH]
  · right; right
    use h_type_S
    rw [inducedLabeledSubgraph_singletonType, ← hH]

lemma set_01_neq_02
    : ({0, 1} : Set (Fin 3)) ≠ ({0, 2} : Set (Fin 3))
  := by
  intro h
  have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
    rw [h]
    exact Set.mem_insert_of_mem 0 rfl
  contradiction

lemma set_01_neq_12
    : ({0, 1} : Set (Fin 3)) ≠ ({1, 2} : Set (Fin 3))
  := by
  intro h
  have : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
    rw [h]
    exact Set.mem_insert_of_mem 1 rfl
  contradiction

lemma set_02_neq_12
    : ({0, 2} : Set (Fin 3)) ≠ ({1, 2} : Set (Fin 3))
  := by
  intro h
  have : (1 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by
    rw [h]
    exact Set.mem_insert 1 {2}
  contradiction


/- single flag densities -/

lemma setOfLabeledSubgraphListIsoHl_K2_O3
    : setOfLabeledSubgraphListIsoHl O3_labeledGraph (labeledGraphToList K2_labeledGraph) = ∅
  := by
  dsimp only [setOfLabeledSubgraphListIsoHl, predIsoLabeledHl, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
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

lemma labeledSubgraphListCount_K2_O3
    : labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) O3_labeledGraph = 0
  := by
  dsimp only [labeledSubgraphListCount]
  simp only [setOfLabeledSubgraphListIsoHl_K2_O3, Set.toFinset_empty, Finset.card_empty]

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
  have h₁ : num = 0 := labeledSubgraphListCount_K2_O3
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  simp only [Nat.cast_zero, Nat.cast_ofNat, zero_div]

def labeledSubgraph_K2_E3 : LabeledSubgraph ∅ₜ E3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType E3_labeledGraph {0, 1}

lemma setOfLabeledSubgraphListIsoHl_K2_E3
    : setOfLabeledSubgraphListIsoHl E3_labeledGraph (labeledGraphToList K2_labeledGraph) =
      {fun _ => labeledSubgraph_K2_E3}
  := by
  dsimp only [setOfLabeledSubgraphListIsoHl, predIsoLabeledHl, labeledGraphToList]
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
      dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph,
        E3_labeledGraph, K2_labeledGraph, coe]
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
      simp only [Fin.isValue, ne_eq, not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]

lemma labeledSubgraphListCount_K2_E3
    : labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) E3_labeledGraph = 1
  := by
  dsimp only [labeledSubgraphListCount]
  simp only [setOfLabeledSubgraphListIsoHl_K2_E3, Set.toFinset_singleton, Finset.card_singleton]

/- test ----------------------------/

theorem labeledSubgraphListDensity_K2_E3
    : labeledSubgraphListDensity (labeledGraphToList K2_labeledGraph) E3_labeledGraph = 1 / 3
  := by
  rw [← K2_eq, ← E3_eq, labeledGraphToList_toLabeledGraphList_eq, labeledSubgraphListDensity_eq]
  native_decide

/- ---------------------------------/

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
  have h₁ : num = 1 := labeledSubgraphListCount_K2_E3
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

lemma setOfLabeledSubgraphListIsoHl_K2_P3
    : setOfLabeledSubgraphListIsoHl P3_labeledGraph (labeledGraphToList K2_labeledGraph) =
      {fun _ => labeledSubgraph_K2_P3, fun _ => labeledSubgraph_K2_P3'}
  := by
  dsimp only [setOfLabeledSubgraphListIsoHl, predIsoLabeledHl, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq]
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
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph,
          P3_labeledGraph, K2_labeledGraph, coe]
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
        simp only [Fin.isValue, ne_eq, not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]
    · repeat' constructor
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_P3']
        apply inducedLabeledSubgraph_emptyType_isInduced
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_P3']
        apply Nonempty.intro
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph,
          P3_labeledGraph, K2_labeledGraph, coe]
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
        simp only [Fin.isValue, ne_eq, not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]

lemma labeledSubgraphListCount_K2_P3
    : labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) P3_labeledGraph = 2
  := by
  dsimp only [labeledSubgraphListCount]
  refine Finset.card_eq_two.mpr ?_
  use fun _ => labeledSubgraph_K2_P3, fun _ => labeledSubgraph_K2_P3'
  constructor
  · refine Function.ne_iff.mpr ⟨0, ?_⟩
    apply labeledSubgraph_emptyType_neq
    exact set_01_neq_02
  · simp only [setOfLabeledSubgraphListIsoHl_K2_P3, Set.toFinset_insert, Set.toFinset_singleton]

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
  have h₁ : num = 2 := labeledSubgraphListCount_K2_P3
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  rfl

def labeledSubgraph_K2_K3 : LabeledSubgraph ∅ₜ K3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType K3_labeledGraph {0, 1}

def labeledSubgraph_K2_K3' : LabeledSubgraph ∅ₜ K3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType K3_labeledGraph {0, 2}

def labeledSubgraph_K2_K3'' : LabeledSubgraph ∅ₜ K3_labeledGraph
  :=
  inducedLabeledSubgraph_emptyType K3_labeledGraph {1, 2}

lemma setOfLabeledSubgraphListIsoHl_K2_K3
    : setOfLabeledSubgraphListIsoHl K3_labeledGraph (labeledGraphToList K2_labeledGraph) =
      {fun _ => labeledSubgraph_K2_K3, fun _ => labeledSubgraph_K2_K3', fun _ => labeledSubgraph_K2_K3''}
  := by
  dsimp only [setOfLabeledSubgraphListIsoHl, predIsoLabeledHl, labeledGraphToList]
  ext Hl
  simp only [Set.mem_setOf_eq]
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
      simp only [Fin.fin_one_eq_zero i, h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, labeledSubgraph_K2_K3]
    · right; left
      funext i
      simp only [Fin.fin_one_eq_zero i, h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, labeledSubgraph_K2_K3']
    · right; right
      funext i
      simp only [Fin.fin_one_eq_zero i, h, inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, labeledSubgraph_K2_K3'']
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h₀ | h₀ | h₀
    · repeat' constructor
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_K3]
        apply inducedLabeledSubgraph_emptyType_isInduced
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_K3]
        apply Nonempty.intro
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph,
          K3_labeledGraph, K2_labeledGraph, coe]
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
        simp only [Fin.isValue, ne_eq, not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]
    · repeat' constructor
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_K3']
        apply inducedLabeledSubgraph_emptyType_isInduced
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_K3']
        apply Nonempty.intro
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph,
          K3_labeledGraph, K2_labeledGraph, coe]
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
        simp only [Fin.isValue, ne_eq, not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]
    · repeat' constructor
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_K3'']
        apply inducedLabeledSubgraph_emptyType_isInduced
      · intro i
        rw [Fin.fin_one_eq_zero i, h₀, labeledSubgraph_K2_K3'']
        apply Nonempty.intro
        dsimp [inducedLabeledSubgraph_emptyType, inducedLabeledSubgraph, inducedSubgraph,
          K3_labeledGraph, K2_labeledGraph, coe]
        have h_card : Fintype.card (@Set.Elem (Fin 3) {1, 2}) = Fintype.card (Fin 2) := rfl
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
        simp only [Fin.isValue, ne_eq, not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]

lemma labeledSubgraphListCount_K2_K3
    : labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) K3_labeledGraph = 3
  := by
  dsimp only [labeledSubgraphListCount]
  refine Finset.card_eq_three.mpr ?_
  use fun _ => labeledSubgraph_K2_K3, fun _ => labeledSubgraph_K2_K3', fun _ => labeledSubgraph_K2_K3''
  repeat' constructor
  · refine Function.ne_iff.mpr ⟨0, ?_⟩
    apply labeledSubgraph_emptyType_neq
    exact set_01_neq_02
  · refine Function.ne_iff.mpr ⟨0, ?_⟩
    apply labeledSubgraph_emptyType_neq
    exact set_01_neq_12
  · refine Function.ne_iff.mpr ⟨0, ?_⟩
    apply labeledSubgraph_emptyType_neq
    exact set_02_neq_12
  · simp only [setOfLabeledSubgraphListIsoHl_K2_K3, Set.toFinset_insert, Set.toFinset_singleton]

@[simp]
theorem flagDensity_K2_K3
    : flagDensity₁ K2_flag K3_flag = 1
  := by
  dsimp [K2_flag, K3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphToList K2_labeledGraph) K3_labeledGraph
  let denom := multinomialCoefficient (fun i ↦ (labeledGraphToList K2_labeledGraph i).size) K3_labeledGraph.size
  show (num : ℚ) / (denom : ℚ) = 1
  have h₁ : num = 3 := labeledSubgraphListCount_K2_K3
  have h₂ : denom = 3 := by
    dsimp [denom, multinomialCoefficient]
    simp [labeledGraphToList]
    rfl
  rw [h₁, h₂]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]


/- flag pair densities -/

def labeledSubgraph_O2₁_O2₁_O3₁ : LabeledSubgraph Sₜ (O3₁_labeledGraph 0)
  :=
  inducedLabeledSubgraph_singletonType (O3₁_labeledGraph 0) {0, 1} (by simp [O3₁_labeledGraph])

def labeledSubgraph_O2₁_O2₁_O3₁' : LabeledSubgraph Sₜ (O3₁_labeledGraph 0)
  :=
  inducedLabeledSubgraph_singletonType (O3₁_labeledGraph 0) {0, 2} (by simp [O3₁_labeledGraph])

lemma labeledSubgraph_O2₁_O2₁_O3₁_isInduced
    : labeledSubgraph_O2₁_O2₁_O3₁.IsInduced
  := by
  apply inducedLabeledSubgraph_singletonType_isInduced

lemma labeledSubgraph_O2₁_O2₁_O3₁'_isInduced
    : labeledSubgraph_O2₁_O2₁_O3₁'.IsInduced
  := by
  apply inducedLabeledSubgraph_singletonType_isInduced

def labeledSubgraph_O2₁_O2₁_O3₁_iso_O2₁_labeledGraph_0
    : labeledSubgraph_O2₁_O2₁_O3₁.coe ≃f O2₁_labeledGraph 0
  := by
  dsimp [labeledSubgraph_O2₁_O2₁_O3₁, inducedLabeledSubgraph_singletonType, inducedLabeledSubgraph,
    inducedSubgraph, LabeledSubgraph.coe, O3₁_labeledGraph, O2₁_labeledGraph]
  exact {
    graph_iso := {
      toFun := fun ⟨i, _⟩ => if i = 0 then 0 else 1
      invFun := fun i => if i = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩
      left_inv := by grind
      right_inv := by grind
      map_rel_iff' := by
        intro i j
        simp only [Equiv.coe_fn_mk, SimpleGraph.Subgraph.coe_adj, Subtype.coe_prop, and_true]
        rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
        rcases hi with hi | hi <;> rcases hj with hj | hj
        <;> subst hi hj
        · simp only [SimpleGraph.irrefl]
        · simp only [O3_graph_01, iff_false]
          exact fun x => x
        · simp only [O3_graph_10, iff_false]
          exact fun x => x
        · simp only [SimpleGraph.irrefl]
    }
    type_preserve := rfl
  }

def labeledSubgraph_O2₁_O2₁_O3₁'_iso_O2₁_labeledGraph_0
    : labeledSubgraph_O2₁_O2₁_O3₁'.coe ≃f O2₁_labeledGraph 0
  := by
  dsimp [labeledSubgraph_O2₁_O2₁_O3₁', inducedLabeledSubgraph_singletonType, inducedLabeledSubgraph,
    inducedSubgraph, LabeledSubgraph.coe, O3₁_labeledGraph, O2₁_labeledGraph]
  exact {
    graph_iso := {
      toFun := fun ⟨i, _⟩ => if i = 0 then 0 else 1
      invFun := fun i => {
        val := if i = 0 then 0 else 2
        property := by simp; exact eq_or_ne i 0
      }
      left_inv := by grind
      right_inv := by grind
      map_rel_iff' := by
        intro i j
        simp only [Equiv.coe_fn_mk, SimpleGraph.Subgraph.coe_adj, Subtype.coe_prop, and_true]
        rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
        rcases hi with hi | hi <;> rcases hj with hj | hj
        <;> subst hi hj
        · simp only [SimpleGraph.irrefl]
        · simp only [O3_graph_02, iff_false]
          exact fun x => x
        · simp only [O3_graph_20, iff_false]
          exact fun x => x
        · simp only [SimpleGraph.irrefl]
    }
    type_preserve := rfl
  }

lemma labeledSubgraph_O2₁_O2₁_O3₁_O3₁'_disjoint
    : (labeledSubgraph_O2₁_O2₁_O3₁.subgraph.verts \ (O3₁_labeledGraph 0).type_verts) ∩ (labeledSubgraph_O2₁_O2₁_O3₁'.subgraph.verts \ (O3₁_labeledGraph 0).type_verts) = ∅
  := by
  dsimp [labeledSubgraph_O2₁_O2₁_O3₁, labeledSubgraph_O2₁_O2₁_O3₁',
    inducedLabeledSubgraph_singletonType, inducedLabeledSubgraph, inducedSubgraph, labeledGraphPairToList, LabeledGraph.type_verts, O3₁_labeledGraph]
  simp only [Set.image_univ, Set.range_const, Set.mem_singleton_iff, Set.insert_diff_of_mem,
    not_false_eq_true, Set.diff_singleton_eq_self, Fin.reduceEq, Set.inter_singleton_eq_empty]

lemma setOfLabeledSubgraphListIsoHl_O2₁_O2₁_O3₁
    : setOfLabeledSubgraphListIsoHl (O3₁_labeledGraph 0) (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) =
      {fun i => match i with | 0 => labeledSubgraph_O2₁_O2₁_O3₁ | 1 => labeledSubgraph_O2₁_O2₁_O3₁',
       fun i => match i with | 0 => labeledSubgraph_O2₁_O2₁_O3₁' | 1 => labeledSubgraph_O2₁_O2₁_O3₁}
  := by
  dsimp only [Fin.isValue, setOfLabeledSubgraphListIsoHl]
  ext Hl
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨h_ind, h_iso, h_verts⟩
    let φ₀ := (h_iso 0).some
    let φ₁ := (h_iso 1).some
    dsimp [labeledGraphPairToList] at φ₀
    dsimp [labeledGraphPairToList] at φ₁
    specialize h_verts 0 1
    simp only [ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
      forall_const] at h_verts
    dsimp [O3₁_labeledGraph, LabeledGraph.type_verts] at h_verts
    have : @Set.univ (Fin 1) = {0} := by
      ext i
      simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
      rw [Fin.fin_one_eq_zero i]
    rw [this] at h_verts
    simp only [Set.image_singleton] at h_verts
    have h_size_0 : (Hl 0).size = 2 := by
      calc
        _ = (O2₁_labeledGraph 0).size := labeledGraphIso_size_eq (Hl 0).coe (O2₁_labeledGraph 0) φ₀
        _ = 2 := O2₁_labeledGraph_size 0
    have h_size_1 : (Hl 1).size = 2 := by
      calc
        _ = (O2₁_labeledGraph 0).size := labeledGraphIso_size_eq (Hl 1).coe (O2₁_labeledGraph 0) φ₁
        _ = 2 := O2₁_labeledGraph_size 0
    rcases inducedLabeledSubgraph_singletonType_size_2 (Hl 0) (h_ind 0) (h_size_0)
      with ⟨h₀_type_0, h₀⟩ | ⟨h₀_type_0, h₀⟩ | ⟨h₀_type_0, h₀⟩
    <;> rcases inducedLabeledSubgraph_singletonType_size_2 (Hl 1) (h_ind 1) (h_size_1)
      with ⟨h₁_type_0, h₁⟩ | ⟨h₁_type_0, h₁⟩ | ⟨h₁_type_0, h₁⟩
    <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    <;> (first
      | left
        funext i
        split <;> assumption
      | right
        funext i
        split <;> assumption
      | rw [h₀, h₁] at h_verts
        simp only [inducedLabeledSubgraph_singletonType_verts] at h_verts
        simp_all
    )
    · exact False.elim ((Ne.symm (Set.ne_insert_of_notMem {2} id)) h_verts)
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with hl | hl
    · have h₀ : Hl 0 = labeledSubgraph_O2₁_O2₁_O3₁ := by rw [hl]
      have h₁ : Hl 1 = labeledSubgraph_O2₁_O2₁_O3₁' := by rw [hl]
      repeat' constructor
      · simp only [LabeledSubgraphList.IsInduced]
        rw [Fin.forall_fin_two, h₀, h₁]
        simp only [labeledSubgraph_O2₁_O2₁_O3₁_isInduced, labeledSubgraph_O2₁_O2₁_O3₁'_isInduced, and_self]
      · rw [Fin.forall_fin_two, h₀, h₁]
        constructor <;> apply Nonempty.intro
        · exact labeledSubgraph_O2₁_O2₁_O3₁_iso_O2₁_labeledGraph_0
        · exact labeledSubgraph_O2₁_O2₁_O3₁'_iso_O2₁_labeledGraph_0
      · intro i j hij
        match i, j with
        | 0, 0 => contradiction
        | 0, 1 => simp only [h₀, h₁, labeledSubgraph_O2₁_O2₁_O3₁_O3₁'_disjoint]
        | 1, 0 => simp only [h₀, h₁, labeledSubgraph_O2₁_O2₁_O3₁_O3₁'_disjoint, Set.inter_comm]
        | 1, 1 => contradiction
    · have h₀ : Hl 0 = labeledSubgraph_O2₁_O2₁_O3₁' := by rw [hl]
      have h₁ : Hl 1 = labeledSubgraph_O2₁_O2₁_O3₁ := by rw [hl]
      repeat' constructor
      · simp only [LabeledSubgraphList.IsInduced]
        rw [Fin.forall_fin_two, h₀, h₁]
        simp only [labeledSubgraph_O2₁_O2₁_O3₁_isInduced, labeledSubgraph_O2₁_O2₁_O3₁'_isInduced, and_self]
      · rw [Fin.forall_fin_two, h₀, h₁]
        constructor <;> apply Nonempty.intro
        · exact labeledSubgraph_O2₁_O2₁_O3₁'_iso_O2₁_labeledGraph_0
        · exact labeledSubgraph_O2₁_O2₁_O3₁_iso_O2₁_labeledGraph_0
      · intro i j hij
        match i, j with
        | 0, 0 => contradiction
        | 0, 1 => simp only [h₀, h₁, labeledSubgraph_O2₁_O2₁_O3₁_O3₁'_disjoint, Set.inter_comm]
        | 1, 0 => simp only [h₀, h₁, labeledSubgraph_O2₁_O2₁_O3₁_O3₁'_disjoint]
        | 1, 1 => contradiction

lemma labeledSubgraphListCount_O2₁_O2₁_O3₁
    : labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (O3₁_labeledGraph 0) = 2
  := by
  dsimp [labeledSubgraphListCount]
  refine Finset.card_eq_two.mpr ?_
  use fun i => match i with | 0 => labeledSubgraph_O2₁_O2₁_O3₁ | 1 => labeledSubgraph_O2₁_O2₁_O3₁',
      fun i => match i with | 0 => labeledSubgraph_O2₁_O2₁_O3₁' | 1 => labeledSubgraph_O2₁_O2₁_O3₁
  constructor
  · refine Function.ne_iff.mpr ⟨0, ?_⟩
    apply labeledSubgraph_singletonType_neq
    exact set_01_neq_02
  · simp only [setOfLabeledSubgraphListIsoHl_O2₁_O2₁_O3₁, Set.toFinset_insert, Set.toFinset_singleton]

@[simp]
theorem flagDensity_O2₁_O2₁_O3₁
    : flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1
  := by
  dsimp [O2₁_flag, O3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (O3₁_labeledGraph 0)
  have h_num : num = 2 := labeledSubgraphListCount_O2₁_O2₁_O3₁
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  show (num : ℚ) / 2 = 1
  rw [h_num]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

lemma labeledSubgraphListCount_O2₁_K2₁_O3₁
    : labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (O3₁_labeledGraph 0) = 0
  := by
  dsimp [labeledSubgraphListCount]
  rw [Finset.card_eq_zero.mpr]
  by_contra h
  push_neg at h
  rw [← Finset.nonempty_iff_ne_empty] at h
  dsimp [Finset.Nonempty] at h
  rcases h with ⟨Hl, hHl⟩
  dsimp [LabeledSubgraphList] at Hl
  simp only [Fin.isValue, setOfLabeledSubgraphListIsoHl, Set.coe_setOf, Set.toFinset_setOf,
    Finset.mem_filter, Finset.mem_univ, true_and] at hHl
  rcases hHl with ⟨h_ind, h_iso, h_verts⟩
  let witness := Hl 1
  have : O3_graph.edgeSet ≠ ∅ := by sorry
  simp only [O3_graph, SimpleGraph.emptyGraph_eq_bot, SimpleGraph.edgeSet_bot, ne_eq,
    not_true_eq_false] at this

@[simp]
theorem flagDensity_O2₁_K2₁_O3₁
    : flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, O3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (O3₁_labeledGraph 0)
  have h_num : num = 0 := labeledSubgraphListCount_O2₁_K2₁_O3₁
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_K2₁_K2₁_O3₁
    : flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0
  := by
  dsimp [K2₁_flag, O3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (O3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁
    : flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0
  := by
  dsimp [O2₁_flag, E3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (E3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁
    : flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2
  := by
  dsimp [O2₁_flag, K2₁_flag, E3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 0)
  have h_num : num = 1 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList, ← one_div]
  show (num : ℚ) / 2 = 1 / 2
  rw [h_num]
  rfl

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁
    : flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0
  := by
  dsimp [K2₁_flag, E3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁'
    : flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1
  := by
  dsimp [O2₁_flag, E3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (E3₁_labeledGraph 2)
  have h_num : num = 2 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  show (num : ℚ) / 2 = 1
  rw [h_num]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁'
    : flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, E3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 2)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁'
    : flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  dsimp [K2₁_flag, E3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 2)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁
    : flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0
  := by
  dsimp [O2₁_flag, P3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (P3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁
    : flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, P3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁
    : flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1
  := by
  dsimp [K2₁_flag, P3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 0)
  have h_num : num = 2 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  show (num : ℚ) / 2 = 1
  rw [h_num]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁'
    : flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0
  := by
  dsimp [O2₁_flag, P3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (P3₁_labeledGraph 1)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁'
    : flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2
  := by
  dsimp [O2₁_flag, K2₁_flag, P3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 1)
  have h_num : num = 1 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList, ← one_div]
  show (num : ℚ) / 2 = 1 / 2
  rw [h_num]
  rfl

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁'
    : flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0
  := by
  dsimp [K2₁_flag, P3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 1)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_O2₁_K3₁
    : flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0
  := by
  dsimp [O2₁_flag, K3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (K3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_O2₁_K2₁_K3₁
    : flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, K3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (K3₁_labeledGraph 0)
  have h_num : num = 0 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  exact h_num

@[simp]
theorem flagDensity_K2₁_K2₁_K3₁
    : flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1
  := by
  dsimp [K2₁_flag, K3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  dsimp [labeledSubgraphListDensity]
  let num := labeledSubgraphListCount (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (K3₁_labeledGraph 0)
  have h_num : num = 2 := by
    sorry
  dsimp [multinomialCoefficient]
  simp [labeledGraphPairToList]
  show (num : ℚ) / 2 = 1
  rw [h_num]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

end MantelTheorem
