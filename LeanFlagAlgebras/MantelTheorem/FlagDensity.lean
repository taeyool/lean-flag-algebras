import «LeanFlagAlgebras».MantelTheorem.FlagDefs

open FlagAlgebras
open LabeledSubgraph
open Classical
open Compute

namespace MantelTheorem

/- single flag densities -/

theorem labeledSubgraphListDensity_K2_O3
    : labeledSubgraphListDensity (labeledGraphToList K2_labeledGraph) O3_labeledGraph = 0
  := by
  rw [← K2_eq, ← O3_eq, labeledSubgraphListDensity_labeledGraphToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2_O3
    : flagDensity₁ K2_flag O3_flag = 0
  := by
  dsimp [K2_flag, O3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  exact labeledSubgraphListDensity_K2_O3

theorem labeledSubgraphListDensity_K2_E3
    : labeledSubgraphListDensity (labeledGraphToList K2_labeledGraph) E3_labeledGraph = 1 / 3
  := by
  rw [← K2_eq, ← E3_eq, labeledSubgraphListDensity_labeledGraphToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2_E3
    : flagDensity₁ K2_flag E3_flag = 1 / 3
  := by
  dsimp [K2_flag, E3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  exact labeledSubgraphListDensity_K2_E3

theorem labeledSubgraphListDensity_K2_P3
    : labeledSubgraphListDensity (labeledGraphToList K2_labeledGraph) P3_labeledGraph = 2 / 3
  := by
  rw [← K2_eq, ← P3_eq, labeledSubgraphListDensity_labeledGraphToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2_P3
    : flagDensity₁ K2_flag P3_flag = 2 / 3
  := by
  dsimp [K2_flag, P3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  exact labeledSubgraphListDensity_K2_P3

theorem labeledSubgraphListDensity_K2_K3
    : labeledSubgraphListDensity (labeledGraphToList K2_labeledGraph) K3_labeledGraph = 1
  := by
  rw [← K2_eq, ← K3_eq, labeledSubgraphListDensity_labeledGraphToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2_K3
    : flagDensity₁ K2_flag K3_flag = 1
  := by
  dsimp [K2_flag, K3_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁]
  exact labeledSubgraphListDensity_K2_K3


/- flag pair densities -/

theorem labeledSubgraphListDensity_O2₁_O2₁_O3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (O3₁_labeledGraph 0) = 1
  := by
  rw [← O2₁_eq, ← O3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_O3₁
    : flagDensity₂ O2₁_flag O2₁_flag O3₁_flag = 1
  := by
  dsimp [O2₁_flag, O3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_O2₁_O3₁

theorem labeledSubgraphListDensity_O2₁_K2₁_O3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (O3₁_labeledGraph 0) = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← O3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_O3₁
    : flagDensity₂ O2₁_flag K2₁_flag O3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, O3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_K2₁_O3₁

theorem labeledSubgraphListDensity_K2₁_K2₁_O3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (O3₁_labeledGraph 0) = 0
  := by
  rw [← K2₁_eq, ← O3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_O3₁
    : flagDensity₂ K2₁_flag K2₁_flag O3₁_flag = 0
  := by
  dsimp [K2₁_flag, O3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_K2₁_K2₁_O3₁

theorem labeledSubgraphListDensity_O2₁_O2₁_E3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (E3₁_labeledGraph 0) = 0
  := by
  rw [← O2₁_eq, ← E3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁
    : flagDensity₂ O2₁_flag O2₁_flag E3₁_flag = 0
  := by
  dsimp [O2₁_flag, E3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_O2₁_E3₁

theorem labeledSubgraphListDensity_O2₁_K2₁_E3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 0) = 1 / 2
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← E3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁
    : flagDensity₂ O2₁_flag K2₁_flag E3₁_flag = 1 / 2
  := by
  dsimp [O2₁_flag, K2₁_flag, E3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_K2₁_E3₁

theorem labeledSubgraphListDensity_K2₁_K2₁_E3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 0) = 0
  := by
  rw [← K2₁_eq, ← E3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁
    : flagDensity₂ K2₁_flag K2₁_flag E3₁_flag = 0
  := by
  dsimp [K2₁_flag, E3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_K2₁_K2₁_E3₁

theorem labeledSubgraphListDensity_O2₁_O2₁_E3₁'
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (E3₁_labeledGraph 2) = 1
  := by
  rw [← O2₁_eq, ← E3₁'_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_E3₁'
    : flagDensity₂ O2₁_flag O2₁_flag E3₁'_flag = 1
  := by
  dsimp [O2₁_flag, E3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_O2₁_E3₁'

theorem labeledSubgraphListDensity_O2₁_K2₁_E3₁'
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 2) = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← E3₁'_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_E3₁'
    : flagDensity₂ O2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, E3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_K2₁_E3₁'

theorem labeledSubgraphListDensity_K2₁_K2₁_E3₁'
    : labeledSubgraphListDensity (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (E3₁_labeledGraph 2) = 0
  := by
  rw [← K2₁_eq, ← E3₁'_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_E3₁'
    : flagDensity₂ K2₁_flag K2₁_flag E3₁'_flag = 0
  := by
  dsimp [K2₁_flag, E3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_K2₁_K2₁_E3₁'

theorem labeledSubgraphListDensity_O2₁_O2₁_P3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (P3₁_labeledGraph 0) = 0
  := by
  rw [← O2₁_eq, ← P3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁
    : flagDensity₂ O2₁_flag O2₁_flag P3₁_flag = 0
  := by
  dsimp [O2₁_flag, P3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_O2₁_P3₁

theorem labeledSubgraphListDensity_O2₁_K2₁_P3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 0) = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← P3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁
    : flagDensity₂ O2₁_flag K2₁_flag P3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, P3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_K2₁_P3₁

theorem labeledSubgraphListDensity_K2₁_K2₁_P3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 0) = 1
  := by
  rw [← K2₁_eq, ← P3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁
    : flagDensity₂ K2₁_flag K2₁_flag P3₁_flag = 1
  := by
  dsimp [K2₁_flag, P3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_K2₁_K2₁_P3₁

theorem labeledSubgraphListDensity_O2₁_O2₁_P3₁'
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (P3₁_labeledGraph 1) = 0
  := by
  rw [← O2₁_eq, ← P3₁'_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_P3₁'
    : flagDensity₂ O2₁_flag O2₁_flag P3₁'_flag = 0
  := by
  dsimp [O2₁_flag, P3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_O2₁_P3₁'

theorem labeledSubgraphListDensity_O2₁_K2₁_P3₁'
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 1) = 1 / 2
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← P3₁'_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_P3₁'
    : flagDensity₂ O2₁_flag K2₁_flag P3₁'_flag = 1 / 2
  := by
  dsimp [O2₁_flag, K2₁_flag, P3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_K2₁_P3₁'

theorem labeledSubgraphListDensity_K2₁_K2₁_P3₁'
    : labeledSubgraphListDensity (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (P3₁_labeledGraph 1) = 0
  := by
  rw [← K2₁_eq, ← P3₁'_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_P3₁'
    : flagDensity₂ K2₁_flag K2₁_flag P3₁'_flag = 0
  := by
  dsimp [K2₁_flag, P3₁'_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_K2₁_K2₁_P3₁'

theorem labeledSubgraphListDensity_O2₁_O2₁_K3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (O2₁_labeledGraph 0)) (K3₁_labeledGraph 0) = 0
  := by
  rw [← O2₁_eq, ← K3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_O2₁_K3₁
    : flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0
  := by
  dsimp [O2₁_flag, K3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_O2₁_K3₁

theorem labeledSubgraphListDensity_O2₁_K2₁_K3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (O2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (K3₁_labeledGraph 0) = 0
  := by
  rw [← O2₁_eq, ← K2₁_eq, ← K3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_O2₁_K2₁_K3₁
    : flagDensity₂ O2₁_flag K2₁_flag K3₁_flag = 0
  := by
  dsimp [O2₁_flag, K2₁_flag, K3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_O2₁_K2₁_K3₁

theorem labeledSubgraphListDensity_K2₁_K2₁_K3₁
    : labeledSubgraphListDensity (labeledGraphPairToList (K2₁_labeledGraph 0) (K2₁_labeledGraph 0)) (K3₁_labeledGraph 0) = 1
  := by
  rw [← K2₁_eq, ← K3₁_eq, labeledSubgraphListDensity_labeledGraphPairToList_eq]
  native_decide

@[simp]
theorem flagDensity_K2₁_K2₁_K3₁
    : flagDensity₂ K2₁_flag K2₁_flag K3₁_flag = 1
  := by
  dsimp [K2₁_flag, K3₁_flag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂]
  exact labeledSubgraphListDensity_K2₁_K2₁_K3₁

end MantelTheorem
