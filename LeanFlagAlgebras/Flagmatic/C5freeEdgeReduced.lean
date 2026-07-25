-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 5:1223344551').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/C5freeEdge_reduced_cert.json \
--     LeanFlagAlgebras/Flagmatic/C5freeEdgeReduced.lean --namespace C5freeEdgeReduced --native-decide --force

import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Automation.Basic
import LeanFlagAlgebras.Automation.FlagMulReduce
import LeanFlagAlgebras.Automation.FlagSumSort
import LeanFlagAlgebras.Automation.Matrix.PosSemiDef
import LeanFlagAlgebras.Automation.FlagExpand
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import LeanFlagAlgebras.Forbid.CommonGraphs

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace C5freeEdgeReduced

-- The forbidden graph, as the 5-vertex `Sym2Graph` term `ForbidGraph`. It is forbidden
-- as a subgraph, not necessarily an induced one, so a copy of `ForbidGraph` may carry extra
-- edges. The generation commands below prune against it: a flag containing `ForbidGraph` is
-- never enumerated, and they emit the subgraph-`ForbidGraph`-free flags, the completeness lemma
-- for that set, and the pair-density / multiplication theorems the proof consumes.
def ForbidGraph : Sym2Graph 5 where
  edges := {s(0, 1), s(0, 4), s(1, 2), s(2, 3), s(3, 4)}
  edges_valid := by decide
-- Generated bridging lemmas are proved by `native_decide`, so the main theorem below
-- additionally depends on the `Lean.ofReduceBool` and `Lean.trustCompiler` axioms,
-- which trust Lean's compiler and runtime for the evaluated decision procedures.
-- Regenerating without `--native-decide` proves the same lemmas by `decide +kernel`
-- and removes both, at a higher build cost.
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 2 ForbidGraph
generate_forbid_free_empty_typed_flags 3 ForbidGraph
generate_forbid_free_empty_typed_flags 5 ForbidGraph
generate_forbid_free_flags 3 1 0 ForbidGraph
generate_forbid_free_flags 5 1 0 ForbidGraph
generate_forbid_free_flag_pair_density_theorems 3 5 1 0 ForbidGraph
generate_forbid_free_mul_theorems 3 5 1 0 ForbidGraph
generate_forbid_free_flag_density_theorems 2 1 5 ForbidGraph

/-- SDP certificate matrix for block 1 (rational, 6×6),
paired with `v`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M : Matrix (Fin 6) (Fin 6) ℚ :=
  !![(1 / 2 : ℚ), (1 / 12 : ℚ), (1 / 6 : ℚ), (-7 / 36 : ℚ), (-1 / 9 : ℚ), (-11 / 12 : ℚ);
    (1 / 12 : ℚ), (1 / 2 : ℚ), 0, (-1 / 3 : ℚ), (7 / 12 : ℚ), (-1 : ℚ);
    (1 / 6 : ℚ), 0, (3 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 : ℚ);
    (-7 / 36 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (7 / 18 : ℚ), (-7 / 12 : ℚ), (7 / 6 : ℚ);
    (-1 / 9 : ℚ), (7 / 12 : ℚ), (1 / 6 : ℚ), (-7 / 12 : ℚ), (23 / 18 : ℚ), (-17 / 12 : ℚ);
    (-11 / 12 : ℚ), (-1 : ℚ), (-2 : ℚ), (7 / 6 : ℚ), (-17 / 12 : ℚ), (6 : ℚ)]
noncomputable def M_real : Matrix (Fin 6) (Fin 6) ℝ :=
  ratMatrixToReal M
-- Candidate exact-rational LDLᵀ witness for `M`: `M = LM * diag dM * LMᵀ`
-- with `LM` unit lower triangular. Computed by the translator and re-checked below by
-- `psd_real_ldlt`, which proves the factorization and `0 ≤ dM` inside Lean; an
-- incorrect witness is rejected rather than trusted.
def dM : Fin 6 → ℚ :=
  ![(1 / 2 : ℚ), (35 / 72 : ℚ), (101 / 70 : ℚ), (71 / 606 : ℚ), 0, (241 / 426 : ℚ)]
def LM : Matrix (Fin 6) (Fin 6) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (1 / 3 : ℚ), (-2 / 35 : ℚ), (1 : ℚ), 0, 0, 0;
    (-7 / 18 : ℚ), (-13 / 21 : ℚ), (-25 / 303 : ℚ), (1 : ℚ), 0, 0;
    (-2 / 9 : ℚ), (26 / 21 : ℚ), (50 / 303 : ℚ), (-2 : ℚ), (1 : ℚ), 0;
    (-11 / 6 : ℚ), (-61 / 35 : ℚ), (-122 / 101 : ℚ), (86 / 71 : ℚ), 0, (1 : ℚ)]
/-- `M_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M_real_posSemidef : M_real.PosSemidef := by
  psd_real_ldlt M LM dM

/-- Label type for block 1 (flagmatic type '1:'). -/
def σ : FlagType (Fin 1) := FlagType_1_0
/-- Flag vector for block 1: the 6 σ-type 3-vertex flags paired with M. -/
noncomputable def v : FlagAlgebraVec σ 6 := ![
  FlagAlgebra_3_1_0_0,
  FlagAlgebra_3_1_0_1,
  FlagAlgebra_3_1_0_2,
  FlagAlgebra_3_1_0_4,
  FlagAlgebra_3_1_0_3,
  FlagAlgebra_3_1_0_5
]

/-- Objective expansion. `flag_expand_hfree 5 ForbidGraph` expands `FlagAlgebra_2_0_0_1`
over the 5-vertex ForbidGraph-free flags, rewriting the expansion theorem onto the
generated set `flagSetHfree_5_0_0_ForbidGraph`. Under the hypothesis the flags
containing ForbidGraph have density zero, so they never enter the sum. -/
lemma C5freeEdge_reduced_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[ForbidGraph.toLabeledGraph.graph] (1 / 10 : ℝ) • FlagAlgebra_5_0_0_1 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_2 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_3 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_4 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_5 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_6 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_7 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_8 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_9 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_10 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_11 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_12 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_13 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_14 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_15 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_16 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_17 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_18 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_20 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_21 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_22 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_23 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_25 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_26 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_27
  := by
  flag_expand_hfree 5 ForbidGraph

/-- **Main theorem (auto-generated).**
Every graph with no C₅ subgraph has edge density at most 1/2.

Certificate description: '2-graph; maximize 2:12 density; forbid 5:1223344551'
Bound: '1/2'. -/
theorem C5freeEdge_reduced_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[ForbidGraph.toLabeledGraph.graph] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[ForbidGraph.toLabeledGraph.graph]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_subgraph ForbidGraph 5)))
  rw [forbidLEWith_rw_left_add_right C5freeEdge_reduced_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_six, add_assoc]
  reduce_downward_flagmul

  expand_one_hfree_at 5 ForbidGraph

  simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end C5freeEdgeReduced
