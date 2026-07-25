-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 3:121323').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/Mantel_cert.json \
--     LeanFlagAlgebras/Flagmatic/Mantel.lean --namespace Mantel --force

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

namespace Mantel

-- The forbidden graph, as the 3-vertex `Sym2Graph` term `K3`: the complete graph
-- K₃, for which containing a copy and containing an induced copy coincide.
-- The generation commands below prune against it: a flag containing K3 is never
-- enumerated, and they emit the K3-free flags, the completeness lemma for that set, and
-- the pair-density / multiplication theorems the proof consumes.
def K3 : Sym2Graph 3 := completeSym2Graph 3
-- Every generated bridging lemma is proved by `decide +kernel`, so this file
-- introduces no compiled-evaluation axiom: `#print axioms` on the main theorem
-- below lists only Lean's own three.
set_option flagGen.kernelDecide true
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 2 K3
generate_forbid_free_empty_typed_flags 3 K3
generate_forbid_free_flags 2 1 0 K3
generate_forbid_free_flags 3 1 0 K3
generate_forbid_free_flag_pair_density_theorems 2 3 1 0 K3
generate_forbid_free_mul_theorems 2 3 1 0 K3
generate_forbid_free_flag_density_theorems 2 1 3 K3

/-- SDP certificate matrix for block 1 (rational, 2×2),
paired with `v`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), (-1 / 2 : ℚ);
    (-1 / 2 : ℚ), (1 / 2 : ℚ)]
noncomputable def M_real : Matrix (Fin 2) (Fin 2) ℝ :=
  ratMatrixToReal M
-- Candidate exact-rational LDLᵀ witness for `M`: `M = LM * diag dM * LMᵀ`
-- with `LM` unit lower triangular. Computed by the translator and re-checked below by
-- `psd_real_ldlt`, which proves the factorization and `0 ≤ dM` inside Lean; an
-- incorrect witness is rejected rather than trusted.
def dM : Fin 2 → ℚ :=
  ![(1 / 2 : ℚ), 0]
def LM : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 : ℚ), 0;
    (-1 : ℚ), (1 : ℚ)]
/-- `M_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M_real_posSemidef : M_real.PosSemidef := by
  psd_real_ldlt M LM dM

/-- Label type for block 1 (flagmatic type '1:'). -/
def σ : FlagType (Fin 1) := FlagType_1_0
/-- Flag vector for block 1: the 2 σ-type 2-vertex flags paired with M. -/
noncomputable def v : FlagAlgebraVec σ 2 := ![
  FlagAlgebra_2_1_0_0,
  FlagAlgebra_2_1_0_1
]

/-- Objective expansion. `flag_expand_hfree 3 K3` expands `FlagAlgebra_2_0_0_1`
over the 3-vertex K3-free flags, rewriting the expansion theorem onto the
generated set `flagSetHfree_3_0_0_K3`. Under the hypothesis the flags
containing K3 have density zero, so they never enter the sum. -/
lemma Mantel_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[completeGraph (Fin 3)] (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
  := by
  flag_expand_hfree 3 K3

/-- **Main theorem (auto-generated).**
Every graph with no K₃ subgraph has edge density at most 1/2.

Certificate description: '2-graph; maximize 2:12 density; forbid 3:121323'
Bound: '1/2'. -/
theorem Mantel_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 3)] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 3)]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 3) 3)))
  rw [forbidLEWith_rw_left_add_right Mantel_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_hfree_at 3 K3

  simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end Mantel
