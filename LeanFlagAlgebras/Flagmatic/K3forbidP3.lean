-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 3:1213 density; forbid 3:121323').
-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-skeleton)
-- Matrix defs (M_t, dM_t, LM_t) and PSD proofs are filled in; the main
-- theorem body still needs to be written (see TODO at the bottom).

import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.Automation.Basic
import LeanFlagAlgebras.Automation.FlagMulReduce
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Automation.FlagSumSort
import LeanFlagAlgebras.Automation.Matrix.PosSemiDef
import LeanFlagAlgebras.Forbid.CommonGraphs

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K3forbidP3

-- Edge-based, pruning-backed forbid-free generation (decision D2): the forbidden graph is the
-- `Sym2Graph 3` term `K3 := completeSym2Graph 3` (no canonical forbidden flag); the K3-containing
-- flags are never generated. The pruned commands emit only the K3-free flags, their completeness,
-- and the forbid-free pair-density / multiplication theorems.
def K3 : Sym2Graph 3 := completeSym2Graph 3
generate_pruned_forbid_free_empty_typed_flags 2 K3
generate_pruned_forbid_free_empty_typed_flags 3 K3
generate_pruned_forbid_free_flags 2 1 0 K3
generate_pruned_forbid_free_flags 3 1 0 K3
generate_pruned_flag_pair_density_theorems 2 3 1 0 K3
generate_pruned_forbid_free_mul_theorems 2 3 1 0 K3 (completeGraph (Fin 3)) (completeSym2Graph_finFlag_mem_forbiddenFlags 3)

/-- SDP certificate matrix for block 1 (rational, 2×2),
paired with `v`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(3 / 4 : ℚ), (-3 / 4 : ℚ);
    (-3 / 4 : ℚ), (3 / 4 : ℚ)]
noncomputable def M_real : Matrix (Fin 2) (Fin 2) ℝ :=
  ratMatrixToReal M
def dM : Fin 2 → ℚ :=
  ![(3 / 4 : ℚ), 0]
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

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 3:1213 density; forbid 3:121323'
Bound: '3/4'. -/
theorem K3forbidP3_flagAlgebra
    : FlagAlgebra_3_0_0_2 ≤[completeGraph (Fin 3)] (3 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_3_0_0_2 ≤[completeGraph (Fin 3)]
            FlagAlgebra_3_0_0_2 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLEWith_refl _ FlagAlgebra_3_0_0_2
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 3) 3)))

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_hfree_at 3 K3

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end K3forbidP3
