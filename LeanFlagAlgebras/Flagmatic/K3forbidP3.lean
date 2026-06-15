-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 3:1213 density; forbid 3:121323').
-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-skeleton)
-- Matrix defs (M_t, dM_t, LM_t) and PSD proofs are filled in; the main
-- theorem body still needs to be written (see TODO at the bottom).

import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.FlagMulReduce
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.API.FlagSumSort
import LeanFlagAlgebras.API.Matrix.PosSemiDef
import LeanFlagAlgebras.Forbid.CommonGraphs

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix

namespace K3forbidP3

generate_forbid_density_theorems 3 K3
generate_flag_pair_density_theorems 2 3 1 0 K3
generate_forbid_mul_theorems 2 3 1 0 K3

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
lemma dM_nonneg (i : Fin 2) : 0 ≤ dM i := by
  fin_cases i <;> norm_num [dM]
lemma M_eq_LDL : M = LM * Matrix.diagonal dM * LMᵀ := by
  decide +kernel
theorem M_posSemidef : M.PosSemidef := by
  exact posSemidef_of_LDLt dM_nonneg M_eq_LDL
lemma dM_real_nonneg (i : Fin 2) : 0 ≤ (dM i : ℝ) := by
  exact_mod_cast dM_nonneg i
lemma M_real_eq_LDL :
    M_real = (ratMatrixToReal LM * Matrix.diagonal (fun i => (dM i : ℝ))) * (ratMatrixToReal LM)ᵀ := by
  calc
    M_real = ratMatrixToReal (LM * Matrix.diagonal dM * LMᵀ) := by
      simp [M_real, ratMatrixToReal, M_eq_LDL]
    _ = (ratMatrixToReal LM * Matrix.diagonal (fun i => (dM i : ℝ))) * (ratMatrixToReal LM)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `M_real` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem M_real_posSemidef : M_real.PosSemidef := by
  exact posSemidef_of_LDLt_real dM_real_nonneg M_real_eq_LDL

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
    : FlagAlgebra_3_0_0_2 ≤[K3.toFinFlag] (3 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_3_0_0_2 ≤[K3.toFinFlag]
            FlagAlgebra_3_0_0_2 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLE_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLE_refl K3.toFinFlag FlagAlgebra_3_0_0_2
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 3)))

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_at 3

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end K3forbidP3
