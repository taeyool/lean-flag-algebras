-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 3:121323').
-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-skeleton)
-- Matrix defs (M_t, dM_t, LM_t) and PSD proofs are filled in; the main
-- theorem body still needs to be written (see TODO at the bottom).

import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.ReduceFlagMul
import LeanFlagAlgebras.Flags.Densities.MulLoader
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.Utils.SortTactic
import LeanFlagAlgebras.Utils.Matrix.PosSemiDef
import LeanFlagAlgebras.Forbid.CommonGraphs

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix

namespace Mantel

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_3_K3_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_3_1_0_from_2_1_0.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_3_1_0_from_2_1_0.json"

/-- SDP certificate matrix for block 1 (rational, 2×2),
paired with `v`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), (-1 / 2 : ℚ);
    (-1 / 2 : ℚ), (1 / 2 : ℚ)]
noncomputable def M_real : Matrix (Fin 2) (Fin 2) ℝ :=
  ratMatrixToReal M
def dM : Fin 2 → ℚ :=
  ![(1 / 2 : ℚ), 0]
def LM : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 : ℚ), 0;
    (-1 : ℚ), (1 : ℚ)]
lemma dM_nonneg (i : Fin 2) : 0 ≤ dM i := by
  fin_cases i <;> norm_num [dM]
lemma M_eq_LDL : M = LM * Matrix.diagonal dM * LMᵀ := by
  decide +kernel
theorem M_posSemidef : M.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose dM_nonneg M_eq_LDL
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
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real dM_real_nonneg M_real_eq_LDL

/-- Label type for block 1 (flagmatic type '1:'). -/
def σ : FlagType (Fin 1) := FlagType_1_0
/-- Flag vector for block 1: the 2 σ-type 2-vertex flags paired with M. -/
noncomputable def v : FlagAlgebraVec σ 2 := ![
  FlagAlgebra_2_1_0_0,
  FlagAlgebra_2_1_0_1
]

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **Main theorem (auto-generated statement, proof body TODO).**
Certificate description: '2-graph; maximize 2:12 density; forbid 3:121323'
Bound: '1/2'. -/
theorem mantel_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end Mantel
