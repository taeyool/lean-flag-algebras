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
import LeanFlagAlgebras.Utils.FlagExpansionTactic
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix
open FlagAlgebras.Compute

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

-- Auto-generated `flagDensity₁` evaluation table (used by
-- `prove_flag_expand 3` to evaluate density coefficients).
@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_0
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_0 = 0
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_1
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_1 = 1 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_2
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_2 = 2 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_3
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_3 = 1
  := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_3]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/-- Auto-generated expansion of the objective under the forbid relation:
`FlagAlgebra_2_0_0_1 =[K3.toFinFlag]` (sum over admissible 3-vertex graphs). -/
lemma mantel_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[K3.toFinFlag] (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
  := by
  have h_unit_3 : (FlagAlgebra_3_0_0_3 : FlagAlgebra ∅ₜ) = ⟦unitVector (⟨3, Flag_3_0_0_3⟩ : FinFlag ∅ₜ)⟧
    := (Quotient.out_inj.mp rfl).symm
  have h_zero_3 : (FlagAlgebra_3_0_0_3 : FlagAlgebra ∅ₜ) =[K3.toFinFlag] 0 := by
    rw [h_unit_3]
    apply unitVector_forbidEq_zero
    rw [unlabel_emptyType]
    exact lt_of_le_of_ne
      (flagListDensity₁_ge_zero K3.toFinFlag.2 Flag_3_0_0_3)
      (Ne.symm flagDensity1_K3_Flag_3_0_0_3_ne_zero)
  have h_eq : FlagAlgebra_2_0_0_1 =[K3.toFinFlag]
      (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3 :=
    forbidEq_of_eq (by prove_flag_expand 3)
  rw [forbidEq_rw_right_add_left h_zero_3, add_zero] at h_eq
  exact h_eq

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 2:12 density; forbid 3:121323'
Bound: '1/2'. -/
theorem mantel_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLE_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLE_refl K3.toFinFlag FlagAlgebra_2_0_0_1
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 3)))
  rw [forbidLE_rw_left_add_right mantel_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_at 3

  simp [smul_smul, downward_add, downward_smul]
  ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end Mantel
