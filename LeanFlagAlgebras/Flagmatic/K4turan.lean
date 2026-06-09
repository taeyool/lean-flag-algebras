-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 4:121314232434').
-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-skeleton)
-- Matrix defs (M_t, dM_t, LM_t) and PSD proofs are filled in; the main
-- theorem body still needs to be written (see TODO at the bottom).

import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.FlagMulReduce
import LeanFlagAlgebras.Flags.Densities.MulLoader
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.API.FlagSumSort
import LeanFlagAlgebras.API.Matrix.PosSemiDef
import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.API.FlagExpand
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K4turan

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_4_K4_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K4.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K4.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K4.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K4.json"

/-- SDP certificate matrix for block 1 (rational, 4×4),
paired with `v₁`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₁ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(2 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ);
    0, (3 / 4 : ℚ), (-5 / 12 : ℚ), 0;
    0, (-5 / 12 : ℚ), (3 / 4 : ℚ), 0;
    (-1 / 3 : ℚ), 0, 0, (1 / 6 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 4) (Fin 4) ℝ :=
  ratMatrixToReal M₁
def dM₁ : Fin 4 → ℚ :=
  ![(2 / 3 : ℚ), (3 / 4 : ℚ), (14 / 27 : ℚ), 0]
def LM₁ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), 0, 0, 0;
    0, (1 : ℚ), 0, 0;
    0, (-5 / 9 : ℚ), (1 : ℚ), 0;
    (-1 / 2 : ℚ), 0, 0, (1 : ℚ)]
lemma dM₁_nonneg (i : Fin 4) : 0 ≤ dM₁ i := by
  fin_cases i <;> norm_num [dM₁]
lemma M₁_eq_LDL : M₁ = LM₁ * Matrix.diagonal dM₁ * LM₁ᵀ := by
  decide +kernel
theorem M₁_posSemidef : M₁.PosSemidef := by
  exact posSemidef_of_LDLt dM₁_nonneg M₁_eq_LDL
lemma dM₁_real_nonneg (i : Fin 4) : 0 ≤ (dM₁ i : ℝ) := by
  exact_mod_cast dM₁_nonneg i
lemma M₁_real_eq_LDL :
    M₁_real = (ratMatrixToReal LM₁ * Matrix.diagonal (fun i => (dM₁ i : ℝ))) * (ratMatrixToReal LM₁)ᵀ := by
  calc
    M₁_real = ratMatrixToReal (LM₁ * Matrix.diagonal dM₁ * LM₁ᵀ) := by
      simp [M₁_real, ratMatrixToReal, M₁_eq_LDL]
    _ = (ratMatrixToReal LM₁ * Matrix.diagonal (fun i => (dM₁ i : ℝ))) * (ratMatrixToReal LM₁)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `M₁_real` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  exact posSemidef_of_LDLt_real dM₁_real_nonneg M₁_real_eq_LDL

/-- SDP certificate matrix for block 2 (rational, 4×4),
paired with `v₂`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₂ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (-2 / 3 : ℚ);
    (1 / 3 : ℚ), (2 / 3 : ℚ), (-1 / 12 : ℚ), (-7 / 12 : ℚ);
    (1 / 3 : ℚ), (-1 / 12 : ℚ), (2 / 3 : ℚ), (-7 / 12 : ℚ);
    (-2 / 3 : ℚ), (-7 / 12 : ℚ), (-7 / 12 : ℚ), (7 / 6 : ℚ)]
noncomputable def M₂_real : Matrix (Fin 4) (Fin 4) ℝ :=
  ratMatrixToReal M₂
def dM₂ : Fin 4 → ℚ :=
  ![(1 : ℚ), (5 / 9 : ℚ), (39 / 80 : ℚ), 0]
def LM₂ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), 0, 0, 0;
    (1 / 3 : ℚ), (1 : ℚ), 0, 0;
    (1 / 3 : ℚ), (-7 / 20 : ℚ), (1 : ℚ), 0;
    (-2 / 3 : ℚ), (-13 / 20 : ℚ), (-1 : ℚ), (1 : ℚ)]
lemma dM₂_nonneg (i : Fin 4) : 0 ≤ dM₂ i := by
  fin_cases i <;> norm_num [dM₂]
lemma M₂_eq_LDL : M₂ = LM₂ * Matrix.diagonal dM₂ * LM₂ᵀ := by
  decide +kernel
theorem M₂_posSemidef : M₂.PosSemidef := by
  exact posSemidef_of_LDLt dM₂_nonneg M₂_eq_LDL
lemma dM₂_real_nonneg (i : Fin 4) : 0 ≤ (dM₂ i : ℝ) := by
  exact_mod_cast dM₂_nonneg i
lemma M₂_real_eq_LDL :
    M₂_real = (ratMatrixToReal LM₂ * Matrix.diagonal (fun i => (dM₂ i : ℝ))) * (ratMatrixToReal LM₂)ᵀ := by
  calc
    M₂_real = ratMatrixToReal (LM₂ * Matrix.diagonal dM₂ * LM₂ᵀ) := by
      simp [M₂_real, ratMatrixToReal, M₂_eq_LDL]
    _ = (ratMatrixToReal LM₂ * Matrix.diagonal (fun i => (dM₂ i : ℝ))) * (ratMatrixToReal LM₂)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `M₂_real` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem M₂_real_posSemidef : M₂_real.PosSemidef := by
  exact posSemidef_of_LDLt_real dM₂_real_nonneg M₂_real_eq_LDL

/-- Label type for block 1 (flagmatic type '2:'). -/
def σ₁ : FlagType (Fin 2) := FlagType_2_0
/-- Flag vector for block 1: the 4 σ-type 3-vertex flags paired with M₁. -/
noncomputable def v₁ : FlagAlgebraVec σ₁ 4 := ![
  FlagAlgebra_3_2_0_0,
  FlagAlgebra_3_2_0_1,
  FlagAlgebra_3_2_0_2,
  FlagAlgebra_3_2_0_3
]

/-- Label type for block 2 (flagmatic type '2:12'). -/
def σ₂ : FlagType (Fin 2) := FlagType_2_1
/-- Flag vector for block 2: the 4 σ-type 3-vertex flags paired with M₂. -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 4 := ![
  FlagAlgebra_3_2_1_0,
  FlagAlgebra_3_2_1_1,
  FlagAlgebra_3_2_1_2,
  FlagAlgebra_3_2_1_3
]

set_option maxHeartbeats 0
set_option maxRecDepth 1500

-- Auto-generated `flagDensity₁` evaluation table (used by
-- `flag_expand 4` to evaluate density coefficients).
@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_0
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_0 = 0
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_1
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_1 = 1 / 6
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_2
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_2 = 1 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_3
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_3 = 1 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_3]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_4
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_4 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_4]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_5
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_5 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_5]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_6
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_6 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_6]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_7
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_7 = 2 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_7]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_8
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_8 = 2 / 3
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_8]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_9
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_9 = 5 / 6
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_9]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_4_0_0_10
    : flagDensity₁ Flag_2_0_0_1 Flag_4_0_0_10 = 1
  := by
  dsimp [Flag_2_0_0_1, Flag_4_0_0_10]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/-- Auto-generated expansion of the objective under the forbid relation:
`FlagAlgebra_2_0_0_1 =[K4.toFinFlag]` (sum over admissible 4-vertex graphs). -/
lemma K4turan_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[K4.toFinFlag] (1 / 6 : ℝ) • FlagAlgebra_4_0_0_1 + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_2 + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_3 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_4 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_5 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_6 + (2 / 3 : ℝ) • FlagAlgebra_4_0_0_7 + (2 / 3 : ℝ) • FlagAlgebra_4_0_0_8 + (5 / 6 : ℝ) • FlagAlgebra_4_0_0_9
  := by
  have h_unit_10 : (FlagAlgebra_4_0_0_10 : FlagAlgebra ∅ₜ) = ⟦basisVector (⟨4, Flag_4_0_0_10⟩ : FinFlag ∅ₜ)⟧
    := (Quotient.out_inj.mp rfl).symm
  have h_zero_10 : (FlagAlgebra_4_0_0_10 : FlagAlgebra ∅ₜ) =[K4.toFinFlag] 0 := by
    rw [h_unit_10]
    apply basisVector_forbidEq_zero
    rw [unlabel_emptyType]
    exact lt_of_le_of_ne
      (flagListDensity₁_ge_zero K4.toFinFlag.2 Flag_4_0_0_10)
      (Ne.symm flagDensity1_K4_Flag_4_0_0_10_ne_zero)
  have h_eq : FlagAlgebra_2_0_0_1 =[K4.toFinFlag]
      (1 / 6 : ℝ) • FlagAlgebra_4_0_0_1 + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_2 + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_3 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_4 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_5 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_6 + (2 / 3 : ℝ) • FlagAlgebra_4_0_0_7 + (2 / 3 : ℝ) • FlagAlgebra_4_0_0_8 + (5 / 6 : ℝ) • FlagAlgebra_4_0_0_9 + FlagAlgebra_4_0_0_10 :=
    forbidEq_of_eq (by flag_expand 4)
  rw [forbidEq_rw_right_add_left h_zero_10, add_zero] at h_eq
  exact h_eq

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 2:12 density; forbid 4:121314232434'
Bound: '2/3'. -/
theorem K4turan_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[K4.toFinFlag] (2 / 3 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[K4.toFinFlag]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀
    := by
    apply forbidLE_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLE_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLE_refl K4.toFinFlag FlagAlgebra_2_0_0_1
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K4.toFinFlag 4)))
  simp only [add_assoc]
  rw [forbidLE_rw_left_add_right K4turan_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_four, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂]
  reduce_downward_flagmul

  expand_one_at 4

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end K4turan
