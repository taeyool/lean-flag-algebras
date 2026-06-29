-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 4:121314232434').
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
import LeanFlagAlgebras.Automation.FlagExpand
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K4turan

-- Edge-based, pruning-backed forbid-free generation (decision D2): the forbidden graph is the
-- `Sym2Graph 4` term `K4 := completeSym2Graph 4` (no canonical forbidden flag); the K4-containing
-- flags are never generated (genuine pruning). The pruned commands emit only the K4-free flags,
-- their completeness, and the forbid-free pair-density / multiplication theorems for both σ-types.
def K4 : Sym2Graph 4 := completeSym2Graph 4
generate_pruned_forbid_free_empty_typed_flags 2 K4
generate_pruned_forbid_free_empty_typed_flags 3 K4
generate_pruned_forbid_free_empty_typed_flags 4 K4
generate_pruned_forbid_free_flags 3 2 0 K4
generate_pruned_forbid_free_flags 3 2 1 K4
generate_pruned_forbid_free_flags 4 2 0 K4
generate_pruned_forbid_free_flags 4 2 1 K4
generate_pruned_flag_pair_density_theorems 3 4 2 0 K4
generate_pruned_forbid_free_mul_theorems 3 4 2 0 K4 (completeGraph (Fin 4)) (completeSym2Graph_finFlag_mem_forbiddenFlags 4)
generate_pruned_flag_pair_density_theorems 3 4 2 1 K4
generate_pruned_forbid_free_mul_theorems 3 4 2 1 K4 (completeGraph (Fin 4)) (completeSym2Graph_finFlag_mem_forbiddenFlags 4)

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
/-- `M₁_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  psd_real_ldlt M₁ LM₁ dM₁

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
/-- `M₂_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₂_real_posSemidef : M₂_real.PosSemidef := by
  psd_real_ldlt M₂ LM₂ dM₂

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

/-- Edge-based forbid-free expansion of the objective: `FlagAlgebra_2_0_0_1` is expanded directly
over the K4-free 4-vertex flags via `flag_expand_hfree 4 K4` (`basisVector_quot_inducedForbidEq_sum`
rewritten onto `flagSetHfree_4_0_0_K4`; the K4 term `Flag_4_0_0_10` is dropped automatically). -/
lemma K4turan_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[completeGraph (Fin 4)]
        (1 / 6 : ℝ) • FlagAlgebra_4_0_0_1 + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_2 + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_3 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_4 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_5 + (1 / 2 : ℝ) • FlagAlgebra_4_0_0_6 + (2 / 3 : ℝ) • FlagAlgebra_4_0_0_7 + (2 / 3 : ℝ) • FlagAlgebra_4_0_0_8 + (5 / 6 : ℝ) • FlagAlgebra_4_0_0_9
  := by
  flag_expand_hfree 4 K4 (completeSym2Graph_finFlag_mem_forbiddenFlags 4)

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 2:12 density; forbid 4:121314232434'
Bound: '2/3'. -/
theorem K4turan_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 4)] (2 / 3 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 4)]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLEWith_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K4⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 4) 4)))
  simp only [add_assoc]
  rw [forbidLEWith_rw_left_add_right K4turan_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_four, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂]
  reduce_downward_flagmul

  expand_one_hfree_at 4 K4

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end K4turan
