-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 4:12132434 density; forbid 3:121323').
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

namespace K3forbidC4

-- Edge-based, pruning-backed forbid-free generation (decision D2): the forbidden graph is the
-- `Sym2Graph 3` term `K3 := completeSym2Graph 3` (no canonical forbidden flag); the K3-containing
-- flags are never generated. The pruned commands emit only the K3-free flags (the C₄ objective
-- `FlagAlgebra_4_0_0_8` among them), their completeness, and the forbid-free pair-density /
-- multiplication theorems for both σ-types.
def K3 : Sym2Graph 3 := completeSym2Graph 3
generate_pruned_forbid_free_empty_typed_flags 3 K3
generate_pruned_forbid_free_empty_typed_flags 4 K3
generate_pruned_forbid_free_flags 3 2 0 K3
generate_pruned_forbid_free_flags 3 2 1 K3
generate_pruned_forbid_free_flags 4 2 0 K3
generate_pruned_forbid_free_flags 4 2 1 K3
generate_pruned_flag_pair_density_theorems 3 4 2 0 K3
generate_pruned_forbid_free_mul_theorems 3 4 2 0 K3 (completeGraph (Fin 3)) (completeSym2Graph_finFlag_mem_forbiddenFlags 3)
generate_pruned_flag_pair_density_theorems 3 4 2 1 K3
generate_pruned_forbid_free_mul_theorems 3 4 2 1 K3 (completeGraph (Fin 3)) (completeSym2Graph_finFlag_mem_forbiddenFlags 3)

/-- SDP certificate matrix for block 1 (rational, 4×4),
paired with `v₁`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₁ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(3 / 8 : ℚ), (-3 / 32 : ℚ), (-3 / 32 : ℚ), (-3 / 8 : ℚ);
    (-3 / 32 : ℚ), (27 / 32 : ℚ), (-9 / 32 : ℚ), (3 / 32 : ℚ);
    (-3 / 32 : ℚ), (-9 / 32 : ℚ), (27 / 32 : ℚ), (3 / 32 : ℚ);
    (-3 / 8 : ℚ), (3 / 32 : ℚ), (3 / 32 : ℚ), (3 / 8 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 4) (Fin 4) ℝ :=
  ratMatrixToReal M₁
def dM₁ : Fin 4 → ℚ :=
  ![(3 / 8 : ℚ), (105 / 128 : ℚ), (99 / 140 : ℚ), 0]
def LM₁ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), 0, 0, 0;
    (-1 / 4 : ℚ), (1 : ℚ), 0, 0;
    (-1 / 4 : ℚ), (-13 / 35 : ℚ), (1 : ℚ), 0;
    (-1 : ℚ), 0, 0, (1 : ℚ)]
/-- `M₁_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  psd_real_ldlt M₁ LM₁ dM₁

/-- SDP certificate matrix for block 2 (rational, 3×3),
paired with `v₂`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₂ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 / 2 : ℚ), 0, 0;
    0, (9 / 8 : ℚ), (-9 / 8 : ℚ);
    0, (-9 / 8 : ℚ), (9 / 8 : ℚ)]
noncomputable def M₂_real : Matrix (Fin 3) (Fin 3) ℝ :=
  ratMatrixToReal M₂
def dM₂ : Fin 3 → ℚ :=
  ![(1 / 2 : ℚ), (9 / 8 : ℚ), 0]
def LM₂ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 0, 0;
    0, (1 : ℚ), 0;
    0, (-1 : ℚ), (1 : ℚ)]
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
/-- Flag vector for block 2: the 3 σ-type 3-vertex flags paired with M₂. -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 3 := ![
  FlagAlgebra_3_2_1_0,
  FlagAlgebra_3_2_1_1,
  FlagAlgebra_3_2_1_2
]

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 4:12132434 density; forbid 3:121323'
Bound: '3/8'. -/
theorem K3forbidC4_flagAlgebra
    : FlagAlgebra_4_0_0_8 ≤[completeGraph (Fin 3)] (3 / 8 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_4_0_0_8 ≤[completeGraph (Fin 3)]
            FlagAlgebra_4_0_0_8 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLEWith_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLEWith_refl _ FlagAlgebra_4_0_0_8
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 3) 4)))

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_four, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂, Fin.sum_univ_three, add_assoc]
  reduce_downward_flagmul

  expand_one_hfree_at 4 K3

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end K3forbidC4
