import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.FlagMulReduce
import LeanFlagAlgebras.Flags.Densities.MulLoader
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.API.FlagSumSort
import LeanFlagAlgebras.API.Matrix.PosSemiDef
import LeanFlagAlgebras.Forbid.CommonGraphs

/-! # API.C4TuranAPI — a 4-vertex graph density bound for K₃-free graphs

Per-problem density-bound proof on the API automation layer. The headline
result `C4_flagAlgebra_API` shows that for K₃-free graphs the density of the
4-vertex flag `FlagAlgebra_4_0_0_8` is at most `3/8`:

  `FlagAlgebra_4_0_0_8 ≤[K3.toFinFlag] (3 / 8 : ℝ) • (1 : FlagAlgebra ∅ₜ)`.

The certificate uses two PSD matrices `M₁` (4×4) and `M₂` (3×3), each shown
positive semidefinite via an explicit LDLᵀ factorization (rational, then cast
to ℝ). These produce non-negative quadratic-form terms that are added to the
bound and discharged with the API tactics. -/

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix

namespace C4TuranAPI

/-- First SDP certificate matrix (rational, 4×4); paired with `v₁` over the
σ₁ = `FlagType_2_0` type. -/
def M₁ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(3 / 8 : ℚ), 0, 0, (-3 / 8: ℚ);
      0, 0, 0, 0;
      0, 0, 0, 0;
    (-3 / 8 : ℚ), 0, 0, (3 / 8 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 4) (Fin 4) ℝ :=
  ratMatrixToReal M₁
def dM₁ : Fin 4 → ℚ :=
  ![(3 / 8 : ℚ), 0, 0, 0]
def LM₁ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), 0, 0, 0;
   0, (1 : ℚ), 0, 0;
   0, 0, (1 : ℚ), 0;
   (-1 : ℚ), 0, 0, (1 : ℚ)]
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

/-- Second SDP certificate matrix (rational, 3×3); paired with `v₂` over the
σ₂ = `FlagType_2_1` type. -/
def M₂ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 0;
      0, (9 / 8 : ℚ), (-9 / 8 : ℚ);
      0, (-9 / 8 : ℚ), (9 / 8 : ℚ)
    ]
noncomputable def M₂_real : Matrix (Fin 3) (Fin 3) ℝ :=
  ratMatrixToReal M₂
def dM₂ : Fin 3 → ℚ :=
  ![0, (9 / 8 : ℚ), 0]
def LM₂ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 0, 0;
   0, (1 : ℚ), 0;
   0, (-1 : ℚ), (1 : ℚ)]
lemma dM₂_nonneg (i : Fin 3) : 0 ≤ dM₂ i := by
  fin_cases i <;> norm_num [dM₂]
lemma M₂_eq_LDL : M₂ = LM₂ * Matrix.diagonal dM₂ * LM₂ᵀ := by
  decide +kernel
theorem M₂_posSemidef : M₂.PosSemidef := by
  exact posSemidef_of_LDLt dM₂_nonneg M₂_eq_LDL
lemma dM₂_real_nonneg (i : Fin 3) : 0 ≤ (dM₂ i : ℝ) := by
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

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_4_K3_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K3.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K3.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K3.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K3.json"

/-- Label type for the first quadratic form: the 2-vertex no-edge type. -/
def σ₁ : FlagType (Fin 2) := FlagType_2_0
/-- Flag vector paired with `M₁` (the four σ₁-type 3-vertex flags). -/
noncomputable def v₁ : FlagAlgebraVec σ₁ 4 := ![
  FlagAlgebra_3_2_0_0, FlagAlgebra_3_2_0_1, FlagAlgebra_3_2_0_2, FlagAlgebra_3_2_0_3
]
/-- Label type for the second quadratic form: the 2-vertex edge type. -/
def σ₂ : FlagType (Fin 2) := FlagType_2_1
/-- Flag vector paired with `M₂` (the three σ₂-type 3-vertex flags). -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 3 := ![
  FlagAlgebra_3_2_1_0, FlagAlgebra_3_2_1_1, FlagAlgebra_3_2_1_2
]

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **K₃-free 4-vertex density bound.** The density of `FlagAlgebra_4_0_0_8` in
K₃-free graphs is at most `3/8`. Proved by adding the two PSD quadratic-form
(SOS) terms from `M₁_real`/`v₁` and `M₂_real`/`v₂`, then reducing with the API
tactics. -/
theorem C4_flagAlgebra_API
    : FlagAlgebra_4_0_0_8 ≤[K3.toFinFlag] (3 / 8 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_4_0_0_8 ≤[K3.toFinFlag]
            FlagAlgebra_4_0_0_8 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀
    := by
    apply forbidLE_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLE_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLE_refl K3.toFinFlag FlagAlgebra_4_0_0_8
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 4)))

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_four, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂, Fin.sum_univ_three, add_assoc]
  reduce_downward_flagmul

  expand_one_at 4

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end C4TuranAPI
