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

namespace C4Turan

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
  exact posSemidef_of_eq_mul_diagonal_mul_transpose dM₁_nonneg M₁_eq_LDL
lemma dM₁_real_nonneg (i : Fin 4) : 0 ≤ (dM₁ i : ℝ) := by
  exact_mod_cast dM₁_nonneg i
lemma M₁_real_eq_LDL :
    M₁_real = (ratMatrixToReal LM₁ * Matrix.diagonal (fun i => (dM₁ i : ℝ))) * (ratMatrixToReal LM₁)ᵀ := by
  calc
    M₁_real = ratMatrixToReal (LM₁ * Matrix.diagonal dM₁ * LM₁ᵀ) := by
      simp [M₁_real, ratMatrixToReal, M₁_eq_LDL]
    _ = (ratMatrixToReal LM₁ * Matrix.diagonal (fun i => (dM₁ i : ℝ))) * (ratMatrixToReal LM₁)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real dM₁_real_nonneg M₁_real_eq_LDL

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
  exact posSemidef_of_eq_mul_diagonal_mul_transpose dM₂_nonneg M₂_eq_LDL
lemma dM₂_real_nonneg (i : Fin 3) : 0 ≤ (dM₂ i : ℝ) := by
  exact_mod_cast dM₂_nonneg i
lemma M₂_real_eq_LDL :
    M₂_real = (ratMatrixToReal LM₂ * Matrix.diagonal (fun i => (dM₂ i : ℝ))) * (ratMatrixToReal LM₂)ᵀ := by
  calc
    M₂_real = ratMatrixToReal (LM₂ * Matrix.diagonal dM₂ * LM₂ᵀ) := by
      simp [M₂_real, ratMatrixToReal, M₂_eq_LDL]
    _ = (ratMatrixToReal LM₂ * Matrix.diagonal (fun i => (dM₂ i : ℝ))) * (ratMatrixToReal LM₂)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
theorem M₂_real_posSemidef : M₂_real.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real dM₂_real_nonneg M₂_real_eq_LDL

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_4_K3_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K3.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_0_from_3_2_0_forbid_K3.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K3.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_4_2_1_from_3_2_1_forbid_K3.json"



def σ₁ : FlagType (Fin 2) := FlagType_2_0
noncomputable def v₁ : FlagAlgebraVec σ₁ 4 := ![
  FlagAlgebra_3_2_0_0, FlagAlgebra_3_2_0_1, FlagAlgebra_3_2_0_2, FlagAlgebra_3_2_0_3
]
def σ₂ : FlagType (Fin 2) := FlagType_2_1
noncomputable def v₂ : FlagAlgebraVec σ₂ 3 := ![
  FlagAlgebra_3_2_1_0, FlagAlgebra_3_2_1_1, FlagAlgebra_3_2_1_2
]

generate_unitVector_lemmas 4 11

set_option maxHeartbeats 0
set_option maxRecDepth 1500

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
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_expand K3.toFinFlag 4)))

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_four, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂, Fin.sum_univ_three, add_assoc]
  reduce_downward_flagmul

  expand_one_at 4

  simp [smul_smul, downward_add, downward_smul]
  ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end C4Turan
