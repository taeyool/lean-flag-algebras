-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 5:1213243545 density; forbid 3:121323').
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

namespace ErdosPentagon

generate_forbid_density_theorems 5 K3
generate_flag_pair_density_theorems 4 5 3 0 K3
generate_forbid_mul_theorems 4 5 3 0 K3
generate_flag_pair_density_theorems 4 5 3 1 K3
generate_forbid_mul_theorems 4 5 3 1 K3
generate_flag_pair_density_theorems 4 5 3 2 K3
generate_forbid_mul_theorems 4 5 3 2 K3

/-- SDP certificate matrix for block 1 (rational, 8×8),
paired with `v₁`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(24 / 625 : ℚ), (-10312978 / 118265625 : ℚ), (-10312978 / 118265625 : ℚ), (-10312978 / 118265625 : ℚ), (8042278 / 118265625 : ℚ), (8042278 / 118265625 : ℚ), (8042278 / 118265625 : ℚ), (-36 / 625 : ℚ);
    (-10312978 / 118265625 : ℚ), (469246 / 946125 : ℚ), (128641 / 946125 : ℚ), (128641 / 946125 : ℚ), (-3641212 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (-17833087 / 39421875 : ℚ), (5156489 / 39421875 : ℚ);
    (-10312978 / 118265625 : ℚ), (128641 / 946125 : ℚ), (469246 / 946125 : ℚ), (128641 / 946125 : ℚ), (-3641212 / 39421875 : ℚ), (-17833087 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (5156489 / 39421875 : ℚ);
    (-10312978 / 118265625 : ℚ), (128641 / 946125 : ℚ), (128641 / 946125 : ℚ), (469246 / 946125 : ℚ), (-17833087 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (5156489 / 39421875 : ℚ);
    (8042278 / 118265625 : ℚ), (-3641212 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (-17833087 / 39421875 : ℚ), (49478122 / 118265625 : ℚ), (6902497 / 118265625 : ℚ), (6902497 / 118265625 : ℚ), (-4021139 / 39421875 : ℚ);
    (8042278 / 118265625 : ℚ), (-3641212 / 39421875 : ℚ), (-17833087 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (6902497 / 118265625 : ℚ), (49478122 / 118265625 : ℚ), (6902497 / 118265625 : ℚ), (-4021139 / 39421875 : ℚ);
    (8042278 / 118265625 : ℚ), (-17833087 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (-3641212 / 39421875 : ℚ), (6902497 / 118265625 : ℚ), (6902497 / 118265625 : ℚ), (49478122 / 118265625 : ℚ), (-4021139 / 39421875 : ℚ);
    (-36 / 625 : ℚ), (5156489 / 39421875 : ℚ), (5156489 / 39421875 : ℚ), (5156489 / 39421875 : ℚ), (-4021139 / 39421875 : ℚ), (-4021139 / 39421875 : ℚ), (-4021139 / 39421875 : ℚ), (54 / 625 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₁
def dM₁ : Fin 8 → ℚ :=
  ![(24 / 625 : ℚ), (40005426955379 / 134272877343750 : ℚ), (285053562603072 / 1000135673884475 : ℚ), (210058282607733 / 791815451675200 : ℚ), 0, 0, 0, 0]
def LM₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (-5156489 / 2270700 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (-5156489 / 2270700 : ℚ), (-8332808888371 / 40005426955379 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (-5156489 / 2270700 : ℚ), (-8332808888371 / 40005426955379 : ℚ), (-8332808888371 / 31672618067008 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (4021139 / 2270700 : ℚ), (8332808888371 / 40005426955379 : ℚ), (8332808888371 / 31672618067008 : ℚ), (-1 : ℚ), (1 : ℚ), 0, 0, 0;
    (4021139 / 2270700 : ℚ), (8332808888371 / 40005426955379 : ℚ), (-1 : ℚ), 0, 0, (1 : ℚ), 0, 0;
    (4021139 / 2270700 : ℚ), (-1 : ℚ), 0, 0, 0, 0, (1 : ℚ), 0;
    (-3 / 2 : ℚ), 0, 0, 0, 0, 0, 0, (1 : ℚ)]
lemma dM₁_nonneg (i : Fin 8) : 0 ≤ dM₁ i := by
  fin_cases i <;> norm_num [dM₁]
lemma M₁_eq_LDL : M₁ = LM₁ * Matrix.diagonal dM₁ * LM₁ᵀ := by
  decide +kernel
theorem M₁_posSemidef : M₁.PosSemidef := by
  exact posSemidef_of_LDLt dM₁_nonneg M₁_eq_LDL
lemma dM₁_real_nonneg (i : Fin 8) : 0 ≤ (dM₁ i : ℝ) := by
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

/-- SDP certificate matrix for block 2 (rational, 6×6),
paired with `v₂`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₂ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![(34250156 / 39421875 : ℚ), (-416279 / 630750 : ℚ), (-416279 / 630750 : ℚ), (-5897 / 9375 : ℚ), (17784719 / 78843750 : ℚ), (17784719 / 78843750 : ℚ);
    (-416279 / 630750 : ℚ), (42389 / 62500 : ℚ), (26839 / 62500 : ℚ), (2727 / 6250 : ℚ), (-38954597 / 157687500 : ℚ), (-31637897 / 157687500 : ℚ);
    (-416279 / 630750 : ℚ), (26839 / 62500 : ℚ), (42389 / 62500 : ℚ), (2727 / 6250 : ℚ), (-31637897 / 157687500 : ℚ), (-38954597 / 157687500 : ℚ);
    (-5897 / 9375 : ℚ), (2727 / 6250 : ℚ), (2727 / 6250 : ℚ), (394 / 625 : ℚ), (-1142 / 9375 : ℚ), (-1142 / 9375 : ℚ);
    (17784719 / 78843750 : ℚ), (-38954597 / 157687500 : ℚ), (-31637897 / 157687500 : ℚ), (-1142 / 9375 : ℚ), (186084501 / 52562500 : ℚ), (-174410149 / 52562500 : ℚ);
    (17784719 / 78843750 : ℚ), (-31637897 / 157687500 : ℚ), (-38954597 / 157687500 : ℚ), (-1142 / 9375 : ℚ), (-174410149 / 52562500 : ℚ), (186084501 / 52562500 : ℚ)]
noncomputable def M₂_real : Matrix (Fin 6) (Fin 6) ℝ :=
  ratMatrixToReal M₂
def dM₂ : Fin 6 → ℚ :=
  ![(34250156 / 39421875 : ℚ), (955338527286107 / 5400821474250000 : ℚ), (88161140461605577 / 597086579553816875 : ℚ), (1007690357076134 / 7086908397235175 : ℚ), (2662839 / 777500 : ℚ), 0]
def LM₂ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0;
    (-52034875 / 68500312 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (-52034875 / 68500312 : ℚ), (-388385855507293 / 955338527286107 : ℚ), (1 : ℚ), 0, 0, 0;
    (-24796885 / 34250156 : ℚ), (-224119197083990 / 955338527286107 : ℚ), (-112059598541995 / 283476335889407 : ℚ), (1 : ℚ), 0, 0;
    (17784719 / 68500312 : ℚ), (-408775394092007 / 955338527286107 : ℚ), (-253 / 622 : ℚ), 0, (1 : ℚ), 0;
    (17784719 / 68500312 : ℚ), (-158177277686807 / 955338527286107 : ℚ), (-369 / 622 : ℚ), 0, (-1 : ℚ), (1 : ℚ)]
lemma dM₂_nonneg (i : Fin 6) : 0 ≤ dM₂ i := by
  fin_cases i <;> norm_num [dM₂]
lemma M₂_eq_LDL : M₂ = LM₂ * Matrix.diagonal dM₂ * LM₂ᵀ := by
  decide +kernel
theorem M₂_posSemidef : M₂.PosSemidef := by
  exact posSemidef_of_LDLt dM₂_nonneg M₂_eq_LDL
lemma dM₂_real_nonneg (i : Fin 6) : 0 ≤ (dM₂ i : ℝ) := by
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

/-- SDP certificate matrix for block 3 (rational, 5×5),
paired with `v₃`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₃ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1512 / 625 : ℚ), (-69481759 / 157687500 : ℚ), (260220559 / 315375000 : ℚ), (260220559 / 315375000 : ℚ), (-121257041 / 157687500 : ℚ);
    (-69481759 / 157687500 : ℚ), (192 / 625 : ℚ), (-166364959 / 630750000 : ℚ), (-166364959 / 630750000 : ℚ), (-27401441 / 315375000 : ℚ);
    (260220559 / 315375000 : ℚ), (-166364959 / 630750000 : ℚ), (197283893 / 63075000 : ℚ), (-128854451 / 52562500 : ℚ), (-93 / 625 : ℚ);
    (260220559 / 315375000 : ℚ), (-166364959 / 630750000 : ℚ), (-128854451 / 52562500 : ℚ), (197283893 / 63075000 : ℚ), (-93 / 625 : ℚ);
    (-121257041 / 157687500 : ℚ), (-27401441 / 315375000 : ℚ), (-93 / 625 : ℚ), (-93 / 625 : ℚ), (74329241 / 157687500 : ℚ)]
noncomputable def M₃_real : Matrix (Fin 5) (Fin 5) ℝ :=
  ratMatrixToReal M₃
def dM₃ : Fin 5 → ℚ :=
  ![(1512 / 625 : ℚ), (13651670474425919 / 60154249050000000 : ℚ), (1759546171 / 630750000 : ℚ), 0, 0]
def LM₃ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0;
    (-69481759 / 381477600 : ℚ), (1 : ℚ), 0, 0, 0;
    (260220559 / 762955200 : ℚ), (-1 / 2 : ℚ), (1 : ℚ), 0, 0;
    (260220559 / 762955200 : ℚ), (-1 / 2 : ℚ), (-1 : ℚ), (1 : ℚ), 0;
    (-121257041 / 381477600 : ℚ), (-1 : ℚ), 0, 0, (1 : ℚ)]
lemma dM₃_nonneg (i : Fin 5) : 0 ≤ dM₃ i := by
  fin_cases i <;> norm_num [dM₃]
lemma M₃_eq_LDL : M₃ = LM₃ * Matrix.diagonal dM₃ * LM₃ᵀ := by
  decide +kernel
theorem M₃_posSemidef : M₃.PosSemidef := by
  exact posSemidef_of_LDLt dM₃_nonneg M₃_eq_LDL
lemma dM₃_real_nonneg (i : Fin 5) : 0 ≤ (dM₃ i : ℝ) := by
  exact_mod_cast dM₃_nonneg i
lemma M₃_real_eq_LDL :
    M₃_real = (ratMatrixToReal LM₃ * Matrix.diagonal (fun i => (dM₃ i : ℝ))) * (ratMatrixToReal LM₃)ᵀ := by
  calc
    M₃_real = ratMatrixToReal (LM₃ * Matrix.diagonal dM₃ * LM₃ᵀ) := by
      simp [M₃_real, ratMatrixToReal, M₃_eq_LDL]
    _ = (ratMatrixToReal LM₃ * Matrix.diagonal (fun i => (dM₃ i : ℝ))) * (ratMatrixToReal LM₃)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `M₃_real` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem M₃_real_posSemidef : M₃_real.PosSemidef := by
  exact posSemidef_of_LDLt_real dM₃_real_nonneg M₃_real_eq_LDL

/-- Label type for block 1 (flagmatic type '3:'). -/
def σ₁ : FlagType (Fin 3) := FlagType_3_0
/-- Flag vector for block 1: the 8 σ-type 4-vertex flags paired with M₁. -/
noncomputable def v₁ : FlagAlgebraVec σ₁ 8 := ![
  FlagAlgebra_4_3_0_0,
  FlagAlgebra_4_3_0_1,
  FlagAlgebra_4_3_0_2,
  FlagAlgebra_4_3_0_3,
  FlagAlgebra_4_3_0_4,
  FlagAlgebra_4_3_0_5,
  FlagAlgebra_4_3_0_6,
  FlagAlgebra_4_3_0_7
]

/-- Label type for block 2 (flagmatic type '3:12'). -/
def σ₂ : FlagType (Fin 3) := FlagType_3_1
/-- Flag vector for block 2: the 6 σ-type 4-vertex flags paired with M₂. -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 6 := ![
  FlagAlgebra_4_3_1_0,
  FlagAlgebra_4_3_1_1,
  FlagAlgebra_4_3_1_2,
  FlagAlgebra_4_3_1_3,
  FlagAlgebra_4_3_1_5,
  FlagAlgebra_4_3_1_6
]

/-- Label type for block 3 (flagmatic type '3:1213'). -/
def σ₃ : FlagType (Fin 3) := FlagType_3_2
/-- Flag vector for block 3: the 5 σ-type 4-vertex flags paired with M₃. -/
noncomputable def v₃ : FlagAlgebraVec σ₃ 5 := ![
  FlagAlgebra_4_3_2_0,
  FlagAlgebra_4_3_2_1,
  FlagAlgebra_4_3_2_2,
  FlagAlgebra_4_3_2_3,
  FlagAlgebra_4_3_2_6
]

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 5:1213243545 density; forbid 3:121323'
Bound: '24/625'. -/
theorem ErdosPentagon_flagAlgebra
    : FlagAlgebra_5_0_0_19 ≤[K3.toFinFlag] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_5_0_0_19 ≤[K3.toFinFlag]
            FlagAlgebra_5_0_0_19 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀ + ⟦flagQuadraticForm M₃_real v₃⟧₀
    := by
    apply forbidLE_add_QuadraticForm M₃_real M₃_real_posSemidef v₃
    apply forbidLE_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLE_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLE_refl K3.toFinFlag FlagAlgebra_5_0_0_19
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 5)))

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_eight, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂, Fin.sum_univ_six, add_assoc]
  simp [v₃, M₃_real, ratMatrixToReal, M₃, Fin.sum_univ_five, add_assoc]
  reduce_downward_flagmul

  expand_one_at 5

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end ErdosPentagon
