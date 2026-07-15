-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 5:12131415232425343545').
-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-skeleton)

import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Automation.Basic
import LeanFlagAlgebras.Automation.FlagMulReduce
import LeanFlagAlgebras.Automation.FlagSumSort
import LeanFlagAlgebras.Automation.Matrix.PosSemiDef
import LeanFlagAlgebras.Automation.FlagExpand
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import LeanFlagAlgebras.Forbid.CommonGraphs

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K5turan

-- Edge-based, pruning-backed forbid-free generation (decision D2): the forbidden graph is the
-- `Sym2Graph 5` term `K5 := completeSym2Graph 5` (no canonical forbidden flag); the K5-containing
-- flags are never generated (genuine pruning). The pruned commands emit only the K5-free flags,
-- their completeness, and the forbid-free pair-density / multiplication theorems for all four
-- σ-types.
def K5 : Sym2Graph 5 := completeSym2Graph 5
generate_forbid_free_empty_typed_flags 2 K5
generate_forbid_free_empty_typed_flags 4 K5
generate_forbid_free_empty_typed_flags 5 K5
generate_forbid_free_flags 4 3 0 K5
generate_forbid_free_flags 4 3 1 K5
generate_forbid_free_flags 4 3 2 K5
generate_forbid_free_flags 4 3 3 K5
generate_forbid_free_flags 5 3 0 K5
generate_forbid_free_flags 5 3 1 K5
generate_forbid_free_flags 5 3 2 K5
generate_forbid_free_flags 5 3 3 K5
generate_pruned_flag_pair_density_theorems 4 5 3 0 K5
generate_forbid_free_mul_theorems 4 5 3 0 K5 (completeGraph (Fin 5)) (completeSym2Graph_finFlag_mem_forbiddenFlags 5)
generate_pruned_flag_pair_density_theorems 4 5 3 1 K5
generate_forbid_free_mul_theorems 4 5 3 1 K5 (completeGraph (Fin 5)) (completeSym2Graph_finFlag_mem_forbiddenFlags 5)
generate_pruned_flag_pair_density_theorems 4 5 3 2 K5
generate_forbid_free_mul_theorems 4 5 3 2 K5 (completeGraph (Fin 5)) (completeSym2Graph_finFlag_mem_forbiddenFlags 5)
generate_pruned_flag_pair_density_theorems 4 5 3 3 K5
generate_forbid_free_mul_theorems 4 5 3 3 K5 (completeGraph (Fin 5)) (completeSym2Graph_finFlag_mem_forbiddenFlags 5)

/-- SDP certificate matrix for block 1 (rational, 8×8),
paired with `v₁`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(3 / 4 : ℚ), 0, 0, 0, 0, 0, 0, (-1 / 4 : ℚ);
    0, (55 / 144 : ℚ), (1 / 144 : ℚ), (1 / 36 : ℚ), 0, 0, 0, 0;
    0, (1 / 144 : ℚ), (55 / 144 : ℚ), (1 / 36 : ℚ), 0, 0, 0, 0;
    0, (1 / 36 : ℚ), (1 / 36 : ℚ), (13 / 36 : ℚ), 0, 0, 0, 0;
    0, 0, 0, 0, (17 / 48 : ℚ), (-1 / 48 : ℚ), 0, 0;
    0, 0, 0, 0, (-1 / 48 : ℚ), (17 / 48 : ℚ), 0, 0;
    0, 0, 0, 0, 0, 0, (1 / 3 : ℚ), 0;
    (-1 / 4 : ℚ), 0, 0, 0, 0, 0, 0, (1 / 12 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₁
def dM₁ : Fin 8 → ℚ :=
  ![(3 / 4 : ℚ), (55 / 144 : ℚ), (21 / 55 : ℚ), (5 / 14 : ℚ), (17 / 48 : ℚ), (6 / 17 : ℚ), (1 / 3 : ℚ), 0]
def LM₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    0, (1 : ℚ), 0, 0, 0, 0, 0, 0;
    0, (1 / 55 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    0, (4 / 55 : ℚ), (1 / 14 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    0, 0, 0, 0, (1 : ℚ), 0, 0, 0;
    0, 0, 0, 0, (-1 / 17 : ℚ), (1 : ℚ), 0, 0;
    0, 0, 0, 0, 0, 0, (1 : ℚ), 0;
    (-1 / 3 : ℚ), 0, 0, 0, 0, 0, 0, (1 : ℚ)]
/-- `M₁_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  psd_real_ldlt M₁ LM₁ dM₁

/-- SDP certificate matrix for block 2 (rational, 8×8),
paired with `v₂`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), 0, 0, 0, 0, 0;
    (1 / 8 : ℚ), (3 / 8 : ℚ), 0, 0, 0, (1 / 16 : ℚ), (-1 / 16 : ℚ), 0;
    (1 / 8 : ℚ), 0, (3 / 8 : ℚ), 0, 0, (-1 / 16 : ℚ), (1 / 16 : ℚ), 0;
    0, 0, 0, (1 / 2 : ℚ), 0, 0, 0, 0;
    0, 0, 0, 0, (1 / 2 : ℚ), 0, 0, 0;
    0, (1 / 16 : ℚ), (-1 / 16 : ℚ), 0, 0, (3 / 8 : ℚ), 0, 0;
    0, (-1 / 16 : ℚ), (1 / 16 : ℚ), 0, 0, 0, (3 / 8 : ℚ), 0;
    0, 0, 0, 0, 0, 0, 0, (1 / 4 : ℚ)]
noncomputable def M₂_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₂
def dM₂ : Fin 8 → ℚ :=
  ![(1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 10 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (17 / 48 : ℚ), (6 / 17 : ℚ), (1 / 4 : ℚ)]
def LM₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (1 / 2 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (1 / 2 : ℚ), (-1 / 5 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    0, 0, 0, (1 : ℚ), 0, 0, 0, 0;
    0, 0, 0, 0, (1 : ℚ), 0, 0, 0;
    0, (1 / 5 : ℚ), (-1 / 6 : ℚ), 0, 0, (1 : ℚ), 0, 0;
    0, (-1 / 5 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 17 : ℚ), (1 : ℚ), 0;
    0, 0, 0, 0, 0, 0, 0, (1 : ℚ)]
/-- `M₂_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₂_real_posSemidef : M₂_real.PosSemidef := by
  psd_real_ldlt M₂ LM₂ dM₂

/-- SDP certificate matrix for block 3 (rational, 8×8),
paired with `v₃`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₃ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 / 4 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    0, (9 / 4 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (13 / 36 : ℚ), (-47 / 36 : ℚ);
    0, (1 / 10 : ℚ), (7 / 16 : ℚ), (-1 / 16 : ℚ), 0, 0, 0, (-1 / 20 : ℚ);
    0, (1 / 10 : ℚ), (-1 / 16 : ℚ), (7 / 16 : ℚ), 0, 0, 0, (-1 / 20 : ℚ);
    0, (1 / 10 : ℚ), 0, 0, (1 / 4 : ℚ), 0, 0, (-1 / 20 : ℚ);
    0, (1 / 10 : ℚ), 0, 0, 0, (1 / 4 : ℚ), 0, (-1 / 20 : ℚ);
    0, (13 / 36 : ℚ), 0, 0, 0, 0, (25 / 36 : ℚ), (-19 / 36 : ℚ);
    0, (-47 / 36 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-19 / 36 : ℚ), (11 / 12 : ℚ)]
noncomputable def M₃_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₃
def dM₃ : Fin 8 → ℚ :=
  ![(1 / 4 : ℚ), (9 / 4 : ℚ), (1559 / 3600 : ℚ), (659 / 1559 : ℚ), (647 / 2636 : ℚ), (635 / 2588 : ℚ), (2170 / 3429 : ℚ), 0]
def LM₃ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    0, (1 : ℚ), 0, 0, 0, 0, 0, 0;
    0, (2 / 45 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    0, (2 / 45 : ℚ), (-241 / 1559 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    0, (2 / 45 : ℚ), (-16 / 1559 : ℚ), (-8 / 659 : ℚ), (1 : ℚ), 0, 0, 0;
    0, (2 / 45 : ℚ), (-16 / 1559 : ℚ), (-8 / 659 : ℚ), (-12 / 647 : ℚ), (1 : ℚ), 0, 0;
    0, (13 / 81 : ℚ), (-520 / 14031 : ℚ), (-260 / 5931 : ℚ), (-130 / 1941 : ℚ), (-26 / 381 : ℚ), (1 : ℚ), 0;
    0, (-47 / 81 : ℚ), (260 / 14031 : ℚ), (130 / 5931 : ℚ), (65 / 1941 : ℚ), (13 / 381 : ℚ), (-1 / 2 : ℚ), (1 : ℚ)]
/-- `M₃_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₃_real_posSemidef : M₃_real.PosSemidef := by
  psd_real_ldlt M₃ LM₃ dM₃

/-- SDP certificate matrix for block 4 (rational, 8×8),
paired with `v₄`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₄ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 / 2 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ);
    (1 / 12 : ℚ), (7 / 24 : ℚ), (1 / 24 : ℚ), 0, (23 / 144 : ℚ), (11 / 144 : ℚ), (-1 / 144 : ℚ), (-11 / 48 : ℚ);
    (1 / 12 : ℚ), (1 / 24 : ℚ), (7 / 24 : ℚ), 0, (11 / 144 : ℚ), (-1 / 144 : ℚ), (23 / 144 : ℚ), (-11 / 48 : ℚ);
    (1 / 12 : ℚ), 0, 0, (1 / 3 : ℚ), (-1 / 144 : ℚ), (23 / 144 : ℚ), (11 / 144 : ℚ), (-11 / 48 : ℚ);
    (1 / 8 : ℚ), (23 / 144 : ℚ), (11 / 144 : ℚ), (-1 / 144 : ℚ), (73 / 72 : ℚ), (-1 / 9 : ℚ), (-7 / 72 : ℚ), (-29 / 36 : ℚ);
    (1 / 8 : ℚ), (11 / 144 : ℚ), (-1 / 144 : ℚ), (23 / 144 : ℚ), (-1 / 9 : ℚ), (73 / 72 : ℚ), (-7 / 72 : ℚ), (-29 / 36 : ℚ);
    (1 / 8 : ℚ), (-1 / 144 : ℚ), (23 / 144 : ℚ), (11 / 144 : ℚ), (-7 / 72 : ℚ), (-7 / 72 : ℚ), (1 : ℚ), (-29 / 36 : ℚ);
    (-3 / 8 : ℚ), (-11 / 48 : ℚ), (-11 / 48 : ℚ), (-11 / 48 : ℚ), (-29 / 36 : ℚ), (-29 / 36 : ℚ), (-29 / 36 : ℚ), (29 / 12 : ℚ)]
noncomputable def M₄_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₄
def dM₄ : Fin 8 → ℚ :=
  ![(1 / 2 : ℚ), (5 / 18 : ℚ), (11 / 40 : ℚ), (7 / 22 : ℚ), (913 / 1008 : ℚ), (12835 / 14608 : ℚ), (90739 / 108720 : ℚ), 0]
def LM₄ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (1 / 10 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (-1 / 20 : ℚ), (-1 / 22 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 33 : ℚ), (-5 / 84 : ℚ), (1 : ℚ), 0, 0, 0;
    (1 / 4 : ℚ), (1 / 5 : ℚ), (-4 / 33 : ℚ), (37 / 84 : ℚ), (-158 / 913 : ℚ), (1 : ℚ), 0, 0;
    (1 / 4 : ℚ), (-1 / 10 : ℚ), (17 / 33 : ℚ), (4 / 21 : ℚ), (-267 / 1826 : ℚ), (-267 / 1510 : ℚ), (1 : ℚ), 0;
    (-3 / 4 : ℚ), (-3 / 5 : ℚ), (-6 / 11 : ℚ), (-4 / 7 : ℚ), (-113 / 166 : ℚ), (-1243 / 1510 : ℚ), (-1 : ℚ), (1 : ℚ)]
/-- `M₄_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₄_real_posSemidef : M₄_real.PosSemidef := by
  psd_real_ldlt M₄ LM₄ dM₄

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
/-- Flag vector for block 2: the 8 σ-type 4-vertex flags paired with M₂. -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 8 := ![
  FlagAlgebra_4_3_1_0,
  FlagAlgebra_4_3_1_1,
  FlagAlgebra_4_3_1_2,
  FlagAlgebra_4_3_1_3,
  FlagAlgebra_4_3_1_4,
  FlagAlgebra_4_3_1_5,
  FlagAlgebra_4_3_1_6,
  FlagAlgebra_4_3_1_7
]

/-- Label type for block 3 (flagmatic type '3:1213'). -/
def σ₃ : FlagType (Fin 3) := FlagType_3_2
/-- Flag vector for block 3: the 8 σ-type 4-vertex flags paired with M₃. -/
noncomputable def v₃ : FlagAlgebraVec σ₃ 8 := ![
  FlagAlgebra_4_3_2_0,
  FlagAlgebra_4_3_2_1,
  FlagAlgebra_4_3_2_2,
  FlagAlgebra_4_3_2_3,
  FlagAlgebra_4_3_2_4,
  FlagAlgebra_4_3_2_5,
  FlagAlgebra_4_3_2_6,
  FlagAlgebra_4_3_2_7
]

/-- Label type for block 4 (flagmatic type '3:121323'). -/
def σ₄ : FlagType (Fin 3) := FlagType_3_3
/-- Flag vector for block 4: the 8 σ-type 4-vertex flags paired with M₄. -/
noncomputable def v₄ : FlagAlgebraVec σ₄ 8 := ![
  FlagAlgebra_4_3_3_0,
  FlagAlgebra_4_3_3_1,
  FlagAlgebra_4_3_3_2,
  FlagAlgebra_4_3_3_3,
  FlagAlgebra_4_3_3_4,
  FlagAlgebra_4_3_3_5,
  FlagAlgebra_4_3_3_6,
  FlagAlgebra_4_3_3_7
]

set_option maxHeartbeats 0
set_option maxRecDepth 2000

-- Auto-generated `flagDensity₁` evaluation table (used by
-- `flag_expand 5` to evaluate density coefficients).
@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_0
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_0 = 0
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_1
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_1 = 1 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_2
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_2 = 1 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_3
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_3 = 1 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_3]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_4
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_4 = 3 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_4]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_5
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_5 = 3 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_5]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_6
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_6 = 3 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_6]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_7
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_7 = 3 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_7]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_8
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_8 = 2 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_8]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_9
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_9 = 2 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_9]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_10
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_10 = 2 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_10]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_11
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_11 = 2 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_11]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_12
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_12 = 2 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_12]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_13
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_13 = 2 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_13]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_14
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_14 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_14]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_15
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_15 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_15]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_16
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_16 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_16]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_17
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_17 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_17]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_18
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_18 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_18]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_19
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_19 = 1 / 2
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_19]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_20
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_20 = 3 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_20]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_21
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_21 = 3 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_21]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_22
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_22 = 3 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_22]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_23
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_23 = 3 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_23]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_24
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_24 = 3 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_24]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_25
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_25 = 3 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_25]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_26
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_26 = 7 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_26]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_27
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_27 = 7 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_27]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_28
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_28 = 7 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_28]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_29
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_29 = 7 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_29]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_30
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_30 = 4 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_30]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_31
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_31 = 4 / 5
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_31]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_5_0_0_32
    : flagDensity₁ Flag_2_0_0_1 Flag_5_0_0_32 = 9 / 10
  := by
  dsimp [Flag_2_0_0_1, Flag_5_0_0_32]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/-- Edge-based forbid-free expansion of the objective: `FlagAlgebra_2_0_0_1` is expanded directly
over the K5-free 5-vertex flags via `flag_expand_hfree 5 K5` (`basisVector_quot_inducedForbidEq_sum`
rewritten onto `flagSetHfree_5_0_0_K5`; the K5 term `Flag_5_0_0_33` is dropped automatically). -/
lemma K5turan_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[completeGraph (Fin 5)]
        (1 / 10 : ℝ) • FlagAlgebra_5_0_0_1 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_2 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_3 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_4 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_5 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_6 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_7 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_8 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_9 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_10 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_11 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_12 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_13 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_14 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_15 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_16 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_17 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_18 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_19 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_20 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_21 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_22 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_23 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_24 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_25 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_26 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_27 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_28 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_29 + (4 / 5 : ℝ) • FlagAlgebra_5_0_0_30 + (4 / 5 : ℝ) • FlagAlgebra_5_0_0_31 + (9 / 10 : ℝ) • FlagAlgebra_5_0_0_32
  := by
  flag_expand_hfree 5 K5 (completeSym2Graph_finFlag_mem_forbiddenFlags 5)

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 2:12 density; forbid 5:12131415232425343545'
Bound: '3/4'. -/
theorem K5turan_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 5)] (3 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 5)]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀ + ⟦flagQuadraticForm M₃_real v₃⟧₀ + ⟦flagQuadraticForm M₄_real v₄⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M₄_real M₄_real_posSemidef v₄
    apply forbidLEWith_add_QuadraticForm M₃_real M₃_real_posSemidef v₃
    apply forbidLEWith_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLEWith_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K5⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 5) 5)))
  simp only [add_assoc]
  rw [forbidLEWith_rw_left_add_right K5turan_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_eight, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂]
  simp [v₃, M₃_real, ratMatrixToReal, M₃]
  simp [v₄, M₄_real, ratMatrixToReal, M₄]
  reduce_downward_flagmul

  expand_one_hfree_at 5 K5

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end K5turan
