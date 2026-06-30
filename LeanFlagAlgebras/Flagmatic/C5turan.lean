-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 5:1223344551').
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

namespace C5turan

-- Subgraph-forbidding generation (Route B): `ForbidGraph` is forbidden as a (non-induced)
-- subgraph. The `generate_subgraph_free_*` commands emit only the subgraph-`ForbidGraph`-free
-- flags + completeness bridging to the subgraph capstone filter (`supergraphFamily`).
def ForbidGraph : Sym2Graph 5 where
  edges := {s(0, 1), s(0, 4), s(1, 2), s(2, 3), s(3, 4)}
  edges_valid := by decide
generate_subgraph_free_empty_typed_flags 2 ForbidGraph
generate_subgraph_free_empty_typed_flags 4 ForbidGraph
generate_subgraph_free_empty_typed_flags 5 ForbidGraph
generate_subgraph_free_flags 4 3 0 ForbidGraph
generate_subgraph_free_flags 4 3 1 ForbidGraph
generate_subgraph_free_flags 4 3 2 ForbidGraph
generate_subgraph_free_flags 4 3 3 ForbidGraph
generate_subgraph_free_flags 5 3 0 ForbidGraph
generate_subgraph_free_flags 5 3 1 ForbidGraph
generate_subgraph_free_flags 5 3 2 ForbidGraph
generate_subgraph_free_flags 5 3 3 ForbidGraph
generate_subgraph_free_flag_pair_density_theorems 4 5 3 0 ForbidGraph
generate_subgraph_free_mul_theorems 4 5 3 0 ForbidGraph
generate_subgraph_free_flag_pair_density_theorems 4 5 3 1 ForbidGraph
generate_subgraph_free_mul_theorems 4 5 3 1 ForbidGraph
generate_subgraph_free_flag_pair_density_theorems 4 5 3 2 ForbidGraph
generate_subgraph_free_mul_theorems 4 5 3 2 ForbidGraph
generate_subgraph_free_flag_pair_density_theorems 4 5 3 3 ForbidGraph
generate_subgraph_free_mul_theorems 4 5 3 3 ForbidGraph

/-- SDP certificate matrix for block 1 (rational, 8×8),
paired with `v₁`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 / 2 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), 0, 0, 0, (-1 / 2 : ℚ);
    (1 / 12 : ℚ), (55 / 192 : ℚ), (1 / 192 : ℚ), 0, (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 12 : ℚ);
    (1 / 12 : ℚ), (1 / 192 : ℚ), (55 / 192 : ℚ), 0, (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 12 : ℚ);
    (1 / 12 : ℚ), 0, 0, (7 / 24 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 12 : ℚ);
    0, (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (175 / 576 : ℚ), (-23 / 576 : ℚ), (-5 / 144 : ℚ), 0;
    0, (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-23 / 576 : ℚ), (175 / 576 : ℚ), (-5 / 144 : ℚ), 0;
    0, (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-5 / 144 : ℚ), (-5 / 144 : ℚ), (43 / 144 : ℚ), 0;
    (-1 / 2 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, 0, 0, (1 / 2 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₁
def dM₁ : Fin 8 → ℚ :=
  ![(1 / 2 : ℚ), (157 / 576 : ℚ), (171 / 628 : ℚ), (21 / 76 : ℚ), (43 / 144 : ℚ), (803 / 2752 : ℚ), (41 / 146 : ℚ), 0]
def LM₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (-5 / 157 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (1 / 6 : ℚ), (-8 / 157 : ℚ), (-1 / 19 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    0, (-12 / 157 : ℚ), (-3 / 38 : ℚ), (-1 / 12 : ℚ), (1 : ℚ), 0, 0, 0;
    0, (-12 / 157 : ℚ), (-3 / 38 : ℚ), (-1 / 12 : ℚ), (-13 / 86 : ℚ), (1 : ℚ), 0, 0;
    0, (-12 / 157 : ℚ), (-3 / 38 : ℚ), (-1 / 12 : ℚ), (-23 / 172 : ℚ), (-23 / 146 : ℚ), (1 : ℚ), 0;
    (-1 : ℚ), 0, 0, 0, 0, 0, 0, (1 : ℚ)]
/-- `M₁_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  psd_real_ldlt M₁ LM₁ dM₁

/-- SDP certificate matrix for block 2 (rational, 8×8),
paired with `v₂`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(5 / 8 : ℚ), (3 / 32 : ℚ), (3 / 32 : ℚ), (7 / 16 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-11 / 16 : ℚ);
    (3 / 32 : ℚ), (7 / 16 : ℚ), (1 / 32 : ℚ), (5 / 32 : ℚ), 0, (-3 / 32 : ℚ), (-1 / 16 : ℚ), (-5 / 16 : ℚ);
    (3 / 32 : ℚ), (1 / 32 : ℚ), (7 / 16 : ℚ), (5 / 32 : ℚ), 0, (-1 / 16 : ℚ), (-3 / 32 : ℚ), (-5 / 16 : ℚ);
    (7 / 16 : ℚ), (5 / 32 : ℚ), (5 / 32 : ℚ), (15 / 16 : ℚ), (-3 / 8 : ℚ), (-3 / 32 : ℚ), (-3 / 32 : ℚ), (-17 / 16 : ℚ);
    (-1 / 8 : ℚ), 0, 0, (-3 / 8 : ℚ), (1 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 16 : ℚ);
    (-1 / 8 : ℚ), (-3 / 32 : ℚ), (-1 / 16 : ℚ), (-3 / 32 : ℚ), (-1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (7 / 16 : ℚ);
    (-1 / 8 : ℚ), (-1 / 16 : ℚ), (-3 / 32 : ℚ), (-3 / 32 : ℚ), (-1 / 4 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ);
    (-11 / 16 : ℚ), (-5 / 16 : ℚ), (-5 / 16 : ℚ), (-17 / 16 : ℚ), (-5 / 16 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (39 / 16 : ℚ)]
noncomputable def M₂_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₂
def dM₂ : Fin 8 → ℚ :=
  ![(5 / 8 : ℚ), (271 / 640 : ℚ), (1833 / 4336 : ℚ), (335 / 564 : ℚ), (4431 / 5360 : ℚ), (921247 / 3686592 : ℚ), (1841537 / 7369976 : ℚ), (284483 / 572128 : ℚ)]
def LM₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (3 / 20 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (3 / 20 : ℚ), (11 / 271 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (7 / 10 : ℚ), (58 / 271 : ℚ), (29 / 141 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (-1 / 5 : ℚ), (12 / 271 : ℚ), (2 / 47 : ℚ), (-333 / 670 : ℚ), (1 : ℚ), 0, 0, 0;
    (-1 / 5 : ℚ), (-48 / 271 : ℚ), (-353 / 3666 : ℚ), (41 / 1340 : ℚ), (-2797 / 8862 : ℚ), (1 : ℚ), 0, 0;
    (-1 / 5 : ℚ), (-28 / 271 : ℚ), (-635 / 3666 : ℚ), (41 / 1340 : ℚ), (-2797 / 8862 : ℚ), (8461 / 921247 : ℚ), (1 : ℚ), 0;
    (-11 / 10 : ℚ), (-134 / 271 : ℚ), (-67 / 141 : ℚ), (-1117 / 1340 : ℚ), (-7271 / 8862 : ℚ), (164606 / 921247 : ℚ), (6331 / 35758 : ℚ), (1 : ℚ)]
/-- `M₂_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₂_real_posSemidef : M₂_real.PosSemidef := by
  psd_real_ldlt M₂ LM₂ dM₂

/-- SDP certificate matrix for block 3 (rational, 8×8),
paired with `v₃`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₃ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(13 / 16 : ℚ), (3 / 4 : ℚ), (9 / 32 : ℚ), (9 / 32 : ℚ), (-7 / 32 : ℚ), (-7 / 32 : ℚ), (-3 / 4 : ℚ), (-17 / 16 : ℚ);
    (3 / 4 : ℚ), (3 / 2 : ℚ), (15 / 32 : ℚ), (15 / 32 : ℚ), (-23 / 64 : ℚ), (-23 / 64 : ℚ), (-3 / 2 : ℚ), (-61 / 32 : ℚ);
    (9 / 32 : ℚ), (15 / 32 : ℚ), (1 / 2 : ℚ), (5 / 32 : ℚ), (-1 / 4 : ℚ), (-1 / 16 : ℚ), (-15 / 32 : ℚ), (-3 / 4 : ℚ);
    (9 / 32 : ℚ), (15 / 32 : ℚ), (5 / 32 : ℚ), (1 / 2 : ℚ), (-1 / 16 : ℚ), (-1 / 4 : ℚ), (-15 / 32 : ℚ), (-3 / 4 : ℚ);
    (-7 / 32 : ℚ), (-23 / 64 : ℚ), (-1 / 4 : ℚ), (-1 / 16 : ℚ), (19 / 32 : ℚ), (-1 / 4 : ℚ), (23 / 64 : ℚ), (1 / 2 : ℚ);
    (-7 / 32 : ℚ), (-23 / 64 : ℚ), (-1 / 16 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (19 / 32 : ℚ), (23 / 64 : ℚ), (1 / 2 : ℚ);
    (-3 / 4 : ℚ), (-3 / 2 : ℚ), (-15 / 32 : ℚ), (-15 / 32 : ℚ), (23 / 64 : ℚ), (23 / 64 : ℚ), (3 / 2 : ℚ), (61 / 32 : ℚ);
    (-17 / 16 : ℚ), (-61 / 32 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (61 / 32 : ℚ), (3 : ℚ)]
noncomputable def M₃_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₃
def dM₃ : Fin 8 → ℚ :=
  ![(13 / 16 : ℚ), (21 / 26 : ℚ), (1249 / 3584 : ℚ), (6963 / 19984 : ℚ), (98947 / 222816 : ℚ), (775431 / 3166304 : ℚ), 0, (62035 / 142608 : ℚ)]
def LM₃ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (12 / 13 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (9 / 26 : ℚ), (29 / 112 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (9 / 26 : ℚ), (29 / 112 : ℚ), (17 / 1249 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (-7 / 26 : ℚ), (-131 / 672 : ℚ), (-957 / 2498 : ℚ), (1487 / 9284 : ℚ), (1 : ℚ), 0, 0, 0;
    (-7 / 26 : ℚ), (-131 / 672 : ℚ), (387 / 2498 : ℚ), (-3577 / 9284 : ℚ), (-66266 / 98947 : ℚ), (1 : ℚ), 0, 0;
    (-12 / 13 : ℚ), (-1 : ℚ), 0, 0, 0, 0, (1 : ℚ), 0;
    (-17 / 13 : ℚ), (-55 / 48 : ℚ), (-511 / 1249 : ℚ), (-511 / 1266 : ℚ), (319 / 98947 : ℚ), (29 / 2971 : ℚ), 0, (1 : ℚ)]
/-- `M₃_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₃_real_posSemidef : M₃_real.PosSemidef := by
  psd_real_ldlt M₃ LM₃ dM₃

/-- SDP certificate matrix for block 4 (rational, 8×8),
paired with `v₄`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₄ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(5 / 8 : ℚ), (11 / 48 : ℚ), (11 / 48 : ℚ), (11 / 48 : ℚ), (-11 / 48 : ℚ), (-11 / 48 : ℚ), (-11 / 48 : ℚ), (-1 : ℚ);
    (11 / 48 : ℚ), (17 / 64 : ℚ), (7 / 64 : ℚ), (5 / 48 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-25 / 48 : ℚ);
    (11 / 48 : ℚ), (7 / 64 : ℚ), (17 / 64 : ℚ), (5 / 48 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-25 / 48 : ℚ);
    (11 / 48 : ℚ), (5 / 48 : ℚ), (5 / 48 : ℚ), (13 / 48 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-25 / 48 : ℚ);
    (-11 / 48 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (85 / 288 : ℚ), (31 / 288 : ℚ), (7 / 72 : ℚ), (7 / 16 : ℚ);
    (-11 / 48 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (31 / 288 : ℚ), (85 / 288 : ℚ), (7 / 72 : ℚ), (7 / 16 : ℚ);
    (-11 / 48 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (7 / 72 : ℚ), (7 / 72 : ℚ), (11 / 36 : ℚ), (7 / 16 : ℚ);
    (-1 : ℚ), (-25 / 48 : ℚ), (-25 / 48 : ℚ), (-25 / 48 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (19 / 8 : ℚ)]
noncomputable def M₄_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₄
def dM₄ : Fin 8 → ℚ :=
  ![(5 / 8 : ℚ), (523 / 2880 : ℚ), (745 / 4184 : ℚ), (109 / 596 : ℚ), (6323 / 31392 : ℚ), (2535 / 12646 : ℚ), (1145 / 5408 : ℚ), (524 / 1145 : ℚ)]
def LM₄ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (11 / 30 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (11 / 30 : ℚ), (73 / 523 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (11 / 30 : ℚ), (58 / 523 : ℚ), (29 / 298 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (-11 / 30 : ℚ), (-78 / 523 : ℚ), (-39 / 298 : ℚ), (-13 / 109 : ℚ), (1 : ℚ), 0, 0, 0;
    (-11 / 30 : ℚ), (-78 / 523 : ℚ), (-39 / 298 : ℚ), (-13 / 109 : ℚ), (437 / 6323 : ℚ), (1 : ℚ), 0, 0;
    (-11 / 30 : ℚ), (-78 / 523 : ℚ), (-39 / 298 : ℚ), (-13 / 109 : ℚ), (110 / 6323 : ℚ), (11 / 676 : ℚ), (1 : ℚ), 0;
    (-8 / 5 : ℚ), (-444 / 523 : ℚ), (-111 / 149 : ℚ), (-74 / 109 : ℚ), (492 / 6323 : ℚ), (123 / 1690 : ℚ), (82 / 1145 : ℚ), (1 : ℚ)]
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

-- Auto-generated `flagDensity₁` evaluation table (used by
-- `flag_expand_hfree 5 ForbidGraph` to evaluate density coefficients).
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

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Edge-based forbid-free expansion of the objective: `FlagAlgebra_2_0_0_1` is
expanded directly over the ForbidGraph-free 5-vertex flags via
`flag_expand_hfree 5 ForbidGraph` (`basisVector_quot_forbidEq_sum` rewritten onto
`flagSetHfree_5_0_0_ForbidGraph`; the forbidden terms are dropped automatically). -/
lemma C5free_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[ForbidGraph.toLabeledGraph.graph] (1 / 10 : ℝ) • FlagAlgebra_5_0_0_1 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_2 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_3 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_4 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_5 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_6 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_7 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_8 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_9 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_10 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_11 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_12 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_13 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_14 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_15 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_16 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_17 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_18 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_20 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_21 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_22 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_23 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_25 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_26 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_27
  := by
  flag_expand_hfree_subgraph 5 ForbidGraph

/-- **Main theorem (auto-generated).**
Certificate description: '2-graph; maximize 2:12 density; forbid 5:1223344551'
Bound: '1/2'. -/
theorem C5free_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[ForbidGraph.toLabeledGraph.graph] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[ForbidGraph.toLabeledGraph.graph]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀ + ⟦flagQuadraticForm M₃_real v₃⟧₀ + ⟦flagQuadraticForm M₄_real v₄⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M₄_real M₄_real_posSemidef v₄
    apply forbidLEWith_add_QuadraticForm M₃_real M₃_real_posSemidef v₃
    apply forbidLEWith_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLEWith_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_subgraph ForbidGraph 5)))
  simp only [add_assoc]
  rw [forbidLEWith_rw_left_add_right C5free_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_eight, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂]
  simp [v₃, M₃_real, ratMatrixToReal, M₃]
  simp [v₄, M₄_real, ratMatrixToReal, M₄]
  reduce_downward_flagmul

  expand_one_hfree_at_subgraph 5 ForbidGraph

  simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end C5turan
