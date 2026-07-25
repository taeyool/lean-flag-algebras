-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 5:12131415232425343545').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/K5freeEdge_reduced_cert.json \
--     LeanFlagAlgebras/Flagmatic/K5freeEdgeReduced.lean --namespace K5freeEdgeReduced --native-decide --force

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

namespace K5freeEdgeReduced

-- The forbidden graph, as the 5-vertex `Sym2Graph` term `K5`: the complete graph
-- K₅, for which containing a copy and containing an induced copy coincide.
-- The generation commands below prune against it: a flag containing K5 is never
-- enumerated, and they emit the K5-free flags, the completeness lemma for that set, and
-- the pair-density / multiplication theorems the proof consumes.
def K5 : Sym2Graph 5 := completeSym2Graph 5
-- Generated bridging lemmas are proved by `native_decide`, so the main theorem below
-- additionally depends on the `Lean.ofReduceBool` and `Lean.trustCompiler` axioms,
-- which trust Lean's compiler and runtime for the evaluated decision procedures.
-- Regenerating without `--native-decide` proves the same lemmas by `decide +kernel`
-- and removes both, at a higher build cost.
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 2 K5
generate_forbid_free_empty_typed_flags 4 K5
generate_forbid_free_empty_typed_flags 5 K5
generate_forbid_free_flags 4 3 0 K5
generate_forbid_free_flags 4 3 2 K5
generate_forbid_free_flags 4 3 3 K5
generate_forbid_free_flags 5 3 0 K5
generate_forbid_free_flags 5 3 2 K5
generate_forbid_free_flags 5 3 3 K5
generate_forbid_free_flag_pair_density_theorems 4 5 3 0 K5
generate_forbid_free_mul_theorems 4 5 3 0 K5
generate_forbid_free_flag_pair_density_theorems 4 5 3 2 K5
generate_forbid_free_mul_theorems 4 5 3 2 K5
generate_forbid_free_flag_pair_density_theorems 4 5 3 3 K5
generate_forbid_free_mul_theorems 4 5 3 3 K5
generate_forbid_free_flag_density_theorems 2 1 5 K5

/-- SDP certificate matrix for block 1 (rational, 8×8),
paired with `v₁`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(3 / 4 : ℚ), (39 / 10240 : ℚ), (39 / 10240 : ℚ), (39 / 10240 : ℚ), (-39 / 2048 : ℚ), (-39 / 2048 : ℚ), (-39 / 2048 : ℚ), (-1 / 4 : ℚ);
    (39 / 10240 : ℚ), (4099 / 6144 : ℚ), (-155 / 6144 : ℚ), (-77 / 3072 : ℚ), (-31 / 2304 : ℚ), (-31 / 2304 : ℚ), (-65 / 1152 : ℚ), (-13 / 10240 : ℚ);
    (39 / 10240 : ℚ), (-155 / 6144 : ℚ), (4099 / 6144 : ℚ), (-77 / 3072 : ℚ), (-31 / 2304 : ℚ), (-65 / 1152 : ℚ), (-31 / 2304 : ℚ), (-13 / 10240 : ℚ);
    (39 / 10240 : ℚ), (-77 / 3072 : ℚ), (-77 / 3072 : ℚ), (683 / 1024 : ℚ), (-65 / 1152 : ℚ), (-31 / 2304 : ℚ), (-31 / 2304 : ℚ), (-13 / 10240 : ℚ);
    (-39 / 2048 : ℚ), (-31 / 2304 : ℚ), (-31 / 2304 : ℚ), (-65 / 1152 : ℚ), (12515 / 18432 : ℚ), (-499 / 18432 : ℚ), (-251 / 9216 : ℚ), (13 / 2048 : ℚ);
    (-39 / 2048 : ℚ), (-31 / 2304 : ℚ), (-65 / 1152 : ℚ), (-31 / 2304 : ℚ), (-499 / 18432 : ℚ), (12515 / 18432 : ℚ), (-251 / 9216 : ℚ), (13 / 2048 : ℚ);
    (-39 / 2048 : ℚ), (-65 / 1152 : ℚ), (-31 / 2304 : ℚ), (-31 / 2304 : ℚ), (-251 / 9216 : ℚ), (-251 / 9216 : ℚ), (6259 / 9216 : ℚ), (13 / 2048 : ℚ);
    (-1 / 4 : ℚ), (-13 / 10240 : ℚ), (-13 / 10240 : ℚ), (-13 / 10240 : ℚ), (13 / 2048 : ℚ), (13 / 2048 : ℚ), (13 / 2048 : ℚ), (1 / 12 : ℚ)]
noncomputable def M₁_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₁
-- Candidate exact-rational LDLᵀ witness for `M₁`: `M₁ = LM₁ * diag dM₁ * LM₁ᵀ`
-- with `LM₁` unit lower triangular. Computed by the translator and re-checked below by
-- `psd_real_ldlt`, which proves the factorization and `0 ≤ dM₁` inside Lean; an
-- incorrect witness is rejected rather than trusted.
def dM₁ : Fin 8 → ℚ :=
  ![(3 / 4 : ℚ), (52465679 / 78643200 : ℚ), (17895216011 / 26862427648 : ℚ), (51563405531 / 77537522688 : ℚ), (639624049397819 / 950416690747392 : ℚ), (9746427347843144821 / 14511790432737717472 : ℚ), (13378660762928211233157 / 19960683208382760593408 : ℚ), 0]
def LM₁ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (13 / 2560 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (13 / 2560 : ℚ), (-1985521 / 52465679 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (13 / 2560 : ℚ), (-1972721 / 52465679 : ℚ), (-1972721 / 50480158 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (-13 / 512 : ℚ), (-3151585 / 157397037 : ℚ), (-3151585 / 151440474 : ℚ), (-13345206139 / 154690216593 : ℚ), (1 : ℚ), 0, 0, 0;
    (-13 / 512 : ℚ), (-3151585 / 157397037 : ℚ), (-9159943393 / 107371296066 : ℚ), (-3740733613 / 154690216593 : ℚ), (-28886529435751 / 639624049397819 : ℚ), (1 : ℚ), 0, 0;
    (-13 / 512 : ℚ), (-1898455 / 22485291 : ℚ), (-2496562537 / 107371296066 : ℚ), (-3740733613 / 154690216593 : ℚ), (-29041219652344 / 639624049397819 : ℚ), (-3707693366446289783 / 77971418782745158568 : ℚ), (1 : ℚ), 0;
    (-1 / 3 : ℚ), 0, 0, 0, 0, 0, 0, (1 : ℚ)]
/-- `M₁_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₁_real_posSemidef : M₁_real.PosSemidef := by
  psd_real_ldlt M₁ LM₁ dM₁

/-- SDP certificate matrix for block 2 (rational, 8×8),
paired with `v₂`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(205 / 512 : ℚ), (-23 / 384 : ℚ), (-31 / 2048 : ℚ), (-31 / 2048 : ℚ), (35 / 1024 : ℚ), (35 / 1024 : ℚ), (5 / 192 : ℚ), (13 / 768 : ℚ);
    (-23 / 384 : ℚ), (9 / 4 : ℚ), (3763 / 30720 : ℚ), (3763 / 30720 : ℚ), (1031 / 30720 : ℚ), (1031 / 30720 : ℚ), (17149 / 73728 : ℚ), (-183037 / 147456 : ℚ);
    (-31 / 2048 : ℚ), (3763 / 30720 : ℚ), (103 / 256 : ℚ), (87 / 1024 : ℚ), (-215 / 4096 : ℚ), (265 / 4096 : ℚ), (425 / 6144 : ℚ), (-23 / 240 : ℚ);
    (-31 / 2048 : ℚ), (3763 / 30720 : ℚ), (87 / 1024 : ℚ), (103 / 256 : ℚ), (265 / 4096 : ℚ), (-215 / 4096 : ℚ), (425 / 6144 : ℚ), (-23 / 240 : ℚ);
    (35 / 1024 : ℚ), (1031 / 30720 : ℚ), (-215 / 4096 : ℚ), (265 / 4096 : ℚ), (225 / 256 : ℚ), (-125 / 256 : ℚ), (-515 / 6144 : ℚ), (193 / 7680 : ℚ);
    (35 / 1024 : ℚ), (1031 / 30720 : ℚ), (265 / 4096 : ℚ), (-215 / 4096 : ℚ), (-125 / 256 : ℚ), (225 / 256 : ℚ), (-515 / 6144 : ℚ), (193 / 7680 : ℚ);
    (5 / 192 : ℚ), (17149 / 73728 : ℚ), (425 / 6144 : ℚ), (425 / 6144 : ℚ), (-515 / 6144 : ℚ), (-515 / 6144 : ℚ), (35075 / 36864 : ℚ), (-87299 / 147456 : ℚ);
    (13 / 768 : ℚ), (-183037 / 147456 : ℚ), (-23 / 240 : ℚ), (-23 / 240 : ℚ), (193 / 7680 : ℚ), (193 / 7680 : ℚ), (-87299 / 147456 : ℚ), (11 / 12 : ℚ)]
noncomputable def M₂_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₂
-- Candidate exact-rational LDLᵀ witness for `M₂`: `M₂ = LM₂ * diag dM₂ * LM₂ᵀ`
-- with `LM₂` unit lower triangular. Computed by the translator and re-checked below by
-- `psd_real_ldlt`, which proves the factorization and `0 ≤ dM₂` inside Lean; an
-- incorrect witness is rejected rather than trusted.
def dM₂ : Fin 8 → ℚ :=
  ![(205 / 512 : ℚ), (132311 / 59040 : ℚ), (34278843463 / 86711336960 : ℚ), (6668512325475 / 17550767853056 : ℚ), (282600204680701 / 331081533153280 : ℚ), (10750260322680651 / 18086413099564864 : ℚ), (138674421630947275 / 159902192579936256 : ℚ), 0]
def LM₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (-92 / 615 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (-31 / 820 : ℚ), (454293 / 8467904 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (-31 / 820 : ℚ), (454293 / 8467904 : ℚ), (6758155463 / 34278843463 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (7 / 82 : ℚ), (146133 / 8467904 : ℚ), (-4619364681 / 34278843463 : ℚ), (15831319359 / 80830452430 : ℚ), (1 : ℚ), 0, 0, 0;
    (7 / 82 : ℚ), (146133 / 8467904 : ℚ), (5542120119 / 34278843463 : ℚ), (-14013770769 / 80830452430 : ℚ), (-155724685665859 / 282600204680701 : ℚ), (1 : ℚ), 0, 0;
    (8 / 123 : ℚ), (3574425 / 33871616 : ℚ), (19933224355 / 137115373852 : ℚ), (1812111305 / 14922545064 : ℚ), (-121067502115495 / 1130400818722804 : ℚ), (-9312884778115 / 39038621235336 : ℚ), (1 : ℚ), 0;
    (26 / 615 : ℚ), (-37446041 / 67743232 : ℚ), (-19933224355 / 274230747704 : ℚ), (-1812111305 / 29845090128 : ℚ), (121067502115495 / 2260801637445608 : ℚ), (9312884778115 / 78077242470672 : ℚ), (-1 / 2 : ℚ), (1 : ℚ)]
/-- `M₂_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₂_real_posSemidef : M₂_real.PosSemidef := by
  psd_real_ldlt M₂ LM₂ dM₂

/-- SDP certificate matrix for block 3 (rational, 8×8),
paired with `v₃`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def M₃ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(765 / 1024 : ℚ), (71 / 1024 : ℚ), (71 / 1024 : ℚ), (71 / 1024 : ℚ), (195 / 1024 : ℚ), (195 / 1024 : ℚ), (195 / 1024 : ℚ), (-585 / 1024 : ℚ);
    (71 / 1024 : ℚ), (20771 / 36864 : ℚ), (701 / 36864 : ℚ), (11 / 576 : ℚ), (2639 / 18432 : ℚ), (2639 / 18432 : ℚ), (695 / 18432 : ℚ), (-1991 / 6144 : ℚ);
    (71 / 1024 : ℚ), (701 / 36864 : ℚ), (20771 / 36864 : ℚ), (11 / 576 : ℚ), (2639 / 18432 : ℚ), (695 / 18432 : ℚ), (2639 / 18432 : ℚ), (-1991 / 6144 : ℚ);
    (71 / 1024 : ℚ), (11 / 576 : ℚ), (11 / 576 : ℚ), (649 / 1152 : ℚ), (695 / 18432 : ℚ), (2639 / 18432 : ℚ), (2639 / 18432 : ℚ), (-1991 / 6144 : ℚ);
    (195 / 1024 : ℚ), (2639 / 18432 : ℚ), (2639 / 18432 : ℚ), (695 / 18432 : ℚ), (427517 / 442368 : ℚ), (-35587 / 442368 : ℚ), (-17789 / 221184 : ℚ), (-29 / 36 : ℚ);
    (195 / 1024 : ℚ), (2639 / 18432 : ℚ), (695 / 18432 : ℚ), (2639 / 18432 : ℚ), (-35587 / 442368 : ℚ), (427517 / 442368 : ℚ), (-17789 / 221184 : ℚ), (-29 / 36 : ℚ);
    (195 / 1024 : ℚ), (695 / 18432 : ℚ), (2639 / 18432 : ℚ), (2639 / 18432 : ℚ), (-17789 / 221184 : ℚ), (-17789 / 221184 : ℚ), (106877 / 110592 : ℚ), (-29 / 36 : ℚ);
    (-585 / 1024 : ℚ), (-1991 / 6144 : ℚ), (-1991 / 6144 : ℚ), (-1991 / 6144 : ℚ), (-29 / 36 : ℚ), (-29 / 36 : ℚ), (-29 / 36 : ℚ), (29 / 12 : ℚ)]
noncomputable def M₃_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal M₃
-- Candidate exact-rational LDLᵀ witness for `M₃`: `M₃ = LM₃ * diag dM₃ * LM₃ᵀ`
-- with `LM₃` unit lower triangular. Computed by the translator and re-checked below by
-- `psd_real_ldlt`, which proves the factorization and `0 ≤ dM₃` inside Lean; an
-- incorrect witness is rejected rather than trusted.
def dM₃ : Fin 8 → ℚ :=
  ![(765 / 1024 : ℚ), (1745371 / 3133440 : ℚ), (248755385 / 446814976 : ℚ), (31776151 / 57113344 : ℚ), (12119842002959 / 14056752365568 : ℚ), (676373970985233307 / 813997106194027520 : ℚ), (36967795404069411888295 / 47097272347643765633024 : ℚ), 0]
def LM₃ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
    (71 / 765 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0, 0;
    (71 / 765 : ℚ), (39421 / 1745371 : ℚ), (1 : ℚ), 0, 0, 0, 0, 0;
    (71 / 765 : ℚ), (39676 / 1745371 : ℚ), (9919 / 446198 : ℚ), (1 : ℚ), 0, 0, 0, 0;
    (13 / 51 : ℚ), (393250 / 1745371 : ℚ), (196625 / 892396 : ℚ), (4952587 / 190656906 : ℚ), (1 : ℚ), 0, 0, 0;
    (13 / 51 : ℚ), (393250 / 1745371 : ℚ), (30736807 / 995021540 : ℚ), (20949032 / 95328453 : ℚ), (-135796035329 / 712931882527 : ℚ), (1 : ℚ), 0, 0;
    (13 / 51 : ℚ), (62770 / 1745371 : ℚ), (223494343 / 995021540 : ℚ), (20949032 / 95328453 : ℚ), (-2308246615234 / 12119842002959 : ℚ), (-159128259363790867 / 676373970985233307 : ℚ), (1 : ℚ), 0;
    (-13 / 17 : ℚ), (-849270 / 1745371 : ℚ), (-424635 / 892396 : ℚ), (-141545 / 304078 : ℚ), (-7503062787132 / 12119842002959 : ℚ), (-517245711621442440 / 676373970985233307 : ℚ), (-1 : ℚ), (1 : ℚ)]
/-- `M₃_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M₃_real_posSemidef : M₃_real.PosSemidef := by
  psd_real_ldlt M₃ LM₃ dM₃

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

/-- Label type for block 2 (flagmatic type '3:1213'). -/
def σ₂ : FlagType (Fin 3) := FlagType_3_2
/-- Flag vector for block 2: the 8 σ-type 4-vertex flags paired with M₂. -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 8 := ![
  FlagAlgebra_4_3_2_0,
  FlagAlgebra_4_3_2_1,
  FlagAlgebra_4_3_2_2,
  FlagAlgebra_4_3_2_3,
  FlagAlgebra_4_3_2_4,
  FlagAlgebra_4_3_2_5,
  FlagAlgebra_4_3_2_6,
  FlagAlgebra_4_3_2_7
]

/-- Label type for block 3 (flagmatic type '3:121323'). -/
def σ₃ : FlagType (Fin 3) := FlagType_3_3
/-- Flag vector for block 3: the 8 σ-type 4-vertex flags paired with M₃. -/
noncomputable def v₃ : FlagAlgebraVec σ₃ 8 := ![
  FlagAlgebra_4_3_3_0,
  FlagAlgebra_4_3_3_1,
  FlagAlgebra_4_3_3_2,
  FlagAlgebra_4_3_3_3,
  FlagAlgebra_4_3_3_4,
  FlagAlgebra_4_3_3_5,
  FlagAlgebra_4_3_3_6,
  FlagAlgebra_4_3_3_7
]

/-- Objective expansion. `flag_expand_hfree 5 K5` expands `FlagAlgebra_2_0_0_1`
over the 5-vertex K5-free flags, rewriting the expansion theorem onto the
generated set `flagSetHfree_5_0_0_K5`. Under the hypothesis the flags
containing K5 have density zero, so they never enter the sum. -/
lemma K5freeEdge_reduced_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[completeGraph (Fin 5)] (1 / 10 : ℝ) • FlagAlgebra_5_0_0_1 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_2 + (1 / 5 : ℝ) • FlagAlgebra_5_0_0_3 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_4 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_5 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_6 + (3 / 10 : ℝ) • FlagAlgebra_5_0_0_7 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_8 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_9 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_10 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_11 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_12 + (2 / 5 : ℝ) • FlagAlgebra_5_0_0_13 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_14 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_15 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_16 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_17 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_18 + (1 / 2 : ℝ) • FlagAlgebra_5_0_0_19 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_20 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_21 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_22 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_23 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_24 + (3 / 5 : ℝ) • FlagAlgebra_5_0_0_25 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_26 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_27 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_28 + (7 / 10 : ℝ) • FlagAlgebra_5_0_0_29 + (4 / 5 : ℝ) • FlagAlgebra_5_0_0_30 + (4 / 5 : ℝ) • FlagAlgebra_5_0_0_31 + (9 / 10 : ℝ) • FlagAlgebra_5_0_0_32
  := by
  flag_expand_hfree 5 K5

/-- **Main theorem (auto-generated).**
Every graph with no K₅ subgraph has edge density at most 3/4.

Certificate description: '2-graph; maximize 2:12 density; forbid 5:12131415232425343545'
Bound: '3/4'. -/
theorem K5freeEdge_reduced_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 5)] (3 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 5)]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M₁_real v₁⟧₀ + ⟦flagQuadraticForm M₂_real v₂⟧₀ + ⟦flagQuadraticForm M₃_real v₃⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M₃_real M₃_real_posSemidef v₃
    apply forbidLEWith_add_QuadraticForm M₂_real M₂_real_posSemidef v₂
    apply forbidLEWith_add_QuadraticForm M₁_real M₁_real_posSemidef v₁
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K5⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 5) 5)))
  simp only [add_assoc]
  rw [forbidLEWith_rw_left_add_right K5freeEdge_reduced_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v₁, M₁_real, ratMatrixToReal, M₁, Fin.sum_univ_eight, add_assoc]
  simp [v₂, M₂_real, ratMatrixToReal, M₂]
  simp [v₃, M₃_real, ratMatrixToReal, M₃]
  reduce_downward_flagmul

  expand_one_hfree_at 5 K5

  simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

end K5freeEdgeReduced
