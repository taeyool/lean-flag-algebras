-- Edge-based, pruning-backed analogue of `Flagmatic/Mantel.lean` (Mantel's theorem: a
-- triangle-free graph has edge density ≤ 1/2). The forbidden graph is the `Sym2Graph 3` term
-- `K3 := completeSym2Graph 3` (decision D2 — no canonical forbidden flag), and the K3-containing
-- flags are *never generated* (genuine pruning). The pipeline runs end-to-end on it:
--
--   * `generate_pruned_forbid_free_empty_typed_flags` / `generate_pruned_forbid_free_flags` emit
--     only the K3-free flags and their filtered-completeness lemma (`flagSetHfree_…_eq`), proved
--     via `prunedFreeFlags_toFinset_eq` (no full enumeration, no canonical flag);
--   * `generate_pruned_forbid_free_mul_theorems` proves the products
--     `=ᵢ[⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩]` over the forbid-free host set;
--   * the objective is expanded with the edge-based `flag_expand_hfree 3 K3`
--     (`basisVector_quot_inducedForbidEq_sum` rewritten onto `flagSetHfree` directly — no full
--     expansion + manual triangle-term drop);
--   * the unit is expanded with the edge-based `expand_one_hfree_at 3 K3`.
--
-- The bound is stated as `≤ᵢ[⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩]`. At host size 3 there is no
-- generation saving (every 3-vertex flag is K3-free except the triangle); the point is to
-- validate the edge-based forbid-free bridges end-to-end. The savings appear at host sizes
-- where only the forbid-free flags need be generated (n ≥ 6, empty-typed).
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

namespace MantelHfree

-- ── Setup: define the forbidden graph `K3` as an edge-based `Sym2Graph` term (D2) ────────
-- The edge-based, pruning-backed pipeline forbids a `Sym2Graph m` term directly: no
-- `generate_empty_typed_flags` + `generate_complete_graph` (no canonical forbidden flag), and
-- the K3-containing flags are *never generated* (genuine pruning).
def K3 : Sym2Graph 3 := completeSym2Graph 3

-- ── Forbid-free generation (genuine pruning): only the K3-free flags, their filtered
-- completeness, and the forbid-free multiplication theorems (over `flagSetHfree`). ──
generate_pruned_forbid_free_empty_typed_flags 2 K3
generate_pruned_forbid_free_empty_typed_flags 3 K3
generate_pruned_forbid_free_flags 2 1 0 K3
generate_pruned_forbid_free_flags 3 1 0 K3
-- Pair densities over the K3-free flags (induced split), consumed by the forbid-free
-- multiplication theorems below.
generate_pruned_flag_pair_density_theorems 2 3 1 0 K3
generate_pruned_forbid_free_mul_theorems 2 3 1 0 K3 (completeGraph (Fin 3)) (completeSym2Graph_finFlag_mem_forbiddenFlags 3)

/-- SDP certificate matrix for block 1 (rational, 2×2), paired with `v`. -/
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
/-- `M_real` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem M_real_posSemidef : M_real.PosSemidef := by
  psd_real_ldlt M LM dM

/-- Label type for block 1 (flagmatic type '1:'). -/
def σ : FlagType (Fin 1) := FlagType_1_0
/-- Flag vector for block 1: the 2 σ-type 2-vertex flags paired with M. -/
noncomputable def v : FlagAlgebraVec σ 2 := ![
  FlagAlgebra_2_1_0_0,
  FlagAlgebra_2_1_0_1
]

set_option maxHeartbeats 0
set_option maxRecDepth 1500

-- `flagDensity₁` evaluation table for the K3-free 3-vertex flags (used by the
-- forbid-free objective expansion below).
@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_0
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_0 = 0 := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_0]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_1
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_1 = 1 / 3 := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_1]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

@[simp]
private theorem auto_flagDensity1_2_0_0_1_3_0_0_2
    : flagDensity₁ Flag_2_0_0_1 Flag_3_0_0_2 = 2 / 3 := by
  dsimp [Flag_2_0_0_1, Flag_3_0_0_2]
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
  native_decide

/-- Forbid-free expansion of the objective: `FlagAlgebra_2_0_0_1` is expanded directly
over the K3-free 3-vertex flags via `basisVector_quot_inducedForbidEq_sum` rewritten onto
`flagSetHfree_3_0_0_K3` (no full `flagSet`, no manual triangle-term drop). -/
lemma mantel_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[completeGraph (Fin 3)]
        (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
  := by
  flag_expand_hfree 3 K3 (completeSym2Graph_finFlag_mem_forbiddenFlags 3)

/-- **Mantel's theorem (forbid-free formalization).**
A `K3`-free graph has edge density at most `1/2`. -/
theorem mantel_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 3)] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 3)]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLEWith_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLEWith_refl _ FlagAlgebra_2_0_0_1
  apply forbidLEWith_trans quadraticForm_trans
  apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags 3) 3)))
  rw [forbidLEWith_rw_left_add_right mantel_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_hfree_at 3 K3

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLEWith_of_le
  flag_nonneg

/-! ## What is (and isn't) forbid-free here

The whole file is now edge-based and genuinely pruned. The only non-`generate_pruned_*`
declarations are:

* **The forbidden graph** — `def K3 : Sym2Graph 3 := completeSym2Graph 3`. This is the
  framework's *input* (decision D2): a plain `Sym2Graph` term, read directly by the
  edge-based commands. There is no canonical forbidden flag and no
  `generate_empty_typed_flags` / `generate_complete_graph` — the K3-containing flags are
  never generated. The forbid-free test the generators use is the analytic density on
  `⟦K3⟧` (`sym2EmptyTypeFlagDensity₁ ⟦K3⟧ S = 0`), and completeness routes through the
  combinatorial pruning predicate via the bridge `not_inducedContains_iff_density_eq_zero`
  (`Flags/ForbidFreePruned.lean`, Tasks 1/4) — the bridge that earlier blocked this file is
  now proved.

* **Pair densities** — `generate_pruned_flag_pair_density_theorems 2 3 1 0 K3`. The
  forbid-free multiplication generator discharges its goal by `simp`-ing each product
  coefficient to a rational, which needs these `@[simp] flagDensity₂ … = c` lemmas. The
  command computes the densities only for the induced-K3-free pattern/host pairs; a density
  is a density, so it is effectively part of the forbid-free pipeline. -/

end MantelHfree
