-- Forbid-free analogue of `Flagmatic/Mantel.lean` (Mantel's theorem: a triangle-free
-- graph has edge density ≤ 1/2). This version exercises the forbid-free generation
-- and bridges end-to-end:
--
--   * `generate_forbid_free_empty_typed_flags` / `generate_forbid_free_flags` emit only
--     the K3-free flags and their filtered-completeness lemma (`flagSetHfree_…_eq`);
--   * `generate_forbid_free_mul_theorems` proves the products `=[K3]` over the
--     forbid-free host set rather than the full `flagSet`;
--   * the objective is expanded with `basisVector_quot_forbidEq_sum` rewritten onto
--     `flagSetHfree` directly (no full expansion + manual triangle-term drop);
--   * the unit is expanded with `expand_one_hfree_at`.
--
-- At host size 3 there is no generation saving (this example generates every
-- 3-vertex flag locally anyway); the point is to validate that the forbid-free
-- bridges compose into a complete density-bound proof. The savings appear at host
-- sizes where only the forbid-free flags need be generated (n ≥ 6, empty-typed).
import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.FlagMulReduce
import LeanFlagAlgebras.API.FlagSumSort
import LeanFlagAlgebras.API.Matrix.PosSemiDef
import LeanFlagAlgebras.API.FlagExpand
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import LeanFlagAlgebras.Forbid.CommonGraphs

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace MantelHfree

-- ── Setup: define the forbidden graph `K3` (the framework's input) ─────────────────
-- The forbid-free framework works *relative to* a forbidden graph, which must already
-- exist. `generate_complete_graph 3 3` names `K3` and proves
-- `K3.toFinFlag = ⟨3, Flag_3_0_0_3⟩`, so it needs the empty-typed 3-vertex flags to name
-- the canonical triangle flag `Flag_3_0_0_3`. That triangle is, by definition, the one
-- flag that is NOT K3-free, so no `generate_forbid_free_*` command produces it — these
-- two lines are irreducible setup (see the note at the end of the file).
generate_empty_typed_flags 3
generate_complete_graph 3 3

-- ── Forbid-free generation: only the K3-free flags, their filtered completeness, and the
-- forbid-free multiplication theorems (proved over `flagSetHfree`, never the full set). ──
generate_forbid_free_empty_typed_flags 2 K3
generate_forbid_free_empty_typed_flags 3 K3
generate_forbid_free_flags 2 1 0 K3
generate_forbid_free_flags 3 1 0 K3
-- Pair densities over the K3-free flags, consumed by the forbid-free multiplication
-- theorems below. `generate_flag_pair_density_theorems … K3` is forbid-restricted (it
-- computes `flagDensity₂` only for K3-free pattern/host pairs); see the end-of-file note.
generate_flag_pair_density_theorems 2 3 1 0 K3
generate_forbid_free_mul_theorems 2 3 1 0 K3

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
lemma dM_nonneg (i : Fin 2) : 0 ≤ dM i := by
  fin_cases i <;> norm_num [dM]
lemma M_eq_LDL : M = LM * Matrix.diagonal dM * LMᵀ := by
  decide +kernel
theorem M_posSemidef : M.PosSemidef := by
  exact posSemidef_of_LDLt dM_nonneg M_eq_LDL
lemma dM_real_nonneg (i : Fin 2) : 0 ≤ (dM i : ℝ) := by
  exact_mod_cast dM_nonneg i
lemma M_real_eq_LDL :
    M_real = (ratMatrixToReal LM * Matrix.diagonal (fun i => (dM i : ℝ))) * (ratMatrixToReal LM)ᵀ := by
  calc
    M_real = ratMatrixToReal (LM * Matrix.diagonal dM * LMᵀ) := by
      simp [M_real, ratMatrixToReal, M_eq_LDL]
    _ = (ratMatrixToReal LM * Matrix.diagonal (fun i => (dM i : ℝ))) * (ratMatrixToReal LM)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `M_real` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem M_real_posSemidef : M_real.PosSemidef := by
  exact posSemidef_of_LDLt_real dM_real_nonneg M_real_eq_LDL

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
over the K3-free 3-vertex flags via `basisVector_quot_forbidEq_sum` rewritten onto
`flagSetHfree_3_0_0_K3` (no full `flagSet`, no manual triangle-term drop). -/
lemma mantel_flagAlgebra_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[K3.toFinFlag] (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
  := by
  flag_expand_hfree 3 K3

/-- **Mantel's theorem (forbid-free formalization).**
A `K3`-free graph has edge density at most `1/2`. -/
theorem mantel_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLE_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLE_refl K3.toFinFlag FlagAlgebra_2_0_0_1
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 3)))
  rw [forbidLE_rw_left_add_right mantel_flagAlgebra_expand_under_forbid]

  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_hfree_at 3 K3

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

/-! ## What is (and isn't) forbid-free here

Everything above the proofs is forbid-free except two unavoidable pieces:

* **Defining the forbidden graph** — `generate_empty_typed_flags 3` +
  `generate_complete_graph 3 3`. The forbidden graph is the *input* the framework works
  relative to, and the framework's H-free test is the **analytic** one,
  `isHfree S := decide (sym2EmptyTypeFlagDensity₁ Sym2Flag_3_0_0_3 S = 0)`, which evaluates
  the density of the forbidden flag `Sym2Flag_3_0_0_3` (equivalently `Flag_3_0_0_3`). That
  flag is by definition the one that is *not* K3-free, so no `generate_forbid_free_*`
  command emits it; it has to come from `generate_empty_typed_flags 3`, and
  `generate_complete_graph 3 3` then names `K3` off it. Removing these entirely would mean
  switching the H-free test to the **combinatorial** predicate `hasTri`
  (`Flags/ForbidFreePruned.lean`), which never mentions a forbidden flag — but wiring that
  in needs the still-unproven bridge `triFree G ↔ flagDensity₁ K3 (unlabel ⟦G⟧) = 0`.

* **Pair densities** — `generate_flag_pair_density_theorems 2 3 1 0 K3`. The forbid-free
  multiplication generator discharges its goal by `simp`-ing each product coefficient to a
  rational, which needs these `@[simp] flagDensity₂ … = c` lemmas. The command is already
  forbid-restricted (it only computes K3-free pattern/host pairs); there is no separate
  `_free`-named version because a density is a density — "forbid-free" only changes *which*
  pairs are computed, not the values. It is effectively part of the forbid-free pipeline.

So the remaining non-`forbid_free`-named commands are (1) the forbidden-graph definition,
which is genuinely the framework's input, and (2) a forbid-restricted density step the
forbid-free multiplication generator consumes. A literally-only-`generate_forbid_free_*`
file is blocked on the combinatorial-vs-analytic H-free bridge above. -/

end MantelHfree
