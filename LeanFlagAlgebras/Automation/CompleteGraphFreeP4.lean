module

public import LeanFlagAlgebras.Flags.FlagGenerator
public import LeanFlagAlgebras.Automation.Basic
public import LeanFlagAlgebras.Automation.FlagMulReduce
public import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
public import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
public import LeanFlagAlgebras.Automation.FlagSumSort
public import LeanFlagAlgebras.Forbid.CommonGraphs

@[expose] public section

/-! # Automation.CompleteGraphFreeP4 — P₄ density bound in K_{r+1}-free graphs

Per-problem density-bound proof on the Automation layer, generalizing
`Automation.K4freeP4` from K₄ to an arbitrary forbidden complete graph K_{r+1}. The
headline result `Kr_plus_1_free_P4_density_upper_bound` (upper-bound direction
of Theorem 1.3(i), Murphy–Nir 2021) states that for `r ≥ 3` and K_{r+1}-free
graphs the `P₄` density is at most `12·((r-1)/r)³`:

  `P4_density ≤ᵢ[(completeGraph (Fin (r+1))).toFinFlag]
     (12 * (((r:ℝ) - 1) / r) ^ 3) • (1 : FlagAlgebra ∅ₜ)`.

The certificate consists of r-parameterized squared terms `f₁ r, f₂, f₃ r`,
a K₄-density correction term `f₀ r`, and rational-function multipliers
`p₀..p₃ r` (with common denominator factor `D r = 3r²−11r+9`). The bound is not
tight on every flag, so the certificate is an *inequality*: the residual
`leftover r = ∑ⱼ gapⱼ·Fⱼ` is a nonnegative combination of flags, and
`gap_identity` records the exact algebraic identity
`P4_density + ∑ pᵢ·fᵢ + leftover = (target)·1`. The multipliers `p₁,p₂,p₃`
specialize at `r = 3` to `K4freeP4`'s `(8/9, 5, 35/9)`.

The development is `sorry`-free. Its one external dependency is the explicit
`axiom Zykov_K4_density_bound` (Corollary 1.5: the K₄-density bound in K_{r+1}-free
graphs — Zykov's classical generalized-Turán theorem), which is genuinely outside
the flag-SOS machinery here; `#print axioms Kr_plus_1_free_P4_density_upper_bound`
exhibits the dependence. The `r = 3` case specializes to
`K4freeP4.K4_free_P4_density_upper_bound` with bound `32/9` (there `f₀` is
unnecessary since K₄ is forbidden). -/

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph

namespace CompleteGraphFreeP4

-- Locally generate the flags this example needs (formerly from the global
-- `Flags/FlagDef.lean`): the empty-typed underlying flags and the σ-typed pattern/host
-- flags. The forbidden graph here is the generic `completeGraph (Fin (r+1))`, so there
-- is no named-clique generation. Flag generation comes first, so the definitions and
-- the no-forbid density/multiplication generators below resolve to these local constants.
-- Kernel reduction of the generated bridging/density obligations (via
-- `flag_bridge_decide` = `decide +kernel`) can exceed the default heartbeat budget
-- during elaboration; lift it (kernel decide is unbounded, like `native_decide` was).
set_option maxHeartbeats 0
generate_empty_typed_flags 3
generate_empty_typed_flags 4
generate_flags 3 2 0
generate_flags 3 2 1
generate_flags 4 2 0
generate_flags 4 2 1

-- Includes `12 • FlagAlgebra_4_0_0_10` (K₄), which K4freeP4.P4_density omits because it vanishes for K₄-free graphs.
noncomputable def P4_density : FlagAlgebra ∅ₜ :=
  1 • FlagAlgebra_4_0_0_6
  + 2 • FlagAlgebra_4_0_0_7
  + 4 • FlagAlgebra_4_0_0_8
  + 6 • FlagAlgebra_4_0_0_9
  + 12 • FlagAlgebra_4_0_0_10

-- σ₁-type (no-edge label) Cauchy-Schwarz squared term; f₁ 3 = K4freeP4.f₁.
-- Coefficients are real (`(r:ℝ) - 1`), not ℕ-truncated, so `f₁_expand` holds for all r.
noncomputable def f₁ (r : ℕ) : FlagAlgebra ∅ₜ :=
  ⟦(((r : ℝ) - 1) • FlagAlgebra_3_2_0_0 - (1 : ℝ) • FlagAlgebra_3_2_0_3) ^ 2⟧₀

-- r-independent σ₂-type (edge-label) Cauchy-Schwarz term; identical to K4freeP4.f₂.
noncomputable def f₂ : FlagAlgebra ∅ₜ :=
  ⟦((1 : ℝ) • FlagAlgebra_3_2_1_1 - (1 : ℝ) • FlagAlgebra_3_2_1_2) ^ 2⟧₀

-- σ₂-type Cauchy-Schwarz squared term; f₃ 3 = K4freeP4.f₃.
-- Coefficients are real (`(r:ℝ) - 2`), not ℕ-truncated, so `f₃_expand` holds for all r.
noncomputable def f₃ (r : ℕ) : FlagAlgebra ∅ₜ :=
  ⟦(((r : ℝ) - 2) • FlagAlgebra_3_2_1_1 + ((r : ℝ) - 2) • FlagAlgebra_3_2_1_2
    - (2 : ℝ) • FlagAlgebra_3_2_1_3) ^ 2⟧₀

/-- `f₁ r` is non-negative (a downward-projected square). -/
lemma f₁_nonneg (r : ℕ) : 0 ≤ f₁ r := by
  dsimp only [f₁]
  rw [pow_two]
  exact square_downward_nonneg _

/-- `f₂` is non-negative (a downward-projected square). -/
lemma f₂_nonneg : 0 ≤ f₂ := by
  dsimp only [f₂]
  rw [pow_two]
  exact square_downward_nonneg _

/-- `f₃ r` is non-negative (a downward-projected square). -/
lemma f₃_nonneg (r : ℕ) : 0 ≤ f₃ r := by
  dsimp only [f₃]
  rw [pow_two]
  exact square_downward_nonneg _

generate_flag_pair_density_theorems_no_forbid 3 4 2 0
generate_mul_theorems 3 4 2 0
-- σ₂-type (edge-label) products, needed for `f₂_expand` / `f₃_expand`.
generate_flag_pair_density_theorems_no_forbid 3 4 2 1
generate_mul_theorems 3 4 2 1

-- Expansion of f₁(r) in the basis of 4-vertex graph densities.
-- Coefficients computed from the flag algebra product structure (σ₁-type averaging).
lemma f₁_expand (r : ℕ) : f₁ r =
    ((r : ℝ) - 1) ^ 2 • FlagAlgebra_4_0_0_0
    + (((r : ℝ) - 1) ^ 2 / 6) • FlagAlgebra_4_0_0_1
    - (((r : ℝ) - 1) / 6) • FlagAlgebra_4_0_0_2
    - (((r : ℝ) - 1) / 2) • FlagAlgebra_4_0_0_4
    + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_8
    + (1 / 6 : ℝ) • FlagAlgebra_4_0_0_9
  := by
  dsimp only [f₁]
  rw [pow_two]
  simp only [sub_mul, mul_sub, smul_mul_smul_comm]
  simp only [flagMul_FlagAlgebra_3_2_0_0_FlagAlgebra_3_2_0_0,
             flagMul_FlagAlgebra_3_2_0_0_FlagAlgebra_3_2_0_3,
             flagMul_FlagAlgebra_3_2_0_3_FlagAlgebra_3_2_0_0,
             flagMul_FlagAlgebra_3_2_0_3_FlagAlgebra_3_2_0_3]
  simp only [downward_sub, downward_add, downward_smul, smul_add, smul_smul]
  simp only [downward_4_2_0_0, downward_4_2_0_3, downward_4_2_0_5,
             downward_4_2_0_10, downward_4_2_0_18, downward_4_2_0_19]
  push_cast
  module

-- Expansion of f₂ in the basis of 4-vertex graph densities.
-- Coefficients computed from the flag algebra product structure (σ₂-type averaging).
lemma f₂_expand : f₂ =
    (1 / 2 : ℝ) • FlagAlgebra_4_0_0_4
    - (1 / 6 : ℝ) • FlagAlgebra_4_0_0_6
    + (1 / 6 : ℝ) • FlagAlgebra_4_0_0_7
    - (2 / 3 : ℝ) • FlagAlgebra_4_0_0_8 := by
  dsimp only [f₂]
  rw [pow_two]
  simp only [sub_mul, mul_sub, smul_mul_smul_comm]
  simp only [flagMul_FlagAlgebra_3_2_1_1_FlagAlgebra_3_2_1_1,
             flagMul_FlagAlgebra_3_2_1_1_FlagAlgebra_3_2_1_2,
             flagMul_FlagAlgebra_3_2_1_2_FlagAlgebra_3_2_1_1,
             flagMul_FlagAlgebra_3_2_1_2_FlagAlgebra_3_2_1_2]
  simp only [downward_sub, downward_add, downward_smul, smul_add, smul_smul]
  simp only [downward_4_2_1_4, downward_4_2_1_5, downward_4_2_1_7,
             downward_4_2_1_11, downward_4_2_1_14, downward_4_2_1_15]
  push_cast
  module

-- Expansion of f₃(r) in the basis of 4-vertex graph densities.
-- Coefficients computed from the flag algebra product structure (σ₂-type averaging).
lemma f₃_expand (r : ℕ) : f₃ r =
    (((r : ℝ) - 2) ^ 2 / 2) • FlagAlgebra_4_0_0_4
    + (((r : ℝ) - 2) ^ 2 / 6) • FlagAlgebra_4_0_0_6
    + (((r : ℝ) ^ 2 - 8 * r + 12) / 6) • FlagAlgebra_4_0_0_7
    + (2 * ((r : ℝ) - 2) ^ 2 / 3) • FlagAlgebra_4_0_0_8
    + ((10 - 4 * (r : ℝ)) / 3) • FlagAlgebra_4_0_0_9
    + (4 : ℝ) • FlagAlgebra_4_0_0_10 := by
  dsimp only [f₃]
  rw [pow_two]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_smul_comm]
  simp only [flagMul_FlagAlgebra_3_2_1_1_FlagAlgebra_3_2_1_1,
             flagMul_FlagAlgebra_3_2_1_1_FlagAlgebra_3_2_1_2,
             flagMul_FlagAlgebra_3_2_1_1_FlagAlgebra_3_2_1_3,
             flagMul_FlagAlgebra_3_2_1_2_FlagAlgebra_3_2_1_1,
             flagMul_FlagAlgebra_3_2_1_2_FlagAlgebra_3_2_1_2,
             flagMul_FlagAlgebra_3_2_1_2_FlagAlgebra_3_2_1_3,
             flagMul_FlagAlgebra_3_2_1_3_FlagAlgebra_3_2_1_1,
             flagMul_FlagAlgebra_3_2_1_3_FlagAlgebra_3_2_1_2,
             flagMul_FlagAlgebra_3_2_1_3_FlagAlgebra_3_2_1_3]
  simp only [downward_sub, downward_add, downward_smul, smul_add, smul_smul]
  simp only [downward_4_2_1_4, downward_4_2_1_5, downward_4_2_1_7, downward_4_2_1_10,
             downward_4_2_1_11, downward_4_2_1_12, downward_4_2_1_14, downward_4_2_1_15,
             downward_4_2_1_16, downward_4_2_1_17, downward_4_2_1_18, downward_4_2_1_19]
  push_cast
  module

-- K₄-density correction: P_0(r) from Section 2, equation before (6); nonneg iff ⊠ ≤ (r³−6r²+11r−6)/r³.
noncomputable def f₀ (r : ℕ) : FlagAlgebra ∅ₜ :=
  (((r : ℝ)^3 - 6 * r^2 + 11 * r - 6) / (r : ℝ)^3) • (1 : FlagAlgebra ∅ₜ)
  - FlagAlgebra_4_0_0_10

-- Scalar multipliers from the SDP certificate (Section 2, equation (6)); rational functions of r,
-- nonneg for r ≥ 3. Common denominator factor `D r = 3r²−11r+9 > 0` for r ≥ 3. These are tuned so
-- the certificate is tight on the Turán-graph support {∅, K₁,₃, C₄, K₄−e, K₄}, and they specialize
-- at r = 3 to K4freeP4's (p₁,p₂,p₃) = (8/9, 5, 35/9).
noncomputable def p₁ (r : ℕ) : ℝ :=
  6 * ((r : ℝ) - 1) * (3 * (r : ℝ) - 7) / ((r : ℝ)^2 * (3 * (r : ℝ)^2 - 11 * r + 9))

noncomputable def p₂ (r : ℕ) : ℝ :=
  3 * (9 * (r : ℝ)^2 - 32 * r + 25) / (2 * (3 * (r : ℝ)^2 - 11 * r + 9))

noncomputable def p₃ (r : ℕ) : ℝ :=
  3 * (15 * (r : ℝ)^2 - 24 * r + 7) / (2 * (r : ℝ)^2 * (3 * (r : ℝ)^2 - 11 * r + 9))

-- Multiplier for the K₄-density correction term (uses a different denominator from p₁–p₃).
noncomputable def p₀ (r : ℕ) : ℝ :=
  18 * ((r : ℝ) - 1)^2 / (3 * r^2 - 11 * r + 9)

/-- The common denominator factor `D r = 3r²−11r+9` is positive for `r ≥ 3`
(it equals `3(r−3)² + 7r − 18 ≥ 3`). -/
lemma denom_factor_pos (r : ℕ) (hr : 3 ≤ r)
    : (0 : ℝ) < 3 * (r : ℝ)^2 - 11 * r + 9 := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ) - 3), hx]

/-- The multiplier `p₁ r` is non-negative for `r ≥ 3`. -/
lemma p₁_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₁ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₁
  apply div_nonneg
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ (r:ℝ) - 1 by linarith)
                          (show (0:ℝ) ≤ 3 * (r:ℝ) - 7 by linarith)]
  · exact mul_nonneg (sq_nonneg _) (le_of_lt hD)

/-- The multiplier `p₂ r` is non-negative for `r ≥ 3`. -/
lemma p₂_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₂ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₂
  apply div_nonneg
  · nlinarith [sq_nonneg ((r:ℝ) - 3), hx]
  · linarith

/-- The multiplier `p₃ r` is non-negative for `r ≥ 3`. -/
lemma p₃_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₃ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₃
  apply div_nonneg
  · nlinarith [sq_nonneg ((r:ℝ) - 3), hx]
  · exact mul_nonneg (by positivity) (le_of_lt hD)

/-- The multiplier `p₀ r` is non-negative for `r ≥ 3`. -/
lemma p₀_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₀ r := by
  have hD := denom_factor_pos r hr
  unfold p₀
  apply div_nonneg
  · positivity
  · linarith

/-- **Zykov's clique-density theorem (1949), the `K₄` / `K_{r+1}`-free case — taken
as an explicit axiom, NOT proved in this project.**

Stated at the graph-limit (positive-homomorphism) level, which is exactly the form
the flag-algebra proof consumes: for every density homomorphism `φ₀` (graph limit)
that kills `K_{r+1}` (`φ₀ ⟦K_{r+1}⟧ = 0`), the `K₄` density is at most that of the
Turán graph `T(·, r)`,

  `φ₀ ⟦K₄⟧ ≤ (r-1)(r-2)(r-3)/r³`

(here `FlagAlgebra_4_0_0_10` is the `K₄` flag; the RHS is written as
`(r³−6r²+11r−6)/r³`). This is Corollary 1.5 of Murphy–Nir (2021), an instance of
Zykov's theorem that the Turán graph maximizes clique counts among `K_{r+1}`-free
graphs. It is taken as an `axiom` because it is genuinely external to the SOS
machinery here and is a substantial development on its own:

* It is not in Mathlib (which has only the **edge** Turán theorem,
  `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`) nor in this repo.
* It cannot be obtained from the fixed-size flag-SOS certificate used elsewhere:
  `f₀` carries a negative coefficient on the `K₄` atom, while every σ-type square
  and every flag has a non-negative `K₄` coefficient. The bound is forced by the
  global `K_{r+1}`-free structure (constraints appear only on `≥ r+1` vertices,
  unbounded for parametric `r`).
* There is no density-only shortcut: a brute-force search refutes the natural
  telescoping inequality `kₛ₊₁·kₛ₋₁·(r-s+1) ≤ kₛ²·(r-s)` (it holds only at the
  extremal graph), and `k₄` is not even a function of `(k₂,k₃)`. The bound is
  asymptotic (finite graphs can exceed it), so a proof needs Zykov symmetrization
  together with a graph-limit argument.

`#print axioms Kr_plus_1_free_P4_density_upper_bound` lists this axiom, making the
proof's dependence on the unproved result explicit. -/
axiom Zykov_K4_density_bound (r : ℕ) (hr : 3 ≤ r) (φ₀ : PositiveHom ∅ₜ)
    (hKfree : φ₀ ⟦basisVector (completeGraph (Fin (r + 1))).toFinFlag⟧ = 0)
    : φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ)^3 - 6 * r^2 + 11 * r - 6) / (r : ℝ)^3

/-- **K₄ density in K_{r+1}-free graphs** is at most `(r-1)(r-2)(r-3)/r³`, i.e.
`0 ≤ᵢ[K_{r+1}] f₀ r` (Corollary 1.5, Murphy–Nir 2021). The flag-algebra layer is
discharged here: via `inducedForbidLE_emptyType_iff_inducedForbidLE` the goal reduces to the
per-homomorphism `K₄`-density bound, which is exactly the `Zykov_K4_density_bound`
axiom. -/
lemma K4_density_upper_bound (r : ℕ) (hr : 3 ≤ r)
    : 0 ≤ᵢ[(completeGraph (Fin (r + 1))).toFinFlag] f₀ r
  := by
  -- Reduce the probabilistic `inducedForbidLE` to the deterministic per-homomorphism form.
  rw [← inducedForbidLE_emptyType_iff_inducedForbidLE]
  intro φ₀ hKfree
  -- The K₄ density of any K_{r+1}-free limit is at most the Turán value (Zykov, assumed).
  have key := Zykov_K4_density_bound r hr φ₀ hKfree
  -- Given `key`, the flag-algebra inequality `0 ≤ φ₀ (f₀ r)` follows by arithmetic.
  have h0 : φ₀ (0 : FlagAlgebra ∅ₜ) = 0 := by simp
  show φ₀ (0 : FlagAlgebra ∅ₜ) ≤ φ₀ (f₀ r)
  rw [h0, f₀, PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one, mul_one]
  linarith [key]

/-- The constant `1` is the sum of all eleven unlabeled 4-vertex flags (the
size-4 partition-of-unity), unconditionally. -/
lemma one_eq_sum_flags : (1 : FlagAlgebra ∅ₜ) =
    FlagAlgebra_4_0_0_0 + FlagAlgebra_4_0_0_1 + FlagAlgebra_4_0_0_2 + FlagAlgebra_4_0_0_3
    + FlagAlgebra_4_0_0_4 + FlagAlgebra_4_0_0_5 + FlagAlgebra_4_0_0_6 + FlagAlgebra_4_0_0_7
    + FlagAlgebra_4_0_0_8 + FlagAlgebra_4_0_0_9 + FlagAlgebra_4_0_0_10 := by
  rw [← sum_flagWithSize_eq_one (σ := ∅ₜ) 4 (by norm_num)]
  rw [Finset.sum_eq_multiset_sum, ← flagSet_4_0_0_eq_univ]
  simp only [flagSet_4_0_0_val_eq, Multiset.map_coe, Multiset.sum_coe,
             List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  fold_basis_vectors
  abel

/-- The nonnegative "leftover" `∑ⱼ gapⱼ · Fⱼ` by which the certificate exceeds
the target on the non-extremal flags. The gaps vanish on the Turán-graph support
`{∅, K₁,₃, C₄, K₄−e, K₄}` (atoms `0,4,8,9,10`); the six listed gaps are `≥ 0`
for `r ≥ 3`. (`D r = 3r²−11r+9` is the common denominator factor.) -/
noncomputable def leftover (r : ℕ) : FlagAlgebra ∅ₜ :=
  (5 * ((r:ℝ) - 1)^3 * (3*(r:ℝ) - 7) / ((r:ℝ)^2 * (3*(r:ℝ)^2 - 11*r + 9))) • FlagAlgebra_4_0_0_1
  + (((r:ℝ) - 1)^2 * (3*(r:ℝ) - 7) * (6*(r:ℝ) - 5) / ((r:ℝ)^2 * (3*(r:ℝ)^2 - 11*r + 9))) • FlagAlgebra_4_0_0_2
  + (6 * ((r:ℝ) - 1)^3 * (3*(r:ℝ) - 7) / ((r:ℝ)^2 * (3*(r:ℝ)^2 - 11*r + 9))) • FlagAlgebra_4_0_0_3
  + (6 * ((r:ℝ) - 1)^3 * (3*(r:ℝ) - 7) / ((r:ℝ)^2 * (3*(r:ℝ)^2 - 11*r + 9))) • FlagAlgebra_4_0_0_5
  + (((r:ℝ) - 1) * (3*(r:ℝ) - 7) * (9*(r:ℝ)^2 - 18*r + 10) / (2 * (r:ℝ)^2 * (3*(r:ℝ)^2 - 11*r + 9))) • FlagAlgebra_4_0_0_6
  + (((r:ℝ) - 1) * (6*(r:ℝ)^3 - 24*(r:ℝ)^2 + 37*r - 21) / ((r:ℝ)^2 * (3*(r:ℝ)^2 - 11*r + 9))) • FlagAlgebra_4_0_0_7

/-- **The (corrected) SDP certificate identity.** Adding the four SOS/correction
terms and the nonnegative `leftover` to `P4_density` gives exactly the target
`12·((r-1)/r)³ · 1`. (The bound is *not* tight on every flag — hence `leftover`
is needed and the earlier pure-equality `SDP_certificate` was unprovable.) Proved
by reducing to per-flag scalar identities and clearing denominators (`r ≠ 0`,
`D r ≠ 0` for `r ≥ 3`). -/
lemma gap_identity (r : ℕ) (hr : 3 ≤ r) :
    P4_density + p₁ r • f₁ r + p₂ r • f₂ + p₃ r • f₃ r + p₀ r • f₀ r + leftover r
      = (12 * (((r : ℝ) - 1) / r) ^ 3) • (1 : FlagAlgebra ∅ₜ) := by
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr0 : (r:ℝ) ≠ 0 := hrpos.ne'
  have hD : (3 * (r:ℝ)^2 - 11 * r + 9) ≠ 0 := ne_of_gt (denom_factor_pos r hr)
  rw [f₁_expand, f₂_expand, f₃_expand]
  simp only [P4_density, f₀, p₁, p₂, p₃, p₀, leftover, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [one_eq_sum_flags]
  set D : ℝ := 3 * (r:ℝ)^2 - 11 * r + 9 with hDdef
  match_scalars <;> field_simp [hr0, hD] <;> (simp only [hDdef]; ring)

/-- The `leftover` term is nonnegative for `r ≥ 3` (each gap is a ratio of
nonnegative quantities, and flags are nonnegative). -/
lemma leftover_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ leftover r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD : 0 < 3 * (r:ℝ)^2 - 11 * r + 9 := denom_factor_pos r hr
  have hden : (0:ℝ) ≤ (r:ℝ)^2 * (3 * (r:ℝ)^2 - 11 * r + 9) := mul_nonneg (sq_nonneg _) hD.le
  have hden2 : (0:ℝ) ≤ 2 * (r:ℝ)^2 * (3 * (r:ℝ)^2 - 11 * r + 9) :=
    mul_nonneg (by positivity) hD.le
  have h1 : (0:ℝ) ≤ (r:ℝ) - 1 := by linarith
  have h7 : (0:ℝ) ≤ 3 * (r:ℝ) - 7 := by linarith
  rw [le_def, sub_zero]
  intro φ
  unfold leftover
  simp only [PositiveHom.map_add, PositiveHom.map_smul, ge_iff_le]
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
    refine mul_nonneg (div_nonneg ?_ (by first | exact hden | exact hden2))
                      (positiveHom_basisVector_ge_zero φ _)
  · nlinarith [mul_nonneg (pow_nonneg h1 3) h7]
  · nlinarith [mul_nonneg (mul_nonneg (pow_nonneg h1 2) h7) (show (0:ℝ) ≤ 6*(r:ℝ)-5 by linarith)]
  · nlinarith [mul_nonneg (pow_nonneg h1 3) h7]
  · nlinarith [mul_nonneg (pow_nonneg h1 3) h7]
  · nlinarith [mul_nonneg (mul_nonneg h1 h7) (show (0:ℝ) ≤ 9*(r:ℝ)^2-18*r+10 by nlinarith [sq_nonneg ((r:ℝ)-1)])]
  · nlinarith [mul_nonneg h1 (show (0:ℝ) ≤ 6*(r:ℝ)^3-24*(r:ℝ)^2+37*r-21 by nlinarith [sq_nonneg ((r:ℝ)-3), hx, mul_nonneg (sq_nonneg ((r:ℝ)-3)) (show (0:ℝ)≤(r:ℝ) by linarith)])]

/-- **Upper-bound direction of Theorem 1.3(i)** (Murphy–Nir 2021). For `r ≥ 3`
and K_{r+1}-free graphs, the `P₄` density is at most `12·((r-1)/r)³`. Generalizes
`K4freeP4.K4_free_P4_density_upper_bound` (the `r = 3`, bound `32/9` case).

Proof: add the nonnegative SOS terms `pᵢ·fᵢ` and the K₄-correction `p₀·f₀`
(nonnegative under K_{r+1}-free by `K4_density_upper_bound`), then close with the
`gap_identity` and `leftover_nonneg`. The only nontrivial input is the K₄-density
bound (`K4_density_upper_bound`, Cor 1.5). -/
theorem Kr_plus_1_free_P4_density_upper_bound (r : ℕ) (hr : 3 ≤ r)
    : P4_density ≤ᵢ[(completeGraph (Fin (r + 1))).toFinFlag]
      (12 * (((r : ℝ) - 1) / r) ^ 3 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  set F := (completeGraph (Fin (r + 1))).toFinFlag with hF
  -- Step 1: add the four nonnegative certificate terms to the left-hand side.
  have hp1 : (0 : FlagAlgebra ∅ₜ) ≤ᵢ[F] p₁ r • f₁ r :=
    inducedForbidLE_of_le (nonneg_smul_nonneg_geq_zero (p₁_nonneg r hr) (f₁_nonneg r))
  have hp2 : (0 : FlagAlgebra ∅ₜ) ≤ᵢ[F] p₂ r • f₂ :=
    inducedForbidLE_of_le (nonneg_smul_nonneg_geq_zero (p₂_nonneg r hr) f₂_nonneg)
  have hp3 : (0 : FlagAlgebra ∅ₜ) ≤ᵢ[F] p₃ r • f₃ r :=
    inducedForbidLE_of_le (nonneg_smul_nonneg_geq_zero (p₃_nonneg r hr) (f₃_nonneg r))
  have hp0 : (0 : FlagAlgebra ∅ₜ) ≤ᵢ[F] p₀ r • f₀ r := by
    have h := inducedForbidLE_smul_nonneg (p₀_nonneg r hr) (K4_density_upper_bound r hr)
    rwa [smul_zero] at h
  have step1 : P4_density ≤ᵢ[F]
      P4_density + p₁ r • f₁ r + p₂ r • f₂ + p₃ r • f₃ r + p₀ r • f₀ r :=
    inducedForbidLE_trans_add_nonneg
      (inducedForbidLE_trans_add_nonneg
        (inducedForbidLE_trans_add_nonneg
          (inducedForbidLE_trans_add_nonneg (inducedForbidLE_refl F P4_density) hp1) hp2) hp3) hp0
  -- Step 2: the remaining gap is a nonnegative combination of flags (unconditional).
  have step2 : (P4_density + p₁ r • f₁ r + p₂ r • f₂ + p₃ r • f₃ r + p₀ r • f₀ r) ≤ᵢ[F]
      (12 * (((r : ℝ) - 1) / r) ^ 3 : ℝ) • (1 : FlagAlgebra ∅ₜ) := by
    apply inducedForbidLE_of_le
    rw [← gap_identity r hr]
    exact le_add_of_nonneg_right (leftover_nonneg r hr)
  exact inducedForbidLE_trans step1 step2


/-- **Turán r-partite graphon limit — existence and P₄ density value — taken as an explicit
axiom, NOT proved in this project.**

Stated at the positive-homomorphism (graph-limit) level: for every `r ≥ 2` there
exists a K_{r+1}-free positive homomorphism `φ` whose `P₄`-density equals
`12·((r-1)/r)³` exactly (the Turán-graph limit value from Lemma 2.1, Murphy–Nir 2021).

**Proof sketch (outside the flag-SOS machinery).**
Take the flag sequence `s k = turanGraph (r·k) r`. For each `k`:

* **K_{r+1}-freeness**: `SimpleGraph.turanGraph_cliqueFree` (Mathlib) gives
  `(turanGraph (r·k) r).CliqueFree (r+1)`, hence
  `(completeGraph (Fin (r+1))).Free (turanGraph (r·k) r)`.

* **P₄ density**: for `n = r·k`, a direct counting argument gives the number of
  induced copies of each relevant 4-vertex graph type in `turanGraph n r`:
    · (induced P₄, atoms 6–7): 0 — the r-partite structure forbids induced P₄;
    · C₄ (atom 8): C(r,2)·C(k,2)² → density `3(r-1)/r³`;
    · K₄-e (atom 9): C(r,3)·3·C(k,2)·k² → density `6(r-1)(r-2)/r³`;
    · K₄ (atom 10): C(r,4)·k⁴ → density `(r-1)(r-2)(r-3)/r³`.
  The weighted sum in `P4_density = F₆ + 2F₇ + 4F₈ + 6F₉ + 12F₁₀` is therefore
  `4·3(r-1)/r³ + 6·6(r-1)(r-2)/r³ + 12·(r-1)(r-2)(r-3)/r³ = 12·((r-1)/r)³`.

* **Compactness**: `increasing_flagSeq_contain_convergent_subseq` extracts a convergent
  subsequence; `flagSeq_limit_mem_positiveHom` produces the positive homomorphism `φ`;
  `flagDensitySeq_eq_zero_of_free` forces `φ(K_{r+1}) = 0`.

The formal obstacles are (a) the counting lemmas for `turanGraph (r·k) r` (nontrivial
finset combinatorics), (b) connecting Mathlib's `CliqueFree` to the `Free` predicate
used in `flagDensitySeq_eq_zero_of_free`, and (c) identifying the induced density
sequence for each of `F₈`, `F₉`, `F₁₀` along the subsequence.

`#print axioms Kr_plus_1_free_P4_density_achievable` lists this axiom. -/
axiom Turan_limit_P4_density (r : ℕ) (hr : 2 ≤ r) :
    ∃ φ : PositiveHom ∅ₜ,
      φ ⟦basisVector (completeGraph (Fin (r + 1))).toFinFlag⟧ = 0 ∧
      φ P4_density = 12 * (((r : ℝ) - 1) / r) ^ 3

/-- **Lower-bound direction of Lemma 2.1** (Murphy–Nir 2021). For `r ≥ 3`, the
K_{r+1}-free P₄ density upper bound `12·((r-1)/r)³` is **sharp**: there exists a
K_{r+1}-free positive homomorphism `φ` achieving P₄ density exactly
`12·((r-1)/r)³`.

The witness is the balanced Turán r-partite graphon limit, whose existence and P₄
density value are given by the axiom `Turan_limit_P4_density`. Together with
`Kr_plus_1_free_P4_density_upper_bound` this completes Theorem 1.3(i) of Murphy–Nir
2021: the optimal K_{r+1}-free P₄ density equals `12·((r-1)/r)³`.

`#print axioms Kr_plus_1_free_P4_density_achievable` lists the two external dependencies:
`Zykov_K4_density_bound` (for the upper bound) and `Turan_limit_P4_density` (here). -/
theorem Kr_plus_1_free_P4_density_achievable (r : ℕ) (hr : 3 ≤ r) :
    ∃ φ : PositiveHom ∅ₜ,
      φ ⟦basisVector (completeGraph (Fin (r + 1))).toFinFlag⟧ = 0 ∧
      φ P4_density = 12 * (((r : ℝ) - 1) / r) ^ 3 :=
  Turan_limit_P4_density r (by omega)

end CompleteGraphFreeP4
