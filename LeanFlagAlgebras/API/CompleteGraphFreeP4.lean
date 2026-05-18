import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.ReduceFlagMul
import LeanFlagAlgebras.Flags.Densities.MulLoader
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.Utils.SortTactic
import LeanFlagAlgebras.Forbid.CommonGraphs

/-! # API.CompleteGraphFreeP4 — P₄ density bound in K_{r+1}-free graphs

Per-problem density-bound proof on the API automation layer, generalizing
`API.K4freeP4` from K₄ to an arbitrary forbidden complete graph K_{r+1}. The
headline result `Kr_plus_1_free_P4_density_upper_bound` (upper-bound direction
of Theorem 1.3(i), Murphy–Nir 2021) states that for `r ≥ 3` and K_{r+1}-free
graphs the `P₄` density is at most `12·((r-1)/r)³`:

  `P4_density ≤[(completeGraph (Fin (r+1))).toFinFlag]
     (12 * (((r:ℝ) - 1) / r) ^ 3) • (1 : FlagAlgebra ∅ₜ)`.

The certificate consists of r-parameterized squared terms `f₁ r, f₂, f₃ r`,
a K₄-density correction term `f₀ r`, and rational-function multipliers
`p₀..p₃ r`. Several supporting facts (the basis expansions, multiplier
non-negativity, the `SDP_certificate` identity, and the headline theorem) are
currently `sorry` placeholders. The `r = 3` case specializes to
`K4freeP4.K4_free_P4_density_upper_bound` with bound `32/9`. -/

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph

namespace CompleteGraphFreeP4

-- Includes `12 • FlagAlgebra_4_0_0_10` (K₄), which K4freeP4.P4_density omits because it vanishes for K₄-free graphs.
noncomputable def P4_density : FlagAlgebra ∅ₜ :=
  1 • FlagAlgebra_4_0_0_6
  + 2 • FlagAlgebra_4_0_0_7
  + 4 • FlagAlgebra_4_0_0_8
  + 6 • FlagAlgebra_4_0_0_9
  + 12 • FlagAlgebra_4_0_0_10

-- σ₁-type (no-edge label) Cauchy-Schwarz squared term; f₁ 3 = K4freeP4.f₁.
noncomputable def f₁ (r : ℕ) : FlagAlgebra ∅ₜ :=
  ⟦((r - 1) • FlagAlgebra_3_2_0_0 - 1 • FlagAlgebra_3_2_0_3) ^ 2⟧₀

-- r-independent σ₂-type (edge-label) Cauchy-Schwarz term; identical to K4freeP4.f₂.
noncomputable def f₂ : FlagAlgebra ∅ₜ :=
  ⟦(1 • FlagAlgebra_3_2_1_1 - 1 • FlagAlgebra_3_2_1_2) ^ 2⟧₀

-- σ₂-type Cauchy-Schwarz squared term; f₃ 3 = K4freeP4.f₃.
noncomputable def f₃ (r : ℕ) : FlagAlgebra ∅ₜ :=
  ⟦((r - 2) • FlagAlgebra_3_2_1_1 + (r - 2) • FlagAlgebra_3_2_1_2
    - 2 • FlagAlgebra_3_2_1_3) ^ 2⟧₀

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

-- Expansion of f₁(r) in the basis of 4-vertex graph densities.
-- Coefficients computed from the flag algebra product structure (σ₁-type averaging).
lemma f₁_expand (r : ℕ) : f₁ r =
    ((r : ℝ) - 1) ^ 2 • FlagAlgebra_4_0_0_0
    + (((r : ℝ) - 1) ^ 2 / 6) • FlagAlgebra_4_0_0_1
    - (((r : ℝ) - 1) / 6) • FlagAlgebra_4_0_0_2
    - (((r : ℝ) - 1) / 2) • FlagAlgebra_4_0_0_4
    + (1 / 3 : ℝ) • FlagAlgebra_4_0_0_8
    + (1 / 6 : ℝ) • FlagAlgebra_4_0_0_9 := by sorry

-- Expansion of f₂ in the basis of 4-vertex graph densities.
-- Coefficients computed from the flag algebra product structure (σ₂-type averaging).
lemma f₂_expand : f₂ =
    (1 / 2 : ℝ) • FlagAlgebra_4_0_0_4
    - (1 / 6 : ℝ) • FlagAlgebra_4_0_0_6
    + (1 / 6 : ℝ) • FlagAlgebra_4_0_0_7
    - (2 / 3 : ℝ) • FlagAlgebra_4_0_0_8 := by sorry

-- Expansion of f₃(r) in the basis of 4-vertex graph densities.
-- Coefficients computed from the flag algebra product structure (σ₂-type averaging).
lemma f₃_expand (r : ℕ) : f₃ r =
    (((r : ℝ) - 2) ^ 2 / 2) • FlagAlgebra_4_0_0_4
    + (((r : ℝ) - 2) ^ 2 / 6) • FlagAlgebra_4_0_0_6
    + (((r : ℝ) ^ 2 - 8 * r + 12) / 6) • FlagAlgebra_4_0_0_7
    + (2 * ((r : ℝ) - 2) ^ 2 / 3) • FlagAlgebra_4_0_0_8
    + ((10 - 4 * (r : ℝ)) / 3) • FlagAlgebra_4_0_0_9
    + (4 : ℝ) • FlagAlgebra_4_0_0_10 := by sorry

-- K₄-density correction: P_0(r) from Section 2, equation before (6); nonneg iff ⊠ ≤ (r³−6r²+11r−6)/r³.
noncomputable def f₀ (r : ℕ) : FlagAlgebra ∅ₜ :=
  (((r : ℝ)^3 - 6 * r^2 + 11 * r - 6) / (r : ℝ)^3) • (1 : FlagAlgebra ∅ₜ)
  - FlagAlgebra_4_0_0_10

-- Scalar multipliers from the SDP certificate (Section 2, equation (6)); rational functions of r, nonneg for r ≥ 3.
noncomputable def p₁ (r : ℕ) : ℝ :=
  (3 * (r : ℝ)^3 - 10 * r^2 + 7 * r) / (3 * r^5 - 11 * r^4 + 9 * r^3)

noncomputable def p₂ (r : ℕ) : ℝ :=
  (9 * (r : ℝ)^5 - 32 * r^4 + 25 * r^3) / (4 * (3 * r^5 - 11 * r^4 + 9 * r^3))

noncomputable def p₃ (r : ℕ) : ℝ :=
  (15 * (r : ℝ)^3 - 24 * r^2 + 7 * r) / (4 * (3 * r^5 - 11 * r^4 + 9 * r^3))

-- Multiplier for the K₄-density correction term (uses a different denominator from p₁–p₃).
noncomputable def p₀ (r : ℕ) : ℝ :=
  18 * ((r : ℝ) - 1)^2 / (3 * r^2 - 11 * r + 9)

/-- The multiplier `p₁ r` is non-negative for `r ≥ 3` (proof TODO). -/
lemma p₁_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₁ r := by sorry

/-- The multiplier `p₂ r` is non-negative for `r ≥ 3` (proof TODO). -/
lemma p₂_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₂ r := by sorry

/-- The multiplier `p₃ r` is non-negative for `r ≥ 3` (proof TODO). -/
lemma p₃_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₃ r := by sorry

/-- The multiplier `p₀ r` is non-negative for `r ≥ 3` (proof TODO). -/
lemma p₀_nonneg (r : ℕ) (hr : 3 ≤ r) : 0 ≤ p₀ r := by sorry

-- K₄ density in K_{r+1}-free graphs is at most (r³−6r²+11r−6)/r³, i.e. f0 r ≥ 0 (Corollary 1.5, Murphy–Nir 2021).
lemma K4_density_upper_bound (r : ℕ) (hr : 3 ≤ r)
    : 0 ≤[(completeGraph (Fin (r + 1))).toFinFlag] f₀ r
  := by sorry

-- Algebraic identity: the SDP certificate terms sum to the target bound.
lemma SDP_certificate (r : ℕ) (hr : 3 ≤ r)
    : P4_density + p₁ r • f₁ r + p₂ r • f₂ + p₃ r • f₃ r + p₀ r • f₀ r
      = (12 * (((r : ℝ) - 1) / r) ^ 3) • (1 : FlagAlgebra ∅ₜ)
  := by sorry

-- Upper bound direction of Theorem 1.3(i) (Murphy–Nir 2021); generalizes K4freeP4.K4_free_P4_density_upper_bound (r = 3, bound = 32/9).
theorem Kr_plus_1_free_P4_density_upper_bound (r : ℕ) (hr : 3 ≤ r)
    : P4_density ≤[(completeGraph (Fin (r + 1))).toFinFlag]
      (12 * (((r : ℝ) - 1) / r) ^ 3 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end CompleteGraphFreeP4
