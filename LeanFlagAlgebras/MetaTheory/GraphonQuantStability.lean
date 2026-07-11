import LeanFlagAlgebras.MetaTheory.GraphonMoments

/-! # Quantitative stability at the kernel level (paper §11.8,
`thm:k4free-p4-quant-stability`, `thm:parametric-quant-stability`)

Near the slice, the exact moment identities survive with explicit errors.  This module is
the kernel-level algebra: it consumes bounds `R_η ≤ A`, `R_τ ≤ B` on the square errors
(delivered, at the hom level, by the certificate through `relative_slackness_term` — see
`ParametricP4Slice`; the kernel-level `R`'s are the graphon evaluations of the same averaged
squares, a correspondence not formalised here, so the bounds enter as hypotheses) and
produces the paper's quantitative conclusions:

* `quadratic_confinement` — `r(2r-3)(p-α⁻)(p-α⁺) ≤ (r-1)√A + ((r-2)/2)√B`, and the same
  bound for the deviation `|（D-p²) - (α⁺-p)(p-α⁻)|` (the two displays of
  `thm:parametric-quant-stability` (iii));
* `interval_localisation` — for `r ≥ 4`, `p` lies within
  `C/((r-1)(r-3))` of the interval `[α⁻, α⁺]` (`thm:parametric-quant-stability` (iii),
  final clause);
* `r3_edge_density_stability` — at `r = 3`: `(3p-2)² ≤ C` and
  `|p - 2/3| ≤ (1/3)·√C`, and the degree concentration `9·∫(d-p)² ≤ C + …` —
  the displays of `thm:k4free-p4-quant-stability` (with `C = 2√R_η + (1/2)√R_τ`; the
  paper's `(3/√2 + 3/(2√35))√Δ` form is the instance under the certificate bounds
  `R_η ≤ (9/8)Δ`, `R_τ ≤ (9/35)Δ`, recorded as `r3_certificate_instance`);
* `stability_via_modulus` — the final modulus implication, with the stability modulus
  taken abstractly: any predicate `close` guaranteed by a sufficiently high edge density is
  guaranteed by a sufficiently small deficit.

The `Δ^{1/4}` rates are stated with nested square roots (`√(C·√Δ)`), avoiding `Real.rpow`.
-/

open MeasureTheory unitInterval

namespace FlagAlgebras.MetaTheory

namespace Graphon

variable (G : Graphon)

/-! ## Parametric quadratic confinement (`thm:parametric-quant-stability` (iii)) -/

/-- Quadratic confinement of the edge density: from square-error bounds `R_η ≤ A`,
`R_τ ≤ B`,
`r(2r-3)(p-α⁻)(p-α⁺) ≤ (r-1)√A + ((r-2)/2)√B`. -/
theorem quadratic_confinement (r : ℕ) (hr : 3 ≤ r) {A B : ℝ}
    (hA : G.Reta r ≤ A) (hB : G.Rtau r ≤ B) :
    (r : ℝ) * (2 * r - 3) * (G.edgeDensity - alphaMinus r) * (G.edgeDensity - alphaPlus r)
      ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B := by
  -- `approximate_moments_interval` + monotonicity of `√` (`Real.sqrt_le_sqrt`) and of the
  -- non-negative coefficients.
  have hr' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : Real.sqrt (G.Reta r) ≤ Real.sqrt A := Real.sqrt_le_sqrt hA
  have h2 : Real.sqrt (G.Rtau r) ≤ Real.sqrt B := Real.sqrt_le_sqrt hB
  have hc1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
  have hc2 : (0 : ℝ) ≤ ((r : ℝ) - 2) / 2 := by linarith
  calc (r : ℝ) * (2 * r - 3) * (G.edgeDensity - alphaMinus r) * (G.edgeDensity - alphaPlus r)
      ≤ ((r : ℝ) - 1) * Real.sqrt (G.Reta r) + (((r : ℝ) - 2) / 2) * Real.sqrt (G.Rtau r) :=
        G.approximate_moments_interval r hr
    _ ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2)

/-- Deviation form: `r(2r-3)·|(D-p²) - (α⁺-p)(p-α⁻)| ≤ (r-1)√A + ((r-2)/2)√B`. -/
theorem moment_deviation_bound (r : ℕ) (hr : 3 ≤ r) {A B : ℝ}
    (hA : G.Reta r ≤ A) (hB : G.Rtau r ≤ B) :
    (r : ℝ) * (2 * r - 3)
        * |G.degSq - G.edgeDensity ^ 2
            - (alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r)|
      ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B := by
  -- `approximate_moments` + `abs_mul` (`r(2r-3) > 0` from `hr`) + `√`-monotonicity.
  have hr' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : Real.sqrt (G.Reta r) ≤ Real.sqrt A := Real.sqrt_le_sqrt hA
  have h2 : Real.sqrt (G.Rtau r) ≤ Real.sqrt B := Real.sqrt_le_sqrt hB
  have hc1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
  have hc2 : (0 : ℝ) ≤ ((r : ℝ) - 2) / 2 := by linarith
  have hpos : (0 : ℝ) ≤ (r : ℝ) * (2 * r - 3) := by nlinarith
  have key : (r : ℝ) * (2 * r - 3)
        * |G.degSq - G.edgeDensity ^ 2
            - (alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r)|
      = |(r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
          - (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
              * (G.edgeDensity - alphaMinus r)| := by
    rw [show (r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
          - (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
              * (G.edgeDensity - alphaMinus r)
        = (r : ℝ) * (2 * r - 3)
            * (G.degSq - G.edgeDensity ^ 2
                - (alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r)) from by ring,
      abs_mul, abs_of_nonneg hpos]
  calc (r : ℝ) * (2 * r - 3)
        * |G.degSq - G.edgeDensity ^ 2
            - (alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r)|
      = |(r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
          - (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
              * (G.edgeDensity - alphaMinus r)| := key
    _ ≤ ((r : ℝ) - 1) * Real.sqrt (G.Reta r) + (((r : ℝ) - 2) / 2) * Real.sqrt (G.Rtau r) :=
        G.approximate_moments r hr
    _ ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2)

/-- **Interval localisation for `r ≥ 4`, upper side** (`thm:parametric-quant-stability`
(iii), final clause): if `p > α⁺` then `p - α⁺ ≤ C/((r-1)(r-3))` where
`C = (r-1)√A + ((r-2)/2)√B`.  The symmetric lower side is
`interval_localisation_below`. -/
theorem interval_localisation (r : ℕ) (hr : 4 ≤ r) {A B : ℝ}
    (hA : G.Reta r ≤ A) (hB : G.Rtau r ≤ B)
    (hout : alphaPlus r < G.edgeDensity) :
    G.edgeDensity - alphaPlus r
      ≤ (((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B)
          / (((r : ℝ) - 1) * ((r : ℝ) - 3)) := by
  -- The paper's estimate: for `p > α⁺`,
  -- `q(p) := r(2r-3)(p-α⁻)(p-α⁺) ≥ r(2r-3)(α⁺-α⁻)(p-α⁺) = (r-1)(r-3)(p-α⁺)` using
  -- `α⁺-α⁻ = (r-1)(r-3)/(r(2r-3))` (verify by `field_simp`/`ring` with `r ≠ 0`,
  -- `2r-3 ≠ 0`); combine with `quadratic_confinement` and divide
  -- (`div` manipulations with `(r-1)(r-3) > 0` from `hr`).
  have hr' : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr3 : 3 ≤ r := le_trans (by norm_num) hr
  have hq := G.quadratic_confinement r hr3 hA hB
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have h2r3 : 2 * (r : ℝ) - 3 ≠ 0 := by linarith
  have hprod_pos : (0 : ℝ) < ((r : ℝ) - 1) * ((r : ℝ) - 3) := by nlinarith
  have hden_nonneg : (0 : ℝ) ≤ (r : ℝ) * (2 * (r : ℝ) - 3) := by nlinarith
  -- `r(2r-3)(α⁺-α⁻) = (r-1)(r-3)`
  have hab : ((r : ℝ) - 1) * ((r : ℝ) - 3)
      = (r : ℝ) * (2 * (r : ℝ) - 3) * (alphaPlus r - alphaMinus r) := by
    have hP : ((r : ℝ) - 1) / (r : ℝ) * (r : ℝ) = (r : ℝ) - 1 := div_mul_cancel₀ _ hr0
    have hM : ((r : ℝ) - 1) / (2 * (r : ℝ) - 3) * (2 * (r : ℝ) - 3) = (r : ℝ) - 1 :=
      div_mul_cancel₀ _ h2r3
    unfold alphaPlus alphaMinus
    linear_combination (-(2 * (r : ℝ) - 3)) * hP + (r : ℝ) * hM
  -- `p - α⁻ ≥ α⁺ - α⁻` since `p > α⁺`
  have hge : alphaPlus r - alphaMinus r ≤ G.edgeDensity - alphaMinus r := by linarith
  have hout' : (0 : ℝ) ≤ G.edgeDensity - alphaPlus r := by linarith
  have hkey : ((r : ℝ) - 1) * ((r : ℝ) - 3) * (G.edgeDensity - alphaPlus r)
      ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B := by
    calc ((r : ℝ) - 1) * ((r : ℝ) - 3) * (G.edgeDensity - alphaPlus r)
        = (r : ℝ) * (2 * (r : ℝ) - 3) * (alphaPlus r - alphaMinus r)
            * (G.edgeDensity - alphaPlus r) := by rw [hab]
      _ ≤ (r : ℝ) * (2 * (r : ℝ) - 3) * (G.edgeDensity - alphaMinus r)
            * (G.edgeDensity - alphaPlus r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hge hden_nonneg) hout'
      _ ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B := hq
  rw [le_div_iff₀ hprod_pos]
  nlinarith [hkey]

/-- **Interval localisation for `r ≥ 4`, lower side** (`thm:parametric-quant-stability`
(iii), the "symmetrically below `α⁻`" clause): if `p < α⁻` then
`α⁻ - p ≤ C/((r-1)(r-3))`. -/
theorem interval_localisation_below (r : ℕ) (hr : 4 ≤ r) {A B : ℝ}
    (hA : G.Reta r ≤ A) (hB : G.Rtau r ≤ B)
    (hout : G.edgeDensity < alphaMinus r) :
    alphaMinus r - G.edgeDensity
      ≤ (((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B)
          / (((r : ℝ) - 1) * ((r : ℝ) - 3)) := by
  -- By symmetry with `interval_localisation`: for `p < α⁻` both factors of
  -- `q(p) = r(2r-3)(p-α⁻)(p-α⁺)` are negative, so
  -- `q(p) = r(2r-3)(α⁻-p)(α⁺-p) ≥ r(2r-3)(α⁺-α⁻)(α⁻-p) = (r-1)(r-3)(α⁻-p)`.
  have hr' : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr3 : 3 ≤ r := le_trans (by norm_num) hr
  have hq := G.quadratic_confinement r hr3 hA hB
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have h2r3 : 2 * (r : ℝ) - 3 ≠ 0 := by linarith
  have hprod_pos : (0 : ℝ) < ((r : ℝ) - 1) * ((r : ℝ) - 3) := by nlinarith
  have hden_pos : (0 : ℝ) < (r : ℝ) * (2 * (r : ℝ) - 3) := by nlinarith
  -- `r(2r-3)(α⁺-α⁻) = (r-1)(r-3)`
  have hab : ((r : ℝ) - 1) * ((r : ℝ) - 3)
      = (r : ℝ) * (2 * (r : ℝ) - 3) * (alphaPlus r - alphaMinus r) := by
    have hP : ((r : ℝ) - 1) / (r : ℝ) * (r : ℝ) = (r : ℝ) - 1 := div_mul_cancel₀ _ hr0
    have hM : ((r : ℝ) - 1) / (2 * (r : ℝ) - 3) * (2 * (r : ℝ) - 3) = (r : ℝ) - 1 :=
      div_mul_cancel₀ _ h2r3
    unfold alphaPlus alphaMinus
    linear_combination (-(2 * (r : ℝ) - 3)) * hP + (r : ℝ) * hM
  -- `α⁻ ≤ α⁺` (from `hab`, both sides positive)
  have hle : alphaMinus r ≤ alphaPlus r := by nlinarith
  have hge' : alphaPlus r - alphaMinus r ≤ alphaPlus r - G.edgeDensity := by linarith
  have hout' : (0 : ℝ) ≤ alphaMinus r - G.edgeDensity := by linarith
  have hkey : ((r : ℝ) - 1) * ((r : ℝ) - 3) * (alphaMinus r - G.edgeDensity)
      ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B := by
    calc ((r : ℝ) - 1) * ((r : ℝ) - 3) * (alphaMinus r - G.edgeDensity)
        = (r : ℝ) * (2 * (r : ℝ) - 3) * (alphaPlus r - alphaMinus r)
            * (alphaMinus r - G.edgeDensity) := by rw [hab]
      _ ≤ (r : ℝ) * (2 * (r : ℝ) - 3) * (alphaPlus r - G.edgeDensity)
            * (alphaMinus r - G.edgeDensity) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hge' hden_pos.le) hout'
      _ = (r : ℝ) * (2 * (r : ℝ) - 3) * (G.edgeDensity - alphaMinus r)
            * (G.edgeDensity - alphaPlus r) := by ring
      _ ≤ ((r : ℝ) - 1) * Real.sqrt A + (((r : ℝ) - 2) / 2) * Real.sqrt B := hq
  rw [le_div_iff₀ hprod_pos]
  nlinarith [hkey]

/-! ## The `r = 3` chain (`thm:k4free-p4-quant-stability`) -/

/-- At `r = 3`: `(3p-2)² ≤ 2√A + (1/2)√B` (the square of the edge-density deviation is
controlled by the square-error bounds). -/
theorem r3_edge_sq_bound {A B : ℝ} (hA : G.Reta 3 ≤ A) (hB : G.Rtau 3 ≤ B)
    (_hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) :
    (3 * G.edgeDensity - 2) ^ 2 ≤ 2 * Real.sqrt A + (1 / 2) * Real.sqrt B := by
  -- At `r = 3`: `r(2r-3) = 9`, `α₃⁻ = α₃⁺ = 2/3`, so
  -- `9(p-α⁻)(p-α⁺) = 9(p-2/3)² = (3p-2)²` (`norm_num`/`ring` after unfolding `alpha*`),
  -- and `quadratic_confinement` gives the bound with coefficients `(3-1) = 2`,
  -- `(3-2)/2 = 1/2`.
  have h := G.quadratic_confinement 3 le_rfl hA hB
  have ha : alphaMinus 3 = 2 / 3 := by norm_num [alphaMinus]
  have hb : alphaPlus 3 = 2 / 3 := by norm_num [alphaPlus]
  rw [ha, hb] at h
  push_cast at h
  nlinarith [h]

/-- At `r = 3`: the degree concentration `9·∫(d-p)² ≤ 2√A + (1/2)√B`. -/
theorem r3_degree_concentration {A B : ℝ} (hA : G.Reta 3 ≤ A) (hB : G.Rtau 3 ≤ B)
    (_hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) :
    9 * (∫ x, (G.deg x - G.edgeDensity) ^ 2) ≤ 2 * Real.sqrt A + (1 / 2) * Real.sqrt B := by
  -- `approximate_moments_variance` at `r = 3`: the product term is `-(3p-2)²/9·9 ≤ 0`,
  -- so it can be dropped; coefficients as above.
  have h := G.approximate_moments_variance 3 le_rfl
  have ha : alphaMinus 3 = 2 / 3 := by norm_num [alphaMinus]
  have hb : alphaPlus 3 = 2 / 3 := by norm_num [alphaPlus]
  rw [ha, hb] at h
  push_cast at h
  have h1 : Real.sqrt (G.Reta 3) ≤ Real.sqrt A := Real.sqrt_le_sqrt hA
  have h2 : Real.sqrt (G.Rtau 3) ≤ Real.sqrt B := Real.sqrt_le_sqrt hB
  nlinarith [h, h1, h2, sq_nonneg (G.edgeDensity - 2 / 3)]

/-- At `r = 3`: the fourth-root edge-density rate, in nested-`√` form:
`|p - 2/3| ≤ (1/3)·√(2√A + (1/2)√B)`. -/
theorem r3_edge_density_stability {A B : ℝ} (hA : G.Reta 3 ≤ A) (hB : G.Rtau 3 ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    |G.edgeDensity - 2 / 3| ≤ (1 / 3) * Real.sqrt (2 * Real.sqrt A + (1 / 2) * Real.sqrt B) := by
  -- From `r3_edge_sq_bound`: `(3p-2)² ≤ RHS²̲` … precisely: `|3p-2| = 3|p-2/3|` and
  -- `|3p-2| ≤ √(bound)` via `abs_le_sqrt` (`(3p-2)² ≤ bound`); divide by 3.
  have h := G.r3_edge_sq_bound hA hB hA0 hB0
  have habs : |3 * G.edgeDensity - 2|
      ≤ Real.sqrt (2 * Real.sqrt A + (1 / 2) * Real.sqrt B) := Real.abs_le_sqrt h
  have heq : |G.edgeDensity - 2 / 3| = (1 / 3) * |3 * G.edgeDensity - 2| := by
    rw [show (1 : ℝ) / 3 = |(1 : ℝ) / 3| from (abs_of_nonneg (by norm_num)).symm, ← abs_mul]
    congr 1
    ring
  rw [heq]
  linarith [habs]

/-- **The certificate instance at `r = 3`** (`thm:k4free-p4-quant-stability`, first two
displays): under the `K₄`-free `P₄`-certificate bounds `R_η ≤ (9/8)Δ`, `R_τ ≤ (9/35)Δ`,
`(3p-2)² ≤ (3/√2 + 3/(2√35))·√Δ`. -/
theorem r3_certificate_instance {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hA : G.Reta 3 ≤ 9 / 8 * Δ) (hB : G.Rtau 3 ≤ 9 / 35 * Δ) :
    (3 * G.edgeDensity - 2) ^ 2
      ≤ (3 / Real.sqrt 2 + 3 / (2 * Real.sqrt 35)) * Real.sqrt Δ := by
  -- `r3_edge_sq_bound` with `A := (9/8)Δ`, `B := (9/35)Δ`; then
  -- `2·√((9/8)Δ) = 2·(3/(2√2))·√Δ = (3/√2)·√Δ` and
  -- `(1/2)·√((9/35)Δ) = (3/(2√35))·√Δ` — `Real.sqrt_mul` (`hΔ`-side conditions),
  -- `Real.sqrt_div`/`sqrt_eq_iff`-style computations; `norm_num` + `Real.sq_sqrt`.
  have hA0 : (0 : ℝ) ≤ 9 / 8 * Δ := by linarith
  have hB0 : (0 : ℝ) ≤ 9 / 35 * Δ := by linarith
  have h := G.r3_edge_sq_bound hA hB hA0 hB0
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs35 : (0 : ℝ) < Real.sqrt 35 := Real.sqrt_pos.mpr (by norm_num)
  have h98 : Real.sqrt (9 / 8) = 3 / (2 * Real.sqrt 2) := by
    have hsq : ((3 : ℝ) / (2 * Real.sqrt 2)) ^ 2 = 9 / 8 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have h935 : Real.sqrt (9 / 35) = 3 / Real.sqrt 35 := by
    have hsq : ((3 : ℝ) / Real.sqrt 35) ^ 2 = 9 / 35 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 35)]
      norm_num
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have e1 : Real.sqrt (9 / 8 * Δ) = 3 / (2 * Real.sqrt 2) * Real.sqrt Δ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 8), h98]
  have e2 : Real.sqrt (9 / 35 * Δ) = 3 / Real.sqrt 35 * Real.sqrt Δ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 35), h935]
  rw [e1, e2] at h
  calc (3 * G.edgeDensity - 2) ^ 2
      ≤ 2 * (3 / (2 * Real.sqrt 2) * Real.sqrt Δ)
          + (1 / 2) * (3 / Real.sqrt 35 * Real.sqrt Δ) := h
    _ = (3 / Real.sqrt 2 + 3 / (2 * Real.sqrt 35)) * Real.sqrt Δ := by
        ring

/-! ## Stability via an abstract modulus -/

/-- **Stability through a Turán modulus** (the final implication of
`thm:k4free-p4-quant-stability`, i.e. the `r = 3` / `ω_Tur` route, with the modulus
abstracted): if edge density `≥ 2/3 - ω` guarantees the target property `close` (the
cut-distance closeness to `T₃`, supplied classically), then a sufficiently small
certificate deficit guarantees `close`.  Quantitatively: if
`(1/3)·√(2√A + (1/2)√B) ≤ ω`, then `close` holds.

(The `r ≥ 4` analogue — `thm:parametric-quant-stability` (iv), the `ω_Zyk` route through
the near-extremal `K₄` density — is formalised in `ParametricStabilityModulus.lean`
(`parametric_stability_via_modulus`), stated at the hom level in the same
modulus-abstraction pattern as this theorem; the kernel-level `R_τ⁻` correspondence is
`graphonHom_f₂_eq_RtauMinus` in `GraphonParametricTransport.lean`.) -/
theorem stability_via_modulus {A B : ℝ} (hA : G.Reta 3 ≤ A) (hB : G.Rtau 3 ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    {ω : ℝ} {close : Prop}
    (hmod : 2 / 3 - ω ≤ G.edgeDensity → close)
    (hsmall : (1 / 3) * Real.sqrt (2 * Real.sqrt A + (1 / 2) * Real.sqrt B) ≤ ω) :
    close := by
  -- `r3_edge_density_stability` gives `|p - 2/3| ≤ (1/3)√(…) ≤ ω`, hence
  -- `p ≥ 2/3 - ω` (`abs_le`), and `hmod` fires.
  have h := G.r3_edge_density_stability hA hB hA0 hB0
  have hle : |G.edgeDensity - 2 / 3| ≤ ω := le_trans h hsmall
  have habs := abs_le.mp hle
  exact hmod (by linarith [habs.1])

end Graphon

end FlagAlgebras.MetaTheory
