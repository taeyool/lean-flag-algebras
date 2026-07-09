import LeanFlagAlgebras.MetaTheory.CertificateCones
import LeanFlagAlgebras.MetaTheory.RelativeSupport

/-! # No closed certificate gap over a slice (paper §11.4, `thm:relative-certificate-gap`)

Relativisation of §10's `thm:no-closed-certificate-gap` to an arbitrary constraint set `Y`:
measuring empty-type contributions by the `Y`-seminorm `‖u‖_Y = sup_{φ₀∈Y} |φ₀ u|` (in the
same ε-form as §10's `Q0Within`), the quotient cone of averaged sums of squares and the
relative ensemble cone (averages of elements non-negative on `S_σ(Y)`) have the same
`‖·‖_Y`-closure.  Even over a slice, labelled terms non-negative merely on the relative
support prove no density consequence beyond averaged sums of squares, except possibly at the
exact finite-certificate level.

* `YWithin` / `MemYClosure` — the `Y`-seminorm ε-closeness and closure membership
  (`Q0Within`/`MemQ0Closure` with `Qσ forb0` replaced by `Y`);
* `relEnsCone` — the relative ensemble cone `C^ens_σ(Y)`;
* `abs_downward_eval_le_of_abs_le_on_relSσ` — the relative master evaluation bound;
* `relEnsCone_subset_closure_quotCone` — the Stone–Weierstrass crux (including the
  `S_σ(Y) = ∅` degenerate branch, where every average is `Y`-null);
* `no_relative_closed_certificate_gap` — the closure equality.
-/

open MeasureTheory
open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## The `Y`-seminorm closure -/

/-- `Y`-seminorm ε-closeness: `|φ₀ u - φ₀ v| ≤ ε` for every base limit in `Y`
(the relative analogue of `Q0Within`). -/
def YWithin (Y : Set (PositiveHomSpace ∅ₜ)) (ε : ℝ) (u v : FlagAlgebra ∅ₜ) : Prop :=
  ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → |φ₀ u - φ₀ v| ≤ ε

/-- Membership in the `‖·‖_Y`-closure of a set of empty-type elements. -/
def MemYClosure (Y : Set (PositiveHomSpace ∅ₜ)) (C : Set (FlagAlgebra ∅ₜ))
    (u : FlagAlgebra ∅ₜ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v ∈ C, YWithin Y ε u v

/-! ## The relative ensemble cone -/

/-- The relative ensemble certificate cone `C^ens_σ(Y)`: unlabelled averages of elements
non-negative on the relative support `S_σ(Y)`. -/
def relEnsCone (Y : Set (PositiveHomSpace ∅ₜ)) (σ : FlagType (Fin n₀)) :
    Set (FlagAlgebra ∅ₜ) :=
  {u | ∃ s : FlagAlgebra σ, (∀ χ ∈ relSσ Y σ, 0 ≤ (PositiveHomSpace.toPosHom χ) s) ∧ u = ⟦s⟧₀}

/-- Squares are non-negative everywhere, so the quotient cone sits inside the relative
ensemble cone (for every `Y`). -/
theorem quotCone_subset_relEnsCone (Y : Set (PositiveHomSpace ∅ₜ)) :
    quotCone σ ⊆ relEnsCone Y σ := by
  -- Mirror `quotCone_subset_ensCone` (CertificateCones): a sum of squares evaluates
  -- non-negatively at every positive homomorphism (`isSumSq_posHom_nonneg`), a fortiori on
  -- `relSσ Y σ`.
  rintro u ⟨s, hs, rfl⟩
  exact ⟨s, fun χ _ => isSumSq_posHom_nonneg hs _, rfl⟩

/-! ## The relative master evaluation bound -/

/-- `φ₀ ⟨σ⟩₀ ≥ 0`: the type flag is a single basis flag, so its value is non-negative
(private mirror of the helper in `DownwardAverage.lean`). -/
private lemma type_eval_nonneg (φ₀ : PositiveHom ∅ₜ) : 0 ≤ φ₀ ⟨σ⟩₀ :=
  positiveHom_basisVector_ge_zero φ₀ ⟨n₀, σ.toEmptyTypeFlag⟩

/-- **Relative master evaluation bound**: if `|s| ≤ δ` on `S_σ(Y)`, then `|φ₀ ⟦s⟧₀| ≤ δ`
for every `φ₀ ∈ Y` (mirror of `abs_downward_eval_le_of_abs_le_on_Sσ` with
`support_subset_relSσ` in place of `support_subset_Sσ`). -/
theorem abs_downward_eval_le_of_abs_le_on_relSσ {Y : Set (PositiveHomSpace ∅ₜ)}
    {s : FlagAlgebra σ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ χ ∈ relSσ Y σ, |(PositiveHomSpace.toPosHom χ) s| ≤ δ)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) :
    |φ₀ (⟦s⟧₀ : FlagAlgebra ∅ₜ)| ≤ δ := by
  -- Copy `abs_downward_eval_le_of_abs_le_on_Sσ` (DownwardAverage) verbatim, replacing the
  -- absolute support containment with `support_subset_relSσ hφ₀ hσ` (RelativeSupport); the
  -- degenerate branch is unchanged (`downward_eval_eq_zero_of_degenerate`).
  rcases eq_or_lt_of_le (type_eval_nonneg (σ := σ) φ₀) with hσ0 | hσpos
  · -- degenerate base limit: the average vanishes
    rw [downward_eval_eq_zero_of_degenerate hσ0.symm s, abs_zero]
    exact hδ
  · -- non-degenerate: evaluate through the random extension
    have hσ : φ₀ ⟨σ⟩₀ > 0 := hσpos
    have h1pos : φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) > 0 :=
      positiveHom_one_downward_pos hσ
    have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ s
    rw [eq_div_iff (ne_of_gt h1pos)] at hspec
    have hint : |∫ (χ : PositiveHomSpace σ), (PositiveHomSpace.toPosHom χ) s
        ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ))| ≤ δ := by
      have hae : ∀ᵐ (χ : PositiveHomSpace σ) ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
          ‖(PositiveHomSpace.toPosHom χ) s‖ ≤ δ := by
        filter_upwards [Measure.support_mem_ae] with χ hχ
        rw [Real.norm_eq_abs]
        exact hs χ (support_subset_relSσ hφ₀ hσ hχ)
      have h := norm_integral_le_of_norm_le_const hae
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
      exact h
    have habs1 : |φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ)| ≤ 1 := by
      rw [abs_of_nonneg (posHom_one_downward_nonneg φ₀)]
      exact posHom_one_downward_le_one φ₀
    rw [← hspec, abs_mul]
    have hfin := mul_le_mul hint habs1 (abs_nonneg _) hδ
    rw [mul_one] at hfin
    exact hfin

/-! ## The crux: relative ensemble averages are `Y`-approximable by quotient averages -/

/-- **Stone–Weierstrass crux over a slice**: every relative-ensemble-cone element lies in
the `‖·‖_Y`-closure of the quotient cone. -/
theorem relEnsCone_subset_closure_quotCone {Y : Set (PositiveHomSpace ∅ₜ)}
    {u : FlagAlgebra ∅ₜ} (hu : u ∈ relEnsCone Y σ) :
    MemYClosure Y (quotCone σ) u := by
  -- Two branches, following the paper:
  -- * `relSσ Y σ = ∅`: then no `φ₀ ∈ Y` has `φ₀ ⟨σ⟩₀ > 0` (a positive type density would
  --   give the probability measure `ℙ[φ₀]` a nonempty support inside `relSσ` — a probability
  --   measure on a compact metric space has nonempty support since the complement is null:
  --   `Measure.measure_compl_support` + `measure_univ`); hence every `φ₀ ∈ Y` is degenerate
  --   and `φ₀ ⟦s⟧₀ = 0 = φ₀ ⟦0⟧₀` (`downward_eval_eq_zero_of_degenerate`).  Approximate by
  --   `⟦0⟧₀ ∈ quotCone` (`IsSumSq.zero`, `downward` of `0`; `|0 - 0| ≤ ε`).
  -- * otherwise: mirror `ensCone_subset_closure_quotCone` (CertificateCones lines 95–165)
  --   with `Sσ T → relSσ Y σ` and the final expectation bound via
  --   `abs_downward_eval_le_of_abs_le_on_relSσ` — Stone–Weierstrass (`exists_flag_near`)
  --   approximates `√(max(χ s, 0))` uniformly on the COMPACT `X_σ` (the §10 proof already
  --   works with a global approximant, so the same script applies; only the final
  --   `Q0Within`-style bound switches to the `Y`-quantifier).
  obtain ⟨s, hs, rfl⟩ := hu
  intro ε hε
  rcases (relSσ Y σ).eq_empty_or_nonempty with hS | -
  · -- degenerate branch: every base limit in `Y` kills every average
    refine ⟨⟦(0 : FlagAlgebra σ)⟧₀, ⟨0, IsSumSq.zero, rfl⟩, fun φ₀ hφ₀ => ?_⟩
    have hdeg : φ₀ ⟨σ⟩₀ = 0 := by
      by_contra hne
      have hσ : φ₀ ⟨σ⟩₀ > 0 := lt_of_le_of_ne (type_eval_nonneg (σ := σ) φ₀) (Ne.symm hne)
      have hsub := support_subset_relSσ (σ := σ) hφ₀ hσ
      rw [hS, Set.subset_empty_iff] at hsub
      have hcompl := Measure.measure_compl_support
        (μ := (ℙ[φ₀] : Measure (PositiveHomSpace σ)))
      rw [hsub, Set.compl_empty, measure_univ] at hcompl
      exact one_ne_zero hcompl
    rw [downward_eval_eq_zero_of_degenerate hdeg s,
      downward_eval_eq_zero_of_degenerate hdeg (0 : FlagAlgebra σ), sub_zero, abs_zero]
    exact hε.le
  · -- main branch: transcribe `ensCone_subset_closure_quotCone` with `Sσ T → relSσ Y σ`
    -- a uniform bound `B` on all evaluations of `s`
    obtain ⟨B, hBnn, hb⟩ : ∃ B : ℝ, 0 ≤ B ∧
        ∀ χ : PositiveHomSpace σ, |(PositiveHomSpace.toPosHom χ) s| ≤ B := by
      refine ⟨‖evalContinuousMap s‖, norm_nonneg _, fun χ => ?_⟩
      have h := (evalContinuousMap s).norm_coe_le_norm χ
      rwa [Real.norm_eq_abs, evalContinuousMap_apply] at h
    -- the continuous function `H χ = √(max (χ s) 0)`, equal to `√(χ s)` on `relSσ Y σ`
    obtain ⟨H, hHcont, hHnn, hHle, hHsq⟩ : ∃ H : PositiveHomSpace σ → ℝ, Continuous H ∧
        (∀ χ, 0 ≤ H χ) ∧ (∀ χ, H χ ≤ Real.sqrt B) ∧
        ∀ χ, 0 ≤ (PositiveHomSpace.toPosHom χ) s →
          H χ * H χ = (PositiveHomSpace.toPosHom χ) s := by
      refine ⟨fun χ => Real.sqrt (max ((PositiveHomSpace.toPosHom χ) s) 0),
        ((continuous_eval s).max continuous_const).sqrt,
        fun χ => Real.sqrt_nonneg _, fun χ => ?_, fun χ hχ => ?_⟩
      · exact Real.sqrt_le_sqrt (max_le ((le_abs_self _).trans (hb χ)) hBnn)
      · dsimp only
        rw [max_eq_left hχ]
        exact Real.mul_self_sqrt hχ
    -- the approximation accuracy `δ`
    have hden : (0 : ℝ) < 2 * Real.sqrt B + 1 := by positivity
    obtain ⟨δ, hδpos, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ ε / (2 * Real.sqrt B + 1) :=
      ⟨min 1 (ε / (2 * Real.sqrt B + 1)), lt_min one_pos (div_pos hε hden),
        min_le_left _ _, min_le_right _ _⟩
    -- Stone–Weierstrass: approximate `H` uniformly within `δ` by a flag-algebra element
    obtain ⟨q₀, hq₀⟩ := exists_flag_near H hHcont hδpos
    refine ⟨⟦q₀ * q₀⟧₀, ⟨q₀ * q₀, IsSumSq.mul_self q₀, rfl⟩, ?_⟩
    intro φ₀ hφ₀
    -- pointwise bound `|χ s - χ (q₀ * q₀)| ≤ ε` on `relSσ Y σ`
    have key : ∀ χ ∈ relSσ Y σ, |(PositiveHomSpace.toPosHom χ) (s - q₀ * q₀)| ≤ ε := by
      intro χ hχ
      have hsχ : 0 ≤ (PositiveHomSpace.toPosHom χ) s := hs χ hχ
      have hHabs : |H χ| ≤ Real.sqrt B := by
        rw [abs_of_nonneg (hHnn χ)]
        exact hHle χ
      have habs_q : |(PositiveHomSpace.toPosHom χ) q₀| ≤ δ + Real.sqrt B :=
        calc |(PositiveHomSpace.toPosHom χ) q₀|
            = |((PositiveHomSpace.toPosHom χ) q₀ - H χ) + H χ| := by congr 1; ring
          _ ≤ |(PositiveHomSpace.toPosHom χ) q₀ - H χ| + |H χ| := abs_add_le _ _
          _ ≤ δ + Real.sqrt B := add_le_add (hq₀ χ).le hHabs
      have hrw : (PositiveHomSpace.toPosHom χ) (s - q₀ * q₀)
          = (H χ + (PositiveHomSpace.toPosHom χ) q₀)
            * (H χ - (PositiveHomSpace.toPosHom χ) q₀) := by
        rw [PositiveHom.map_sub, PositiveHom.map_mul, ← hHsq χ hsχ, mul_self_sub_mul_self]
      rw [hrw, abs_mul]
      have hsum : |H χ + (PositiveHomSpace.toPosHom χ) q₀| ≤ 2 * Real.sqrt B + 1 :=
        calc |H χ + (PositiveHomSpace.toPosHom χ) q₀|
            ≤ |H χ| + |(PositiveHomSpace.toPosHom χ) q₀| := abs_add_le _ _
          _ ≤ Real.sqrt B + (δ + Real.sqrt B) := add_le_add hHabs habs_q
          _ ≤ 2 * Real.sqrt B + 1 := by linarith only [hδ1]
      have hdiffb : |H χ - (PositiveHomSpace.toPosHom χ) q₀|
          ≤ ε / (2 * Real.sqrt B + 1) := by
        rw [abs_sub_comm]
        exact (hq₀ χ).le.trans hδε
      calc |H χ + (PositiveHomSpace.toPosHom χ) q₀|
            * |H χ - (PositiveHomSpace.toPosHom χ) q₀|
          ≤ (2 * Real.sqrt B + 1) * (ε / (2 * Real.sqrt B + 1)) :=
            mul_le_mul hsum hdiffb (abs_nonneg _) hden.le
        _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hden)]
    -- push the bound through the unlabelled average via the relative master bound
    have hmaster := abs_downward_eval_le_of_abs_le_on_relSσ hε.le key hφ₀
    rw [downward_sub, PositiveHom.map_sub] at hmaster
    exact hmaster

/-! ## The closure equality -/

/-- **No closed certificate gap over a slice** (`thm:relative-certificate-gap`): the
`‖·‖_Y`-closures of the quotient cone and of the relative ensemble cone coincide, for every
`Y` and every type. -/
theorem no_relative_closed_certificate_gap (Y : Set (PositiveHomSpace ∅ₜ))
    (σ : FlagType (Fin n₀)) (u : FlagAlgebra ∅ₜ) :
    MemYClosure Y (quotCone σ) u ↔ MemYClosure Y (relEnsCone Y σ) u := by
  -- Mirror `no_closed_certificate_gap` (CertificateCones lines 166–188): monotonicity along
  -- `quotCone_subset_relEnsCone` one way; ε/2 + ε/2 triangle through
  -- `relEnsCone_subset_closure_quotCone` the other.
  constructor
  · -- monotonicity along `quotCone ⊆ relEnsCone`
    intro h ε hε
    obtain ⟨v, hv, hvw⟩ := h ε hε
    exact ⟨v, quotCone_subset_relEnsCone Y hv, hvw⟩
  · -- ε/2 for the relative ensemble approximant, ε/2 for its quotient approximant, triangle
    intro h ε hε
    obtain ⟨v, hvEns, hv⟩ := h (ε / 2) (by positivity)
    obtain ⟨w, hwQuot, hw⟩ := relEnsCone_subset_closure_quotCone hvEns (ε / 2) (by positivity)
    refine ⟨w, hwQuot, fun φ₀ hφ₀ => ?_⟩
    have h1 := hv φ₀ hφ₀
    have h2 := hw φ₀ hφ₀
    have h3 := abs_sub_le (φ₀ u) (φ₀ v) (φ₀ w)
    linarith only [h1, h2, h3]

end FlagAlgebras.MetaTheory
