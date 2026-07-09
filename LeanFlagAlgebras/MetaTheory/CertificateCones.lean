import LeanFlagAlgebras.MetaTheory.DownwardAverage
import LeanFlagAlgebras.MetaTheory.VanishingIdeal
import Mathlib.Algebra.Ring.SumsOfSquares

/-! # No closed certificate gap (paper §10, `thm:no-closed-certificate-gap`)

A flag-algebra certificate reaches its empty-type conclusion through unlabelled averages
`⟦s⟧₀` of labelled non-negative terms.  The *quotient* proof system takes `s` to be a sum
of squares; an *ensemble-relaxed* proof system would allow any `s` that is non-negative
merely on the root-planting set `S_σ`.  This module shows the relaxation gains nothing
for asymptotic density bounds: the two cones of empty-type contributions have the same
closure in the `Q₀`-seminorm `‖u‖_{Q₀} = sup_{φ₀∈Q₀} |φ₀ u|`.

Formalisation choices (documented in `README.md`):
* Closeness in the `Q₀`-seminorm is stated pointwise (`Q0Within ε u v`: every constrained
  unlabelled limit evaluates `u` and `v` within `ε`) and closure membership as
  ε-approximability (`MemQ0Closure`), avoiding a seminorm-space formalisation; this is
  exactly the paper's meaning of the closure.
* The quotient cone uses sums of squares of the **ambient** algebra `A^σ[T₀]`
  (Mathlib's `IsSumSq`).  It is contained in the paper's cone (sums of squares of
  `A^σ[T₁]`), which in turn is contained in the ensemble cone, so equality of the two
  closures here *implies* the paper's statement — the sandwiched cone has the same
  closure.
* The theorem is proved for **every** type `σ`, without the paper's non-degeneracy
  hypothesis: degenerate base points evaluate all unlabelled averages to `0`
  (`downward_eval_eq_zero_of_degenerate`), so they never distinguish the cones.

Main results: `quotCone_subset_ensCone`, `ensCone_subset_closure_quotCone` (the crux,
by Stone–Weierstrass approximation of `√s`), and `no_closed_certificate_gap`.
-/

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## The `Q₀`-seminorm, as ε-closeness of evaluations -/

/-- `u` and `v` are within `ε` in the `Q₀`-seminorm: every constrained unlabelled limit
evaluates them within `ε`. -/
def Q0Within (forb0 : FinFlag ∅ₜ → Prop) (ε : ℝ) (u v : FlagAlgebra ∅ₜ) : Prop :=
  ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ forb0 → |φ₀ u - φ₀ v| ≤ ε

/-- Membership in the `Q₀`-seminorm closure of a set of empty-type elements:
`u` is approximated within every `ε > 0` by a member of `C`. -/
def MemQ0Closure (forb0 : FinFlag ∅ₜ → Prop) (C : Set (FlagAlgebra ∅ₜ))
    (u : FlagAlgebra ∅ₜ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v ∈ C, Q0Within forb0 ε u v

/-! ## The two certificate cones -/

/-- The quotient certificate cone `C^quot_σ`: unlabelled averages of sums of squares. -/
def quotCone (σ : FlagType (Fin n₀)) : Set (FlagAlgebra ∅ₜ) :=
  {u | ∃ s : FlagAlgebra σ, IsSumSq s ∧ u = ⟦s⟧₀}

/-- The ensemble certificate cone `C^ens_σ`: unlabelled averages of elements that are
non-negative on the root-planting set `S_σ`. -/
def ensCone (T : Constraint σ) : Set (FlagAlgebra ∅ₜ) :=
  {u | ∃ s : FlagAlgebra σ, (∀ χ ∈ Sσ T, 0 ≤ (PositiveHomSpace.toPosHom χ) s) ∧ u = ⟦s⟧₀}

/-- A sum of squares evaluates non-negatively at every positive homomorphism. -/
lemma isSumSq_posHom_nonneg {s : FlagAlgebra σ} (hs : IsSumSq s) (φ : PositiveHom σ) :
    0 ≤ φ s := by
  -- induction on `hs`: `φ 0 = 0`, and
  -- `φ (a*a + t) = (φ a) * (φ a) + φ t ≥ 0` by `PositiveHom.map_add`/`map_mul`.
  induction hs with
  | zero => exact le_of_eq (PositiveHom.map_zero φ).symm
  | sq_add a hs ih =>
    rw [PositiveHom.map_add, PositiveHom.map_mul]
    exact add_nonneg (mul_self_nonneg (φ a)) ih

/-- The quotient cone is contained in the ensemble cone (a sum of squares is non-negative
everywhere, in particular on `S_σ`). -/
lemma quotCone_subset_ensCone (T : Constraint σ) : quotCone σ ⊆ ensCone T := by
  rintro u ⟨s, hs, rfl⟩
  exact ⟨s, fun χ _ => isSumSq_posHom_nonneg hs _, rfl⟩

/-! ## The crux: ensemble terms are `Q₀`-approximated by squares -/

/-- **The ensemble cone lies in the `Q₀`-closure of the quotient cone** (the substantive
inclusion of `thm:no-closed-certificate-gap`).

Proof route (paper §10): let `u = ⟦s⟧₀` with `s ≥ 0` on `S_σ` and let `ε > 0`.
* Bound the evaluation: `B := ‖mkOfCompact (evalContinuousMap s)‖` satisfies
  `|χ s| ≤ B` for all `χ` (`BoundedContinuousFunction.norm_coe_le_norm`), and `0 ≤ B`.
* The function `H χ := √(max (χ s) 0)` is continuous
  (`Real.continuous_sqrt`, `Continuous.max`, `continuous_eval`), and `|H χ| ≤ √B`.
* Stone–Weierstrass (`exists_flag_near`) gives `q₀ ∈ A^σ` with `|χ q₀ - H χ| < δ` for
  all `χ`, where `δ := min 1 (ε / (2 * √B + 1)) > 0`.
* Set `q := q₀ * q₀`, a sum of squares (`IsSumSq.mul_self`).  For `χ ∈ S_σ`,
  `χ s ≥ 0` gives `H χ * H χ = χ s` (`Real.mul_self_sqrt`), so
  `|χ s - χ q| = |H χ - χ q₀| · |H χ + χ q₀| ≤ δ · (2√B + δ) ≤ δ · (2√B + 1) ≤ ε`
  (using `δ ≤ 1` and `PositiveHom.map_mul`).
* The master bound `abs_downward_eval_le_of_abs_le_on_Sσ` applied to `s - q` (with
  `downward_sub`, `PositiveHom.map_sub`) gives `|φ₀ ⟦s⟧₀ - φ₀ ⟦q⟧₀| ≤ ε` on `Q₀`. -/
theorem ensCone_subset_closure_quotCone (T : Constraint σ) {u : FlagAlgebra ∅ₜ}
    (hu : u ∈ ensCone T) : MemQ0Closure T.forb0 (quotCone σ) u := by
  obtain ⟨s, hs, rfl⟩ := hu
  intro ε hε
  -- a uniform bound `B` on all evaluations of `s`
  obtain ⟨B, hBnn, hb⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ χ : PositiveHomSpace σ, |(PositiveHomSpace.toPosHom χ) s| ≤ B := by
    refine ⟨‖evalContinuousMap s‖, norm_nonneg _, fun χ => ?_⟩
    have h := (evalContinuousMap s).norm_coe_le_norm χ
    rwa [Real.norm_eq_abs, evalContinuousMap_apply] at h
  -- the continuous function `H χ = √(max (χ s) 0)`, equal to `√(χ s)` on `S_σ`
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
  -- pointwise bound `|χ s - χ (q₀ * q₀)| ≤ ε` on `S_σ`
  have key : ∀ χ ∈ Sσ T, |(PositiveHomSpace.toPosHom χ) (s - q₀ * q₀)| ≤ ε := by
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
    have hdiffb : |H χ - (PositiveHomSpace.toPosHom χ) q₀| ≤ ε / (2 * Real.sqrt B + 1) := by
      rw [abs_sub_comm]
      exact (hq₀ χ).le.trans hδε
    calc |H χ + (PositiveHomSpace.toPosHom χ) q₀| * |H χ - (PositiveHomSpace.toPosHom χ) q₀|
        ≤ (2 * Real.sqrt B + 1) * (ε / (2 * Real.sqrt B + 1)) :=
          mul_le_mul hsum hdiffb (abs_nonneg _) hden.le
      _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hden)]
  -- push the bound through the unlabelled average via the master bound
  have hmaster := abs_downward_eval_le_of_abs_le_on_Sσ T hε.le key hφ₀
  rw [downward_sub, PositiveHom.map_sub] at hmaster
  exact hmaster

/-! ## The closed-cone equality -/

/-- **`thm:no-closed-certificate-gap`**: the quotient and ensemble certificate cones have
the same closure in the `Q₀`-seminorm.  Allowing labelled terms that are non-negative
merely on `S_σ` does not enlarge the closed cone of empty-type certificate contributions,
for any hereditary constraint and any type. -/
theorem no_closed_certificate_gap (T : Constraint σ) (u : FlagAlgebra ∅ₜ) :
    MemQ0Closure T.forb0 (quotCone σ) u ↔ MemQ0Closure T.forb0 (ensCone T) u := by
  constructor
  · -- monotonicity along `quotCone ⊆ ensCone`
    intro h ε hε
    obtain ⟨v, hv, hvw⟩ := h ε hε
    exact ⟨v, quotCone_subset_ensCone T hv, hvw⟩
  · -- ε/2 for the ensemble approximant, ε/2 for its quotient approximant, triangle
    intro h ε hε
    obtain ⟨v, hvEns, hv⟩ := h (ε / 2) (by positivity)
    obtain ⟨w, hwQuot, hw⟩ := ensCone_subset_closure_quotCone T hvEns (ε / 2) (by positivity)
    refine ⟨w, hwQuot, fun φ₀ hφ₀ => ?_⟩
    have h1 := hv φ₀ hφ₀
    have h2 := hw φ₀ hφ₀
    have h3 := abs_sub_le (φ₀ u) (φ₀ v) (φ₀ w)
    linarith only [h1, h2, h3]

/-- **`prop:ideal-zero`, final clause** (contrapositive form): if every element that is
non-negative on `S_σ` agrees *on `S_σ`* with some sum of squares, then the ensemble
relaxation adds nothing even at the exact (pre-closure) level — every ensemble-cone
member has the same `Q₀`-evaluation as a quotient-cone member.  Hence a strict exact
inclusion `C^ens ⊋ C^quot` requires a *Positivstellensatz gap on the support variety*:
an `s ≥ 0` on `S_σ` whose restriction to `S_σ` is matched by no sum of squares. -/
theorem ensCone_eval_eq_quotCone_of_sos_agreement (T : Constraint σ)
    (hsos : ∀ s : FlagAlgebra σ, (∀ χ ∈ Sσ T, 0 ≤ (PositiveHomSpace.toPosHom χ) s) →
      ∃ q : FlagAlgebra σ, IsSumSq q ∧
        ∀ χ ∈ Sσ T, (PositiveHomSpace.toPosHom χ) s = (PositiveHomSpace.toPosHom χ) q)
    {u : FlagAlgebra ∅ₜ} (hu : u ∈ ensCone T) :
    ∃ v ∈ quotCone σ, ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ T.forb0 →
      φ₀ u = φ₀ v := by
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨q, hq, hagree⟩ := hsos s hs
  exact ⟨⟦q⟧₀, ⟨q, hq, rfl⟩,
    fun φ₀ hφ₀ => downward_eval_congr_of_eqOn_Sσ T hagree hφ₀⟩

end FlagAlgebras.MetaTheory
