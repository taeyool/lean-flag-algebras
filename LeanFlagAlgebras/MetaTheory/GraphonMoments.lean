import LeanFlagAlgebras.MetaTheory.GraphonBasic

/-! # Moment identities from the local slice equations (paper §11.7
`thm:parametric-moments`, §11.8 `thm:approximate-moments`)

For a graphon `W` define the local errors of the two mined slice equations

  `ℓ_η(x,y) = (r-1)(1 - d(x) - d(y) + c(x,y)) - c(x,y)`  (the non-edge equation)
  `ℓ_τ(x,y) = (r-2)(d(x) + d(y) - 2c(x,y)) - 2c(x,y)`    (the edge equation)

and their square averages `R_η = ∫∫ (1-W)·ℓ_η²`, `R_τ = ∫∫ W·ℓ_τ²`.  The **approximate
moment theorem** (`thm:approximate-moments`, certificate-free, valid for EVERY graphon)
bounds the deviation of the moment identity by `(r-1)√R_η + ((r-2)/2)√R_τ`; the **exact
moment identities** (`thm:parametric-moments`) are the `R_η = R_τ = 0` instance:

* (i) `(r-1)T = (r-2)D`;
* (ii) `r(2r-3)D = (r-1)²(3p-1)`;
* (iii) `D - p² = (α⁺-p)(p-α⁻)` where `α⁻ = (r-1)/(2r-3)`, `α⁺ = (r-1)/r`;
* (iv) `α⁻ ≤ p ≤ α⁺`, with degree-regularity exactly at the endpoints.

The a.e. form of the hypotheses ("the equation holds for `W`-almost every pair") is
equivalent to `R = 0` (`Rtau_eq_zero_iff_ae`, `Reta_eq_zero_iff_ae`), matching the paper's
phrasing.
-/

open MeasureTheory unitInterval

namespace FlagAlgebras.MetaTheory

namespace Graphon

variable (G : Graphon)

/-! ## The local errors and their square averages -/

/-- The non-edge local error `ℓ_η`. -/
noncomputable def ellEta (r : ℕ) (x y : I) : ℝ :=
  ((r : ℝ) - 1) * (1 - G.deg x - G.deg y + G.codeg x y) - G.codeg x y

/-- The edge local error `ℓ_τ`. -/
noncomputable def ellTau (r : ℕ) (x y : I) : ℝ :=
  ((r : ℝ) - 2) * (G.deg x + G.deg y - 2 * G.codeg x y) - 2 * G.codeg x y

/-- The non-edge square error `R_η = ∫∫ (1-W)·ℓ_η²`. -/
noncomputable def Reta (r : ℕ) : ℝ :=
  ∫ z : I × I, (1 - G.W z.1 z.2) * (G.ellEta r z.1 z.2) ^ 2

/-- The edge square error `R_τ = ∫∫ W·ℓ_τ²`. -/
noncomputable def Rtau (r : ℕ) : ℝ :=
  ∫ z : I × I, G.W z.1 z.2 * (G.ellTau r z.1 z.2) ^ 2

/-- The two Turán endpoints `α_r^- = (r-1)/(2r-3)` and `α_r^+ = (r-1)/r`. -/
noncomputable def alphaMinus (r : ℕ) : ℝ := ((r : ℝ) - 1) / (2 * r - 3)

/-- See `alphaMinus`. -/
noncomputable def alphaPlus (r : ℕ) : ℝ := ((r : ℝ) - 1) / r

/-! ## Private infrastructure: integrability, measurability, boundedness

Everything in sight is a bounded measurable function on the probability space `I` or
`I × I`, so integrability is automatic.  `GraphonBasic`'s helper is `private`, so we keep a
local copy. -/

/-- Local copy of `GraphonBasic`'s (private) bounded-measurable integrability helper. -/
private lemma integrable_of_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

private lemma measurable_ellEta (r : ℕ) :
    Measurable fun z : I × I => G.ellEta r z.1 z.2 := by
  simp only [ellEta]
  exact (measurable_const.mul
    (((measurable_const.sub (G.measurable_deg.comp measurable_fst)).sub
      (G.measurable_deg.comp measurable_snd)).add G.measurable_codeg)).sub G.measurable_codeg

private lemma measurable_ellTau (r : ℕ) :
    Measurable fun z : I × I => G.ellTau r z.1 z.2 := by
  simp only [ellTau]
  exact (measurable_const.mul
    (((G.measurable_deg.comp measurable_fst).add (G.measurable_deg.comp measurable_snd)).sub
      (measurable_const.mul G.measurable_codeg))).sub (measurable_const.mul G.measurable_codeg)

/-- Crude uniform bound `|ℓ_η| ≤ 2r + 4` from `d, c ∈ [0,1]`. -/
private lemma abs_ellEta_le (r : ℕ) (x y : I) : |G.ellEta r x y| ≤ 2 * (r : ℝ) + 4 := by
  have h1 := G.deg_nonneg x; have h2 := G.deg_le_one x
  have h3 := G.deg_nonneg y; have h4 := G.deg_le_one y
  have h5 := G.codeg_nonneg x y; have h6 := G.codeg_le_one x y
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  simp only [ellEta]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_of_le_one_right hr0 h2, mul_le_of_le_one_right hr0 h4,
      mul_le_of_le_one_right hr0 h6, mul_nonneg hr0 h1, mul_nonneg hr0 h3,
      mul_nonneg hr0 h5]
  · nlinarith [mul_le_of_le_one_right hr0 h2, mul_le_of_le_one_right hr0 h4,
      mul_le_of_le_one_right hr0 h6, mul_nonneg hr0 h1, mul_nonneg hr0 h3,
      mul_nonneg hr0 h5]

/-- Crude uniform bound `|ℓ_τ| ≤ 2r + 4` from `d, c ∈ [0,1]`. -/
private lemma abs_ellTau_le (r : ℕ) (x y : I) : |G.ellTau r x y| ≤ 2 * (r : ℝ) + 4 := by
  have h1 := G.deg_nonneg x; have h2 := G.deg_le_one x
  have h3 := G.deg_nonneg y; have h4 := G.deg_le_one y
  have h5 := G.codeg_nonneg x y; have h6 := G.codeg_le_one x y
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  simp only [ellTau]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_of_le_one_right hr0 h2, mul_le_of_le_one_right hr0 h4,
      mul_le_of_le_one_right hr0 h6, mul_nonneg hr0 h1, mul_nonneg hr0 h3,
      mul_nonneg hr0 h5]
  · nlinarith [mul_le_of_le_one_right hr0 h2, mul_le_of_le_one_right hr0 h4,
      mul_le_of_le_one_right hr0 h6, mul_nonneg hr0 h1, mul_nonneg hr0 h3,
      mul_nonneg hr0 h5]

private lemma integrable_W : Integrable fun z : I × I => G.W z.1 z.2 :=
  integrable_of_bounds G.measurable (fun z => G.nonneg z.1 z.2) (fun z => G.le_one z.1 z.2)

private lemma integrable_codeg : Integrable fun z : I × I => G.codeg z.1 z.2 :=
  integrable_of_bounds G.measurable_codeg (fun z => G.codeg_nonneg z.1 z.2)
    (fun z => G.codeg_le_one z.1 z.2)

private lemma integrable_deg_fst : Integrable fun z : I × I => G.deg z.1 :=
  integrable_of_bounds (G.measurable_deg.comp measurable_fst)
    (fun z => G.deg_nonneg z.1) (fun z => G.deg_le_one z.1)

private lemma integrable_deg_snd : Integrable fun z : I × I => G.deg z.2 :=
  integrable_of_bounds (G.measurable_deg.comp measurable_snd)
    (fun z => G.deg_nonneg z.2) (fun z => G.deg_le_one z.2)

private lemma integrable_W_deg_fst : Integrable fun z : I × I => G.W z.1 z.2 * G.deg z.1 :=
  integrable_of_bounds (G.measurable.mul (G.measurable_deg.comp measurable_fst))
    (fun z => mul_nonneg (G.nonneg z.1 z.2) (G.deg_nonneg z.1))
    (fun z => mul_le_one₀ (G.le_one z.1 z.2) (G.deg_nonneg z.1) (G.deg_le_one z.1))

private lemma integrable_W_deg_snd : Integrable fun z : I × I => G.W z.1 z.2 * G.deg z.2 :=
  integrable_of_bounds (G.measurable.mul (G.measurable_deg.comp measurable_snd))
    (fun z => mul_nonneg (G.nonneg z.1 z.2) (G.deg_nonneg z.2))
    (fun z => mul_le_one₀ (G.le_one z.1 z.2) (G.deg_nonneg z.2) (G.deg_le_one z.2))

private lemma integrable_W_codeg :
    Integrable fun z : I × I => G.W z.1 z.2 * G.codeg z.1 z.2 :=
  integrable_of_bounds (G.measurable.mul G.measurable_codeg)
    (fun z => mul_nonneg (G.nonneg z.1 z.2) (G.codeg_nonneg z.1 z.2))
    (fun z => mul_le_one₀ (G.le_one z.1 z.2) (G.codeg_nonneg z.1 z.2)
      (G.codeg_le_one z.1 z.2))

private lemma integrable_oneSubW : Integrable fun z : I × I => 1 - G.W z.1 z.2 :=
  integrable_of_bounds (b := 1) (measurable_const.sub G.measurable)
    (fun z => sub_nonneg.mpr (G.le_one z.1 z.2))
    (fun z => by linarith [G.nonneg z.1 z.2])

private lemma integrable_oneSubW_deg_fst :
    Integrable fun z : I × I => (1 - G.W z.1 z.2) * G.deg z.1 :=
  integrable_of_bounds ((measurable_const.sub G.measurable).mul
      (G.measurable_deg.comp measurable_fst))
    (fun z => mul_nonneg (sub_nonneg.mpr (G.le_one z.1 z.2)) (G.deg_nonneg z.1))
    (fun z => mul_le_one₀ (by linarith [G.nonneg z.1 z.2]) (G.deg_nonneg z.1)
      (G.deg_le_one z.1))

private lemma integrable_oneSubW_deg_snd :
    Integrable fun z : I × I => (1 - G.W z.1 z.2) * G.deg z.2 :=
  integrable_of_bounds ((measurable_const.sub G.measurable).mul
      (G.measurable_deg.comp measurable_snd))
    (fun z => mul_nonneg (sub_nonneg.mpr (G.le_one z.1 z.2)) (G.deg_nonneg z.2))
    (fun z => mul_le_one₀ (by linarith [G.nonneg z.1 z.2]) (G.deg_nonneg z.2)
      (G.deg_le_one z.2))

private lemma integrable_oneSubW_codeg :
    Integrable fun z : I × I => (1 - G.W z.1 z.2) * G.codeg z.1 z.2 :=
  integrable_of_bounds ((measurable_const.sub G.measurable).mul G.measurable_codeg)
    (fun z => mul_nonneg (sub_nonneg.mpr (G.le_one z.1 z.2)) (G.codeg_nonneg z.1 z.2))
    (fun z => mul_le_one₀ (by linarith [G.nonneg z.1 z.2]) (G.codeg_nonneg z.1 z.2)
      (G.codeg_le_one z.1 z.2))

/-! ## Private Fubini primitives -/

/-- `∫∫ d(x) d(x,y) = p` (the second variable integrates to `1`). -/
private lemma integral_deg_fst : (∫ z : I × I, G.deg z.1) = G.edgeDensity := by
  have hint : Integrable (fun z : I × I => G.deg z.1) ((volume : Measure I).prod volume) :=
    integrable_of_bounds (G.measurable_deg.comp measurable_fst)
      (fun z => G.deg_nonneg z.1) (fun z => G.deg_le_one z.1)
  have h : (∫ z : I × I, G.deg z.1) = ∫ x, ∫ _ : I, G.deg x := by
    rw [Measure.volume_eq_prod]
    exact integral_prod _ hint
  rw [h]
  calc (∫ x, ∫ _ : I, G.deg x) = ∫ x, G.deg x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
    _ = G.edgeDensity := rfl

/-- `∫∫ d(y) d(x,y) = p` (the first variable integrates to `1`). -/
private lemma integral_deg_snd : (∫ z : I × I, G.deg z.2) = G.edgeDensity := by
  have hint : Integrable (fun z : I × I => G.deg z.2) ((volume : Measure I).prod volume) :=
    integrable_of_bounds (G.measurable_deg.comp measurable_snd)
      (fun z => G.deg_nonneg z.2) (fun z => G.deg_le_one z.2)
  have h : (∫ z : I × I, G.deg z.2) = ∫ _ : I, ∫ y, G.deg y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod _ hint
  have h2 : (∫ _ : I, ∫ y, G.deg y) = ∫ _ : I, G.edgeDensity := rfl
  rw [h, h2]
  simp

/-- `∫∫ (1 - W) = 1 - p`. -/
private lemma integral_oneSubW : (∫ z : I × I, (1 - G.W z.1 z.2)) = 1 - G.edgeDensity := by
  rw [integral_sub (integrable_const 1) G.integrable_W, G.edgeDensity_eq_integral_prod]
  simp

/-- `∫∫ (1 - W)·d(x) = p - D`. -/
private lemma integral_oneSubW_mul_deg_fst :
    (∫ z : I × I, (1 - G.W z.1 z.2) * G.deg z.1) = G.edgeDensity - G.degSq := by
  have e : (fun z : I × I => (1 - G.W z.1 z.2) * G.deg z.1)
      = fun z => G.deg z.1 - G.W z.1 z.2 * G.deg z.1 := by
    funext z; ring
  rw [e, integral_sub G.integrable_deg_fst G.integrable_W_deg_fst, G.integral_deg_fst,
    G.integral_W_mul_deg_left]

/-- `∫∫ (1 - W)·d(y) = p - D`. -/
private lemma integral_oneSubW_mul_deg_snd :
    (∫ z : I × I, (1 - G.W z.1 z.2) * G.deg z.2) = G.edgeDensity - G.degSq := by
  have e : (fun z : I × I => (1 - G.W z.1 z.2) * G.deg z.2)
      = fun z => G.deg z.2 - G.W z.1 z.2 * G.deg z.2 := by
    funext z; ring
  rw [e, integral_sub G.integrable_deg_snd G.integrable_W_deg_snd, G.integral_deg_snd,
    G.integral_W_mul_deg_right]

/-- `∫∫ (1 - W)·c = D - T`. -/
private lemma integral_oneSubW_mul_codeg :
    (∫ z : I × I, (1 - G.W z.1 z.2) * G.codeg z.1 z.2) = G.degSq - G.triDensity := by
  have e : (fun z : I × I => (1 - G.W z.1 z.2) * G.codeg z.1 z.2)
      = fun z => G.codeg z.1 z.2 - G.W z.1 z.2 * G.codeg z.1 z.2 := by
    funext z; ring
  rw [e, integral_sub G.integrable_codeg G.integrable_W_codeg, G.integral_codeg_eq_degSq]
  rfl

/-! ## The elementary integral Cauchy–Schwarz -/

/-- Cauchy–Schwarz with a `[0,1]`-valued weight, `|∫ w·ℓ| ≤ √(∫ w·ℓ²)`, via the
discriminant of the non-negative quadratic `t ↦ ∫ w·(ℓ + t)²` (the same trick as the
repo's `posSemidef_dotProduct_mulVec_sq_le`), using `∫ w ≤ 1`. -/
private lemma abs_integral_weight_mul_le {w l : I × I → ℝ} {M : ℝ}
    (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    (hl : Measurable l) (hM0 : 0 ≤ M) (hlM : ∀ z, |l z| ≤ M) :
    |∫ z : I × I, w z * l z| ≤ Real.sqrt (∫ z : I × I, w z * l z ^ 2) := by
  have hw_int : Integrable (fun z : I × I => w z) := integrable_of_bounds hw hw0 hw1
  have hwl_int : Integrable (fun z : I × I => w z * l z) := by
    refine integrable_of_bounds (a := -M) (b := M) (hw.mul hl) (fun z => ?_) (fun z => ?_)
    · have hb := abs_le.mp (hlM z)
      nlinarith [mul_le_mul_of_nonneg_left hb.1 (hw0 z), mul_le_of_le_one_left hM0 (hw1 z)]
    · have hb := abs_le.mp (hlM z)
      nlinarith [mul_le_mul_of_nonneg_left hb.2 (hw0 z), mul_le_of_le_one_left hM0 (hw1 z)]
  have hwl2_int : Integrable (fun z : I × I => w z * l z ^ 2) := by
    refine integrable_of_bounds (a := 0) (b := M ^ 2) (hw.mul (hl.pow_const 2))
      (fun z => mul_nonneg (hw0 z) (sq_nonneg _)) (fun z => ?_)
    have hb := abs_le.mp (hlM z)
    exact le_trans (mul_le_of_le_one_left (sq_nonneg _) (hw1 z)) (sq_le_sq' hb.1 hb.2)
  -- the non-negative quadratic in `t`
  have key : ∀ t : ℝ,
      0 ≤ (∫ z : I × I, w z) * (t * t) + 2 * (∫ z : I × I, w z * l z) * t
        + (∫ z : I × I, w z * l z ^ 2) := by
    intro t
    have h0 : 0 ≤ ∫ z : I × I, w z * (l z + t) ^ 2 :=
      integral_nonneg fun z => mul_nonneg (hw0 z) (sq_nonneg _)
    have e : (fun z : I × I => w z * (l z + t) ^ 2)
        = fun z => (w z * l z ^ 2 + 2 * t * (w z * l z)) + t ^ 2 * w z := by
      funext z; ring
    have hsum : Integrable (fun z : I × I => w z * l z ^ 2 + 2 * t * (w z * l z)) :=
      hwl2_int.add (hwl_int.const_mul (2 * t))
    rw [e, integral_add hsum (hw_int.const_mul (t ^ 2)),
      integral_add hwl2_int (hwl_int.const_mul (2 * t)), integral_const_mul,
      integral_const_mul] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  have hC0 : 0 ≤ ∫ z : I × I, w z * l z ^ 2 :=
    integral_nonneg fun z => mul_nonneg (hw0 z) (sq_nonneg _)
  have hA1 : (∫ z : I × I, w z) ≤ 1 := by
    have h := integral_mono hw_int (integrable_const 1) hw1
    simpa using h
  have hB2 : (∫ z : I × I, w z * l z) ^ 2 ≤ ∫ z : I × I, w z * l z ^ 2 := by
    nlinarith [hd, mul_le_mul_of_nonneg_right hA1 hC0]
  calc |∫ z : I × I, w z * l z|
      = Real.sqrt ((∫ z : I × I, w z * l z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∫ z : I × I, w z * l z ^ 2) := Real.sqrt_le_sqrt hB2

lemma Reta_nonneg (r : ℕ) : 0 ≤ G.Reta r := by
  -- integrand nonneg (`(1-W) ≥ 0` and a square); `integral_nonneg`.
  exact integral_nonneg fun z =>
    mul_nonneg (sub_nonneg.mpr (G.le_one z.1 z.2)) (sq_nonneg _)

lemma Rtau_nonneg (r : ℕ) : 0 ≤ G.Rtau r :=
  integral_nonneg fun z => mul_nonneg (G.nonneg z.1 z.2) (sq_nonneg _)

/-! ## The integrated local errors -/

/-- The integrated edge error `E_τ = ∫∫ W·ℓ_τ = 2(r-2)D - 2(r-1)T`. -/
lemma integral_W_ellTau (r : ℕ) :
    (∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2)
      = 2 * ((r : ℝ) - 2) * G.degSq - 2 * ((r : ℝ) - 1) * G.triDensity := by
  -- Expand `ellTau`, distribute the integral (`integral_add`/`integral_sub`/
  -- `integral_const_mul` with integrability of all bounded measurable pieces), and use
  -- `integral_W_mul_deg_left`/`integral_W_mul_deg_right` (each `= D`) and the definition of
  -- `T = ∫∫ W·c`; collect with `ring`.  Note
  -- `∫∫ W·(d(x)+d(y)) = 2D` and `∫∫ W·c = T`, so
  -- `E_τ = (r-2)(2D - 2T) - 2T = 2(r-2)D - 2(r-1)T`.
  have e : (fun z : I × I => G.W z.1 z.2 * G.ellTau r z.1 z.2)
      = fun z => (((r : ℝ) - 2) * (G.W z.1 z.2 * G.deg z.1)
            + ((r : ℝ) - 2) * (G.W z.1 z.2 * G.deg z.2))
          - (2 * (r : ℝ) - 2) * (G.W z.1 z.2 * G.codeg z.1 z.2) := by
    funext z; simp only [ellTau]; ring
  have hsum : Integrable fun z : I × I =>
      ((r : ℝ) - 2) * (G.W z.1 z.2 * G.deg z.1)
        + ((r : ℝ) - 2) * (G.W z.1 z.2 * G.deg z.2) :=
    (G.integrable_W_deg_fst.const_mul _).add (G.integrable_W_deg_snd.const_mul _)
  rw [e, integral_sub hsum (G.integrable_W_codeg.const_mul _),
    integral_add (G.integrable_W_deg_fst.const_mul _) (G.integrable_W_deg_snd.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    G.integral_W_mul_deg_left, G.integral_W_mul_deg_right]
  have hT : (∫ z : I × I, G.W z.1 z.2 * G.codeg z.1 z.2) = G.triDensity := rfl
  rw [hT]
  ring

/-- The integrated non-edge error
`E_η = ∫∫ (1-W)·ℓ_η = (r-1)(1-3p) + (3r-4)D - (r-2)T`. -/
lemma integral_oneSubW_ellEta (r : ℕ) :
    (∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2)
      = ((r : ℝ) - 1) * (1 - 3 * G.edgeDensity) + (3 * (r : ℝ) - 4) * G.degSq
        - ((r : ℝ) - 2) * G.triDensity := by
  -- Expand; the needed integrals are `∫∫ 1 = 1` (probability), `∫∫ d(x) = ∫∫ d(y) = p`
  -- (Fubini + `∫ d = p`), `∫∫ c = D` (`integral_codeg_eq_degSq`), `∫∫ W = p`,
  -- `∫∫ W·d = D` (both variables), `∫∫ W·c = T`; collect with `ring`.
  -- Paper check: `(r-1)((1-p) - (2p-2D) + (D-T)) - (D-T) = (r-1)(1-3p) + ((r-1)·3-1)D
  --   - ((r-1)+... ` — trust the STATED coefficients (they match the paper's display
  --   `E_η=(r-1)(1-3p)+(3r-4)D-(r-2)T`) and let `ring` arbitrate after substitution.
  have e : (fun z : I × I => (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2)
      = fun z => (((r : ℝ) - 1) * (1 - G.W z.1 z.2)
            - ((r : ℝ) - 1) * ((1 - G.W z.1 z.2) * G.deg z.1)
            - ((r : ℝ) - 1) * ((1 - G.W z.1 z.2) * G.deg z.2))
          + ((r : ℝ) - 2) * ((1 - G.W z.1 z.2) * G.codeg z.1 z.2) := by
    funext z; simp only [ellEta]; ring
  have hs1 : Integrable fun z : I × I =>
      ((r : ℝ) - 1) * (1 - G.W z.1 z.2)
        - ((r : ℝ) - 1) * ((1 - G.W z.1 z.2) * G.deg z.1) :=
    (G.integrable_oneSubW.const_mul _).sub (G.integrable_oneSubW_deg_fst.const_mul _)
  have hs2 : Integrable fun z : I × I =>
      (((r : ℝ) - 1) * (1 - G.W z.1 z.2)
          - ((r : ℝ) - 1) * ((1 - G.W z.1 z.2) * G.deg z.1))
        - ((r : ℝ) - 1) * ((1 - G.W z.1 z.2) * G.deg z.2) :=
    hs1.sub (G.integrable_oneSubW_deg_snd.const_mul _)
  rw [e, integral_add hs2 (G.integrable_oneSubW_codeg.const_mul _),
    integral_sub hs1 (G.integrable_oneSubW_deg_snd.const_mul _),
    integral_sub (G.integrable_oneSubW.const_mul _)
      (G.integrable_oneSubW_deg_fst.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    G.integral_oneSubW, G.integral_oneSubW_mul_deg_fst, G.integral_oneSubW_mul_deg_snd,
    G.integral_oneSubW_mul_codeg]
  ring

/-! ## The master identity and the approximate moment theorem -/

/-- **The master moment identity** (the display in the proof of `thm:approximate-moments`):
`r(2r-3)(D - p²) = r(2r-3)(α⁺-p)(p-α⁻) + (r-1)E_η - ((r-2)/2)E_τ`. -/
lemma master_moment_identity (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
      = (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
          * (G.edgeDensity - alphaMinus r)
        + ((r : ℝ) - 1) * (∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2)
        - (((r : ℝ) - 2) / 2) * (∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2) := by
  -- Substitute `integral_W_ellTau` and `integral_oneSubW_ellEta`; the identity is then a
  -- polynomial identity in `p, D, T, r` — after clearing the denominators `r ≠ 0`,
  -- `2r-3 ≠ 0` (from `hr`: `(3:ℝ) ≤ r`), `field_simp` + `ring` should close.  The
  -- `α`-factorisation to verify: `(r-1)²(3p-1) - r(2r-3)p² = r(2r-3)(α⁺-p)(p-α⁻)`.
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h0 : (r : ℝ) ≠ 0 := by linarith
  have h1 : 2 * (r : ℝ) - 3 ≠ 0 := by linarith
  -- clear the two denominators via `b * (a/b) = a`, then it is one `linear_combination`
  have hu : (r : ℝ) * alphaPlus r = (r : ℝ) - 1 := by
    simp only [alphaPlus]; exact mul_div_cancel₀ _ h0
  have hv : (2 * (r : ℝ) - 3) * alphaMinus r = (r : ℝ) - 1 := by
    simp only [alphaMinus]; exact mul_div_cancel₀ _ h1
  rw [G.integral_W_ellTau r, G.integral_oneSubW_ellEta r]
  linear_combination (-(2 * (r : ℝ) - 3) * (G.edgeDensity - alphaMinus r)) * hu
    + (((r : ℝ) - 1) - (r : ℝ) * G.edgeDensity) * hv

/-- **Cauchy–Schwarz for the integrated errors**: `|E_η| ≤ √R_η` and `|E_τ| ≤ √R_τ`
(the weights `1-W` resp. `W` are sub-probability densities). -/
lemma abs_integral_ellEta_le (r : ℕ) :
    |∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2| ≤ Real.sqrt (G.Reta r) := by
  -- Write `(1-W)·ℓ = √(1-W)·(√(1-W)·ℓ)` and apply the integral Cauchy–Schwarz
  -- (elementary route: the two-function CS `(∫ fg)² ≤ (∫ f²)(∫ g²)` via the discriminant
  -- of `t ↦ ∫ w·(ℓ + t)² ≥ 0`, as in the repo's `posSemidef_dotProduct_mulVec_sq_le`
  -- pattern — all integrands bounded measurable so integrable).
  -- With the weight `w := 1-W`: `∫ w ≤ 1` and `∫ w·ℓ² = R_η`; then `|E_η| ≤ √R_η`.
  have hw0 : ∀ z : I × I, 0 ≤ 1 - G.W z.1 z.2 := fun z => sub_nonneg.mpr (G.le_one z.1 z.2)
  have hw1 : ∀ z : I × I, 1 - G.W z.1 z.2 ≤ 1 := fun z => by linarith [G.nonneg z.1 z.2]
  have h := abs_integral_weight_mul_le (w := fun z : I × I => 1 - G.W z.1 z.2)
    (l := fun z : I × I => G.ellEta r z.1 z.2) (M := 2 * (r : ℝ) + 4)
    (measurable_const.sub G.measurable) hw0 hw1 (G.measurable_ellEta r) (by positivity)
    (fun z => G.abs_ellEta_le r z.1 z.2)
  exact h

/-- See `abs_integral_ellEta_le`. -/
lemma abs_integral_ellTau_le (r : ℕ) :
    |∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2| ≤ Real.sqrt (G.Rtau r) := by
  have h := abs_integral_weight_mul_le (w := fun z : I × I => G.W z.1 z.2)
    (l := fun z : I × I => G.ellTau r z.1 z.2) (M := 2 * (r : ℝ) + 4)
    G.measurable (fun z => G.nonneg z.1 z.2) (fun z => G.le_one z.1 z.2)
    (G.measurable_ellTau r) (by positivity) (fun z => G.abs_ellTau_le r z.1 z.2)
  exact h

/-- **Approximate moment identities** (`thm:approximate-moments`, first display): for every
graphon,
`|r(2r-3)(D-p²) - r(2r-3)(α⁺-p)(p-α⁻)| ≤ (r-1)√R_η + ((r-2)/2)√R_τ`. -/
theorem approximate_moments (r : ℕ) (hr : 3 ≤ r) :
    |(r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
        - (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
            * (G.edgeDensity - alphaMinus r)|
      ≤ ((r : ℝ) - 1) * Real.sqrt (G.Reta r)
        + (((r : ℝ) - 2) / 2) * Real.sqrt (G.Rtau r) := by
  -- Rearrange `master_moment_identity` and estimate by `abs_integral_*_le`
  -- (`abs_add_le`-chains, `abs_mul`, the coefficients `(r-1) ≥ 0`, `(r-2)/2 ≥ 0`).
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hm := G.master_moment_identity r hr
  have h1 := G.abs_integral_ellEta_le r
  have h2 := G.abs_integral_ellTau_le r
  have key : (r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
        - (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
            * (G.edgeDensity - alphaMinus r)
      = ((r : ℝ) - 1) * (∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2)
        - (((r : ℝ) - 2) / 2) * (∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2) := by
    linear_combination hm
  rw [key]
  have ha : |((r : ℝ) - 1) * (∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2)|
      ≤ ((r : ℝ) - 1) * Real.sqrt (G.Reta r) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1)]
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have hb : |(((r : ℝ) - 2) / 2) * (∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2)|
      ≤ (((r : ℝ) - 2) / 2) * Real.sqrt (G.Rtau r) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((r : ℝ) - 2) / 2)]
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  exact le_trans (abs_sub _ _) (add_le_add ha hb)

/-- `thm:approximate-moments`, second display: since `D - p² ≥ 0`,
`r(2r-3)(p-α⁻)(p-α⁺) ≤ (r-1)√R_η + ((r-2)/2)√R_τ`. -/
theorem approximate_moments_interval (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) * (2 * r - 3) * (G.edgeDensity - alphaMinus r)
        * (G.edgeDensity - alphaPlus r)
      ≤ ((r : ℝ) - 1) * Real.sqrt (G.Reta r)
        + (((r : ℝ) - 2) / 2) * Real.sqrt (G.Rtau r) := by
  -- From `approximate_moments` + `variance_deg`-nonnegativity
  -- (`D - p² = ∫ (d-p)² ≥ 0` via `integral_nonneg`), `abs_le`, sign bookkeeping:
  -- `(α⁺-p)(p-α⁻) = -(p-α⁺)(p-α⁻)` — `nlinarith`/`linarith` after unfolding.
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hvar : 0 ≤ G.degSq - G.edgeDensity ^ 2 := by
    rw [← G.variance_deg]
    exact integral_nonneg fun x => sq_nonneg _
  have hprod : 0 ≤ (r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hvar
  have happ := abs_le.mp (G.approximate_moments r hr)
  nlinarith [happ.2, hprod]

/-- `thm:approximate-moments`, third display: the degree-variance bound
`r(2r-3)∫(d-p)² ≤ r(2r-3)(α⁺-p)(p-α⁻) + (r-1)√R_η + ((r-2)/2)√R_τ`. -/
theorem approximate_moments_variance (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) * (2 * r - 3) * (∫ x, (G.deg x - G.edgeDensity) ^ 2)
      ≤ (r : ℝ) * (2 * r - 3) * (alphaPlus r - G.edgeDensity)
          * (G.edgeDensity - alphaMinus r)
        + ((r : ℝ) - 1) * Real.sqrt (G.Reta r)
        + (((r : ℝ) - 2) / 2) * Real.sqrt (G.Rtau r) := by
  -- `variance_deg` + `approximate_moments` + `abs_le`.
  rw [G.variance_deg]
  have happ := abs_le.mp (G.approximate_moments r hr)
  linarith [happ.2]

/-! ## The exact moment identities (`thm:parametric-moments`) -/

/-- `R_η = 0` kills the integrated non-edge error, via `|E_η| ≤ √R_η = 0`. -/
private lemma integral_oneSubW_ellEta_eq_zero {r : ℕ} (hη : G.Reta r = 0) :
    (∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2) = 0 := by
  have h := G.abs_integral_ellEta_le r
  rw [hη, Real.sqrt_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- `R_τ = 0` kills the integrated edge error, via `|E_τ| ≤ √R_τ = 0`. -/
private lemma integral_W_ellTau_eq_zero {r : ℕ} (hτ : G.Rtau r = 0) :
    (∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2) = 0 := by
  have h := G.abs_integral_ellTau_le r
  rw [hτ, Real.sqrt_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

section Exact

variable {r : ℕ} (hr : 3 ≤ r) (hη : G.Reta r = 0) (hτ : G.Rtau r = 0)

/-- `thm:parametric-moments` (i): `(r-1)T = (r-2)D`. -/
theorem moments_T (hτ : G.Rtau r = 0) :
    ((r : ℝ) - 1) * G.triDensity = ((r : ℝ) - 2) * G.degSq := by
  -- `E_τ = 0` from `|E_τ| ≤ √R_τ = 0`; then `integral_W_ellTau` gives
  -- `2(r-2)D - 2(r-1)T = 0`; `linarith`.
  have h := G.integral_W_ellTau r
  rw [G.integral_W_ellTau_eq_zero hτ] at h
  linarith [h]

include hη hτ

/-- `thm:parametric-moments` (ii): `r(2r-3)D = (r-1)²(3p-1)`. -/
theorem moments_D :
    (r : ℝ) * (2 * r - 3) * G.degSq = ((r : ℝ) - 1) ^ 2 * (3 * G.edgeDensity - 1) := by
  -- Both `E`'s vanish; from `integral_oneSubW_ellEta = 0` and (i), eliminate `T`
  -- (`field_simp`/`nlinarith` with `(r:ℝ) - 1 ≠ 0`).
  have h1 := G.moments_T hτ
  have h2 := G.integral_oneSubW_ellEta r
  rw [G.integral_oneSubW_ellEta_eq_zero hη] at h2
  linear_combination (-((r : ℝ) - 1)) * h2 + ((r : ℝ) - 2) * h1

include hr

/-- `thm:parametric-moments` (iii): the degree variance is
`D - p² = (α⁺-p)(p-α⁻)`. -/
theorem moments_variance :
    G.degSq - G.edgeDensity ^ 2
      = (alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r) := by
  -- `master_moment_identity` with vanishing `E`'s; divide by `r(2r-3) > 0`.
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hpos : (0 : ℝ) < (r : ℝ) * (2 * r - 3) :=
    mul_pos (by linarith) (by linarith)
  have hm := G.master_moment_identity r hr
  rw [G.integral_oneSubW_ellEta_eq_zero hη, G.integral_W_ellTau_eq_zero hτ] at hm
  have hcancel : (r : ℝ) * (2 * r - 3) * (G.degSq - G.edgeDensity ^ 2)
      = (r : ℝ) * (2 * r - 3)
          * ((alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r)) := by
    linear_combination hm
  exact mul_left_cancel₀ (ne_of_gt hpos) hcancel

/-- `thm:parametric-moments` (iv), interval: `α⁻ ≤ p ≤ α⁺`. -/
theorem moments_interval :
    alphaMinus r ≤ G.edgeDensity ∧ G.edgeDensity ≤ alphaPlus r := by
  -- `0 ≤ ∫(d-p)² = D - p² = (α⁺-p)(p-α⁻)` (via `variance_deg`, `integral_nonneg`,
  -- `moments_variance`); a non-negative product of two factors whose sum of roots
  -- satisfies `α⁻ ≤ α⁺` (`(r-1)/(2r-3) ≤ (r-1)/r` for `r ≥ 3`: `div_le_div_of_nonneg_left`
  -- style with `r ≤ 2r-3`... careful, that is FALSE — for `r ≥ 3`, `r ≤ 2r-3` ⟺ `3 ≤ r` ✓
  -- so `α⁻ ≥ α⁺`?? NO: larger denominator gives SMALLER fraction, so `2r-3 ≥ r` gives
  -- `α⁻ ≤ α⁺` ✓).  Case analysis / `nlinarith` on the product sign.
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h0 : 0 ≤ G.degSq - G.edgeDensity ^ 2 := by
    rw [← G.variance_deg]
    exact integral_nonneg fun x => sq_nonneg _
  have hprod : 0 ≤ (alphaPlus r - G.edgeDensity) * (G.edgeDensity - alphaMinus r) := by
    rw [← G.moments_variance hr hη hτ]
    exact h0
  have hαα : alphaMinus r ≤ alphaPlus r := by
    simp only [alphaMinus, alphaPlus]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  constructor
  · nlinarith [hprod, hαα, sq_nonneg (G.edgeDensity - alphaMinus r)]
  · nlinarith [hprod, hαα, sq_nonneg (G.edgeDensity - alphaPlus r)]

/-- `thm:parametric-moments` (iv), rigidity of regularity: the degree variance vanishes iff
`p ∈ {α⁻, α⁺}`. -/
theorem moments_regular_iff :
    (∫ x, (G.deg x - G.edgeDensity) ^ 2) = 0
      ↔ G.edgeDensity = alphaMinus r ∨ G.edgeDensity = alphaPlus r := by
  -- `variance_deg` + `moments_variance`: the variance equals the product, which vanishes
  -- iff a factor does (`mul_eq_zero`, `sub_eq_zero`).
  rw [G.variance_deg, G.moments_variance hr hη hτ, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm

end Exact

/-! ## The a.e. form of the hypotheses -/

/-- `R_τ = 0` iff the edge equation holds `W`-almost everywhere (the paper's phrasing):
the integrand is non-negative, so zero integral means it vanishes a.e., i.e. at almost
every pair either `W = 0` or `ℓ_τ = 0`. -/
lemma Rtau_eq_zero_iff_ae (r : ℕ) :
    G.Rtau r = 0
      ↔ ∀ᵐ z : I × I, G.W z.1 z.2 = 0 ∨ G.ellTau r z.1 z.2 = 0 := by
  -- `integral_eq_zero_iff_of_nonneg_ae` (integrand `≥ 0`, integrable by boundedness);
  -- `W·ℓ² = 0 ↔ W = 0 ∨ ℓ = 0` pointwise (`mul_eq_zero`, `pow_eq_zero_iff`).
  have hint : Integrable (fun z : I × I => G.W z.1 z.2 * G.ellTau r z.1 z.2 ^ 2) :=
    integrable_of_bounds (a := 0) (b := (2 * (r : ℝ) + 4) ^ 2)
      (G.measurable.mul ((G.measurable_ellTau r).pow_const 2))
      (fun z => mul_nonneg (G.nonneg z.1 z.2) (sq_nonneg _))
      (fun z => by
        have hb := abs_le.mp (G.abs_ellTau_le r z.1 z.2)
        exact le_trans (mul_le_of_le_one_left (sq_nonneg _) (G.le_one z.1 z.2))
          (sq_le_sq' hb.1 hb.2))
  have hnn : (0 : I × I → ℝ) ≤ fun z : I × I => G.W z.1 z.2 * G.ellTau r z.1 z.2 ^ 2 :=
    fun z => mul_nonneg (G.nonneg z.1 z.2) (sq_nonneg _)
  have hR : G.Rtau r = ∫ z : I × I, G.W z.1 z.2 * G.ellTau r z.1 z.2 ^ 2 := rfl
  rw [hR, integral_eq_zero_iff_of_nonneg hnn hint]
  constructor
  · intro h
    filter_upwards [h] with z hz
    simp only [Pi.zero_apply] at hz
    rcases mul_eq_zero.mp hz with h' | h'
    · exact Or.inl h'
    · exact Or.inr (sq_eq_zero_iff.mp h')
  · intro h
    filter_upwards [h] with z hz
    rcases hz with h' | h'
    · simp [h']
    · simp [h']

/-- See `Rtau_eq_zero_iff_ae`. -/
lemma Reta_eq_zero_iff_ae (r : ℕ) :
    G.Reta r = 0
      ↔ ∀ᵐ z : I × I, G.W z.1 z.2 = 1 ∨ G.ellEta r z.1 z.2 = 0 := by
  -- Same with the weight `1 - W` (`sub_eq_zero` for the first disjunct).
  have hint : Integrable
      (fun z : I × I => (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2 ^ 2) :=
    integrable_of_bounds (a := 0) (b := (2 * (r : ℝ) + 4) ^ 2)
      ((measurable_const.sub G.measurable).mul ((G.measurable_ellEta r).pow_const 2))
      (fun z => mul_nonneg (sub_nonneg.mpr (G.le_one z.1 z.2)) (sq_nonneg _))
      (fun z => by
        have hb := abs_le.mp (G.abs_ellEta_le r z.1 z.2)
        exact le_trans
          (mul_le_of_le_one_left (sq_nonneg _) (by linarith [G.nonneg z.1 z.2]))
          (sq_le_sq' hb.1 hb.2))
  have hnn : (0 : I × I → ℝ)
      ≤ fun z : I × I => (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2 ^ 2 :=
    fun z => mul_nonneg (sub_nonneg.mpr (G.le_one z.1 z.2)) (sq_nonneg _)
  have hR : G.Reta r = ∫ z : I × I, (1 - G.W z.1 z.2) * G.ellEta r z.1 z.2 ^ 2 := rfl
  rw [hR, integral_eq_zero_iff_of_nonneg hnn hint]
  constructor
  · intro h
    filter_upwards [h] with z hz
    simp only [Pi.zero_apply] at hz
    rcases mul_eq_zero.mp hz with h' | h'
    · exact Or.inl (sub_eq_zero.mp h').symm
    · exact Or.inr (sq_eq_zero_iff.mp h')
  · intro h
    filter_upwards [h] with z hz
    rcases hz with h' | h'
    · simp [h']
    · simp [h']

end Graphon

end FlagAlgebras.MetaTheory
