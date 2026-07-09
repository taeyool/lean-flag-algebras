import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-! # Graphons and their degree/codegree kernels (paper §11.7 preliminaries)

Mathlib has no graphon theory; this module sets up the minimal kernel calculus the §11.7–§11.8
graphon-level results need.  A **graphon** is a symmetric measurable `[0,1]`-valued kernel on
the unit square (`unitInterval` carries a probability `volume` with all product/Fubini
instances).  We define

* `Graphon` — the structure;
* `deg W x = ∫ W(x,u) du`, `codeg W x y = ∫ W(x,u)W(y,u) du` — the paper's `d`, `c`;
* `edgeDensity W = p`, `degSq W = D = ∫ d²`, `triDensity W = T = ∫∫ W·c`;

with measurability, boundedness, integrability, and the two Fubini identities the moment
computations run on:

* `integral_mul_deg_left : ∫∫ W(x,y)·d(x) = D`  (Fubini + the definition of `d`);
* `integral_codeg : ∫∫ c(x,y) dx dy = D`        (Fubini, integrating out the middle vertex).

Everything is on the probability space `I = unitInterval`; all integrands are bounded
measurable, so integrability is automatic (`MemLp.of_bound`-style) and Fubini applies.
-/

open MeasureTheory unitInterval
open scoped ENNReal

namespace FlagAlgebras.MetaTheory

/-- On a probability space, a measurable function squeezed between two constants is
integrable.  This is the workhorse integrability lemma of this file. -/
private lemma integrable_of_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-- A **graphon**: a symmetric, measurable, `[0,1]`-valued kernel on the unit square. -/
structure Graphon where
  /-- The kernel. -/
  W : I → I → ℝ
  /-- Joint measurability. -/
  measurable : Measurable (Function.uncurry W)
  /-- Symmetry. -/
  symm : ∀ x y, W x y = W y x
  /-- Lower bound. -/
  nonneg : ∀ x y, 0 ≤ W x y
  /-- Upper bound. -/
  le_one : ∀ x y, W x y ≤ 1

namespace Graphon

variable (G : Graphon)

/-- The degree function `d(x) = ∫ W(x,u) du`. -/
noncomputable def deg (x : I) : ℝ := ∫ u, G.W x u

/-- The codegree kernel `c(x,y) = ∫ W(x,u)·W(y,u) du`. -/
noncomputable def codeg (x y : I) : ℝ := ∫ u, G.W x u * G.W y u

/-- The edge density `p = ∫∫ W`. -/
noncomputable def edgeDensity : ℝ := ∫ x, G.deg x

/-- The degree second moment `D = ∫ d(x)² dx`. -/
noncomputable def degSq : ℝ := ∫ x, (G.deg x) ^ 2

/-- The triangle density `T = ∫∫ W(x,y)·c(x,y) dx dy` (in the graphon normalisation of the
paper). -/
noncomputable def triDensity : ℝ := ∫ z : I × I, G.W z.1 z.2 * G.codeg z.1 z.2

/-! ## Sections, bounds, measurability, integrability -/

lemma measurable_left (x : I) : Measurable (G.W x) :=
  -- `Measurable.of_uncurry_left` on `G.measurable`.
  G.measurable.of_uncurry_left

lemma deg_nonneg (x : I) : 0 ≤ G.deg x :=
  -- `integral_nonneg` from `G.nonneg`.
  integral_nonneg fun u => G.nonneg x u

lemma deg_le_one (x : I) : G.deg x ≤ 1 := by
  -- `∫ W(x,·) ≤ ∫ 1 = 1` on the probability space: `integral_mono` (integrability of both
  -- sides from boundedness via `integrable_of_bounds`) + `integral_const`/`measure_univ`.
  have h : G.deg x ≤ ∫ _ : I, (1 : ℝ) :=
    integral_mono (integrable_of_bounds (G.measurable_left x) (G.nonneg x) (G.le_one x))
      (integrable_const 1) (G.le_one x)
  simpa using h

lemma measurable_deg : Measurable G.deg :=
  -- Measurability of the parametric integral via
  -- `MeasureTheory.StronglyMeasurable.integral_prod_right'` on the uncurried kernel.
  G.measurable.stronglyMeasurable.integral_prod_right'.measurable

lemma codeg_nonneg (x y : I) : 0 ≤ G.codeg x y :=
  integral_nonneg fun u => mul_nonneg (G.nonneg x u) (G.nonneg y u)

lemma codeg_le_one (x y : I) : G.codeg x y ≤ 1 := by
  have h : G.codeg x y ≤ ∫ _ : I, (1 : ℝ) :=
    integral_mono
      (integrable_of_bounds ((G.measurable_left x).mul (G.measurable_left y))
        (fun u => mul_nonneg (G.nonneg x u) (G.nonneg y u))
        (fun u => mul_le_one₀ (G.le_one x u) (G.nonneg y u) (G.le_one y u)))
      (integrable_const 1)
      (fun u => mul_le_one₀ (G.le_one x u) (G.nonneg y u) (G.le_one y u))
  simpa using h

lemma codeg_symm (x y : I) : G.codeg x y = G.codeg y x :=
  -- pointwise under the integral (`integral_congr_ae` with `mul_comm`).
  integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm (G.W x u) (G.W y u))

lemma codeg_le_deg_left (x y : I) : G.codeg x y ≤ G.deg x :=
  -- `W(x,u)·W(y,u) ≤ W(x,u)` pointwise (`mul_le_of_le_one_right` with bounds).
  integral_mono
    (integrable_of_bounds ((G.measurable_left x).mul (G.measurable_left y))
      (fun u => mul_nonneg (G.nonneg x u) (G.nonneg y u))
      (fun u => mul_le_one₀ (G.le_one x u) (G.nonneg y u) (G.le_one y u)))
    (integrable_of_bounds (G.measurable_left x) (G.nonneg x) (G.le_one x))
    (fun u => mul_le_of_le_one_right (G.nonneg x u) (G.le_one y u))

lemma measurable_codeg : Measurable (Function.uncurry G.codeg) := by
  -- Parametric-integral measurability in the pair variable: view
  -- `(x,y) ↦ ∫ u, W(x,u)W(y,u)` as `integral_prod_right'` of the measurable
  -- `((x,y),u) ↦ W(x,u)W(y,u)` (compositions of `G.measurable` with measurable
  -- projections/products).
  have h1 : Measurable fun q : (I × I) × I => G.W q.1.1 q.2 :=
    G.measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  have h2 : Measurable fun q : (I × I) × I => G.W q.1.2 q.2 :=
    G.measurable.comp (measurable_fst.snd.prodMk measurable_snd)
  exact (h1.mul h2).stronglyMeasurable.integral_prod_right'.measurable

lemma edgeDensity_nonneg : 0 ≤ G.edgeDensity :=
  integral_nonneg fun x => G.deg_nonneg x

lemma edgeDensity_le_one : G.edgeDensity ≤ 1 := by
  have h : G.edgeDensity ≤ ∫ _ : I, (1 : ℝ) :=
    integral_mono (integrable_of_bounds G.measurable_deg G.deg_nonneg G.deg_le_one)
      (integrable_const 1) G.deg_le_one
  simpa using h

/-- `p = ∫∫ W` (edge density as a double integral). -/
lemma edgeDensity_eq_integral_prod :
    G.edgeDensity = ∫ z : I × I, G.W z.1 z.2 := by
  -- Fubini (`MeasureTheory.integral_prod`, integrability from boundedness + joint
  -- measurability); `volume` on `I × I` is the product measure (`Measure.volume_eq_prod`).
  have hint : Integrable (fun z : I × I => G.W z.1 z.2)
      ((volume : Measure I).prod volume) :=
    integrable_of_bounds G.measurable (fun z => G.nonneg z.1 z.2) (fun z => G.le_one z.1 z.2)
  have h : (∫ z : I × I, G.W z.1 z.2) = ∫ x, ∫ y, G.W x y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod _ hint
  rw [h]
  rfl

/-- By symmetry, a column slice integrates to the degree: `∫ x, W(x,u) dx = d(u)`. -/
private lemma integral_symm_slice (u : I) : (∫ x, G.W x u) = G.deg u :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => G.symm x u)

/-! ## The two Fubini identities of the moment computations -/

/-- `∫∫ W(x,y)·d(x) dx dy = D`. -/
lemma integral_W_mul_deg_left :
    (∫ z : I × I, G.W z.1 z.2 * G.deg z.1) = G.degSq := by
  -- Fubini in the `y`-then-`x` order: `∫∫ W(x,y)·d(x) dy dx = ∫ (∫ W(x,y) dy)·d(x) dx
  -- = ∫ d(x)² dx`.  Use `integral_prod` + `integral_mul_const` rearrangement.
  have hint : Integrable (fun z : I × I => G.W z.1 z.2 * G.deg z.1)
      ((volume : Measure I).prod volume) :=
    integrable_of_bounds (G.measurable.mul (G.measurable_deg.comp measurable_fst))
      (fun z => mul_nonneg (G.nonneg z.1 z.2) (G.deg_nonneg z.1))
      (fun z => mul_le_one₀ (G.le_one z.1 z.2) (G.deg_nonneg z.1) (G.deg_le_one z.1))
  have h : (∫ z : I × I, G.W z.1 z.2 * G.deg z.1) = ∫ x, ∫ y, G.W x y * G.deg x := by
    rw [Measure.volume_eq_prod]
    exact integral_prod _ hint
  have hinner : ∀ x : I, (∫ y, G.W x y * G.deg x) = G.deg x ^ 2 := fun x =>
    calc (∫ y, G.W x y * G.deg x) = (∫ y, G.W x y) * G.deg x := integral_mul_const _ _
      _ = G.deg x * G.deg x := rfl
      _ = G.deg x ^ 2 := (pow_two _).symm
  rw [h]
  calc (∫ x, ∫ y, G.W x y * G.deg x) = ∫ x, G.deg x ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = G.degSq := rfl

/-- `∫∫ c(x,y) dx dy = D` (integrate out the middle vertex). -/
lemma integral_codeg_eq_degSq :
    (∫ z : I × I, G.codeg z.1 z.2) = G.degSq := by
  -- `∫∫∫ W(x,u)W(y,u) du d(x,y)`: Fubini to integrate `x` and `y` first —
  -- `∫ u (∫ x W(x,u)) (∫ y W(y,u)) du = ∫ u d(u)² du` using symmetry
  -- (`G.symm`: `∫ x, W(x,u) dx = ∫ x, W(u,x) dx = d(u)`).  This is a triple-integral
  -- shuffle: set it up as `integral_prod` once plus `integral_integral_swap` twice, with
  -- all integrands bounded measurable.
  have hint : Integrable (fun z : I × I => G.codeg z.1 z.2)
      ((volume : Measure I).prod volume) :=
    integrable_of_bounds G.measurable_codeg (fun z => G.codeg_nonneg z.1 z.2)
      (fun z => G.codeg_le_one z.1 z.2)
  have h1 : (∫ z : I × I, G.codeg z.1 z.2) = ∫ x, ∫ y, G.codeg x y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod _ hint
  -- For fixed `x`, swap the `y` and `u` integrals and integrate out `y` by symmetry.
  have h2 : ∀ x : I, (∫ y, G.codeg x y) = ∫ u, G.W x u * G.deg u := by
    intro x
    have hint2 : Integrable (Function.uncurry fun (y : I) (u : I) => G.W x u * G.W y u)
        ((volume : Measure I).prod volume) :=
      integrable_of_bounds (((G.measurable_left x).comp measurable_snd).mul G.measurable)
        (fun p => mul_nonneg (G.nonneg x p.2) (G.nonneg p.1 p.2))
        (fun p => mul_le_one₀ (G.le_one x p.2) (G.nonneg p.1 p.2) (G.le_one p.1 p.2))
    have hpt : ∀ u : I, (∫ y, G.W x u * G.W y u) = G.W x u * G.deg u := by
      intro u
      rw [integral_const_mul, G.integral_symm_slice u]
    calc (∫ y, G.codeg x y) = ∫ y, ∫ u, G.W x u * G.W y u := rfl
      _ = ∫ u, ∫ y, G.W x u * G.W y u := integral_integral_swap hint2
      _ = ∫ u, G.W x u * G.deg u := integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- Swap `x` and `u`, then integrate out `x` by symmetry again.
  have hint3 : Integrable (Function.uncurry fun (x : I) (u : I) => G.W x u * G.deg u)
      ((volume : Measure I).prod volume) :=
    integrable_of_bounds (G.measurable.mul (G.measurable_deg.comp measurable_snd))
      (fun p => mul_nonneg (G.nonneg p.1 p.2) (G.deg_nonneg p.2))
      (fun p => mul_le_one₀ (G.le_one p.1 p.2) (G.deg_nonneg p.2) (G.deg_le_one p.2))
  have h4 : ∀ u : I, (∫ x, G.W x u * G.deg u) = G.deg u ^ 2 := by
    intro u
    rw [integral_mul_const, G.integral_symm_slice u, ← pow_two]
  calc (∫ z : I × I, G.codeg z.1 z.2)
      = ∫ x, ∫ y, G.codeg x y := h1
    _ = ∫ x, ∫ u, G.W x u * G.deg u := integral_congr_ae (Filter.Eventually.of_forall h2)
    _ = ∫ u, ∫ x, G.W x u * G.deg u := integral_integral_swap hint3
    _ = ∫ u, G.deg u ^ 2 := integral_congr_ae (Filter.Eventually.of_forall h4)
    _ = G.degSq := rfl

/-- Symmetrised form: `∫∫ W(x,y)·d(y) = D` as well (by symmetry of `W` and `prod_swap`). -/
lemma integral_W_mul_deg_right :
    (∫ z : I × I, G.W z.1 z.2 * G.deg z.2) = G.degSq := by
  -- Symmetric Fubini (`integral_prod_symm`) integrates `x` first; then `∫ x, W(x,y) = d(y)`
  -- by symmetry of `W`, and the inner integral becomes `d(y)²`.
  have hint : Integrable (fun z : I × I => G.W z.1 z.2 * G.deg z.2)
      ((volume : Measure I).prod volume) :=
    integrable_of_bounds (G.measurable.mul (G.measurable_deg.comp measurable_snd))
      (fun z => mul_nonneg (G.nonneg z.1 z.2) (G.deg_nonneg z.2))
      (fun z => mul_le_one₀ (G.le_one z.1 z.2) (G.deg_nonneg z.2) (G.deg_le_one z.2))
  have h : (∫ z : I × I, G.W z.1 z.2 * G.deg z.2) = ∫ y, ∫ x, G.W x y * G.deg y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_symm _ hint
  have hinner : ∀ y : I, (∫ x, G.W x y * G.deg y) = G.deg y ^ 2 := by
    intro y
    rw [integral_mul_const, G.integral_symm_slice y, ← pow_two]
  rw [h]
  calc (∫ y, ∫ x, G.W x y * G.deg y) = ∫ y, G.deg y ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = G.degSq := rfl

/-- The degree variance identity: `∫ (d(x) - p)² dx = D - p²`. -/
lemma variance_deg :
    (∫ x, (G.deg x - G.edgeDensity) ^ 2) = G.degSq - G.edgeDensity ^ 2 := by
  -- Expand the square (`ring`), integrate term by term (`integral_add`/`integral_sub`
  -- with integrability from boundedness), `∫ d = p`, `∫ p² = p²` (probability measure).
  have hd : Integrable G.deg (volume : Measure I) :=
    integrable_of_bounds G.measurable_deg G.deg_nonneg G.deg_le_one
  have hd2 : Integrable (fun x => G.deg x ^ 2) (volume : Measure I) :=
    integrable_of_bounds (G.measurable_deg.pow_const 2) (fun x => sq_nonneg _)
      (fun x => pow_le_one₀ (G.deg_nonneg x) (G.deg_le_one x))
  have hpd : Integrable (fun x => 2 * G.edgeDensity * G.deg x) (volume : Measure I) :=
    hd.const_mul _
  have hsub : Integrable (fun x => G.deg x ^ 2 - 2 * G.edgeDensity * G.deg x)
      (volume : Measure I) := hd2.sub hpd
  have hexp : ∀ x : I, (G.deg x - G.edgeDensity) ^ 2
      = G.deg x ^ 2 - 2 * G.edgeDensity * G.deg x + G.edgeDensity ^ 2 := fun x => by ring
  have h1 : (∫ x, (G.deg x - G.edgeDensity) ^ 2)
      = ∫ x, (G.deg x ^ 2 - 2 * G.edgeDensity * G.deg x + G.edgeDensity ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hexp)
  have hconst : (∫ _ : I, G.edgeDensity ^ 2) = G.edgeDensity ^ 2 := by simp
  have hD : (∫ x : I, G.deg x ^ 2) = G.degSq := rfl
  have hp : (∫ x : I, G.deg x) = G.edgeDensity := rfl
  rw [h1, integral_add hsub (integrable_const _), integral_sub hd2 hpd,
    integral_const_mul, hconst, hD, hp]
  ring

end Graphon

end FlagAlgebras.MetaTheory
