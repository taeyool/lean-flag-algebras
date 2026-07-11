import LeanFlagAlgebras.MetaTheory.GraphonMoments

/-! # Rigidity at the regular endpoint (paper §11.7, `thm:slice-rigidity`,
`cor:r3-rigidity`)

Any graphon satisfying the two mined local equations whose edge density sits at the regular
endpoint `α_r⁺ = (r-1)/r` **is** the balanced complete `r`-partite graphon — with no
forbidden subgraph, no certificate, and no classical equality theorem.

Formalisation of "up to measure-preserving relabelling, `T_r`": we produce the intrinsic
normal form — a measurable `r`-colouring `P : I → Fin r` with all colour classes of measure
`1/r` such that `W = 0` on same-colour pairs and `W = 1` on different-colour pairs, almost
everywhere (`slice_rigidity`).  A measure-preserving relabelling sending each class to an
interval then carries `W` to `T_r` literally; that final cosmetic step is not formalised.

At `r = 3` the two endpoints coincide, so the edge-density hypothesis is automatic:
`cor:r3-rigidity` (`r3_rigidity`) holds for ANY graphon satisfying the two local equations.

Proof ladder (each step a lemma, following the paper):
1. `rigid_deg_ae` — `d = (r-1)/r` a.e. (zero variance at the endpoint);
2. `rigid_codeg_ae` — `c = (r-1)/r` for `(1-W)`-a.e. pair (substitute into the non-edge
   equation);
3. `rigid_sections_boolean` — the equality case of `c ≤ d`: for a.e. `x`, the section
   `W(x,·)` is a.e. `{0,1}`-valued with zero-set of measure `1/r`, and non-neighbours have
   a.e.-equal zero-sets;
4. `slice_rigidity` — the partition: pick `r` successive generic representatives, colour by
   their zero-sets.
-/

open MeasureTheory unitInterval
open scoped ENNReal

namespace FlagAlgebras.MetaTheory

namespace Graphon

variable (G : Graphon)

/-- On the probability space `I`, a measurable function squeezed between two constants is
integrable (local copy of the `GraphonBasic` workhorse, which is `private` there). -/
private lemma integrable_bdd {f : I → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-- A set of nonzero measure survives the removal of a null set. -/
private lemma nonempty_diff_null {s t : Set I} (hs : volume s ≠ 0) (ht : volume t = 0) :
    (s \ t).Nonempty :=
  nonempty_of_measure_ne_zero (μ := (volume : Measure I)) (by rwa [measure_diff_null ht])

/-- The zero-set of the section at `x`: `C(x) = {y : W(x,y) = 0}` (measurable for every
`x`). -/
def zeroSet (x : I) : Set I := {y | G.W x y = 0}

lemma measurableSet_zeroSet (x : I) : MeasurableSet (G.zeroSet x) :=
  -- preimage of `{0}` under the measurable section `G.measurable_left x`.
  G.measurable_left x (measurableSet_singleton 0)

/-- **Step 1**: at the regular endpoint the degree function is a.e. constant `(r-1)/r`. -/
theorem rigid_deg_ae (r : ℕ) (hr : 3 ≤ r)
    (hτ : G.Rtau r = 0) (hη : G.Reta r = 0) (hp : G.edgeDensity = alphaPlus r) :
    ∀ᵐ x, G.deg x = ((r : ℝ) - 1) / r := by
  -- `moments_variance` at `p = α⁺` makes the variance product vanish
  -- (`(α⁺-p) = 0`), so `∫ (d - p)² = 0` (`variance_deg`); a non-negative integrand with
  -- zero integral vanishes a.e. (`integral_eq_zero_iff_of_nonneg_ae` — integrability from
  -- boundedness of `deg`); `sub_eq_zero` + `hp` finish (unfold `alphaPlus`).
  have hvar : (∫ x, (G.deg x - G.edgeDensity) ^ 2) = 0 := by
    rw [G.variance_deg, G.moments_variance (r := r) hr hη hτ, hp, sub_self, zero_mul]
  have hnn : ∀ x, (0 : ℝ) ≤ (G.deg x - G.edgeDensity) ^ 2 := fun x => sq_nonneg _
  have hmeas : Measurable fun x => (G.deg x - G.edgeDensity) ^ 2 :=
    (G.measurable_deg.sub measurable_const).pow_const 2
  have hbd : ∀ x, (G.deg x - G.edgeDensity) ^ 2 ≤ 1 := fun x => by
    nlinarith [G.deg_nonneg x, G.deg_le_one x, G.edgeDensity_nonneg, G.edgeDensity_le_one,
      mul_nonneg (sub_nonneg.mpr (G.deg_le_one x)) (sub_nonneg.mpr G.edgeDensity_le_one),
      mul_nonneg (G.deg_nonneg x) G.edgeDensity_nonneg]
  have h0 : (fun x => (G.deg x - G.edgeDensity) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      (integrable_bdd hmeas hnn hbd)).mp hvar
  filter_upwards [h0] with x hx
  have hsq : (G.deg x - G.edgeDensity) ^ 2 = 0 := by simpa using hx
  have : G.deg x = G.edgeDensity :=
    sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hsq)
  rw [this, hp, alphaPlus]

/-- If `d(y) = c(y,x)` then the non-negative integrand `W(y,·)(1 - W(x,·))` has zero
integral, hence vanishes a.e.: the equality case of `c ≤ d`, pointwise in the pair. -/
private lemma ae_section_mul_compl_eq_zero {x y : I} (h : G.deg y = G.codeg y x) :
    ∀ᵐ u, G.W y u * (1 - G.W x u) = 0 := by
  have hmeas : Measurable fun u => G.W y u * (1 - G.W x u) :=
    (G.measurable_left y).mul (measurable_const.sub (G.measurable_left x))
  have hnn : ∀ u, (0 : ℝ) ≤ G.W y u * (1 - G.W x u) := fun u =>
    mul_nonneg (G.nonneg y u) (by linarith [G.le_one x u])
  have hle : ∀ u, G.W y u * (1 - G.W x u) ≤ 1 := fun u =>
    mul_le_one₀ (G.le_one y u) (by linarith [G.le_one x u]) (by linarith [G.nonneg x u])
  have hval : (∫ u, G.W y u * (1 - G.W x u)) = 0 := by
    have h1 : (∫ u, G.W y u * (1 - G.W x u)) = ∫ u, (G.W y u - G.W y u * G.W x u) :=
      integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    have h2 : (∫ u, (G.W y u - G.W y u * G.W x u)) = G.deg y - G.codeg y x :=
      integral_sub (integrable_bdd (G.measurable_left y) (G.nonneg y) (G.le_one y))
        (integrable_bdd ((G.measurable_left y).mul (G.measurable_left x))
          (fun u => mul_nonneg (G.nonneg y u) (G.nonneg x u))
          (fun u => mul_le_one₀ (G.le_one y u) (G.nonneg x u) (G.le_one x u)))
    rw [h1, h2, ← h, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    (integrable_bdd hmeas hnn hle)).mp hval
  filter_upwards [hae] with u hu using by simpa using hu

/-- **Step 2**: for `(1-W)`-a.e. pair, the codegree equals `(r-1)/r`. -/
theorem rigid_codeg_ae (r : ℕ) (hr : 3 ≤ r)
    (hτ : G.Rtau r = 0) (hη : G.Reta r = 0) (hp : G.edgeDensity = alphaPlus r) :
    ∀ᵐ z : I × I, G.W z.1 z.2 = 1 ∨ G.codeg z.1 z.2 = ((r : ℝ) - 1) / r := by
  -- Combine `Reta_eq_zero_iff_ae` (the non-edge equation a.e.) with `rigid_deg_ae` at both
  -- coordinates, lifted to the product via `Measure.quasiMeasurePreserving_fst/snd`. On
  -- the good set, `ℓ_η = 0` and `d = (r-1)/r` at both roots give
  -- `(r-1)(1 - 2(r-1)/r + c) = c`, i.e. `(r-2)c = (r-1)(r-2)/r`, and `r-2 ≠ 0` yields
  -- `c = (r-1)/r` (`field_simp`, `(r:ℝ) ≠ 0`, `(r:ℝ)-2 ≠ 0` from `hr`).
  have hEta : ∀ᵐ z : I × I, G.W z.1 z.2 = 1 ∨ G.ellEta r z.1 z.2 = 0 :=
    (G.Reta_eq_zero_iff_ae r).mp hη
  have hdeg := G.rigid_deg_ae r hr hτ hη hp
  have hd1 : ∀ᵐ z : I × I, G.deg z.1 = ((r : ℝ) - 1) / r := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hdeg
  have hd2 : ∀ᵐ z : I × I, G.deg z.2 = ((r : ℝ) - 1) / r := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hdeg
  filter_upwards [hEta, hd1, hd2] with z hz h1 h2
  rcases hz with h | h
  · exact Or.inl h
  · right
    have hr' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2ne : (r : ℝ) - 2 ≠ 0 := by linarith
    have hrne : (r : ℝ) ≠ 0 := by linarith
    simp only [ellEta] at h
    set c := G.codeg z.1 z.2 with hc
    set q := ((r : ℝ) - 1) / r with hqdef
    rw [h1, h2] at h
    have hq : q * r = (r : ℝ) - 1 := div_mul_cancel₀ _ hrne
    have h5 : (((r : ℝ) - 1) * (1 - q - q + c) - c) * r = 0 := by rw [h, zero_mul]
    have key : ((r : ℝ) - 2) * (c * r - ((r : ℝ) - 1)) = 0 := by
      linear_combination h5 + 2 * ((r : ℝ) - 1) * hq
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h2ne
    · have hcr : c * r = (r : ℝ) - 1 := by linarith
      rw [hqdef, eq_div_iff hrne]
      exact hcr

/-- The pair-level key fact distilled from the paper's Step 2: for a.e. pair `(x,y)`,
either `W(x,y) = 1` or the section `W(x,·)` is a.e. `{0,1}`-valued with the same zero-set
as `W(y,·)` (the five-set chain of the paper, collapsed to its two usable consequences). -/
private lemma pair_key (r : ℕ) (hr : 3 ≤ r)
    (hτ : G.Rtau r = 0) (hη : G.Reta r = 0) (hp : G.edgeDensity = alphaPlus r) :
    ∀ᵐ z : I × I, G.W z.1 z.2 = 1 ∨
      ((∀ᵐ u, G.W z.1 u = 0 ∨ G.W z.1 u = 1)
        ∧ (∀ᵐ u, (G.W z.1 u = 0 ↔ G.W z.2 u = 0))) := by
  have hcod := G.rigid_codeg_ae r hr hτ hη hp
  have hdeg := G.rigid_deg_ae r hr hτ hη hp
  have hd1 : ∀ᵐ z : I × I, G.deg z.1 = ((r : ℝ) - 1) / r := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hdeg
  have hd2 : ∀ᵐ z : I × I, G.deg z.2 = ((r : ℝ) - 1) / r := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hdeg
  filter_upwards [hcod, hd1, hd2] with z hz h1 h2
  rcases hz with h | hcz
  · exact Or.inl h
  · right
    -- the two vanishing mixed integrals: `∫ W(y,·)(1-W(x,·)) = d(y) - c = 0` and the swap
    have hA : ∀ᵐ u, G.W z.2 u * (1 - G.W z.1 u) = 0 := by
      apply G.ae_section_mul_compl_eq_zero
      rw [h2, G.codeg_symm, hcz]
    have hB : ∀ᵐ u, G.W z.1 u * (1 - G.W z.2 u) = 0 := by
      apply G.ae_section_mul_compl_eq_zero
      rw [h1, hcz]
    constructor
    · filter_upwards [hA, hB] with u hu1 hu2
      rcases mul_eq_zero.mp hu2 with h0 | h0
      · exact Or.inl h0
      · have hy1 : G.W z.2 u = 1 := by linarith [sub_eq_zero.mp h0]
        rcases mul_eq_zero.mp hu1 with h3 | h3
        · rw [hy1] at h3; norm_num at h3
        · exact Or.inr (by linarith [sub_eq_zero.mp h3])
    · filter_upwards [hA, hB] with u hu1 hu2
      constructor
      · intro hx0
        rcases mul_eq_zero.mp hu1 with h3 | h3
        · exact h3
        · have := sub_eq_zero.mp h3
          rw [hx0] at this; norm_num at this
      · intro hy0
        rcases mul_eq_zero.mp hu2 with h3 | h3
        · exact h3
        · have := sub_eq_zero.mp h3
          rw [hy0] at this; norm_num at this

/-- **Step 3 (the equality case of `c ≤ d`)**: for a.e. `x`, the section `W(x,·)` is a.e.
`{0,1}`-valued and its zero-set has measure `1/r`; moreover for a.e. `x`, for a.e.
`y ∈ zeroSet x`, the two zero-sets agree up to null sets. -/
theorem rigid_sections_boolean (r : ℕ) (hr : 3 ≤ r)
    (hτ : G.Rtau r = 0) (hη : G.Reta r = 0) (hp : G.edgeDensity = alphaPlus r) :
    (∀ᵐ x, (∀ᵐ y, G.W x y = 0 ∨ G.W x y = 1)
        ∧ volume (G.zeroSet x) = ENNReal.ofReal (1 / r))
      ∧ (∀ᵐ x, ∀ᵐ y, G.W x y = 0 →
          volume (symmDiff (G.zeroSet x) (G.zeroSet y)) = 0) := by
  -- From `pair_key`, lifted from pairs to a.e.-in-`x`-then-a.e.-in-`y` via
  -- `Measure.ae_ae_of_ae_prod`: for a.e. `x`, pick a partner `y` with `W x y ≠ 1`
  -- (possible since `d(x) = (r-1)/r < 1`, so `{W x · ≠ 1}` has positive measure); the
  -- boolean-section half of `pair_key` at `(x,y)` gives the section statement directly,
  -- and the zero-set measure follows by expressing `1 - W(x,·)` as the a.e.-indicator of
  -- `zeroSet x` and integrating.  The zero-set-agreement half restates `pair_key`'s
  -- iff-of-zero-sets via `measure_symmDiff_eq_zero_iff ↔ ae_eq_set`.
  have hkey := G.pair_key r hr hτ hη hp
  rw [Measure.volume_eq_prod] at hkey
  have hkey' := Measure.ae_ae_of_ae_prod hkey
  have hdeg := G.rigid_deg_ae r hr hτ hη hp
  have hr' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := by linarith
  constructor
  · filter_upwards [hkey', hdeg] with x hkx hdx
    -- extract a partner `y` with `W x y ≠ 1` (possible since `d(x) = (r-1)/r < 1`)
    have hne : volume {y | ¬ (G.W x y = 1)} ≠ 0 := by
      intro h0
      have hae : ∀ᵐ y, G.W x y = 1 := ae_iff.mpr h0
      have hone : G.deg x = 1 := by
        have : G.deg x = ∫ (_ : I), (1 : ℝ) :=
          integral_congr_ae (by filter_upwards [hae] with y hy using hy)
        simpa using this
      rw [hdx] at hone
      field_simp at hone
      linarith
    obtain ⟨y, hy⟩ := nonempty_diff_null hne (ae_iff.mp hkx)
    rcases not_not.mp hy.2 with h | ⟨hbool, _⟩
    · exact absurd h hy.1
    refine ⟨hbool, ?_⟩
    -- boolean section ⟹ `1 - W(x,·)` is a.e. the indicator of the zero-set
    have hind : (fun u => 1 - G.W x u) =ᵐ[volume] (G.zeroSet x).indicator 1 := by
      filter_upwards [hbool] with u hu
      rcases hu with h0 | h1
      · have hm : u ∈ G.zeroSet x := h0
        rw [Set.indicator_of_mem hm, h0, Pi.one_apply]
        norm_num
      · have hm : u ∉ G.zeroSet x := by simp [zeroSet, h1]
        rw [Set.indicator_of_notMem hm, h1]
        norm_num
    have hIval : (∫ u, (1 - G.W x u)) = 1 - G.deg x := by
      rw [integral_sub (integrable_const 1)
        (integrable_bdd (G.measurable_left x) (G.nonneg x) (G.le_one x))]
      simp [deg]
    have hreal : volume.real (G.zeroSet x) = 1 - G.deg x := by
      rw [← integral_indicator_one (G.measurableSet_zeroSet x),
        ← integral_congr_ae hind, hIval]
    rw [hdx] at hreal
    have h1r : volume.real (G.zeroSet x) = 1 / r := by
      rw [hreal]
      field_simp
      ring
    calc volume (G.zeroSet x)
        = ENNReal.ofReal (volume.real (G.zeroSet x)) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (1 / r) := by rw [h1r]
  · filter_upwards [hkey'] with x hkx
    filter_upwards [hkx] with y hxy h0
    rcases hxy with h1 | ⟨_, hiff⟩
    · rw [h0] at h1
      norm_num at h1
    · rw [measure_symmDiff_eq_zero_iff, Filter.eventuallyEq_set]
      filter_upwards [hiff] with u hu
      simpa [zeroSet] using hu

/-! ### Step 3 infrastructure: good points, the class dichotomy, and representatives -/

/-- A point is **good** if its section is a.e. boolean, its zero-set has measure `1/r`,
and its zero-partners share its zero-set — the conclusions of `rigid_sections_boolean`,
held pointwise. -/
private def GoodPt (r : ℕ) (x : I) : Prop :=
  (∀ᵐ y, G.W x y = 0 ∨ G.W x y = 1)
    ∧ volume (G.zeroSet x) = ENNReal.ofReal (1 / r)
    ∧ ∀ᵐ y, G.W x y = 0 → volume (symmDiff (G.zeroSet x) (G.zeroSet y)) = 0

private lemma ae_goodPt (r : ℕ) (hr : 3 ≤ r)
    (hτ : G.Rtau r = 0) (hη : G.Reta r = 0) (hp : G.edgeDensity = alphaPlus r) :
    ∀ᵐ x, G.GoodPt r x := by
  obtain ⟨h1, h2⟩ := G.rigid_sections_boolean r hr hτ hη hp
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1.1, hx1.2, hx2⟩

/-- Two good zero-sets are a.e. equal or a.e. disjoint (paper Step 3, first
consequence): a generic point of the intersection forces both to agree with its own
zero-set. -/
private lemma goodPt_eq_or_disjoint {r : ℕ} {x x' : I}
    (hx : G.GoodPt r x) (hx' : G.GoodPt r x') :
    G.zeroSet x =ᵐ[volume] G.zeroSet x'
      ∨ volume (G.zeroSet x ∩ G.zeroSet x') = 0 := by
  by_cases h : volume (G.zeroSet x ∩ G.zeroSet x') = 0
  · exact Or.inr h
  · left
    obtain ⟨y, hy⟩ := nonempty_diff_null h
      (measure_union_null (ae_iff.mp hx.2.2) (ae_iff.mp hx'.2.2))
    have e1 : G.zeroSet x =ᵐ[volume] G.zeroSet y :=
      measure_symmDiff_eq_zero_iff.mp
        (not_not.mp (fun hc => hy.2 (Or.inl hc)) hy.1.1)
    have e2 : G.zeroSet x' =ᵐ[volume] G.zeroSet y :=
      measure_symmDiff_eq_zero_iff.mp
        (not_not.mp (fun hc => hy.2 (Or.inr hc)) hy.1.2)
    exact e1.trans e2.symm

/-- The section of the "common zero" set of a fixed `x'`, viewed from the first
coordinate. -/
private lemma prodMk_preimage_overlap (x' x : I) :
    Prod.mk x ⁻¹' ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x'))
      = G.zeroSet x ∩ G.zeroSet x' := by
  ext u
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
  rfl

private lemma measurableSet_overlapProd (x' : I) :
    MeasurableSet ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x')) := by
  refine MeasurableSet.inter ?_ (measurable_snd (G.measurableSet_zeroSet x'))
  exact G.measurable (measurableSet_singleton 0)

private lemma measurable_overlap (x' : I) :
    Measurable fun x => volume (G.zeroSet x ∩ G.zeroSet x') := by
  have h := measurable_measure_prodMk_left (ν := (volume : Measure I))
    (G.measurableSet_overlapProd x')
  simpa only [G.prodMk_preimage_overlap x'] using h

/-- **Fubini/Markov bound**: the set of points whose zero-set meets a fixed
measure-`1/r` zero-set in measure `≥ 1/r` has measure at most `1/r`.  (The double
integral of the overlap kernel is `(1/r)²` by Fubini and Step 2.) -/
private lemma overlap_bound {r : ℕ} (hrpos : 0 < (1 : ℝ) / r)
    (hvol : ∀ᵐ y, volume (G.zeroSet y) = ENNReal.ofReal (1 / r)) (x' : I)
    (hx' : volume (G.zeroSet x') = ENNReal.ofReal (1 / r)) :
    volume {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet x')}
      ≤ ENNReal.ofReal (1 / r) := by
  have hSmeas := G.measurableSet_overlapProd x'
  -- the double integral of the overlap kernel, sliced the other way
  have hdown : ((volume : Measure I).prod volume)
      ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x'))
        = ENNReal.ofReal (1 / r) * ENNReal.ofReal (1 / r) := by
    rw [Measure.prod_apply_symm hSmeas]
    have hinner : ∀ y : I,
        volume ((fun x => (x, y)) ⁻¹'
            ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x')))
          = Set.indicator (G.zeroSet x') (fun v => volume (G.zeroSet v)) y := by
      intro y
      by_cases hy : y ∈ G.zeroSet x'
      · rw [Set.indicator_of_mem hy]
        congr 1
        ext u
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, _⟩
          show G.W y u = 0
          rw [G.symm y u]
          exact h1
        · intro h1
          have : G.W u y = 0 := by rw [G.symm u y]; exact h1
          exact ⟨this, hy⟩
      · rw [Set.indicator_of_notMem hy]
        have hempty : ((fun x => (x, y)) ⁻¹'
            ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x'))) = ∅ := by
          ext u
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun _ => hy
        rw [hempty]
        exact measure_empty
    calc (∫⁻ y, volume ((fun x => (x, y)) ⁻¹'
            ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x'))))
        = ∫⁻ y, Set.indicator (G.zeroSet x') (fun v => volume (G.zeroSet v)) y :=
          lintegral_congr hinner
      _ = ∫⁻ y, Set.indicator (G.zeroSet x') (fun _ => ENNReal.ofReal (1 / r)) y := by
          apply lintegral_congr_ae
          filter_upwards [hvol] with y hy
          by_cases hmem : y ∈ G.zeroSet x'
          · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hy]
          · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      _ = ENNReal.ofReal (1 / r) * volume (G.zeroSet x') :=
          lintegral_indicator_const (G.measurableSet_zeroSet x') _
      _ = ENNReal.ofReal (1 / r) * ENNReal.ofReal (1 / r) := by rw [hx']
  -- Markov's inequality for the measurable overlap kernel
  have hofne : ENNReal.ofReal (1 / r) ≠ 0 := (ENNReal.ofReal_pos.mpr hrpos).ne'
  have hchain : ENNReal.ofReal (1 / r)
      * volume {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet x')}
        ≤ ENNReal.ofReal (1 / r) * ENNReal.ofReal (1 / r) := by
    calc ENNReal.ofReal (1 / r)
        * volume {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet x')}
        ≤ ∫⁻ x, volume (G.zeroSet x ∩ G.zeroSet x') :=
          mul_meas_ge_le_lintegral₀ (G.measurable_overlap x').aemeasurable _
      _ = ∫⁻ x, volume (Prod.mk x ⁻¹'
            ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x'))) := by
          refine lintegral_congr fun x => ?_
          rw [G.prodMk_preimage_overlap x']
      _ = ((volume : Measure I).prod volume)
            ({z : I × I | G.W z.1 z.2 = 0} ∩ (Prod.snd ⁻¹' G.zeroSet x')) :=
          (Measure.prod_apply hSmeas).symm
      _ = ENNReal.ofReal (1 / r) * ENNReal.ofReal (1 / r) := hdown
  exact (ENNReal.mul_le_mul_iff_right hofne ENNReal.ofReal_ne_top).mp hchain

/-- Recursive extraction of `k ≤ r` good representatives with pairwise a.e.-disjoint
zero-sets: the Markov bound leaves room for a fresh good point at every stage. -/
private lemma exists_reps {r : ℕ} (hr : 3 ≤ r)
    (hgood : ∀ᵐ x, G.GoodPt r x)
    (hvol : ∀ᵐ y, volume (G.zeroSet y) = ENNReal.ofReal (1 / r)) :
    ∀ k : ℕ, k ≤ r → ∃ f : Fin k → I, (∀ j, G.GoodPt r (f j)) ∧
      ∀ j j' : Fin k, j ≠ j' →
        volume (G.zeroSet (f j) ∩ G.zeroSet (f j')) = 0 := by
  have hr0 : 0 < (r : ℝ) := by
    have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hrpos : 0 < (1 : ℝ) / r := by positivity
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ k ih =>
    intro hk1
    obtain ⟨f, hfgood, hfdisj⟩ := ih (Nat.le_of_succ_le hk1)
    -- the measurable set of points whose class meets some previous class substantially
    have hBadMeas : MeasurableSet (⋃ j : Fin k,
        {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))}) :=
      MeasurableSet.iUnion fun j =>
        (G.measurable_overlap (f j)) measurableSet_Ici
    have hBadSmall : volume (⋃ j : Fin k,
        {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))}) < 1 := by
      calc volume (⋃ j : Fin k,
            {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))})
          ≤ ∑ j : Fin k, volume
              {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))} :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ _j : Fin k, ENNReal.ofReal (1 / r) :=
            Finset.sum_le_sum fun j _ => G.overlap_bound hrpos hvol (f j) ((hfgood j).2.1)
        _ = (k : ℝ≥0∞) * ENNReal.ofReal (1 / r) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ENNReal.ofReal ((k : ℝ) * (1 / r)) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        _ < 1 := by
            rw [ENNReal.ofReal_lt_one, mul_one_div, div_lt_one hr0]
            exact_mod_cast hk1
    have hcompl : volume ((⋃ j : Fin k,
        {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))})ᶜ) ≠ 0 := by
      intro h0
      have h1 : volume (Set.univ : Set I)
          ≤ volume (⋃ j : Fin k,
              {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))})
            + volume ((⋃ j : Fin k,
              {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))})ᶜ) := by
        rw [← Set.union_compl_self (⋃ j : Fin k,
          {x | ENNReal.ofReal (1 / r) ≤ volume (G.zeroSet x ∩ G.zeroSet (f j))})]
        exact measure_union_le _ _
      rw [measure_univ, h0, add_zero] at h1
      exact absurd h1 (not_le.mpr hBadSmall)
    obtain ⟨x0, hx0⟩ := nonempty_diff_null hcompl (ae_iff.mp hgood)
    have hx0good : G.GoodPt r x0 := not_not.mp hx0.2
    have hx0dis : ∀ j : Fin k, volume (G.zeroSet x0 ∩ G.zeroSet (f j)) = 0 := by
      intro j
      have hlt : ¬ (ENNReal.ofReal (1 / r)
          ≤ volume (G.zeroSet x0 ∩ G.zeroSet (f j))) := fun hge =>
        hx0.1 (Set.mem_iUnion.mpr ⟨j, hge⟩)
      rcases G.goodPt_eq_or_disjoint hx0good (hfgood j) with heq | hnull
      · exfalso
        apply hlt
        have hfull : volume (G.zeroSet x0 ∩ G.zeroSet (f j))
            = volume (G.zeroSet (f j)) := by
          refine le_antisymm (measure_mono Set.inter_subset_right) ?_
          calc volume (G.zeroSet (f j))
              ≤ volume ((G.zeroSet x0 ∩ G.zeroSet (f j))
                  ∪ (G.zeroSet (f j) \ G.zeroSet x0)) := by
                refine measure_mono fun u hu => ?_
                by_cases h : u ∈ G.zeroSet x0
                · exact Or.inl ⟨h, hu⟩
                · exact Or.inr ⟨hu, h⟩
            _ ≤ volume (G.zeroSet x0 ∩ G.zeroSet (f j))
                + volume (G.zeroSet (f j) \ G.zeroSet x0) := measure_union_le _ _
            _ = volume (G.zeroSet x0 ∩ G.zeroSet (f j)) := by
                rw [(ae_eq_set.mp heq).2, add_zero]
        rw [hfull, (hfgood j).2.1]
      · exact hnull
    refine ⟨Fin.snoc f x0, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · rw [Fin.snoc_last]
        exact hx0good
      · intro i
        rw [Fin.snoc_castSucc]
        exact hfgood i
    · intro j j' hjj'
      induction j using Fin.lastCases with
      | last =>
        induction j' using Fin.lastCases with
        | last => exact absurd rfl hjj'
        | cast i' =>
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hx0dis i'
      | cast i =>
        induction j' using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, Fin.snoc_castSucc, Set.inter_comm]
          exact hx0dis i
        | cast i' =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hfdisj i i' fun h => hjj' (congrArg Fin.castSucc h)

open Classical in
/-- The colouring induced by a family of representatives: the first index whose zero-set
contains `x` (default `0` on the null leftover). -/
private noncomputable def colour {r : ℕ} [NeZero r] (f : Fin r → I) (x : I) : Fin r :=
  if h : ∃ i, x ∈ G.zeroSet (f i) then Fin.find (fun i => x ∈ G.zeroSet (f i)) h else 0

open Classical in
private lemma colour_eq_iff {r : ℕ} [NeZero r] (f : Fin r → I) (x : I) (i : Fin r) :
    G.colour f x = i ↔
      ((x ∈ G.zeroSet (f i) ∧ ∀ j < i, x ∉ G.zeroSet (f j))
        ∨ (i = 0 ∧ ∀ j, x ∉ G.zeroSet (f j))) := by
  unfold colour
  by_cases h : ∃ k, x ∈ G.zeroSet (f k)
  · rw [dif_pos h, Fin.find_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨_, h2⟩)
      · exact ⟨h1, h2⟩
      · obtain ⟨j, hj⟩ := h
        exact absurd hj (h2 j)
  · rw [dif_neg h]
    push_neg at h
    constructor
    · rintro rfl
      exact Or.inr ⟨rfl, h⟩
    · rintro (⟨h1, _⟩ | ⟨hi, _⟩)
      · exact absurd h1 (h i)
      · exact hi.symm

open Classical in
private lemma mem_zeroSet_colour {r : ℕ} [NeZero r] (f : Fin r → I) (x : I)
    (h : ∃ i, x ∈ G.zeroSet (f i)) : x ∈ G.zeroSet (f (G.colour f x)) := by
  unfold colour
  rw [dif_pos h]
  exact Fin.find_spec h

private lemma colour_preimage {r : ℕ} [NeZero r] (f : Fin r → I) (i : Fin r) :
    G.colour f ⁻¹' {i}
      = (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))
        ∪ (if i = 0 then (⋃ j, G.zeroSet (f j))ᶜ else ∅) := by
  ext x
  rw [Set.mem_preimage, Set.mem_singleton_iff, G.colour_eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨hi, h2⟩)
    · left
      refine ⟨h1, fun hmem => ?_⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hji, hjC⟩ := Set.mem_iUnion.mp hj
      exact h2 j hji hjC
    · right
      rw [if_pos hi, Set.mem_compl_iff]
      intro hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      exact h2 j hj
  · rintro (⟨h1, h2⟩ | h2)
    · left
      exact ⟨h1, fun j hji hjC =>
        h2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hjC⟩⟩)⟩
    · by_cases hi : i = 0
      · rw [if_pos hi] at h2
        right
        exact ⟨hi, fun j hj => h2 (Set.mem_iUnion.mpr ⟨j, hj⟩)⟩
      · rw [if_neg hi] at h2
        exact absurd h2 (Set.notMem_empty x)

/-- **Rigidity at the regular endpoint** (`thm:slice-rigidity`): a graphon satisfying the
two local equations with edge density `(r-1)/r` is, up to relabelling, the balanced complete
`r`-partite graphon — intrinsic normal form: a measurable `r`-colouring with classes of
measure `1/r`, with `W = 0` on same-colour and `W = 1` on different-colour pairs a.e. -/
theorem slice_rigidity (r : ℕ) (hr : 3 ≤ r)
    (hτ : G.Rtau r = 0) (hη : G.Reta r = 0) (hp : G.edgeDensity = alphaPlus r) :
    ∃ P : I → Fin r, Measurable P
      ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / r))
      ∧ ∀ᵐ z : I × I, G.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 := by
  -- The paper's Step 3, with a representative trick for measurability. Call `x` GOOD
  -- (`GoodPt`) if it satisfies the conclusions of `rigid_sections_boolean` pointwise:
  -- boolean section, zero-set measure `1/r`, a.e.-agreement with its zero-partners — a
  -- full-measure property (`ae_goodPt`). Representatives `f 0, …, f (r-1)` with
  -- pairwise-a.e.-disjoint zero-sets `C i := zeroSet (f i)` are extracted recursively
  -- (`exists_reps`): having chosen `j < i` many, a Markov/Fubini bound
  -- (`overlap_bound`) shows the set of points whose class overlaps a previous one
  -- substantially has small measure, leaving room for a fresh good point (two zero-sets
  -- are a.e.-equal or a.e.-disjoint, `goodPt_eq_or_disjoint`, via a generic common
  -- point). After `r` steps the disjointified classes `A i := C i \ ⋃_{j<i} C j` tile `I`
  -- up to a null set (total measure `r·(1/r) = 1`). The colouring `P := colour f` sends
  -- `x` to the least `i` with `x ∈ A i` (default `0` on the null leftover); each fibre
  -- has measure `1/r`. The block form follows a.e.: if `P x = P y = i`, both lie
  -- a.e.-in `C i =ᵐ zeroSet x`, so `W(x,y) = 0`; if `P x ≠ P y`, then `y ∉ zeroSet x` mod
  -- null and the boolean section forces `W(x,y) = 1`.
  classical
  haveI : NeZero r := ⟨by omega⟩
  have hr0 : 0 < (r : ℝ) := by
    have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hgood := G.ae_goodPt r hr hτ hη hp
  have hvol : ∀ᵐ y, volume (G.zeroSet y) = ENNReal.ofReal (1 / r) := by
    filter_upwards [hgood] with y hy using hy.2.1
  -- Step 3a: the representatives and their classes
  obtain ⟨f, hfgood, hfdisj⟩ := G.exists_reps hr hgood hvol r le_rfl
  -- Step 3b: the disjointified classes tile `I` up to a null set
  have hAmeas : ∀ i : Fin r, MeasurableSet
      (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j)) := fun i =>
    (G.measurableSet_zeroSet (f i)).diff
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
        G.measurableSet_zeroSet (f j))
  have hAvol : ∀ i : Fin r,
      volume (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))
        = ENNReal.ofReal (1 / r) := by
    intro i
    have hnull : volume (G.zeroSet (f i) ∩ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j)) = 0 := by
      have hdistrib : (G.zeroSet (f i) ∩ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))
          = ⋃ j, ⋃ (_ : j < i), G.zeroSet (f i) ∩ G.zeroSet (f j) := by
        rw [Set.inter_iUnion]
        exact Set.iUnion_congr fun j => by rw [Set.inter_iUnion]
      rw [hdistrib, measure_iUnion_null_iff]
      intro j
      rw [measure_iUnion_null_iff]
      intro hji
      exact hfdisj i j (ne_of_lt hji).symm
    calc volume (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))
        = volume (G.zeroSet (f i)
            \ (G.zeroSet (f i) ∩ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))) := by
          rw [Set.diff_self_inter]
      _ = volume (G.zeroSet (f i)) := measure_diff_null hnull
      _ = ENNReal.ofReal (1 / r) := (hfgood i).2.1
  have hAdisj : Pairwise (Function.onFun Disjoint
      fun i : Fin r => G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.mpr fun x hxi hxj =>
        hxj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨h, hxi.1⟩⟩)
    · exact Set.disjoint_left.mpr fun x hxi hxj =>
        hxi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨h, hxj.1⟩⟩)
  have hsum : (∑' _i : Fin r, ENNReal.ofReal (1 / r)) = 1 := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast r, ← ENNReal.ofReal_mul (by positivity), mul_one_div,
      div_self hrne, ENNReal.ofReal_one]
  have hUA : volume (⋃ i : Fin r,
      (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))) = 1 := by
    rw [measure_iUnion hAdisj hAmeas]
    rw [tsum_congr fun i => hAvol i]
    exact hsum
  have hUC : volume (⋃ j, G.zeroSet (f j)) = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞)
        = volume (⋃ i : Fin r,
            (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))) := hUA.symm
      _ ≤ volume (⋃ j, G.zeroSet (f j)) :=
          measure_mono (Set.iUnion_mono fun i => Set.diff_subset)
  have hL : volume ((⋃ j, G.zeroSet (f j))ᶜ) = 0 := by
    rw [prob_compl_eq_one_sub
      (MeasurableSet.iUnion fun j => G.measurableSet_zeroSet (f j)), hUC, tsub_self]
  -- Step 3c: the colouring, its measurability and its fibre volumes
  have hPmeas : Measurable (G.colour f) := by
    apply measurable_to_countable'
    intro i
    rw [G.colour_preimage f i]
    refine ((hAmeas i).union ?_)
    split_ifs
    · exact (MeasurableSet.iUnion fun j => G.measurableSet_zeroSet (f j)).compl
    · exact MeasurableSet.empty
  have hfib : ∀ i, volume (G.colour f ⁻¹' {i}) = ENNReal.ofReal (1 / r) := by
    intro i
    rw [G.colour_preimage f i]
    have hite : volume (if i = 0 then (⋃ j, G.zeroSet (f j))ᶜ else (∅ : Set I)) = 0 := by
      split_ifs
      · exact hL
      · exact measure_empty
    refine le_antisymm ?_ ?_
    · calc volume ((G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))
            ∪ (if i = 0 then (⋃ j, G.zeroSet (f j))ᶜ else ∅))
          ≤ volume (G.zeroSet (f i) \ ⋃ j, ⋃ (_ : j < i), G.zeroSet (f j))
            + volume (if i = 0 then (⋃ j, G.zeroSet (f j))ᶜ else (∅ : Set I)) :=
            measure_union_le _ _
        _ = ENNReal.ofReal (1 / r) := by rw [hite, add_zero, hAvol i]
    · rw [← hAvol i]
      exact measure_mono Set.subset_union_left
  -- Step 3d: the a.e. class dictionary — membership in `C i` reads off the colour
  have hOnull : volume (⋃ i : Fin r, ⋃ j : Fin r, ⋃ (_ : i ≠ j),
      G.zeroSet (f i) ∩ G.zeroSet (f j)) = 0 := by
    rw [measure_iUnion_null_iff]
    intro i
    rw [measure_iUnion_null_iff]
    intro j
    rw [measure_iUnion_null_iff]
    intro hij
    exact hfdisj i j hij
  have hclass : ∀ᵐ y, ∀ i, (y ∈ G.zeroSet (f i) ↔ G.colour f y = i) := by
    have h1 := measure_eq_zero_iff_ae_notMem.mp hL
    have h2 := measure_eq_zero_iff_ae_notMem.mp hOnull
    filter_upwards [h1, h2] with y hy1 hy2
    intro i
    constructor
    · intro hyi
      rw [G.colour_eq_iff]
      left
      refine ⟨hyi, fun j hji hyj => ?_⟩
      exact hy2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨(ne_of_lt hji).symm, ⟨hyi, hyj⟩⟩⟩⟩)
    · intro hcol
      rw [G.colour_eq_iff] at hcol
      rcases hcol with ⟨h3, _⟩ | ⟨_, h3⟩
      · exact h3
      · exact absurd (fun hmem => by
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
          exact h3 j hj) hy1
  -- Step 3e: for a.e. `x`, the zero-set of `x` is its colour class (mod null)
  have hrep : ∀ᵐ x, ∀ i : Fin r, G.W (f i) x = 0 →
      volume (symmDiff (G.zeroSet (f i)) (G.zeroSet x)) = 0 := by
    rw [ae_all_iff]
    intro i
    exact (hfgood i).2.2
  have hcover : ∀ᵐ x, ∃ i, x ∈ G.zeroSet (f i) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hL] with x hx
    have hmem : x ∈ ⋃ j, G.zeroSet (f j) := by
      by_contra hmem
      exact hx hmem
    exact Set.mem_iUnion.mp hmem
  have hzs : ∀ᵐ x, G.zeroSet x =ᵐ[volume] G.zeroSet (f (G.colour f x)) := by
    filter_upwards [hrep, hcover] with x hx1 hx2
    have hmem := G.mem_zeroSet_colour f x hx2
    have h0 : G.W (f (G.colour f x)) x = 0 := hmem
    exact (measure_symmDiff_eq_zero_iff.mp (hx1 (G.colour f x) h0)).symm
  -- Step 3f: the block form, iterated a.e.
  have hmain : ∀ᵐ x, ∀ᵐ y,
      G.W x y = if G.colour f x = G.colour f y then 0 else 1 := by
    filter_upwards [hzs, hgood] with x hxzs hxgood
    have hxzs' : ∀ᵐ y, (y ∈ G.zeroSet x ↔ y ∈ G.zeroSet (f (G.colour f x))) :=
      Filter.eventuallyEq_set.mp hxzs
    filter_upwards [hxgood.1, hxzs', hclass] with y hybool hyzs hyclass
    by_cases hPP : G.colour f x = G.colour f y
    · rw [if_pos hPP]
      have hyC : y ∈ G.zeroSet (f (G.colour f x)) := by
        rw [hPP]
        exact (hyclass (G.colour f y)).mpr rfl
      exact hyzs.mpr hyC
    · rw [if_neg hPP]
      have hnot : y ∉ G.zeroSet (f (G.colour f x)) := fun h =>
        hPP ((hyclass (G.colour f x)).mp h).symm
      have hnot2 : y ∉ G.zeroSet x := fun h => hnot (hyzs.mp h)
      rcases hybool with h0 | h1
      · exact absurd h0 hnot2
      · exact h1
  -- Step 3g: upgrade to the product measure via measurability of the block set
  refine ⟨G.colour f, hPmeas, hfib, ?_⟩
  have hWm : Measurable fun z : I × I => G.W z.1 z.2 := G.measurable
  have h1 : MeasurableSet {z : I × I | G.colour f z.1 = G.colour f z.2} :=
    measurableSet_eq_fun (hPmeas.comp measurable_fst) (hPmeas.comp measurable_snd)
  have h2 : Measurable fun z : I × I =>
      if G.colour f z.1 = G.colour f z.2 then (0 : ℝ) else 1 :=
    Measurable.ite h1 measurable_const measurable_const
  have hset : MeasurableSet {z : I × I |
      G.W z.1 z.2 = if G.colour f z.1 = G.colour f z.2 then 0 else 1} :=
    measurableSet_eq_fun hWm h2
  rw [Measure.volume_eq_prod]
  exact (Measure.ae_prod_mem_iff_ae_ae_mem hset).mpr hmain

/-- **Unconditional rigidity at `r = 3`** (`cor:r3-rigidity`): at `r = 3` the two local
equations alone identify the balanced complete tripartite graphon (the two endpoints
coincide, so the edge density is pinned automatically). -/
theorem r3_rigidity (hτ : G.Rtau 3 = 0) (hη : G.Reta 3 = 0) :
    ∃ P : I → Fin 3, Measurable P
      ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / 3))
      ∧ ∀ᵐ z : I × I, G.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 := by
  -- `alphaMinus 3 = alphaPlus 3 = 2/3` (`norm_num` on the defs), so
  -- `moments_variance`+`variance_deg` read `0 ≤ ∫(d-p)² = -(p-2/3)²·…` — concretely
  -- `(α⁺-p)(p-α⁻) = -(p-2/3)²`, non-negative only at `p = 2/3`; hence
  -- `G.edgeDensity = alphaPlus 3` and `slice_rigidity` applies with `r := 3`.
  have hiv := G.moments_interval (r := 3) le_rfl hη hτ
  have hm : alphaMinus 3 = alphaPlus 3 := by
    unfold alphaMinus alphaPlus
    norm_num
  have hp : G.edgeDensity = alphaPlus 3 :=
    le_antisymm hiv.2 (by rw [← hm]; exact hiv.1)
  obtain ⟨P, h1, h2, h3⟩ := G.slice_rigidity 3 le_rfl hτ hη hp
  refine ⟨P, h1, fun i => ?_, h3⟩
  rw [h2 i]
  norm_num

end Graphon

end FlagAlgebras.MetaTheory
