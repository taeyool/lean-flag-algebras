import «LeanFlagAlgebras».Differential.DeleteEdge
import «LeanFlagAlgebras».Differential.Ensemble
import «LeanFlagAlgebras».Differential.Telescope
import «LeanFlagAlgebras».Differential.EdgeRound
import «LeanFlagAlgebras».FlagAlgebra.RandomHom
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Variational principles (Razborov §4.3: Theorems 4.3, 4.5, Corollary 4.6)

Let `M⃗ = (M₁, …, M_h)` be fixed models, `f ∈ C¹(U)` a goal function on an
open neighbourhood `U` of the density point
`a = (φ₀(M₁), …, φ₀(M_h))` of a positive homomorphism `φ₀`, and suppose `φ₀`
*locally minimises* `φ ↦ f(φ(M₁), …, φ(M_h))` over `Hom⁺(A⁰, ℝ)`. Razborov's
differential calculus turns this extremality into two "variational
principles" for the gradient element

  `Grad_{M⃗,a}(f) = ∑ᵢ (∂f/∂xᵢ)(a) · Mᵢ ∈ A⁰` (here `grad`):

* **Theorem 4.3** (`vertex_variational`): the random `1`-rooted extension
  `φ₀¹` of `φ₀` satisfies `P[φ₀¹(∂₁ Grad_{M⃗,a}(f)) = 0] = 1`;
* **Theorem 4.5** (`edge_variational`): if moreover `φ₀(ρ) > 0`, the random
  `E`-rooted extension satisfies `P[φ₀^E(∂_E Grad_{M⃗,a}(f)) ≥ 0] = 1`;
* **Corollary 4.6** (`downward_grad_vertex_eq_zero`,
  `downward_grad_edge_nonneg`): the "light" versions not referring to random
  homomorphisms — for every `g ∈ A¹`, `φ₀(⟦(∂₁ Grad_{M⃗,a}(f)) g⟧₁) = 0`,
  and for every `g ∈ C_sem(A^E)`, `φ₀(⟦(∂_E Grad_{M⃗,a}(f)) g⟧_E) ≥ 0`.

The ensembles are the probability measures `ℙ[φ₀]` on `PositiveHomSpace σ`
constructed in `FlagAlgebra.RandomHom` (Razborov's Definition 10 /
Theorem 3.5), whose defining property is
`∫ φ, φ(x) ∂ℙ[φ₀] = φ₀(⟦x⟧_σ) / φ₀(⟦1⟧_σ)`.

**Status: everything in this file is proved, with no `sorry` anywhere in the
development.** Theorems 4.3/4.5 are obtained by the following route replacing
Razborov's Theorems 3.9/3.12:

* `Ensemble.lean` provides the Stone–Weierstrass moment machinery: along
  *any* flag sequence realising `φ₀`, empirical integrals of coordinate
  polynomials converge to the corresponding `ℙ[φ₀]`-moments;
* `ae_nonneg_of_empirical_negPart` (this file) turns "the empirical average
  of `negPart(p^{(N,v)}(D))` tends to `0` along one such sequence" into
  "`φ(D) ≥ 0` `ℙ[φ₀]`-a.s.", by sandwiching the negative part between
  coordinate polynomials; combined with the vanishing mean (Lemma 4.2 c) for
  the vertex case) this gives the almost-sure statements;
* the purely finite-combinatorial cores `bad_vertex_negPart_tendsto_zero`
  and `bad_edge_negPart_tendsto_zero` (Razborov's estimates (29)–(33)) are
  proved at the end of this file: under local minimality no `ε`-bad set of
  roots/edges of positive density can persist, because deleting the bad
  ones — each step controlled by Lemmas 4.2 a) / 4.4 a), with the hitting
  estimates of `Hitting.lean` / `EdgeRound.lean` preserving badness — would
  drive `f` strictly below its local minimum via the `C¹` expansion.  The
  finite deletion machinery lives in `Telescope.lean` (vertex case) and
  `EdgeRound.lean` (edge case);
* Corollary 4.6 is then derived in full from Theorems 4.3/4.5 and the
  defining property of `ℙ[φ₀]`.
-/

open MeasureTheory Filter
open scoped Topology

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

variable {h : ℕ}

/-! ## The gradient element `Grad_{M⃗,a}(f)` -/

/-- The density point `(φ(M₁), …, φ(M_h)) ∈ ℝ^h` of a positive homomorphism
at a tuple of models. -/
noncomputable def densityPoint (Mv : Fin h → FinFlag ∅ₜ) (φ : PositiveHom ∅ₜ)
    : Fin h → ℝ
  :=
  fun i => φ ⟦basisVector (Mv i)⟧

/-- Razborov's gradient element
`Grad_{M⃗,a}(f) = ∑ᵢ (∂f/∂xᵢ)|_{x=a} · Mᵢ ∈ ℝℱ⁰`. -/
noncomputable def gradVec (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (a : Fin h → ℝ)
    : FlagVector ∅ₜ
  :=
  ∑ i : Fin h, (fderiv ℝ f a (Pi.single i 1)) • basisVector (Mv i)

/-- `Grad_{M⃗,a}(f)` as an element of the flag algebra `A⁰`. -/
noncomputable def grad (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (a : Fin h → ℝ)
    : FlagAlgebra ∅ₜ
  :=
  ⟦gradVec Mv f a⟧

/-! ## The one-vertex type is non-degenerate at every `φ₀` -/

/-- Every positive homomorphism gives the single-vertex flag the value `1`
(graphs are vertex uniform). -/
theorem positiveHom_vertexType_eq_one (φ₀ : PositiveHom ∅ₜ)
    : φ₀ ⟨vertexType⟩₀ = 1
  := by
  have h1 := sum_positiveHom_basisVector_flagWithSize_eq_one φ₀ 1 (Nat.zero_le 1)
  rw [Fintype.sum_unique] at h1
  dsimp only [flagType_asEmptyTypeAlgebra]
  have h2 : (vertexType.toEmptyTypeFlag : Flag ∅ₜ (Fin 1)) = default := Subsingleton.elim _ _
  rw [h2]
  exact h1

theorem positiveHom_vertexType_pos (φ₀ : PositiveHom ∅ₜ)
    : φ₀ ⟨vertexType⟩₀ > 0
  := by
  rw [positiveHom_vertexType_eq_one]
  norm_num

/-! ## Measurability of evaluation on the positive-homomorphism space -/

/-- Evaluation of a fixed flag-algebra element is a measurable function on
`PositiveHomSpace σ`. -/
theorem measurable_toPosHom_apply {n₀ : ℕ} {σ : FlagType (Fin n₀)} (x : FlagAlgebra σ)
    : Measurable (fun φ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom φ) x)
  := by
  rcases Quotient.exists_rep x with ⟨f, rfl⟩
  have heq : (fun φ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom φ) ⟦f⟧)
      = fun φ : PositiveHomSpace σ => ∑ F ∈ f.support, f F * (φ.val F) := by
    funext φ
    conv_lhs => rw [flagVector_eq_sum_basisVector f]
    rw [sum_quot, PositiveHom.map_sum]
    apply Finset.sum_congr rfl
    intro F _
    rw [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector]
  rw [heq]
  apply Finset.measurable_sum
  intro F _
  apply Measurable.const_mul
  exact Measurable.comp (flagDensitySpace_eval_measurable F) measurable_subtype_coe

/-! ## The negative part, and the reduction to a finite estimate -/

/-- The negative part `max (−x) 0` of a real number. -/
noncomputable def negPart (x : ℝ) : ℝ := max (-x) 0

theorem negPart_nonneg (x : ℝ) : 0 ≤ negPart x := le_max_right _ _

theorem negPart_eq_zero_iff {x : ℝ} : negPart x = 0 ↔ 0 ≤ x := by
  dsimp only [negPart]
  rw [max_eq_right_iff]
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem continuous_negPart : Continuous negPart :=
  Continuous.max continuous_neg continuous_const

theorem measurable_negPart_comp {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) : Measurable (fun a => negPart (f a)) :=
  Measurable.max hf.neg measurable_const

theorem abs_negPart_le (x : ℝ) : |negPart x| ≤ |x| := by
  rw [abs_of_nonneg (negPart_nonneg x)]
  dsimp only [negPart]
  apply max_le
  · exact neg_le_abs x
  · exact abs_nonneg x

/-- **The measure-theoretic reduction.** If, along some flag sequence
converging to `φ₀`, the empirical averages of the negative part of the
evaluation of `D` tend to `0` (the content of Razborov's finite estimates
(29)–(33)), then the evaluation of `D` is `ℙ[φ₀]`-a.e. nonnegative. Proven
from the Stone–Weierstrass moment machinery of `Ensemble.lean` alone. -/
theorem ae_nonneg_of_empirical_negPart {n₀ : ℕ} {σ : FlagType (Fin n₀)} (hn₀ : 1 ≤ n₀)
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0) (D : FlagVector σ)
    {s : FlagSeq ∅ₜ} (hs_conv : ConvergesTo s φ₀.coe)
    (hs_den : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    (hkfl : Tendsto (fun n => ∫ a, negPart (densityEvalFun D a)
      ∂((s n).toMeasure (hs_den n))) atTop (𝓝 0))
    : ∀ᵐ φ ∂(probMeasure_extend_emptyType_positiveHom φ₀ hσ).toMeasure,
        0 ≤ (PositiveHomSpace.toPosHom φ) ⟦D⟧
  := by
  set hD : FlagDensitySpace σ → ℝ := fun a => negPart (densityEvalFun D a) with hhD
  have hDc : Continuous hD := continuous_negPart.comp (continuous_densityEvalFun D)
  have hDm : Measurable hD := measurable_negPart_comp (measurable_densityEvalFun D)
  set B : ℝ := ∑ F ∈ D.support, |D F| with hB
  have hDb : ∀ a, |hD a| ≤ B := fun a =>
    le_trans (abs_negPart_le _) (abs_densityEvalFun_le D a)
  set μ := (probMeasure_extend_emptyType_positiveHom φ₀ hσ).toMeasure with hμ
  have hμ_int : Integrable (fun φ : PositiveHomSpace σ => hD φ.val) μ :=
    integrable_of_bounded (hDm.comp measurable_subtype_coe) B (fun φ => hDb _)
  -- the ℙ[φ₀]-integral of the negative part vanishes
  have hzero : ∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ = 0 := by
    have hnn : 0 ≤ ∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ :=
      integral_nonneg (fun φ => negPart_nonneg _)
    have hub : ∀ η : ℝ, 0 < η → ∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ ≤ 2 * η := by
      intro η hη
      obtain ⟨g, hgmem, hg⟩ := exists_coordAlgebra_near hD hDc hη
      obtain ⟨v, C, hC, hgm, hghom, hgapp⟩ := coordAlgebra_approx hgmem
      have hg_int : Integrable (fun φ : PositiveHomSpace σ => g φ.val) μ :=
        integrable_of_bounded (hgm.comp measurable_subtype_coe) ‖g‖ (fun φ => by
          have := g.norm_coe_le_norm φ.val
          rwa [Real.norm_eq_abs] at this)
      -- ℙ-side: ∫ hD ≤ ∫ g + η
      have h1 : ∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ
          ≤ (∫ φ, g (φ : PositiveHomSpace σ).val ∂μ) + η := by
        have h3 : (∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ)
            - ∫ φ, g (φ : PositiveHomSpace σ).val ∂μ ≤ η := by
          rw [← integral_sub hμ_int hg_int]
          have hb : (fun φ : PositiveHomSpace σ => hD φ.val - g φ.val) ≤ fun _ => η := by
            intro φ
            have h4 := hg φ.val
            have h5 : hD φ.val - g φ.val ≤ |g φ.val - hD φ.val| := by
              rw [abs_sub_comm]
              exact le_abs_self _
            linarith
          calc ∫ φ, (hD (φ : PositiveHomSpace σ).val - g φ.val) ∂μ
              ≤ ∫ _, η ∂μ := integral_mono (hμ_int.sub hg_int) (integrable_const η) hb
            _ = η := by simp [measure_univ]
        linarith
      have h4 : ∫ φ, g (φ : PositiveHomSpace σ).val ∂μ
          = φ₀ ⟦⟦v⟧⟧₀ / φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ :=
        integral_probMeasure_coordAlgebra hσ hghom
      have h5 := tendsto_integral_coordAlgebra hn₀ hσ hs_conv hs_den hgm hC hgapp
      -- finite side: ∫ g dPₙ ≤ ∫ hD dPₙ + η
      have h6 : ∀ n, (∫ a, g a ∂((s n).toMeasure (hs_den n)))
          ≤ (∫ a, hD a ∂((s n).toMeasure (hs_den n))) + η := by
        intro n
        have hint_g : Integrable ⇑g ((s n).toMeasure (hs_den n)) :=
          integrable_of_bounded hgm ‖g‖ (fun a => by
            have := g.norm_coe_le_norm a
            rwa [Real.norm_eq_abs] at this)
        have hint_h : Integrable hD ((s n).toMeasure (hs_den n)) :=
          integrable_of_bounded hDm B hDb
        have h7 : (∫ a, g a ∂((s n).toMeasure (hs_den n)))
            - ∫ a, hD a ∂((s n).toMeasure (hs_den n)) ≤ η := by
          rw [← integral_sub hint_g hint_h]
          have hb : (fun a => g a - hD a) ≤ fun _ => η := by
            intro a
            have h8 := hg a
            have h9 : g a - hD a ≤ |g a - hD a| := le_abs_self _
            linarith
          calc ∫ a, (g a - hD a) ∂((s n).toMeasure (hs_den n))
              ≤ ∫ _, η ∂((s n).toMeasure (hs_den n)) :=
                integral_mono (hint_g.sub hint_h) (integrable_const η) hb
            _ = η := by simp [measure_univ]
        linarith
      have h11 : φ₀ ⟦⟦v⟧⟧₀ / φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ ≤ 0 + η := by
        apply le_of_tendsto_of_tendsto' h5 (hkfl.add_const η) h6
      calc ∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ
          ≤ (∫ φ, g (φ : PositiveHomSpace σ).val ∂μ) + η := h1
        _ = φ₀ ⟦⟦v⟧⟧₀ / φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ + η := by rw [h4]
        _ ≤ (0 + η) + η := by linarith
        _ = 2 * η := by ring
    by_contra hne
    have hpos : 0 < ∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ :=
      lt_of_le_of_ne hnn (Ne.symm hne)
    have h12 := hub ((∫ φ, hD (φ : PositiveHomSpace σ).val ∂μ) / 4) (by linarith)
    linarith
  have hae0 : (fun φ : PositiveHomSpace σ => hD φ.val) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun φ => negPart_nonneg _)) hμ_int).mp hzero
  filter_upwards [hae0] with φ hφ
  have h8 : negPart (densityEvalFun D φ.val) = 0 := by
    have h9 : hD φ.val = 0 := by
      simpa using hφ
    simpa [hhD] using h9
  have h9 : 0 ≤ densityEvalFun D φ.val := negPart_eq_zero_iff.mp h8
  rwa [densityEvalFun_toPosHom] at h9

/-! ## The finite estimates: the combinatorial core -/

/-- **The finite core of Theorem 4.3** (Razborov's estimates (29)–(33)).
Under the extremality hypotheses, along any flag sequence realising `φ₀` the
empirical average of the negative part of `p^{(N,v)}(∂₁ Grad_{M⃗,a}(f))` over
a random root `v` tends to `0`.

Razborov's argument: were an `ε`-bad set of roots of density `≥ ε'` to
persist, deleting `⌊δ ℓₙ⌋` bad vertices one at a time — each step controlled
exactly by `vertex_deletion_density` (Lemma 4.2 a), proved in this
development) — would produce a sequence subconverging (via
`increasing_flagSeq_contain_convergent_subseq` and
`flagSeq_limit_mem_positiveHom`) to a positive homomorphism `ψ` whose density
point stays in `U` but with `ψ(Grad) ≤ φ₀(Grad) − εδ/2 + O(δ²)`, so the `C¹`
expansion of `f` at `a` contradicts local minimality. -/
theorem bad_vertex_negPart_tendsto_zero (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (φ₀ : PositiveHom ∅ₜ) {U : Set (Fin h → ℝ)} (hU : U ∈ nhds (densityPoint Mv φ₀))
    (hf : ContDiffOn ℝ 1 f U)
    (hmin : ∀ φ : PositiveHom ∅ₜ, densityPoint Mv φ ∈ U →
      f (densityPoint Mv φ₀) ≤ f (densityPoint Mv φ))
    {s : FlagSeq ∅ₜ} (hs_conv : ConvergesTo s φ₀.coe)
    (hs_den : ∀ n, flagDensity₁ vertexType.toEmptyTypeFlag (s n).2 > 0)
    : Tendsto (fun n => ∫ a, negPart (densityEvalFun
        (partialVertexVec (gradVec Mv f (densityPoint Mv φ₀))) a)
        ∂((s n).toMeasure (hs_den n))) atTop (𝓝 0)
  := by
  classical
  set a₀ : Fin h → ℝ := densityPoint Mv φ₀ with ha₀
  set gv : FlagVector ∅ₜ := gradVec Mv f a₀ with hgv
  set D : FlagVector vertexType := partialVertexVec gv with hDdef
  set B : ℝ := ∑ F ∈ D.support, |D F| with hBdef
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun F _ => abs_nonneg _
  clear_value B
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ F ∈ D.support, F.1 ≤ K + 1 :=
    ⟨D.support.sup (fun F => F.1),
      fun F hF => le_trans (Finset.le_sup hF) (Nat.le_succ _)⟩
  obtain ⟨Kg, hKg⟩ : ∃ Kg : ℕ, ∀ M ∈ gv.support, M.1 ≤ Kg :=
    ⟨gv.support.sup (fun M => M.1), fun M hM => Finset.le_sup hM⟩
  set KM : ℕ := (Finset.univ : Finset (Fin h)).sup (fun i => (Mv i).1) with hKMdef
  set C : Fin h → ℝ := fun i =>
    ∑ F ∈ (partialVertexVec (basisVector (Mv i))).support,
      |partialVertexVec (basisVector (Mv i)) F| with hCdef
  have hCnn : ∀ i, 0 ≤ C i := fun i => Finset.sum_nonneg fun F _ => abs_nonneg _
  set Cstar : ℝ := (∑ i, C i) + 1 with hCstardef
  have hCstar : 0 < Cstar := by
    have h1 : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hCnn i
    linarith
  have hCle : ∀ i, C i ≤ Cstar := by
    intro i
    have h1 : C i ≤ ∑ i, C i :=
      Finset.single_le_sum (fun i _ => hCnn i) (Finset.mem_univ i)
    linarith
  clear_value Cstar
  -- suppose the empirical averages do not vanish
  have hInn : ∀ n, 0 ≤ ∫ a, negPart (densityEvalFun D a)
      ∂((s n).toMeasure (hs_den n)) :=
    fun n => integral_nonneg fun a => negPart_nonneg _
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push_neg at hcon
  obtain ⟨ε₀, hε₀, hfreq⟩ := hcon
  have hfreq' : ∀ N, ∃ n ≥ N, ε₀ ≤ ∫ a, negPart (densityEvalFun D a)
      ∂((s n).toMeasure (hs_den n)) := by
    intro N
    obtain ⟨n, hn, hd⟩ := hfreq N
    refine ⟨n, hn, ?_⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hInn n)] at hd
  obtain ⟨φ₁, hφ₁mono, hφ₁⟩ := Filter.extraction_of_frequently_atTop
    (Filter.frequently_atTop.mpr hfreq')
  -- neighbourhood and C¹ Taylor data at the minimiser
  obtain ⟨rU, hrU, hballU⟩ := Metric.mem_nhds_iff.mp hU
  have hct : ContDiffAt ℝ 1 f a₀ := hf.contDiffAt hU
  have hdiff : DifferentiableAt ℝ f a₀ := hct.differentiableAt one_ne_zero
  have hFD : HasFDerivAt f (fderiv ℝ f a₀) a₀ := hdiff.hasFDerivAt
  have hlo := hFD.isLittleO
  have hcT : (0:ℝ) < ε₀ / (64 * Cstar) := div_pos hε₀ (by linarith)
  have hev := hlo.def hcT
  obtain ⟨rT, hrT, hTay⟩ := Metric.eventually_nhds_iff.mp hev
  -- choose the deletion fraction δ
  set B' : ℝ := B + 1 with hB'def
  have hB'pos : 0 < B' := by rw [hB'def]; linarith
  clear_value B'
  obtain ⟨δ, hδpos, hδhalf, hδbad, hδcorr, hδrad⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ δ ≤ ε₀ / (2 * B') ∧
        2 * B' * (K:ℝ) * δ ≤ ε₀ / 4 ∧ 2 * δ * Cstar < min rU rT := by
    have hmin' : (0:ℝ) < min rU rT := lt_min hrU hrT
    refine ⟨min (min (1/2) (ε₀ / (2 * B')))
      (min (ε₀ / (8 * B' * ((K:ℝ) + 1))) (min rU rT / (4 * Cstar))), ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · have h1 : min (min (1/2) (ε₀ / (2 * B')))
          (min (ε₀ / (8 * B' * ((K:ℝ) + 1))) (min rU rT / (4 * Cstar)))
          ≤ ε₀ / (8 * B' * ((K:ℝ) + 1)) :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : (0:ℝ) < 8 * B' * ((K:ℝ) + 1) := by positivity
      have h3 : 2 * B' * (K:ℝ) * (ε₀ / (8 * B' * ((K:ℝ) + 1))) ≤ ε₀ / 4 := by
        rw [← mul_div_assoc, div_le_div_iff₀ h2 (by norm_num : (0:ℝ) < 4)]
        nlinarith [mul_nonneg hB'pos.le hε₀.le]
      calc 2 * B' * (K:ℝ) * (min (min (1/2) (ε₀ / (2 * B')))
            (min (ε₀ / (8 * B' * ((K:ℝ) + 1))) (min rU rT / (4 * Cstar))))
          ≤ 2 * B' * (K:ℝ) * (ε₀ / (8 * B' * ((K:ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ ε₀ / 4 := h3
    · have h1 : min (min (1/2) (ε₀ / (2 * B')))
          (min (ε₀ / (8 * B' * ((K:ℝ) + 1))) (min rU rT / (4 * Cstar)))
          ≤ min rU rT / (4 * Cstar) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have h3 : 2 * (min rU rT / (4 * Cstar)) * Cstar < min rU rT := by
        have h4 : 2 * (min rU rT / (4 * Cstar)) * Cstar
            = min rU rT * (2 * Cstar) / (4 * Cstar) := by
          ring
        rw [h4, div_lt_iff₀ (by positivity)]
        nlinarith [mul_pos hmin' hCstar]
      calc 2 * (min (min (1/2) (ε₀ / (2 * B')))
            (min (ε₀ / (8 * B' * ((K:ℝ) + 1))) (min rU rT / (4 * Cstar)))) * Cstar
          ≤ 2 * (min rU rT / (4 * Cstar)) * Cstar := by
            apply mul_le_mul_of_nonneg_right ?_ hCstar.le
            apply mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ < min rU rT := h3
  -- the largeness threshold
  obtain ⟨Nδ, hNδ⟩ : ∃ Nδ : ℕ, 2 ≤ δ * (Nδ:ℝ) := by
    obtain ⟨Nδ, hNδ⟩ := exists_nat_ge (2 / δ)
    refine ⟨Nδ, ?_⟩
    rw [div_le_iff₀ hδpos] at hNδ
    linarith
  set J₀ : ℕ := max (max (2*Kg + 2) (2*K + 4)) (max (2*KM + 2) Nδ) with hJ₀def
  -- the per-index deleted hosts
  have hkey : ∀ j : ℕ, ∃ Q : FinFlag ∅ₜ,
      J₀ ≤ j →
      ((j ≤ 2 * Q.1) ∧
       (densityEval gv Q ≤ densityEval gv (s (φ₁ j)) - ε₀ * δ / 8) ∧
       (∀ i : Fin h, |(flagDensity₁ (Mv i).2 Q.2 : ℝ)
          - (flagDensity₁ (Mv i).2 (s (φ₁ j)).2 : ℝ)| ≤ 2 * δ * Cstar)) := by
    intro j
    by_cases hj : J₀ ≤ j
    swap
    · exact ⟨⟨0, default⟩, fun hj' => absurd hj' hj⟩
    set n := φ₁ j with hn
    set L := (s n).1 with hLdef
    have hLj : j ≤ L := le_trans hφ₁mono.le_apply (hs_conv.1.id_le n)
    have hJL : J₀ ≤ L := le_trans hj hLj
    have hLg : 2 * Kg + 2 ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hJL
    have hLK : 2 * K + 4 ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hJL
    have hLM : 2 * KM + 2 ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hJL
    have hLNδ : Nδ ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hJL
    have hδL : 2 ≤ δ * (L : ℝ) := by
      refine le_trans hNδ ?_
      apply mul_le_mul_of_nonneg_left ?_ hδpos.le
      exact_mod_cast hLNδ
    have h1L : 1 ≤ L := by omega
    have hLpos : (0:ℝ) < (L:ℝ) := by
      have h2 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast h1L
      linarith
    set N : LabeledGraph ∅ₜ (Fin L) := (s n).2.out with hNdef
    -- the empirical average is a root average
    have h2 : ε₀ ≤ ∫ a, negPart (densityEvalFun D a)
        ∂((s (φ₁ j)).toMeasure (hs_den (φ₁ j))) := hφ₁ j
    rw [← hn] at h2
    have h3 := integral_toMeasure_eq_root_average' (s n) h1L (hs_den n) D negPart
      continuous_negPart.measurable
      (fun a => le_trans (abs_negPart_le _) (abs_densityEvalFun_le D a))
    rw [h3] at h2
    have havg : ε₀ ≤ (1 / (L : ℝ)) * ∑ r, max (-(pEval D N r)) 0 := h2
    -- run one deletion round
    obtain ⟨W, hW2, hWr, hWdesc⟩ := exists_deleted_host N gv hε₀ hδpos hδhalf hB'pos
      (by show ∑ F ∈ D.support, |D F| ≤ B'
          rw [← hBdef, hB'def]
          linarith)
      hK hKg hδbad hδcorr hLg hLK hδL havg
    have hcard : Fintype.card {u : Fin L // u ∉ W} = L - W.card := by
      rw [card_deleteFinset, Fintype.card_fin]
    refine ⟨⟨L - W.card, getCanonicalFlag (deleteFinset N W) hcard⟩, fun _ => ⟨?_, ?_, ?_⟩⟩
    · show j ≤ 2 * (L - W.card)
      omega
    · show densityEval gv ⟨L - W.card, getCanonicalFlag (deleteFinset N W) hcard⟩
        ≤ densityEval gv (s n) - ε₀ * δ / 8
      rw [densityEval_getCanonicalFlag]
      calc pdensityVec gv (deleteFinset N W)
          ≤ pdensityVec gv N - ε₀ * δ / 8 := hWdesc
        _ = densityEval gv (s n) - ε₀ * δ / 8 := by
            rw [hNdef, pdensityVec_out gv (s n)]
    · intro i
      show |(flagDensity₁ (Mv i).2 (getCanonicalFlag (deleteFinset N W) hcard) : ℝ)
          - (flagDensity₁ (Mv i).2 (s n).2 : ℝ)| ≤ 2 * δ * Cstar
      have e1 : pdensityVec (basisVector (Mv i)) (deleteFinset N W)
          = (flagDensity₁ (Mv i).2 (getCanonicalFlag (deleteFinset N W) hcard) : ℝ) :=
        Eq.trans
          (densityEval_getCanonicalFlag (basisVector (Mv i)) (deleteFinset N W) hcard).symm
          (densityEval_basisVector (Mv i)
            ⟨L - W.card, getCanonicalFlag (deleteFinset N W) hcard⟩)
      have e2 : pdensityVec (basisVector (Mv i)) N
          = (flagDensity₁ (Mv i).2 (s n).2 : ℝ) := by
        rw [pdensityVec_basisVector, hNdef, Quotient.out_eq]
      have hstab := pdensityVec_deleteFinset_stability (basisVector (Mv i)) N W ?hWlt ?hfit
      case hWlt =>
        rw [Fintype.card_fin]
        omega
      case hfit =>
        intro M hM
        rw [Fintype.card_fin]
        have hMi : M = Mv i := by
          have h5 := hM
          rw [basisVector_support] at h5
          exact Finset.mem_singleton.mp h5
        subst hMi
        have h6 : (Mv i).1 ≤ KM :=
          Finset.le_sup (f := fun i => (Mv i).1) (Finset.mem_univ i)
        omega
      have hstab' : |pdensityVec (basisVector (Mv i)) (deleteFinset N W)
          - pdensityVec (basisVector (Mv i)) N|
          ≤ (W.card : ℝ) * C i / ((L : ℝ) - W.card) := by
        rw [Fintype.card_fin] at hstab
        exact hstab
      have hWhalf : (W.card : ℝ) ≤ (L : ℝ) / 2 := by
        have h8 : ((2 * W.card : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hW2
        push_cast at h8
        linarith
      have hbound : (W.card : ℝ) * C i / ((L : ℝ) - W.card) ≤ 2 * δ * Cstar := by
        have hd : (L : ℝ) / 2 ≤ (L : ℝ) - W.card := by linarith
        have hdpos : (0:ℝ) < (L : ℝ) / 2 := by linarith
        calc (W.card : ℝ) * C i / ((L : ℝ) - W.card)
            ≤ (δ * L) * Cstar / ((L : ℝ) / 2) := by
              apply div_le_div₀ (by positivity) ?_ hdpos hd
              exact mul_le_mul hWr (hCle i) (hCnn i) (by positivity)
          _ = 2 * δ * Cstar := by
              field_simp
      calc |(flagDensity₁ (Mv i).2 (getCanonicalFlag (deleteFinset N W) hcard) : ℝ)
            - (flagDensity₁ (Mv i).2 (s n).2 : ℝ)|
          = |pdensityVec (basisVector (Mv i)) (deleteFinset N W)
            - pdensityVec (basisVector (Mv i)) N| := by rw [e1, e2]
        _ ≤ (W.card : ℝ) * C i / ((L : ℝ) - W.card) := hstab'
        _ ≤ 2 * δ * Cstar := hbound
  -- assemble the deleted flag sequence
  choose Qf hQf using hkey
  set QSeq : FlagSeq ∅ₜ := fun j => Qf (J₀ + j) with hQSeqdef
  have hq1 : ∀ j, J₀ + j ≤ 2 * (QSeq j).1 :=
    fun j => ((hQf (J₀ + j)) (by omega)).1
  have hq2 : ∀ j, densityEval gv (QSeq j)
      ≤ densityEval gv (s (φ₁ (J₀ + j))) - ε₀ * δ / 8 :=
    fun j => ((hQf (J₀ + j)) (by omega)).2.1
  have hq3 : ∀ j i, |(flagDensity₁ (Mv i).2 (QSeq j).2 : ℝ)
      - (flagDensity₁ (Mv i).2 (s (φ₁ (J₀ + j))).2 : ℝ)| ≤ 2 * δ * Cstar :=
    fun j i => ((hQf (J₀ + j)) (by omega)).2.2 i
  have hsz : Tendsto (fun j => (QSeq j).1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    refine ⟨2 * b, fun j hj => ?_⟩
    have h1 := hq1 j
    omega
  obtain ⟨ψ, hψmono, hψsz⟩ :=
    exists_strictMono_comp_strictMono (fun j => (QSeq j).1) hsz
  have hIncQ : Increases (QSeq ∘ ψ) := hψsz
  obtain ⟨aQ, χ, hχmono, hconvQ⟩ :=
    increasing_flagSeq_contain_convergent_subseq (QSeq ∘ ψ) hIncQ
  obtain ⟨ψlim, hψcoe⟩ := flagSeq_limit_mem_positiveHom _ hconvQ
  set jdx : ℕ → ℕ := fun k => ψ (χ k) with hjdxdef
  set ndx : ℕ → ℕ := fun k => φ₁ (J₀ + jdx k) with hndxdef
  have hndxmono : StrictMono ndx := by
    intro k1 k2 hk
    apply hφ₁mono
    have h1 := hψmono (hχmono hk)
    show J₀ + ψ (χ k1) < J₀ + ψ (χ k2)
    omega
  -- coordinatewise limits
  have hQlim := (flagSeq_convergesTo_iff.mp hconvQ).2
  have hslim := (flagSeq_convergesTo_iff.mp hs_conv).2
  have hL1 : ∀ F : FinFlag ∅ₜ, Tendsto
      (fun k => (flagDensity₁ F.2 (QSeq (jdx k)).2 : ℝ)) atTop (𝓝 (aQ F)) :=
    fun F => hQlim F
  have hL2 : ∀ F : FinFlag ∅ₜ, Tendsto
      (fun k => (flagDensity₁ F.2 (s (ndx k)).2 : ℝ)) atTop (𝓝 (φ₀.coe F)) :=
    fun F => (hslim F).comp hndxmono.tendsto_atTop
  -- the limit density point stays 2δC★-close to a₀
  have hy : ∀ i : Fin h, |aQ (Mv i) - φ₀.coe (Mv i)| ≤ 2 * δ * Cstar := by
    intro i
    have h1 : Tendsto (fun k => |(flagDensity₁ (Mv i).2 (QSeq (jdx k)).2 : ℝ)
        - (flagDensity₁ (Mv i).2 (s (ndx k)).2 : ℝ)|) atTop
        (𝓝 |aQ (Mv i) - φ₀.coe (Mv i)|) :=
      ((hL1 (Mv i)).sub (hL2 (Mv i))).abs
    apply le_of_tendsto h1
    exact Filter.Eventually.of_forall (fun k => hq3 (jdx k) i)
  -- the gradient combination strictly drops in the limit
  have hgrad_le : ψlim ⟦gv⟧ ≤ φ₀ ⟦gv⟧ - ε₀ * δ / 8 := by
    have h1 : Tendsto (fun k => densityEval gv (QSeq (jdx k))) atTop
        (𝓝 (densityEvalFun gv aQ)) :=
      tendsto_finset_sum gv.support
        (fun M (_ : M ∈ gv.support) => (hL1 M).const_mul (gv M))
    have h4 : Tendsto (fun k => densityEval gv (s (ndx k))) atTop
        (𝓝 (densityEvalFun gv φ₀.coe)) :=
      tendsto_finset_sum gv.support
        (fun M (_ : M ∈ gv.support) => (hL2 M).const_mul (gv M))
    have h5 : densityEvalFun gv aQ ≤ densityEvalFun gv φ₀.coe - ε₀ * δ / 8 := by
      apply le_of_tendsto_of_tendsto' h1 (h4.sub_const _)
      intro k
      exact hq2 (jdx k)
    rw [densityEvalFun_hom gv φ₀] at h5
    have h7 : densityEvalFun gv aQ = ψlim ⟦gv⟧ := by
      rw [← hψcoe]
      exact densityEvalFun_hom gv ψlim
    rw [h7] at h5
    exact h5
  -- density points
  set y : Fin h → ℝ := densityPoint Mv ψlim with hydef
  have hyi : ∀ i, y i = aQ (Mv i) := by
    intro i
    show ψlim ⟦basisVector (Mv i)⟧ = aQ (Mv i)
    rw [← PositiveHom.coe_flag, hψcoe]
  have ha₀i : ∀ i, a₀ i = φ₀.coe (Mv i) := by
    intro i
    show φ₀ ⟦basisVector (Mv i)⟧ = φ₀.coe (Mv i)
    rw [← PositiveHom.coe_flag]
  have hdist : ∀ i, |y i - a₀ i| ≤ 2 * δ * Cstar := by
    intro i
    rw [hyi i, ha₀i i]
    exact hy i
  have hnorm : ‖y - a₀‖ ≤ 2 * δ * Cstar := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact hdist i
  have hyU : y ∈ U := by
    apply hballU
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖y - a₀‖ ≤ 2 * δ * Cstar := hnorm
      _ < min rU rT := hδrad
      _ ≤ rU := min_le_left _ _
  have hmin2 : f a₀ ≤ f y := hmin ψlim hyU
  -- the C¹ expansion at radius ‖y − a₀‖
  have hyT : dist y a₀ < rT := by
    rw [dist_eq_norm]
    calc ‖y - a₀‖ ≤ 2 * δ * Cstar := hnorm
      _ < min rU rT := hδrad
      _ ≤ rT := min_le_right _ _
  have hTay' := hTay hyT
  have hx : y - a₀ = ∑ i, ((y - a₀) i) • Pi.single i (1 : ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single (y - a₀)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hfd : (fderiv ℝ f a₀) (y - a₀)
      = ∑ i, ((y - a₀) i) * (fderiv ℝ f a₀ (Pi.single i 1)) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
  have hgv_eval : ∀ φ : PositiveHom ∅ₜ, φ ⟦gv⟧
      = ∑ i, (fderiv ℝ f a₀ (Pi.single i 1)) * densityPoint Mv φ i := by
    intro φ
    rw [hgv]
    show φ ⟦∑ i, (fderiv ℝ f a₀ (Pi.single i 1)) • basisVector (Mv i)⟧ = _
    rw [sum_quot, PositiveHom.map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_quot, PositiveHom.map_smul]
    rfl
  have hdir : (fderiv ℝ f a₀) (y - a₀) ≤ -(ε₀ * δ / 8) := by
    have h8 : ψlim ⟦gv⟧ - φ₀ ⟦gv⟧ ≤ -(ε₀ * δ / 8) := by linarith [hgrad_le]
    have h9 : (fderiv ℝ f a₀) (y - a₀) = ψlim ⟦gv⟧ - φ₀ ⟦gv⟧ := by
      rw [hfd, hgv_eval ψlim, hgv_eval φ₀, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h10 : (y - a₀) i = densityPoint Mv ψlim i - densityPoint Mv φ₀ i := by
        rw [Pi.sub_apply]
      rw [h10]
      ring
    linarith [h9.le, h9.ge, h8]
  have hTb : ‖f y - f a₀ - (fderiv ℝ f a₀) (y - a₀)‖
      ≤ ε₀ / (64 * Cstar) * ‖y - a₀‖ := hTay'
  rw [Real.norm_eq_abs] at hTb
  have habs := (abs_le.mp hTb).2
  have hnormb : ε₀ / (64 * Cstar) * ‖y - a₀‖
      ≤ ε₀ / (64 * Cstar) * (2 * δ * Cstar) :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsmall : ε₀ / (64 * Cstar) * (2 * δ * Cstar) = ε₀ * δ / 32 := by
    field_simp
    ring
  have hεδ : 0 < ε₀ * δ := mul_pos hε₀ hδpos
  linarith [hmin2, habs, hdir, hnormb, hsmall.le, hsmall.ge, hεδ]

set_option maxHeartbeats 3200000 in
/-- **The finite core of Theorem 4.5**: the edge analogue of
`bad_vertex_negPart_tendsto_zero`, with bad edges deleted inside a random
vertex subset of size `⌊δ^{1/2} ℓₙ⌋` (Razborov, p. 40) and each deletion step
controlled by `edge_deletion_density` (Lemma 4.4 a)). -/
theorem bad_edge_negPart_tendsto_zero (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (φ₀ : PositiveHom ∅ₜ) {U : Set (Fin h → ℝ)} (hU : U ∈ nhds (densityPoint Mv φ₀))
    (hf : ContDiffOn ℝ 1 f U)
    (hmin : ∀ φ : PositiveHom ∅ₜ, densityPoint Mv φ ∈ U →
      f (densityPoint Mv φ₀) ≤ f (densityPoint Mv φ))
    (hρ : φ₀ ⟨edgeType⟩₀ > 0)
    {s : FlagSeq ∅ₜ} (hs_conv : ConvergesTo s φ₀.coe)
    (hs_den : ∀ n, flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 > 0)
    : Tendsto (fun n => ∫ a, negPart (densityEvalFun
        (partialEdgeVec (gradVec Mv f (densityPoint Mv φ₀))) a)
        ∂((s n).toMeasure (hs_den n))) atTop (𝓝 0)
  := by
  classical
  set a₀ : Fin h → ℝ := densityPoint Mv φ₀ with ha₀
  set gv : FlagVector ∅ₜ := gradVec Mv f a₀ with hgv
  set D : FlagVector edgeType := partialEdgeVec gv with hDdef
  set B : ℝ := ∑ F ∈ D.support, |D F| with hBdef
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun F _ => abs_nonneg _
  clear_value B
  set B' : ℝ := B + 1 with hB'def
  have hB'pos : 0 < B' := by rw [hB'def]; linarith
  have hBb : B ≤ B' := by rw [hB'def]; linarith
  clear_value B'
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ F ∈ D.support, F.1 ≤ K + 2 :=
    ⟨D.support.sup (fun F => F.1),
      fun F hF => le_trans (Finset.le_sup (f := fun F : FinFlag edgeType => F.1) hF)
        (by omega)⟩
  obtain ⟨Kg, hKg⟩ : ∃ Kg : ℕ, ∀ M ∈ gv.support, M.1 ≤ Kg :=
    ⟨gv.support.sup (fun M => M.1), fun M hM => Finset.le_sup hM⟩
  set KM : ℕ := (Finset.univ : Finset (Fin h)).sup (fun i => (Mv i).1) with hKMdef
  set C : Fin h → ℝ := fun i =>
    ∑ F ∈ (partialEdgeVec (basisVector (Mv i))).support,
      |partialEdgeVec (basisVector (Mv i)) F| with hCdef
  have hCnn : ∀ i, 0 ≤ C i := fun i => Finset.sum_nonneg fun F _ => abs_nonneg _
  set Cstar : ℝ := (∑ i, C i) + 1 with hCstardef
  have hCstar : 0 < Cstar := by
    have h1 : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hCnn i
    linarith
  have hCle : ∀ i, C i ≤ Cstar := by
    intro i
    have h1 : C i ≤ ∑ i, C i :=
      Finset.single_le_sum (fun i _ => hCnn i) (Finset.mem_univ i)
    linarith
  clear_value Cstar
  -- the limiting edge density is positive
  set ρF : FinFlag ∅ₜ := ⟨2, edgeType.toEmptyTypeFlag⟩ with hρFdef
  have hρpos : 0 < φ₀.coe ρF := hρ
  set ρlim : ℝ := φ₀.coe ρF with hρposdef
  have hρpos2 : 0 < ρlim := hρpos
  have hρlim : Tendsto (fun n => (flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 : ℝ))
      atTop (𝓝 ρlim) := (flagSeq_convergesTo_iff.mp hs_conv).2 ρF
  clear_value ρlim
  -- suppose the empirical averages do not vanish
  have hInn : ∀ n, 0 ≤ ∫ a, negPart (densityEvalFun D a)
      ∂((s n).toMeasure (hs_den n)) :=
    fun n => integral_nonneg fun a => negPart_nonneg _
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push_neg at hcon
  obtain ⟨ε₀, hε₀, hfreq⟩ := hcon
  have hfreq' : ∀ N, ∃ n ≥ N, ε₀ ≤ ∫ a, negPart (densityEvalFun D a)
      ∂((s n).toMeasure (hs_den n)) := by
    intro N
    obtain ⟨n, hn, hd⟩ := hfreq N
    refine ⟨n, hn, ?_⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hInn n)] at hd
  obtain ⟨φ₁, hφ₁mono, hφ₁⟩ := Filter.extraction_of_frequently_atTop
    (Filter.frequently_atTop.mpr hfreq')
  -- neighbourhood and C¹ Taylor data at the minimiser
  obtain ⟨rU, hrU, hballU⟩ := Metric.mem_nhds_iff.mp hU
  have hct : ContDiffAt ℝ 1 f a₀ := hf.contDiffAt hU
  have hdiff : DifferentiableAt ℝ f a₀ := hct.differentiableAt one_ne_zero
  have hFD : HasFDerivAt f (fderiv ℝ f a₀) a₀ := hdiff.hasFDerivAt
  have hlo := hFD.isLittleO
  have hcT : (0:ℝ) < ε₀^2 * ρlim / (4096 * B' * Cstar) := by positivity
  have hev := hlo.def hcT
  obtain ⟨rT, hrT, hTay⟩ := Metric.eventually_nhds_iff.mp hev
  -- the deletion-fraction parameter σ
  set CB : ℝ := B' * (2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) + 1 with hCBdef
  have hCBpos : 0 < CB := by
    have h1 : (0:ℝ) ≤ B' * (2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) := by positivity
    linarith
  obtain ⟨σ, hσpos, hσhalf, hσcorr, hσrad⟩ :
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1/2 ∧
        B' * (2 * ((K:ℝ) + 2) * σ + 4 * ((K:ℝ) + 2)^2 * σ^2) ≤ ε₀/4 ∧
        4 * σ^2 * Cstar < min rU rT := by
    have hmin2 : (0:ℝ) < min rU rT := lt_min hrU hrT
    refine ⟨min (min (1/2) (ε₀ / (4 * CB))) (min rU rT / (4 * Cstar + 1)),
      ?_, ?_, ?_, ?_⟩
    · positivity
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · set σ' := min (min (1/2) (ε₀ / (4 * CB))) (min rU rT / (4 * Cstar + 1)) with hσ'
      have hσ'pos : 0 < σ' := by rw [hσ']; positivity
      have h1 : σ' ≤ 1/2 := le_trans (min_le_left _ _) (min_le_left _ _)
      have h2 : σ' ≤ ε₀ / (4 * CB) := le_trans (min_le_left _ _) (min_le_right _ _)
      have h3 : σ'^2 ≤ σ' := by nlinarith
      have h4 : B' * (2 * ((K:ℝ) + 2) * σ' + 4 * ((K:ℝ) + 2)^2 * σ'^2)
          ≤ B' * (2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) * σ' := by
        have h5 : 2 * ((K:ℝ) + 2) * σ' + 4 * ((K:ℝ) + 2)^2 * σ'^2
            ≤ (2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) * σ' := by
          have h6 : 4 * ((K:ℝ) + 2)^2 * σ'^2 ≤ 4 * ((K:ℝ) + 2)^2 * σ' :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
          nlinarith
        calc B' * (2 * ((K:ℝ) + 2) * σ' + 4 * ((K:ℝ) + 2)^2 * σ'^2)
            ≤ B' * ((2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) * σ') :=
              mul_le_mul_of_nonneg_left h5 hB'pos.le
          _ = B' * (2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) * σ' := by ring
      have h7 : B' * (2 * ((K:ℝ) + 2) + 4 * ((K:ℝ) + 2)^2) * σ' ≤ CB * σ' := by
        apply mul_le_mul_of_nonneg_right ?_ hσ'pos.le
        rw [hCBdef]
        linarith
      have h8 : CB * σ' ≤ CB * (ε₀ / (4 * CB)) :=
        mul_le_mul_of_nonneg_left h2 hCBpos.le
      have h9 : CB * (ε₀ / (4 * CB)) = ε₀ / 4 := by
        field_simp
      linarith
    · set σ' := min (min (1/2) (ε₀ / (4 * CB))) (min rU rT / (4 * Cstar + 1)) with hσ'
      have hσ'pos : 0 < σ' := by rw [hσ']; positivity
      have h1 : σ' ≤ 1/2 := le_trans (min_le_left _ _) (min_le_left _ _)
      have h2 : σ' ≤ min rU rT / (4 * Cstar + 1) := min_le_right _ _
      have h3 : σ'^2 ≤ σ' := by nlinarith
      calc 4 * σ'^2 * Cstar ≤ 4 * σ' * Cstar := by nlinarith
        _ ≤ 4 * (min rU rT / (4 * Cstar + 1)) * Cstar := by
            apply mul_le_mul_of_nonneg_right ?_ hCstar.le
            nlinarith
        _ < min rU rT := by
            rw [show (4:ℝ) * (min rU rT / (4 * Cstar + 1)) * Cstar
              = min rU rT * (4 * Cstar) / (4 * Cstar + 1) from by ring]
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [hmin2, hCstar, mul_pos hmin2 hCstar]
  -- the drop constant
  set Δc : ℝ := ε₀^2 * (ρlim/2) * σ^2 / (128 * B') with hΔcdef
  have hΔcpos : 0 < Δc := by
    rw [hΔcdef]
    positivity
  -- the largeness threshold
  obtain ⟨Nσ, hNσ⟩ : ∃ Nσ : ℕ, 4 ≤ σ * (Nσ:ℝ) := by
    obtain ⟨Nσ, hNσ⟩ := exists_nat_ge (4 / σ)
    refine ⟨Nσ, ?_⟩
    rw [div_le_iff₀ hσpos] at hNσ
    linarith
  -- the edge density is eventually at least ρlim/2
  obtain ⟨Nρ, hNρ⟩ : ∃ Nρ : ℕ, ∀ n ≥ Nρ,
      ρlim/2 ≤ (flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 : ℝ) := by
    have h1 : ∀ᶠ n in atTop, (fun n =>
        (flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 : ℝ)) n ∈ Metric.ball ρlim (ρlim/2) :=
      hρlim (Metric.ball_mem_nhds ρlim (by linarith : (0:ℝ) < ρlim/2))
    obtain ⟨Nρ, hNρ⟩ := Filter.eventually_atTop.mp h1
    refine ⟨Nρ, fun n hn => ?_⟩
    have h2 := hNρ n hn
    rw [Metric.mem_ball, Real.dist_eq] at h2
    have h3 := abs_lt.mp h2
    linarith [h3.1]
  set J₀ : ℕ := max (max (K + 2) (max Kg KM)) (max 4 (max Nσ Nρ)) with hJ₀def
  -- the per-index deleted hosts
  have hkey : ∀ j : ℕ, ∃ Q : FinFlag ∅ₜ,
      J₀ ≤ j →
      ((Q.1 = (s (φ₁ j)).1) ∧
       (densityEval gv Q ≤ densityEval gv (s (φ₁ j)) - Δc) ∧
       (∀ i : Fin h, |(flagDensity₁ (Mv i).2 Q.2 : ℝ)
          - (flagDensity₁ (Mv i).2 (s (φ₁ j)).2 : ℝ)| ≤ 4 * σ^2 * Cstar)) := by
    intro j
    by_cases hj : J₀ ≤ j
    swap
    · exact ⟨⟨0, default⟩, fun hj' => absurd hj' hj⟩
    set n := φ₁ j with hn
    set L := (s n).1 with hLdef
    have hLj : j ≤ L := le_trans hφ₁mono.le_apply (hs_conv.1.id_le n)
    have hJL : J₀ ≤ L := le_trans hj hLj
    have hLK : K + 2 ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hJL
    have hLg : Kg ≤ L := le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_right _ _)) (le_max_left _ _)) hJL
    have hLM : KM ≤ L := le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) (le_max_left _ _)) hJL
    have hL4 : 4 ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hJL
    have hLNσ : Nσ ≤ L := le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_right _ _)) (le_max_right _ _)) hJL
    have hσL : 4 ≤ σ * (L : ℝ) := by
      refine le_trans hNσ ?_
      apply mul_le_mul_of_nonneg_left ?_ hσpos.le
      exact_mod_cast hLNσ
    have hnNρ : Nρ ≤ n := by
      have h1 : Nρ ≤ j := le_trans (le_trans (le_trans (le_max_right _ _)
        (le_max_right _ _)) (le_max_right _ _)) hj
      exact le_trans h1 hφ₁mono.le_apply
    have h2L : 2 ≤ (s n).1 := by omega
    set N : LabeledGraph ∅ₜ (Fin L) := (s n).2.out with hNdef
    -- the empirical average is a pair average
    have h2 : ε₀ ≤ ∫ a, negPart (densityEvalFun D a)
        ∂((s (φ₁ j)).toMeasure (hs_den (φ₁ j))) := hφ₁ j
    rw [← hn] at h2
    have h3 := integral_toMeasure_eq_pair_average' (s n) h2L (hs_den n) D negPart
      continuous_negPart.measurable
      (fun a => le_trans (abs_negPart_le _) (abs_densityEvalFun_le D a))
    rw [h3] at h2
    -- the ordered edge count is bounded below via the density
    have hpairs : (ρlim/2) * (L:ℝ) * ((L:ℝ) - 1) ≤ ((adjPairs N).card : ℝ) := by
      have h4 := card_adjPairs_eq' (s n) h2L
      have h5 : ((adjPairs ((s n).2.out)).card : ℝ)
          = (flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 : ℝ)
            * (((s n).1 : ℝ) * (((s n).1 : ℝ) - 1)) := by
        exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) h4
      have h6 : ρlim/2 ≤ (flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 : ℝ) :=
        hNρ n hnNρ
      have h7 : (0:ℝ) ≤ (L:ℝ) * ((L:ℝ) - 1) := by
        have h8 : (4:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL4
        nlinarith
      calc (ρlim/2) * (L:ℝ) * ((L:ℝ) - 1)
          = (ρlim/2) * ((L:ℝ) * ((L:ℝ) - 1)) := by ring
        _ ≤ (flagDensity₁ edgeType.toEmptyTypeFlag (s n).2 : ℝ)
            * ((L:ℝ) * ((L:ℝ) - 1)) := mul_le_mul_of_nonneg_right h6 h7
        _ = ((adjPairs N).card : ℝ) := by
            rw [hNdef]
            rw [h5]
    -- run the deletion round
    obtain ⟨Dd, hDadj, hDuniq, hDub, hDdrop⟩ := exists_deleted_host_edge N gv
      hε₀ hσpos hσhalf hB'pos
      (by show ∑ F ∈ D.support, |D F| ≤ B'
          rw [← hBdef]
          linarith)
      hK (fun M hM => le_trans (hKg M hM) hLg)
      hσcorr hLK hσL (by positivity) hpairs h2
    refine ⟨⟨L, (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L)⟩, fun _ => ⟨rfl, ?_, ?_⟩⟩
    · -- the density of the gradient combination drops
      have hQN : (⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩ : FinFlag ∅ₜ) = s n := by
        rw [hNdef, Quotient.out_eq]
        rfl
      show densityEval gv ⟨L, (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L)⟩
        ≤ densityEval gv (s n) - Δc
      rw [← hQN]
      exact hDdrop
    · -- every model density moves by at most 4σ²C★
      intro i
      show |(flagDensity₁ (Mv i).2 (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L) : ℝ)
          - (flagDensity₁ (Mv i).2 (s n).2 : ℝ)| ≤ 4 * σ^2 * Cstar
      have e1 : (flagDensity₁ (Mv i).2 (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L) : ℝ)
          = densityEval (basisVector (Mv i))
              ⟨L, (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L)⟩ :=
        (densityEval_basisVector (Mv i)
          ⟨L, (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L)⟩).symm
      have e2 : densityEval (basisVector (Mv i)) ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩
          = (flagDensity₁ (Mv i).2 (s n).2 : ℝ) := by
        rw [densityEval_basisVector, hNdef, Quotient.out_eq]
      have hstab := edge_stability (basisVector (Mv i)) N ?hsuppi (by omega)
        Dd hDadj hDuniq
      case hsuppi =>
        intro M hM
        rw [basisVector_support, Finset.mem_singleton] at hM
        subst hM
        have h6 : (Mv i).1 ≤ KM :=
          Finset.le_sup (f := fun i => (Mv i).1) (Finset.mem_univ i)
        omega
      have hb : |densityEval (basisVector (Mv i))
            ⟨L, (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L)⟩
          - densityEval (basisVector (Mv i)) ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩|
          ≤ (Dd.card : ℝ) * C i * 2 / ((L:ℝ) * ((L:ℝ) - 1)) := hstab
      have hL4r : (4:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL4
      have hLL1 : (0:ℝ) < (L:ℝ) * ((L:ℝ) - 1) := by nlinarith
      have hbound : (Dd.card : ℝ) * C i * 2 / ((L:ℝ) * ((L:ℝ) - 1))
          ≤ 4 * σ^2 * Cstar := by
        rw [div_le_iff₀ hLL1]
        have h7 : (L:ℝ)^2 ≤ 2 * ((L:ℝ) * ((L:ℝ) - 1)) := by nlinarith
        calc (Dd.card : ℝ) * C i * 2
            ≤ (σ^2 * (L:ℝ)^2) * C i * 2 := by
              apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_right hDub (hCnn i)
          _ ≤ (σ^2 * (2 * ((L:ℝ) * ((L:ℝ) - 1)))) * Cstar * 2 := by
              apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
              apply mul_le_mul ?_ (hCle i) (hCnn i) (by positivity)
              exact mul_le_mul_of_nonneg_left h7 (sq_nonneg σ)
          _ = 4 * σ^2 * Cstar * ((L:ℝ) * ((L:ℝ) - 1)) := by ring
      calc |(flagDensity₁ (Mv i).2 (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L) : ℝ)
            - (flagDensity₁ (Mv i).2 (s n).2 : ℝ)|
          = |densityEval (basisVector (Mv i))
              ⟨L, (⟦deleteEdgeSet N Dd⟧ : FlagWithSize ∅ₜ L)⟩
            - densityEval (basisVector (Mv i)) ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩| := by
            rw [e1, ← e2]
        _ ≤ (Dd.card : ℝ) * C i * 2 / ((L:ℝ) * ((L:ℝ) - 1)) := hb
        _ ≤ 4 * σ^2 * Cstar := hbound
  -- assemble the deleted flag sequence
  choose Qf hQf using hkey
  set QSeq : FlagSeq ∅ₜ := fun j => Qf (J₀ + j) with hQSeqdef
  have hq1 : ∀ j, (QSeq j).1 = (s (φ₁ (J₀ + j))).1 :=
    fun j => ((hQf (J₀ + j)) (by omega)).1
  have hq2 : ∀ j, densityEval gv (QSeq j)
      ≤ densityEval gv (s (φ₁ (J₀ + j))) - Δc :=
    fun j => ((hQf (J₀ + j)) (by omega)).2.1
  have hq3 : ∀ j i, |(flagDensity₁ (Mv i).2 (QSeq j).2 : ℝ)
      - (flagDensity₁ (Mv i).2 (s (φ₁ (J₀ + j))).2 : ℝ)| ≤ 4 * σ^2 * Cstar :=
    fun j i => ((hQf (J₀ + j)) (by omega)).2.2 i
  have hIncQ : Increases QSeq := by
    intro j k hjk
    show (QSeq j).1 < (QSeq k).1
    rw [hq1 j, hq1 k]
    exact hs_conv.1 (hφ₁mono (by omega))
  obtain ⟨aQ, χ, hχmono, hconvQ⟩ :=
    increasing_flagSeq_contain_convergent_subseq QSeq hIncQ
  obtain ⟨ψlim, hψcoe⟩ := flagSeq_limit_mem_positiveHom _ hconvQ
  set ndx : ℕ → ℕ := fun k => φ₁ (J₀ + χ k) with hndxdef
  have hndxmono : StrictMono ndx := by
    intro k1 k2 hk
    apply hφ₁mono
    have h1 := hχmono hk
    show J₀ + χ k1 < J₀ + χ k2
    omega
  -- coordinatewise limits
  have hQlim := (flagSeq_convergesTo_iff.mp hconvQ).2
  have hslim := (flagSeq_convergesTo_iff.mp hs_conv).2
  have hL1 : ∀ F : FinFlag ∅ₜ, Tendsto
      (fun k => (flagDensity₁ F.2 (QSeq (χ k)).2 : ℝ)) atTop (𝓝 (aQ F)) :=
    fun F => hQlim F
  have hL2 : ∀ F : FinFlag ∅ₜ, Tendsto
      (fun k => (flagDensity₁ F.2 (s (ndx k)).2 : ℝ)) atTop (𝓝 (φ₀.coe F)) :=
    fun F => (hslim F).comp hndxmono.tendsto_atTop
  -- the limit density point stays 4σ²C★-close to a₀
  have hy : ∀ i : Fin h, |aQ (Mv i) - φ₀.coe (Mv i)| ≤ 4 * σ^2 * Cstar := by
    intro i
    have h1 : Tendsto (fun k => |(flagDensity₁ (Mv i).2 (QSeq (χ k)).2 : ℝ)
        - (flagDensity₁ (Mv i).2 (s (ndx k)).2 : ℝ)|) atTop
        (𝓝 |aQ (Mv i) - φ₀.coe (Mv i)|) :=
      ((hL1 (Mv i)).sub (hL2 (Mv i))).abs
    apply le_of_tendsto h1
    exact Filter.Eventually.of_forall (fun k => hq3 (χ k) i)
  -- the gradient combination strictly drops in the limit
  have hgrad_le : ψlim ⟦gv⟧ ≤ φ₀ ⟦gv⟧ - Δc := by
    have h1 : Tendsto (fun k => densityEval gv (QSeq (χ k))) atTop
        (𝓝 (densityEvalFun gv aQ)) :=
      tendsto_finset_sum gv.support
        (fun M (_ : M ∈ gv.support) => (hL1 M).const_mul (gv M))
    have h4 : Tendsto (fun k => densityEval gv (s (ndx k))) atTop
        (𝓝 (densityEvalFun gv φ₀.coe)) :=
      tendsto_finset_sum gv.support
        (fun M (_ : M ∈ gv.support) => (hL2 M).const_mul (gv M))
    have h5 : densityEvalFun gv aQ ≤ densityEvalFun gv φ₀.coe - Δc := by
      apply le_of_tendsto_of_tendsto' h1 (h4.sub_const _)
      intro k
      exact hq2 (χ k)
    rw [densityEvalFun_hom gv φ₀] at h5
    have h7 : densityEvalFun gv aQ = ψlim ⟦gv⟧ := by
      rw [← hψcoe]
      exact densityEvalFun_hom gv ψlim
    rw [h7] at h5
    exact h5
  -- density points
  set y : Fin h → ℝ := densityPoint Mv ψlim with hydef
  have hyi : ∀ i, y i = aQ (Mv i) := by
    intro i
    show ψlim ⟦basisVector (Mv i)⟧ = aQ (Mv i)
    rw [← PositiveHom.coe_flag, hψcoe]
  have ha₀i : ∀ i, a₀ i = φ₀.coe (Mv i) := by
    intro i
    show φ₀ ⟦basisVector (Mv i)⟧ = φ₀.coe (Mv i)
    rw [← PositiveHom.coe_flag]
  have hdist : ∀ i, |y i - a₀ i| ≤ 4 * σ^2 * Cstar := by
    intro i
    rw [hyi i, ha₀i i]
    exact hy i
  have hnorm : ‖y - a₀‖ ≤ 4 * σ^2 * Cstar := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact hdist i
  have hyU : y ∈ U := by
    apply hballU
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖y - a₀‖ ≤ 4 * σ^2 * Cstar := hnorm
      _ < min rU rT := hσrad
      _ ≤ rU := min_le_left _ _
  have hmin2 : f a₀ ≤ f y := hmin ψlim hyU
  -- the C¹ expansion at radius ‖y − a₀‖
  have hyT : dist y a₀ < rT := by
    rw [dist_eq_norm]
    calc ‖y - a₀‖ ≤ 4 * σ^2 * Cstar := hnorm
      _ < min rU rT := hσrad
      _ ≤ rT := min_le_right _ _
  have hTay' := hTay hyT
  have hx : y - a₀ = ∑ i, ((y - a₀) i) • Pi.single i (1 : ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single (y - a₀)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hfd : (fderiv ℝ f a₀) (y - a₀)
      = ∑ i, ((y - a₀) i) * (fderiv ℝ f a₀ (Pi.single i 1)) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
  have hgv_eval : ∀ φ : PositiveHom ∅ₜ, φ ⟦gv⟧
      = ∑ i, (fderiv ℝ f a₀ (Pi.single i 1)) * densityPoint Mv φ i := by
    intro φ
    rw [hgv]
    show φ ⟦∑ i, (fderiv ℝ f a₀ (Pi.single i 1)) • basisVector (Mv i)⟧ = _
    rw [sum_quot, PositiveHom.map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_quot, PositiveHom.map_smul]
    rfl
  have hdir : (fderiv ℝ f a₀) (y - a₀) ≤ -Δc := by
    have h8 : ψlim ⟦gv⟧ - φ₀ ⟦gv⟧ ≤ -Δc := by linarith [hgrad_le]
    have h9 : (fderiv ℝ f a₀) (y - a₀) = ψlim ⟦gv⟧ - φ₀ ⟦gv⟧ := by
      rw [hfd, hgv_eval ψlim, hgv_eval φ₀, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h10 : (y - a₀) i = densityPoint Mv ψlim i - densityPoint Mv φ₀ i := by
        rw [Pi.sub_apply]
      rw [h10]
      ring
    linarith [h9.le, h9.ge, h8]
  have hTb : ‖f y - f a₀ - (fderiv ℝ f a₀) (y - a₀)‖
      ≤ ε₀^2 * ρlim / (4096 * B' * Cstar) * ‖y - a₀‖ := hTay'
  rw [Real.norm_eq_abs] at hTb
  have habs := (abs_le.mp hTb).2
  have hnormb : ε₀^2 * ρlim / (4096 * B' * Cstar) * ‖y - a₀‖
      ≤ ε₀^2 * ρlim / (4096 * B' * Cstar) * (4 * σ^2 * Cstar) :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsmall : ε₀^2 * ρlim / (4096 * B' * Cstar) * (4 * σ^2 * Cstar) ≤ Δc / 2 := by
    have h1 : ε₀^2 * ρlim / (4096 * B' * Cstar) * (4 * σ^2 * Cstar)
        = ε₀^2 * ρlim * σ^2 / (1024 * B') := by
      field_simp
      ring
    have h2 : Δc / 2 = ε₀^2 * ρlim * σ^2 / (512 * B') := by
      rw [hΔcdef]
      field_simp
      ring
    rw [h1, h2]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ε₀) hρpos2.le) (sq_nonneg σ), hB'pos]
  linarith [hmin2, habs, hdir, hnormb, hsmall, hΔcpos]

/-! ## Theorem 4.3: the vertex variational principle -/

/-- **Razborov, Theorem 4.3** (graphs). Let `M⃗ = (M₁, …, M_h)` be fixed
models, `φ₀ ∈ Hom⁺(A⁰, ℝ)` and `f ∈ C¹(U)` for a neighbourhood `U` of the
density point `a = (φ₀(M₁), …, φ₀(M_h))`. If every `φ ∈ Hom⁺(A⁰, ℝ)` whose
density point lies in `U` satisfies `f(φ(M⃗)) ≥ f(a)`, then the random
`1`-rooted extension `φ₀¹` of `φ₀` almost surely annihilates
`∂₁ Grad_{M⃗,a}(f)`:

`P[φ₀¹(∂₁ Grad_{M⃗,a}(f)) = 0] = 1`.

The proof (Razborov, pp. 36–38) fixes an increasing sequence `Nₙ` realising
`φ₀`, transfers a hypothetical positive-probability event
`{φ₀¹(∂₁ Grad) < −ε}` to a positive density of bad roots `v ∈ V(Nₙ)` (via
weak convergence `P¹_{Nₙ} → ℙ[φ₀]`, his Theorem 3.12 + portmanteau), deletes
`⌊δ ℓₙ⌋` bad vertices one at a time — each step controlled by Lemma 4.2 a)
(`vertex_deletion_density` here) with cumulative error `O(δ²)` — and obtains
a limit homomorphism whose density point stays in `U` but decreases `f`,
contradicting minimality via the `C¹` expansion of `f` at `a`. -/
theorem vertex_variational (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (φ₀ : PositiveHom ∅ₜ) {U : Set (Fin h → ℝ)} (hU : U ∈ nhds (densityPoint Mv φ₀))
    (hf : ContDiffOn ℝ 1 f U)
    (hmin : ∀ φ : PositiveHom ∅ₜ, densityPoint Mv φ ∈ U →
      f (densityPoint Mv φ₀) ≤ f (densityPoint Mv φ))
    : (probMeasure_extend_emptyType_positiveHom φ₀ (positiveHom_vertexType_pos φ₀)).toMeasure
        {φ : PositiveHomSpace vertexType |
          (PositiveHomSpace.toPosHom φ) (partialVertex (grad Mv f (densityPoint Mv φ₀))) = 0}
      = 1
  := by
  have hσ : φ₀ ⟨vertexType⟩₀ > 0 := positiveHom_vertexType_pos φ₀
  set Dv : FlagVector vertexType := partialVertexVec (gradVec Mv f (densityPoint Mv φ₀)) with hDv
  have hDalg : (⟦Dv⟧ : FlagAlgebra vertexType)
      = partialVertex (grad Mv f (densityPoint Mv φ₀)) := rfl
  obtain ⟨s, hs_conv, hs_den⟩ := exists_converge_flagSeq_with_flagDensity_pos hσ
  have hkfl := bad_vertex_negPart_tendsto_zero Mv f φ₀ hU hf hmin hs_conv hs_den
  have hae := ae_nonneg_of_empirical_negPart (le_refl 1) hσ Dv hs_conv hs_den hkfl
  rw [hDalg] at hae
  set μ := (probMeasure_extend_emptyType_positiveHom φ₀ hσ).toMeasure with hμ
  set X : PositiveHomSpace vertexType → ℝ := fun φ =>
    (PositiveHomSpace.toPosHom φ) (partialVertex (grad Mv f (densityPoint Mv φ₀))) with hX
  have hXm : Measurable X := measurable_toPosHom_apply _
  have hXb : ∀ φ, |X φ| ≤ ∑ F ∈ Dv.support, |Dv F| := by
    intro φ
    have h1 : X φ = densityEvalFun Dv φ.val := by
      rw [hX]
      rw [← hDalg]
      exact (densityEvalFun_toPosHom Dv φ).symm
    rw [h1]
    exact abs_densityEvalFun_le Dv φ.val
  have hX_int : Integrable X μ := integrable_of_bounded hXm _ hXb
  have hmean : ∫ φ, X φ ∂μ = 0 := by
    have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ
      (partialVertex (grad Mv f (densityPoint Mv φ₀)))
    rw [downward_partialVertex, PositiveHom.map_zero, zero_div] at hspec
    exact hspec
  have haeeq : X =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hae hX_int).mp hmean
  have hae2 : ∀ᵐ φ ∂μ, X φ = 0 := by
    filter_upwards [haeeq] with φ hφ
    simpa using hφ
  have hmeas : MeasurableSet {φ : PositiveHomSpace vertexType | X φ = 0} :=
    hXm (measurableSet_singleton 0)
  rw [← prob_compl_eq_zero_iff hmeas]
  rw [MeasureTheory.ae_iff] at hae2
  exact hae2

/-! ## Theorem 4.5: the edge variational principle -/

/-- **Razborov, Theorem 4.5**. In the theory of graphs, with the hypotheses of
Theorem 4.3 and additionally `φ₀(ρ) > 0` (positive edge density, i.e.
`φ₀ ⟨E⟩₀ > 0`), the random `E`-rooted extension `φ₀^E` of `φ₀` almost surely
satisfies the *inequality*

`P[φ₀^E(∂_E Grad_{M⃗,a}(f)) ≥ 0] = 1`

(only one direction, since edges can be deleted but not created without
leaving the hereditary theory). The proof mirrors Theorem 4.3, deleting a
sparse set of bad edges chosen inside a random vertex subset of size
`⌊δ^{1/2} ℓₙ⌋` so that no vertex loses too many edges (Razborov, p. 40), with
each deletion step controlled by Lemma 4.4 a) (`edge_deletion_density`). -/
theorem edge_variational (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (φ₀ : PositiveHom ∅ₜ) {U : Set (Fin h → ℝ)} (hU : U ∈ nhds (densityPoint Mv φ₀))
    (hf : ContDiffOn ℝ 1 f U)
    (hmin : ∀ φ : PositiveHom ∅ₜ, densityPoint Mv φ ∈ U →
      f (densityPoint Mv φ₀) ≤ f (densityPoint Mv φ))
    (hρ : φ₀ ⟨edgeType⟩₀ > 0)
    : (probMeasure_extend_emptyType_positiveHom φ₀ hρ).toMeasure
        {φ : PositiveHomSpace edgeType |
          0 ≤ (PositiveHomSpace.toPosHom φ) (partialEdge (grad Mv f (densityPoint Mv φ₀)))}
      = 1
  := by
  set DE : FlagVector edgeType := partialEdgeVec (gradVec Mv f (densityPoint Mv φ₀)) with hDE
  have hDalg : (⟦DE⟧ : FlagAlgebra edgeType)
      = partialEdge (grad Mv f (densityPoint Mv φ₀)) := rfl
  obtain ⟨s, hs_conv, hs_den⟩ := exists_converge_flagSeq_with_flagDensity_pos hρ
  have hkfl := bad_edge_negPart_tendsto_zero Mv f φ₀ hU hf hmin hρ hs_conv hs_den
  have hae := ae_nonneg_of_empirical_negPart (by norm_num) hρ DE hs_conv hs_den hkfl
  rw [hDalg] at hae
  have hmeas : MeasurableSet {φ : PositiveHomSpace edgeType |
      0 ≤ (PositiveHomSpace.toPosHom φ) (partialEdge (grad Mv f (densityPoint Mv φ₀)))} :=
    measurable_toPosHom_apply _ measurableSet_Ici
  rw [← prob_compl_eq_zero_iff hmeas]
  rw [MeasureTheory.ae_iff] at hae
  exact hae

/-! ## Corollary 4.6: the light versions -/

/-- **Razborov, Corollary 4.6 a)** (graphs): under the extremality hypotheses
of Theorem 4.3, for every `g ∈ A¹`,

`φ₀(⟦(∂₁ Grad_{M⃗,a}(f)) · g⟧₁) = 0`.

Derived from Theorem 4.3 and the defining property of the ensemble `ℙ[φ₀]`:
the integrand `φ ↦ φ(∂₁Grad · g) = φ(∂₁Grad) · φ(g)` vanishes almost surely,
so `φ₀(⟦∂₁Grad · g⟧₁)/φ₀(⟦1⟧₁) = E[φ(∂₁Grad · g)] = 0`. -/
theorem downward_grad_vertex_eq_zero (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (φ₀ : PositiveHom ∅ₜ) {U : Set (Fin h → ℝ)} (hU : U ∈ nhds (densityPoint Mv φ₀))
    (hf : ContDiffOn ℝ 1 f U)
    (hmin : ∀ φ : PositiveHom ∅ₜ, densityPoint Mv φ ∈ U →
      f (densityPoint Mv φ₀) ≤ f (densityPoint Mv φ))
    (g : FlagAlgebra vertexType)
    : φ₀ ⟦(partialVertex (grad Mv f (densityPoint Mv φ₀))) * g⟧₀ = 0
  := by
  set D : FlagAlgebra vertexType := partialVertex (grad Mv f (densityPoint Mv φ₀)) with hD
  have hσ : φ₀ ⟨vertexType⟩₀ > 0 := positiveHom_vertexType_pos φ₀
  have h43 := vertex_variational Mv f φ₀ hU hf hmin
  have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ (D * g)
  have hmeas : MeasurableSet {φ : PositiveHomSpace vertexType |
      (PositiveHomSpace.toPosHom φ) D = 0} :=
    measurable_toPosHom_apply D (measurableSet_singleton 0)
  have hae : ∀ᵐ φ ∂(probMeasure_extend_emptyType_positiveHom φ₀ hσ).toMeasure,
      (PositiveHomSpace.toPosHom φ) D = 0 := by
    rw [MeasureTheory.ae_iff]
    have hcompl : {φ : PositiveHomSpace vertexType |
        ¬(PositiveHomSpace.toPosHom φ) D = 0}
        = {φ : PositiveHomSpace vertexType | (PositiveHomSpace.toPosHom φ) D = 0}ᶜ := rfl
    rw [hcompl, prob_compl_eq_zero_iff hmeas]
    exact h43
  have hzero : ∫ φ, (PositiveHomSpace.toPosHom φ) (D * g)
      ∂(probMeasure_extend_emptyType_positiveHom φ₀ hσ).toMeasure = 0 := by
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [hae] with φ hφ
    rw [Pi.zero_apply, PositiveHom.map_mul, hφ, zero_mul]
  rw [hzero] at hspec
  have h1 : φ₀ ⟦(1 : FlagAlgebra vertexType)⟧₀ > 0 := positiveHom_one_downward_pos hσ
  rw [eq_comm, div_eq_iff (ne_of_gt h1), zero_mul] at hspec
  exact hspec

/-- **Razborov, Corollary 4.6 b)** (graphs): under the extremality hypotheses
of Theorem 4.3, for every `g ∈ C_sem(A^E)` (in particular for every
`E`-flag),

`φ₀(⟦(∂_E Grad_{M⃗,a}(f)) · g⟧_E) ≥ 0`

provided `φ₀(ρ) > 0`. Derived from Theorem 4.5 and the defining property of
`ℙ[φ₀]`: the integrand `φ ↦ φ(∂_E Grad) · φ(g)` is a.s. a product of
nonnegatives. -/
theorem downward_grad_edge_nonneg (Mv : Fin h → FinFlag ∅ₜ) (f : (Fin h → ℝ) → ℝ)
    (φ₀ : PositiveHom ∅ₜ) {U : Set (Fin h → ℝ)} (hU : U ∈ nhds (densityPoint Mv φ₀))
    (hf : ContDiffOn ℝ 1 f U)
    (hmin : ∀ φ : PositiveHom ∅ₜ, densityPoint Mv φ ∈ U →
      f (densityPoint Mv φ₀) ≤ f (densityPoint Mv φ))
    (hρ : φ₀ ⟨edgeType⟩₀ > 0)
    {g : FlagAlgebra edgeType} (hg : g ∈ semanticCone edgeType)
    : 0 ≤ φ₀ ⟦(partialEdge (grad Mv f (densityPoint Mv φ₀))) * g⟧₀
  := by
  set D : FlagAlgebra edgeType := partialEdge (grad Mv f (densityPoint Mv φ₀)) with hD
  have h45 := edge_variational Mv f φ₀ hU hf hmin hρ
  have hspec := probMeasure_extend_emptyType_positiveHom_spec hρ (D * g)
  have hmeas : MeasurableSet {φ : PositiveHomSpace edgeType |
      0 ≤ (PositiveHomSpace.toPosHom φ) D} :=
    measurable_toPosHom_apply D measurableSet_Ici
  have hae : ∀ᵐ φ ∂(probMeasure_extend_emptyType_positiveHom φ₀ hρ).toMeasure,
      0 ≤ (PositiveHomSpace.toPosHom φ) D := by
    rw [MeasureTheory.ae_iff]
    have hcompl : {φ : PositiveHomSpace edgeType |
        ¬0 ≤ (PositiveHomSpace.toPosHom φ) D}
        = {φ : PositiveHomSpace edgeType | 0 ≤ (PositiveHomSpace.toPosHom φ) D}ᶜ := rfl
    rw [hcompl, prob_compl_eq_zero_iff hmeas]
    exact h45
  have hnonneg : 0 ≤ ∫ φ, (PositiveHomSpace.toPosHom φ) (D * g)
      ∂(probMeasure_extend_emptyType_positiveHom φ₀ hρ).toMeasure := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [hae] with φ hφ
    rw [PositiveHom.map_mul]
    exact mul_nonneg hφ (hg (PositiveHomSpace.toPosHom φ))
  rw [hspec] at hnonneg
  have h1 : φ₀ ⟦(1 : FlagAlgebra edgeType)⟧₀ > 0 := positiveHom_one_downward_pos hρ
  have := mul_nonneg hnonneg (le_of_lt h1)
  rwa [div_mul_cancel₀ _ (ne_of_gt h1)] at this

end Differential
end FlagAlgebras
