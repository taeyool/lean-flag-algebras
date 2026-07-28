import «LeanFlagAlgebras».Differential.DeleteEdge
import «LeanFlagAlgebras».Differential.Ensemble
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

**Status.** Corollary 4.6 is derived in full from Theorems 4.3/4.5 and the
defining property of `ℙ[φ₀]`. Theorems 4.3/4.5 themselves are **proved**
here, by the following route replacing Razborov's Theorems 3.9/3.12:

* `Ensemble.lean` provides the Stone–Weierstrass moment machinery: along
  *any* flag sequence realising `φ₀`, empirical integrals of coordinate
  polynomials converge to the corresponding `ℙ[φ₀]`-moments;
* `ae_nonneg_of_empirical_negPart` (this file) turns "the empirical average
  of `negPart(p^{(N,v)}(D))` tends to `0` along one such sequence" into
  "`φ(D) ≥ 0` `ℙ[φ₀]`-a.s.", by sandwiching the negative part between
  coordinate polynomials; combined with the vanishing mean (Lemma 4.2 c) for
  the vertex case) this gives the almost-sure statements.

The *only* remaining gap is the purely finite-combinatorial core, stated as
`bad_vertex_negPart_tendsto_zero` / `bad_edge_negPart_tendsto_zero`
(Razborov's estimates (29)–(33)): under local minimality no `ε`-bad set of
roots of positive density can persist, because deleting `⌊δℓₙ⌋` bad
vertices/edges — each step controlled by the fully proved Lemmas 4.2 a) /
4.4 a) — would drive `f` strictly below its local minimum via the `C¹`
expansion. These two lemmas mention no measures beyond finite averages.
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

/-! ## The finite estimates: the remaining combinatorial core -/

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
  sorry

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
  sorry

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
