import «LeanFlagAlgebras».Differential.DeleteEdge
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

**Status.** Corollary 4.6 is *derived here in full* from Theorems 4.3/4.5 and
the defining property of `ℙ[φ₀]`. The two theorems themselves are stated
faithfully but left `sorry`: Razborov's proofs need two further ingredients
not yet in the library —

1. his Theorem 3.12 (for *any* increasing sequence `Nₙ` with `p^{Nₙ} → φ₀`,
   the root-empirical measures `P^{σ}_{Nₙ}` converge weakly to `ℙ[φ₀]`; the
   library's `exists_converge_flagSeq_and_probMeasure_tendsto` provides only
   *some* such sequence), together with a portmanteau argument
   (his Theorem 3.9) transferring positive mass of the open "bad" event to
   the finite stages; and
2. the finite deletion estimates (his (29)–(33)): deleting a sparse set of
   bad vertices/edges changes every fixed-size density by `O(δ)` — the
   one-step versions being exactly `vertex_deletion_density` /
   `edge_deletion_density` proved in this development — followed by a
   compactness + `C¹`-Taylor argument contradicting local minimality.
-/

open MeasureTheory

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
  sorry

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
  sorry

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
