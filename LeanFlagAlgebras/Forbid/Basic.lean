import LeanFlagAlgebras.FlagAlgebra.QuadraticForm
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

/-! # Forbidden-subgraph reasoning framework

This file defines the relations `f =ᵢ[F] g` (`inducedForbidEq`) and `f ≤ᵢ[F] g` (`inducedForbidLE`),
the statement language for the end-to-end density bounds. They mean that, almost surely
under random positive homomorphisms `φ` drawn conditioned on the forbidden flag `F`
having density `0` (`φ₀ ⟦basisVector F⟧ = 0`), one has `φ f = φ g` resp. `φ f ≤ φ g`
(probability `1`). The file proves the algebraic and order lemmas (refl/symm/trans,
add/smul, `inducedForbidLE_of_le`, downward monotonicity, …) consumed by the Automation tactics, as
well as the empty-type variants and the equivalence between them.
-/

open FlagAlgebras
open MeasureTheory
open Lean Elab Tactic

namespace Forbid

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Core relations -/

/-- A forbidden condition is a property of the ambient empty-type positive homomorphism.

The old single-forbidden-flag semantics is recovered by `inducedForbiddenCondition`;
ordinary-free semantics can be added by replacing this condition with one that kills
all induced patterns containing the forbidden graph as an ordinary subgraph. -/
def ForbidCondition : Type :=
  PositiveHom ∅ₜ → Prop

/-- The condition used by the original `inducedForbidEq`/`inducedForbidLE` API: the empty-type
forbidden flag has density zero. -/
def inducedForbiddenCondition (F_forbid : FinFlag ∅ₜ) : ForbidCondition :=
  fun φ₀ => φ₀ ⟦basisVector F_forbid⟧ = 0

/-- A condition that kills every empty-type flag in a prescribed family. This is the
basic shape needed for ordinary-free semantics, where one forbids all induced patterns
that contain the forbidden graph as an ordinary subgraph. -/
def familyForbiddenCondition (Fs : Set (FinFlag ∅ₜ)) : ForbidCondition :=
  fun φ₀ => ∀ F, F ∈ Fs → φ₀ ⟦basisVector F⟧ = 0

/-- Empty-type flags whose underlying graph contains `H` as an ordinary, not
necessarily induced, subgraph. This is the graph family that should vanish when
the ambient objects are ordinary `H`-free. -/
noncomputable def forbiddenFlags {n : ℕ} (H : SimpleGraph (Fin n)) :
    Set (FinFlag ∅ₜ) :=
  fun F =>
    ∃ G : LabeledGraph ∅ₜ (Fin F.1), F.2 = ⟦G⟧ ∧ SimpleGraph.IsContained H G.graph

/-- Ordinary-free forbidden condition: every induced pattern whose underlying graph
contains `H` as an ordinary subgraph has density zero. -/
noncomputable def forbiddenCondition {n : ℕ} (H : SimpleGraph (Fin n)) :
    ForbidCondition :=
  familyForbiddenCondition (forbiddenFlags H)

/-- `forbidEqWith C f g`: for every base homomorphism `φ₀` satisfying the forbidden
condition `C`, the conditioned random homomorphism `φ` satisfies `φ f = φ g` almost
surely. -/
def forbidEqWith
    (C : ForbidCondition) (f g : FlagAlgebra σ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), (hσ : φ₀ ⟨σ⟩₀ > 0)
    → C φ₀
    → ℙ[φ₀] {φ | φ f = φ g} = 1

/-- `forbidLEWith C f g`: for every base homomorphism `φ₀` satisfying the forbidden
condition `C`, the conditioned random homomorphism `φ` satisfies `φ f ≤ φ g` almost
surely. -/
def forbidLEWith
    (C : ForbidCondition) (f g : FlagAlgebra σ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), (hσ : φ₀ ⟨σ⟩₀ > 0)
    → C φ₀
    → ℙ[φ₀] {φ | φ f ≤ φ g} = 1

/-- `f =ᵢ[F_forbid] g`: for every base homomorphism `φ₀` with `σ` of positive density that
assigns density `0` to the forbidden flag `F_forbid`, the conditioned random homomorphism
`φ` satisfies `φ f = φ g` almost surely (probability `1`). -/
def inducedForbidEq
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra σ) : Prop
  :=
  forbidEqWith (inducedForbiddenCondition F_forbid) f g

/-- `f ≤ᵢ[F_forbid] g`: for every base homomorphism `φ₀` with `σ` of positive density that
assigns density `0` to the forbidden flag `F_forbid`, the conditioned random homomorphism
`φ` satisfies `φ f ≤ φ g` almost surely (probability `1`). -/
def inducedForbidLE
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra σ) : Prop
  :=
  forbidLEWith (inducedForbiddenCondition F_forbid) f g

/-- Equality modulo the ordinary `H`-free condition. -/
noncomputable def forbidEq {m : ℕ}
    (H : SimpleGraph (Fin m)) (f g : FlagAlgebra σ) : Prop :=
  forbidEqWith (forbiddenCondition H) f g

/-- Order modulo the ordinary `H`-free condition. -/
noncomputable def forbidLE {m : ℕ}
    (H : SimpleGraph (Fin m)) (f g : FlagAlgebra σ) : Prop :=
  forbidLEWith (forbiddenCondition H) f g

-- Notation: `f =ᵢ[F] g` for `inducedForbidEq F f g` and `f ≤ᵢ[F] g` for `inducedForbidLE F f g`.
notation f "=ᵢ[" F_forbid "]" g => inducedForbidEq F_forbid f g
notation f "≤ᵢ[" F_forbid "]" g => inducedForbidLE F_forbid f g
notation f "=[" H "]" g => forbidEq H f g
notation f "≤[" H "]" g => forbidLE H f g

lemma positiveHomSpace_eval_eq_sum
    (k : FlagAlgebra σ)
    : (fun ψ : PositiveHomSpace σ => ψ k)
      = (fun ψ => ∑ F ∈ k.out.support, k.out F * ψ.val F)
  := by
  funext ψ
  conv_lhs =>
    rw [← Quotient.out_eq k, flagVector_eq_sum_basisVector k.out]
    rw [sum_quot, PositiveHom.map_sum]
    simp only [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector]

lemma positiveHomSpace_toPosHom_continuous
    : Continuous (fun (ψ : PositiveHomSpace σ) => (PositiveHomSpace.toPosHom ψ : FlagAlgebra σ → ℝ))
  := by
  apply continuous_pi
  intro k
  have h_cont_sum : Continuous (fun ψ : PositiveHomSpace σ => ∑ F ∈ k.out.support, k.out F * ψ.val F) := by
    apply continuous_finset_sum
    intro F hF
    exact Continuous.mul continuous_const ((FinFlag.continuous F).comp continuous_subtype_val)
  simpa [positiveHomSpace_eval_eq_sum (σ := σ) k] using h_cont_sum

lemma positiveHomSpace_eval_continuous
    (f : FlagAlgebra σ)
    : Continuous (fun ψ : PositiveHomSpace σ => ψ f)
  :=
  (continuous_apply f).comp positiveHomSpace_toPosHom_continuous

lemma forbidEq_set_measurable
    (f g : FlagAlgebra σ)
    : MeasurableSet {φ : PositiveHomSpace σ | φ f = φ g}
  :=
  (isClosed_eq (positiveHomSpace_eval_continuous (σ := σ) f)
    (positiveHomSpace_eval_continuous (σ := σ) g)).measurableSet

lemma forbidLE_set_measurable
    (f g : FlagAlgebra σ)
    : MeasurableSet {φ : PositiveHomSpace σ | φ f ≤ φ g}
  :=
  (isClosed_le (positiveHomSpace_eval_continuous (σ := σ) f)
    (positiveHomSpace_eval_continuous (σ := σ) g)).measurableSet

/-! ## Reflexivity, symmetry, transitivity and the equality/order bridge -/

theorem forbidEqWith_refl
    (C : ForbidCondition) (f : FlagAlgebra σ)
    : forbidEqWith C f f
  := by
  intro φ₀ hσ hC
  simp

theorem inducedForbidEq_refl
    (F_forbid : FinFlag ∅ₜ) (f : FlagAlgebra σ)
    : f =ᵢ[F_forbid] f
  := forbidEqWith_refl (inducedForbiddenCondition F_forbid) f

theorem forbidLEWith_refl
    (C : ForbidCondition) (f : FlagAlgebra σ)
    : forbidLEWith C f f
  := by
  intro φ₀ hσ hC
  simp

theorem inducedForbidLE_refl
    (F_forbid : FinFlag ∅ₜ) (f : FlagAlgebra σ)
    : f ≤ᵢ[F_forbid] f
  := forbidLEWith_refl (inducedForbiddenCondition F_forbid) f

theorem forbidEqWith_symm
    {C : ForbidCondition} {f g : FlagAlgebra σ}
    (hfg : forbidEqWith C f g)
    : forbidEqWith C g f
  := by
  intro φ₀ hσ hC
  simpa [eq_comm] using hfg φ₀ hσ hC

theorem inducedForbidEq_symm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : g =ᵢ[F_forbid] f
  := forbidEqWith_symm hfg

theorem forbidEqWith_of_eq
    {C : ForbidCondition} {f g : FlagAlgebra σ}
    (hfg : f = g)
    : forbidEqWith C f g
  := by
  subst hfg
  exact forbidEqWith_refl C f

theorem inducedForbidEq_of_eq
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f = g)
    : f =ᵢ[F_forbid] g
  := forbidEqWith_of_eq hfg

/-- An unconditional flag-algebra inequality `f ≤ g` lifts to the forbidden relation
`forbidLEWith C f g` for any forbidden condition `C`. -/
theorem forbidLEWith_of_le
    {C : ForbidCondition} {f g : FlagAlgebra σ}
    (hfg : f ≤ g)
    : forbidLEWith C f g
  := by
  intro φ₀ hσ hC
  have hsubset : (Set.univ : Set (PositiveHomSpace σ)) ⊆
      {φ : PositiveHomSpace σ | φ f ≤ φ g} := by
    intro φ _
    have hcone : g - f ∈ semanticCone σ := (le_def f g).1 hfg
    have hnonneg : 0 ≤ (PositiveHomSpace.toPosHom φ) (g - f) := hcone (PositiveHomSpace.toPosHom φ)
    have hsub : (PositiveHomSpace.toPosHom φ) (g - f) = φ g - φ f := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (PositiveHom.map_sub (PositiveHomSpace.toPosHom φ) g f)
    have hsub' : 0 ≤ φ g - φ f := by simpa [hsub] using hnonneg
    exact sub_nonneg.mp hsub'
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (Set.univ : Set (PositiveHomSpace σ)) := by simp
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- An unconditional flag-algebra inequality `f ≤ g` lifts to the forbidden relation
`f ≤ᵢ[F_forbid] g` for any forbidden flag. -/
theorem inducedForbidLE_of_le
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f ≤ g)
    : f ≤ᵢ[F_forbid] g
  := forbidLEWith_of_le hfg

/-- A forbidden equality `forbidEqWith C f g` implies the forbidden inequality
`forbidLEWith C f g`. -/
theorem forbidLEWith_of_forbidEqWith
    {C : ForbidCondition} {f g : FlagAlgebra σ}
    (hfg : forbidEqWith C f g)
    : forbidLEWith C f g
  := by
  intro φ₀ hσ hC
  have hEq : ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ g} = 1 := hfg φ₀ hσ hC
  have hmono :
      {φ : PositiveHomSpace σ | φ f = φ g} ⊆ {φ : PositiveHomSpace σ | φ f ≤ φ g} := by
    intro φ hφ
    exact le_of_eq (by simpa using hφ)
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ g} := by
        simpa using hEq.symm
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hmono

/-- A forbidden equality `f =ᵢ[F_forbid] g` implies the forbidden inequality
`f ≤ᵢ[F_forbid] g`. -/
theorem inducedForbidLE_of_inducedForbidEq
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : f ≤ᵢ[F_forbid] g
  := forbidLEWith_of_forbidEqWith hfg

/-- Transitivity of the forbidden equality relation (condition-parametric). -/
theorem forbidEqWith_trans
    {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidEqWith C f g) (hgh : forbidEqWith C g h)
    : forbidEqWith C f h
  := by
  intro φ₀ hσ hC
  let A : Set (PositiveHomSpace σ) := {φ | φ f = φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ g = φ h}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
  have hB : ℙ[φ₀] B = 1 := hgh φ₀ hσ hC
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidEq_set_measurable (σ := σ) f g)
      (forbidEq_set_measurable (σ := σ) g h) hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ f = φ h} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hgh'⟩
    exact Eq.trans (by simpa [A] using hfg') (by simpa [B] using hgh')
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ h} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- Transitivity of the forbidden equality relation. -/
theorem inducedForbidEq_trans
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g) (hgh : g =ᵢ[F_forbid] h)
    : f =ᵢ[F_forbid] h
  := forbidEqWith_trans hfg hgh

theorem inducedForbidEq_rw_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (f =ᵢ[F_forbid] h) ↔ (g =ᵢ[F_forbid] h)
  := by
  constructor
  · intro hfh
    exact inducedForbidEq_trans (inducedForbidEq_symm hfg) hfh
  · intro hgh
    exact inducedForbidEq_trans hfg hgh

theorem inducedForbidEq_rw_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (h =ᵢ[F_forbid] f) ↔ (h =ᵢ[F_forbid] g)
  := by
  constructor
  · intro hhf
    exact inducedForbidEq_trans hhf hfg
  · intro hhg
    exact inducedForbidEq_trans hhg (inducedForbidEq_symm hfg)

/-- Transitivity of the forbidden inequality relation (condition-parametric). -/
theorem forbidLEWith_trans
    {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidLEWith C f g) (hgh : forbidLEWith C g h)
    : forbidLEWith C f h
  := by
  intro φ₀ hσ hC
  let A : Set (PositiveHomSpace σ) := {φ | φ f ≤ φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ g ≤ φ h}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
  have hB : ℙ[φ₀] B = 1 := hgh φ₀ hσ hC
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidLE_set_measurable (σ := σ) f g)
      (forbidLE_set_measurable (σ := σ) g h) hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ f ≤ φ h} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hgh'⟩
    exact le_trans (by simpa [A] using hfg') (by simpa [B] using hgh')
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ h} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- Transitivity of the forbidden inequality relation. -/
theorem inducedForbidLE_trans
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤ᵢ[F_forbid] g) (hgh : g ≤ᵢ[F_forbid] h)
    : f ≤ᵢ[F_forbid] h
  := forbidLEWith_trans hfg hgh

theorem inducedForbidLE_trans_inducedForbidEq_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g) (hgh : g ≤ᵢ[F_forbid] h)
    : f ≤ᵢ[F_forbid] h
  :=
  inducedForbidLE_trans (inducedForbidLE_of_inducedForbidEq hfg) hgh

theorem inducedForbidLE_trans_inducedForbidEq_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤ᵢ[F_forbid] g) (hgh : g =ᵢ[F_forbid] h)
    : f ≤ᵢ[F_forbid] h
  :=
  inducedForbidLE_trans hfg (inducedForbidLE_of_inducedForbidEq hgh)

theorem inducedForbidLE_rw_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (f ≤ᵢ[F_forbid] h) ↔ (g ≤ᵢ[F_forbid] h)
  := by
  constructor
  · intro hfh
    exact inducedForbidLE_trans (inducedForbidLE_of_inducedForbidEq (inducedForbidEq_symm hfg)) hfh
  · intro hgh
    exact inducedForbidLE_trans (inducedForbidLE_of_inducedForbidEq hfg) hgh

theorem inducedForbidLE_rw_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (h ≤ᵢ[F_forbid] f) ↔ (h ≤ᵢ[F_forbid] g)
  := by
  constructor
  · intro hhf
    exact inducedForbidLE_trans hhf (inducedForbidLE_of_inducedForbidEq hfg)
  · intro hhg
    exact inducedForbidLE_trans hhg (inducedForbidLE_of_inducedForbidEq (inducedForbidEq_symm hfg))

theorem forbidLEWith_antisymm
    {C : ForbidCondition} {f g : FlagAlgebra σ}
    (hfg : forbidLEWith C f g) (hgf : forbidLEWith C g f)
    : forbidEqWith C f g
  := by
  intro φ₀ hσ hC
  let A : Set (PositiveHomSpace σ) := {φ | φ f ≤ φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ g ≤ φ f}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
  have hB : ℙ[φ₀] B = 1 := hgf φ₀ hσ hC
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidLE_set_measurable (σ := σ) f g)
      (forbidLE_set_measurable (σ := σ) g f) hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ f = φ g} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hgf'⟩
    exact le_antisymm (by simpa [A] using hfg') (by simpa [B] using hgf')
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ g} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

theorem inducedForbidLE_antisymm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f ≤ᵢ[F_forbid] g) (hgf : g ≤ᵢ[F_forbid] f)
    : f =ᵢ[F_forbid] g
  := forbidLEWith_antisymm hfg hgf

/-! ## Compatibility with addition, subtraction, scalar multiplication and sums -/

/-- Forbidden equality is additive (condition-parametric). -/
theorem forbidEqWith_add
    {C : ForbidCondition} {f g f' g' : FlagAlgebra σ}
    (hfg : forbidEqWith C f g) (hf'g' : forbidEqWith C f' g')
    : forbidEqWith C (f + f') (g + g')
  := by
  intro φ₀ hσ hC
  let A : Set (PositiveHomSpace σ) := {φ | φ f = φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ f' = φ g'}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
  have hB : ℙ[φ₀] B = 1 := hf'g' φ₀ hσ hC
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidEq_set_measurable (σ := σ) f g)
      (forbidEq_set_measurable (σ := σ) f' g') hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ (f + f') = φ (g + g')} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hf'g''⟩
    have h₁ : φ f = φ g := by simpa [A] using hfg'
    have h₂ : φ f' = φ g' := by simpa [B] using hf'g''
    calc
      φ (f + f') = φ f + φ f' := by simp [PositiveHom.map_add]
      _ = φ g + φ g' := by simp [h₁, h₂]
      _ = φ (g + g') := by simp [PositiveHom.map_add]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (f + f') = φ (g + g')} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- Forbidden equality is additive: adding two forbidden equalities side by side. -/
theorem inducedForbidEq_add
    {F_forbid : FinFlag ∅ₜ} {f g f' g' : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g) (hf'g' : f' =ᵢ[F_forbid] g')
    : (f + f') =ᵢ[F_forbid] (g + g')
  := forbidEqWith_add hfg hf'g'

theorem inducedForbidEq_add_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (h + f) =ᵢ[F_forbid] (h + g)
  :=
  inducedForbidEq_add (inducedForbidEq_refl F_forbid h) hfg

theorem inducedForbidEq_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (f + h) =ᵢ[F_forbid] (g + h)
  :=
  inducedForbidEq_add hfg (inducedForbidEq_refl F_forbid h)

theorem forbidEqWith_sum_eq_zero
    {C : ForbidCondition} {α : Type*}
    (s : Finset α) (f : α → FlagAlgebra σ)
    (hzero : ∀ a ∈ s, forbidEqWith C (f a) 0)
    : forbidEqWith C (Finset.sum s f) 0
  := by
  classical
  revert hzero
  refine Finset.induction_on s ?base ?step
  · intro _
    simpa using (forbidEqWith_refl C (0 : FlagAlgebra σ))
  · intro a s ha ih hzero
    have ha0 : forbidEqWith C (f a) 0 := hzero a (by simp)
    have hs : ∀ x ∈ s, forbidEqWith C (f x) 0 := by
      intro x hx
      exact hzero x (by simp [hx])
    have hs0 : forbidEqWith C (Finset.sum s f) 0 := ih hs
    simpa [Finset.sum_insert, ha] using (forbidEqWith_add ha0 hs0)

theorem inducedForbidEq_sum_eq_zero
    {F_forbid : FinFlag ∅ₜ} {α : Type*}
    (s : Finset α) (f : α → FlagAlgebra σ)
    (hzero : ∀ a ∈ s, f a =ᵢ[F_forbid] 0)
    : (Finset.sum s f) =ᵢ[F_forbid] 0
  := forbidEqWith_sum_eq_zero s f hzero

theorem forbidEqWith_sum_filter_eq_zero
    {C : ForbidCondition} {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → FlagAlgebra σ)
    (hzero : ∀ a ∈ s, p a → forbidEqWith C (f a) 0)
  : forbidEqWith C (Finset.sum (s.filter p) f) 0
  := by
  apply forbidEqWith_sum_eq_zero (C := C) (s := s.filter p) (f := f)
  intro a ha
  exact hzero a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2

theorem inducedForbidEq_sum_filter_eq_zero
    {F_forbid : FinFlag ∅ₜ} {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → FlagAlgebra σ)
    (hzero : ∀ a ∈ s, p a → f a =ᵢ[F_forbid] 0)
  : (Finset.sum (s.filter p) f) =ᵢ[F_forbid] 0
  := forbidEqWith_sum_filter_eq_zero s p f hzero

/-- Forbidden equality is preserved by scaling both sides by the same real `c`
(condition-parametric). -/
theorem forbidEqWith_smul
    {C : ForbidCondition} {f g : FlagAlgebra σ} {c : ℝ}
    (hfg : forbidEqWith C f g)
    : forbidEqWith C (c • f) (c • g)
  := by
  intro φ₀ hσ hC
  let A : Set (PositiveHomSpace σ) := {φ | φ f = φ g}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
  have hsubset :
      A ⊆ {φ : PositiveHomSpace σ | φ (c • f) = φ (c • g)} := by
    intro φ hφ
    have hfg' : φ f = φ g := by simpa using hφ
    calc
      φ (c • f) = c * φ f := by simp [PositiveHom.map_smul]
      _ = c * φ g := by simp [hfg']
      _ = φ (c • g) := by simp [PositiveHom.map_smul]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] A := by simpa using hA.symm
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (c • f) = φ (c • g)} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- Forbidden equality is preserved by scaling both sides by the same real `c`. -/
theorem inducedForbidEq_smul
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ} {c : ℝ}
    (hfg : f =ᵢ[F_forbid] g)
    : (c • f) =ᵢ[F_forbid] (c • g)
  := forbidEqWith_smul hfg

/-- Forbidden equality is preserved by negation (the `c := -1` instance of `forbidEqWith_smul`).
Used by `reduce_downward_flagmul` to handle `downward (-(A * B))` summands, where a `(-1) • _`
coefficient was simplified to a bare negation. -/
theorem forbidEqWith_neg
    {C : ForbidCondition} {f g : FlagAlgebra σ}
    (hfg : forbidEqWith C f g)
    : forbidEqWith C (-f) (-g)
  := by simpa only [neg_one_smul] using forbidEqWith_smul (c := -1) hfg

theorem inducedForbidEq_neg
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (-f) =ᵢ[F_forbid] (-g)
  := forbidEqWith_neg hfg

theorem forbidEqWith_smul_zero
    {C : ForbidCondition} {f : FlagAlgebra σ} {c : ℝ}
    (hfg : forbidEqWith C f 0)
    : forbidEqWith C (c • f) 0
  := by
  have := forbidEqWith_smul (c := c) hfg
  simpa using this

theorem inducedForbidEq_smul_zero
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} {c : ℝ}
    (hfg : f =ᵢ[F_forbid] 0)
    : (c • f) =ᵢ[F_forbid] 0
  := forbidEqWith_smul_zero hfg

theorem inducedForbidEq_rw_left_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h k : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : ((f + h) =ᵢ[F_forbid] k) ↔ ((g + h) =ᵢ[F_forbid] k)
  :=
  inducedForbidEq_rw_left (inducedForbidEq_add_right hfg)

theorem inducedForbidEq_rw_left_add_left
    {F_forbid : FinFlag ∅ₜ} {f g h k : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : ((h + f) =ᵢ[F_forbid] k) ↔ ((h + g) =ᵢ[F_forbid] k)
  :=
  inducedForbidEq_rw_left (inducedForbidEq_add_left hfg)

theorem inducedForbidEq_rw_right_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h k : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (k =ᵢ[F_forbid] (f + h)) ↔ (k =ᵢ[F_forbid] (g + h))
  :=
  inducedForbidEq_rw_right (inducedForbidEq_add_right hfg)

theorem inducedForbidEq_rw_right_add_left
    {F_forbid : FinFlag ∅ₜ} {f g h k : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : (k =ᵢ[F_forbid] (h + f)) ↔ (k =ᵢ[F_forbid] (h + g))
  :=
  inducedForbidEq_rw_right (inducedForbidEq_add_left hfg)

theorem inducedForbidEq_rw_left_smul
    {F_forbid : FinFlag ∅ₜ} {f g k : FlagAlgebra σ} {c : ℝ}
    (hfg : f =ᵢ[F_forbid] g)
    : ((c • f) =ᵢ[F_forbid] k) ↔ ((c • g) =ᵢ[F_forbid] k)
  :=
  inducedForbidEq_rw_left (inducedForbidEq_smul (c := c) hfg)

theorem inducedForbidEq_rw_right_smul
    {F_forbid : FinFlag ∅ₜ} {f g k : FlagAlgebra σ} {c : ℝ}
    (hfg : f =ᵢ[F_forbid] g)
    : (k =ᵢ[F_forbid] (c • f)) ↔ (k =ᵢ[F_forbid] (c • g))
  :=
  inducedForbidEq_rw_right (inducedForbidEq_smul (c := c) hfg)

theorem inducedForbidEq_move_add_left_iff
    {F_forbid : FinFlag ∅ₜ} {a b c : FlagAlgebra σ}
    : ((a + b) =ᵢ[F_forbid] c) ↔ (b =ᵢ[F_forbid] (c - a))
  := by
  constructor
  · intro habc
    have h1 := inducedForbidEq_add_right (h := -a) habc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  · intro hbc
    have h1 := inducedForbidEq_add_left (h := a) hbc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1

theorem inducedForbidEq_move_add_left
    {F_forbid : FinFlag ∅ₜ} {a b c : FlagAlgebra σ}
    (habc : (a + b) =ᵢ[F_forbid] c)
    : b =ᵢ[F_forbid] (c - a)
  :=
  (inducedForbidEq_move_add_left_iff (F_forbid := F_forbid) (a := a) (b := b) (c := c)).1 habc

theorem inducedForbidEq_collect_smul_left_iff
    {F_forbid : FinFlag ∅ₜ} {a b : ℝ} {x y : FlagAlgebra σ}
    : ((a • x + b • x) =ᵢ[F_forbid] y) ↔ (((a + b) • x) =ᵢ[F_forbid] y)
  := by
  constructor
  · intro h
    simpa [add_smul] using h
  · intro h
    simpa [add_smul] using h

theorem inducedForbidEq_collect_smul_right_iff
    {F_forbid : FinFlag ∅ₜ} {a b : ℝ} {x y : FlagAlgebra σ}
    : (y =ᵢ[F_forbid] (a • x + b • x)) ↔ (y =ᵢ[F_forbid] ((a + b) • x))
  := by
  constructor
  · intro h
    simpa [add_smul] using h
  · intro h
    simpa [add_smul] using h

theorem inducedForbidEq_collect_sub_smul_left_iff
    {F_forbid : FinFlag ∅ₜ} {a b : ℝ} {x y : FlagAlgebra σ}
    : ((a • x - b • x) =ᵢ[F_forbid] y) ↔ (((a - b) • x) =ᵢ[F_forbid] y)
  := by
  constructor
  · intro h
    simpa [sub_eq_add_neg, add_smul] using h
  · intro h
    simpa [sub_eq_add_neg, add_smul] using h

theorem inducedForbidEq_collect_sub_smul_right_iff
    {F_forbid : FinFlag ∅ₜ} {a b : ℝ} {x y : FlagAlgebra σ}
    : (y =ᵢ[F_forbid] (a • x - b • x)) ↔ (y =ᵢ[F_forbid] ((a - b) • x))
  := by
  constructor
  · intro h
    simpa [sub_eq_add_neg, add_smul] using h
  · intro h
    simpa [sub_eq_add_neg, add_smul] using h

theorem inducedForbidEq_move_term_left_iff
    {F_forbid : FinFlag ∅ₜ} {a c : FlagAlgebra σ}
    : (a =ᵢ[F_forbid] c) ↔ ((0 : FlagAlgebra σ) =ᵢ[F_forbid] (c - a))
  := by
  constructor
  · intro hac
    have hsum : (a + (0 : FlagAlgebra σ)) =ᵢ[F_forbid] c := by
      simpa using (inducedForbidEq_add_right (h := (0 : FlagAlgebra σ)) hac)
    exact (inducedForbidEq_move_add_left_iff (F_forbid := F_forbid)
      (a := a) (b := (0 : FlagAlgebra σ)) (c := c)).1 hsum
  · intro hzero
    have hsum : (a + (0 : FlagAlgebra σ)) =ᵢ[F_forbid] c :=
      (inducedForbidEq_move_add_left_iff (F_forbid := F_forbid)
        (a := a) (b := (0 : FlagAlgebra σ)) (c := c)).2 hzero
    simpa using hsum

theorem inducedForbidEq_move_term_left
    {F_forbid : FinFlag ∅ₜ} {a c : FlagAlgebra σ}
    (hac : a =ᵢ[F_forbid] c)
    : (0 : FlagAlgebra σ) =ᵢ[F_forbid] (c - a)
  :=
  (inducedForbidEq_move_term_left_iff (F_forbid := F_forbid) (a := a) (c := c)).1 hac

/-- Forbidden inequality is additive (condition-parametric). -/
theorem forbidLEWith_add
    {C : ForbidCondition} {f g f' g' : FlagAlgebra σ}
    (hfg : forbidLEWith C f g) (hf'g' : forbidLEWith C f' g')
    : forbidLEWith C (f + f') (g + g')
  := by
  intro φ₀ hσ hC
  let A : Set (PositiveHomSpace σ) := {φ | φ f ≤ φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ f' ≤ φ g'}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
  have hB : ℙ[φ₀] B = 1 := hf'g' φ₀ hσ hC
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidLE_set_measurable (σ := σ) f g)
      (forbidLE_set_measurable (σ := σ) f' g') hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ (f + f') ≤ φ (g + g')} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hf'g''⟩
    have h₁ : φ f ≤ φ g := by simpa [A] using hfg'
    have h₂ : φ f' ≤ φ g' := by simpa [B] using hf'g''
    calc
      φ (f + f') = φ f + φ f' := by simp [PositiveHom.map_add]
      _ ≤ φ g + φ g' := add_le_add h₁ h₂
      _ = φ (g + g') := by simp [PositiveHom.map_add]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (f + f') ≤ φ (g + g')} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- Forbidden inequality is additive: adding two forbidden inequalities side by side. -/
theorem inducedForbidLE_add
    {F_forbid : FinFlag ∅ₜ} {f g f' g' : FlagAlgebra σ}
    (hfg : f ≤ᵢ[F_forbid] g) (hf'g' : f' ≤ᵢ[F_forbid] g')
    : (f + f') ≤ᵢ[F_forbid] (g + g')
  := forbidLEWith_add hfg hf'g'

theorem inducedForbidLE_add_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤ᵢ[F_forbid] g)
    : (h + f) ≤ᵢ[F_forbid] (h + g)
  :=
  inducedForbidLE_add (inducedForbidLE_refl F_forbid h) hfg

theorem inducedForbidLE_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤ᵢ[F_forbid] g)
    : (f + h) ≤ᵢ[F_forbid] (g + h)
  :=
  inducedForbidLE_add hfg (inducedForbidLE_refl F_forbid h)

/-- Scaling a forbidden inequality by a nonnegative real preserves it (condition-parametric). -/
theorem forbidLEWith_smul_nonneg
    {C : ForbidCondition} {f g : FlagAlgebra σ} {c : ℝ}
    (hc : 0 ≤ c) (hfg : forbidLEWith C f g)
    : forbidLEWith C (c • f) (c • g)
  := by
  intro φ₀ hσ hC
  have hA : ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} = 1 := hfg φ₀ hσ hC
  have hsubset :
      {φ : PositiveHomSpace σ | φ f ≤ φ g} ⊆
      {φ : PositiveHomSpace σ | φ (c • f) ≤ φ (c • g)} := by
    intro φ hφ
    have hfg' : φ f ≤ φ g := by simpa using hφ
    calc
      φ (c • f) = c * φ f := by simp [PositiveHom.map_smul]
      _ ≤ c * φ g := mul_le_mul_of_nonneg_left hfg' hc
      _ = φ (c • g) := by simp [PositiveHom.map_smul]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} := by simpa using hA.symm
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (c • f) ≤ φ (c • g)} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

/-- Scaling a forbidden inequality by a nonnegative real preserves it. -/
theorem inducedForbidLE_smul_nonneg
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ} {c : ℝ}
    (hc : 0 ≤ c) (hfg : f ≤ᵢ[F_forbid] g)
    : (c • f) ≤ᵢ[F_forbid] (c • g)
  := forbidLEWith_smul_nonneg hc hfg

/-! ## Forbidden flags vanish, and flag expansion modulo the forbidden flag -/

/-- A flag `F` whose unlabeled version contains the forbidden flag with positive density
is forced to density `0` under the conditioning: `⟦basisVector F⟧ =ᵢ[F_forbid] 0`. -/
theorem basisVector_inducedForbidEq_zero
    (F_forbid : FinFlag ∅ₜ) (F : FinFlag σ) (hF : flagDensity₁ F_forbid.2 (unlabel F.2) > 0)
    : ⟦basisVector F⟧ =ᵢ[F_forbid] 0
  := by
  intro φ₀ hσ hF_forbid
  have h_nonneg : ∀ φ : PositiveHomSpace σ, 0 ≤ φ ⟦basisVector F⟧ := by
    intro φ
    exact positiveHom_basisVector_ge_zero (PositiveHomSpace.toPosHom φ) F
  have h_measurable :
      Measurable (fun φ : PositiveHomSpace σ => φ ⟦basisVector F⟧) := by
    simpa using
      (positiveHomSpace_eval_continuous (σ := σ) (⟦basisVector F⟧ : FlagAlgebra σ)).measurable
  have h_integrable :
      Integrable
        (fun φ : PositiveHomSpace σ => φ ⟦basisVector F⟧)
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))) := by
    apply Integrable.of_bound
    · exact Measurable.aestronglyMeasurable h_measurable
    · exact Filter.Eventually.of_forall (fun φ => by
        simp only [Real.norm_eq_abs]
        simpa [PositiveHomSpace.toPosHom_basisVector] using flagDensitySpace_abs_le_one φ F)
  have h_integral_zero :
      ∫ φ : PositiveHomSpace σ, φ ⟦basisVector F⟧ ∂(ℙ[φ₀]) = 0 := by
    rw [probMeasure_extend_emptyType_positiveHom_spec]
    simp; left
    simp [downward, downwardFlagVectorQuot, downwardFlagVector_basisVector, downwardFlag]
    simp [smul_quot, PositiveHom.map_smul]
    right
    exact positiveHom_basisVector_eq_zero φ₀ hF hF_forbid
  have h_prob_zero :
      ℙ[φ₀] {φ | φ ⟦basisVector F⟧ = 0} = 1 :=
    ae_zero_of_integral_eq_zero h_nonneg h_measurable (by simpa using h_integrable) h_integral_zero
  simpa [PositiveHomSpace.toPosHom_basisVector] using h_prob_zero

/-- **Family version of basis-vector vanishing.** If some forbidden flag `D ∈ Fs` appears in
`F` with positive density, then `⟦basisVector F⟧` is `familyForbiddenCondition Fs`-zero. -/
theorem basisVector_familyForbidEq_zero
    (Fs : Set (FinFlag ∅ₜ)) (D : FinFlag ∅ₜ) (hD : D ∈ Fs)
    (F : FinFlag σ) (hF : flagDensity₁ D.2 (unlabel F.2) > 0)
    : forbidEqWith (familyForbiddenCondition Fs) (⟦basisVector F⟧ : FlagAlgebra σ) 0
  := by
  intro φ₀ hσ hcond
  have h_nonneg : ∀ φ : PositiveHomSpace σ, 0 ≤ φ ⟦basisVector F⟧ := by
    intro φ
    exact positiveHom_basisVector_ge_zero (PositiveHomSpace.toPosHom φ) F
  have h_measurable :
      Measurable (fun φ : PositiveHomSpace σ => φ ⟦basisVector F⟧) := by
    simpa using
      (positiveHomSpace_eval_continuous (σ := σ) (⟦basisVector F⟧ : FlagAlgebra σ)).measurable
  have h_integrable :
      Integrable
        (fun φ : PositiveHomSpace σ => φ ⟦basisVector F⟧)
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))) := by
    apply Integrable.of_bound
    · exact Measurable.aestronglyMeasurable h_measurable
    · exact Filter.Eventually.of_forall (fun φ => by
        simp only [Real.norm_eq_abs]
        simpa [PositiveHomSpace.toPosHom_basisVector] using flagDensitySpace_abs_le_one φ F)
  have h_integral_zero :
      ∫ φ : PositiveHomSpace σ, φ ⟦basisVector F⟧ ∂(ℙ[φ₀]) = 0 := by
    rw [probMeasure_extend_emptyType_positiveHom_spec]
    simp; left
    simp [downward, downwardFlagVectorQuot, downwardFlagVector_basisVector, downwardFlag]
    simp [smul_quot, PositiveHom.map_smul]
    right
    exact positiveHom_basisVector_eq_zero φ₀ hF (hcond D hD)
  have h_prob_zero :
      ℙ[φ₀] {φ | φ ⟦basisVector F⟧ = 0} = 1 :=
    ae_zero_of_integral_eq_zero h_nonneg h_measurable (by simpa using h_integrable) h_integral_zero
  simpa [PositiveHomSpace.toPosHom_basisVector] using h_prob_zero

/-- **Generic kill-predicate expansion.** Modulo any forbidden condition `C`, a flag
`⟦basisVector F⟧` equals its size-`ℓ` expansion restricted to the *surviving* terms `¬ Kill F'`,
provided every *killed* term `Kill F'` is forced to be `C`-zero (`hkill`). The single-induced-flag
and forbidden-family theorems below are specializations. -/
theorem basisVector_quot_forbidEqWith_sum_of_kill
    (C : ForbidCondition) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    (Kill : FlagWithSize σ ℓ → Prop) [DecidablePred Kill]
    (hkill : ∀ F' : FlagWithSize σ ℓ, Kill F' →
      forbidEqWith C (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ) 0)
    : forbidEqWith C (⟦basisVector F⟧ : FlagAlgebra σ)
      (∑ F' : FlagWithSize σ ℓ with ¬ Kill F',
        (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
  := by
  rw [basisVector_quot_eq_sum F ℓ hℓ]
  have hsplit :
      (∑ x : FlagWithSize σ ℓ,
        (flagDensity₁ F.2 x : ℝ) • (⟦basisVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        =
      (∑ x : FlagWithSize σ ℓ with Kill x,
        (flagDensity₁ F.2 x : ℝ) • (⟦basisVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        +
      (∑ x : FlagWithSize σ ℓ with ¬ Kill x,
        (flagDensity₁ F.2 x : ℝ) • (⟦basisVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun x => Kill x)]
  rw [hsplit]
  nth_rw 2 [← zero_add (∑ F' with ¬ Kill F', _)]
  apply forbidEqWith_add
  · apply forbidEqWith_sum_filter_eq_zero
    intro x _ hx
    exact forbidEqWith_smul_zero (hkill x hx)
  · apply forbidEqWith_refl

/-- Modulo the forbidden flag, a flag `⟦basisVector F⟧` equals its size-`ℓ` expansion
restricted to flags that avoid `F_forbid` (those with `F_forbid`-density `0`). -/
theorem basisVector_quot_inducedForbidEq_sum
    (F_forbid : FinFlag ∅ₜ) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦basisVector F⟧ =ᵢ[F_forbid]
      ∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') = 0,
        (flagDensity₁ F.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧
  := by
  have hfilter :
      Finset.univ.filter (fun F' : FlagWithSize σ ℓ => flagDensity₁ F_forbid.2 (unlabel F') = 0)
        = Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ F_forbid.2 (unlabel F'))) :=
    Finset.filter_congr (fun x _ => by
      constructor
      · intro hx; rw [hx]; exact lt_irrefl 0
      · intro hx; exact le_antisymm (le_of_not_gt hx) (flagListDensity₁_ge_zero F_forbid.2 (unlabel x)))
  rw [show (∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') = 0,
        (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      = Finset.sum (Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ F_forbid.2 (unlabel F'))))
          (fun F' => (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      from by rw [hfilter]]
  exact basisVector_quot_forbidEqWith_sum_of_kill (inducedForbiddenCondition F_forbid) F ℓ hℓ
      (fun x => 0 < flagDensity₁ F_forbid.2 (unlabel x))
      (fun x hx => basisVector_inducedForbidEq_zero F_forbid ⟨ℓ, x⟩ hx)

/-- **Generic kill-predicate product expansion.** The multiplication analogue of
`basisVector_quot_forbidEqWith_sum_of_kill`. -/
theorem basisVector_quot_mul_forbidEqWith_sum_of_kill
    (C : ForbidCondition) (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    (Kill : FlagWithSize σ ℓ → Prop) [DecidablePred Kill]
    (hkill : ∀ F' : FlagWithSize σ ℓ, Kill F' →
      forbidEqWith C (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ) 0)
    : forbidEqWith C ((⟦basisVector F₁⟧ * ⟦basisVector F₂⟧ : FlagAlgebra σ))
      (∑ F' : FlagWithSize σ ℓ with ¬ Kill F',
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
  := by
  rw [basisVector_quot_mul_eq_flagMulWithSize_quot F₁ F₂ ℓ hℓ]
  simp [flagMulWithSize, sum_quot, smul_quot]
  have hsplit :
      (∑ x : FlagWithSize σ ℓ,
        (flagDensity₂ F₁.2 F₂.2 x : ℝ) • (⟦basisVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        =
      (∑ x : FlagWithSize σ ℓ with Kill x,
        (flagDensity₂ F₁.2 F₂.2 x : ℝ) • (⟦basisVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        +
      (∑ x : FlagWithSize σ ℓ with ¬ Kill x,
        (flagDensity₂ F₁.2 F₂.2 x : ℝ) • (⟦basisVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun x => Kill x)]
  rw [hsplit]
  nth_rw 2 [← zero_add (∑ F' with ¬ Kill F', _)]
  apply forbidEqWith_add
  · apply forbidEqWith_sum_filter_eq_zero
    intro x _ hx
    exact forbidEqWith_smul_zero (hkill x hx)
  · apply forbidEqWith_refl

/-- Modulo the forbidden flag, a product `⟦basisVector F₁⟧ * ⟦basisVector F₂⟧` equals its
size-`ℓ` expansion restricted to flags that avoid `F_forbid`. -/
theorem basisVector_quot_mul_inducedForbidEq_sum
    (F_forbid : FinFlag ∅ₜ) (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    : (⟦basisVector F₁⟧ * ⟦basisVector F₂⟧ : FlagAlgebra σ) =ᵢ[F_forbid]
      ∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') = 0,
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧
  := by
  have hfilter :
      Finset.univ.filter (fun F' : FlagWithSize σ ℓ => flagDensity₁ F_forbid.2 (unlabel F') = 0)
        = Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ F_forbid.2 (unlabel F'))) :=
    Finset.filter_congr (fun x _ => by
      constructor
      · intro hx; rw [hx]; exact lt_irrefl 0
      · intro hx; exact le_antisymm (le_of_not_gt hx) (flagListDensity₁_ge_zero F_forbid.2 (unlabel x)))
  rw [show (∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') = 0,
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      = Finset.sum (Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ F_forbid.2 (unlabel F'))))
          (fun F' => (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      from by rw [hfilter]]
  exact basisVector_quot_mul_forbidEqWith_sum_of_kill (inducedForbiddenCondition F_forbid) F₁ F₂ ℓ hℓ
      (fun x => 0 < flagDensity₁ F_forbid.2 (unlabel x))
      (fun x hx => basisVector_inducedForbidEq_zero F_forbid ⟨ℓ, x⟩ hx)

/-- **Forbidden-family expansion** (Part 4). Specialization of the generic kill-predicate
expansion to `familyForbiddenCondition Fs`: kill every term whose underlying flag contains some
`D ∈ Fs` with positive density; the surviving terms are exactly those with zero density of every
`D ∈ Fs`. Appropriate for hereditary classes encoded as all forbidden induced flags outside the
class, and for ordinary `H`-free semantics through `forbiddenFlags H`. -/
theorem basisVector_quot_familyForbidEq_sum
    (Fs : Set (FinFlag ∅ₜ)) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    [DecidablePred (fun F' : FlagWithSize σ ℓ => ∃ D ∈ Fs, flagDensity₁ D.2 (unlabel F') > 0)]
    : forbidEqWith (familyForbiddenCondition Fs) (⟦basisVector F⟧ : FlagAlgebra σ)
      (∑ F' : FlagWithSize σ ℓ with ¬ (∃ D ∈ Fs, flagDensity₁ D.2 (unlabel F') > 0),
        (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
  := basisVector_quot_forbidEqWith_sum_of_kill (familyForbiddenCondition Fs) F ℓ hℓ
      (fun F' => ∃ D ∈ Fs, flagDensity₁ D.2 (unlabel F') > 0)
      (fun F' hF' => by
        obtain ⟨D, hD, hDF'⟩ := hF'
        exact basisVector_familyForbidEq_zero Fs D hD ⟨ℓ, F'⟩ hDF')

/-! ### Finite-family `forbidEq H` expansions (subgraph forbidding, Route B / G3)

The ordinary `_ofMem` lemmas (further below) kill by a *single* forbidden flag's induced density —
exact for complete-graph forbids (induced = subgraph there). For an arbitrary forbidden graph `H`
under *subgraph* semantics, the killed flags are those containing **some** member of a finite family
`Fs ⊆ forbiddenFlags H` (e.g. the supergraphs of `H`) with positive induced density. These wrappers
state the `=[H]` expansion with that finite-family kill, reusing the generic kill lemmas and the
family vanishing `basisVector_familyForbidEq_zero` (each member is in `forbiddenFlags H`, so each
killed term is `forbiddenCondition H`-zero). Matching the survivor set to the generator's
subgraph-`H`-free flag set is done at the generator (G4). -/

/-- **Finite-family ordinary expansion** (subgraph forbidding). Survivors are the flags with zero
induced density of *every* `D ∈ Fs`; this is the family analogue of `basisVector_quot_forbidEq_sum_ofMem`. -/
theorem basisVector_quot_forbidEq_sum_ofFamilyMem
    {N : ℕ} {H : SimpleGraph (Fin N)} (Fs : List (FinFlag ∅ₜ))
    (hmem : ∀ D ∈ Fs, D ∈ forbiddenFlags H) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦basisVector F⟧ =[H]
      ∑ F' : FlagWithSize σ ℓ with (∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0),
        (flagDensity₁ F.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧ := by
  have hfilter :
      Finset.univ.filter (fun F' : FlagWithSize σ ℓ => ∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0)
        = Finset.univ.filter (fun F' => ¬ (∃ D ∈ Fs, 0 < flagDensity₁ D.2 (unlabel F'))) :=
    Finset.filter_congr (fun x _ => by
      constructor
      · intro h hex
        obtain ⟨D, hD, hpos⟩ := hex
        rw [h D hD] at hpos; exact lt_irrefl 0 hpos
      · intro h D hD
        by_contra hne
        exact h ⟨D, hD, lt_of_le_of_ne (flagListDensity₁_ge_zero D.2 (unlabel x)) (Ne.symm hne)⟩)
  rw [show (∑ F' : FlagWithSize σ ℓ with (∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0),
        (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      = Finset.sum (Finset.univ.filter (fun F' => ¬ (∃ D ∈ Fs, 0 < flagDensity₁ D.2 (unlabel F'))))
          (fun F' => (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      from by rw [hfilter]]
  exact basisVector_quot_forbidEqWith_sum_of_kill (forbiddenCondition H) F ℓ hℓ
      (fun F' => ∃ D ∈ Fs, 0 < flagDensity₁ D.2 (unlabel F'))
      (fun F' hF' => by
        obtain ⟨D, hD, hDF'⟩ := hF'
        exact basisVector_familyForbidEq_zero (forbiddenFlags H) D (hmem D hD) ⟨ℓ, F'⟩ hDF')

/-- **Finite-family ordinary product expansion** (subgraph forbidding). The multiplication analogue
of `basisVector_quot_forbidEq_sum_ofFamilyMem`. -/
theorem basisVector_quot_mul_forbidEq_sum_ofFamilyMem
    {N : ℕ} {H : SimpleGraph (Fin N)} (Fs : List (FinFlag ∅ₜ))
    (hmem : ∀ D ∈ Fs, D ∈ forbiddenFlags H) (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    : (⟦basisVector F₁⟧ * ⟦basisVector F₂⟧ : FlagAlgebra σ) =[H]
      ∑ F' : FlagWithSize σ ℓ with (∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0),
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧ := by
  have hfilter :
      Finset.univ.filter (fun F' : FlagWithSize σ ℓ => ∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0)
        = Finset.univ.filter (fun F' => ¬ (∃ D ∈ Fs, 0 < flagDensity₁ D.2 (unlabel F'))) :=
    Finset.filter_congr (fun x _ => by
      constructor
      · intro h hex
        obtain ⟨D, hD, hpos⟩ := hex
        rw [h D hD] at hpos; exact lt_irrefl 0 hpos
      · intro h D hD
        by_contra hne
        exact h ⟨D, hD, lt_of_le_of_ne (flagListDensity₁_ge_zero D.2 (unlabel x)) (Ne.symm hne)⟩)
  rw [show (∑ F' : FlagWithSize σ ℓ with (∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0),
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      = Finset.sum (Finset.univ.filter (fun F' => ¬ (∃ D ∈ Fs, 0 < flagDensity₁ D.2 (unlabel F'))))
          (fun F' => (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      from by rw [hfilter]]
  exact basisVector_quot_mul_forbidEqWith_sum_of_kill (forbiddenCondition H) F₁ F₂ ℓ hℓ
      (fun F' => ∃ D ∈ Fs, 0 < flagDensity₁ D.2 (unlabel F'))
      (fun F' hF' => by
        obtain ⟨D, hD, hDF'⟩ := hF'
        exact basisVector_familyForbidEq_zero (forbiddenFlags H) D (hmem D hD) ⟨ℓ, F'⟩ hDF')

lemma flagType_asEmptyTypeAlgebra_emptyType_eq_one
    : ⟨∅ₜ⟩₀ = 1
  := by
  show _ = ⟦basisVector ⟨0, default⟩⟧
  simp [flagType_asEmptyTypeAlgebra]
  congr
  apply Quotient.sound
  exact Nonempty.intro {
    graph_iso := SimpleGraph.Iso.refl
    type_preserve := List.ofFn_inj.mp rfl
  }

lemma probMeasure_extend_emptyType_positiveHom_singleton_eq_one
    (φ₀ : PositiveHom ∅ₜ)
    : probMeasure_extend_emptyType_positiveHom (σ := ∅ₜ) φ₀
        (by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one])
        {⟨φ₀.coe, ⟨φ₀, rfl⟩⟩} = 1
  := by
  have hσ : φ₀ ⟨∅ₜ⟩₀ > 0 := by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one]
  let a₀ : PositiveHomSpace ∅ₜ := ⟨φ₀.coe, ⟨φ₀, rfl⟩⟩
  have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ
  have hspec' : ∀ f : FlagAlgebra ∅ₜ, ∫ φ : PositiveHomSpace ∅ₜ, φ f ∂ℙ[φ₀] = φ₀ f := by
    intro f
    have h := hspec f
    simpa [downward_emptyType, div_one] using h
  have h_int_var : ∀ f : FlagAlgebra ∅ₜ,
      ∫ φ : PositiveHomSpace ∅ₜ, ((φ f) - (φ₀ f))^2 ∂ℙ[φ₀] = 0 := by
    intro f
    let q : FlagAlgebra ∅ₜ :=
      (f - (φ₀ f) • (1 : FlagAlgebra ∅ₜ)) * (f - (φ₀ f) • (1 : FlagAlgebra ∅ₜ))
    have hq : ∫ φ : PositiveHomSpace ∅ₜ, φ q ∂ℙ[φ₀] = φ₀ q := hspec' q
    calc
      ∫ φ : PositiveHomSpace ∅ₜ, ((φ f) - (φ₀ f))^2 ∂ℙ[φ₀]
          = ∫ φ : PositiveHomSpace ∅ₜ, φ q ∂ℙ[φ₀] := by
              apply integral_congr_ae
              filter_upwards with φ
              rw [pow_two]
              simp [q, PositiveHom.map_mul, PositiveHom.map_sub,
                PositiveHom.map_smul, PositiveHom.map_one]
      _ = φ₀ q := hq
      _ = 0 := by
            simp [q, PositiveHom.map_mul, PositiveHom.map_sub,
              PositiveHom.map_smul, PositiveHom.map_one]
  have h_unit_ae : ∀ F : FinFlag ∅ₜ,
      ℙ[φ₀] {φ : PositiveHomSpace ∅ₜ | φ ⟦basisVector F⟧ = φ₀ ⟦basisVector F⟧} = 1 := by
    intro F
    let g : PositiveHomSpace ∅ₜ → ℝ :=
      fun φ => ((φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧))^2
    have hg_nonneg : ∀ φ : PositiveHomSpace ∅ₜ, 0 ≤ g φ := by
      intro φ
      positivity
    have hg_measurable : Measurable g := by
      dsimp [g]
      have hsub : Measurable (fun φ : PositiveHomSpace ∅ₜ =>
          (φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧)) :=
        Measurable.sub
          ((positiveHomSpace_eval_continuous (σ := ∅ₜ)
            (⟦basisVector F⟧ : FlagAlgebra ∅ₜ)).measurable)
          measurable_const
      simpa [pow_two] using Measurable.mul hsub hsub
    have hg_integrable : Integrable g ℙ[φ₀] := by
      apply Integrable.of_bound
      · exact Measurable.aestronglyMeasurable hg_measurable
      · exact Filter.Eventually.of_forall (fun φ => by
          dsimp [g]
          have hφ_abs : |φ ⟦basisVector F⟧| ≤ 1 := by
            simpa [PositiveHomSpace.toPosHom_basisVector] using flagDensitySpace_abs_le_one φ F
          have hφ₀_abs : |φ₀ ⟦basisVector F⟧| ≤ 1 := by
            rw [abs_le]
            constructor
            · linarith [positiveHom_basisVector_ge_zero φ₀ F]
            · exact positiveHom_basisVector_le_one φ₀ F
          have hsub_abs : |(φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧)| ≤ 2 := by
            calc
              |(φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧)|
                  ≤ |φ ⟦basisVector F⟧| + |φ₀ ⟦basisVector F⟧| := abs_sub _ _
              _ ≤ 1 + 1 := add_le_add hφ_abs hφ₀_abs
              _ = 2 := by norm_num
          have hsub_nonneg : 0 ≤ |(φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧)| := abs_nonneg _
          have hsq_le : |(φ ⟦basisVector F⟧ - φ₀ ⟦basisVector F⟧)| ^ 2 ≤ 4 := by
            nlinarith [hsub_abs, hsub_nonneg]
          have hnorm_eq : ‖((φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧))^2‖
              = |(φ ⟦basisVector F⟧ - φ₀ ⟦basisVector F⟧)| ^ 2 := by
            simp [Real.norm_eq_abs, pow_two]
          simpa [hnorm_eq] using hsq_le)
    have hg_int_zero : ∫ φ : PositiveHomSpace ∅ₜ, g φ ∂ℙ[φ₀] = 0 := by
      simpa [g] using h_int_var (⟦basisVector F⟧ : FlagAlgebra ∅ₜ)
    have h_sq_zero :
        ℙ[φ₀] {φ : PositiveHomSpace ∅ₜ |
          ((φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧))^2 = 0} = 1 := by
      exact ae_zero_of_integral_eq_zero hg_nonneg hg_measurable hg_integrable hg_int_zero
    have h_sub_eq :
        {φ : PositiveHomSpace ∅ₜ |
          (φ ⟦basisVector F⟧) - (φ₀ ⟦basisVector F⟧) = 0}
        = {φ : PositiveHomSpace ∅ₜ | φ ⟦basisVector F⟧ = φ₀ ⟦basisVector F⟧} := by
      ext φ
      constructor
      · intro hφ
        exact sub_eq_zero.mp hφ
      · intro hφ
        exact sub_eq_zero.mpr hφ
    simpa [h_sub_eq] using h_sq_zero
  have h_all_unit_ae :
      ℙ[φ₀] (⋂ F : FinFlag ∅ₜ,
        {φ : PositiveHomSpace ∅ₜ | φ ⟦basisVector F⟧ = φ₀ ⟦basisVector F⟧}) = 1 := by
    refine prob_iInter_eq_one_of_all_prob_eq_one ?_ h_unit_ae
    intro F
    simpa [PositiveHom.map_smul, PositiveHom.map_one] using
      (forbidEq_set_measurable (σ := ∅ₜ)
        (⟦basisVector F⟧ : FlagAlgebra ∅ₜ)
        ((φ₀ ⟦basisVector F⟧) • (1 : FlagAlgebra ∅ₜ)))
  have hsubset_singleton :
      (⋂ F : FinFlag ∅ₜ,
        {φ : PositiveHomSpace ∅ₜ | φ ⟦basisVector F⟧ = φ₀ ⟦basisVector F⟧}) ⊆ {a₀}
    := by
    intro φ hφ
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have hval_eq : φ.val = a₀.val := by
      ext F
      have hF : φ ⟦basisVector F⟧ = φ₀ ⟦basisVector F⟧ := (Set.mem_iInter.mp hφ) F
      calc
        φ.val F = φ ⟦basisVector F⟧ := by
          symm
          simpa using (PositiveHomSpace.toPosHom_basisVector φ F)
        _ = φ₀ ⟦basisVector F⟧ := hF
        _ = (PositiveHomSpace.toPosHom a₀) ⟦basisVector F⟧ := by simp [ha₀_toPosHom]
        _ = a₀.val F := by simpa using (PositiveHomSpace.toPosHom_basisVector a₀ F)
    have hφa₀ : φ = a₀ := SetCoe.ext hval_eq
    simpa [Set.mem_singleton_iff] using hφa₀
  have hsingle' : ℙ[φ₀] ({a₀} : Set (PositiveHomSpace ∅ₜ)) = 1 := by
    apply le_antisymm
    · exact ProbabilityMeasure.apply_le_one ℙ[φ₀] _
    · calc
        1 = ℙ[φ₀] (⋂ F : FinFlag ∅ₜ,
              {a : PositiveHomSpace ∅ₜ | a ⟦basisVector F⟧ = φ₀ ⟦basisVector F⟧}) := by
                simpa using h_all_unit_ae.symm
        _ ≤ ℙ[φ₀] {a₀} := ProbabilityMeasure.apply_mono ℙ[φ₀] hsubset_singleton
  simpa [a₀, Set.setOf_eq_eq_singleton] using hsingle'

/-! ## Empty-type variants and their equivalence with the probabilistic relations -/

/-- Empty-type form of `forbidEqWith`: for the empty type `∅ₜ`, the deterministic
statement that every base homomorphism satisfying `C` gives the same value to `f`
and `g`. -/
def forbidEq_emptyTypeWith
    (C : ForbidCondition) (f g : FlagAlgebra ∅ₜ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), C φ₀ → φ₀ f = φ₀ g

/-- Empty-type form of `forbidLEWith`: for the empty type `∅ₜ`, the deterministic
statement that every base homomorphism satisfying `C` evaluates `f` below `g`. -/
def forbidLE_emptyTypeWith
    (C : ForbidCondition) (f g : FlagAlgebra ∅ₜ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), C φ₀ → φ₀ f ≤ φ₀ g

/-- Empty-type form of `inducedForbidEq`: for the empty type `∅ₜ`, the deterministic statement
that every base homomorphism `φ₀` killing `F_forbid` satisfies `φ₀ f = φ₀ g`. -/
def inducedForbidEq_emptyType
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ) : Prop
  :=
  forbidEq_emptyTypeWith (inducedForbiddenCondition F_forbid) f g

/-- Empty-type form of `inducedForbidLE`: for the empty type `∅ₜ`, the deterministic statement
that every base homomorphism `φ₀` killing `F_forbid` satisfies `φ₀ f ≤ φ₀ g`. -/
def inducedForbidLE_emptyType
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ) : Prop
  :=
  forbidLE_emptyTypeWith (inducedForbiddenCondition F_forbid) f g

/-- Empty-type equality modulo the ordinary `H`-free condition. -/
noncomputable def forbidEq_emptyType {m : ℕ}
    (H : SimpleGraph (Fin m)) (f g : FlagAlgebra ∅ₜ) : Prop :=
  forbidEq_emptyTypeWith (forbiddenCondition H) f g

/-- Empty-type order modulo the ordinary `H`-free condition. -/
noncomputable def forbidLE_emptyType {m : ℕ}
    (H : SimpleGraph (Fin m)) (f g : FlagAlgebra ∅ₜ) : Prop :=
  forbidLE_emptyTypeWith (forbiddenCondition H) f g

-- Notation: `f =ᵢ[F]₀ g` / `f ≤ᵢ[F]₀ g` for the empty-type variants.
notation f "=ᵢ[" F_forbid "]₀" g => inducedForbidEq_emptyType F_forbid f g
notation f "≤ᵢ[" F_forbid "]₀" g => inducedForbidLE_emptyType F_forbid f g
notation f "=[" H "]₀" g => forbidEq_emptyType H f g
notation f "≤[" H "]₀" g => forbidLE_emptyType H f g

theorem inducedForbidEq_emptyType_symm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (hf_eq_g : f =ᵢ[F_forbid]₀ g)
    : g =ᵢ[F_forbid]₀ f
  := by
  intro φ₀ hF_forbid
  exact (hf_eq_g φ₀ hF_forbid).symm

theorem inducedForbidEq_emptyType_implies_inducedForbidLE_emptyType
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (hf_eq_g : f =ᵢ[F_forbid]₀ g)
    : f ≤ᵢ[F_forbid]₀ g
  := by
  intro φ₀ hF_forbid
  exact le_of_eq (hf_eq_g φ₀ hF_forbid)

theorem inducedForbidLE_emptyType_antisymm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (hfg : f ≤ᵢ[F_forbid]₀ g) (hgf : g ≤ᵢ[F_forbid]₀ f)
    : f =ᵢ[F_forbid]₀ g
  := by
  intro φ₀ hF_forbid
  exact le_antisymm (hfg φ₀ hF_forbid) (hgf φ₀ hF_forbid)

/-- For the empty type, the deterministic relation `≤ᵢ[F]₀` is equivalent to the
probabilistic relation `≤ᵢ[F]`. -/
theorem inducedForbidLE_emptyType_iff_inducedForbidLE
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ)
    : (f ≤ᵢ[F_forbid]₀ g) ↔ (f ≤ᵢ[F_forbid] g)
  := by
  constructor
  · intro hfg φ₀ hσ hF_forbid
    let a₀ : PositiveHomSpace ∅ₜ := (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)
    let S : Set (PositiveHomSpace ∅ₜ) := ({a₀} : Set (PositiveHomSpace ∅ₜ))
    let A : Set (PositiveHomSpace ∅ₜ) := {φ | φ f ≤ φ g}
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have ha₀A : a₀ ∈ A := by
      have ha₀A' : a₀ f ≤ a₀ g := by
        simpa [ha₀_toPosHom] using (hfg φ₀ hF_forbid)
      simpa [A] using ha₀A'
    have hsubset : S ⊆ A := by
      intro φ hφ
      have hEq : φ = a₀ := by simpa [S] using hφ
      subst hEq
      exact ha₀A
    have hsingle : ℙ[φ₀] S = 1 := by
      simpa [S, a₀, Set.setOf_eq_eq_singleton] using
        probMeasure_extend_emptyType_positiveHom_singleton_eq_one φ₀
    apply le_antisymm
    · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) A
    · calc
        1 = ℙ[φ₀] S := by simpa using hsingle.symm
        _ ≤ ℙ[φ₀] A := ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset
  · intro hfg φ₀ hF_forbid
    have hσ : φ₀ ⟨∅ₜ⟩₀ > 0 := by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one]
    let a₀ : PositiveHomSpace ∅ₜ := (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)
    let S : Set (PositiveHomSpace ∅ₜ) := ({a₀} : Set (PositiveHomSpace ∅ₜ))
    let A : Set (PositiveHomSpace ∅ₜ) := {φ | φ f ≤ φ g}
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
    have hsingle : ℙ[φ₀] S = 1 := by
      simpa [S, a₀, Set.setOf_eq_eq_singleton] using
        probMeasure_extend_emptyType_positiveHom_singleton_eq_one φ₀
    have hinter : ℙ[φ₀] (S ∩ A) = 1 := by
      apply prob_inter_eq_one_of_prob_eq_one
      · simp [S]
      · exact (forbidLE_set_measurable (σ := ∅ₜ) f g)
      · exact hsingle
      · exact hA
    have ha₀A : a₀ ∈ A := by
      by_contra ha₀A
      have hempty : (S ∩ A : Set (PositiveHomSpace ∅ₜ)) = ∅ := by
        ext φ
        constructor
        · intro hφ
          rcases hφ with ⟨hS, hAφ⟩
          have hEq : φ = a₀ := by simpa [S] using hS
          subst hEq
          exact (ha₀A hAφ).elim
        · intro hφ
          exact False.elim hφ
      have hzero : ℙ[φ₀] (S ∩ A) = 0 := by
        simp [hempty]
      have : (1 : NNReal) = 0 := by
        calc
          (1 : NNReal) = ℙ[φ₀] (S ∩ A) := by simpa using hinter.symm
          _ = 0 := hzero
      exact one_ne_zero this
    have ha₀A' : a₀ f ≤ a₀ g := by
      simpa [A] using ha₀A
    simpa [ha₀_toPosHom] using ha₀A'

/-- Condition-parametric version of `inducedForbidLE_emptyType_iff_inducedForbidLE`. -/
theorem forbidLE_emptyTypeWith_iff_forbidLEWith
    (C : ForbidCondition) (f g : FlagAlgebra ∅ₜ)
    : forbidLE_emptyTypeWith C f g ↔ forbidLEWith C f g
  := by
  constructor
  · intro hfg φ₀ hσ hC
    let a₀ : PositiveHomSpace ∅ₜ := (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)
    let S : Set (PositiveHomSpace ∅ₜ) := ({a₀} : Set (PositiveHomSpace ∅ₜ))
    let A : Set (PositiveHomSpace ∅ₜ) := {φ | φ f ≤ φ g}
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have ha₀A : a₀ ∈ A := by
      have ha₀A' : a₀ f ≤ a₀ g := by
        simpa [ha₀_toPosHom] using (hfg φ₀ hC)
      simpa [A] using ha₀A'
    have hsubset : S ⊆ A := by
      intro φ hφ
      have hEq : φ = a₀ := by simpa [S] using hφ
      subst hEq
      exact ha₀A
    have hsingle : ℙ[φ₀] S = 1 := by
      simpa [S, a₀, Set.setOf_eq_eq_singleton] using
        probMeasure_extend_emptyType_positiveHom_singleton_eq_one φ₀
    apply le_antisymm
    · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) A
    · calc
        1 = ℙ[φ₀] S := by simpa using hsingle.symm
        _ ≤ ℙ[φ₀] A := ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset
  · intro hfg φ₀ hC
    have hσ : φ₀ ⟨∅ₜ⟩₀ > 0 := by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one]
    let a₀ : PositiveHomSpace ∅ₜ := (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)
    let S : Set (PositiveHomSpace ∅ₜ) := ({a₀} : Set (PositiveHomSpace ∅ₜ))
    let A : Set (PositiveHomSpace ∅ₜ) := {φ | φ f ≤ φ g}
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hC
    have hsingle : ℙ[φ₀] S = 1 := by
      simpa [S, a₀, Set.setOf_eq_eq_singleton] using
        probMeasure_extend_emptyType_positiveHom_singleton_eq_one φ₀
    have hinter : ℙ[φ₀] (S ∩ A) = 1 := by
      apply prob_inter_eq_one_of_prob_eq_one
      · simp [S]
      · exact (forbidLE_set_measurable (σ := ∅ₜ) f g)
      · exact hsingle
      · exact hA
    have ha₀A : a₀ ∈ A := by
      by_contra ha₀A
      have hempty : (S ∩ A : Set (PositiveHomSpace ∅ₜ)) = ∅ := by
        ext φ
        constructor
        · intro hφ
          rcases hφ with ⟨hS, hA'⟩
          have hEq : φ = a₀ := by simpa [S] using hS
          subst hEq
          exact (ha₀A hA').elim
        · intro hφ
          exact False.elim hφ
      have hzero : ℙ[φ₀] (S ∩ A) = 0 := by
        simp [hempty]
      have : (1 : NNReal) = 0 := by
        calc
          (1 : NNReal) = ℙ[φ₀] (S ∩ A) := by simpa using hinter.symm
          _ = 0 := hzero
      exact one_ne_zero this
    have ha₀A' : a₀ f ≤ a₀ g := by
      simpa [A] using ha₀A
    simpa [ha₀_toPosHom] using ha₀A'

/-- For the empty type, the deterministic relation `=ᵢ[F]₀` is equivalent to the
probabilistic relation `=ᵢ[F]`. -/
theorem inducedForbidEq_emptyType_iff_inducedForbidEq
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ)
    : (f =ᵢ[F_forbid]₀ g) ↔ (f =ᵢ[F_forbid] g)
  := by
  constructor
  · intro hfg
    apply inducedForbidLE_antisymm <;> rw [← inducedForbidLE_emptyType_iff_inducedForbidLE]
    · exact inducedForbidEq_emptyType_implies_inducedForbidLE_emptyType hfg
    · exact inducedForbidEq_emptyType_implies_inducedForbidLE_emptyType (inducedForbidEq_emptyType_symm hfg)
  · intro hfg
    apply inducedForbidLE_emptyType_antisymm <;> rw [inducedForbidLE_emptyType_iff_inducedForbidLE]
    · exact inducedForbidLE_of_inducedForbidEq hfg
    · exact inducedForbidLE_of_inducedForbidEq (inducedForbidEq_symm hfg)

/-! ## Downward (unlabeling) monotonicity -/

/-- Empty-type form of downward monotonicity (condition-parametric): if `0 ≤ f` modulo any
forbidden condition `C` for a labeled `f`, then its unlabeling `⟦f⟧₀` is `C`-nonnegative.
This is the main soundness theorem that stays meaningful for arbitrary relative constraints
(e.g. an equality-slice ensemble `C_Y φ₀ := φ₀ ∈ Y`), where there is no basis flag to kill. -/
theorem downward_forbidLEWith_nonneg_emptyType
    {C : ForbidCondition} {f : FlagAlgebra σ} (hf : forbidLEWith C 0 f)
    : forbidLE_emptyTypeWith C (0 : FlagAlgebra ∅ₜ) ⟦f⟧₀
  := by
  intro φ₀ hC
  simp only [PositiveHom.map_zero]
  have hσ_nonneg : 0 ≤ φ₀ ⟨σ⟩₀ := positiveHom_basisVector_ge_zero φ₀ _
  rcases eq_or_lt_of_le hσ_nonneg with hσ_zero | hσ_pos
  · have hzero : φ₀ ⟦f⟧₀ = 0 := downward_zero_at_hom (σ := σ) φ₀ hσ_zero.symm f
    simp only [hzero, le_refl]
  · have hprob : ℙ[φ₀] {φ : PositiveHomSpace σ | 0 ≤ φ f} = 1 := by
      simpa using (hf φ₀ hσ_pos hC)
    have hprob_zero :
        ℙ[φ₀] {φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f} = 1 := by
      simpa [PositiveHom.map_zero] using hprob
    have hprob_zero_measure :
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))
          {φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f}) = 1 := by
      have hprob_zero_toNNReal :
          (((ℙ[φ₀] : Measure (PositiveHomSpace σ))
            {φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f}).toNNReal) = 1 := by
        simpa [ProbabilityMeasure.mk_apply] using hprob_zero
      rw [ENNReal.toNNReal_eq_one_iff] at hprob_zero_toNNReal
      exact hprob_zero_toNNReal
    have hcompl_zero :
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))
          ({φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f}ᶜ)) = 0 := by
      exact (prob_compl_eq_zero_iff
        (μ := (ℙ[φ₀] : Measure (PositiveHomSpace σ)))
        (forbidLE_set_measurable (σ := σ) (0 : FlagAlgebra σ) f)).mpr hprob_zero_measure
    have h_ae_zero :
        ∀ᵐ φ : PositiveHomSpace σ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
          φ (0 : FlagAlgebra σ) ≤ φ f := by
      exact (mem_ae_iff).2 hcompl_zero
    have h_ae : ∀ᵐ φ : PositiveHomSpace σ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)), 0 ≤ φ f := by
      filter_upwards [h_ae_zero] with φ hφ
      simpa [PositiveHom.map_zero] using hφ
    have hint_nonneg : 0 ≤ ∫ φ : PositiveHomSpace σ, φ f ∂(ℙ[φ₀]) := by
      exact integral_nonneg_of_ae h_ae
    have hspec := probMeasure_extend_emptyType_positiveHom_spec (σ := σ) (φ₀ := φ₀) hσ_pos f
    have hden_pos : 0 < φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ := positiveHom_one_downward_pos hσ_pos
    have hfrac_nonneg : 0 ≤ (φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) := by
      simpa [hspec] using hint_nonneg
    have hmul_nonneg :
        0 ≤ ((φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀)) * (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) := by
      exact mul_nonneg hfrac_nonneg (le_of_lt hden_pos)
    have : 0 ≤ φ₀ ⟦f⟧₀ := by
      have hden_ne : (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) ≠ 0 := ne_of_gt hden_pos
      simpa [hden_ne] using hmul_nonneg
    exact this

/-- Empty-type form of downward monotonicity: if `0 ≤ᵢ[F_forbid] f` for a labeled `f`,
then its unlabeling `⟦f⟧₀` is forbidden-nonnegative. -/
theorem downward_inducedForbidLE_nonneg_emptyType
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : 0 ≤ᵢ[F_forbid] f)
    : (0 : FlagAlgebra ∅ₜ) ≤ᵢ[F_forbid]₀ ⟦f⟧₀
  := downward_forbidLEWith_nonneg_emptyType hf

/-- Downward monotonicity (condition-parametric): if `0 ≤ f` modulo `C` then `⟦f⟧₀` is
`C`-nonnegative. The main soundness theorem meaningful for arbitrary relative constraints. -/
theorem downward_forbidLEWith_nonneg
    {C : ForbidCondition} {f : FlagAlgebra σ} (hf : forbidLEWith C 0 f)
    : forbidLEWith C (0 : FlagAlgebra ∅ₜ) ⟦f⟧₀
  := by
  have h0 : forbidLE_emptyTypeWith C (0 : FlagAlgebra ∅ₜ) ⟦f⟧₀ :=
    downward_forbidLEWith_nonneg_emptyType (σ := σ) hf
  exact (forbidLE_emptyTypeWith_iff_forbidLEWith C (0 : FlagAlgebra ∅ₜ) ⟦f⟧₀).1 h0

/-- Downward monotonicity: if `0 ≤ᵢ[F_forbid] f` then the unlabeling `⟦f⟧₀` is
forbidden-nonnegative. -/
theorem downward_inducedForbidLE_nonneg
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : 0 ≤ᵢ[F_forbid] f)
    : 0 ≤ᵢ[F_forbid] ⟦f⟧₀
  := downward_forbidLEWith_nonneg hf

theorem inducedForbidLE_move_add_left_iff
    {F_forbid : FinFlag ∅ₜ} {a b c : FlagAlgebra σ}
    : ((a + b) ≤ᵢ[F_forbid] c) ↔ (b ≤ᵢ[F_forbid] (c - a))
  := by
  constructor
  · intro habc
    have h1 := inducedForbidLE_add_right (h := -a) habc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  · intro hbc
    have h1 := inducedForbidLE_add_left (h := a) hbc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1

theorem inducedForbidLE_move_add_left
    {F_forbid : FinFlag ∅ₜ} {a b c : FlagAlgebra σ}
    (habc : (a + b) ≤ᵢ[F_forbid] c)
    : b ≤ᵢ[F_forbid] (c - a)
  :=
  (inducedForbidLE_move_add_left_iff (F_forbid := F_forbid) (a := a) (b := b) (c := c)).1 habc

theorem inducedForbidLE_move_term_left_iff
    {F_forbid : FinFlag ∅ₜ} {a c : FlagAlgebra σ}
    : (a ≤ᵢ[F_forbid] c) ↔ ((0 : FlagAlgebra σ) ≤ᵢ[F_forbid] (c - a))
  := by
  simpa using
    (inducedForbidLE_move_add_left_iff (F_forbid := F_forbid) (a := a) (b := (0 : FlagAlgebra σ)) (c := c))

theorem inducedForbidLE_move_term_left
    {F_forbid : FinFlag ∅ₜ} {a c : FlagAlgebra σ}
    (hac : a ≤ᵢ[F_forbid] c)
    : (0 : FlagAlgebra σ) ≤ᵢ[F_forbid] (c - a)
  :=
  (inducedForbidLE_move_term_left_iff (F_forbid := F_forbid) (a := a) (c := c)).1 hac

/-- Downward monotonicity for equalities: if `f =ᵢ[F_forbid] 0` then `⟦f⟧₀ =ᵢ[F_forbid] 0`. -/
theorem downward_inducedForbidEq_zero
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : f =ᵢ[F_forbid] 0)
    : ⟦f⟧₀ =ᵢ[F_forbid] 0
  := by
  refine inducedForbidLE_antisymm ?_ ?_
  · have hf' : (-1 • f) =ᵢ[F_forbid] 0 := by
      refine inducedForbidEq_move_term_left_iff.mpr ?_
      simp only [Int.reduceNeg, neg_smul, one_smul, sub_neg_eq_add, zero_add]
      exact inducedForbidEq_symm hf
    simp only [Int.reduceNeg, neg_smul, one_smul] at hf'
    rw [inducedForbidLE_move_term_left_iff]
    simp only [zero_sub, ← downward_neg]
    exact downward_inducedForbidLE_nonneg (inducedForbidLE_of_inducedForbidEq (inducedForbidEq_symm hf'))
  · exact downward_inducedForbidLE_nonneg (inducedForbidLE_of_inducedForbidEq (inducedForbidEq_symm hf))

/-- Downward monotonicity for equalities: a forbidden equality `a =ᵢ[F_forbid] b` descends
to the unlabelings `⟦a⟧₀ =ᵢ[F_forbid] ⟦b⟧₀`. -/
theorem downward_inducedForbidEq_equal_flags
    {F_forbid : FinFlag ∅ₜ} {a b : FlagAlgebra σ}
    (hab : a =ᵢ[F_forbid] b)
    : ⟦a⟧₀ =ᵢ[F_forbid] ⟦b⟧₀
  := by
  refine inducedForbidEq_move_term_left_iff.mpr ?_
  rw [← downward_sub]
  exact inducedForbidEq_symm (downward_inducedForbidEq_zero ((inducedForbidEq_symm (inducedForbidEq_move_term_left hab))))

theorem inducedForbidLE_rw_left_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h k : FlagAlgebra σ}
    (hfg : f =ᵢ[F_forbid] g)
    : ((f + h) ≤ᵢ[F_forbid] k) ↔ ((g + h) ≤ᵢ[F_forbid] k)
  := inducedForbidLE_rw_left (inducedForbidEq_add_right hfg)

/-! ## Condition-generic relation algebra + ordinary expansions (Option B)

These are condition-parametric (`forbidLEWith C` / `forbidEqWith C`) ports of the induced
move/rewrite lemmas above, plus the ordinary `H`-free expansions. The induced lemmas are
recovered as the `C := inducedForbiddenCondition _` instances; the ordinary examples use the
`C := forbiddenCondition H` instances. -/

theorem forbidLEWith_add_right {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidLEWith C f g) : forbidLEWith C (f + h) (g + h)
  := forbidLEWith_add hfg (forbidLEWith_refl C h)

theorem forbidLEWith_add_left {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidLEWith C f g) : forbidLEWith C (h + f) (h + g)
  := forbidLEWith_add (forbidLEWith_refl C h) hfg

theorem forbidEqWith_add_right {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidEqWith C f g) : forbidEqWith C (f + h) (g + h)
  := forbidEqWith_add hfg (forbidEqWith_refl C h)

theorem forbidLEWith_move_add_left_iff {C : ForbidCondition} {a b c : FlagAlgebra σ}
    : (forbidLEWith C (a + b) c) ↔ (forbidLEWith C b (c - a)) := by
  constructor
  · intro habc
    have h1 := forbidLEWith_add_right (h := -a) habc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  · intro hbc
    have h1 := forbidLEWith_add_left (h := a) hbc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1

theorem forbidLEWith_move_term_left_iff {C : ForbidCondition} {a c : FlagAlgebra σ}
    : (forbidLEWith C a c) ↔ (forbidLEWith C (0 : FlagAlgebra σ) (c - a)) := by
  simpa using
    (forbidLEWith_move_add_left_iff (C := C) (a := a) (b := (0 : FlagAlgebra σ)) (c := c))

theorem forbidEqWith_move_term_left_iff {C : ForbidCondition} {a c : FlagAlgebra σ}
    : (forbidEqWith C a c) ↔ (forbidEqWith C (0 : FlagAlgebra σ) (c - a)) := by
  constructor
  · intro h
    have h1 := forbidEqWith_add_right (h := -a) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  · intro h
    have h1 := forbidEqWith_add_right (h := a) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1

theorem forbidEqWith_move_term_left {C : ForbidCondition} {a c : FlagAlgebra σ}
    (hac : forbidEqWith C a c) : forbidEqWith C (0 : FlagAlgebra σ) (c - a)
  := forbidEqWith_move_term_left_iff.1 hac

theorem forbidLEWith_rw_left {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidEqWith C f g)
    : (forbidLEWith C f h) ↔ (forbidLEWith C g h) := by
  constructor
  · intro hfh
    exact forbidLEWith_trans (forbidLEWith_of_forbidEqWith (forbidEqWith_symm hfg)) hfh
  · intro hgh
    exact forbidLEWith_trans (forbidLEWith_of_forbidEqWith hfg) hgh

theorem forbidLEWith_rw_left_add_right {C : ForbidCondition} {f g h k : FlagAlgebra σ}
    (hfg : forbidEqWith C f g)
    : (forbidLEWith C (f + h) k) ↔ (forbidLEWith C (g + h) k)
  := forbidLEWith_rw_left (forbidEqWith_add_right hfg)

theorem forbidLEWith_trans_forbidEqWith_right {C : ForbidCondition} {f g h : FlagAlgebra σ}
    (hfg : forbidLEWith C f g) (hgh : forbidEqWith C g h) : forbidLEWith C f h
  := forbidLEWith_trans hfg (forbidLEWith_of_forbidEqWith hgh)

/-- Downward monotonicity for equalities (port of `downward_inducedForbidEq_zero`). -/
theorem downward_forbidEqWith_zero {C : ForbidCondition} {f : FlagAlgebra σ}
    (hf : forbidEqWith C f 0) : forbidEqWith C ⟦f⟧₀ 0 := by
  refine forbidLEWith_antisymm ?_ ?_
  · have hf' : forbidEqWith C (-1 • f) 0 := by
      refine forbidEqWith_move_term_left_iff.mpr ?_
      simp only [Int.reduceNeg, neg_smul, one_smul, sub_neg_eq_add, zero_add]
      exact forbidEqWith_symm hf
    simp only [Int.reduceNeg, neg_smul, one_smul] at hf'
    rw [forbidLEWith_move_term_left_iff]
    simp only [zero_sub, ← downward_neg]
    exact downward_forbidLEWith_nonneg (forbidLEWith_of_forbidEqWith (forbidEqWith_symm hf'))
  · exact downward_forbidLEWith_nonneg (forbidLEWith_of_forbidEqWith (forbidEqWith_symm hf))

/-- Downward monotonicity for equalities (port of `downward_inducedForbidEq_equal_flags`). -/
theorem downward_forbidEqWith_equal_flags {C : ForbidCondition} {a b : FlagAlgebra σ}
    (hab : forbidEqWith C a b)
    : forbidEqWith C ⟦a⟧₀ ⟦b⟧₀ := by
  refine forbidEqWith_move_term_left_iff.mpr ?_
  rw [← downward_sub]
  exact forbidEqWith_symm (downward_forbidEqWith_zero ((forbidEqWith_symm (forbidEqWith_move_term_left hab))))

/-- **Ordinary basis-vector expansion.** Modulo the ordinary `H`-free condition, `⟦basisVector F⟧`
expands over the `Fforbid`-free flags. The kill predicate is the SAME decidable single-flag density
check used by the induced version; the vanishing of killed flags under `forbiddenCondition H` is
discharged from `Fforbid ∈ forbiddenFlags H` (`hmem`), so no family-existential decidability is
needed. The examples instantiate `Fforbid := ⟨_, toFlag ⟦K_r⟧⟩`, `H := completeGraph (Fin r)`. -/
theorem basisVector_quot_forbidEq_sum_ofMem
    {N : ℕ} {H : SimpleGraph (Fin N)} (Fforbid : FinFlag ∅ₜ)
    (hmem : Fforbid ∈ forbiddenFlags H) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦basisVector F⟧ =[H]
      ∑ F' : FlagWithSize σ ℓ with flagDensity₁ Fforbid.2 (unlabel F') = 0,
        (flagDensity₁ F.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧ := by
  have hfilter :
      Finset.univ.filter (fun F' : FlagWithSize σ ℓ => flagDensity₁ Fforbid.2 (unlabel F') = 0)
        = Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ Fforbid.2 (unlabel F'))) :=
    Finset.filter_congr (fun x _ => by
      constructor
      · intro hx; rw [hx]; exact lt_irrefl 0
      · intro hx; exact le_antisymm (le_of_not_gt hx) (flagListDensity₁_ge_zero Fforbid.2 (unlabel x)))
  rw [show (∑ F' : FlagWithSize σ ℓ with flagDensity₁ Fforbid.2 (unlabel F') = 0,
        (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      = Finset.sum (Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ Fforbid.2 (unlabel F'))))
          (fun F' => (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      from by rw [hfilter]]
  exact basisVector_quot_forbidEqWith_sum_of_kill (forbiddenCondition H) F ℓ hℓ
      (fun x => 0 < flagDensity₁ Fforbid.2 (unlabel x))
      (fun x hx => basisVector_familyForbidEq_zero (forbiddenFlags H) Fforbid hmem ⟨ℓ, x⟩ hx)

/-- **Ordinary product expansion** (multiplication analogue of `basisVector_quot_forbidEq_sum_ofMem`). -/
theorem basisVector_quot_mul_forbidEq_sum_ofMem
    {N : ℕ} {H : SimpleGraph (Fin N)} (Fforbid : FinFlag ∅ₜ)
    (hmem : Fforbid ∈ forbiddenFlags H) (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    : (⟦basisVector F₁⟧ * ⟦basisVector F₂⟧ : FlagAlgebra σ) =[H]
      ∑ F' : FlagWithSize σ ℓ with flagDensity₁ Fforbid.2 (unlabel F') = 0,
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧ := by
  have hfilter :
      Finset.univ.filter (fun F' : FlagWithSize σ ℓ => flagDensity₁ Fforbid.2 (unlabel F') = 0)
        = Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ Fforbid.2 (unlabel F'))) :=
    Finset.filter_congr (fun x _ => by
      constructor
      · intro hx; rw [hx]; exact lt_irrefl 0
      · intro hx; exact le_antisymm (le_of_not_gt hx) (flagListDensity₁_ge_zero Fforbid.2 (unlabel x)))
  rw [show (∑ F' : FlagWithSize σ ℓ with flagDensity₁ Fforbid.2 (unlabel F') = 0,
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      = Finset.sum (Finset.univ.filter (fun F' => ¬ (0 < flagDensity₁ Fforbid.2 (unlabel F'))))
          (fun F' => (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
      from by rw [hfilter]]
  exact basisVector_quot_mul_forbidEqWith_sum_of_kill (forbiddenCondition H) F₁ F₂ ℓ hℓ
      (fun x => 0 < flagDensity₁ Fforbid.2 (unlabel x))
      (fun x hx => basisVector_familyForbidEq_zero (forbiddenFlags H) Fforbid hmem ⟨ℓ, x⟩ hx)



end Forbid
