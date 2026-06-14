import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Order.OrderClosed

/-! # Almost-sure non-negativity and support

This is the Lean counterpart of `lem:support-as` from `MetaTheory/paper.tex` (§2):

> Let `P` be a Borel probability measure on a compact metrizable space `X`, and let
> `h : X → ℝ` be continuous.  Then `P[h(x) ≥ 0] = 1` if and only if `h(x) ≥ 0` for every
> `x ∈ supp(P)`.

We use Mathlib's topological support of a measure (`MeasureTheory.Measure.support`).  The
statement is proved for any probability measure on a space in which the support is conull,
i.e. a hereditarily Lindelöf space (compact metrizable spaces qualify, via
`SecondCountableTopology.toHereditarilyLindelof`).  In applications `X` is the
homomorphism space `PositiveHomSpace σ` and `h χ = χ f`.
-/

open MeasureTheory Set

open scoped ENNReal

namespace FlagAlgebras.MetaTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [HereditarilyLindelofSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- **Almost-sure non-negativity and support** (`lem:support-as`).  For a probability
measure `μ` on a (hereditarily Lindelöf) space and a continuous `h : X → ℝ`, the event
`h ≥ 0` has full measure iff `h` is non-negative on every point of the support of `μ`. -/
theorem ae_nonneg_iff_nonneg_on_support {h : X → ℝ} (hh : Continuous h) :
    μ {x | 0 ≤ h x} = 1 ↔ ∀ x ∈ μ.support, 0 ≤ h x := by
  have hmeas : MeasurableSet {x | 0 ≤ h x} :=
    (isClosed_le continuous_const hh).measurableSet
  constructor
  · -- (⇒) full measure forces non-negativity on the support
    intro hP x hx
    by_contra hneg
    push_neg at hneg
    have hopen : IsOpen {y | h y < 0} := isOpen_lt hh continuous_const
    have hpos : 0 < μ {y | h y < 0} :=
      (Measure.mem_support_iff_forall (μ := μ) x).mp hx _ (hopen.mem_nhds hneg)
    have hzero : μ {y | h y < 0} = 0 := by
      have hco : {y : X | h y < 0} = {x | 0 ≤ h x}ᶜ := by
        ext y; simp [not_le]
      rw [hco, prob_compl_eq_one_sub hmeas, hP, tsub_self]
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · -- (⇐) non-negativity on the (conull) support gives full measure
    intro H
    have hsub : μ.support ⊆ {x | 0 ≤ h x} := fun x hx => H x hx
    have hsupp1 : μ μ.support = 1 := by
      have hadd := measure_add_measure_compl (μ := μ)
        (Measure.isClosed_support (μ := μ)).measurableSet
      rw [Measure.measure_compl_support, add_zero, measure_univ] at hadd
      exact hadd
    refine le_antisymm ?_ ?_
    · calc μ {x | 0 ≤ h x} ≤ μ univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    · calc (1 : ℝ≥0∞) = μ μ.support := hsupp1.symm
        _ ≤ μ {x | 0 ≤ h x} := measure_mono hsub

end FlagAlgebras.MetaTheory
