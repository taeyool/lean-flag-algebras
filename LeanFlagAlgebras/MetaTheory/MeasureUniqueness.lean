import LeanFlagAlgebras.MetaTheory.EvalAlgebra
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! # Uniqueness of a measure on `X_σ` from its flag-integrals

A probability measure on the homomorphism space `X_σ = PositiveHomSpace σ` is completely
determined by the integrals `∫ χ, (χ f)` of the flag evaluations.  This is the measure-theoretic
counterpart of the Stone–Weierstrass density established in `EvalAlgebra.lean`: the flag
evaluations are sup-norm dense in `C(X_σ, ℝ)`, and the integral against a finite Borel measure is
a continuous (in fact Lipschitz) linear functional, so agreement on a dense subalgebra forces
agreement on all of `C(X_σ, ℝ)`, hence on all bounded continuous functions, hence equality of the
measures.

The headline result is `measure_eq_of_integral_flag_eq`.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## The integral as a continuous functional -/

/-- Integration against a finite Borel measure is a Lipschitz (hence continuous) functional on
the bounded continuous functions `X_σ →ᵇ ℝ`. -/
lemma continuous_integral_boundedContinuous (μ : Measure (PositiveHomSpace σ))
    [IsFiniteMeasure μ] :
    Continuous (fun f : PositiveHomSpace σ →ᵇ ℝ => ∫ x, f x ∂μ) := by
  apply LipschitzWith.continuous (K := (μ.real Set.univ).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq,
    ← integral_sub (BoundedContinuousFunction.integrable μ f)
      (BoundedContinuousFunction.integrable μ g)]
  calc |∫ x, (f x - g x) ∂μ|
      = ‖∫ x, (f - g : PositiveHomSpace σ →ᵇ ℝ) x ∂μ‖ := by
        rw [Real.norm_eq_abs]; simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
    _ ≤ μ.real Set.univ * ‖(f - g : PositiveHomSpace σ →ᵇ ℝ)‖ :=
        BoundedContinuousFunction.norm_integral_le_mul_norm μ _
    _ = μ.real Set.univ * dist f g := by rw [dist_eq_norm]

/-- Integration against a finite Borel measure, viewed as a functional on `C(X_σ, ℝ)` (via the
isometric identification with bounded continuous functions on the compact space `X_σ`), is
continuous. -/
lemma continuous_integral_continuousMap (μ : Measure (PositiveHomSpace σ))
    [IsFiniteMeasure μ] :
    Continuous (fun g : C(PositiveHomSpace σ, ℝ) => ∫ x, g x ∂μ) := by
  have hmk : Continuous (BoundedContinuousFunction.mkOfCompact :
      C(PositiveHomSpace σ, ℝ) → (PositiveHomSpace σ →ᵇ ℝ)) :=
    (ContinuousMap.isometryEquivBoundedOfCompact (PositiveHomSpace σ) ℝ).isometry.continuous
  exact (continuous_integral_boundedContinuous μ).comp hmk

/-! ## Uniqueness from flag-integrals -/

/-- A probability measure on `X_σ = PositiveHomSpace σ` is determined by the integrals of the
flag evaluations `χ ↦ χ f`. -/
theorem measure_eq_of_integral_flag_eq (P Q : ProbabilityMeasure (PositiveHomSpace σ))
    (h : ∀ f : FlagAlgebra σ,
      ∫ χ, (PositiveHomSpace.toPosHom χ) f ∂(P : Measure (PositiveHomSpace σ))
        = ∫ χ, (PositiveHomSpace.toPosHom χ) f ∂(Q : Measure (PositiveHomSpace σ))) :
    P = Q := by
  -- Linear functionals "integrate against `P` / `Q`" on `C(X_σ, ℝ)`.
  set LP : C(PositiveHomSpace σ, ℝ) → ℝ :=
    fun g => ∫ x, g x ∂(P : Measure (PositiveHomSpace σ)) with hLP
  set LQ : C(PositiveHomSpace σ, ℝ) → ℝ :=
    fun g => ∫ x, g x ∂(Q : Measure (PositiveHomSpace σ)) with hLQ
  -- They are continuous.
  have hLPc : Continuous LP := continuous_integral_continuousMap _
  have hLQc : Continuous LQ := continuous_integral_continuousMap _
  -- They agree on the (dense) flag-evaluation subalgebra.
  have hEqOn : Set.EqOn LP LQ (evalSubalgebra σ : Set C(PositiveHomSpace σ, ℝ)) := by
    intro g hg
    rw [evalSubalgebra, AlgHom.coe_range, Set.mem_range] at hg
    obtain ⟨f, rfl⟩ := hg
    simp only [hLP, hLQ, evalAlgHom_apply]
    exact h f
  -- The flag-evaluation subalgebra is dense in `C(X_σ, ℝ)`.
  have hDense : Dense (evalSubalgebra σ : Set C(PositiveHomSpace σ, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, evalSubalgebra_dense]
    rfl
  -- Hence `LP = LQ` everywhere.
  have hLPeqLQ : LP = LQ := hLPc.ext_on hDense hLQc hEqOn
  -- In particular the integrals of all bounded continuous functions agree.
  have hbcf : ∀ f : PositiveHomSpace σ →ᵇ ℝ,
      ∫ x, f x ∂(P : Measure (PositiveHomSpace σ))
        = ∫ x, f x ∂(Q : Measure (PositiveHomSpace σ)) := by
    intro f
    have := congrFun hLPeqLQ f.toContinuousMap
    simpa [hLP, hLQ] using this
  -- Conclude equality of the measures, then of the probability measures.
  have hPQ : (P : Measure (PositiveHomSpace σ)) = (Q : Measure (PositiveHomSpace σ)) :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure hbcf
  exact ProbabilityMeasure.toMeasure_injective hPQ

end FlagAlgebras.MetaTheory
