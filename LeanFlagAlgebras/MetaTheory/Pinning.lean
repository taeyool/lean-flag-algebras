import LeanFlagAlgebras.MetaTheory.SupportClosure

/-! # Pinning obstructions (paper §9)

This module starts the formalisation of paper §9, "Degenerate classes are not
root-plantable", with the abstract obstruction mechanism.

The paper's `thm:pinning` says: if a labelled quantity is almost surely pinned to a
constant under every admissible random extension, but the constrained quotient space
contains a point where that quantity has a different value, then the class is not
root-plantable at the chosen type.  The proof is purely topological:

1. almost-sure pinning plus closedness of an evaluation level set forces every support
   point of every admissible extension into that level set;
2. the closure defining `S_σ` stays inside the same level set;
3. any quotient point outside the level set witnesses `S_σ ≠ Q_σ`.
-/

open MeasureTheory

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- If the evaluation of `g` is almost surely equal to `c` under every admissible random
extension, then the whole root-planting set `S_σ` lies in the same level set. -/
theorem Sσ_subset_eval_eq_of_ae_pinned (T : Constraint σ) (g : FlagAlgebra σ) (c : ℝ)
    (hpin : ∀ (φ₀ : PositiveHom ∅ₜ), posHomPoint φ₀ ∈ Qσ T.forb0 →
      ∀ (hσ : φ₀ ⟨σ⟩₀ > 0),
        ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
          (PositiveHomSpace.toPosHom χ) g = c) :
    Sσ T ⊆ {χ : PositiveHomSpace σ | (PositiveHomSpace.toPosHom χ) g = c} := by
  refine closure_minimal ?_ (isClosed_eq (continuous_eval g) continuous_const)
  refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ =>
    Set.iUnion_subset fun hσ => ?_
  exact Measure.support_subset_of_isClosed
    (isClosed_eq (continuous_eval g) continuous_const) (hpin φ₀ hφ₀ hσ)

/-- Support-level pinning obstruction: if `S_σ` is contained in one evaluation level set
but `Q_σ` contains a point outside it, then the constraint is not root-plantable. -/
theorem support_pinning_obstruction (T : Constraint σ) (g : FlagAlgebra σ) (c : ℝ)
    (hS : Sσ T ⊆ {χ : PositiveHomSpace σ | (PositiveHomSpace.toPosHom χ) g = c})
    (hψ : ∃ ψ ∈ Qσ T.forbσ, (PositiveHomSpace.toPosHom ψ) g ≠ c) :
    ¬ RootPlantable T := by
  rintro hroot
  obtain ⟨ψ, hψQ, hψne⟩ := hψ
  have hψS : ψ ∈ Sσ T := by
    rw [hroot]
    exact hψQ
  exact hψne (hS hψS)

/-- **Pinning obstruction** (`thm:pinning`): if a flag-algebra element `g` is almost
surely pinned to a constant `c` across all admissible unlabelled limits, while some
quotient point evaluates `g` differently, then `S_σ ≠ Q_σ`.

The paper states this for a `σ`-flag `g` and `c ∈ [0,1]`; the proof only uses the
corresponding flag-algebra element and a real constant, so the Lean statement is slightly
more general. -/
theorem pinning_obstruction (T : Constraint σ) (g : FlagAlgebra σ) (c : ℝ)
    (hpin : ∀ (φ₀ : PositiveHom ∅ₜ), posHomPoint φ₀ ∈ Qσ T.forb0 →
      ∀ (hσ : φ₀ ⟨σ⟩₀ > 0),
        ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
          (PositiveHomSpace.toPosHom χ) g = c)
    (hψ : ∃ ψ ∈ Qσ T.forbσ, (PositiveHomSpace.toPosHom ψ) g ≠ c) :
    ¬ RootPlantable T :=
  support_pinning_obstruction T g c (Sσ_subset_eval_eq_of_ae_pinned T g c hpin) hψ

end FlagAlgebras.MetaTheory
