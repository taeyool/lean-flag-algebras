import «LeanFlagAlgebras».FlagSequence

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open MeasureTheory

def flagType_asEmptyType (σ : FlagType (Fin n₀)) : FlagAlgebra ∅ₜ
  := by
  sorry

notation "⟨" σ "⟩₀" => (flagType_asEmptyType σ)

theorem exists_prob_measure_extend_emptyType_positiveHom
    (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ∃ (ℙ : Measure (PositiveHomSpace σ)), IsProbabilityMeasure ℙ ∧
      ∀ (f : FlagAlgebra σ), ∫ φ, (PositiveHomSpace.toPosHom φ) f ∂ℙ = (φ₀ ⟦f⟧₀) / (φ₀ ⟨σ⟩₀)
  := by
  sorry
