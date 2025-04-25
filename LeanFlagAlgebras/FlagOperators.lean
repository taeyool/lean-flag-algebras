import «LeanFlagAlgebras».FlagAlgebra

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/- Downward operator from σ-type to the empty type -/

def emptyType : FlagType (Fin 0) := emptyGraph (Fin 0)

notation "∅ₜ" => emptyType

def downwardNormalizingFactor (F : Flag σ (Fin n)) : ℚ :=
  sorry

def unlabel {V : Type} (F : Flag σ V) : Flag ∅ₜ V :=
  sorry

noncomputable def downward (F : Flag σ (Fin n)) : FlagVector ∅ₜ :=
  downwardNormalizingFactor F • unitVector ⟨n, unlabel F⟩
