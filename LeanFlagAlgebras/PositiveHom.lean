import «LeanFlagAlgebras».FlagAlgebra

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

abbrev Hom (σ : FlagType (Fin n₀))
  :=
  FlagAlgebra σ →ₐ[ℝ] ℝ

def positiveHom (σ : FlagType (Fin n₀)) : Type
  :=
  { φ : Hom σ // ∀ (F : FinFlag σ), φ ⟦unitVector F⟧ ≥ 0 }

instance : FunLike (positiveHom σ) (FlagAlgebra σ) ℝ where
  coe := fun φ => φ.val
  coe_injective' f g h := by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp at h
    congr

def semanticCone (σ : FlagType (Fin n₀)) : Set (FlagAlgebra σ) :=
  { f : FlagAlgebra σ | ∀ (φ : positiveHom σ), φ f ≥ 0 }

instance : LE (FlagAlgebra σ) where
  le := fun f g => g - f ∈ semanticCone σ

instance : Preorder (FlagAlgebra σ) where
  le_refl := by
    intro f
    show f - f ∈ semanticCone σ
    simp [semanticCone]
    intro φ
    sorry
  le_trans := sorry
