import «LeanFlagAlgebras».FlagOperators

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

namespace PositiveHom

theorem map_zero (φ : positiveHom σ) : φ 0 = 0
  :=
  RingHom.map_zero (φ.val : FlagAlgebra σ →+* ℝ)

theorem map_one (φ : positiveHom σ) : φ 1 = 1
  :=
  RingHom.map_one (φ.val : FlagAlgebra σ →+* ℝ)

theorem map_add (φ : positiveHom σ) (f g : FlagAlgebra σ) : φ (f + g) = φ f + φ g
  :=
  RingHom.map_add (φ.val : FlagAlgebra σ →+* ℝ) f g

theorem map_sub (φ : positiveHom σ) (f g : FlagAlgebra σ) : φ (f - g) = φ f - φ g
  :=
  RingHom.map_sub (φ.val : FlagAlgebra σ →+* ℝ) f g

theorem map_mul (φ : positiveHom σ) (f g : FlagAlgebra σ) : φ (f * g) = φ f * φ g
  :=
  RingHom.map_mul (φ.val : FlagAlgebra σ →+* ℝ) f g

end PositiveHom

def semanticCone (σ : FlagType (Fin n₀)) : Set (FlagAlgebra σ) :=
  { f : FlagAlgebra σ | ∀ (φ : positiveHom σ), φ f ≥ 0 }

instance : LE (FlagAlgebra σ) where
  le := fun f g => g - f ∈ semanticCone σ

@[simp]
theorem le_def (f g : FlagAlgebra σ) : f ≤ g ↔ g - f ∈ semanticCone σ :=
  Iff.rfl

instance : Preorder (FlagAlgebra σ) where
  le_refl f := by
    simp [semanticCone]
    intro φ
    rw [PositiveHom.map_zero φ]
  le_trans f g h := by
    intro hfg hgh
    simp [semanticCone] at *
    intro φ
    specialize hfg φ
    specialize hgh φ
    have : φ (h - f) = φ (h - g) + φ (g - f) := by
      repeat rw [PositiveHom.map_sub φ]
      ring
    rw [this]
    exact add_nonneg hgh hfg

theorem square_downward_geq_zero
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  :=
  sorry
