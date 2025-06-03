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

theorem map_smul (φ : positiveHom σ) (r : ℝ) (f : FlagAlgebra σ) : φ (r • f) = r * φ f
  := by
  calc
    _ = φ.val (r • f) := rfl
    _ = r * φ.val f := by simp only [_root_.map_smul, smul_eq_mul]
    _ = r * φ f := rfl

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

theorem flag_sub_nonneg
    (f g : FlagAlgebra σ)
    : f ≤ g ↔ 0 ≤ g - f
  := by
  simp only [le_def, sub_zero]

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

theorem flag_geq_zero
    (F : FinFlag σ)
    : (⟦unitVector F⟧ : FlagAlgebra σ) ≥ 0
  := by
  simp [semanticCone]
  intro φ
  exact φ.2 F

theorem flag_add_le_add
    {f f' g g' : FlagAlgebra σ} (hf : f ≤ f') (hg : g ≤ g')
    : f + g ≤ f' + g'
  := by
  simp [le_def] at *
  intro φ
  have : f' + g' - (f + g) = (f' - f) + (g' - g) := by ring
  rw [this]
  rw [PositiveHom.map_add φ]
  exact add_nonneg (hf φ) (hg φ)

theorem nonneg_smul_nonneg_geq_zero
    {r : ℝ} {f : FlagAlgebra σ} (hr : r ≥ 0) (hf : f ≥ 0)
    : r • f ≥ 0
  := by
  simp [semanticCone]
  intro φ
  rw [PositiveHom.map_smul]
  have hφf : 0 ≤ φ f := by
    rw [ge_iff_le, le_def, sub_zero] at hf
    exact hf φ
  exact Left.mul_nonneg hr hφf

theorem square_downward_geq_zero
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  :=
  sorry
