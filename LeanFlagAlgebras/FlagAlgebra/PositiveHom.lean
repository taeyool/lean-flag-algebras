import «LeanFlagAlgebras».FlagAlgebra.FlagOperators
import «LeanFlagAlgebras».FlagAlgebra.SubflagListDensityProp
import Mathlib.Algebra.Algebra.Hom

namespace FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

abbrev Hom (σ : FlagType (Fin n₀))
  :=
  FlagAlgebra σ →ₐ[ℝ] ℝ

def PositiveHom (σ : FlagType (Fin n₀)) : Type
  :=
  { φ : Hom σ // ∀ (F : FinFlag σ), φ ⟦unitVector F⟧ ≥ 0 }

instance : FunLike (PositiveHom σ) (FlagAlgebra σ) ℝ where
  coe := fun φ => φ.val
  coe_injective' f g h := by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp at h
    congr

@[ext]
theorem ext {φ₁ φ₂ : PositiveHom σ} (h : ∀ f : FlagAlgebra σ, φ₁ f = φ₂ f) : φ₁ = φ₂
  := by
  apply Subtype.ext
  exact AlgHom.ext h

namespace PositiveHom

@[simp]
theorem map_zero (φ : PositiveHom σ) : φ 0 = 0
  :=
  RingHom.map_zero (φ.val : FlagAlgebra σ →+* ℝ)

@[simp]
theorem map_one (φ : PositiveHom σ) : φ 1 = 1
  :=
  RingHom.map_one (φ.val : FlagAlgebra σ →+* ℝ)

theorem map_add (φ : PositiveHom σ) (f g : FlagAlgebra σ) : φ (f + g) = φ f + φ g
  :=
  RingHom.map_add (φ.val : FlagAlgebra σ →+* ℝ) f g

theorem map_sub (φ : PositiveHom σ) (f g : FlagAlgebra σ) : φ (f - g) = φ f - φ g
  :=
  RingHom.map_sub (φ.val : FlagAlgebra σ →+* ℝ) f g

theorem map_smul (φ : PositiveHom σ) (r : ℝ) (f : FlagAlgebra σ) : φ (r • f) = r * φ f
  := by
  calc
    _ = φ.val (r • f) := rfl
    _ = r * φ.val f := by simp only [_root_.map_smul, smul_eq_mul]
    _ = r * φ f := rfl

theorem map_mul (φ : PositiveHom σ) (f g : FlagAlgebra σ) : φ (f * g) = φ f * φ g
  :=
  RingHom.map_mul (φ.val : FlagAlgebra σ →+* ℝ) f g

theorem map_sum (φ : PositiveHom σ) {ι : Type} (s : Finset ι) (f : ι → FlagAlgebra σ)
    : φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i)
  :=
  _root_.map_sum (φ.val : FlagAlgebra σ →+* ℝ) f s

end PositiveHom

theorem positiveHom_unitVector_ge_zero
    (φ : PositiveHom σ) (F : FinFlag σ)
    : 0 ≤ φ ⟦unitVector F⟧
  :=
  φ.2 F

theorem sum_positiveHom_unitVector_flagWithSize_eq_one
    (φ : PositiveHom σ) (ℓ : ℕ) (hℓ : ℓ ≥ n₀)
    : ∑ F : FlagWithSize σ ℓ, φ ⟦unitVector ⟨ℓ, F⟩⟧ = 1
  := by
  rw [← PositiveHom.map_sum, sum_flagWithSize_eq_one ℓ hℓ, PositiveHom.map_one]

theorem positiveHom_unitVector_le_one
    (φ : PositiveHom σ) (F : FinFlag σ)
    : φ ⟦unitVector F⟧ ≤ 1
  := by
  classical
  let ℓ := F.1
  have hℓ : ℓ ≥ n₀ := finFlag_size_ge_n₀ F
  rw [← sum_positiveHom_unitVector_flagWithSize_eq_one φ ℓ hℓ]
  rw [← @Finset.add_sum_erase _ _ _ _ _ _ F.2 (by simp)]
  have : F = ⟨ℓ, F.2⟩ := rfl
  rw [← this, le_add_iff_nonneg_right]
  apply Finset.sum_nonneg
  intro G _
  exact positiveHom_unitVector_ge_zero φ ⟨ℓ, G⟩

theorem positiveHom_unitVector_eq_zero
    (φ : PositiveHom σ) {ℓ ℓ' : ℕ} {F : FlagWithSize σ ℓ} {G : FlagWithSize σ ℓ'}
    (h : flagDensity₁ F G > 0) (hF : φ ⟦unitVector ⟨ℓ, F⟩⟧ = 0)
    : φ ⟦unitVector ⟨ℓ', G⟩⟧ = 0
  := by
  have hℓ : ℓ ≤ ℓ' := by
    have := flagDensity_le_card h
    simp_all only [gt_iff_lt, Fintype.card_fin]
  rw [unitVector_quot_eq_sum_density_mul_flagWithSize ⟨ℓ, F⟩ ℓ' hℓ] at hF
  simp_rw [PositiveHom.map_sum, PositiveHom.map_smul] at hF
  rw [Finset.sum_eq_zero_iff_of_nonneg] at hF
  · specialize hF G (Finset.mem_univ G)
    simp only [Rat.cast_eq_zero, mul_eq_zero] at hF
    rcases hF with hG | hG
    · simp_all only [lt_self_iff_false]
    · exact hG
  · intro G' hG'
    apply Left.mul_nonneg
    · simp only [Rat.cast_nonneg]
      apply flagListDensity_ge_zero
    · exact positiveHom_unitVector_ge_zero φ ⟨ℓ', G'⟩

def semanticCone (σ : FlagType (Fin n₀)) : Set (FlagAlgebra σ) :=
  { f : FlagAlgebra σ | ∀ (φ : PositiveHom σ), φ f ≥ 0 }

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
  le_refl f := by simp [semanticCone]
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

end FlagAlgebras
