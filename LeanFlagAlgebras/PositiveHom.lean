import «LeanFlagAlgebras».FlagOperators

open FlagAlgebras

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

namespace PosHom

theorem map_zero (φ : PositiveHom σ) : φ 0 = 0
  :=
  RingHom.map_zero (φ.val : FlagAlgebra σ →+* ℝ)

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

theorem map_sum (φ : PositiveHom σ) {ι : Type*} (s : Finset ι) (f : ι → FlagAlgebra σ) :
  φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) :=
  _root_.map_sum (φ.val : FlagAlgebra σ →+* ℝ) f s

end PosHom

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
  le_refl f := by
    simp [semanticCone]
    intro φ
    rw [PosHom.map_zero φ]
  le_trans f g h := by
    intro hfg hgh
    simp [semanticCone] at *
    intro φ
    specialize hfg φ
    specialize hgh φ
    have : φ (h - f) = φ (h - g) + φ (g - f) := by
      repeat rw [PosHom.map_sub φ]
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
  rw [PosHom.map_add φ]
  exact add_nonneg (hf φ) (hg φ)

theorem nonneg_smul_nonneg_geq_zero
    {r : ℝ} {f : FlagAlgebra σ} (hr : r ≥ 0) (hf : f ≥ 0)
    : r • f ≥ 0
  := by
  simp [semanticCone]
  intro φ
  rw [PosHom.map_smul]
  have hφf : 0 ≤ φ f := by
    rw [ge_iff_le, le_def, sub_zero] at hf
    exact hf φ
  exact Left.mul_nonneg hr hφf

theorem square_downward_geq_zero
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  := by
  simp [semanticCone]
  intro φ
  obtain ⟨f', hf'⟩ := Quotient.exists_rep f
  rw [← hf']
  have tmp : ∃ (g : FlagVector σ), (⟦f'⟧ * ⟦f'⟧ : FlagAlgebra σ) = ⟦g * g⟧ := by
    sorry
  obtain ⟨g, hg⟩ := tmp
  rw [hg]
  dsimp [downward, downwardFlagVectorQuot, downwardFlagVector]
  have tmp1 : ⟦∑ G ∈ (g * g).support, ((g * g) G) • downwardFlag G.snd⟧ = ∑ G ∈ (g * g).support, (⟦((g * g) G) • downwardFlag G.snd⟧ : FlagAlgebra ∅ₜ) := by

    sorry
  rw [tmp1, PosHom.map_sum φ]
  have tmp2 : ∀ G ∈ (g * g).support, φ ⟦((g * g) G) • downwardFlag G.snd⟧ ≥ 0 := by
    intro G hG
    have tmp3 : ⟦((g * g) G) • downwardFlag G.snd⟧ = (g * g) G • (⟦downwardFlag G.snd⟧ : FlagAlgebra ∅ₜ) := by sorry
    rw [tmp3]
    rw [PosHom.map_smul φ]
    have tmp4 : (g * g) G ≥ 0 := by
      rw [flagVector_mul_def]
      sorry
    have tmp5 : φ (⟦downwardFlag G.snd⟧ : FlagAlgebra ∅ₜ) ≥ 0 := by
      dsimp [downwardFlag]
      have h_smul : ⟦(downwardNormalizingFactor G.snd) • unitVector ⟨G.fst, unlabel G.snd⟩⟧ =
        (downwardNormalizingFactor G.snd : ℝ) • (⟦unitVector ⟨G.fst, unlabel G.snd⟩⟧ : FlagAlgebra ∅ₜ) := by
        sorry
      -- rw [PosHom.map_smul φ]

      have h_nonneg_factor : (downwardNormalizingFactor G.snd : ℝ) ≥ 0 := by
        sorry -- downward normalizing factor should be nonnegative
      have h_unit_nonneg : φ ⟦unitVector ⟨G.fst, unlabel G.snd⟩⟧ ≥ 0 := φ.2 ⟨G.fst, unlabel G.snd⟩
      -- exact Left.mul_nonneg h_nonneg_factor h_unit_nonneg
      sorry
    exact Left.mul_nonneg tmp4 tmp5
  exact Finset.sum_nonneg tmp2
