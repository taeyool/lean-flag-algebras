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

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def flagVectorDensity
    (f : FlagVector σ) (G : Flag σ V)
    : ℝ
  :=
  ∑ F in f.support, f F * flagDensity₁ F.2 G

theorem flagVectorDensity_respects_eqv
    (f f' : FlagVector σ) (hf : f ∼v f') (G : Flag σ V)
    : flagVectorDensity f G = flagVectorDensity f' G
  := by
  sorry

noncomputable def flagAlgebraDensity
    : FlagAlgebra σ → Flag σ V → ℝ
  := by
  apply Quot.lift flagVectorDensity
  intro f f' hf
  ext G
  exact flagVectorDensity_respects_eqv f f' hf G

theorem downward_unitVector_nonneg
    (φ : PositiveHom ∅ₜ) (F : FinFlag σ)
    : 0 ≤ φ (downward ⟦unitVector F⟧) := by
  dsimp [downward, downwardFlagVectorQuot, downwardFlagVector]
  simp_all only [unitVector_support, Finset.sum_singleton, unitVector_apply_self, one_smul]
  dsimp [downwardFlag]
  have tmp : ⟦((downwardNormalizingFactor F.snd : ℝ)) • unitVector ⟨F.fst, unlabel F.snd⟩⟧ = (downwardNormalizingFactor F.snd : ℝ) • (⟦unitVector ⟨F.fst, unlabel F.snd⟩⟧ : FlagAlgebra ∅ₜ) := rfl
  rw [tmp, PosHom.map_smul φ]
  apply mul_nonneg
  · let F' := F.snd
    obtain ⟨f', hf'⟩ := Quotient.exists_rep F'
    dsimp [F'] at hf'
    rw [← hf']
    dsimp [downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph]
    simp only [Rat.cast_div, Rat.cast_natCast]
    apply div_nonneg <;> simp_all only [Nat.cast_nonneg]
  · exact φ.2 ⟨F.fst, unlabel F.snd⟩

theorem downward_preserve_semanticCone
    (f : FlagAlgebra σ) (hf : f ∈ semanticCone σ)
    : ⟦f⟧₀ ∈ semanticCone ∅ₜ
  := by
  sorry

theorem square_downward_geq_zero
    (f : FlagAlgebra σ)
    : ⟦f * f⟧₀ ≥ 0
  := by
  simp only [ge_iff_le, le_def, sub_zero]
  apply downward_preserve_semanticCone
  intro φ
  rw [PosHom.map_mul]
  exact mul_self_nonneg (φ f)
