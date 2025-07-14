import «LeanFlagAlgebras».FlagOperators
import Mathlib.Order.Filter.Basic

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

noncomputable def flagVectorDensity
    (f : FlagVector σ) (G : FinFlag σ)
    : ℝ
  :=
  linearExtension (fun F : FinFlag σ => flagDensity₁ F.2 G.2) f

theorem flagVectorDensity_zero
    (G : FinFlag σ)
    : flagVectorDensity 0 G = 0
  := by
  simp only [flagVectorDensity, linearExtension_zero]

theorem flagVectorDensity_add
    (f f' : FlagVector σ) (G : FinFlag σ)
    : flagVectorDensity (f + f') G = flagVectorDensity f G + flagVectorDensity f' G
  := by
  simp only [flagVectorDensity, linearExtension_add]

theorem flagVectorDensity_sum
    (s : Finset ι) (c : ι → FlagVector σ) (G : FinFlag σ)
    : flagVectorDensity (∑ i in s, c i) G = ∑ i in s, flagVectorDensity (c i) G
  := by
  simp only [flagVectorDensity, linearExtension_sum]

theorem flagVectorDensity_neg
    (f : FlagVector σ) (G : FinFlag σ)
    : flagVectorDensity (-f) G = -flagVectorDensity f G
  := by
  simp only [flagVectorDensity, linearExtension_neg]

theorem flagVectorDensity_sub
    (f f' : FlagVector σ) (G : FinFlag σ)
    : flagVectorDensity (f - f') G = flagVectorDensity f G - flagVectorDensity f' G
  := by
  simp only [flagVectorDensity, linearExtension_sub]

theorem flagVectorDensity_smul
    (f : FlagVector σ) (r : ℝ) (G : FinFlag σ)
    : flagVectorDensity (r • f) G = r • flagVectorDensity f G
  := by
  simp only [flagVectorDensity, linearExtension_smul]

theorem flagVectorDensity_zeroElement
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ) (G : FinFlag σ) (hG : ℓ ≤ G.1)
    : flagVectorDensity (zeroElement F ℓ) G = 0
  := by
  dsimp [zeroElement, densityFlagSum]
  simp_rw [flagVectorDensity_sub, sub_eq_zero, flagVectorDensity_sum, flagVectorDensity_smul]
  dsimp [flagVectorDensity, linearExtension]
  simp only [unitVector_support, Finset.sum_singleton, unitVector_apply_self, one_mul]
  rw [density_chain_rule₁₁ ℓ]
  · simp only [FlagWithSize, Rat.cast_sum, Rat.cast_mul]
  · sorry
  · exact hℓ
  · exact hG

theorem flagVectorDensity_zeroSpace
    (k : FlagVector σ) (hk_zero : k ∈ ZeroSpace σ) (G : FinFlag σ)
    : flagVectorDensity k G = 0
  := by
  rcases zeroSpace_eq_sum_spanElement k hk_zero with ⟨I, hI, c, v, hv, hk_sum⟩
  rw [hk_sum, flagVectorDensity_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [flagVectorDensity_smul]
  specialize hv i
  rw [mem_zeroSet] at hv
  rcases hv with ⟨F, ℓ, hℓ, hvi⟩
  rw [hvi, flagVectorDensity_zeroElement F ℓ hℓ G, smul_zero]
  sorry

theorem flagVectorDensity_respects_eqv
    (f f' : FlagVector σ) (hf : f ∼v f') (G : FinFlag σ)
    : flagVectorDensity f G = flagVectorDensity f' G
  := by
  rw [← sub_eq_zero, ← flagVectorDensity_sub]
  apply flagVectorDensity_zeroSpace (f - f') hf

noncomputable def flagAlgebraDensity
    : FlagAlgebra σ → FinFlag σ → ℝ
  := by
  apply Quot.lift flagVectorDensity
  intro f f' hf
  ext G
  exact flagVectorDensity_respects_eqv f f' hf G

def Increases (s : ℕ → FinFlag σ) : Prop
  :=
  ∀ n m, n ≤ m → (s n).1 ≤ (s m).1

def Converges (s : ℕ → FinFlag σ) : Prop
  :=
  sorry

theorem downward_unitVector_nonneg
    (φ : PositiveHom ∅ₜ) (F : FinFlag σ)
    : 0 ≤ φ (downward ⟦unitVector F⟧) := by
  dsimp [downward, downwardFlagVectorQuot, downwardFlagVector, linearExtension]
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
