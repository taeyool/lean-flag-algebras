import «LeanFlagAlgebras».FlagAlgebra.FlagOperators
import «LeanFlagAlgebras».FlagAlgebra.SubflagListDensityProp
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Order.Monoid.Defs

/-! # Positive algebra homomorphisms and the semantic order

A `PositiveHom σ` is an `ℝ`-algebra homomorphism `FlagAlgebra σ → ℝ` that sends
every flag (unit vector) to a nonnegative number; these are the semantic
evaluations of the flag algebra (limits of graph densities). The set of
elements that every positive homomorphism sends to a nonnegative value is the
`semanticCone`, which induces the partial preorder `≤` on `FlagAlgebra σ` used
to state density bounds. This file collects the homomorphism algebra rules and
the basic monotonicity/positivity facts for that order.
-/

namespace FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- An `ℝ`-algebra homomorphism from the flag algebra to the reals. -/
abbrev Hom (σ : FlagType (Fin n₀))
  :=
  FlagAlgebra σ →ₐ[ℝ] ℝ

/-- A *positive* homomorphism: an algebra map `FlagAlgebra σ → ℝ` that is
nonnegative on every flag. These are exactly the semantic evaluations
(limits of subgraph densities) of the flag algebra. -/
def PositiveHom (σ : FlagType (Fin n₀)) : Type
  :=
  { φ : Hom σ // ∀ (F : FinFlag σ), φ ⟦basisVector F⟧ ≥ 0 }

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

/-! ## Algebra-homomorphism rules for positive homomorphisms -/

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

/-- A positive homomorphism is nonnegative on every flag (the defining
property, restated as `0 ≤ …`). -/
theorem positiveHom_basisVector_ge_zero
    (φ : PositiveHom σ) (F : FinFlag σ)
    : 0 ≤ φ ⟦basisVector F⟧
  :=
  φ.2 F

/-- The φ-values of all flags of a fixed size `ℓ ≥ n₀` sum to `1`
(a probability-distribution normalization). -/
theorem sum_positiveHom_basisVector_flagWithSize_eq_one
    (φ : PositiveHom σ) (ℓ : ℕ) (hℓ : ℓ ≥ n₀)
    : ∑ F : FlagWithSize σ ℓ, φ ⟦basisVector ⟨ℓ, F⟩⟧ = 1
  := by
  rw [← PositiveHom.map_sum, sum_flagWithSize_eq_one ℓ hℓ, PositiveHom.map_one]

/-- A positive homomorphism maps every flag into `[0, 1]`: the upper bound,
since each flag is one summand of a sum-to-one of nonnegatives. -/
theorem positiveHom_basisVector_le_one
    (φ : PositiveHom σ) (F : FinFlag σ)
    : φ ⟦basisVector F⟧ ≤ 1
  := by
  classical
  let ℓ := F.1
  have hℓ : ℓ ≥ n₀ := finFlag_size_ge_n₀ F
  rw [← sum_positiveHom_basisVector_flagWithSize_eq_one φ ℓ hℓ]
  rw [← @Finset.add_sum_erase _ _ _ _ _ _ F.2 (by simp)]
  have : F = ⟨ℓ, F.2⟩ := rfl
  rw [← this, le_add_iff_nonneg_right]
  apply Finset.sum_nonneg
  intro G _
  exact positiveHom_basisVector_ge_zero φ ⟨ℓ, G⟩

/-- Vanishing propagates along positive density: if `φ` kills a flag `F` and a
larger flag `G` contains `F` with positive density, then `φ` kills `G` too. -/
theorem positiveHom_basisVector_eq_zero
    (φ : PositiveHom σ) {ℓ ℓ' : ℕ} {F : FlagWithSize σ ℓ} {G : FlagWithSize σ ℓ'}
    (h : flagDensity₁ F G > 0) (hF : φ ⟦basisVector ⟨ℓ, F⟩⟧ = 0)
    : φ ⟦basisVector ⟨ℓ', G⟩⟧ = 0
  := by
  have hℓ : ℓ ≤ ℓ' := by
    have := flagDensity_le_card h
    simp_all only [gt_iff_lt, Fintype.card_fin]
  rw [basisVector_quot_eq_sum ⟨ℓ, F⟩ ℓ' hℓ] at hF
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
    · exact positiveHom_basisVector_ge_zero φ ⟨ℓ', G'⟩

/-! ## The semantic cone and the induced order on the flag algebra -/

/-- The semantic cone: flag-algebra elements that *every* positive homomorphism
sends to a nonnegative value. Membership `0 ≤ f` is exactly an unconditional
density inequality, so this cone is what density bounds are proved in. -/
def semanticCone (σ : FlagType (Fin n₀)) : Set (FlagAlgebra σ) :=
  { f : FlagAlgebra σ | ∀ (φ : PositiveHom σ), φ f ≥ 0 }

instance : LE (FlagAlgebra σ) where
  le := fun f g => g - f ∈ semanticCone σ

/-- Unfolds the semantic order: `f ≤ g` means `g - f` lies in the semantic
cone, i.e. every positive homomorphism agrees `φ f ≤ φ g`. -/
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

/-- Every flag is nonnegative in the semantic order. -/
theorem flag_geq_zero
    (F : FinFlag σ)
    : (⟦basisVector F⟧ : FlagAlgebra σ) ≥ 0
  := by
  simp [semanticCone]
  intro φ
  exact φ.2 F

/-- The semantic order is compatible with addition (add inequalities). -/
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

theorem flag_add_le_add_left
    {f g : FlagAlgebra σ} (h : f ≤ g) (a : FlagAlgebra σ)
    : a + f ≤ a + g
  :=
  flag_add_le_add (le_refl a) h

theorem flag_add_le_add_right
    {f g : FlagAlgebra σ} (h : f ≤ g) (a : FlagAlgebra σ)
    : f + a ≤ g + a
  := by
  simpa [add_comm] using flag_add_le_add h (le_refl a)

instance : AddLeftMono (FlagAlgebra σ) where
  elim := fun a _ _ h ↦ flag_add_le_add_left h a

instance : AddRightMono (FlagAlgebra σ) where
  elim := fun a _ _ h ↦ flag_add_le_add_right h a

/-- A nonnegative scalar times a nonnegative element is nonnegative. -/
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
