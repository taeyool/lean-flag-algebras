import «LeanFlagAlgebras».SubflagDensity
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span

open FlagAlgebras
open Finset

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

abbrev FlagWithSize (σ : FlagType T) (n : ℕ) : Type
  := Flag σ (Fin n)

instance flagWithSize_inhabited (n : ℕ) (hn : n ≥ n₀) : Inhabited (FlagWithSize σ n) where
  default := sorry

instance : Unique (FlagWithSize σ n₀) where
  default := (flagWithSize_inhabited n₀ (by simp)).default
  uniq := sorry

noncomputable instance (n : ℕ) : Fintype (FlagWithSize σ n)
  := FlagFintype σ (Fin n)

def FinFlag (σ : FlagType (Fin n₀)) : Type
  := Σ (n : ℕ), FlagWithSize σ n

instance : One (FinFlag σ) where
  one := ⟨n₀, (default : FlagWithSize σ n₀)⟩

abbrev FlagVector (σ : FlagType (Fin n₀)) : Type
  := FinFlag σ →₀ ℝ

noncomputable instance : AddCommMonoid (FlagVector σ)
  := Finsupp.instAddCommMonoid

noncomputable instance : AddCommGroup (FlagVector σ)
  := Finsupp.instAddCommGroup

noncomputable instance : Module ℝ (FlagVector σ)
  := Finsupp.module (FinFlag σ) ℝ

noncomputable def unitVector (F : FinFlag σ) : FlagVector σ
  := Finsupp.single F 1

noncomputable instance : One (FlagVector σ) where
  one := unitVector 1

@[simp]
theorem rat_smul_eq_real_smul
    (a : ℚ) (f : FlagVector σ) : a • f = (a : ℝ) • f
  := rfl

noncomputable def densityFlagSum
    (F : FinFlag σ) (ℓ : ℕ) : FlagVector σ
  :=
  let ℓ_flags : Finset (FlagWithSize σ ℓ) := univ
  ∑ F' in ℓ_flags, (flagDensity₁ F.2 F') • unitVector ⟨ℓ, F'⟩

noncomputable def zeroElement
    (F : FinFlag σ) (ℓ : ℕ) : FlagVector σ
  := unitVector F - densityFlagSum F ℓ

noncomputable def zeroSet : Set (FlagVector σ)
  :=
  {k | ∃ (F : FinFlag σ) (ℓ : ℕ), F.1 ≤ ℓ ∧ k = zeroElement F ℓ}

@[simp]
theorem mem_zeroSpanSet
    {k : FlagVector σ} : k ∈ zeroSet ↔ ∃ F ℓ, F.1 ≤ ℓ ∧ k = zeroElement F ℓ
  := Iff.rfl

noncomputable def ZeroSpace : Submodule ℝ (FlagVector σ)
  :=
  Submodule.span ℝ zeroSet

def flagVectorEqv (f g : FlagVector σ) : Prop
  :=
  f - g ∈ ZeroSpace

infixl:50 " ∼v " => flagVectorEqv

theorem flagVectorEqv.refl (f : FlagVector σ)
    : f ∼v f
  :=
  sorry

theorem flagVectorEqv.symm
    : ∀ {f f' : FlagVector σ}, f ∼v f' → f' ∼v f
  :=
  sorry

theorem flagVectorEqv.trans
    : ∀ {f f' f'' : FlagVector σ}, f ∼v f' → f' ∼v f'' → f ∼v f''
  :=
  sorry

instance flagVectorSetoid (σ : FlagType (Fin n₀))
    : Setoid (FlagVector σ) where
  r     := flagVectorEqv
  iseqv := {
    refl := flagVectorEqv.refl,
    symm := flagVectorEqv.symm,
    trans := flagVectorEqv.trans
  }

abbrev FlagAlgebra : Type :=
  Quotient (flagVectorSetoid σ)
