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

noncomputable def flagMulWithSize
    (F F' : FinFlag σ) (ℓ : ℕ) : FlagVector σ
  :=
  let ℓ_flags : Finset (FlagWithSize σ ℓ) := univ
  ∑ G in ℓ_flags, (flagDensity₂ F.2 F'.2 G) • unitVector ⟨ℓ, G⟩

noncomputable def flagMul
    (F F' : FinFlag σ) : FlagVector σ
  :=
  flagMulWithSize F F' (F.1 + F'.1)

noncomputable instance : Mul (FlagVector σ) where
  mul f g := ∑ F in f.support, ∑ G in g.support, ((f F) * (g G)) • flagMul F G

theorem flagVector_mul_def
    (f g : FlagVector σ) : f * g = ∑ F in f.support, ∑ G in g.support, ((f F) * (g G)) • flagMul F G
  := rfl

theorem flagVector_mul_comm
    (f g : FlagVector σ) : f * g = g * f
  :=
  sorry

noncomputable instance : CommMagma (FlagVector σ) where
  mul_comm := flagVector_mul_comm

instance : IsScalarTower ℝ (FlagVector σ) (FlagVector σ) where
  smul_assoc r g h := by
    simp [flagVector_mul_def]
    by_cases hr : r = 0
    · simp [hr]
    · have hg_supp : (r • g).support = g.support := Finsupp.support_smul_eq hr
      rw [hg_supp]
      repeat (rw [smul_sum]; congr; apply funext; intro)
      simp [smul_mul_assoc, mul_assoc, smul_smul]

theorem flagVector_neg_mul
    (f g : FlagVector σ) : -f * g = -(f * g)
  :=
  sorry

noncomputable instance : HasDistribNeg (FlagVector σ) where
  neg_mul := flagVector_neg_mul
  mul_neg g h := by
    rw [mul_comm g (-h), mul_comm g h, flagVector_neg_mul h g]

theorem flagVector_left_distrib
    (f g h : FlagVector σ) : f * (g + h) = f * g + f * h
  :=
  sorry

theorem flagVector_right_distrib
    (f g h : FlagVector σ) : (f + g) * h = f * h + g * h
  := by
  simp [flagVector_mul_comm, flagVector_left_distrib]

theorem flagVector_zero_mul
    (f : FlagVector σ) : 0 * f = 0
  := by
  simp [flagVector_mul_def]

theorem flagVector_mul_sum
    (I : Finset ι) (v : ι → FlagVector σ) (f : FlagVector σ)
    : f * ∑ i ∈ I, v i = ∑ i ∈ I, f * v i
  := by
  classical
  refine Finset.induction_on I ?_ ?_
  · simp
    rw [flagVector_mul_comm, flagVector_zero_mul]
  · intros r R hr ih
    simp [sum_insert hr, flagVector_left_distrib, ih]

theorem flagVector_sum_mul
    (I : Finset ι) (v : ι → FlagVector σ) (f : FlagVector σ)
    : (∑ i ∈ I, v i) * f = ∑ i ∈ I, v i * f
  := by
  simp [flagVector_mul_comm, flagVector_mul_sum]

noncomputable instance : NonUnitalNonAssocRing (FlagVector σ) where
  left_distrib := flagVector_left_distrib
  right_distrib := by
    simp [mul_comm, flagVector_left_distrib]
  zero_mul := flagVector_zero_mul
  mul_zero := by
    intros; rw [mul_comm, flagVector_zero_mul]

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

noncomputable def zeroSet
    (σ : FlagType (Fin n₀)) : Set (FlagVector σ)
  :=
  {k | ∃ (F : FinFlag σ) (ℓ : ℕ), F.1 ≤ ℓ ∧ k = zeroElement F ℓ}

@[simp]
theorem mem_zeroSet
    {k : FlagVector σ} : k ∈ zeroSet σ ↔ ∃ F ℓ, F.1 ≤ ℓ ∧ k = zeroElement F ℓ
  := Iff.rfl

noncomputable def ZeroSpace
    (σ : FlagType (Fin n₀)) : Submodule ℝ (FlagVector σ)
  :=
  Submodule.span ℝ (zeroSet σ)

theorem zeroSpace_closed_under_add
    (f f' : FlagVector σ) (f_zero : f ∈ ZeroSpace σ) (f'_zero : f' ∈ ZeroSpace σ)
    : f + f' ∈ ZeroSpace σ
  := by
  apply Submodule.add_mem <;> assumption

lemma zeroSpace_closed_under_sum
    (S : Finset α) (v : α → FlagVector σ) (h_zero : ∀ s ∈ S, v s ∈ ZeroSpace σ)
    : ∑ s ∈ S, v s ∈ ZeroSpace σ
  := by
  apply Submodule.sum_mem
  assumption

lemma zeroSet_closed_under_smul
    (r : ℝ) (f : FlagVector σ) (f_zero : f ∈ ZeroSpace σ)
    : r • f ∈ ZeroSpace σ
  := by
  apply SMulMemClass.smul_mem
  assumption

def flagVectorEqv (f g : FlagVector σ) : Prop
  :=
  f - g ∈ ZeroSpace σ

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

abbrev FlagAlgebra (σ : FlagType (Fin n₀)) : Type :=
  Quotient (flagVectorSetoid σ)

instance : Zero (FlagAlgebra σ) where
  zero := ⟦0⟧

noncomputable instance : One (FlagAlgebra σ) where
  one := ⟦1⟧

noncomputable instance : Add (FlagAlgebra σ) where
  add := by
    apply Quotient.map₂ (· + ·)
    intro f f' _ g g' _
    show (f + g) ∼v (f' + g')
    dsimp [flagVectorEqv]
    rw [← sub_add_sub_comm f f' g g']
    apply zeroSpace_closed_under_add <;> assumption

noncomputable instance : SMul ℝ (FlagAlgebra σ) where
  smul r := by
    apply Quotient.map (r • ·)
    intro g g' hg
    show (r • g) ∼v (r • g')
    dsimp [flagVectorEqv]
    rw [← smul_sub]
    apply zeroSet_closed_under_smul
    exact hg

noncomputable instance : Neg (FlagAlgebra σ) where
  neg := ((-1 : ℝ) • ·)

noncomputable instance : MulAction ℝ (FlagAlgebra σ) where
  one_smul g := by
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
  mul_smul r s g := by
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [mul_smul]
