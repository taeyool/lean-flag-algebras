import «LeanFlagAlgebras».SubflagDensity
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span

open FlagAlgebras
open Finset

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

abbrev FlagWithSize (σ : FlagType T) (n : ℕ) : Type
  := Flag σ (Fin n)

instance labeledGraph_inhabited (σ : FlagType (Fin n₀)) {n : ℕ} (hn : n ≥ n₀)
    : Inhabited (LabeledGraph σ (Fin n)) where
  default :=
    let f : Fin n₀ ↪ Fin n := {
      toFun := fun ⟨i, hi⟩ => ⟨i, Nat.lt_of_lt_of_le hi hn⟩,
      inj' := by
        intro i j h
        simp [Fin.mk.injEq, ge_iff_le] at h
        ext1
        assumption
    }
    { graph := σ.map f, type_embed := SimpleGraph.Embedding.map f σ }

instance flagWithSize_inhabited (σ : FlagType (Fin n₀)) {n : ℕ} (hn : n ≥ n₀)
    : Inhabited (FlagWithSize σ n) where
  default := ⟦(labeledGraph_inhabited σ hn).default⟧

instance flagWithSize_inhabited_empty (σ : FlagType (Fin n₀))
    : Inhabited (FlagWithSize σ n₀) where
  default := emptyFlag σ

noncomputable def graphEmbedIso
    {G G' : SimpleGraph (Fin n₀)} (f : G ↪g G') : G ≃g G' where
  toEquiv := by
    apply Equiv.ofBijective f
    rw [← Finite.injective_iff_bijective]
    exact RelEmbedding.injective f
  map_rel_iff' := by
    intro a b
    simp only [Equiv.ofBijective_apply, SimpleGraph.Embedding.map_adj_iff]

instance : Unique (FlagWithSize σ n₀) where
  uniq := by
    intro F
    rcases Quotient.exists_rep F with ⟨Frep, hFrep⟩
    rw [← hFrep]
    apply Quotient.sound
    apply Nonempty.intro
    refine ⟨?_, ?_⟩
    · exact (graphEmbedIso Frep.type_embed).symm
    · simp [graphEmbedIso, emptyLabeledGraph]
      subst hFrep
      ext
      simp only [Function.comp_apply, Equiv.ofBijective_symm_apply_apply, RelEmbedding.refl_apply]

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

theorem flagMulWithSize_comm
    (F F' : FinFlag σ) (ℓ : ℕ) : flagMulWithSize F F' ℓ = flagMulWithSize F' F ℓ
  := by
  dsimp [flagMulWithSize]
  apply sum_congr rfl
  intros
  simp [flagPairDensity_comm]

noncomputable def flagMul
    (F F' : FinFlag σ) : FlagVector σ
  :=
  flagMulWithSize F F' (F.1 + F'.1)

theorem flagMul_comm
    (F F' : FinFlag σ) : flagMul F F' = flagMul F' F
  := by
  simp [flagMul, add_comm, flagMulWithSize_comm]

noncomputable instance : Mul (FlagVector σ) where
  mul f g := ∑ F in f.support, ∑ G in g.support, ((f F) * (g G)) • flagMul F G

theorem flagVector_mul_def
    (f g : FlagVector σ) : f * g = ∑ F in f.support, ∑ G in g.support, ((f F) * (g G)) • flagMul F G
  := rfl

theorem flagVector_mul_comm
    (f g : FlagVector σ) : f * g = g * f
  := by
  simp [flagVector_mul_def]
  rw [sum_comm]
  repeat (apply sum_congr rfl; intros)
  rw [mul_comm, flagMul_comm]

theorem flagVector_mul_one
    (f : FlagVector σ) : f * 1 = f
  :=
  sorry

noncomputable instance : CommMagma (FlagVector σ) where
  mul_comm := flagVector_mul_comm

noncomputable instance : MulOneClass (FlagVector σ) where
  one_mul g := by
    rw [mul_comm, flagVector_mul_one]
  mul_one := flagVector_mul_one

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

theorem flagVector_mul_zeroSpace
   (f : FlagVector σ) {k : FlagVector σ} (hk_zero : k ∈ ZeroSpace σ) : f * k ∈ ZeroSpace σ
  :=
  sorry

noncomputable instance : Mul (FlagAlgebra σ) where
  mul := by
    apply Quotient.map₂ (· * ·)
    intro f' f hf g' g hg
    show (f' * g') ∼v (f * g)
    dsimp [flagVectorEqv]
    let kf := f' - f
    let kg := g' - g
    have : f' * g' = (f + kf) * (g + kg) := by
      rw [← sub_add_cancel f' f, ← sub_add_cancel g' g]
      simp only [kf, kg, add_comm]
    rw [this, mul_add, add_mul, add_mul, add_assoc, add_sub_cancel_left]
    apply zeroSpace_closed_under_add
    · rw [mul_comm]
      exact flagVector_mul_zeroSpace g hf
    · apply zeroSpace_closed_under_add
      · exact flagVector_mul_zeroSpace f hg
      · exact flagVector_mul_zeroSpace kf hg

theorem flagAlgebra_mul_comm
    (f g : FlagAlgebra σ) : f * g = g * f
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g]
  apply Quotient.sound
  simp
  rw [mul_comm]

theorem flagAlgebra_left_distrib
    (f g h : FlagAlgebra σ) : f * (g + h) = f * g + f * h
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp [mul_add]
  rfl

theorem flagAlgebra_mul_zero
    (f : FlagAlgebra σ) : f * 0 = 0
  := by
  rw [← Quotient.out_eq f]
  apply Quotient.sound
  simp; rfl

theorem flagAlgebra_mul_one
    (f : FlagAlgebra σ) : f * 1 = f
  := by
  rw [← Quotient.out_eq f]
  apply Quotient.sound
  simp

theorem flagVector_smul_mul_smul_comm
    (f g : FlagVector σ) (a b : ℝ)
    : a • f * b • g = (a * b) • (f * g)
  :=
  sorry

theorem flagVector_mul_assoc
    (f g h : FlagVector σ) : (f * g * h) ∼v (f * (g * h))
  :=
  sorry

theorem flagAlgebra_mul_assoc
    (f g h : FlagAlgebra σ) : f * g * h = f * (g * h)
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  apply flagVector_mul_assoc

theorem flagAlgebra_smul_mul_smul_comm
    (f g : FlagAlgebra σ) (a b : ℝ)
    : a • f * b • g = (a * b) • (f * g)
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g]
  apply Quotient.sound
  simp
  rw [flagVector_smul_mul_smul_comm]

noncomputable instance : Ring (FlagAlgebra σ) where
  add := (· + ·)
  add_assoc a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c]
    apply Quotient.sound
    simp_all
    rw [add_assoc]
  zero := 0
  zero_add a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  add_zero a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  neg := -(·)
  add_comm a b := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    apply Quotient.sound
    simp
    rw [add_comm]
  neg_add_cancel a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp; rfl
  mul := (· * ·)
  mul_assoc := flagAlgebra_mul_assoc
  zero_mul a := by
    rw [flagAlgebra_mul_comm]
    apply flagAlgebra_mul_zero
  mul_zero := flagAlgebra_mul_zero
  one := 1
  one_mul a := by
    rw [flagAlgebra_mul_comm]
    apply flagAlgebra_mul_one
  mul_one := flagAlgebra_mul_one
  left_distrib := flagAlgebra_left_distrib
  right_distrib a b c := by
    simp [flagAlgebra_mul_comm, flagAlgebra_left_distrib]
  nsmul n g := (n : ℝ) • g
  nsmul_zero g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  nsmul_succ n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul z g := (z : ℝ) • g
  zsmul_zero' g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  zsmul_succ' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul_neg' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [← neg_smul, neg_add_rev]

noncomputable instance : CommRing (FlagAlgebra σ) where
  mul_comm := flagAlgebra_mul_comm

instance : NeZero (1 : FlagAlgebra σ) where
  out := sorry

instance : Nontrivial (FlagAlgebra σ) where
  exists_pair_ne := ⟨0, 1, (by simp)⟩

noncomputable instance : Algebra ℝ (FlagAlgebra σ) where
  toFun r := r • 1
  map_zero' := by
    apply Quotient.sound
    simp; rfl
  map_one' := by
    apply Quotient.sound
    simp; rfl
  map_add' x y := by
    apply Quotient.sound
    simp
    rw [add_smul]
  map_mul' x y := by
    apply Quotient.sound
    simp
    rw [mul_smul]
  smul_def' r g := by
    simp
    nth_rw 1 [← one_mul g]
    nth_rw 2 [← one_smul ℝ g]
    rw [flagAlgebra_smul_mul_smul_comm, mul_one]
  commutes' := by
    intros; simp
    rw [mul_comm]
