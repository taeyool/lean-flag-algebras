import «LeanFlagAlgebras».Utils.LinExtension
import «LeanFlagAlgebras».FlagAlgebra.SubflagListDensity
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The Flag Algebra `A^σ`

This file builds Razborov's flag algebra over the reals. Starting from flags of
a fixed type `σ` (from `FlagDef.lean`), it forms `FlagVector σ` (finitely
supported real combinations of size-tagged flags `FinFlag σ`), defines flag
multiplication via subflag densities (`flagMul`/`flagMulWithSize`), and the
`ZeroSpace` spanned by Razborov's averaging relations (`zeroElement`). The
quotient `FlagAlgebra σ = FlagVector σ / ZeroSpace σ` is then equipped with its
commutative ring and `ℝ`-algebra structure, including `⟦·⟧` quotient lemmas.

Sits above `FlagDef`/`SubflagListDensity` and below the `Forbid`/`Automation` layers
that use it to prove extremal density bounds. -/

namespace FlagAlgebras

open Finset

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- A flag of type `σ` on a fixed `n`-element vertex carrier `Fin n`. -/
abbrev FlagWithSize (σ : FlagType (Fin n₀)) (n : ℕ) : Type
  := Flag σ (Fin n)

instance labeledGraph_inhabited (σ : FlagType (Fin n₀)) {n : ℕ} (hn : n ≥ n₀)
    : Inhabited (LabeledGraph σ (Fin n)) where
  default :=
    let f : Fin n₀ ↪ Fin n := {
      toFun := fun ⟨i, hi⟩ => ⟨i, Nat.lt_of_lt_of_le hi hn⟩,
      inj' := by
        intro i j h
        simp only [Fin.mk.injEq] at h
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
    rcases Quotient.exists_rep F with ⟨Frep, rfl⟩
    refine Quotient.sound (Nonempty.intro ⟨(graphEmbedIso Frep.type_embed).symm, ?_⟩)
    simp [graphEmbedIso, emptyLabeledGraph]
    ext
    simp only [Function.comp_apply, Equiv.ofBijective_symm_apply_apply, RelEmbedding.refl_apply]

noncomputable instance (n : ℕ) : Fintype (FlagWithSize σ n)
  := FlagFintype σ (Fin n)

/-- A flag together with its size: a dependent pair `⟨n, F⟩` of a vertex count
`n` and a flag on `Fin n`. The basis index of `FlagVector σ`. -/
def FinFlag (σ : FlagType (Fin n₀)) : Type
  := Σ (n : ℕ), FlagWithSize σ n

instance : Countable (FinFlag σ)
  :=
  instCountableSigma

/-- The unit flag: the empty flag at size `n₀` (the type `σ` itself). -/
instance : One (FinFlag σ) where
  one := ⟨n₀, (default : FlagWithSize σ n₀)⟩

theorem finFlag_one_fst
    : (1 : FinFlag σ).1 = n₀
  := rfl

theorem finFlag_one_snd
    : (1 : FinFlag σ).2 = emptyFlag σ
  := rfl

theorem flagDensity_one
    (F : FlagWithSize σ n)
    : flagDensity₁ (1 : FinFlag σ).2 F = 1
  := by
  rw [finFlag_one_snd]
  exact flagDensity_empty F

theorem flagPairDensity_one
    (F : FlagWithSize σ n) (G : FlagWithSize σ m)
    : flagDensity₂ (1 : FinFlag σ).2 F G = flagDensity₁ F G
  :=
  flagPairDensity_empty F G

theorem finFlag_size_ge_n₀
    (F : FinFlag σ) : n₀ ≤ F.1 := by
  rcases F with ⟨n, F⟩
  simp_all only
  dsimp [FlagWithSize] at F
  rcases Quotient.exists_rep F with ⟨Frep, _⟩
  have ⟨⟨funF, inj⟩, adj⟩ := Frep.type_embed
  have h_card : Fintype.card (Fin n₀) ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective funF inj
  simp only [Fintype.card_fin] at h_card
  exact h_card

/-- A formal real combination of size-tagged flags: the underlying module of
the flag algebra, before quotienting by Razborov's relations. -/
abbrev FlagVector (σ : FlagType (Fin n₀)) : Type
  := FinFlag σ →₀ ℝ

@[simp]
lemma rat_smul_eq_real_smul
    (a : ℚ) (f : FlagVector σ) : a • f = (a : ℝ) • f
  := rfl

noncomputable instance : MulAction ℚ (FlagVector σ) where
  one_smul f := by simp only [rat_smul_eq_real_smul, Rat.cast_one, one_smul]
  mul_smul r s f := by
    simp only [rat_smul_eq_real_smul, Rat.cast_mul]
    rw [smul_smul]

noncomputable instance : AddCommMonoid (FlagVector σ)
  := Finsupp.instAddCommMonoid

noncomputable instance : AddCommGroup (FlagVector σ)
  := Finsupp.instAddCommGroup

noncomputable instance : Module ℝ (FlagVector σ)
  := Finsupp.module (FinFlag σ) ℝ

/-- The basis vector for a single flag `F`: coefficient `1` on `F`, `0`
elsewhere. -/
noncomputable def basisVector (F : FinFlag σ) : FlagVector σ
  := Finsupp.single F 1

@[simp]
theorem basisVector_apply_self
    (F : FinFlag σ)
    : (basisVector F) F = 1
  := by
  simp [basisVector]

@[simp]
theorem basisVector_support
    (F : FinFlag σ)
    : (basisVector F).support = {F}
  := by
  dsimp only [basisVector]
  rw [Finsupp.support_single_ne_zero _ (by simp)]

theorem basisVector_apply_other
    (F F' : FinFlag σ) (hF : F ≠ F')
    : (basisVector F) F' = 0
  := by
 simp [basisVector, hF]

theorem basisVector_apply_other_size
    (F F' : FinFlag σ) (hF : F.1 ≠ F'.1)
    : (basisVector F) F' = 0
  := by
  apply basisVector_apply_other
  exact fun a ↦ hF (congrArg Sigma.fst a)

/-- Every flag vector expands as the finite sum of its coefficients times the
corresponding `basisVector`s; the workhorse for reducing to single flags. -/
theorem flagVector_eq_sum_basisVector
    (f : FlagVector σ)
    : f = ∑ F ∈ f.support, f F • basisVector F
  := by
  dsimp only [basisVector]
  rw [← Finsupp.sum_single f]
  apply sum_congr (by simp_rw [Finsupp.sum_single])
  rintro _ -
  simp_rw [Finsupp.sum_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The unit flag vector: the basis vector of the unit flag `1`. -/
noncomputable instance : One (FlagVector σ) where
  one := basisVector 1

@[simp]
theorem flagVector_one_support
    : (1 : FlagVector σ).support = {(1 : FinFlag σ)}
  := by
  show (basisVector 1).support = {(1 : FinFlag σ)}
  simp

@[simp]
theorem flagVector_one_apply_one
    : (1 : FlagVector σ) 1 = 1
  := by
  show (basisVector 1) 1 = 1
  simp

/-- Product of two flags expanded onto flags of a chosen size `ℓ`: the formal
combination `∑_G d(F, F'; G) • G` over all size-`ℓ` flags `G`, with `d` the
pair subflag density. Up to `∼v` it is independent of `ℓ` (large enough). -/
noncomputable def flagMulWithSize
    (F F' : FinFlag σ) (ℓ : ℕ) : FlagVector σ
  :=
  ∑ G : FlagWithSize σ ℓ, (flagDensity₂ F.2 F'.2 G) • basisVector ⟨ℓ, G⟩

theorem flagMulWithSize_comm
    (F F' : FinFlag σ) (ℓ : ℕ) : flagMulWithSize F F' ℓ = flagMulWithSize F' F ℓ
  := by
  dsimp [flagMulWithSize]
  apply sum_congr rfl
  rintro _
  simp [flagPairDensity_comm]

theorem flagMulWithSize_one
    (F : FinFlag σ) : flagMulWithSize F 1 F.1 = basisVector F
  := by
  classical
  dsimp [flagMulWithSize]
  rw [finFlag_one_snd]
  have h_univ_split : univ = insert F.2 (univ.erase F.2) := (insert_erase (mem_univ _)).symm
  rw [h_univ_split, sum_insert (notMem_erase _ _)]
  rw [flagPairDensity_empty', flagDensity_self, ← add_zero (basisVector F)]
  congr
  · simp
  · apply sum_eq_zero
    intro F' hF'
    rw [flagPairDensity_empty']
    have hF'_ne_F : F.2 ≠ F' := by
      simp_all only [mem_univ, insert_erase, mem_erase, ne_eq, and_true]
      exact fun a ↦ hF' (id (Eq.symm a))
    norm_num [flagDensity_other hF'_ne_F]

/-- The flag product of `F` and `F'`, taken at the minimal size
`F.1 + F'.1 - n₀` (the natural target size for the pair density). -/
noncomputable def flagMul
    (F F' : FinFlag σ) : FlagVector σ
  :=
  flagMulWithSize F F' (F.1 + F'.1 - n₀)

theorem flagMul_comm
    (F F' : FinFlag σ) : flagMul F F' = flagMul F' F
  := by
  simp [flagMul, add_comm, flagMulWithSize_comm]

theorem flagMul_one
    (F : FinFlag σ) : flagMul F 1 = basisVector F
  := by
  dsimp [flagMul]
  rw [finFlag_one_fst, ← Nat.eq_sub_of_add_eq rfl]
  exact flagMulWithSize_one F

/-- Multiplication on flag vectors: the bilinear extension of `flagMul`. -/
noncomputable instance : Mul (FlagVector σ) where
  mul := bilinearExtension flagMul

theorem flagVector_mul_eq_nested_sum
    (f g : FlagVector σ) : f * g = ∑ F ∈ f.support, ∑ G ∈ g.support, ((f F) * (g G)) • flagMul F G
  :=
  bilinearExtension_eq_nested_sum _ _ _

theorem flagVector_mul_comm
    (f g : FlagVector σ) : f * g = g * f
  := by
  simp only [flagVector_mul_eq_nested_sum]
  rw [sum_comm]
  repeat (apply sum_congr rfl; rintro _ -)
  rw [mul_comm, flagMul_comm]

noncomputable instance : CommMagma (FlagVector σ) where
  mul_comm := flagVector_mul_comm

instance : IsScalarTower ℝ (FlagVector σ) (FlagVector σ) where
  smul_assoc := bilinearExtension_smul_left flagMul

noncomputable instance : HasDistribNeg (FlagVector σ) where
  neg_mul := bilinearExtension_neg_left flagMul
  mul_neg := bilinearExtension_neg_right flagMul

/-- Flag vectors form a non-unital non-associative ring (distributivity and
absorption come from bilinearity of the product); unitality and associativity
hold only up to `∼v` and are established on the quotient. -/
noncomputable instance : NonUnitalNonAssocRing (FlagVector σ) where
  left_distrib := bilinearExtension_add_right flagMul
  right_distrib := bilinearExtension_add_left flagMul
  zero_mul := bilinearExtension_zero_left flagMul
  mul_zero := bilinearExtension_zero_right flagMul

theorem flagVector_mul_one
    (f : FlagVector σ) : f * 1 = f
  := by
  rw [flagVector_eq_sum_basisVector f, sum_mul]
  apply sum_congr rfl
  intro G _
  rw [smul_mul_assoc]; congr
  simp [flagVector_mul_eq_nested_sum, flagMul_one]

noncomputable instance : MulOneClass (FlagVector σ) where
  one_mul g := by
    rw [mul_comm, flagVector_mul_one]
  mul_one := flagVector_mul_one

/-- The averaged expansion of a flag `F` onto size-`ℓ` flags:
`∑_{F'} d(F; F') • F'`. Setting `F` equal to this sum is Razborov's relation. -/
noncomputable def flagExpansion
    (F : FinFlag σ) (ℓ : ℕ) : FlagVector σ
  :=
  ∑ F' : FlagWithSize σ ℓ, (flagDensity₁ F.2 F') • basisVector ⟨ℓ, F'⟩

/-- A generating relation of the flag algebra: `F - ∑_{F'} d(F; F') • F'`,
which is identified with `0` (chain rule / averaging identity). -/
noncomputable def zeroElement
    (F : FinFlag σ) (ℓ : ℕ) : FlagVector σ
  := basisVector F - flagExpansion F ℓ

/-- The set of all generating relations `zeroElement F ℓ` (with `F.1 ≤ ℓ`). -/
noncomputable def zeroSet
    (σ : FlagType (Fin n₀)) : Set (FlagVector σ)
  :=
  {k | ∃ (F : FinFlag σ) (ℓ : ℕ), F.1 ≤ ℓ ∧ k = zeroElement F ℓ}

@[simp]
theorem mem_zeroSet
    {k : FlagVector σ} : k ∈ zeroSet σ ↔ ∃ F ℓ, F.1 ≤ ℓ ∧ k = zeroElement F ℓ
  := Iff.rfl

/-- The submodule spanned by all averaging relations; quotienting by it yields
the flag algebra. Two vectors are flag-equal iff their difference lies here. -/
noncomputable def ZeroSpace
    (σ : FlagType (Fin n₀)) : Submodule ℝ (FlagVector σ)
  :=
  Submodule.span ℝ (zeroSet σ)

theorem zeroElement_in_zeroSpace
    {F : FinFlag σ} {ℓ : ℕ} (hℓ : F.1 ≤ ℓ)
    : zeroElement F ℓ ∈ ZeroSpace σ
  := by
  apply Submodule.mem_span.mpr fun p a ↦ a ?_
  simp; use F; use ℓ

theorem zeroSpace_eq_sum_spanElement
    (k : FlagVector σ) (h_zero : k ∈ ZeroSpace σ)
    : ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (v : I → FlagVector σ),
      (∀ i, v i ∈ zeroSet σ) ∧ (k = ∑ i, c i • v i)
  := by
  rcases Submodule.mem_span_set'.mp h_zero with ⟨n, c, v', h⟩
  let v := fun i ↦ (v' i).val
  have hv : ∀ i, v i ∈ zeroSet σ := by intro i; simp [v, (v' i).property]
  use Fin n, inferInstance, c, v
  simp only [hv, implies_true, true_and, h.symm]
  rfl

theorem zeroSpace_closed_under_add
    (f f' : FlagVector σ) (f_zero : f ∈ ZeroSpace σ) (f'_zero : f' ∈ ZeroSpace σ)
    : f + f' ∈ ZeroSpace σ
  := by
  apply Submodule.add_mem <;> assumption

theorem zeroSpace_closed_under_sub
    (f f' : FlagVector σ) (f_zero : f ∈ ZeroSpace σ) (f'_zero : f' ∈ ZeroSpace σ)
    : f - f' ∈ ZeroSpace σ := by
  apply Submodule.sub_mem <;> assumption

theorem zeroSpace_closed_under_sum
    (S : Finset α) (v : α → FlagVector σ) (h_zero : ∀ s ∈ S, v s ∈ ZeroSpace σ)
    : ∑ s ∈ S, v s ∈ ZeroSpace σ
  :=
  Submodule.sum_mem _ h_zero

theorem zeroSpace_closed_under_smul
    (r : ℝ) (f : FlagVector σ) (f_zero : f ∈ ZeroSpace σ)
    : r • f ∈ ZeroSpace σ
  :=
  SMulMemClass.smul_mem _ f_zero

/-- Flag-equality `f ∼v g`: `f` and `g` differ by an element of `ZeroSpace σ`,
i.e. they represent the same element of the flag algebra. -/
def flagVectorEqv (f g : FlagVector σ) : Prop
  :=
  f - g ∈ ZeroSpace σ

infixl:50 " ∼v " => flagVectorEqv

theorem basisVector_eqv_flagExpansion
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : basisVector F ∼v flagExpansion F ℓ
  :=
  zeroElement_in_zeroSpace hℓ

theorem one_vector_eqv_flagExpansion
    (ℓ : ℕ) (hℓ : n₀ ≤ ℓ)
    : (1 : FlagVector σ) ∼v flagExpansion 1 ℓ
  :=
  basisVector_eqv_flagExpansion _ _ (finFlag_one_fst ▸ hℓ)

@[refl]
theorem flagVectorEqv.refl (f : FlagVector σ)
    : f ∼v f
  := by
  dsimp [flagVectorEqv]
  rw [sub_self]
  exact Submodule.zero_mem _

@[simp]
theorem flagVectorEqv.rfl {f : FlagVector σ}
    : f ∼v f
  :=
  .refl f

@[symm]
theorem flagVectorEqv.symm
    : ∀ {f f' : FlagVector σ}, f ∼v f' → f' ∼v f
  := by
  intro f f' h
  dsimp [flagVectorEqv] at *
  exact sub_mem_comm_iff.mp h

theorem flagVectorEqv.trans
    : ∀ {f f' f'' : FlagVector σ}, f ∼v f' → f' ∼v f'' → f ∼v f''
  := by
  intro f f' f'' h h'
  dsimp [flagVectorEqv] at *
  rw [← sub_add_sub_cancel]
  exact zeroSpace_closed_under_add (f - f') (f' - f'') h h'

instance : Trans (@flagVectorEqv n₀ σ) (@flagVectorEqv n₀ σ) (@flagVectorEqv n₀ σ) where
  trans := flagVectorEqv.trans

theorem flagVector_eq_eqv
    {f f' : FlagVector σ} (h : f = f') : f ∼v f'
  :=
  h ▸ .rfl

theorem flagVectorEqv_sum
    {S : Finset α} {v v' : α → FlagVector σ} (h_eqv : ∀ s ∈ S, v s ∼v v' s)
    : ∑ s ∈ S, v s ∼v ∑ s ∈ S, v' s
  := by
  rw [flagVectorEqv, ← sum_sub_distrib]
  exact zeroSpace_closed_under_sum _ _ h_eqv

theorem flagVectorEqv_smul
    (r : ℝ) {f f' : FlagVector σ} (h_eqv : f ∼v f')
    : r • f ∼v r • f'
  := by
  rw [flagVectorEqv, ← smul_sub]
  exact zeroSpace_closed_under_smul _ _ h_eqv

/-- The setoid on flag vectors given by flag-equality `∼v`; its quotient is
`FlagAlgebra σ`. -/
instance flagVectorSetoid (σ : FlagType (Fin n₀))
    : Setoid (FlagVector σ) where
  r     := flagVectorEqv
  iseqv := {
    refl := flagVectorEqv.refl,
    symm := flagVectorEqv.symm,
    trans := flagVectorEqv.trans
  }

/-- The flag algebra `A^σ`: flag vectors modulo Razborov's averaging relations.
Carries a commutative `ℝ`-algebra structure (built below). -/
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
    exact zeroSpace_closed_under_smul _ _ hg

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

theorem add_quot
    (f f' : FlagVector σ)
    : (⟦f + f'⟧ : FlagAlgebra σ) = ⟦f⟧ + ⟦f'⟧
  :=
  rfl

theorem neg_quot
    (f : FlagVector σ) : (⟦-f⟧ : FlagAlgebra σ) = -⟦f⟧
  := by
  apply Quotient.sound
  simp only [neg_smul, one_smul]
  rfl

theorem smul_quot
    (r : ℝ) (f : FlagVector σ) : (⟦r • f⟧ : FlagAlgebra σ) = r • ⟦f⟧
  :=
  rfl

theorem sum_smul
    (s : Finset ι) (c : ι → ℝ) (f : FlagVector σ) : (∑ i ∈ s, c i) • f = ∑ i ∈ s, c i • f
  := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [sum_empty, zero_smul]
  · intro r R hr ih
    simp only [sum_insert hr, add_smul, ih]

/-- The size at which a flag product is expanded does not matter modulo `∼v`,
as long as it is large enough. Justifies the choice in `flagMul`. -/
theorem flagMulWithSize_indep_on_size
    {F₁ F₂ : FinFlag σ} {ℓ₁ ℓ₂ : ℕ} (hℓ₁ : F₁.1 + F₂.1 ≤ ℓ₁ + n₀) (hℓ₂ : F₁.1 + F₂.1 ≤ ℓ₂ + n₀)
    : flagMulWithSize F₁ F₂ ℓ₁ ∼v flagMulWithSize F₁ F₂ ℓ₂
  := by
  wlog hℓ : ℓ₁ ≤ ℓ₂ generalizing ℓ₁ ℓ₂
  · have hℓ' : ℓ₂ ≤ ℓ₁ := Nat.le_of_not_ge hℓ
    exact (this hℓ₂ hℓ₁ hℓ').symm
  simp only [flagMulWithSize]
  calc
    _ ∼v (∑ F' : FlagWithSize σ ℓ₁, ↑(flagDensity₂ F₁.2 F₂.2 F') • flagExpansion ⟨ℓ₁, F'⟩ ℓ₂) := by
      apply flagVectorEqv_sum; rintro _ -
      apply flagVectorEqv_smul
      apply zeroElement_in_zeroSpace hℓ
    _ ∼v (∑ F' : FlagWithSize σ ℓ₁, ∑ G' : FlagWithSize σ ℓ₂,
          ↑(flagDensity₂ F₁.snd F₂.snd F') • ↑(flagDensity₁ F' G') • basisVector ⟨ℓ₂, G'⟩) := by
      apply flagVectorEqv_sum; rintro _ -
      dsimp only [flagExpansion]
      rw [smul_sum]
    _ ∼v _ := by
      rw [sum_comm]
      apply flagVectorEqv_sum; rintro _ -
      rw [density_chain_rule₂₁ ℓ₁] <;> try (first | assumption | apply finFlag_size_ge_n₀)
      simp_rw [rat_smul_eq_real_smul, Rat.cast_sum, Rat.cast_mul, sum_smul]
      apply flagVectorEqv_sum; rintro _ -
      rw [smul_smul]

theorem flagMul_indep_on_size
    {F₁ F₂ : FinFlag σ} {ℓ' : ℕ} (hℓ' : F₁.1 + F₂.1 ≤ ℓ' + n₀)
    : (flagMul F₁ F₂) ∼v (flagMulWithSize F₁ F₂ ℓ')
  := by
  refine flagMulWithSize_indep_on_size ?_ hℓ'
  rw [Nat.sub_add_cancel]
  exact Nat.le_add_right_of_le (finFlag_size_ge_n₀ _)

theorem flag_mul_zeroElement
    (F G : FinFlag σ) (ℓ : ℕ) (hℓ : G.1 ≤ ℓ) : (basisVector F) * (zeroElement G ℓ) ∈ ZeroSpace σ
  := by
  rw [zeroElement, mul_sub]
  show _ ∼v _
  simp only [flagExpansion, rat_smul_eq_real_smul, mul_sum]
  let L := F.1 + G.1 + ℓ
  symm
  calc
    _ ∼v (∑ i : FlagWithSize σ ℓ, ↑(flagDensity₁ G.2 i) • (basisVector F * basisVector ⟨ℓ, i⟩)) := by
      apply flagVectorEqv_sum; rintro _ -
      simp_rw [mul_comm (basisVector F), smul_mul_assoc, mul_comm]
      rfl
    _ ∼v (∑ F' : FlagWithSize σ ℓ, ↑(flagDensity₁ G.2 F') • flagMulWithSize F ⟨ℓ, F'⟩ L) := by
      apply flagVectorEqv_sum; rintro _ -
      apply flagVectorEqv_smul
      simp_rw [flagVector_mul_eq_nested_sum, basisVector_support, sum_singleton,
        basisVector_apply_self, mul_one, one_smul]
      apply flagMul_indep_on_size
      grind
    _ ∼v (∑ G' : FlagWithSize σ L, ∑ F' : FlagWithSize σ ℓ,
          ↑(flagDensity₁ G.2 F') • ↑(flagDensity₂ F.2 F' G') • basisVector ⟨L, G'⟩) := by
      rw [sum_comm]
      apply flagVectorEqv_sum; rintro _ -
      simp_rw [flagMulWithSize, rat_smul_eq_real_smul]
      rw [smul_sum]
    _ ∼v (∑ G' : FlagWithSize σ L, (∑ F' : FlagWithSize σ ℓ,
          ↑(flagDensity₁ G.2 F') * ↑(flagDensity₂ F.2 F' G')) • basisVector ⟨L, G'⟩) := by
      apply flagVectorEqv_sum; rintro _ -
      simp_rw [rat_smul_eq_real_smul, Rat.cast_sum, Rat.cast_mul, sum_smul]
      apply flagVectorEqv_sum; rintro _ -
      rw [smul_smul]
    _ ∼v flagMulWithSize F G (F.1 + G.1 + ℓ) := by
      apply flagVectorEqv_sum; rintro _ -
      nth_rw 1 [flagPairDensity_comm]
      rw [density_chain_rule₁₂ ℓ _ _ _ _ _ hℓ (by grind)] <;> try (apply finFlag_size_ge_n₀)
      apply flagVector_eq_eqv
      simp_rw [rat_smul_eq_real_smul]; congr
      funext
      rw [flagPairDensity_comm]
    _ ∼v (basisVector F * basisVector G) := by
      simp_rw [flagVector_mul_eq_nested_sum, basisVector_support, sum_singleton,
        basisVector_apply_self, mul_one, one_smul]
      symm
      apply flagMul_indep_on_size
      grind

/-- `ZeroSpace σ` is an ideal: multiplying any flag vector by a relation stays
in `ZeroSpace σ`. This is what makes multiplication well defined on the
quotient. -/
theorem flagVector_mul_zeroSpace
   (f : FlagVector σ) {k : FlagVector σ} (hk_zero : k ∈ ZeroSpace σ) : f * k ∈ ZeroSpace σ
  := by
  rw [flagVector_eq_sum_basisVector f, sum_mul]
  apply zeroSpace_closed_under_sum
  intro F _
  rcases zeroSpace_eq_sum_spanElement k hk_zero with ⟨I, hI, c, v, hv, hk_sum⟩
  rw [hk_sum, mul_sum]
  apply zeroSpace_closed_under_sum
  intro i _
  rw [smul_mul_assoc]
  apply zeroSpace_closed_under_smul
  rw [mul_comm, smul_mul_assoc]
  apply zeroSpace_closed_under_smul
  obtain ⟨H, ℓ, hℓ, hvi⟩ := mem_zeroSet.mp (hv i)
  simp [mul_comm, hvi]
  exact flag_mul_zeroElement F H ℓ hℓ

/-- Multiplication on the flag algebra, descended from `FlagVector` via the
ideal property of `ZeroSpace σ`. -/
noncomputable instance : Mul (FlagAlgebra σ) where
  mul := by
    apply Quotient.map₂ (· * ·)
    intro f' f hf g' g hg
    show (f' * g') ∼v (f * g)
    dsimp [flagVectorEqv]
    let kf := f' - f
    let kg := g' - g
    have : f' * g' = (f + kf) * (g + kg) := by
      rw [← sub_add_cancel f' f, ← sub_add_cancel g' g, add_comm _ f, add_comm _ g]
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

@[simp]
theorem flagAlgebra_mul_zero
    (f : FlagAlgebra σ) : f * 0 = 0
  := by
  rw [← Quotient.out_eq f]
  apply Quotient.sound
  simp

@[simp]
theorem flagAlgebra_mul_one
    (f : FlagAlgebra σ) : f * 1 = f
  := by
  rw [← Quotient.out_eq f]
  apply Quotient.sound
  simp

theorem flagVector_smul_mul_smul_comm
    (f g : FlagVector σ) (a b : ℝ)
    : a • f * b • g = (a * b) • (f * g)
  := by
  show bilinearExtension flagMul (a • f) (b • g) = (a * b) • bilinearExtension flagMul f g
  rw [bilinearExtension_smul_left, bilinearExtension_smul_right, smul_smul]

/-- A product of three single-flag basis vectors equals (mod `∼v`) the sum over
size-`ℓ` flags weighted by the triple subflag density; the engine behind
associativity. -/
theorem three_flag_mul_eqv_sum_tripleDensity
    {F₁ F₂ F₃ : FinFlag σ} {ℓ : ℕ} (hℓ : ℓ = F₁.1 + F₂.1 + F₃.1 - n₀ - n₀)
    : (basisVector F₁ * basisVector F₂ * basisVector F₃) ∼v
      (∑ (G : FlagWithSize σ ℓ), (flagDensity₃ F₁.2 F₂.2 F₃.2 G) • basisVector ⟨ℓ, G⟩)
  := by
  nth_rw 2 [flagVector_mul_eq_nested_sum]
  simp_rw [basisVector_support, flagMul, flagMulWithSize, sum_singleton, basisVector_apply_self,
    mul_one, one_smul, sum_mul]
  let ℓ' := F₁.1 + F₂.1 - n₀
  calc
    _ ∼v (∑ F : FlagWithSize σ ℓ, ∑ F' : FlagWithSize σ ℓ',
          flagDensity₂ F₁.2 F₂.2 F' • flagDensity₂ F' F₃.2 F • basisVector ⟨ℓ, F⟩) := by
      rw [sum_comm]
      apply flagVectorEqv_sum; rintro _ -; simp_rw [rat_smul_eq_real_smul]
      rw [smul_mul_assoc, ← smul_sum]
      apply flagVectorEqv_smul
      simp [flagVector_mul_eq_nested_sum, flagMul, flagMulWithSize]
      rw [hℓ, ← Nat.sub_add_comm]
      exact Nat.le_add_right_of_le (finFlag_size_ge_n₀ _)
    _ ∼v (∑ G : FlagWithSize σ ℓ, (∑ F' : FlagWithSize σ ℓ',
          flagDensity₂ F₁.2 F₂.2 F' • flagDensity₂ F' F₃.2 G) • basisVector ⟨ℓ, G⟩) := by
      apply flagVectorEqv_sum; rintro _ -; simp [sum_smul]
      apply flagVectorEqv_sum; rintro _ -; simp [smul_smul]
    _ ∼v _ := by
      apply flagVectorEqv_sum
      rintro G -
      have : flagDensity₃ F₁.2 F₂.2 F₃.2 G
        = ∑ F' : FlagWithSize σ ℓ', flagDensity₂ F₁.2 F₂.2 F' * flagDensity₂ F' F₃.2 G := by
        apply density_chain_rule₂₂ ℓ' <;> try (apply finFlag_size_ge_n₀)
        · rw [Nat.sub_add_cancel]
          exact Nat.le_add_right_of_le (finFlag_size_ge_n₀ _)
        · simp only [ℓ', hℓ]
          apply Nat.le_of_eq
          calc
            _ = F₁.1 + F₂.1 + F₃.1 - n₀ := by
              rw [← Nat.sub_add_comm]
              exact Nat.le_add_right_of_le (finFlag_size_ge_n₀ _)
            _ = F₁.1 + F₂.1 + F₃.1 - n₀ - n₀ + n₀ := by
              rw [Nat.sub_add_cancel]
              refine Nat.le_sub_of_add_le (Nat.add_le_add (Nat.le_add_right_of_le ?_) ?_) <;>
              apply finFlag_size_ge_n₀
      simp [this]

theorem basisVector_mul_assoc
    (F₁ F₂ F₃ : FinFlag σ)
    : (basisVector F₁ * basisVector F₂ * basisVector F₃) ∼v
      (basisVector F₁ * (basisVector F₂ * basisVector F₃))
  := by
  nth_rw 2 [mul_comm (basisVector F₁)]
  let ℓ := F₁.1 + F₂.1 + F₃.1 - n₀ - n₀
  calc
    _ ∼v (∑ (G : FlagWithSize σ ℓ), (flagDensity₃ F₁.2 F₂.2 F₃.2 G) • basisVector ⟨ℓ, G⟩) :=
      three_flag_mul_eqv_sum_tripleDensity rfl
    _ ∼v (∑ (G : FlagWithSize σ ℓ), (flagDensity₃ F₂.2 F₃.2 F₁.2 G) • basisVector ⟨ℓ, G⟩) :=
      flagVectorEqv_sum fun _ _ ↦ by rw [flagTripleDensity_comm]
    _ ∼v basisVector F₂ * basisVector F₃ * basisVector F₁ := by
      refine (three_flag_mul_eqv_sum_tripleDensity ?_).symm
      dsimp only [ℓ]
      ring_nf

/-- Associativity of the flag product holds modulo `∼v` (it fails on the nose
on `FlagVector`); lifted to genuine associativity on the quotient. -/
theorem flagVector_mul_assoc
    (f g h : FlagVector σ) : (f * g * h) ∼v (f * (g * h))
  := by
  rw [flagVector_eq_sum_basisVector f, flagVector_eq_sum_basisVector g, flagVector_eq_sum_basisVector h]
  simp only [mul_sum, sum_mul, flagVector_smul_mul_smul_comm, mul_assoc]
  iterate 3 (apply flagVectorEqv_sum; rintro _ -)
  exact flagVectorEqv_smul _ (basisVector_mul_assoc _ _ _)

theorem flagAlgebra_mul_assoc
    (f g h : FlagAlgebra σ) : f * g * h = f * (g * h)
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  exact Quotient.sound (flagVector_mul_assoc _ _ _)

theorem flagAlgebra_smul_mul_smul_comm
    (f g : FlagAlgebra σ) (a b : ℝ)
    : a • f * b • g = (a * b) • (f * g)
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g]
  apply Quotient.sound
  simp only [flagVector_smul_mul_smul_comm, Setoid.refl]

/-- The flag algebra is a ring: all axioms descend from `FlagVector` since the
defects (unitality, associativity) vanish modulo `ZeroSpace σ`. -/
noncomputable instance : Ring (FlagAlgebra σ) where
  add_assoc a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c]
    apply Quotient.sound
    simp [add_assoc]
  zero_add a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  add_zero a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  add_comm a b := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    apply Quotient.sound
    simp
    rw [add_comm]
  neg_add_cancel a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  mul_assoc := flagAlgebra_mul_assoc
  zero_mul a := by
    simp only [flagAlgebra_mul_comm, flagAlgebra_mul_zero]
  mul_zero := flagAlgebra_mul_zero
  one_mul a := by
    simp only [flagAlgebra_mul_comm, flagAlgebra_mul_one]
  mul_one := flagAlgebra_mul_one
  left_distrib := flagAlgebra_left_distrib
  right_distrib a b c := by
    simp only [flagAlgebra_mul_comm, flagAlgebra_left_distrib]
  nsmul n g := (n : ℝ) • g
  nsmul_zero g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
  nsmul_succ n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [add_smul, one_smul]
  zsmul z g := (z : ℝ) • g
  zsmul_zero' g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
  zsmul_succ' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [add_smul, one_smul]
  zsmul_neg' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [← neg_smul, neg_add_rev]

/-- The flag algebra is commutative (flag products are symmetric). -/
noncomputable instance : CommRing (FlagAlgebra σ) where
  mul_comm := flagAlgebra_mul_comm

theorem mul_quot
    (f f' : FlagVector σ)
    : (⟦f * f'⟧ : FlagAlgebra σ) = ⟦f⟧ * ⟦f'⟧
  :=
  rfl

theorem sum_quot
    {ι : Type} (s : Finset ι) (f : ι → FlagVector σ)
    : ⟦∑ i ∈ s, f i⟧ = ∑ i ∈ s, (⟦f i⟧ : FlagAlgebra σ)
  := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s his ih
  simp only [Finset.sum_insert his, add_quot, ih]

/-- In the flag algebra, a single flag equals its density expansion onto larger
flags: the averaging relation rendered as an equation on `⟦·⟧`. -/
theorem basisVector_quot_eq_sum
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦basisVector F⟧ = ∑ F' : FlagWithSize σ ℓ, (flagDensity₁ F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ)
  := by
  simp_rw [← smul_quot, ← sum_quot]
  apply Quotient.sound
  exact basisVector_eqv_flagExpansion _ _ hℓ

/-- The sum of all flags of any fixed size `ℓ ≥ n₀` equals `1` in the flag
algebra; the basic normalization identity used throughout density proofs. -/
theorem sum_flagWithSize_eq_one
    (ℓ : ℕ) (hℓ : ℓ ≥ n₀)
    : ∑ F : FlagWithSize σ ℓ, (⟦basisVector ⟨ℓ, F⟩⟧ : FlagAlgebra σ) = (1 : FlagAlgebra σ)
  := by
  show _ = ⟦basisVector 1⟧
  rw [basisVector_quot_eq_sum 1 ℓ hℓ]
  apply Finset.sum_congr rfl
  rintro F -
  rw [flagDensity_one F]
  simp only [Rat.cast_one, one_smul]

theorem basisVector_quot_mul_eq_flagMulWithSize_quot
    (F G : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 + G.1 ≤ ℓ + n₀)
    : (⟦basisVector F⟧ * ⟦basisVector G⟧ : FlagAlgebra σ) = ⟦flagMulWithSize F G ℓ⟧
  := by
  apply Quotient.sound
  simp only [flagVector_mul_eq_nested_sum, basisVector_support, sum_singleton, basisVector_apply_self,
    mul_one, one_smul]
  exact flagMul_indep_on_size hℓ

/-- The product of two flags in the algebra is the quotient of their `flagMul`
(the density-weighted expansion); links the ring product to subflag densities. -/
theorem basisVector_quot_mul_eq_flagMul_quot
    (F G : FinFlag σ)
    : (⟦basisVector F⟧ * ⟦basisVector G⟧ : FlagAlgebra σ) = ⟦flagMul F G⟧
  := by
  rw [basisVector_quot_mul_eq_flagMulWithSize_quot F G (F.1 + G.1 - n₀) (by omega)]
  apply Quotient.sound
  exact flagMul_indep_on_size (by omega)

theorem linearExtension_basisVector
    {R : Type} [AddCommGroup R] [Module ℝ R] (f : FinFlag σ → R) (F : FinFlag σ)
    : linearExtension f (basisVector F) = f F
  := by
  simp only [basisVector, linearExtension_single_one]

/-- In the flag algebra, `0 ≠ 1`: a linear density functional `φ` separating the
unit `1` from every generator of `ZeroSpace σ` witnesses nontriviality. -/
theorem flagAlgebra_zero_ne_one : (0 : FlagAlgebra σ) ≠ 1 := by
    intro h_zero_eq_one
    have one_eq_zero : (1 : FlagAlgebra σ) = 0 := h_zero_eq_one.symm
    have h_one_zeroSet : (1 : FlagVector σ) ∈ ZeroSpace σ := by
      rw [← sub_zero 1]
      exact Quotient.exact one_eq_zero
    rcases zeroSpace_eq_sum_spanElement 1 h_one_zeroSet with ⟨I, hI, c, v, hv, hx⟩
    choose G ℓ hG using hv
    let L := max (Finset.sup (univ : Finset I) ℓ) n₀
    have hL : L ≥ n₀ := le_max_right _ _
    let F := (flagWithSize_inhabited σ hL).default
    let φ : FlagVector σ → ℝ := linearExtension (fun G => flagDensity₁ G.2 F)
    have φ_add : ∀ (g h : FlagVector σ), φ (g + h) = φ g + φ h := linearExtension_add _
    have φ_smul : ∀ (r : ℝ) (g : FlagVector σ), φ (r • g) = r * φ g := linearExtension_smul _
    have φ_sum : ∀ (s : Finset I) (f : I → FlagVector σ), φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) :=
      linearExtension_sum _
    have hφ : ∀ (i : I), φ (v i) = 0 := by
      intro i
      let iG := G i
      have ⟨hℓ', hG2⟩ : iG.fst ≤ ℓ i ∧ v i = zeroElement iG (ℓ i) := by apply hG
      have hℓ : ℓ i ≤ L := le_sup_iff.mpr <| .inl <| le_sup (mem_univ _)
      have φ_sum' : ∀ (s : Finset (FlagWithSize σ (ℓ i))) (f : FlagWithSize σ (ℓ i) → FlagVector σ), φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) :=
        linearExtension_sum _
      have φ_neg : φ (-flagExpansion iG (ℓ i)) = -φ (flagExpansion iG (ℓ i)) :=
        linearExtension_neg _ _
      rw [hG2, zeroElement, sub_eq_add_neg, φ_add]
      rw [φ_neg, ← sub_eq_add_neg, sub_eq_zero, flagExpansion, φ_sum']
      have : φ (basisVector iG) = flagDensity₁ iG.2 F := by
        simp only [φ, linearExtension_basisVector]
      have hℓ'' : n₀ ≤ iG.fst := finFlag_size_ge_n₀ iG
      rw [this, density_chain_rule₁₁ (ℓ i) iG.2 F hℓ'' hℓ' hℓ]
      simp only [Rat.cast_sum, Rat.cast_mul, rat_smul_eq_real_smul]
      refine sum_congr rfl fun x _ ↦ ?_
      simp_rw [φ_smul, mul_eq_mul_left_iff, Rat.cast_eq_zero]
      rw [Or.comm, or_iff_not_imp_left]
      simp only [linearExtension_basisVector, φ, implies_true]
    have h_φ_1 : φ 1 = 1 := by
      show ∑ G ∈ (basisVector 1).support, _ = 1
      simp [sum_singleton, flagDensity_one]
    have h_φ_sum : φ (∑ i, c i • v i) = 0 := by
      simp_all only [mul_zero, sum_const_zero, zero_ne_one]
    rw [hx] at h_φ_1
    have zero_eq_one : (0 : ℝ) = (1 : ℝ) := by rw [← h_φ_1, ← h_φ_sum]
    exact zero_ne_one zero_eq_one

instance : NeZero (1 : FlagAlgebra σ) where
  out := flagAlgebra_zero_ne_one.symm

/-- The flag algebra is nontrivial: `0 ≠ 1`, via the `NeZero (1 : FlagAlgebra σ)`
witness `flagAlgebra_zero_ne_one`. -/
instance : Nontrivial (FlagAlgebra σ) where
  exists_pair_ne := ⟨0, 1, flagAlgebra_zero_ne_one⟩

/-- The `ℝ`-algebra structure on the flag algebra, with `algebraMap r = r • 1`;
this is the final structure used by the density-bound proofs. -/
noncomputable instance : Algebra ℝ (FlagAlgebra σ) where
  algebraMap := {
    toFun r := r • 1
    map_zero' := by
      apply Quotient.sound
      simp only [zero_smul, Setoid.refl]
    map_one' := by
      apply Quotient.sound
      simp only [one_smul, Setoid.refl]
    map_add' x y := by
      apply Quotient.sound
      simp only
      rw [add_smul]
    map_mul' x y := by
      apply Quotient.sound
      simp only [smul_one_mul]
      rw [mul_smul]
  }
  smul_def' r g := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    nth_rw 1 [← one_mul g]
    nth_rw 2 [← one_smul ℝ g]
    rw [flagAlgebra_smul_mul_smul_comm, mul_one]
  commutes' := by
    rintro _ -; simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [mul_comm]

end FlagAlgebras
