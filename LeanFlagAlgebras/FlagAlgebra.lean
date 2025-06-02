import «LeanFlagAlgebras».SubflagDensity
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span

open FlagAlgebras
open Finset

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

abbrev FlagWithSize (σ : FlagType (Fin n₀)) (n : ℕ) : Type
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

theorem finFlag_one_fst
    : (1 : FinFlag σ).1 = n₀
  := rfl

theorem finFlag_one_snd
    : (1 : FinFlag σ).2 = emptyFlag σ
  := rfl

theorem flagDensity_one
    (F : FlagWithSize σ n)
    : flagDensity₁ (1 : FinFlag σ).2 F = 1
  := by sorry

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
  have ⟨emb, adj⟩ := Frep.type_embed
  have ⟨funF, inj⟩ := emb
  have : n₀ ≤ n := by
    have h_card : Fintype.card (Fin n₀) ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective funF inj
    simp only [Fintype.card_fin] at h_card
    exact h_card
  exact this

abbrev FlagVector (σ : FlagType (Fin n₀)) : Type
  := FinFlag σ →₀ ℝ

@[simp]
lemma rat_smul_eq_real_smul
    (a : ℚ) (f : FlagVector σ) : a • f = (a : ℝ) • f
  := rfl

noncomputable instance : AddCommMonoid (FlagVector σ)
  := Finsupp.instAddCommMonoid

noncomputable instance : AddCommGroup (FlagVector σ)
  := Finsupp.instAddCommGroup

noncomputable instance : Module ℝ (FlagVector σ)
  := Finsupp.module (FinFlag σ) ℝ

noncomputable def unitVector (F : FinFlag σ) : FlagVector σ
  := Finsupp.single F 1

@[simp]
theorem unitVector_apply_self
    (F : FinFlag σ)
    : (unitVector F) F = 1
  := by
  simp [unitVector]

@[simp]
theorem unitVector_support
    (F : FinFlag σ)
    : (unitVector F).support = {F}
  := by
  dsimp [unitVector]
  rw [Finsupp.support_single_ne_zero _ (by simp)]

theorem flagVector_eq_sum_unitVector
    (f : FlagVector σ)
    : f = ∑ F in f.support, f F • unitVector F
  := by
  dsimp [unitVector]
  rw [← Finsupp.sum_single f]
  apply sum_congr (by simp)
  intros; simp

noncomputable instance : One (FlagVector σ) where
  one := unitVector 1

@[simp]
theorem flagVector_one_support
    : (1 : FlagVector σ).support = {(1 : FinFlag σ)}
  := by
  show (unitVector 1).support = {(1 : FinFlag σ)}
  simp

@[simp]
theorem flagVector_one_apply_one
    : (1 : FlagVector σ) 1 = 1
  := by
  show (unitVector 1) 1 = 1
  simp

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

theorem flagMulWithSize_one
    (F : FinFlag σ) : flagMulWithSize F 1 F.1 = unitVector F
  := by
  classical
  dsimp [flagMulWithSize]
  rw [finFlag_one_snd]
  have h_univ_split : univ = insert F.2 (univ.erase F.2) := Eq.symm (insert_erase (by simp))
  rw [h_univ_split, sum_insert (not_mem_erase _ _)]
  rw [flagPairDensity_empty', flagDensity_self, ← add_zero (unitVector F)]
  congr
  · simp
  · apply sum_eq_zero
    intro F' hF'
    rw [flagPairDensity_empty']
    have hF'_ne_F : F.2 ≠ F' := by
      simp_all only [mem_univ, insert_erase, mem_erase, ne_eq, and_true]
      exact fun a ↦ hF' (id (Eq.symm a))
    simp [flagDensity_other hF'_ne_F]

noncomputable def flagMul
    (F F' : FinFlag σ) : FlagVector σ
  :=
  flagMulWithSize F F' (F.1 + F'.1 - n₀)

theorem flagMul_comm
    (F F' : FinFlag σ) : flagMul F F' = flagMul F' F
  := by
  simp [flagMul, add_comm, flagMulWithSize_comm]

theorem flagMul_one
    (F : FinFlag σ) : flagMul F 1 = unitVector F
  := by
  dsimp [flagMul]
  rw [finFlag_one_fst, ← Nat.eq_sub_of_add_eq rfl]
  exact flagMulWithSize_one F

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

noncomputable instance : CommMagma (FlagVector σ) where
  mul_comm := flagVector_mul_comm

theorem flagVector_smul_assoc
    (r : ℝ) (f g : FlagVector σ) : (r • f) * g = r • (f * g)
  := by
  simp [flagVector_mul_def]
  by_cases hr : r = 0
  · simp [hr]
  · have hf_supp : (r • f).support = f.support := Finsupp.support_smul_eq hr
    rw [hf_supp]
    repeat (rw [smul_sum]; congr; apply funext; intro)
    simp [smul_mul_assoc, mul_assoc, smul_smul]

instance : IsScalarTower ℝ (FlagVector σ) (FlagVector σ) where
  smul_assoc := flagVector_smul_assoc

theorem flagVector_neg_mul
    (f g : FlagVector σ) : -f * g = -(f * g)
  := by
  show ∑ F in (-f).support, ∑ G in g.support, _ = -∑ F in f.support, ∑ G in g.support, _
  simp [flagVector_mul_def]

noncomputable instance : HasDistribNeg (FlagVector σ) where
  neg_mul := flagVector_neg_mul
  mul_neg f g := by
    rw [mul_comm f (-g), mul_comm f g, flagVector_neg_mul g f]

lemma flagVector_add_support
    (f g : FlagVector σ) {α : Type} [AddCommGroup α] (ψ : FlagVector σ → FinFlag σ → α)
    (hψ1 : ∀ f g x, f x + g x = 0 → ψ f x + ψ g x = 0)
    (hψ2 : ∀ f x, f x = 0 -> ψ f x = 0)
    : ∑ K ∈ (f + g).support, (ψ f K + ψ g K) =
        ∑ F ∈ f.support, ψ f F + ∑ G ∈ g.support, ψ g G
  := by
  classical
  have add_support_sub : (f + g).support ⊆ f.support ∪ g.support := Finsupp.support_add
  have sum_decomposition : ∑ x ∈ (f + g).support, (ψ f x + ψ g x) =
  ∑ x ∈ f.support ∪ g.support, (ψ f x + ψ g x) - ∑ x ∈ (f.support ∪ g.support) \ (f + g).support, (ψ f x + ψ g x) := by
    rw [sum_sdiff_eq_sub add_support_sub]
    exact
      Eq.symm
        (sub_sub_self (∑ x ∈ f.support ∪ g.support, (ψ f x + ψ g x))
          (∑ x ∈ (f + g).support, (ψ f x + ψ g x)))
  have sum_extra_eq_0 : ∑ x ∈ (f.support ∪ g.support) \ (f + g).support, (ψ f x + ψ g x) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff] at hx
    obtain ⟨h_in_union, h_not_in_sum⟩ := hx
    rw [Finsupp.not_mem_support_iff, Finsupp.add_apply] at h_not_in_sum
    rw [←union_sdiff_self_eq_union, mem_union] at h_in_union
    exact hψ1 f g x h_not_in_sum
  rw [sum_decomposition, sum_extra_eq_0, sub_zero]
  have disjoint_1 : Disjoint f.support (g.support \ f.support) := disjoint_sdiff
  have disjoint_2 : Disjoint (f.support \ g.support) (f.support ∩ g.support) := disjoint_sdiff_inter f.support g.support
  have disjoint_3 : Disjoint (f.support ∩ g.support) (g.support \ f.support)  := by
    rw [inter_comm]; symm
    exact disjoint_sdiff_inter g.support f.support
  have decomposition : ∑ x ∈ f.support ∪ g.support, (ψ f x + ψ g x) = ∑ x ∈ f.support \ g.support ∪ f.support ∩ g.support, (ψ f x + ψ g x) + ∑ x ∈ g.support \ f.support, (ψ f x + ψ g x) := by
    rw [←union_sdiff_self_eq_union]
    rw [sdiff_union_inter f.support g.support]
    exact sum_union disjoint_1
  rw [decomposition, sum_union disjoint_2, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have sum_not_g_supp_eq_0 : ∑ x ∈ f.support \ g.support, ψ g x = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff, Finsupp.not_mem_support_iff] at hx
    apply hψ2
    exact hx.2
  have sum_not_f_supp_eq_0 : ∑ x ∈ g.support \ f.support, ψ f x = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff, Finsupp.not_mem_support_iff] at hx
    apply hψ2
    exact hx.2
  rw [sum_not_g_supp_eq_0, sum_not_f_supp_eq_0, add_zero, zero_add]
  rw [add_assoc, add_assoc, ← sum_union disjoint_3, union_comm, inter_comm, sdiff_union_inter g.support f.support]
  rw [←add_assoc, inter_comm, ← sum_union disjoint_2, sdiff_union_inter f.support g.support]

theorem flagVector_left_distrib
    (f g h : FlagVector σ) : f * (g + h) = f * g + f * h
  := by
  show ∑ F in f.support, ∑ K in (g + h).support, _ = ∑ F in f.support, ∑ G in g.support, _ + ∑ F in f.support, ∑ H in h.support, _
  simp [Finset.sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro F _
  simp [mul_add, add_smul]
  let ψ : (FlagVector σ) → (FinFlag σ) → (FlagVector σ)
    := fun g G => (f F * g G) • flagMul F G
  have hψ1 : ∀ (g h : FlagVector σ) (x : FinFlag σ), g x + h x = 0 → ψ g x + ψ h x = 0 := by
    intro g' h' x hx
    simp [ψ]
    rw [add_eq_zero_iff_neg_eq] at hx
    rw [← hx]
    simp
  have hψ2 : ∀ (g : FlagVector σ) (x : FinFlag σ), g x = 0 → ψ g x = 0 := by
    intro g x hx
    simp [ψ]
    left; right
    exact hx
  apply flagVector_add_support g h ψ hψ1 hψ2

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

theorem flagVector_mul_one
    (f : FlagVector σ) : f * 1 = f
  := by
  rw [flagVector_eq_sum_unitVector f, sum_mul]
  apply sum_congr rfl
  intro G _
  rw [smul_mul_assoc]; congr
  dsimp [flagVector_mul_def]
  simp [flagMul_one]

noncomputable instance : MulOneClass (FlagVector σ) where
  one_mul g := by
    rw [mul_comm, flagVector_mul_one]
  mul_one := flagVector_mul_one

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

theorem flag_mul_zeroElement
    (F G: FinFlag σ) (ℓ : ℕ) (hℓ : G.1 ≤ ℓ) : (unitVector F) * (zeroElement G ℓ) ∈ ZeroSpace σ
  := by
  sorry

theorem zeroSpace_eq_sum_spanElement
    (k : FlagVector σ) (h_zero : k ∈ ZeroSpace σ)
    : ∃ (I : Type) (hI : Fintype I) (c : I → ℝ) (v : I → FlagVector σ),
      (∀ i, v i ∈ zeroSet σ) ∧ (k = ∑ i, c i • v i)
  := by
  revert h_zero
  apply Submodule.span_induction'
  · intro k h_zero
    use PUnit; use inferInstance
    use fun _ ↦ 1; use fun _ ↦ k
    simp_all only [mem_zeroSet, implies_true, univ_unique, PUnit.default_eq_unit, one_smul, sum_const,
      card_singleton, and_self]
  · use Empty; use inferInstance
    use fun _ ↦ 0; use fun _ ↦ 0
    simp
  · intro x hx y hy hx_ind hy_ind
    rcases hx_ind with ⟨I, hI, c, v, hv, hx⟩
    rcases hy_ind with ⟨J, hJ, d, w, hw, hy⟩
    use Sum I J; use inferInstance
    use Sum.elim c d; use Sum.elim v w
    subst hy hx
    simp_all only [mem_zeroSet, Sum.forall, Sum.elim_inl, implies_true, Sum.elim_inr, and_self,
      Fintype.sum_sum_type]
  · intro r x hx hx_ind
    rcases hx_ind with ⟨I, hI, c, v, hv, hx⟩
    use I; use hI; use fun i ↦ r * c i; use fun i ↦ v i
    constructor
    · intro i
      subst hx
      simp_all only [mem_zeroSet]
    · rw [hx, smul_sum]
      apply sum_congr (by rfl)
      intro i _
      rw [smul_smul]

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

lemma zeroSpace_closed_under_smul
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
  := by
  dsimp [flagVectorEqv]
  rw [sub_self]
  apply Submodule.zero_mem

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
    apply zeroSpace_closed_under_smul
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
  := by
  rw [flagVector_eq_sum_unitVector f, sum_mul]
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
  := by
  by_cases hab : a = 0 ∨ b = 0
  · cases' hab with ha hb
    · simp [ha, zero_mul, zero_smul]
    · simp [hb, zero_mul, zero_smul]
  · push_neg at hab
    obtain ⟨ha, hb⟩ := hab
    show ∑ F in (a • f).support, ∑ G in (b • g).support, _ = (a * b) • ∑ F in _, ∑ G in _, _
    rw [Finsupp.support_smul_eq ha, Finsupp.support_smul_eq hb]
    repeat (rw [smul_sum]; apply sum_congr (by rfl); intros)
    simp [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    congr 1; ring

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
  out := by
    intro one_eq_zero
    have h_one_zeroSet : (1 : FlagVector σ) ∈ ZeroSpace σ := by
      rw [← sub_zero 1]
      exact Quotient.exact one_eq_zero
    have zeroSet_decomp := zeroSpace_eq_sum_spanElement 1 h_one_zeroSet
    rcases zeroSet_decomp with ⟨I, hI, c, v, hv, hx⟩
    have zeroElem_exists : ∀ (i : I), ∃ (G : FinFlag σ) (ℓ : ℕ), G.1 ≤ ℓ ∧ v i = zeroElement G ℓ := by
      intro t; exact hv t
    choose G ℓ hG using zeroElem_exists
    let L := max (Finset.sup (univ : Finset I) ℓ) n₀
    have hL : L ≥ n₀ := le_max_right _ _
    let F := (flagWithSize_inhabited σ hL).default
    let φ : FlagVector σ → ℝ
      := fun g => ∑ G in g.support, (g G) * flagDensity₁ G.2 F
    have φ_add : ∀ (g h : FlagVector σ), φ (g + h) = φ g + φ h := by
      intro g h
      simp [φ, add_mul]
      let ψ : FlagVector σ → FinFlag σ → ℝ
        := fun g G => (g G) * flagDensity₁ G.2 F
      have hψ1 : ∀ (g h : FlagVector σ) (x : FinFlag σ), g x + h x = 0 → ψ g x + ψ h x = 0 := by
        intro g' h' x hx
        simp [ψ]
        rw [add_eq_zero_iff_neg_eq] at hx
        rw [← hx]
        simp only [neg_mul, add_neg_cancel]
      have hψ2 : ∀ (g : FlagVector σ) (x : FinFlag σ), g x = 0 → ψ g x = 0 := by
        intro g' x hx
        simp [ψ]
        exact Or.symm (Or.inr hx)
      apply flagVector_add_support g h ψ hψ1 hψ2
    have φ_smul : ∀ (r : ℝ) (g : FlagVector σ), φ (r • g) = r * φ g := by
      intro r g
      show ∑ G in _, _ = _ * ∑ G in _, _
      by_cases hr : r = 0
      · simp [hr]
      · have hg_supp : (r • g).support = g.support := Finsupp.support_smul_eq hr
        rw [hg_supp, mul_sum]
        apply sum_congr (by rfl)
        intro x _
        simp [mul_sum, mul_assoc]
    have φ_sum : ∀ (s : Finset I) (f : I → FlagVector σ), φ (∑ i in s, f i) = ∑ i in s, φ (f i) := by
      intro s f
      show ∑ G in _, _ = ∑ i in _, _
      classical
      refine Finset.induction_on s ?_ ?_
      · simp [φ]
      · intro r R hr ih
        simp [sum_insert hr, Module.add_smul]
        simp_all only [Finsupp.coe_add, Pi.add_apply, φ]
    have hφ : ∀ (i : I), φ (v i) = 0 := by
      intro i
      let iG := G i
      have ⟨hℓ', hG2⟩ : iG.fst ≤ ℓ i ∧ v i = zeroElement iG (ℓ i) := by apply hG
      have hℓ : ℓ i ≤ L := by
        simp [L, le_max_iff]; left
        apply Finset.le_sup; simp
      have φ_sum' : ∀ (s : Finset (FlagWithSize σ (ℓ i))) (f : FlagWithSize σ (ℓ i) → FlagVector σ), φ (∑ i in s, f i) = ∑ i in s, φ (f i) := by
        intro s f
        classical
        refine Finset.induction_on s ?_ ?_
        · simp [φ]
        · intro r R hr ih
          simp [sum_insert hr, Module.add_smul]
          simp_all only [Finsupp.coe_add, Pi.add_apply, φ]
      rw [hG2]
      dsimp [zeroElement]
      rw [sub_eq_add_neg, φ_add]
      have : φ (-densityFlagSum iG (ℓ i)) = -φ (densityFlagSum iG (ℓ i)) := by
        simp_all only [Finsupp.support_neg, Finsupp.coe_neg, Pi.neg_apply, neg_mul, sum_neg_distrib, φ]
      rw [this, ← sub_eq_add_neg, sub_eq_zero]
      dsimp [densityFlagSum]
      rw [φ_sum']
      have : φ (unitVector iG) = flagDensity₁ iG.2 F := by
        simp_all only [unitVector_support, sum_singleton, unitVector_apply_self, one_mul, φ]
      have hℓ'' : n₀ ≤ iG.fst := finFlag_size_ge_n₀ iG
      rw [this, density_chain_rule₁₁ (ℓ i) iG.2 F hℓ'' hℓ' hℓ]
      simp
      dsimp [FlagWithSize]
      apply sum_congr (by rfl)
      intro x
      rw [φ_smul]
      simp
      by_cases s : flagDensity₁ iG.2 x = 0
      · right; exact s
      · left
        dsimp [φ]
        simp
    have h_φ_1 : φ 1 = 1 := by
      show ∑ G in (unitVector 1).support, _ = 1
      simp [sum_singleton, flagDensity_one]
    have h_φ_sum : φ (∑ i, c i • v i) = 0 := by
      simp_all only [mul_zero, sum_const_zero, zero_ne_one]
    rw [hx] at h_φ_1
    have zero_eq_one : (0 : ℝ) = (1 : ℝ) := by rw [←h_φ_1, ←h_φ_sum]
    exact zero_ne_one zero_eq_one

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
