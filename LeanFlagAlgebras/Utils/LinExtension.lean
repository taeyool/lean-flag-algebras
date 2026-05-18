import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic

/-! # Linear and bilinear extensions of maps on a basis

Shared utility for extending a map `f : α → β` (resp. `f : α → α → β`) to a linear map
`(α →₀ ℝ) → β` (resp. bilinear `(α →₀ ℝ) → (α →₀ ℝ) → β`) on the free `ℝ`-vector space on `α`,
plus their additivity / scaling / sum lemmas. Used to turn formal flag combinations into
their evaluated densities throughout the flag-algebra development.
-/

open Finset

variable {α β : Type} [AddCommGroup β] [Module ℝ β]

/- Linear Extension -/

/-! ## Linear extension -/

/-- The linear extension of `f : α → β` to `α →₀ ℝ`: `v ↦ ∑ a ∈ v.support, v a • f a`. -/
def linearExtension
    (f : α → β)
    : (α →₀ ℝ) → β
  :=
  fun v => ∑ a ∈ v.support, (v a) • (f a)

theorem linearExtension_zero
    (f : α → β)
    : linearExtension f 0 = 0
  := by
  simp only [linearExtension, Finsupp.support_zero, Finset.sum_empty]

theorem linearExtension_single_one
    (f : α → β) (a : α)
    : linearExtension f (Finsupp.single a 1) = f a
  := by
  classical
  dsimp [linearExtension]
  rw [Finsupp.support_single_ne_zero a one_ne_zero, Finset.sum_singleton, Finsupp.single_apply]
  simp only [↓reduceIte, one_smul]

omit [Module ℝ β] in
/-- Generic support-splitting lemma underlying `linearExtension_add`: a sum over the support of
`v + w` of `ψ v a + ψ w a` splits into separate sums over the supports of `v` and `w`,
given that `ψ` vanishes off-support and is additive where coefficients cancel. -/
lemma linearExtension_add_support
    (v w : α →₀ ℝ) (ψ : (α →₀ ℝ) → α → β)
    (hψ₁ : ∀ v w a, v a + w a = 0 → ψ v a + ψ w a = 0)
    (hψ₂ : ∀ v a, v a = 0 → ψ v a = 0)
    : ∑ a ∈ (v + w).support, (ψ v a + ψ w a) =
        ∑ a ∈ v.support, ψ v a + ∑ a ∈ w.support, ψ w a
  := by
  classical
  have add_support_sub : (v + w).support ⊆ v.support ∪ w.support := Finsupp.support_add
  have disjoint₁ : Disjoint v.support (w.support \ v.support) := disjoint_sdiff
  have disjoint₂ : Disjoint (v.support \ w.support) (v.support ∩ w.support) := disjoint_sdiff_inter v.support w.support
  calc
    _ = ∑ a ∈ v.support ∪ w.support, (ψ v a + ψ w a) -
        ∑ a ∈ (v.support ∪ w.support) \ (v + w).support, (ψ v a + ψ w a) := by
      rw [sum_sdiff_eq_sub add_support_sub]
      simp only [sub_sub_self]
    _ = ∑ a ∈ v.support ∪ w.support, (ψ v a + ψ w a) := by
      have sum_extra_eq_0 : ∑ a ∈ (v.support ∪ w.support) \ (v + w).support, (ψ v a + ψ w a) = 0 := by
        apply sum_eq_zero
        intro a ha
        rw [mem_sdiff] at ha
        obtain ⟨h_in_union, h_not_in_sum⟩ := ha
        rw [Finsupp.notMem_support_iff, Finsupp.add_apply] at h_not_in_sum
        rw [← union_sdiff_self_eq_union, mem_union] at h_in_union
        exact hψ₁ v w a h_not_in_sum
      exact sub_eq_self.mpr sum_extra_eq_0
    _ = ∑ a ∈ v.support \ w.support ∪ v.support ∩ w.support,
        (ψ v a + ψ w a) + ∑ a ∈ w.support \ v.support, (ψ v a + ψ w a) := by
      rw [← union_sdiff_self_eq_union, sdiff_union_inter, sum_union disjoint₁]
    _ = (∑ x ∈ v.support \ w.support, ψ v x + ∑ x ∈ v.support ∩ w.support, ψ v x) +
        (∑ x ∈ w.support \ v.support, ψ w x + ∑ x ∈ v.support ∩ w.support, ψ w x) := by
      rw [sum_union disjoint₂, sum_add_distrib, sum_add_distrib, sum_add_distrib]
      have sum_not_supp_eq_0 : ∀ (v w : α →₀ ℝ), ∑ a ∈ v.support \ w.support, ψ w a = 0 := by
        intro v w
        apply sum_eq_zero
        intro a ha
        rw [mem_sdiff, Finsupp.notMem_support_iff] at ha
        apply hψ₂ _ _ ha.2
      rw [sum_not_supp_eq_0 v w, sum_not_supp_eq_0 w v, add_zero, zero_add]
      rw [add_comm (∑ x ∈ w.support \ v.support, ψ w x)]
      simp only [add_assoc]
    _ = ∑ a ∈ v.support, ψ v a + ∑ a ∈ w.support, ψ w a := by
      have sum_supp_sdiff_inter : ∀ (v w : α →₀ ℝ), ∑ x ∈ v.support \ w.support, ψ v x + ∑ x ∈ v.support ∩ w.support, ψ v x = ∑ x ∈ v.support, ψ v x := by
        intro v w
        rw [← sum_union (disjoint_sdiff_inter v.support w.support)]
        congr
        exact sdiff_union_inter v.support w.support
      rw [sum_supp_sdiff_inter v w, inter_comm, sum_supp_sdiff_inter w v]

/-- `linearExtension f` is additive. -/
theorem linearExtension_add
    (f : α → β) (v w : α →₀ ℝ)
    : linearExtension f (v + w) = linearExtension f v + linearExtension f w := by
  dsimp [linearExtension]
  let ψ : (α →₀ ℝ) → α → β := fun v a => (v a) • (f a)
  have hψ₁ : ∀ v w a, v a + w a = 0 → ψ v a + ψ w a = 0 := by
    intro v' w' a ha
    dsimp [ψ]
    rw [← add_smul, ha, zero_smul]
  have hψ₂ : ∀ v a, v a = 0 → ψ v a = 0 := by
    intro v a ha
    dsimp [ψ]
    rw [ha, zero_smul]
  calc
    _ = ∑ a ∈ (v + w).support, (ψ v a + ψ w a) := by
      apply sum_congr rfl
      intro a _
      dsimp [ψ]
      rw [add_smul]
    _ = ∑ a ∈ v.support, ψ v a + ∑ a ∈ w.support, ψ w a :=
      linearExtension_add_support v w ψ hψ₁ hψ₂

/-- `linearExtension f` commutes with finite sums. -/
theorem linearExtension_sum
    (f : α → β) (s : Finset ι) (c : ι → (α →₀ ℝ))
    : linearExtension f (∑ i ∈ s, c i) = ∑ i ∈ s, linearExtension f (c i)
  := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, linearExtension_zero]
  · intro i s his ih
    simp only [Finset.sum_insert his, linearExtension_add, ih]

theorem linearExtension_neg
    (f : α → β) (v : α →₀ ℝ)
    : linearExtension f (-v) = -linearExtension f v := by
  dsimp [linearExtension]
  simp only [Finsupp.support_neg, neg_smul, Finset.sum_neg_distrib]

theorem linearExtension_sub
    (f : α → β) (v w : α →₀ ℝ)
    : linearExtension f (v - w) = linearExtension f v - linearExtension f w := by
  simp only [sub_eq_add_neg, linearExtension_add, linearExtension_neg]

/-- `linearExtension f` is `ℝ`-homogeneous. -/
theorem linearExtension_smul
    (f : α → β) (r : ℝ) (v : α →₀ ℝ)
    : linearExtension f (r • v) = r • linearExtension f v := by
  dsimp [linearExtension]
  by_cases hr : r = 0
  · simp only [hr, zero_smul, zero_mul, Finset.sum_const_zero]
  · rw [Finsupp.support_smul_eq hr, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_smul r (v a) (f a)


/- Bilinear Extension -/

/-! ## Bilinear extension -/

/-- The bilinear extension of `f : α → α → β`, extending first in the right argument
then the left. Equal to `bilinearExtension'` (see `bilinearExtension_def_eq`). -/
def bilinearExtension
    (f : α → α → β)
    : (α →₀ ℝ) → (α →₀ ℝ) → β
  :=
  fun v w => linearExtension (flip (fun a => linearExtension (f a)) w) v

/-- Alternative bilinear extension of `f`, extending first in the left argument
then the right; provably equal to `bilinearExtension` via `bilinearExtension_def_eq`. -/
def bilinearExtension'
    (f : α → α → β)
    : (α →₀ ℝ) → (α →₀ ℝ) → β
  :=
  fun v w => linearExtension (fun b => linearExtension (flip f b) v) w

/-- Expands `bilinearExtension f v w` as the double sum `∑ₐ ∑_b (v a * w b) • f a b`. -/
theorem bilinearExtension_eq_nested_sum
    (f : α → α → β) (v w : α →₀ ℝ)
    : bilinearExtension f v w = ∑ a ∈ v.support, ∑ b ∈ w.support, ((v a) * (w b)) • f a b := by
  dsimp [bilinearExtension, linearExtension]
  apply Finset.sum_congr rfl
  intro a _
  rw [flip, linearExtension, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact smul_smul (v a) (w b) (f a b)

theorem bilinearExtension'_eq_nested_sum
    (f : α → α → β) (v w : α →₀ ℝ)
    : bilinearExtension' f v w = ∑ a ∈ v.support, ∑ b ∈ w.support, ((v a) * (w b)) • f a b := by
  dsimp [bilinearExtension', linearExtension]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [flip, smul_smul, mul_comm]

/-- The two extension orders agree: `bilinearExtension f = bilinearExtension' f`. -/
theorem bilinearExtension_def_eq
    (f : α → α → β) (v w : α →₀ ℝ)
    : bilinearExtension f v w = bilinearExtension' f v w := by
  simp only [bilinearExtension_eq_nested_sum, bilinearExtension'_eq_nested_sum]

theorem bilinearExtension_zero_left
    (f : α → α → β) (w : α →₀ ℝ)
    : bilinearExtension f 0 w = 0 := by
  simp only [bilinearExtension, linearExtension_zero]

theorem bilinearExtension_zero_right
    (f : α → α → β) (v : α →₀ ℝ)
    : bilinearExtension f v 0 = 0 := by
  rw [bilinearExtension_def_eq]
  simp only [bilinearExtension', linearExtension_zero]

theorem bilinearExtension_add_left
    (f : α → α → β) (v v' : α →₀ ℝ) (w : α →₀ ℝ)
    : bilinearExtension f (v + v') w = bilinearExtension f v w + bilinearExtension f v' w := by
  simp only [bilinearExtension, linearExtension_add]

theorem bilinearExtension_add_right
    (f : α → α → β) (v : α →₀ ℝ) (w w' : α →₀ ℝ)
    : bilinearExtension f v (w + w') = bilinearExtension f v w + bilinearExtension f v w' := by
  repeat rw [bilinearExtension_def_eq]
  simp only [bilinearExtension', linearExtension_add]

theorem bilinearExtension_sum_left
    (f : α → α → β) (s : Finset ι) (c : ι → (α →₀ ℝ)) (w : α →₀ ℝ)
    : bilinearExtension f (∑ i ∈ s, c i) w = ∑ i ∈ s, bilinearExtension f (c i) w := by
  simp only [bilinearExtension, linearExtension_sum]

theorem bilinearExtension_sum_right
    (f : α → α → β) (v : α →₀ ℝ) (s : Finset ι) (c : ι → (α →₀ ℝ))
    : bilinearExtension f v (∑ i ∈ s, c i) = ∑ i ∈ s, bilinearExtension f v (c i) := by
  repeat simp_rw [bilinearExtension_def_eq]
  simp only [bilinearExtension', linearExtension_sum]

theorem bilinearExtension_neg_left
    (f : α → α → β) (v : α →₀ ℝ) (w : α →₀ ℝ)
    : bilinearExtension f (-v) w = -bilinearExtension f v w := by
  simp only [bilinearExtension, linearExtension_neg]

theorem bilinearExtension_neg_right
    (f : α → α → β) (v : α →₀ ℝ) (w : α →₀ ℝ)
    : bilinearExtension f v (-w) = -bilinearExtension f v w := by
  repeat rw [bilinearExtension_def_eq]
  simp only [bilinearExtension', linearExtension_neg]

theorem bilinearExtension_sub_left
    (f : α → α → β) (v v' : α →₀ ℝ) (w : α →₀ ℝ)
    : bilinearExtension f (v - v') w = bilinearExtension f v w - bilinearExtension f v' w := by
  simp only [bilinearExtension, linearExtension_sub]

theorem bilinearExtension_sub_right
    (f : α → α → β) (v : α →₀ ℝ) (w w' : α →₀ ℝ)
    : bilinearExtension f v (w - w') = bilinearExtension f v w - bilinearExtension f v w' := by
  repeat rw [bilinearExtension_def_eq]
  simp only [bilinearExtension', linearExtension_sub]

theorem bilinearExtension_smul_left
    (f : α → α → β) (r : ℝ) (v : α →₀ ℝ) (w : α →₀ ℝ)
    : bilinearExtension f (r • v) w = r • bilinearExtension f v w := by
  simp only [bilinearExtension, linearExtension_smul]

theorem bilinearExtension_smul_right
    (f : α → α → β) (r : ℝ) (v : α →₀ ℝ) (w : α →₀ ℝ)
    : bilinearExtension f v (r • w) = r • bilinearExtension f v w := by
  repeat rw [bilinearExtension_def_eq]
  simp only [bilinearExtension', linearExtension_smul]
