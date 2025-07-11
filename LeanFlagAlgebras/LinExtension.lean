import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

open Finset

variable {α β : Type} [AddCommGroup β] [Module ℝ β]

def linearExtension
    (f : α → β)
    : (α →₀ ℝ) → β
  :=
  fun v => ∑ a in v.support, (v a) • (f a)

theorem linearExtension_zero
    (f : α → β)
    : linearExtension f 0 = 0 := by
  simp only [linearExtension, Finsupp.support_zero, Finset.sum_empty]

omit [Module ℝ β] in
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
        rw [Finsupp.not_mem_support_iff, Finsupp.add_apply] at h_not_in_sum
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
        rw [mem_sdiff, Finsupp.not_mem_support_iff] at ha
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
    _ = ∑ a in (v + w).support, (ψ v a + ψ w a) := by
      apply sum_congr rfl
      intro a _
      dsimp [ψ]
      rw [add_smul]
    _ = ∑ a in v.support, ψ v a + ∑ a in w.support, ψ w a :=
      linearExtension_add_support v w ψ hψ₁ hψ₂

theorem linearExtension_sum
    (f : α → β) (s : Finset ι) (c : ι → (α →₀ ℝ))
    : linearExtension f (∑ i in s, c i) = ∑ i in s, linearExtension f (c i)
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
