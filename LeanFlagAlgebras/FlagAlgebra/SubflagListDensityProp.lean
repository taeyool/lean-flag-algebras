import «LeanFlagAlgebras».FlagAlgebra.SubflagListDensity
import «LeanFlagAlgebras».FlagAlgebra.FlagDef
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Vector.Basic
import Mathlib.Data.FinEnum

/-! # Asymptotic Independence of Subflag List Densities

This file proves the key probabilistic estimate underlying the
"product of densities" reasoning in flag algebras: in a large host flag `G`,
the joint density of finding two disjoint subflags `F`, `F'`
(`flagDensity₂`) differs from the product of their individual densities
(`flagDensity₁ F G * flagDensity₁ F' G`) by `O(1 / |G|)`. The single result,
`flagListDensity₂_prod_approx`, exhibits an explicit constant
`c = 2 (|F| + |F'|)²` independent of `G`. The proof models the choice of two
vertex subsets as a finite probability space `Ω`, with events `A` (each
subset induces a copy of the right flag) and `B` (the subsets are disjoint
off the type), and bounds the overlap-correction term combinatorially. Uses
`FlagAlgebra.SubflagListDensity` and `FlagAlgebra.FlagDef`; a commented-out
generalization to lists of `t` flags is sketched at the end. -/

namespace FlagAlgebras

open LabeledSubgraph
open Classical
open Finset
open MeasureTheory ProbabilityTheory

variable {T : Type} [Fintype T] [DecidableEq T]
variable {V : Type} [Fintype V] [DecidableEq V]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {U : Type} [Fintype U] [DecidableEq U]

variable {σ : FlagType T} {t : ℕ}
variable {Vl  : Fin t → Type} [FintypeList Vl]  [DecidableEqList Vl]
variable {Fl : FlagList σ t Vl}

set_option maxHeartbeats 500000
omit [DecidableEq T] in
/-- Asymptotic independence of two subflag densities: there is a constant
`c ≥ 0` (here `2 (|F| + |F'|)²`), independent of the host flag `G`, with
`|flagDensity₂ F F' G − flagDensity₁ F G · flagDensity₁ F' G| ≤ c / |G|`.
This justifies treating distinct flag densities as asymptotically
multiplicative in the flag-algebra density-bound arguments. -/
theorem flagListDensity₂_prod_approx
    (F : Flag σ V) (F' : Flag σ U)
    : ∃ c ≥ 0, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
    |flagDensity₂ F F' G - flagDensity₁ F G * flagDensity₁ F' G| ≤ c / G.out.size
  := by
  use 2 * (F.out.size + F'.out.size) ^ 2
  constructor; (simp only [ge_iff_le, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sq_nonneg])
  intro W _ _ G
  let ⟨Grep, hGrep₁⟩ := Quotient.exists_rep G
  have hGrep₂ : (⟦Grep⟧ : Quotient (labeledGraphSetoid σ W)).out.size = Grep.size := rfl
  let ⟨Frep, hFrep₁⟩ := Quotient.exists_rep F
  have hFrep₂ : (⟦Frep⟧ : Quotient (labeledGraphSetoid σ V)).out.size = Frep.size := rfl
  let ⟨F'rep, hF'rep₁⟩ := Quotient.exists_rep F'
  have hF'rep₂ : (⟦F'rep⟧ : Quotient (labeledGraphSetoid σ U)).out.size = F'rep.size := rfl
  dsimp only [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F G, ← subflagDensity_eq_flagListDensity F' G]
  rw [← hFrep₁, hFrep₂, ← hF'rep₁, hF'rep₂, ← hGrep₁, hGrep₂, ← labeledGraphListDensity_eq_flagDensity₂ Frep F'rep Grep]
  dsimp only [subflagDensity, Quotient.lift_mk, labeledGraphDensityLifted]

  let freeG := Finset.univ \ Grep.type_verts.toFinset
  have hfreeG_size : freeG.card = Grep.size - σ.size := by
    simp_all only [freeG]
    rw [← Grep.type_verts_card_eq, Finset.card_sdiff]; try simp only [subset_univ]
    simp only [card_univ, inter_univ, Set.toFinset_card, LabeledGraph.size]
  let hfreeG_sub (w : Finset W) : w ⊆ freeG → Disjoint w Grep.type_verts.toFinset := by
    intro h_sub
    refine disjoint_iff_inter_eq_empty.mpr ?_
    ext x; simp only [mem_inter, Set.mem_toFinset, notMem_empty, iff_false, not_and]
    intro hx
    have hx_in_freeG := h_sub hx
    simp_all only [mem_sdiff, Set.mem_toFinset, not_false_eq_true, freeG]
  let freeF := Finset.univ \ Frep.type_verts.toFinset
  have hfreeF_size : freeF.card = Frep.size - σ.size := by
    simp_all only [freeF]
    rw [← Frep.type_verts_card_eq, Finset.card_sdiff]; try simp only [subset_univ]
    simp only [card_univ, inter_univ, Set.toFinset_card, LabeledGraph.size]
  let freeF' := Finset.univ \ F'rep.type_verts.toFinset
  have hfreeF'_size : freeF'.card = F'rep.size - σ.size := by
    simp_all only [freeF']
    rw [← F'rep.type_verts_card_eq, Finset.card_sdiff]; try simp only [subset_univ]
    simp only [card_univ, inter_univ, Set.toFinset_card, LabeledGraph.size]

  let Ω := { (w₁, w₂) : Finset W × Finset W | (w₁.card = Frep.size ∧ Grep.type_verts ⊆ w₁) ∧ (w₂.card = F'rep.size ∧ Grep.type_verts ⊆ w₂)}
  have hΩ_size : Ω.toFinset.card = (freeG.card).choose freeF.card * (freeG.card).choose freeF'.card := by
    rw [← combinations_card freeG freeF.card, ← combinations_card freeG freeF'.card, ← Finset.card_product, eq_comm]
    simp only [Set.toFinset_card, Fintype.card_ofFinset]
    apply Finset.card_eq_of_equiv
    refine Equiv.ofBijective ?_ ?_
    · intro ⟨⟨w₁, w₂⟩, hw⟩
      use (w₁ ∪ Grep.type_verts.toFinset, w₂ ∪ Grep.type_verts.toFinset)
      simp only [mem_filter, mem_univ, Set.mem_setOf_eq, true_and, Ω, coe_union, Set.coe_toFinset, Set.subset_union_right, and_true]
      simp only [combinations, mem_product, mem_filter, mem_powerset] at hw
      obtain ⟨⟨hw₁_free, hw₁_size⟩, ⟨hw₂_free, hw₂_size⟩⟩ := hw
      constructor
      · rw [card_union_eq_card_add_card.mpr (hfreeG_sub w₁ hw₁_free), hw₁_size, hfreeF_size]
        rw [Set.toFinset_card, Grep.type_verts_card_eq]
        exact Nat.sub_add_cancel Frep.type_size_le_size
      · rw [card_union_eq_card_add_card.mpr (hfreeG_sub w₂ hw₂_free), hw₂_size, hfreeF'_size]
        rw [Set.toFinset_card, Grep.type_verts_card_eq]
        exact Nat.sub_add_cancel F'rep.type_size_le_size
    · constructor
      · intro ⟨⟨w₁, w₂⟩, hw⟩ ⟨⟨w'₁, w'₂⟩, hw'⟩ h_eq
        simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
        simp only [combinations, mem_product, mem_filter, mem_powerset] at hw hw'
        obtain ⟨⟨hw₁_free, _⟩, ⟨hw₂_free, _⟩⟩ := hw
        obtain ⟨⟨hw'₁_free, _⟩, ⟨hw'₂_free, _⟩⟩ := hw'
        rw [← union_sdiff_cancel_right (hfreeG_sub w₁ hw₁_free), ← union_sdiff_cancel_right (hfreeG_sub w'₁ hw'₁_free), h_eq.1]
        rw [← union_sdiff_cancel_right (hfreeG_sub w₂ hw₂_free), ← union_sdiff_cancel_right (hfreeG_sub w'₂ hw'₂_free), h_eq.2]
        simp only [and_self]
      · intro ⟨⟨w₁, w₂⟩, hw⟩
        simp only [mem_filter, mem_univ, Set.mem_setOf_eq, true_and, Ω] at hw
        obtain ⟨⟨hw₁_size, hw₁_tverts⟩, ⟨hw₂_size, hw₂_tverts⟩⟩ := hw
        let w := (w₁ \ Grep.type_verts.toFinset, w₂ \ Grep.type_verts.toFinset)
        have hw : w ∈ (combinations freeG freeF.card ×ˢ combinations freeG freeF'.card) := by
          simp only [combinations, mem_product, mem_filter, mem_powerset, freeG, freeF, freeF']
          constructor <;> constructor
          · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
            exact subset_univ w₁
          · rw [Finset.card_sdiff_of_subset, Set.toFinset_card]
            · rw [hw₁_size, hfreeF_size, ← Grep.type_verts_card_eq]
            · rwa [Set.toFinset_subset]
          · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
            exact subset_univ w₂
          · rw [Finset.card_sdiff_of_subset, Set.toFinset_card]
            · rw [hw₂_size, hfreeF'_size, ← Grep.type_verts_card_eq]
            · rwa [Set.toFinset_subset]
        use ⟨w, hw⟩
        simp_all only [sdiff_union_self_eq_union, Subtype.mk.injEq, Prod.mk.injEq, union_eq_left, Set.toFinset_subset, and_self, w]
  have hΩ_card_eq : (@univ (↑Ω) (Subtype.fintype (Membership.mem Ω))).card = Ω.toFinset.card := by simp only [card_univ, Fintype.card_ofFinset, Set.toFinset_card]
  let A : Finset Ω := { w | by
    obtain ⟨⟨w₁, w₂⟩, h⟩ := w
    exact Nonempty ((inducedLabeledSubgraph Grep w₁ h.1.2).coe ≃f Frep) ∧ Nonempty ((inducedLabeledSubgraph Grep w₂ h.2.2).coe ≃f F'rep) }
  let B : Finset Ω := { w | by
    obtain ⟨⟨w₁, w₂⟩, h⟩ := w
    exact (w₁ \ Grep.type_verts.toFinset) ∩ (w₂ \ Grep.type_verts.toFinset) = ∅ }
  let r_list : Fin 2 → ℕ := fun i ↦
    (match i with
      | 0 => Frep.size - σ.size
      | 1 => F'rep.size - σ.size)
  have hB_size : B.card = multinomialCoefficient r_list freeG.card := by
    rw [← partition_card freeG r_list]
    apply Finset.card_eq_of_equiv
    refine Equiv.ofBijective ?_ ?_
    · intro ⟨⟨⟨w₁, w₂⟩, h_in_Ω⟩, h_in_B⟩
      let r : Fin 2 → Finset W := fun i ↦
        (match i with
          | 0 => w₁ \ Grep.type_verts.toFinset
          | 1 => w₂ \ Grep.type_verts.toFinset)
      use r
      simp only [Set.mem_setOf_eq, Ω] at h_in_Ω
      simp only [mem_filter, mem_univ, true_and, B] at h_in_B
      simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter, true_and]
      constructor <;> try constructor
      · intro i
        by_cases hi : i = 0
        · simp only [hi, Fin.isValue, r, r_list]
          constructor
          · intro w hw
            simp_all only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, not_false_eq_true, freeG]
          · rw [Finset.card_sdiff_of_subset (by simp only [Set.toFinset_subset]; exact h_in_Ω.1.2)]
            rw [h_in_Ω.1.1, Set.toFinset_card, Grep.type_verts_card_eq]
        · simp only [Fin.eq_one_of_ne_zero i hi, Fin.isValue, r, r_list]
          constructor
          · intro w hw
            simp_all only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, not_false_eq_true, freeG]
          · rw [Finset.card_sdiff_of_subset (by simp only [Set.toFinset_subset]; exact h_in_Ω.2.2)]
            rw [h_in_Ω.2.1, Set.toFinset_card, Grep.type_verts_card_eq]
      · intro i j hij
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fin.isValue, not_true_eq_false]
        · simp_all only [Fin.isValue, Fin.eq_one_of_ne_zero j hj, disjoint_iff_inter_eq_empty, r]
        · rw [Finset.inter_comm] at h_in_B
          simp_all only [Fin.isValue, Fin.eq_one_of_ne_zero i hi, disjoint_iff_inter_eq_empty, r]
        · simp_all only [Fin.eq_one_of_ne_zero i hi, Fin.eq_one_of_ne_zero j hj, not_true_eq_false]
      · intro i
        by_cases hi : i = 0
        · simp only [hi, Fin.isValue, r]
          intro x hx
          simp_all only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, not_false_eq_true, freeG]
        · simp only [Fin.eq_one_of_ne_zero i hi, Fin.isValue, r]
          intro x hx
          simp_all only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, not_false_eq_true, freeG]
    · constructor
      · intro ⟨⟨⟨w₁, w₂⟩, hw_in_Ω⟩, _⟩ ⟨⟨⟨w'₁, w'₂⟩, hw'_in_Ω⟩, _⟩ h_eq
        simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
        simp only [Set.mem_setOf_eq, Ω] at hw_in_Ω hw'_in_Ω
        have hw₁ : w₁ ∩ Grep.type_verts.toFinset = Grep.type_verts.toFinset := by
          simp only [inter_eq_right, Set.toFinset_subset]
          exact hw_in_Ω.1.2
        have hw₂ : w₂ ∩ Grep.type_verts.toFinset = Grep.type_verts.toFinset := by
          simp only [inter_eq_right, Set.toFinset_subset]
          exact hw_in_Ω.2.2
        have hw'₁ : w'₁ ∩ Grep.type_verts.toFinset = Grep.type_verts.toFinset := by
          simp only [inter_eq_right, Set.toFinset_subset]
          exact hw'_in_Ω.1.2
        have hw'₂ : w'₂ ∩ Grep.type_verts.toFinset = Grep.type_verts.toFinset := by
          simp only [inter_eq_right, Set.toFinset_subset]
          exact hw'_in_Ω.2.2
        have h₁ := congrFun h_eq 0
        have h₂ := congrFun h_eq 1
        simp only at h₁ h₂
        rw [← sdiff_union_inter w₁ Grep.type_verts.toFinset, ← sdiff_union_inter w'₁ Grep.type_verts.toFinset, h₁, hw₁, hw'₁]
        rw [← sdiff_union_inter w₂ Grep.type_verts.toFinset, ← sdiff_union_inter w'₂ Grep.type_verts.toFinset, h₂, hw₂, hw'₂]
        simp only [sdiff_union_self_eq_union, and_self]
      · intro ⟨l, hl⟩
        simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter, true_and] at hl
        obtain ⟨hl, hl_disj, _⟩ := hl
        let w := (l 0 ∪ Grep.type_verts.toFinset, l 1 ∪ Grep.type_verts.toFinset)
        have hw_in_Ω : w ∈ Ω := by
          simp only [Fin.isValue, Set.mem_setOf_eq, coe_union, Set.coe_toFinset, Set.subset_union_right, and_true, Ω, w]
          constructor
          · rw [card_union_eq_card_add_card.mpr (hfreeG_sub (l 0) (hl 0).1), (hl 0).2]
            simp only [Fin.isValue, Set.toFinset_card, r_list]
            rw [Grep.type_verts_card_eq]
            exact Nat.sub_add_cancel Frep.type_size_le_size
          · rw [card_union_eq_card_add_card.mpr (hfreeG_sub (l 1) (hl 1).1), (hl 1).2]
            simp only [Fin.isValue, Set.toFinset_card, r_list]
            rw [Grep.type_verts_card_eq]
            exact Nat.sub_add_cancel F'rep.type_size_le_size
        have hw_in_B : ⟨w, hw_in_Ω⟩ ∈ B := by
          simp only [Fin.isValue, mem_filter, mem_univ, true_and, B, w]
          have hl0 : (l 0 ∪ Grep.type_verts.toFinset) \ Grep.type_verts.toFinset = l 0 := by
            refine union_sdiff_cancel_right ?_
            exact hfreeG_sub (l 0) (hl 0).1
          have hl1 : (l 1 ∪ Grep.type_verts.toFinset) \ Grep.type_verts.toFinset = l 1 := by
            refine union_sdiff_cancel_right ?_
            exact hfreeG_sub (l 1) (hl 1).1
          rw [hl0, hl1, ← disjoint_iff_inter_eq_empty]
          exact hl_disj 0 1 Fin.zero_ne_one
        use ⟨⟨w, hw_in_Ω⟩, hw_in_B⟩
        simp only [Subtype.mk.injEq]
        funext i
        by_cases hi : i = 0
        · simp only [hi, Fin.isValue, w]
          exact union_sdiff_cancel_right (hfreeG_sub (l 0) (hl 0).1)
        · simp only [Fin.eq_one_of_ne_zero i hi, Fin.isValue, w]
          exact union_sdiff_cancel_right (hfreeG_sub (l 1) (hl 1).1)

  have P₁ : labeledGraphDensity Frep Grep * labeledGraphDensity F'rep Grep = A.card / Ω.toFinset.card := by
    dsimp only [labeledGraphDensity]
    field_simp; congr
    · dsimp only [labeledGraphCount]
      rw [← Nat.cast_mul, Nat.cast_inj, ← Finset.card_product]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨⟨G₁, G₂⟩, hG⟩
        let W_G₁G₂ : Finset W × Finset W := (G₁.subgraph.verts.toFinset, G₂.subgraph.verts.toFinset)
        have hW_G₁G₂_in_Ω : W_G₁G₂ ∈ Ω := by
          simp only [Set.mem_setOf_eq, Ω, W_G₁G₂]
          simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and] at hG
          obtain ⟨⟨_, hG₁_iso⟩, ⟨_, hG₂_iso⟩⟩ := hG
          constructor <;> constructor
          · rw [← labeledGraphIso_size_eq G₁.coe Frep (Classical.choice hG₁_iso)]
            simp only [Set.toFinset_card, Fintype.card_ofFinset, LabeledGraph.size]
          · simp only [Set.coe_toFinset]
            exact labeledSubgraph_contain_type_verts Grep G₁
          · rw [← labeledGraphIso_size_eq G₂.coe F'rep (Classical.choice hG₂_iso)]
            simp only [Set.toFinset_card, Fintype.card_ofFinset, LabeledGraph.size]
          · simp only [Set.coe_toFinset]
            exact labeledSubgraph_contain_type_verts Grep G₂
        use ⟨W_G₁G₂, hW_G₁G₂_in_Ω⟩
        simp_all only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and, Set.coe_setOf, Set.mem_setOf_eq, Ω, A]
        obtain ⟨⟨hG₁_ind, hG₁_iso⟩, ⟨hG₂_ind, hG₂_iso⟩⟩ := hG
        obtain ⟨⟨hG₁_size, hG₁_tverts⟩, ⟨hG₂_size, hG₂_tverts⟩⟩ := hW_G₁G₂_in_Ω
        constructor <;> apply Nonempty.intro
        · have iso_G₁_G₁' : G₁.coe ≃f (inducedLabeledSubgraph Grep W_G₁G₂.1 hG₁_tverts).coe := by
            rw [inducedLabeledSubgraph_eq hG₁_ind]
            apply LabeledGraphIso.labeledSubgraphIso_eq
            congr!
            simp only [Set.coe_toFinset, W_G₁G₂]
          exact iso_G₁_G₁'.symm.trans (Classical.choice hG₁_iso)
        · have iso_G₂_G₂' : G₂.coe ≃f (inducedLabeledSubgraph Grep W_G₁G₂.2 hG₂_tverts).coe := by
            rw [inducedLabeledSubgraph_eq hG₂_ind]
            apply LabeledGraphIso.labeledSubgraphIso_eq
            congr!
            simp only [Set.coe_toFinset, W_G₁G₂]
          exact iso_G₂_G₂'.symm.trans (Classical.choice hG₂_iso)
      · constructor
        · intro ⟨⟨G₁, G₂⟩, hG⟩ ⟨⟨G'₁, G'₂⟩, hG'⟩ h_eq
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, Set.toFinset_inj]
          simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and] at hG hG'
          obtain ⟨⟨hG₁_ind, _⟩, ⟨hG₂_ind, _⟩⟩ := hG
          obtain ⟨⟨hG'₁_ind, _⟩, ⟨hG'₂_ind, _⟩⟩ := hG'
          exact ⟨labeledSubgraph_eq_from_subgraph_eq (hG₁_ind.eq_of_verts_eq hG'₁_ind h_eq.1),
                labeledSubgraph_eq_from_subgraph_eq (hG₂_ind.eq_of_verts_eq hG'₂_ind h_eq.2)⟩
        · intro ⟨⟨⟨w₁, w₂⟩, h_in_Ω⟩, h_in_A⟩
          obtain ⟨⟨_, h_w₁_tverts⟩, ⟨_, h_w₂_tverts⟩⟩ := h_in_Ω
          simp only [mem_filter, mem_univ, true_and, A] at h_in_A
          let G₁ := inducedLabeledSubgraph Grep w₁ h_w₁_tverts
          let G₂ := inducedLabeledSubgraph Grep w₂ h_w₂_tverts
          use ⟨(G₁, G₂), by simp_all only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, inducedLabeledSubgraph_isInduced, true_and, G₁, G₂]⟩
          simp only [inducedLabeledSubgraph_verts, toFinset_coe, G₁, G₂]
    · rw [← Nat.cast_mul, Nat.cast_inj]
      rw [hfreeG_size, hfreeF_size, hfreeF'_size] at hΩ_size
      rw [hΩ_size]; rfl

  have P₂ : labeledGraphListDensity (labeledGraphPairToList Frep F'rep) Grep = (A ∩ B).card / B.card := by
    dsimp only [labeledGraphListDensity]
    congr
    · dsimp only [labeledGraphListCount]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨l, hl⟩
        simp only [LabeledSubgraphList] at l
        use ⟨((l 0).subgraph.verts.toFinset, (l 1).subgraph.verts.toFinset), by
          simp only [Fin.isValue, Set.mem_setOf_eq, Set.toFinset_card, Fintype.card_ofFinset,
            Set.coe_toFinset, Ω]
          simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
            predDisjointLabeledSubgraphList, ne_eq, Set.coe_setOf, Set.toFinset_setOf, mem_filter,
            mem_univ, true_and] at hl
          obtain ⟨hl_ind, hl_iso, hl_disj⟩ := hl
          constructor <;> constructor
          · have : ((l 0).subgraph.verts.toFinset).card = Frep.size := by
              rw [← labeledGraphIso_size_eq (l 0).coe Frep (Classical.choice (hl_iso 0))]
              simp only [Fin.isValue, Set.toFinset_card, Fintype.card_ofFinset, LabeledGraph.size]
            simp_all only [Fin.isValue, Set.toFinset_card, Fintype.card_ofFinset]
          · exact labeledSubgraph_contain_type_verts Grep (l 0)
          · have : ((l 1).subgraph.verts.toFinset).card = F'rep.size := by
              rw [← labeledGraphIso_size_eq (l 1).coe F'rep (Classical.choice (hl_iso 1))]
              simp only [Fin.isValue, Set.toFinset_card, Fintype.card_ofFinset, LabeledGraph.size]
            simp_all only [Fin.isValue, Set.toFinset_card, Fintype.card_ofFinset]
          · exact labeledSubgraph_contain_type_verts Grep (l 1)⟩
        simp only [Fin.isValue, mem_inter, mem_filter, mem_univ, true_and, A, B]
        simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
          labeledGraphPairToList, predDisjointLabeledSubgraphList, ne_eq, Set.coe_setOf,
          Set.toFinset_setOf, mem_filter, mem_univ, true_and] at hl
        obtain ⟨hl_ind, hl_iso, hl_disj⟩ := hl
        constructor <;> try constructor
        · apply Nonempty.intro
          let h_iso₀ := Classical.choice (hl_iso 0)
          rw [inducedLabeledSubgraph_eq (hl_ind 0)] at h_iso₀
          simp only [Fin.isValue] at h_iso₀
          refine LabeledGraphIso.labeledSubgraphIso_cast ?_ h_iso₀
          simp only [Fin.isValue, Set.coe_toFinset]
        · apply Nonempty.intro
          let h_iso₁ := Classical.choice (hl_iso 1)
          rw [inducedLabeledSubgraph_eq (hl_ind 1)] at h_iso₁
          simp only [Fin.isValue] at h_iso₁
          refine LabeledGraphIso.labeledSubgraphIso_cast ?_ h_iso₁
          simp only [Fin.isValue, Set.coe_toFinset]
        · have := hl_disj 0 1 Fin.zero_ne_one
          rwa [← Set.toFinset_diff, ← Set.toFinset_diff, ← Set.toFinset_inter, Set.toFinset_eq_empty]
      · constructor
        · intro ⟨l, hl⟩ ⟨l', hl'⟩ h_eq
          simp_all only [Fin.isValue, Subtype.mk.injEq, Prod.mk.injEq, Set.toFinset_inj]
          simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
            predDisjointLabeledSubgraphList, ne_eq, Set.coe_setOf, Set.toFinset_setOf, mem_filter,
            mem_univ, true_and] at hl hl'
          obtain ⟨hl_ind, _⟩ := hl
          obtain ⟨hl'_ind, _⟩ := hl'
          funext i
          by_cases hi : i = 0
          · rw [inducedLabeledSubgraph_eq (hl_ind i), inducedLabeledSubgraph_eq (hl'_ind i)]
            simp_all
          · rw [inducedLabeledSubgraph_eq (hl_ind i), inducedLabeledSubgraph_eq (hl'_ind i)]
            simp_all [Fin.eq_one_of_ne_zero i hi]
        · intro ⟨⟨(w₁, w₂), hw_in_Ω⟩, hw_in_AB⟩
          simp only [Set.mem_setOf_eq, Ω] at hw_in_Ω
          simp only [mem_inter, mem_filter, mem_univ, true_and, A, B] at hw_in_AB
          obtain ⟨⟨hw₁_iso_F, hw₂_iso_F'⟩, hw_disj⟩ := hw_in_AB
          let l : LabeledSubgraphList σ 2 Grep := fun i ↦
            (match i with
              | 0 => inducedLabeledSubgraph Grep w₁ hw_in_Ω.1.2
              | 1 => inducedLabeledSubgraph Grep w₂ hw_in_Ω.2.2)
          use ⟨l, by
            simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced,
              predIsoLabeledHl, predDisjointLabeledSubgraphList, ne_eq, Set.coe_setOf,
              Set.toFinset_setOf, mem_filter, mem_univ, true_and]
            constructor <;> try constructor
            · intro i
              simp only [l]; split <;> simp_all only [inducedLabeledSubgraph_isInduced]
            · intro i
              simp only [l]; split <;> simp_all only [labeledGraphPairToList]
            · intro i j hij
              by_cases hi : i = 0 <;> by_cases hj : j = 0
              · simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fin.isValue, not_true_eq_false]
              · simp only [hi, Fin.isValue, inducedLabeledSubgraph_verts, Fin.eq_one_of_ne_zero j hj, l]
                rwa [← Set.toFinset_eq_empty, Set.toFinset_inter, Set.toFinset_diff, Set.toFinset_diff, toFinset_coe, toFinset_coe]
              · simp only [hj, Fin.isValue, inducedLabeledSubgraph_verts, Fin.eq_one_of_ne_zero i hi, l]
                rw [Finset.inter_comm] at hw_disj
                rwa [← Set.toFinset_eq_empty, Set.toFinset_inter, Set.toFinset_diff, Set.toFinset_diff, toFinset_coe, toFinset_coe]
              · simp_all only [Fin.eq_one_of_ne_zero i hi, Fin.eq_one_of_ne_zero j hj, not_true_eq_false] ⟩
          simp only [Fin.isValue, inducedLabeledSubgraph_verts, toFinset_coe, l]
    · rw [hB_size, hfreeG_size]
      simp only [r_list]; rfl
  rw [P₁, P₂]; clear P₁ P₂

  by_cases hG_size : Grep.size ≤ Frep.size + F'rep.size
  · by_cases hG_zero : Grep.size = 0
    · rw [hG_zero]
      simp only [CharP.cast_eq_zero, div_zero, abs_nonpos_iff, sub_eq_zero]
      by_cases hF_size : ¬Frep.size = 0 ∨ ¬F'rep.size = 0
      · obtain (hF_zero | hF'_zero) := hF_size
        · have fG_lt_fF : Grep.size - σ.size < Frep.size - σ.size := by
            apply Nat.sub_lt_sub_right (by exact Grep.type_size_le_size)
            rw [hG_zero]; exact Nat.zero_lt_of_ne_zero hF_zero
          have hΩ_zero : Ω.toFinset.card = 0 := by
            rw [hΩ_size]; apply mul_eq_zero_of_left
            rw [Nat.choose_eq_zero_iff, hfreeG_size, hfreeF_size]
            exact fG_lt_fF
          have hB_zero : B.card = 0 := by
            rw [hB_size]
            dsimp [multinomialCoefficient]
            apply if_neg; simp only [Fin.sum_univ_two, ge_iff_le, not_le, r_list]
            apply Nat.lt_add_right; rw [hfreeG_size]
            exact fG_lt_fF
          rw [hΩ_zero, hB_zero]
          simp only [CharP.cast_eq_zero, div_zero]
        · have fG_lt_fF' : Grep.size - σ.size < F'rep.size - σ.size := by
            apply Nat.sub_lt_sub_right (by exact Grep.type_size_le_size)
            rw [hG_zero]; exact Nat.zero_lt_of_ne_zero hF'_zero
          have hΩ_zero : Ω.toFinset.card = 0 := by
            rw [hΩ_size]; apply mul_eq_zero_of_right
            rw [Nat.choose_eq_zero_iff, hfreeG_size, hfreeF'_size]
            exact fG_lt_fF'
          have hB_zero : B.card = 0 := by
            rw [hB_size]
            dsimp [multinomialCoefficient]
            apply if_neg; simp only [Fin.sum_univ_two, ge_iff_le, not_le, r_list]
            apply Nat.lt_add_left; rw [hfreeG_size]
            exact fG_lt_fF'
          rw [hΩ_zero, hB_zero]
          simp only [CharP.cast_eq_zero, div_zero]
      · simp at hF_size
        have hΩ_one : Ω.toFinset.card = 1 := by
          rw [hΩ_size, hfreeF_size, hF_size.1, hfreeF'_size, hF_size.2, zero_tsub]
          simp only [Nat.choose_zero_right, mul_one]
        have hB_one : B.card = 1 := by
          rw [hB_size]
          dsimp only [multinomialCoefficient]
          split
          next h =>
            simp only [Fin.prod_univ_two, Fin.sum_univ_two, r_list]
            have fG_fac : freeG.card.factorial = 1 := by
              rw [Nat.factorial_eq_one, hfreeG_size, hG_zero, zero_tsub]
              simp only [zero_le]
            have fF_fac : (Frep.size - σ.size).factorial = 1 := by
              rw [Nat.factorial_eq_one, hF_size.1, zero_tsub]
              simp only [zero_le]
            have fF'_fac : (F'rep.size - σ.size).factorial = 1 := by
              rw [Nat.factorial_eq_one, hF_size.2, zero_tsub]
              simp only [zero_le]
            have f_fac : (#freeG - (Frep.size - σ.size + (F'rep.size - σ.size))).factorial = 1 := by
              rw [Nat.factorial_eq_one, hfreeG_size, hG_zero, hF_size.1, hF_size.2, zero_tsub, zero_tsub]
              simp only [zero_le]
            rw [fG_fac, fF_fac, fF'_fac, f_fac, mul_one, one_mul]
          next h =>
            exfalso
            simp only [Fin.sum_univ_two, ge_iff_le, not_le, r_list] at h
            rw [hfreeG_size, hG_zero, hF_size.1, hF_size.2, zero_tsub, add_zero] at h
            exact Nat.not_lt_zero _ h
        rw [hΩ_one, hB_one, Nat.cast_one, div_one, div_one, Nat.cast_inj]
        have hAUB_one : (A ∪ B).card = 1 := by
          apply Nat.le_antisymm
          · refine Preorder.le_trans _ Ω.toFinset.card _ ?_ ?_
            · rw [← hΩ_card_eq]
              exact card_le_card (Finset.subset_univ (A ∪ B))
            · rw [hΩ_one]
          · rw [← card_sdiff_add_card, hB_one]
            simp only [le_add_iff_nonneg_left, zero_le]
        rw [card_inter, hB_one, hAUB_one, add_tsub_cancel_right]
    · refine Preorder.le_trans _ 1 _ ?_ ?_
      · refine abs_sub_le_of_nonneg_of_le ?_ ?_ ?_ ?_
        · apply div_nonneg <;> simp only [Nat.cast_nonneg]
        · apply div_le_one_of_le₀
          · rw [Nat.cast_le]; exact card_le_card inter_subset_right
          · simp only [Nat.cast_nonneg]
        · apply div_nonneg <;> simp only [Nat.cast_nonneg]
        · apply div_le_one_of_le₀
          · rw [Nat.cast_le, ← hΩ_card_eq]; exact card_le_card (Finset.subset_univ A)
          · simp only [Nat.cast_nonneg]
      · refine (one_le_div₀ ?_).mpr ?_
        · rw [Nat.cast_pos]
          exact Nat.zero_lt_of_ne_zero hG_zero
        · refine Preorder.le_trans _ (Frep.size + F'rep.size : ℚ) _ (by rwa [← Nat.cast_add, Nat.cast_le]) ?_
          refine Preorder.le_trans _ ((Frep.size + F'rep.size) ^ 2 : ℚ) _ ?_ ?_
          · rw [← Nat.cast_add, ← Nat.cast_pow, Nat.cast_le]
            apply Nat.le_pow Nat.ofNat_pos
          · exact le_mul_of_one_le_left (by simp only [sq_nonneg]) rfl
  · simp only [not_le] at hG_size
    have hF_size := Frep.type_size_le_size
    have hF'_size := F'rep.type_size_le_size
    have hG_pos : 0 < Grep.size := Nat.zero_lt_of_lt hG_size
    have hG_size' : 2 * σ.size ≤ Grep.size := by
      rw [two_mul]
      refine Preorder.le_trans _ (Frep.size + F'rep.size) _ ?_ (Nat.le_of_lt hG_size)
      exact Nat.add_le_add hF_size hF'_size
    have hfG_pos : 0 < freeG.card := by omega
    have hΩ_nonzero : ¬ Ω.toFinset.card = 0 := by
      rw [hΩ_size]
      apply mul_ne_zero <;> apply Nat.choose_ne_zero_iff.mpr <;> omega
    have hΩ_pos : 0 < (Ω.toFinset.card : ℚ) := by
      rw [Nat.cast_pos]
      exact Nat.zero_lt_of_ne_zero hΩ_nonzero
    have hB_nonzero : ¬ B.card = 0 := by
      rw [← ne_eq, ← pos_iff_ne_zero, hB_size]
      apply multinomialCoefficient_pos
      simp only [Fin.sum_univ_two, ge_iff_le, r_list]
      omega
    have hB_pos : 0 < (B.card : ℚ) := Nat.cast_pos.mpr (Nat.zero_lt_of_ne_zero hB_nonzero)
    have compl_card : (@Nat.cast ℚ _ (SetLike.coe B)ᶜ.toFinset.card) / ↑Ω.toFinset.card = 1 - ↑(B.card) / ↑(Ω.toFinset.card) := by
      rw [← hΩ_card_eq]
      simp only [Set.compl_eq_univ_diff (SetLike.coe B), Set.toFinset_diff, Set.toFinset_univ, toFinset_coe]
      rw [card_sdiff_of_subset (by exact Finset.subset_univ B)]
      rw [Nat.cast_sub (by exact Finset.card_le_card (Finset.subset_univ B))]
      rw [sub_div, div_self (by rwa [hΩ_card_eq, ne_eq, Rat.natCast_eq_zero_iff])]

    have cond_bound : |((A ∩ B).card : ℚ) / (B.card : ℚ) - (A.card : ℚ) / (Ω.toFinset.card : ℚ)| ≤ 1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ) := by
      rw [abs_le]; constructor
      · rw [neg_le_sub_iff_le_add', ← tsub_le_iff_right]
        have hA_card : A.card = (A ∩ B).card + ((SetLike.coe A) ∩ (SetLike.coe B)ᶜ).toFinset.card := by
          have hA_union := Set.toFinset_congr (Set.inter_union_compl (SetLike.coe A) (SetLike.coe B))
          simp only [toFinset_coe] at hA_union
          nth_rw 1 [← hA_union, Set.toFinset_union]
          rw [card_union_eq_card_add_card.mpr (by
            rw [disjoint_iff_inter_eq_empty, ← Set.toFinset_inter, Set.toFinset_eq_empty, ← Set.inter_inter_distrib_left]
            simp only [Set.inter_compl_self, Set.inter_empty])]
          simp only [Set.toFinset_inter, toFinset_coe, Set.toFinset_compl]
        rw [hA_card, Nat.cast_add, add_div, add_comm, add_sub_assoc]
        refine Preorder.le_trans _ ?_ _ ?_ ?_
        · exact ↑(#((SetLike.coe A) ∩ (SetLike.coe B)ᶜ).toFinset) / ↑(#Ω.toFinset)
        · rw [add_le_iff_nonpos_right, sub_nonpos, div_le_div_iff₀ hΩ_pos hB_pos]
          rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le, ← hΩ_card_eq]
          apply Nat.mul_le_mul_left
          exact Finset.card_le_card (Finset.subset_univ B)
        · rw [← compl_card, div_le_div_iff_of_pos_right hΩ_pos]
          simp only [Set.toFinset_inter, toFinset_coe, Set.toFinset_compl, Nat.cast_le]
          exact card_le_card inter_subset_right
      · suffices (((A ∩ B).card : ℚ) / (B.card : ℚ) - (A.card : ℚ) / (Ω.toFinset.card : ℚ)) * B.card ≤ (1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ)) * B.card by
          exact le_of_mul_le_mul_right this hB_pos
        rw [sub_mul, tsub_le_iff_right, ← add_mul]
        rw [div_mul, div_self (by rwa [ne_eq, Rat.natCast_eq_zero_iff]), div_one]
        suffices @Nat.cast ℚ _ (min A.card B.card) ≤ (1 - ↑(B.card) / ↑(Ω.toFinset.card) + ↑(A.card) / ↑(Ω.toFinset.card)) * ↑(B.card) by
          calc
            @Nat.cast ℚ _ (A ∩ B).card ≤ @Nat.cast ℚ _ (min A.card B.card) := by
              rw [Nat.cast_le, Nat.le_min]
              constructor <;> apply card_le_card
              · exact inter_subset_left
              · exact inter_subset_right
            _ ≤ (1 - ↑(B.card) / ↑(Ω.toFinset.card) + ↑(A.card) / ↑(Ω.toFinset.card)) * ↑(B.card) := by exact this
        simp only [Nat.cast_min, inf_le_iff]
        by_cases hAB : A.card ≤ B.card
        · left
          rw [Rat.le_iff_sub_nonneg, add_mul, div_mul, add_sub_assoc]
          have : (@Nat.cast ℚ _ (#A)) / (↑(#Ω.toFinset) / ↑(#B)) - ↑(#A) = - ↑(#A) * (1 - ↑(#B) / ↑(#Ω.toFinset)) := by
            rw [neg_mul_comm, neg_sub, div_div_eq_mul_div, mul_sub, mul_one, mul_div]
          rw [this, mul_comm, ← add_mul]
          refine Rat.mul_nonneg ?_ ?_
          · simp_all only [le_add_neg_iff_add_le, zero_add, Nat.cast_le]
          · rw [sub_nonneg, div_le_iff₀ hΩ_pos, one_mul, Nat.cast_le, ← hΩ_card_eq]
            exact Finset.card_le_card (Finset.subset_univ B)
        · right
          rw [mul_comm, le_mul_iff_one_le_right hB_pos]
          rw [sub_add_eq_add_sub, add_sub_assoc, le_add_iff_nonneg_right, sub_nonneg]
          simp only [not_le] at hAB
          rw [div_le_div_iff_of_pos_right hΩ_pos, Nat.cast_le]
          exact Nat.le_of_lt hAB
    refine Preorder.le_trans ?_ (1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ)) _ (by exact cond_bound) ?_

    refine Preorder.le_trans _ ?_ _ ?_ ?_
    · exact ((Frep.size - σ.size) * (F'rep.size - σ.size) + (F'rep.size - σ.size) ^ 2) / (Grep.size - σ.size)
    · have hB_size' : B.card = Nat.choose (freeG.card) (freeF.card) * Nat.choose (freeG.card - freeF.card) (freeF'.card) := by
        rw [hB_size]
        have : Frep.size - σ.size + (F'rep.size - σ.size) ≤ freeG.card := by omega
        simp only [multinomialCoefficient, Fin.sum_univ_two, ge_iff_le, this, ↓reduceDIte, Fin.prod_univ_two, r_list]
        rw [Nat.choose_eq_factorial_div_factorial (by omega), Nat.choose_eq_factorial_div_factorial (by omega)]
        nth_rw 2 [← Nat.div_div_eq_div_mul]
        rw [Nat.div_mul_div (by apply Nat.dvd_div_of_mul_dvd; apply Nat.factorial_mul_factorial_dvd_factorial; omega) (by apply Nat.factorial_mul_factorial_dvd_factorial; omega)]
        rw [mul_assoc, Nat.div_div_eq_div_mul, ← hfreeF_size, ← hfreeF'_size, Nat.sub_sub]
      rw [hΩ_size, hB_size']
      rw [← Nat.cast_sub (by exact Frep.type_size_le_size), ← hfreeF_size]
      rw [← Nat.cast_sub (by exact F'rep.type_size_le_size), ← hfreeF'_size]
      rw [← Nat.cast_sub (by exact Grep.type_size_le_size), ← hfreeG_size]
      rw [Nat.cast_mul, Nat.cast_mul, ← div_div_eq_mul_div, ← div_mul]
      rw [← div_div, div_self (by rw [ne_eq, Rat.natCast_eq_zero_iff, ← ne_eq]; exact Nat.choose_ne_zero (by omega)), one_div_mul_eq_div]
      rw [pow_two, ← add_mul, mul_comm, mul_div_assoc, tsub_le_iff_tsub_le]
      refine Preorder.le_trans _ ?_ _ ?_ ?_
      · exact (freeG.card - freeF.card - freeF'.card) ^ freeF'.card / freeG.card ^ freeF'.card
      · rw [← div_pow, sub_sub, sub_div, div_self (by simp only [ne_eq, Rat.natCast_eq_zero_iff]; rw [hfreeG_size]; omega)]
        rw [sub_eq_add_neg, sub_eq_add_neg, ← Nat.cast_add, neg_mul_eq_mul_neg]
        have : -2 ≤ -(@Nat.cast ℚ _ (#freeF + #freeF') / ↑(#freeG)) := by
          simp only [Nat.cast_add, neg_le_neg_iff]
          refine Preorder.le_trans _ 1 _ ?_ (by simp only [Nat.one_le_ofNat])
          refine div_le_one_of_le₀ ?_ ?_
          · rw [← Nat.cast_add ,Nat.cast_le]; omega
          · simp only [Nat.cast_nonneg]
        exact one_add_mul_le_pow this freeF'.card
      · rw [Nat.choose_eq_factorial_div_factorial (by omega), Nat.choose_eq_factorial_div_factorial (by omega)]
        rw [mul_comm, ← Nat.div_div_eq_div_mul]
        rw [mul_comm, ← Nat.div_div_eq_div_mul]
        rw [Nat.cast_div (by apply Nat.dvd_div_of_mul_dvd; rw [mul_comm];apply Nat.factorial_mul_factorial_dvd_factorial; omega) (by simp only [ne_eq,
          Rat.natCast_eq_zero_iff, Nat.factorial_ne_zero, not_false_eq_true])]
        nth_rw 2 [Nat.cast_div (by apply Nat.dvd_div_of_mul_dvd;rw [mul_comm];apply Nat.factorial_mul_factorial_dvd_factorial; omega) (by simp only [ne_eq,
          Rat.natCast_eq_zero_iff, Nat.factorial_ne_zero, not_false_eq_true])]
        rw [div_div_div_cancel_right₀ (by
          simp only [ne_eq, Rat.natCast_eq_zero_iff, Nat.factorial_ne_zero, not_false_eq_true])]
        rw [Nat.cast_div (by apply Nat.factorial_dvd_factorial; omega) (by simp only [ne_eq, Rat.natCast_eq_zero_iff, Nat.factorial_ne_zero, not_false_eq_true])]
        rw [Nat.cast_div (by apply Nat.factorial_dvd_factorial; omega) (by simp only [ne_eq, Rat.natCast_eq_zero_iff, Nat.factorial_ne_zero, not_false_eq_true])]
        refine (div_le_div_iff₀ ?_ ?_).mpr ?_
        · refine pow_pos ?_ _
          exact Nat.cast_pos.mpr hfG_pos
        · apply div_pos <;> simp only [Nat.cast_pos, Nat.factorial_pos]
        · refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          · rw [sub_sub, ← Nat.cast_add, ← Nat.cast_sub (by omega), ← Nat.cast_pow]
            rw [← Nat.cast_div (by apply Nat.factorial_dvd_factorial; omega) (by simp only [ne_eq, Rat.natCast_eq_zero_iff, Nat.factorial_ne_zero, not_false_eq_true]), Nat.cast_le, Nat.sub_sub]
            refine (Nat.le_div_iff_mul_le ?_).mpr ?_
            · simp only [Nat.factorial_pos]
            · rw [mul_comm]
              have hnm : freeG.card - (freeF.card + freeF'.card) ≤ freeG.card - freeF.card := by omega
              have : freeG.card - freeF.card - (freeG.card - (freeF.card + freeF'.card)) = freeF'.card := by omega
              nth_rw 3 [← this]
              exact Nat.factorial_mul_pow_sub_le_factorial hnm
          · rw [← Nat.cast_div (by apply Nat.factorial_dvd_factorial; omega) (by
              rw [ne_eq, Rat.natCast_eq_zero_iff, ← ne_eq]
              apply Nat.factorial_ne_zero)]
            rw [← Nat.cast_pow, Nat.cast_le]
            have h : freeF'.card ≤ freeG.card := by omega
            rw [← Nat.descFactorial_eq_div h]
            apply Nat.descFactorial_le_pow
          · refine pow_nonneg ?_ _
            simp only [le_sub_iff_add_le]
            rw [zero_add, ← Nat.cast_add, Nat.cast_le]
            omega
          · apply pow_nonneg
            simp only [Nat.cast_nonneg]
    · refine Preorder.le_trans _ ?_ _ ?_ ?_
      · exact (Frep.size + F'rep.size) ^ 2 / (Grep.size - σ.size)
      · apply (div_le_div_iff_of_pos_right (by
          simp only [sub_pos, Nat.cast_lt]
          omega)).mpr
        rw [sub_mul, mul_sub, mul_sub, sub_sub, sub_add_eq_add_sub]
        rw [sub_le_iff_le_add']
        refine le_add_of_nonneg_of_le ?_ ?_
        · rw [← add_sub_assoc, mul_comm, ← mul_add]
          apply sub_nonneg_of_le
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [← Nat.cast_add, Nat.cast_le]
          exact Nat.le_add_right_of_le (Frep.type_size_le_size)
        · rw [pow_two, sub_mul, mul_sub, mul_sub, sub_sub, ← add_sub_assoc]
          refine Preorder.le_trans _ ?_ _ ?_ ?_
          · exact ↑Frep.size * ↑F'rep.size + ↑F'rep.size * ↑F'rep.size
          · apply sub_le_self
            refine add_nonneg ?_ ?_
            · rw [← Nat.cast_mul]
              apply Nat.cast_nonneg
            · rw [sub_nonneg]
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · rw [Nat.cast_le]; exact F'rep.type_size_le_size
              · apply Nat.cast_nonneg
          · rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add]
            rw [← Nat.cast_add, ← Nat.cast_pow, Nat.cast_le]
            rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
            omega
      · refine (div_le_div_iff₀ ?_ ?_).mpr ?_
        · simp only [sub_pos, Nat.cast_lt]; omega
        · simp only [Nat.cast_pos]
          exact Nat.zero_lt_of_ne_zero (by omega)
        · rw [mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · rw [← Nat.cast_sub (by exact Grep.type_size_le_size), ← Nat.cast_ofNat, ← Nat.cast_mul, Nat.cast_le]
            omega
          · rw [← Nat.cast_add]; apply sq_nonneg

-- theorem flagListDensity_prod_approx
--     (Fl : FlagList σ t Vl)
--     : ∃ k, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
--     |flagListDensity Fl G - ∏ i ∈ Finset.univ, flagDensity₁ (Fl i) G| ≤ (∑ i ∈ Finset.univ, (Fl i).out.size) ^ k / G.out.size
--   := by sorry

end FlagAlgebras
