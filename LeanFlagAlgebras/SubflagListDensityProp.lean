import «LeanFlagAlgebras».SubgraphUtil
import «LeanFlagAlgebras».FlagDef
import «LeanFlagAlgebras».SubflagListDensity

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Vector.Basic
import Mathlib.Data.FinEnum

open FlagAlgebras
open LabeledSubgraph
open Classical
open Finset
open MeasureTheory ProbabilityTheory
noncomputable section

variable {T : Type} [Fintype T] [DecidableEq T]
variable {V : Type} [Fintype V] [DecidableEq V]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {U : Type} [Fintype U] [DecidableEq U]

variable {σ : FlagType T} {t : ℕ}
variable {Vl  : Fin t → Type} [FintypeList Vl]  [DecidableEqList Vl]
variable {Fl : FlagList σ t Vl}

theorem flagListDensity₂_prod_approx
    (F : Flag σ V) (F' : Flag σ U)
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    : ∃ c ≥ 0, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
    |flagDensity₂ F F' G - flagDensity₁ F G * flagDensity₁ F' G| ≤ c / G.out.size
  := by
  let c := max (2 * (F.out.size + F'.out.size) ^ 2) (2 * σ.size)
  use c
  constructor; (sorry)
  intro W _ _ G
  let ⟨Grep, hGrep₁⟩ := Quotient.exists_rep G
  have hGrep₂ : (⟦Grep⟧ : Quotient (labeledGraphSetoid σ W)).out.size = Grep.size := rfl
  let ⟨Frep, hFrep₁⟩ := Quotient.exists_rep F
  have hFrep₂ : (⟦Frep⟧ : Quotient (labeledGraphSetoid σ V)).out.size = Frep.size := rfl
  let ⟨F'rep, hF'rep₁⟩ := Quotient.exists_rep F'
  have hF'rep₂ : (⟦F'rep⟧ : Quotient (labeledGraphSetoid σ U)).out.size = F'rep.size := rfl
  dsimp only [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F G, ← subflagDensity_eq_flagListDensity F' G]
  rw [← hFrep₁, ← hF'rep₁, ← hGrep₁, hGrep₂, ← labeledSubgraphListDensity_eq_flagDensity₂ Frep F'rep Grep]
  dsimp only [subflagDensity, Quotient.lift_mk, labeledSubgraphDensityLifted]
  -- rw [hFrep₂, hF'rep₂, hGrep₂]
  -- clear hFrep₁ hF'rep₁ hGrep₁ hFrep₂ hF'rep₂ hGrep₂

  let freeG := Finset.univ \ Grep.type_verts.toFinset
  have hfreeG_size : freeG.card = Grep.size - σ.size := by
    simp_all only [freeG]
    rw [← Grep.type_verts_card_eq, Finset.card_sdiff] <;> try simp only [subset_univ]
    simp only [card_univ, Set.toFinset_card]; rfl
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
    rw [← Frep.type_verts_card_eq, Finset.card_sdiff] <;> try simp only [subset_univ]
    simp only [card_univ, Set.toFinset_card]; rfl
  let freeF' := Finset.univ \ F'rep.type_verts.toFinset
  have hfreeF'_size : freeF'.card = F'rep.size - σ.size := by
    simp_all only [freeF']
    rw [← F'rep.type_verts_card_eq, Finset.card_sdiff] <;> try simp only [subset_univ]
    simp only [card_univ, Set.toFinset_card]; rfl
  let Ω := { (w₁, w₂) : Finset W × Finset W | (w₁.card = Frep.size ∧ Grep.type_verts ⊆ w₁) ∧ (w₂.card = F'rep.size ∧ Grep.type_verts ⊆ w₂)}
  have hΩ_size : Ω.toFinset.card = (freeG.card).choose freeF.card * (freeG.card).choose freeF'.card := by
    rw [← comb_card freeG freeF.card, ← comb_card freeG freeF'.card, ← Finset.card_product, eq_comm]
    simp only [Set.toFinset_card, Fintype.card_ofFinset]
    apply Finset.card_eq_of_equiv
    refine Equiv.ofBijective ?_ ?_
    · intro ⟨⟨w₁, w₂⟩, hw⟩
      use (w₁ ∪ Grep.type_verts.toFinset, w₂ ∪ Grep.type_verts.toFinset)
      simp only [mem_filter, mem_univ, Set.mem_setOf_eq, true_and, Ω, coe_union, Set.coe_toFinset, Set.subset_union_right, and_true]
      simp only [combinations, mem_product, mem_filter, mem_powerset] at hw
      obtain ⟨⟨hw₁_free, hw₁_size⟩, ⟨hw₂_free, hw₂_size⟩⟩ := hw
      constructor
      · rw [Finset.card_union, hw₁_size, hfreeF_size, ← Grep.type_verts_card_eq, Set.toFinset_card]
        have hw₁_sub : (w₁ ∩ Grep.type_verts.toFinset).card = 0 := by
          rw [card_eq_zero]
          apply disjoint_iff_inter_eq_empty.mp (hfreeG_sub w₁ hw₁_free)
        rw [hw₁_sub, tsub_zero]
        apply Nat.sub_add_cancel
        rw [Grep.type_verts_card_eq, ← Frep.type_verts_card_eq, LabeledGraph.size]
        exact set_fintype_card_le_univ Frep.type_verts
      · rw [Finset.card_union, hw₂_size, hfreeF'_size, ← Grep.type_verts_card_eq, Set.toFinset_card]
        have hw₂_sub : (w₂ ∩ Grep.type_verts.toFinset).card = 0 := by
          rw [card_eq_zero]
          apply disjoint_iff_inter_eq_empty.mp (hfreeG_sub w₂ hw₂_free)
        rw [hw₂_sub, tsub_zero]
        apply Nat.sub_add_cancel
        rw [Grep.type_verts_card_eq, ← F'rep.type_verts_card_eq, LabeledGraph.size]
        exact set_fintype_card_le_univ F'rep.type_verts
    · constructor
      · intro ⟨⟨w₁, w₂⟩, hw⟩ ⟨⟨w'₁, w'₂⟩, hw'⟩ h
        simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
        simp only [combinations, mem_product, mem_filter, mem_powerset] at hw hw'
        obtain ⟨h₁, h₂⟩ := h
        obtain ⟨⟨hw₁_free, _⟩, ⟨hw₂_free, _⟩⟩ := hw
        obtain ⟨⟨hw'₁_free, _⟩, ⟨hw'₂_free, _⟩⟩ := hw'
        rw [← union_sdiff_cancel_right (hfreeG_sub w₁ hw₁_free), ← union_sdiff_cancel_right (hfreeG_sub w'₁ hw'₁_free), h₁]
        rw [← union_sdiff_cancel_right (hfreeG_sub w₂ hw₂_free), ← union_sdiff_cancel_right (hfreeG_sub w'₂ hw'₂_free), h₂]
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
          · rw [Finset.card_sdiff, Set.toFinset_card]
            · rw [hw₁_size, hfreeF_size, ← Grep.type_verts_card_eq]
            · simp only [Set.toFinset_subset]
              exact hw₁_tverts
          · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
            exact subset_univ w₂
          · rw [Finset.card_sdiff, Set.toFinset_card]
            · rw [hw₂_size, hfreeF'_size, ← Grep.type_verts_card_eq]
            · simp only [Set.toFinset_subset]
              exact hw₂_tverts
        use ⟨w, hw⟩
        simp only [sdiff_union_self_eq_union, Subtype.mk.injEq, Prod.mk.injEq, union_eq_left, Set.toFinset_subset, w]
        exact ⟨hw₁_tverts, hw₂_tverts⟩
  let A : Finset Ω := { v | by
    obtain ⟨⟨v₁, v₂⟩, h⟩ := v
    exact Nonempty ((inducedLabeledSubgraph Grep v₁ h.1.2).coe ≃f Frep) ∧ Nonempty ((inducedLabeledSubgraph Grep v₂ h.2.2).coe ≃f F'rep) }
  let B : Finset Ω := { v | by
    obtain ⟨⟨v₁, v₂⟩, h⟩ := v
    exact (v₁ \ Grep.type_verts.toFinset) ∩ (v₂ \ Grep.type_verts.toFinset) = ∅ }

  have P₁ : labeledSubgraphDensity Frep Grep * labeledSubgraphDensity F'rep Grep = A.card / Ω.toFinset.card := by
    dsimp only [labeledSubgraphDensity]
    field_simp
    congr
    · dsimp only [labeledSubgraphCount]
      rw [← Nat.cast_mul, Nat.cast_inj, ← Finset.card_product]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨⟨G₁, G₂⟩, hG⟩
        let V_G₁G₂ : Finset W × Finset W := (G₁.subgraph.verts.toFinset, G₂.subgraph.verts.toFinset)
        have h_V_G₁G₂_in_Ω : V_G₁G₂ ∈ Ω := by
          simp only [Set.mem_setOf_eq, Ω, V_G₁G₂]
          simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and] at hG
          obtain ⟨⟨_, hG₁_iso⟩, ⟨_, hG₂_iso⟩⟩ := hG
          constructor
          · constructor
            · rw [← labeledGraphIso_size_eq G₁.coe Frep (Classical.choice hG₁_iso)]
              simp only [Set.toFinset_card, Fintype.card_ofFinset, LabeledGraph.size]
            · simp only [Set.coe_toFinset]
              exact labeledSubgraph_contain_type_verts Grep G₁
          · constructor
            · rw [← labeledGraphIso_size_eq G₂.coe F'rep (Classical.choice hG₂_iso)]
              simp only [Set.toFinset_card, Fintype.card_ofFinset, LabeledGraph.size]
            · simp only [Set.coe_toFinset]
              exact labeledSubgraph_contain_type_verts Grep G₂
        use ⟨V_G₁G₂, h_V_G₁G₂_in_Ω⟩
        simp_all only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and, Set.coe_setOf, Set.mem_setOf_eq, Ω, A]
        obtain ⟨⟨hG₁_ind, hG₁_iso⟩, ⟨hG₂_ind, hG₂_iso⟩⟩ := hG
        obtain ⟨⟨hG₁_size, hG₁_tverts⟩, ⟨hG₂_size, hG₂_tverts⟩⟩ := h_V_G₁G₂_in_Ω
        constructor <;> apply Nonempty.intro
        · have iso_G₁_G₁' : G₁.coe ≃f (inducedLabeledSubgraph Grep V_G₁G₂.1 hG₁_tverts).coe := by
            rw [inducedLabeledSubgraph_eq hG₁_ind]
            apply LabeledGraphIso.labeledSubgraphIso_eq
            congr!
            simp only [Set.coe_toFinset, V_G₁G₂]
          exact iso_G₁_G₁'.symm.trans (Classical.choice hG₁_iso)
        · have iso_G₂_G₂' : G₂.coe ≃f (inducedLabeledSubgraph Grep V_G₁G₂.2 hG₂_tverts).coe := by
            rw [inducedLabeledSubgraph_eq hG₂_ind]
            apply LabeledGraphIso.labeledSubgraphIso_eq
            congr!
            simp only [Set.coe_toFinset, V_G₁G₂]
          exact iso_G₂_G₂'.symm.trans (Classical.choice hG₂_iso)
      · constructor
        · intro ⟨⟨G₁, G₂⟩, hG⟩ ⟨⟨G'₁, G'₂⟩, hG'⟩ h
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, Set.toFinset_inj]
          simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and] at hG hG'
          obtain ⟨h₁, h₂⟩ := h
          obtain ⟨⟨hG₁_ind, _⟩, ⟨hG₂_ind, _⟩⟩ := hG
          obtain ⟨⟨hG'₁_ind, _⟩, ⟨hG'₂_ind, _⟩⟩ := hG'
          constructor
          · exact labeledSubgraph_eq_from_subgraph_eq (inducedSubgraph_eq_verts hG₁_ind hG'₁_ind h₁)
          · exact labeledSubgraph_eq_from_subgraph_eq (inducedSubgraph_eq_verts hG₂_ind hG'₂_ind h₂)
        · intro ⟨⟨⟨w₁, w₂⟩, h_in_Ω⟩, h_in_A⟩
          obtain ⟨⟨_, h_w₁_tverts⟩, ⟨_, h_w₂_tverts⟩⟩ := h_in_Ω
          simp only [mem_filter, mem_univ, true_and, A] at h_in_A
          let G₁ := inducedLabeledSubgraph Grep w₁ h_w₁_tverts
          let G₂ := inducedLabeledSubgraph Grep w₂ h_w₂_tverts
          use ⟨(G₁, G₂), by
            simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, inducedLabeledSubgraph_isInduced, true_and, G₁, G₂]
            exact h_in_A⟩
          simp only [inducedLabeledSubgraph_verts, toFinset_coe, G₁, G₂]
    · rw [← Nat.cast_mul, Nat.cast_inj]
      -- I don't know why just using `rw` here doesn't work
      calc
        (Grep.size - σ.size).choose (Frep.size - σ.size) * (Grep.size - σ.size).choose (F'rep.size - σ.size)
          = (freeG.card).choose (freeF.card) * (freeG.card).choose (freeF'.card) := by rw [hfreeG_size, hfreeF_size, hfreeF'_size]
        _ = (freeG.card).choose (freeF.card) * (freeG.card).choose (freeF'.card) := rfl
      rw [← hΩ_size]
      simp only [Set.toFinset_card, Fintype.card_ofFinset]

  have P₂ : labeledSubgraphListDensity (labeledGraphPairToList Frep F'rep) Grep = (A ∩ B).card / B.card := by
    dsimp only [labeledSubgraphListDensity]
    congr
    · dsimp only [labeledSubgraphListCount]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨l, hl⟩
        simp [LabeledSubgraphList] at l
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
          simp only [Subtype.mk.injEq]
          simp only [Fin.isValue, Subtype.mk.injEq, Prod.mk.injEq, Set.toFinset_inj] at h_eq
          simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
            predDisjointLabeledSubgraphList, ne_eq, Set.coe_setOf, Set.toFinset_setOf, mem_filter,
            mem_univ, true_and] at hl hl'
          obtain ⟨hl_ind, _⟩ := hl
          obtain ⟨hl'_ind, _⟩ := hl'
          funext i
          rw [inducedLabeledSubgraph_eq (hl_ind i), inducedLabeledSubgraph_eq (hl'_ind i)]
          congr
          by_cases hi : i = 0
          · simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fin.isValue]
          · simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fin.isValue,
            Fin.eq_one_of_ne_zero i hi, one_ne_zero, not_false_eq_true]
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
              simp only [l]
              split <;> simp_all only [inducedLabeledSubgraph_isInduced]
            · intro i
              simp only [l]
              split <;> simp_all only [labeledGraphPairToList]
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
    · simp only [labeledGraphPairToList]
      let r_list : Fin 2 → ℕ := fun i ↦
        (match i with
          | 0 => Frep.size - σ.size
          | 1 => F'rep.size - σ.size)
      have hB : B.card = multinomialCoefficient r_list freeG.card := by
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
            by_cases h : i = 0
            · simp only [h, Fin.isValue, r, r_list]
              constructor
              · intro x hx
                simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, freeG]
                simp only [mem_sdiff, Set.mem_toFinset] at hx
                exact Set.notMem_of_mem_diff hx
              · rw [Finset.card_sdiff (by simp only [Set.toFinset_subset]; exact h_in_Ω.1.2)]
                rw [h_in_Ω.1.1, ← Grep.type_verts_card_eq, Set.toFinset_card]
            · simp only [Fin.eq_one_of_ne_zero i h, Fin.isValue, r, r_list]
              constructor
              · intro x hx
                simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, freeG]
                simp only [mem_sdiff, Set.mem_toFinset] at hx
                exact Set.notMem_of_mem_diff hx
              · rw [Finset.card_sdiff (by simp only [Set.toFinset_subset]; exact h_in_Ω.2.2)]
                rw [h_in_Ω.2.1, ← Grep.type_verts_card_eq, Set.toFinset_card]
          · intro i j hij
            by_cases hi : i = 0 <;> by_cases hj : j = 0
            · simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fin.isValue, not_true_eq_false]
            · simp only [hi, Fin.isValue, Fin.eq_one_of_ne_zero j hj, r]
              exact disjoint_iff_inter_eq_empty.mpr h_in_B
            · simp only [hj, Fin.isValue, Fin.eq_one_of_ne_zero i hi, r]
              rw [Finset.inter_comm] at h_in_B
              exact disjoint_iff_inter_eq_empty.mpr h_in_B
            · simp_all only [Fin.eq_one_of_ne_zero i hi, Fin.eq_one_of_ne_zero j hj, not_true_eq_false]
          · intro i
            by_cases h : i = 0
            · simp only [h, Fin.isValue, r]
              intro x hx
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, freeG]
              simp only [mem_sdiff, Set.mem_toFinset] at hx
              exact Set.notMem_of_mem_diff hx
            · simp only [Fin.eq_one_of_ne_zero i h, Fin.isValue, r]
              intro x hx
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, freeG]
              simp only [mem_sdiff, Set.mem_toFinset] at hx
              exact Set.notMem_of_mem_diff hx
        · constructor
          · intro ⟨⟨⟨w₁, w₂⟩, hw_in_Ω⟩, hw_in_B⟩ ⟨⟨⟨w'₁, w'₂⟩, hw'_in_Ω⟩, hw'_in_B⟩ h_eq
            simp only [Subtype.mk.injEq] at h_eq
            simp only [Subtype.mk.injEq, Prod.mk.injEq]
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
            let w := (l 0 ∪ Grep.type_verts.toFinset, l 1 ∪ Grep.type_verts.toFinset)
            have hw_in_Ω : w ∈ Ω := by
              simp only [Fin.isValue, Set.mem_setOf_eq, coe_union, Set.coe_toFinset, Set.subset_union_right, and_true, Ω, w]
              constructor
              · have hl0_sub : ((l 0) ∩ Grep.type_verts.toFinset).card = 0 := by
                  rw [card_eq_zero]
                  apply disjoint_iff_inter_eq_empty.mp (hfreeG_sub (l 0) (hl.1 0).1)
                rw [card_union, (hl.1 0).2, hl0_sub, tsub_zero]
                simp only [Fin.isValue, Set.toFinset_card, r_list]
                rw [← Grep.type_verts_card_eq]
                refine Nat.sub_add_cancel ?_
                rw [Grep.type_verts_card_eq, ← Frep.type_verts_card_eq, LabeledGraph.size]
                exact set_fintype_card_le_univ Frep.type_verts
              · have hl1_sub : ((l 1) ∩ Grep.type_verts.toFinset).card = 0 := by
                  rw [card_eq_zero]
                  apply disjoint_iff_inter_eq_empty.mp (hfreeG_sub (l 1) (hl.1 1).1)
                rw [card_union, (hl.1 1).2, hl1_sub, tsub_zero]
                simp only [Fin.isValue, Set.toFinset_card, r_list]
                rw [← Grep.type_verts_card_eq]
                refine Nat.sub_add_cancel ?_
                rw [Grep.type_verts_card_eq, ← F'rep.type_verts_card_eq, LabeledGraph.size]
                exact set_fintype_card_le_univ F'rep.type_verts
            have hw_in_B : ⟨w, hw_in_Ω⟩ ∈ B := by
              simp only [Fin.isValue, mem_filter, mem_univ, true_and, B, w]
              have hl0 : (l 0 ∪ Grep.type_verts.toFinset) \ Grep.type_verts.toFinset = l 0 := by
                refine union_sdiff_cancel_right ?_
                exact hfreeG_sub (l 0) (hl.1 0).1
              have hl1 : (l 1 ∪ Grep.type_verts.toFinset) \ Grep.type_verts.toFinset = l 1 := by
                refine union_sdiff_cancel_right ?_
                exact hfreeG_sub (l 1) (hl.1 1).1
              rw [hl0, hl1, ← disjoint_iff_inter_eq_empty]
              apply hl.2.1 0 1
              simp only [Fin.isValue, zero_ne_one, not_false_eq_true]
            use ⟨⟨w, hw_in_Ω⟩, hw_in_B⟩
            simp only [Subtype.mk.injEq]
            funext i
            by_cases h : i = 0
            · simp only [h, Fin.isValue, w]
              refine union_sdiff_cancel_right ?_
              exact hfreeG_sub (l 0) (hl.1 0).1
            · simp only [Fin.eq_one_of_ne_zero i h, Fin.isValue, w]
              refine union_sdiff_cancel_right ?_
              exact hfreeG_sub (l 1) (hl.1 1).1
      rw [hB, hfreeG_size]
      simp only [r_list]; rfl
  rw [P₁, P₂]
  clear P₁ P₂

  have Ω_card : (@univ (↑Ω) (Subtype.fintype (Membership.mem Ω))).card = Ω.toFinset.card := by
    simp only [card_univ, Fintype.card_ofFinset, Set.toFinset_card]
  by_cases h : B.card = 0 ∨ Ω.toFinset.card = 0
  /- case where B.card = 0 ∨ Ω.toFinset.card = 0 -/
  · obtain hB | hΩ := h
    · rw [hB]
      simp only [CharP.cast_eq_zero, div_zero, zero_sub, abs_neg, ge_iff_le]
      sorry
    · rw [hΩ]
      simp only [CharP.cast_eq_zero, div_zero, sub_zero, ge_iff_le]
      rw [card_eq_zero, Set.toFinset_eq_empty] at hΩ
      have hB : B.card = 0 := by
        rw [card_eq_zero]
        by_contra hB_nonempty
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hB_nonempty
        obtain ⟨⟨_, hx_in_Ω⟩, _⟩ := hB_nonempty
        rwa [hΩ, Set.mem_empty_iff_false] at hx_in_Ω
      rw [hB]
      simp only [CharP.cast_eq_zero, div_zero, abs_zero, ge_iff_le]
      apply div_nonneg <;> simp only [Nat.cast_nonneg]

  /- case where B.card ≠ 0 ∧ Ω.toFinset.card ≠ 0 -/
  simp only [not_or] at h
  obtain ⟨hB_nonzero, hΩ_nonzero⟩ := h
  have compl_card : (@Nat.cast ℚ _ (B.toSet)ᶜ.toFinset.card) / ↑Ω.toFinset.card = 1 - ↑(B.card) / ↑(Ω.toFinset.card) := by
    rw [← Ω_card]
    simp only [Set.compl_eq_univ_diff B.toSet, Set.toFinset_diff, Set.toFinset_univ, toFinset_coe]
    rw [card_sdiff (by exact Finset.subset_univ B)]
    rw [Nat.cast_sub (by exact Finset.card_le_card (Finset.subset_univ B))]
    rw [sub_div, div_self (by rwa [Ω_card, ne_eq, Rat.natCast_eq_zero])]

  have cond_bound : |((A ∩ B).card : ℚ) / (B.card : ℚ) - (A.card : ℚ) / (Ω.toFinset.card : ℚ)| ≤ 1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ) := by
    rw [abs_le]
    constructor
    · rw [neg_le_sub_iff_le_add', ← tsub_le_iff_right]
      have hA_card : A.card = (A ∩ B).card + (A.toSet ∩ B.toSetᶜ).toFinset.card := by
        have hA_split : A = (A ∩ B) ∪ (A.toSet ∩ B.toSetᶜ).toFinset := by
          ext x; constructor
          · intro hx
            by_cases h_in_B : x ∈ B
            · apply mem_union_left
              exact mem_inter.mpr ⟨hx, h_in_B⟩
            · apply mem_union_right
              simp only [Set.toFinset_inter, toFinset_coe, Set.toFinset_compl, mem_inter, mem_compl]
              exact ⟨hx, h_in_B⟩
          · intro hx
            simp only [Set.toFinset_inter, toFinset_coe, Set.toFinset_compl, mem_union, mem_inter, mem_compl] at hx
            obtain hx | hx := hx <;> exact hx.1
        nth_rw 1 [hA_split, Finset.card_union]
        have : #(A ∩ B ∩ (A.toSet ∩ (B.toSet)ᶜ).toFinset) = 0 := by
          rw [card_eq_zero]
          ext x
          simp only [Set.toFinset_inter, toFinset_coe, Set.toFinset_compl, inter_assoc, mem_inter, mem_compl, notMem_empty, iff_false, not_and, Decidable.not_not]
          exact fun _ hx _ ↦ hx
        rw [this, tsub_zero]
      rw [hA_card, Nat.cast_add, add_div, add_comm, add_sub_assoc]
      have add_le : (@Nat.cast ℚ _ (#(A.toSet ∩ (B.toSet)ᶜ).toFinset)) / ↑(#Ω.toFinset) + (↑(#(A ∩ B)) / ↑(#Ω.toFinset) - ↑(#(A ∩ B)) / ↑(#B))
        ≤ ↑(#(A.toSet ∩ (B.toSet)ᶜ).toFinset) / ↑(#Ω.toFinset) := by
          rw [add_le_iff_nonpos_right, sub_nonpos]
          refine (div_le_div_iff₀ ?_ ?_).mpr ?_
          · simp only [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hΩ_nonzero
          · simp only [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hB_nonzero
          · rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
            apply Nat.mul_le_mul_left
            rw [← Ω_card]
            exact Finset.card_le_card (Finset.subset_univ B)
      have cap_le : (@Nat.cast ℚ _ (A.toSet ∩ (B.toSet)ᶜ).toFinset.card) / ↑(#Ω.toFinset) ≤ ↑(B.toSet)ᶜ.toFinset.card / ↑(#Ω.toFinset) := by
        rw [div_le_div_iff_of_pos_right]
        simp only [Set.toFinset_inter, toFinset_coe, Set.toFinset_compl, Nat.cast_le]
        · refine card_le_card ?_
          exact inter_subset_right
        · simp only [Nat.cast_pos]
          exact Nat.zero_lt_of_ne_zero hΩ_nonzero
      rw [compl_card] at cap_le
      exact add_le.trans cap_le
    · suffices (((A ∩ B).card : ℚ) / (B.card : ℚ) - (A.card : ℚ) / (Ω.toFinset.card : ℚ)) * B.card ≤ (1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ)) * B.card by
        rwa [mul_le_mul_right (by rw [Nat.cast_pos]; exact Nat.zero_lt_of_ne_zero hB_nonzero)] at this
      rw [sub_mul, tsub_le_iff_right, ← add_mul]
      rw [div_mul, div_self (by simp_all only [ne_eq, Rat.natCast_eq_zero, not_false_eq_true]), div_one]
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
        · simp only [le_add_neg_iff_add_le, zero_add, Nat.cast_le]
          exact hAB
        · simp only [sub_nonneg]
          rw [div_le_iff₀ (by rw [Nat.cast_pos]; exact Nat.zero_lt_of_ne_zero hΩ_nonzero), one_mul, Nat.cast_le]
          rw [← Ω_card]
          exact Finset.card_le_card (Finset.subset_univ B)
      · right
        rw [mul_comm, le_mul_iff_one_le_right (by rw [Nat.cast_pos]; exact Nat.zero_lt_of_ne_zero hB_nonzero)]
        rw [sub_add_eq_add_sub, add_sub_assoc, le_add_iff_nonneg_right, sub_nonneg]
        simp only [not_le] at hAB
        rw [div_le_div_iff_of_pos_right (by rw [Nat.cast_pos]; exact Nat.zero_lt_of_ne_zero hΩ_nonzero), Nat.cast_le]
        exact Nat.le_of_lt hAB
  suffices 1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ) ≤ (c : ℚ) / (Grep.size : ℚ) by exact cond_bound.trans this
  clear cond_bound A

  by_cases hG_size : Grep.size ≤ 2 * σ.size
  · suffices 1 ≤ (c : ℚ) / (Grep.size : ℚ) by
      have prob_prop : 1- (@Nat.cast ℚ _ (B.card)) / Ω.toFinset.card ≤ 1 := by
        simp only [Set.toFinset_card, Fintype.card_ofFinset, tsub_le_iff_right, le_add_iff_nonneg_right]
        apply div_nonneg <;> simp only [Nat.cast_nonneg]
      exact prob_prop.trans this
    refine (one_le_div₀ ?_).mpr ?_
    · by_contra hG_zero
      simp only [Nat.cast_pos, not_lt, nonpos_iff_eq_zero] at hG_zero
      have : Ω.toFinset.card = 0 := by sorry
      exact hΩ_nonzero this
    · simp only [Nat.cast_max, Nat.cast_pow, Nat.cast_add, le_sup_iff, Nat.cast_le, c]
      right; exact hG_size
  · have hG_nzero : ¬Grep.size = 0 := by
      intro hG_zero
      rw [hG_zero] at hG_size
      simp only [zero_le, not_true_eq_false] at hG_size
    have hG_size' : σ.size < Grep.size := by
      have : σ.size ≤ 2 * σ.size := by
        apply Nat.le_mul_of_pos_left
        simp only [Nat.ofNat_pos]
      simp only [not_le] at hG_size
      exact lt_of_le_of_lt this hG_size
    suffices 1 - (@Nat.cast ℚ _ B.card) / Ω.toFinset.card ≤ 2 * (Frep.size + F'rep.size) ^ 2 / (Grep.size) by
      have hc_ge :2 * (@Nat.cast ℚ _ Frep.size + F'rep.size) ^ 2 / (Grep.size) ≤ c / Grep.size := by
        refine (div_le_div_iff_of_pos_right ?_).mpr ?_
        · simp only [Nat.cast_pos]
          exact Nat.zero_lt_of_ne_zero hG_nzero
        · sorry
          -- simp only [Nat.cast_max, Nat.cast_pow, Nat.cast_add, le_sup_iff, c]
          -- left; rw [← hFrep₁, hFrep₂, ← hF'rep₁,  hF'rep₂]
      exact this.trans hc_ge
    rw [← compl_card]
    suffices (@Nat.cast ℚ _ (B.toSet)ᶜ.toFinset.card) / Ω.toFinset.card ≤ ((Frep.size - σ.size) * (F'rep.size - σ.size) + (F'rep.size - σ.size) ^ 2) / (Grep.size - σ.size) by
      have simp_calc : ((@Nat.cast ℚ _ Frep.size - σ.size) * (F'rep.size - σ.size) + (F'rep.size - σ.size) ^ 2) / (Grep.size - σ.size) ≤ 2 * (Frep.size + F'rep.size) ^ 2 / (Grep.size) := by
        have calc₁ : (@Nat.cast ℚ _ Frep.size - σ.size) * (F'rep.size - σ.size) + (F'rep.size - σ.size) ^ 2 ≤ (Frep.size + F'rep.size) ^ 2 := by
          have hFrep_size : σ.size ≤ Frep.size := by
            rw [← Frep.type_verts_card_eq]
            simp [LabeledGraph.size]
            exact set_fintype_card_le_univ Frep.type_verts
          have hF'rep_size : σ.size ≤ F'rep.size := by
            rw [← F'rep.type_verts_card_eq]
            simp [LabeledGraph.size]
            exact set_fintype_card_le_univ F'rep.type_verts
          rw [← Nat.cast_sub hFrep_size, ← Nat.cast_sub hF'rep_size]
          rw [← Nat.cast_mul, ← Nat.cast_pow, ← Nat.cast_add]
          rw [← Nat.cast_add, ← Nat.cast_pow, Nat.cast_le]
          calc
            (Frep.size - σ.size) * (F'rep.size - σ.size) + (F'rep.size - σ.size) ^ 2
                = Frep.size * F'rep.size - σ.size * Frep.size - σ.size * F'rep.size + σ.size ^ 2 + F'rep.size ^ 2 - 2 * σ.size * F'rep.size + σ.size ^ 2 := by sorry
            _ ≤ Frep.size * F'rep.size + σ.size ^ 2 +  F'rep.size ^ 2 + σ.size ^ 2 := by
              sorry
            _ ≤ (Frep.size + F'rep.size) ^ 2 := by
              sorry

        suffices (@Nat.cast ℚ _ Frep.size + F'rep.size) ^ 2 / (Grep.size - σ.size) ≤ 2 * (Frep.size + F'rep.size) ^ 2 / (Grep.size) by
          have calc₃ : ((@Nat.cast ℚ _ Frep.size - σ.size) * (F'rep.size - σ.size) + (F'rep.size - σ.size) ^ 2) / (Grep.size - σ.size) ≤ (Frep.size + F'rep.size) ^ 2 / (Grep.size - σ.size) := by
            refine (div_le_div_iff_of_pos_right ?_).mpr calc₁
            simp_all only [sub_pos, Nat.cast_lt, not_le]
          have := calc₃.trans this
          exact this
        refine (div_le_div_iff₀ ?_ ?_).mpr ?_
        · simp only [sub_pos, Nat.cast_lt]
          exact hG_size'
        · simp only [Nat.cast_pos]
          exact Nat.zero_lt_of_ne_zero hG_nzero
        · rw [mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · rw [← Nat.cast_sub (by sorry)]
            rw [← Nat.cast_ofNat, ← Nat.cast_mul, Nat.cast_le]
            sorry
          · rw [← Nat.cast_add]
            apply sq_nonneg
      exact this.trans simp_calc
    sorry

example {E : Type} (W : Set E) (A B : Finset W) (hB : W = ∅) : A ≠ B := by
  refine ne_of_lt ?_
  simp only [lt_eq_subset]
  -- refine (ssubset_iff_of_subset ?_).mpr ?_
  sorry
  -- exact inter_subset_left

example (A B C : ℕ) : A ≤ 2 * A := by
  refine Nat.le_mul_of_pos_left A ?_
  -- exact Nat.div_div_eq_div_mul A B C
  -- refine Nat.div_mul_right_comm ?_ C
  -- refine Nat.mul_div_assoc A ?_
  -- exact eq_comm
  -- refine Nat.div_le_div_right ?_
  -- refine Nat.le_mul_of_pos_left A ?_
  -- exact Nat.le_mul_self A
  sorry

example (A B C D : ℚ) (h : A ≤ B) : 0 ≤ A ^ 2 := by
  -- exact sq_nonneg A
  -- refine mul_le_mul_of_nonneg_left h ?_
  -- refine (Rat.le_iff_sub_nonneg A B).mpr ?_
  -- refine (one_le_div₀ ?_).mpr ?_
  -- exact inv_inj
  -- exact Eq.symm (mul_inv A B)
  -- exact sub_eq_zero
  -- exact sq_nonneg A
  -- refine div_nonneg ?_ ?_
  -- exact le_mul_of_one_le_left hA rfl
  -- exact mul_le_mul_of_nonneg_right rfl hA
  -- exact Rat.mul_nonneg rfl hA
  -- refine mul_le_mul_of_nonneg_left hA ?_
  -- refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  sorry
  -- exact div_div_eq_mul_div A B C
  -- exact neg_mul_comm A B
  -- exact Rat.mul_nonneg hA hB
  -- refine Eq.symm (CancelDenoms.sub_subst ?_ ?_)
  -- refine (div_le_div_iff_of_pos_right ?_).mpr ?_
  -- exact Eq.symm (neg_sub B A)
  -- simp only [le_sub_self_iff, Left.nonneg_neg_iff]
  -- exact le_mul_iff_one_le_right h
  -- exact Rat.le_iff_sub_nonneg A B

-- theorem flagListDensity_prod_approx
--     (Fl : FlagList σ t Vl)
--     : ∃ k, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
--     |flagListDensity Fl G - ∏ i ∈ Finset.univ, flagDensity₁ (Fl i) G| ≤ (∑ i ∈ Finset.univ, (Fl i).out.size) ^ k / G.out.size
--   := by
--   use 2
--   intro W _ _ G
--   let Vs := Fin t → Finset W
--   let Ω : Finset Vs := { Vs : Vs | ∀ i , (Vs i).card = (Fl i).out.size ∧ ∀ i, G.out.type_verts ⊆ (Vs i).toSet }
--   let B : Finset Vs := { Vs : Vs | ∀ i j, i ≠ j → Disjoint (Vs i) (Vs j) }
--   let B_c : Finset Vs := { Vs : Vs | ¬(∀ i j, i ≠ j → Disjoint (Vs i) (Vs j)) }
--   let B_c_ij : Fin t → Fin t → Finset Vs := fun i j => { Vs : Vs | ¬ Disjoint (Vs i) (Vs j) }
--   have : B_c.card ≤ ∑ i : Fin t, ∑ j : Fin t, (B_c_ij i j).card := sorry
--   sorry
