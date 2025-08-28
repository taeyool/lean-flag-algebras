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

theorem flagListDensity_prod_approx
    (Fl : FlagList σ t Vl)
    : ∃ k, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
    |flagListDensity Fl G - ∏ i ∈ Finset.univ, flagDensity₁ (Fl i) G| ≤ (∑ i ∈ Finset.univ, (Fl i).out.size) ^ k / G.out.size
  := by
  use 2
  intro W _ _ G
  let Vs := Fin t → Finset W
  let Ω : Finset Vs := { Vs : Vs | ∀ i , (Vs i).card = (Fl i).out.size ∧ ∀ i, G.out.type_verts ⊆ (Vs i).toSet }
  let B : Finset Vs := { Vs : Vs | ∀ i j, i ≠ j → Disjoint (Vs i) (Vs j) }
  let B_c : Finset Vs := { Vs : Vs | ¬(∀ i j, i ≠ j → Disjoint (Vs i) (Vs j)) }
  let B_c_ij : Fin t → Fin t → Finset Vs := fun i j => { Vs : Vs | ¬ Disjoint (Vs i) (Vs j) }
  have : B_c.card ≤ ∑ i : Fin t, ∑ j : Fin t, (B_c_ij i j).card := sorry
  sorry

def cast_iso
    {σ : FlagType T} {G : LabeledGraph σ V} {F F₁ F₂ : LabeledSubgraph σ G}
    (h_eq : F₁ = F₂) (h_iso : F₁.coe ≃f F.coe) : F₂.coe ≃f F.coe :=
  by
  rw [h_eq] at h_iso
  exact h_iso

theorem flagListDensity₂_prod_approx
    (F : Flag σ V) (F' : Flag σ U)
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    : ∃ c ≥ 0, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
    |flagDensity₂ F F' G - flagDensity₁ F G * flagDensity₁ F' G| ≤ c / G.out.size
  := by
  use (F.out.size + F'.out.size) ^ 2
  constructor; (apply sq_nonneg)
  intro W _ _ G
  let ⟨Frep, hFrep₁⟩ := Quotient.exists_rep F
  let ⟨F'rep, hF'rep₁⟩ := Quotient.exists_rep F'
  let ⟨Grep, hGrep₁⟩ := Quotient.exists_rep G
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F G, ← subflagDensity_eq_flagListDensity F' G]
  rw [← hFrep₁, ← hF'rep₁, ← hGrep₁]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂ Frep F'rep Grep]
  dsimp [subflagDensity, labeledSubgraphDensityLifted]
  have hFrep₂ : (⟦Frep⟧ : Quotient (labeledGraphSetoid σ V)).out.size = Frep.size := rfl
  have hF'rep₂ : (⟦F'rep⟧ : Quotient (labeledGraphSetoid σ U)).out.size = F'rep.size := rfl
  have hGrep₂ : (⟦Grep⟧ : Quotient (labeledGraphSetoid σ W)).out.size = Grep.size := rfl
  rw [hFrep₂, hF'rep₂, hGrep₂]

  let free_Grep := Finset.univ \ Grep.type_verts.toFinset
  have h_free_Grep : free_Grep.card = Grep.size - σ.size := by
    simp_all only [free_Grep]
    rw [← Grep.type_verts_card_eq, Finset.card_sdiff] <;> try simp only [subset_univ]
    simp only [card_univ, Set.toFinset_card]; rfl
  let free_Frep := Finset.univ \ Frep.type_verts.toFinset
  have h_free_Frep : free_Frep.card = Frep.size - σ.size := by
    simp_all only [free_Frep]
    rw [← Frep.type_verts_card_eq, Finset.card_sdiff] <;> try simp only [subset_univ]
    simp only [card_univ, Set.toFinset_card]; rfl
  let free_F'rep := Finset.univ \ F'rep.type_verts.toFinset
  have h_free_F'rep : free_F'rep.card = F'rep.size - σ.size := by
    simp_all only [free_F'rep]
    rw [← F'rep.type_verts_card_eq, Finset.card_sdiff] <;> try simp only [subset_univ]
    simp only [card_univ, Set.toFinset_card]; rfl

  let Ω := { v : Finset W × Finset W | (v.1.card = Frep.size ∧ Grep.type_verts ⊆ v.1) ∧ (v.2.card = F'rep.size ∧ Grep.type_verts ⊆ v.2)}
  let h_Ω (w : Finset W × Finset W) : w ∈ Ω → w.1 = w.1 \ Grep.type_verts.toFinset ∧ w.2 = w.2 \ Grep.type_verts.toFinset := by
    intro h
    simp only [Set.mem_setOf_eq, Ω] at h
    constructor
    · nth_rw 1 [← sdiff_union_inter w.1 Grep.type_verts.toFinset]


      sorry
    · sorry
  let A : Finset Ω := { v | by
    obtain ⟨⟨v₁, v₂⟩, h⟩ := v
    exact Nonempty ((inducedLabeledSubgraph Grep v₁ h.1.2).coe ≃f Frep) ∧ Nonempty ((inducedLabeledSubgraph Grep v₂ h.2.2).coe ≃f F'rep) }
  let B : Finset Ω := { v | by
    obtain ⟨⟨v₁, v₂⟩, h⟩ := v
    exact (v₁ \ Grep.type_verts.toFinset) ∩ (v₂ \ Grep.type_verts.toFinset) = ∅ }
  have P₁ : labeledSubgraphDensity Frep Grep * labeledSubgraphDensity F'rep Grep
    = A.card / Ω.toFinset.card := by
    dsimp [labeledSubgraphDensity]
    field_simp
    congr
    · dsimp [labeledSubgraphCount]
      rw [← Nat.cast_mul, Nat.cast_inj, ← Finset.card_product]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨⟨G₁, G₂⟩, h⟩
        let V_G₁_G₂ : Finset W × Finset W := (G₁.subgraph.verts.toFinset, G₂.subgraph.verts.toFinset)
        have h_V_G₁_G₂ : V_G₁_G₂ ∈ Ω := by
          simp only [Set.mem_setOf_eq, Ω, V_G₁_G₂]
          simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and] at h
          obtain ⟨⟨h_G₁_1, h_G₁_2⟩, ⟨h_G₂_1, h_G₂_2⟩⟩ := h
          constructor
          · constructor
            · have := labeledGraphIso_size_eq G₁.coe Frep (Classical.choice h_G₁_2)
              simp only [Set.toFinset_card, Fintype.card_ofFinset]
              simp [LabeledGraph.size] at this
              exact this
            · simp only [Set.coe_toFinset]
              exact labeledSubgraph_contain_type_verts Grep G₁
          · constructor
            · have := labeledGraphIso_size_eq G₂.coe F'rep (Classical.choice h_G₂_2)
              simp only [Set.toFinset_card, Fintype.card_ofFinset]
              simp [LabeledGraph.size] at this
              exact this
            · simp only [Set.coe_toFinset]
              exact labeledSubgraph_contain_type_verts Grep G₂
        use ⟨V_G₁_G₂, h_V_G₁_G₂⟩
        simp_all only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and, Set.coe_setOf, Set.mem_setOf_eq, Ω, A]
        obtain ⟨⟨h_G₁_1, h_G₁_2⟩, ⟨h_G₂_1, h_G₂_2⟩⟩ := h
        obtain ⟨⟨h_G₁_3, h_G₁_4⟩, ⟨h_G₂_3, h_G₂_4⟩⟩ := h_V_G₁_G₂
        constructor
        · apply Nonempty.intro
          let iso_G₁_F := Classical.choice h_G₁_2
          have iso_G₁_G₁' : G₁.coe ≃f (inducedLabeledSubgraph Grep V_G₁_G₂.1 h_G₁_4).coe := by
            rw [inducedLabeledSubgraph_eq h_G₁_1]
            apply LabeledGraphIso.labeledSubgraphIso_eq
            congr!
            simp only [Set.coe_toFinset, V_G₁_G₂]
          exact iso_G₁_G₁'.symm.trans iso_G₁_F
        · apply Nonempty.intro
          let iso_G₂_F' := Classical.choice h_G₂_2
          have iso_G₂_G₂' : G₂.coe ≃f (inducedLabeledSubgraph Grep V_G₁_G₂.2 h_G₂_4).coe := by
            rw [inducedLabeledSubgraph_eq h_G₂_1]
            apply LabeledGraphIso.labeledSubgraphIso_eq
            congr!
            simp only [Set.coe_toFinset, V_G₁_G₂]
          exact iso_G₂_G₂'.symm.trans iso_G₂_F'
      · constructor
        · intro ⟨⟨v1_1, v1_2⟩, h1⟩ ⟨⟨v2_1, v2_2⟩, h2⟩ h
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, Set.toFinset_inj,]
          simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, true_and] at h1 h2
          obtain ⟨h₁, h₂⟩ := h
          obtain ⟨⟨h1_v₁_1, h1_v₁_2⟩, ⟨h1_v₂_1, h1_v₂_2⟩⟩ := h1
          obtain ⟨⟨h2_v₁_1, h2_v₁_2⟩, ⟨h2_v₂_1, h2_v₂_2⟩⟩ := h2
          constructor
          · exact labeledSubgraph_eq_from_subgraph_eq (inducedSubgraph_eq_verts h1_v₁_1 h2_v₁_1 h₁)
          · exact labeledSubgraph_eq_from_subgraph_eq (inducedSubgraph_eq_verts h1_v₂_1 h2_v₂_1 h₂)
        · intro ⟨⟨⟨v1, v2⟩, hΩ⟩, hA⟩
          obtain ⟨⟨h_v1_1, h_v1_2⟩, ⟨h_v2_1, h_v2_2⟩⟩ := hΩ
          simp only [mem_filter, mem_univ, true_and, A] at hA
          let G₁ := inducedLabeledSubgraph Grep v1 h_v1_2
          let G₂ := inducedLabeledSubgraph Grep v2 h_v2_2
          use ⟨(G₁, G₂), by
            simp only [Set.toFinset_setOf, mem_product, mem_filter, mem_univ, inducedLabeledSubgraph_isInduced, true_and, G₁, G₂]
            exact hA⟩
          simp only [inducedLabeledSubgraph_verts, toFinset_coe, G₁, G₂]
    · rw [← Nat.cast_mul, Nat.cast_inj]
      -- I don't know why just using `rw` here doesn't work
      calc
        (Grep.size - σ.size).choose (Frep.size - σ.size) * (Grep.size - σ.size).choose (F'rep.size - σ.size)
          = (free_Grep.card).choose (free_Frep.card) * (free_Grep.card).choose (free_F'rep.card) := by rw [h_free_Grep, h_free_Frep, h_free_F'rep]
        _ = (free_Grep.card).choose (free_Frep.card) * (free_Grep.card).choose (free_F'rep.card) := rfl
      rw [← comb_card free_Grep free_Frep.card, ← comb_card free_Grep free_F'rep.card, ← Finset.card_product]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨⟨S₁, S₂⟩, h⟩
        use (S₁ ∪ Grep.type_verts.toFinset, S₂ ∪ Grep.type_verts.toFinset)
        simp only [mem_filter, mem_univ, Set.mem_setOf_eq, true_and, Ω, coe_union, Set.coe_toFinset, Set.subset_union_right, and_true]
        simp [combinations] at h
        obtain ⟨⟨h_S₁_1, h_S₁_2⟩, ⟨h_S₂_1, h_S₂_2⟩⟩ := h
        constructor
        · rw [Finset.card_union, h_S₁_2, h_free_Frep, ← Grep.type_verts_card_eq]
          simp only [Set.toFinset_card]
          have : (S₁ ∩ Grep.type_verts.toFinset).card = 0 := by
            simp [free_Grep] at h_S₁_1
            simp only [card_eq_zero]
            apply Finset.eq_empty_of_forall_notMem
            intro x hx
            simp only [mem_inter, Set.mem_toFinset] at hx
            obtain ⟨hx₁, hx₂⟩ := hx
            have := h_S₁_1 hx₁
            simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at this
            exact this hx₂
          rw[this, tsub_zero]
          apply Nat.sub_add_cancel
          rw [Grep.type_verts_card_eq, ← Frep.type_verts_card_eq]
          simp only [LabeledGraph.size]
          exact set_fintype_card_le_univ Frep.type_verts
        · rw [Finset.card_union, h_S₂_2, h_free_F'rep, ← Grep.type_verts_card_eq]
          simp only [Set.toFinset_card]
          have : (S₂ ∩ Grep.type_verts.toFinset).card = 0 := by
            simp [free_Grep] at h_S₂_1
            simp only [card_eq_zero]
            apply Finset.eq_empty_of_forall_notMem
            intro x hx
            simp only [mem_inter, Set.mem_toFinset] at hx
            obtain ⟨hx₁, hx₂⟩ := hx
            have := h_S₂_1 hx₁
            simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at this
            exact this hx₂
          rw[this, tsub_zero]
          apply Nat.sub_add_cancel
          rw [Grep.type_verts_card_eq, ← F'rep.type_verts_card_eq]
          simp only [LabeledGraph.size]
          exact set_fintype_card_le_univ F'rep.type_verts
      · constructor
        · intro ⟨⟨s1_1, s1_2⟩, h1⟩ ⟨⟨s2_1, s2_2⟩, h2⟩ h
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
          obtain ⟨h₁, h₂⟩ := h
          simp only [combinations, mem_product, mem_filter, mem_powerset] at h1 h2
          obtain ⟨⟨h1_s1_1, h1_s1_2⟩, ⟨h1_s2_1, h1_s2_2⟩⟩ := h1
          obtain ⟨⟨h2_s1_1, h2_s1_2⟩, ⟨h2_s2_1, h2_s2_2⟩⟩ := h2
          constructor
          · have h_S1_1 : Disjoint s1_1 Grep.type_verts.toFinset := by
              refine disjoint_iff_inter_eq_empty.mpr ?_
              dsimp [free_Grep] at h1_s1_1
              apply Finset.eq_empty_of_forall_notMem
              intro x hx
              simp only [mem_inter, Set.mem_toFinset] at hx
              obtain ⟨hx₁, hx₂⟩ := hx
              have := h1_s1_1 hx₁
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at this
              exact this hx₂
            have h_S2_1 : Disjoint s2_1 Grep.type_verts.toFinset := by
              refine disjoint_iff_inter_eq_empty.mpr ?_
              dsimp [free_Grep] at h2_s1_1
              apply Finset.eq_empty_of_forall_notMem
              intro x hx
              simp only [mem_inter, Set.mem_toFinset] at hx
              obtain ⟨hx₁, hx₂⟩ := hx
              have := h2_s1_1 hx₁
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at this
              exact this hx₂
            rw [← union_sdiff_cancel_right h_S1_1, ← union_sdiff_cancel_right h_S2_1, h₁]
          · have h_S1_2 : Disjoint s1_2 Grep.type_verts.toFinset := by
              refine disjoint_iff_inter_eq_empty.mpr ?_
              dsimp [free_Grep] at h1_s2_1
              apply Finset.eq_empty_of_forall_notMem
              intro x hx
              simp only [mem_inter, Set.mem_toFinset] at hx
              obtain ⟨hx₁, hx₂⟩ := hx
              have := h1_s2_1 hx₁
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at this
              exact this hx₂
            have h_S2_2 : Disjoint s2_2 Grep.type_verts.toFinset := by
              refine disjoint_iff_inter_eq_empty.mpr ?_
              dsimp [free_Grep] at h2_s2_1
              apply Finset.eq_empty_of_forall_notMem
              intro x hx
              simp only [mem_inter, Set.mem_toFinset] at hx
              obtain ⟨hx₁, hx₂⟩ := hx
              have := h2_s2_1 hx₁
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at this
              exact this hx₂
            rw [← union_sdiff_cancel_right h_S1_2, ← union_sdiff_cancel_right h_S2_2, h₂]
        · intro ⟨⟨V₁, V₂⟩, h⟩
          simp only [mem_filter, mem_univ, Set.mem_setOf_eq, true_and, Ω] at h
          use ⟨(V₁ \ Grep.type_verts.toFinset, V₂ \ Grep.type_verts.toFinset), by
            simp only [combinations, mem_product, mem_filter, mem_powerset, free_Grep, free_Frep, free_F'rep]
            constructor <;> constructor
            · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
              exact subset_univ V₁
            · rw [Finset.card_sdiff, Set.toFinset_card]
              · rw [h.1.1, h_free_Frep, ← Grep.type_verts_card_eq]
              · simp only [Set.toFinset_subset]
                exact h.1.2
            · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
              exact subset_univ V₂
            · rw [Finset.card_sdiff, Set.toFinset_card]
              · rw [h.2.1, h_free_F'rep, ← Grep.type_verts_card_eq]
              · simp only [Set.toFinset_subset]
                exact h.2.2 ⟩
          simp only [sdiff_union_self_eq_union, Subtype.mk.injEq, Prod.mk.injEq, union_eq_left, Set.toFinset_subset]
          exact ⟨h.1.2, h.2.2⟩

  have P₂ : labeledSubgraphListDensity (labeledGraphPairToList Frep F'rep) Grep = (A ∩ B).card / B.card := by
    dsimp [labeledSubgraphListDensity]
    congr
    · dsimp only [labeledSubgraphListCount]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨l, hl⟩
        simp [LabeledSubgraphList] at l
        use ⟨((l 0).subgraph.verts.toFinset, (l 1).subgraph.verts.toFinset), by
          simp only [Fin.isValue, Set.mem_setOf_eq, Set.toFinset_card, Fintype.card_ofFinset,
            Set.coe_toFinset, Ω]
          sorry⟩
        simp only [Fin.isValue, mem_inter, mem_filter, mem_univ, true_and, A, B]
        simp only [setOfLabeledSubgraphListIsoHl, predIsoLabeledHl, labeledGraphPairToList, LabeledSubgraphList.IsInduced,
          Set.coe_setOf, Set.toFinset_setOf, mem_filter, mem_univ, true_and] at hl
        obtain ⟨hl_ind, hl_iso, hl_disj⟩ := hl
        constructor <;> try constructor
        · specialize hl_iso 0
          simp only [Fin.isValue] at hl_iso
          obtain ⟨h_iso₀⟩ := hl_iso
          apply Nonempty.intro
          -- have h_iso₁ : (l 0).coe ≃f
          have := inducedLabeledSubgraph_eq (hl_ind 0)
          -- rw [← this]
          -- apply cast_iso
          sorry
        · sorry
        · sorry
      · constructor
        · intro x y h_eq
          simp at h_eq
          sorry
        · intro ⟨x, hx⟩
          sorry
    · simp only [labeledGraphPairToList]
      let r_list : Fin 2 → ℕ := fun i ↦
        (match i with
          | 0 => Frep.size - σ.size
          | 1 => F'rep.size - σ.size)
      have hB : B.card = multinomialCoefficient r_list free_Grep.card := by
        rw [← partition_card free_Grep r_list]
        apply Finset.card_eq_of_equiv
        refine Equiv.ofBijective ?_ ?_
        · intro ⟨⟨⟨w₁, w₂⟩, h₁⟩, h₂⟩
          let r : Fin 2 → Finset W := fun i ↦
            (match i with
              | 0 => w₁ \ Grep.type_verts.toFinset
              | 1 => w₂ \ Grep.type_verts.toFinset)
          use r
          simp only [Set.mem_setOf_eq, Ω] at h₁
          simp only [mem_filter, mem_univ, true_and, B] at h₂
          simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const,
            mem_filter, true_and]
          constructor <;> try constructor
          · intro i
            by_cases h : i = 0
            · simp only [h, Fin.isValue, r, r_list]
              constructor
              · intro x hx
                simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, free_Grep]
                simp only [mem_sdiff, Set.mem_toFinset] at hx
                exact Set.notMem_of_mem_diff hx
              · rw [Finset.card_sdiff (by simp only [Set.toFinset_subset]; exact h₁.1.2)]
                rw [h₁.1.1, ← Grep.type_verts_card_eq, Set.toFinset_card]
            · simp only [Fin.eq_one_of_ne_zero i h, Fin.isValue, r, r_list]
              constructor
              · intro x hx
                simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, free_Grep]
                simp only [mem_sdiff, Set.mem_toFinset] at hx
                exact Set.notMem_of_mem_diff hx
              · rw [Finset.card_sdiff (by simp only [Set.toFinset_subset]; exact h₁.2.2)]
                rw [h₁.2.1, ← Grep.type_verts_card_eq, Set.toFinset_card]
          · intro i j hij
            by_cases hi : i = 0 <;> by_cases hj : j = 0
            · simp_all only [Set.toFinset_card, Fintype.card_ofFinset, Fin.isValue,
              not_true_eq_false]
            · simp only [hi, Fin.isValue, Fin.eq_one_of_ne_zero j hj, r]
              exact disjoint_iff_inter_eq_empty.mpr h₂
            · simp only [hj, Fin.isValue, Fin.eq_one_of_ne_zero i hi, r]
              rw [Finset.inter_comm] at h₂
              exact disjoint_iff_inter_eq_empty.mpr h₂
            · simp_all only [Fin.eq_one_of_ne_zero i hi, Fin.eq_one_of_ne_zero j hj, not_true_eq_false]
          · intro i
            by_cases h : i = 0
            · simp only [h, Fin.isValue, r]
              intro x hx
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, free_Grep]
              simp only [mem_sdiff, Set.mem_toFinset] at hx
              exact Set.notMem_of_mem_diff hx
            · simp only [Fin.eq_one_of_ne_zero i h, Fin.isValue, r]
              intro x hx
              simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and, free_Grep]
              simp only [mem_sdiff, Set.mem_toFinset] at hx
              exact Set.notMem_of_mem_diff hx
        · constructor
          · intro ⟨⟨⟨w₁_1, w₁_2⟩, r₁⟩, h_r₁⟩ ⟨⟨⟨w₂_1, w₂_2⟩, r₂⟩, h_r₂⟩ h_eq
            simp only [Subtype.mk.injEq] at h_eq
            simp only [Subtype.mk.injEq, Prod.mk.injEq]
            have h1 := congrFun h_eq 0
            have h2 := congrFun h_eq 1
            simp only at h1 h2
            simp [Ω] at r₁ r₂
            constructor
            ·
              rw [← sdiff_union_inter w₁_1 Grep.type_verts.toFinset, ← sdiff_union_inter w₂_1 Grep.type_verts.toFinset]
              have h_w₁_1 : w₁_1 ∩ Grep.type_verts.toFinset = Grep.type_verts.toFinset := by
                refine inter_eq_right.mpr ?_
                simp only [Set.toFinset_subset]
                exact r₁.1.2
              have h_w₂_1 : w₂_1 ∩ Grep.type_verts.toFinset = Grep.type_verts.toFinset := by
                refine inter_eq_right.mpr ?_
                simp only [Set.toFinset_subset]
                exact r₂.1.2
              rw [h1, h_w₁_1, h_w₂_1]

            sorry
          · intro ⟨r, hr⟩
            sorry
      rw [hB, h_free_Grep]
      simp only [r_list]; rfl

  rw [P₁, P₂]

  have calc₁ : |((A ∩ B).card : ℚ) / (B.card : ℚ) - (A.card : ℚ) / (Ω.toFinset.card : ℚ)| ≤ 1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ) := by sorry

  have calc₂ : 1 - (B.card : ℚ) / (Ω.toFinset.card : ℚ) ≤ ((2 : ℚ) * ↑Frep.size * ↑F'rep.size) / ↑Grep.size := by
    sorry

  have calc₄ : 2 * Frep.size * F'rep.size ≤ (Frep.size + F'rep.size) ^ 2 := by
    ring_nf
    apply Nat.le_add_right_of_le (Nat.le_add_right_of_le (le_refl _))
  rw [← Nat.cast_le (α := ℚ)] at calc₄

  have calc₃ : ((2 : ℚ) * ↑Frep.size * ↑F'rep.size) / ↑Grep.size ≤ ((↑Frep.size + ↑F'rep.size) ^ 2) / ↑Grep.size := by
    refine (div_le_div_iff_of_pos_right ?_).mpr ?_
    · sorry
    · simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add] at calc₄
      exact calc₄

  exact (calc₁.trans calc₂).trans calc₃
