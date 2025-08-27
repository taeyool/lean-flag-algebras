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

-- Version 1. define the single space, then use the product space

def SingleChoiceSpace
  (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) (i : Fin t) : Type _ :=
  { S : Finset V // S.card = (Fl i).out.size ∧ G.type_verts ⊆ S.toSet }
instance (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) (i : Fin t) : Fintype (SingleChoiceSpace Fl G i) := by
  apply Subtype.fintype

instance (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) (i : Fin t) : MeasurableSpace (SingleChoiceSpace Fl G i) :=
  sorry

instance (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) (i : Fin t) : Nonempty (SingleChoiceSpace Fl G i) := by
  dsimp [SingleChoiceSpace]
  let S := (Fl i).out.top.subgraph.verts.toFinset
  sorry

def P_single (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) (i : Fin t) : Measure (SingleChoiceSpace Fl G i) :=
  (PMF.uniformOfFintype (SingleChoiceSpace Fl G i)).toMeasure
instance P_single.isProbabilityMeasure (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) (i : Fin t) :
  IsProbabilityMeasure (P_single Fl G i) := by
  apply PMF.toMeasure.isProbabilityMeasure

def Ω (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) : Type _ := (i : Fin t) → SingleChoiceSpace Fl G i
instance measurableSpaceΩ (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) : MeasurableSpace (Ω Fl G) :=
  MeasurableSpace.pi

def P (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) : Measure (Ω Fl G) :=
  Measure.pi (fun i => P_single Fl G i)

instance P.isProbabilityMeasure (Fl : FlagList σ t Vl) (G : LabeledGraph σ V) :
  IsProbabilityMeasure (P Fl G) := sorry

-- Version 2. define the product space directly

def base_verts (G : LabeledGraph σ V) : Finset V := Finset.univ \ G.type_verts.toFinset
def r_list (Fl : LabeledGraphList σ t Vl) : Fin t → ℕ := fun i => (Fl i).size - σ.size

def SampleSpace (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V) : Type _ :=
  { parts : Fin t → Finset V // ∀ i, parts i ⊆ base_verts G ∧ ∀ i, (parts i).card = (r_list Fl) i ∧ ∀ i j, i ≠ j → Disjoint (parts i) (parts j)}

instance SampleSpace.fintype (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V) : Fintype (SampleSpace Fl G) := by
  apply Subtype.fintype

instance SampleSpace.measurableSpace (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V) : MeasurableSpace (SampleSpace Fl G) :=
  sorry

instance SampleSpace.nonempty (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V) : Nonempty (SampleSpace Fl G) := by
  sorry

theorem SampleSpace_eq_multinomialCoefficient
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V)
    : Fintype.card (SampleSpace Fl G) = multinomialCoefficient (r_list Fl) (G.size - σ.size):= by
  sorry

/- Lemma 2.3 -/

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

example (a b c d : ℚ) : (a / b) * (c / d) = (a * c) / (b * d) := by
  field_simp

theorem flagListDensity₂_prod_approx
    (F : Flag σ V) (F' : Flag σ U)
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

  let Ω := { v : Finset W × Finset W | (v.1.card = Frep.size ∧ Grep.type_verts ⊆ v.1) ∧ (v.2.card = F'rep.size ∧ Grep.type_verts ⊆ v.2)}
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
          simp at h
          simp only [Subtype.mk.injEq, Prod.mk.injEq]
          sorry
        · intro ⟨⟨V₁, V₂⟩, h⟩
          simp only [mem_filter, mem_univ, Set.mem_setOf_eq, true_and, Ω] at h
          use ⟨(V₁ \ Grep.type_verts.toFinset, V₂ \ Grep.type_verts.toFinset), by
            simp only [combinations, mem_product, mem_filter, mem_powerset, free_Grep, free_Frep, free_F'rep]
            constructor <;> constructor
            · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
              exact subset_univ V₁
            · rw [Finset.card_sdiff, Set.toFinset_card]
              · sorry
              · simp only [Set.toFinset_subset]
                exact h.1.2
            · refine sdiff_subset_sdiff ?_ fun ⦃a⦄ a ↦ a
              exact subset_univ V₂
            · sorry
            ⟩
          simp only [sdiff_union_self_eq_union, Subtype.mk.injEq, Prod.mk.injEq, union_eq_left, Set.toFinset_subset]
          exact ⟨h.1.2, h.2.2⟩

  -- let Ω := (Finset.univ : Finset (Finset W × Finset W)).filter (fun v => (v.1.card = Frep.size ∧ Grep.type_verts ⊆ v.1) ∧ (v.2.card = F'rep.size ∧ Grep.type_verts ⊆ v.2))
  -- let A' := { v | ∃ (h : v ∈ Ω), true }
  -- let A := Ω.filter (fun v => Nonempty ((inducedLabeledSubgraph Grep v.1.toSet (by sorry)).coe ≃f Frep) ∧ Nonempty ((inducedLabeledSubgraph Grep v.2.toSet (by sorry)).coe ≃f F'rep))
  -- let B := Ω.filter (fun (v : Finset W × Finset W) => (v.1 \ Grep.type_verts.toFinset) ∩ (v.2 \ Grep.type_verts.toFinset) = ∅)

  have calc₁ : 2 * Frep.size * F'rep.size ≤ (Frep.size + F'rep.size) ^ 2 := by
    ring_nf
    apply Nat.le_add_right_of_le (Nat.le_add_right_of_le (le_refl _))
  rw [← Nat.cast_le (α := ℚ)] at calc₁
  have calc₂ : ((2 : ℚ) * ↑Frep.size * ↑F'rep.size) / ↑Grep.size ≤ ((↑Frep.size + ↑F'rep.size) ^ 2) / ↑Grep.size := by
    refine (div_le_div_iff_of_pos_right ?_).mpr ?_
    · sorry
    · simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add] at calc₁
      exact calc₁
  have calc₃ :  |labeledSubgraphListDensity (labeledGraphPairToList Frep F'rep) Grep -
      labeledSubgraphDensity Frep Grep * labeledSubgraphDensity F'rep Grep| ≤ ((2 : ℚ) * ↑Frep.size * ↑F'rep.size) / ↑Grep.size := by
    sorry
  exact calc₃.trans calc₂
