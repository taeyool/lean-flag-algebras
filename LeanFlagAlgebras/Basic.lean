import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Nonempty


variable {α : Type*} [DecidableEq α]

open Finset

def combinations (V : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (V.powerset).filter fun W ↦ W.card = ℓ

theorem comb_card_aux (V : Finset α) (ℓ : ℕ) :
    ∀ V' ⊆ V, (combinations V' ℓ).card = V'.card.choose ℓ := by
  induction ℓ with
  | zero =>
    intro V' _
    simp [combinations, card_filter]
  | succ _ hindℓ =>
    refine induction_on' V ?_ ?_
    · intro V' hV'
      have : V' = ∅ := subset_empty.mp hV'
      rw [this]
      rfl
    · intro a S _ hSV haS hindS V' hV'
      by_cases haV' : a ∈ V'
      · let V'a := V'.erase a
        have hsub : V'a ⊆ S := subset_insert_iff.mp hV'
        have hcard : V'.card = V'a.card + 1 := Eq.symm (card_erase_add_one haV')
        have hadd : V' = insert a V'a :=
          (erase_eq_iff_eq_insert haV' fun a_1 ↦ haS (hsub a_1)).mp rfl
        rw [hcard, Nat.choose_succ_succ', add_comm (V'a.card.choose _)]
        rw [combinations, hadd, powerset_insert, filter_union, card_union_of_disjoint]
        · rw [← combinations, hindS V'a hsub]
          apply Nat.add_left_cancel_iff.mpr
          have := hindℓ V'a (fun ⦃a⦄ a_1 ↦ hSV (hsub a_1))
          rw [filter_image, ← this, combinations]
          refine card_nbij' (erase · a) (insert a) ?_ ?_ ?_ ?_
          · intro T hT; simp_all
            obtain ⟨Ta, ⟨hTaV'a, hTacard⟩, hiaTa⟩ := hT
            constructor
            · refine subset_trans ?_ hTaV'a
              rw [← hiaTa]
              exact erase_insert_subset a Ta
            · rw [hiaTa] at hTacard
              apply (@Nat.add_right_cancel _ 1)
              simp only [← hTacard, card_erase_add_one, ← hiaTa, mem_insert_self]
          · intro T hT
            rw [mem_filter] at hT
            obtain ⟨hTV'a, hTcard⟩ := hT
            rw [mem_image]; use T
            constructor
            · rw [mem_filter, ← hTcard]
              constructor
              · exact hTV'a
              · apply card_insert_of_not_mem
                rw [mem_powerset] at hTV'a
                exact fun a_1 ↦ haS (hsub (hTV'a a_1))
            · rfl
          · intro T hT; simp_all
            apply insert_erase
            obtain ⟨Ta, ⟨_, hTa⟩⟩ := hT
            rw [← hTa]
            exact mem_insert_self a Ta
          · intro T hT; simp_all
            exact fun a_1 ↦ haS (hsub (hT.1 a_1))
        · apply disjoint_filter_filter
          intro T hT₁ hT₂ X hXT
          have hanX : a ∉ X :=
            not_mem_of_mem_powerset_of_not_mem (hT₁ hXT) fun a_1 ↦ haS (hsub a_1)
          have haX : a ∈ X := by
            have := hT₂ hXT
            rw [mem_image] at this
            obtain ⟨_, ⟨_, hiaX⟩⟩ := this
            rw [← hiaX]
            apply mem_insert_self a
          contradiction
      · have hsub : V' ⊆ S := (subset_insert_iff_of_not_mem haV').mp hV'
        exact hindS V' hsub

theorem comb_card (V : Finset α) (ℓ : ℕ) : (combinations V ℓ).card = V.card.choose ℓ := by
  apply comb_card_aux V ℓ
  exact fun ⦃a⦄ a ↦ a

open SimpleGraph

noncomputable def subgraph_count {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (H : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  let iso_sub := { G' : G.Subgraph | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let f : iso_sub → Set W × Set (W × W) := fun G' => (G'.val.verts, { (u, v) | G'.val.Adj u v })
  have f_inj : Function.Injective f := by
    rintro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.val.verts = G2.val.verts := (Prod.ext_iff.mp h_eq).1
      exact Eq.to_iff (congrFun h_eq_verts u)
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact Eq.to_iff (congrFun h_eq_edges (u, v))
  have iso_sub_fintype : Fintype iso_sub := Fintype.ofInjective f f_inj
  (@Set.toFinset _ iso_sub iso_sub_fintype).card

noncomputable def subgraph_density {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (H : SimpleGraph V) (G : SimpleGraph W) : ℚ :=
  let iso_sub := { G' : G.Subgraph | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let f : iso_sub → Set W × Set (W × W) := fun G' => (G'.val.verts, { (u, v) | G'.val.Adj u v })
  have f_inj : Function.Injective f := by
    rintro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.val.verts = G2.val.verts := (Prod.ext_iff.mp h_eq).1
      exact Eq.to_iff (congrFun h_eq_verts u)
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact Eq.to_iff (congrFun h_eq_edges (u, v))
  let iso_sub_fintype : Fintype iso_sub := Fintype.ofInjective f f_inj
  let num_of_all_induced_subgraphs := (Fintype.card W).choose (Fintype.card V)
  (@Set.toFinset _ iso_sub iso_sub_fintype).card / num_of_all_induced_subgraphs

theorem subgraph_density_ge_0 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
          (H : SimpleGraph V) (G : SimpleGraph W)
          : 0 ≤ subgraph_density H G := by
  dsimp [subgraph_density]
  apply div_nonneg
  . let iso_sub := { G' : G.Subgraph | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
    let f : iso_sub → Set W × Set (W × W) := fun G' => (G'.val.verts, { (u, v) | G'.val.Adj u v })
    have f_inj : Function.Injective f := by
      rintro G1 G2 h_eq
      dsimp [f] at h_eq
      ext u v
      . have h_eq_verts : G1.val.verts = G2.val.verts := (Prod.ext_iff.mp h_eq).1
        exact Eq.to_iff (congrFun h_eq_verts u)
      . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
        exact Eq.to_iff (congrFun h_eq_edges (u, v))
    let iso_sub_fintype : Fintype iso_sub := Fintype.ofInjective f f_inj
    exact Nat.cast_nonneg' (@Set.toFinset _ iso_sub iso_sub_fintype).card
  . exact Nat.cast_nonneg' ((Fintype.card W).choose (Fintype.card V))

theorem subgraph_density_le_1 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
          (H : SimpleGraph V) (G : SimpleGraph W)
          : subgraph_density H G ≤ 1 := by
  dsimp [subgraph_density]
  let iso_sub := { G' : G.Subgraph | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let f : iso_sub → Set W × Set (W × W) := fun G' => (G'.val.verts, { (u, v) | G'.val.Adj u v })
  have f_inj : Function.Injective f := by
    rintro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.val.verts = G2.val.verts := (Prod.ext_iff.mp h_eq).1
      exact Eq.to_iff (congrFun h_eq_verts u)
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact Eq.to_iff (congrFun h_eq_edges (u, v))
  let iso_sub_fintype : Fintype iso_sub := Fintype.ofInjective f f_inj
  have h1 : (@Set.toFinset _ iso_sub iso_sub_fintype).card ≤ (Fintype.card W).choose (Fintype.card V) := by sorry
  have h2 : (Fintype.card W).choose (Fintype.card V) > 0 := by sorry
  exact div_le_one_of_le (Nat.cast_le.mpr h1) (by sorry)
