import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card

variable {α : Type*} [DecidableEq α]

namespace Finset

def combinations (V : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (V.powerset).filter fun W ↦ W.card = ℓ

theorem comb_card_aux (V : Finset α) (ℓ : ℕ) :
    ∀ V' ⊆ V, (combinations V' ℓ).card = V'.card.choose ℓ := by
  induction ℓ
  · intro V' hVV'
    simp [combinations, card_filter]
  · refine induction_on' V ?_ ?_
    · intro V' hV'
      have : V' = ∅ := subset_empty.mp hV'
      rw [this]
      rfl
    · intro a S haV hSV haS hind V' hV'
      by_cases haV' : a ∈ V'
      · let V'a := V'.erase a
        have hsub : V'a ⊆ S := subset_insert_iff.mp hV'
        have hcard : V'.card = V'a.card + 1 := Eq.symm (card_erase_add_one haV')
        have hadd : V' = insert a V'a :=
          (erase_eq_iff_eq_insert haV' fun a_1 ↦ haS (hsub a_1)).mp rfl
        rw [combinations, hadd, powerset_insert, filter_union, card_union_of_disjoint]
        · rw [← combinations, hind V'a hsub]
          rw [filter_image]
          sorry
        · apply disjoint_filter_filter
          intro T hT₁ hT₂ X hXT
          have hanX : a ∉ X :=
            not_mem_of_mem_powerset_of_not_mem (hT₁ hXT) fun a_1 ↦ haS (hsub a_1)
          have haX : a ∈ X := by
            have := hT₂ hXT
            rw [mem_image] at this
            have ⟨_, ⟨_, hiaX⟩⟩ := this
            rw [← hiaX]
            apply mem_insert_self a
          contradiction
      · have hsub : V' ⊆ S := (subset_insert_iff_of_not_mem haV').mp hV'
        exact hind V' hsub

theorem comb_card (V : Finset α) (ℓ : ℕ) : (combinations V ℓ).card = V.card.choose ℓ := by
  apply comb_card_aux V ℓ
  exact fun ⦃a⦄ a ↦ a

end Finset

def p (M : SimpleGraph α) (N : SimpleGraph β) [DecidableRel M.Adj] [DecidableRel N.Adj] : ℚ :=
  sorry
