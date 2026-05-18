import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Powerset

/-! # Combinations: `ℓ`-element subsets of a finset

Shared utility providing `combinations V ℓ`, the finset of all `ℓ`-element subsets of `V`,
together with the cardinality identity `(combinations V ℓ).card = V.card.choose ℓ`. Used
throughout the flag-algebra development for counting induced/partitioned configurations.
-/

open Finset

/-- The finset of all subsets of `V` of size exactly `ℓ`. -/
def combinations [DecidableEq α] (V : Finset α) (ℓ : ℕ) : Finset (Finset α)
  := (V.powerset).filter fun W ↦ W.card = ℓ

/-- Inductive helper for `combinations_card`: counts `ℓ`-subsets of every `V' ⊆ V`. -/
theorem combinations_card_aux
    [DecidableEq α] (V : Finset α) (ℓ : ℕ) :
    ∀ V' ⊆ V, (combinations V' ℓ).card = V'.card.choose ℓ
  := by
  induction ℓ with
  | zero =>
    intro V' _
    simp [combinations, card_filter]
  | succ _ hindℓ =>
    refine induction_on' V ?_ ?_
    · intro V' hV'
      rw [subset_empty.mp hV']
      rfl
    · intro a S _ hSV haS hindS V' hV'
      by_cases haV' : a ∈ V'
      · let V'a := V'.erase a
        have hsub : V'a ⊆ S := subset_insert_iff.mp hV'
        have hcard : V'.card = V'a.card + 1 := (card_erase_add_one haV').symm
        have hadd : V' = insert a V'a :=
          (erase_eq_iff_eq_insert haV' fun a_1 ↦ haS (hsub a_1)).mp rfl
        rw [hcard, Nat.choose_succ_succ', add_comm (V'a.card.choose _),
          combinations, hadd, powerset_insert, filter_union, card_union_of_disjoint]
        · rw [← combinations, hindS V'a hsub]
          apply Nat.add_left_cancel_iff.mpr
          have := hindℓ V'a (fun ⦃a⦄ a_1 ↦ hSV (hsub a_1))
          rw [filter_image, ← this, combinations]
          refine card_nbij' (erase · a) (insert a) ?_ ?_ ?_ ?_ <;> intro T hT
          · simp only [coe_image, coe_filter, mem_powerset] at hT ⊢
            obtain ⟨Ta, ⟨hTaV'a, hTacard⟩, rfl⟩ := hT
            refine ⟨subset_trans (erase_insert_subset a Ta) hTaV'a, ?_⟩
            have : a ∉ Ta := fun h ↦ haS (hsub (hTaV'a h))
            rw [Finset.card_insert_of_notMem this] at hTacard
            rw [Finset.erase_insert this]
            omega
          · simp only [coe_filter, mem_powerset, Set.mem_setOf_eq] at hT
            obtain ⟨hTV'a, rfl⟩ := hT
            simp only [coe_image, coe_filter, mem_powerset, Set.mem_image, Set.mem_setOf_eq]
            use T
            refine ⟨⟨hTV'a, ?_⟩, rfl⟩
            rw [card_insert_of_notMem]
            exact fun x ↦ haS (hsub (hTV'a x))
          · simp only [coe_image, Set.mem_image] at hT
            apply insert_erase
            obtain ⟨Ta, ⟨_, rfl⟩⟩ := hT
            exact mem_insert_self a Ta
          · simp only [coe_filter, mem_powerset, erase_insert_eq_erase, erase_eq_self] at hT ⊢
            exact fun a_1 ↦ haS (hsub (hT.1 a_1))
        · apply disjoint_filter_filter
          intro T hT₁ hT₂ X hXT
          have hanX : a ∉ X :=
            notMem_of_mem_powerset_of_notMem (hT₁ hXT) fun a_1 ↦ haS (hsub a_1)
          have haX : a ∈ X := by
            obtain ⟨_, ⟨_, rfl⟩⟩ := mem_image.mp (hT₂ hXT)
            exact mem_insert_self a _
          contradiction
      · have hsub : V' ⊆ S := (subset_insert_iff_of_notMem haV').mp hV'
        exact hindS V' hsub

/-- The number of `ℓ`-element subsets of `V` equals `V.card.choose ℓ`. -/
theorem combinations_card
    [DecidableEq α] (V : Finset α) (ℓ : ℕ) : (combinations V ℓ).card = V.card.choose ℓ
  :=
  combinations_card_aux V ℓ _ subset_rfl
