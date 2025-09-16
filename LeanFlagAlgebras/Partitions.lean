import Mathlib

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {t : ℕ}

/--
A `partition` of a `V` with respect to `r_list` is collection of parititons of subset of `V`. -/
def partitions (V : Finset α) (r_list : Fin t → ℕ)
    : Finset (Fin t → Finset α)
  := (Finset.univ : Finset (Fin t → Finset α)).filter fun p =>
      (∀ i, p i ⊆ V ∧ (p i).card = r_list i) ∧
      (∀ i j, i ≠ j → Disjoint (p i) (p j))

@[simp]
lemma partitions_empty_eq_of_isEmpty_of_eq_zero
    {r_list : Fin t → ℕ} (h : r_list = 0)
    : partitions (∅ : Finset α) r_list = {fun _ ↦ ∅}
  := by
  ext a; simp [partitions, h]; constructor <;> intro h₁
  · obtain ⟨h₁, -⟩ := h₁; funext; exact h₁ _
  · subst h₁; tauto

@[simp]
lemma partitions_of_isEmpty_of_nonzero
    {r_list : Fin t → ℕ} (h : r_list ≠ 0)
    : partitions (∅ : Finset α) r_list = ∅
  := by
  ext a; simp [partitions]; intro h₁
  by_contra h'; simp at h'
  match t with
  | 0 => rw [Matrix.zero_empty] at h; exact h (Matrix.empty_eq r_list)
  | 1 =>
    obtain ⟨h₂, h₃⟩ := h₁ 0; simp [h₂] at h₃
    apply h; funext x; rw [Fin.fin_one_eq_zero x, ← h₃]; rfl
  | t + 2 =>
    apply h; funext x; rw [Pi.zero_apply]
    obtain ⟨h₂, h₃⟩ := h₁ x; exact (h₂ ▸ h₃).symm

section One

lemma partitions_one_eq_biUnion_filter_eq_card
    {V : Finset α} {r_list : Fin 1 → ℕ} :
    partitions V r_list = (V.powerset.filter (·.card = r_list 0)).biUnion ({fun _ ↦ ·})
  := by
  ext f; simp [partitions]; constructor <;> intro h₁
  · obtain ⟨h₁, h₂⟩ := h₁.1 0
    use f 0, ⟨h₁, h₂⟩
    funext; congr; exact Fin.fin_one_eq_zero _
  · obtain ⟨f, ⟨h₁, h₂⟩, rfl⟩ := h₁; simp [h₁, h₂, Fin.fin_one_eq_zero]

lemma partitions_one_card_eq_filter_eq_card
    {V : Finset α} {r_list : Fin 1 → ℕ} :
    (partitions V r_list).card = (V.powerset.filter (·.card = r_list 0)).card
  := by
  rw [partitions_one_eq_biUnion_filter_eq_card, Finset.card_biUnion] <;> simp
  intro s hs t ht h₁ u h₂ h₃
  simp at hs ht h₂ h₃ ⊢
  rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃ <;> try tauto
  subst h₂; exfalso; apply h₁
  rw [Finset.singleton_inj] at h₃
  apply congrFun at h₃; exact h₃ 0

/-- Alternative definition of `partitions`. -/
def partitions' (V : Finset α) (r_list : Fin t → ℕ) : Finset (Fin t → Finset α) :=
  inner t V r_list
where
  inner (t : ℕ) (V : Finset α) (r_list : Fin t → ℕ) : Finset (Fin t → Finset α) :=
  match t with
  | 0 => if r_list = 0 then {fun _ ↦ ∅} else ∅
  | t + 1 =>
    let possible_subsets : Finset (Finset α) := (V.powerset.filter (·.card = r_list (.last _)))
    possible_subsets.biUnion fun s ↦ -- `s` is the subset of `V` with size `r_list (.last _)`.
      (inner t (V \ s) (r_list ·.castSucc)).image fun f x ↦ if h : x < t then f ⟨x, h⟩ else s

lemma partitions_eq_partitions'_of_zero
    {V : Finset α} {r_list : Fin t → ℕ}
    : partitions V r_list = partitions' V r_list
  := by
  ext a; simp [partitions, partitions']
  induction t generalizing V
  case zero => simp!; exact Finset.insert_eq_self.mp rfl
  case succ t ih =>
  simp [partitions'.inner]
  constructor <;> intro h₁
  · sorry
  · obtain ⟨s₁, ⟨h₁, h₂⟩, f, h₃, rfl⟩ := h₁
    simp only
    obtain ⟨h₄, h₆⟩ := (ih f).mpr h₃; obtain h₅ := (h₄ · |>.2); obtain h₄ := (h₄ · |>.1)
    refine ⟨fun i ↦ ⟨?_, ?_⟩, fun i j h₇ ↦ ?_⟩
    · split
      · intro _ h; exact Finset.mem_sdiff.mp (h₄ _ h) |>.1
      · exact h₁
    · split
      · exact h₅ _
      · exact h₂ ▸ Fin.last_le_iff.mp (not_lt.mp (by assumption)) ▸ rfl
    · split
      · intro _ h₈ h₉; simp at h₈ h₉ ⊢; split at h₉
        · refine Finset.subset_empty.mp (h₆ _ _ (fun h ↦ h₇ ?_) h₈ h₉)
          rw [Fin.mk.injEq] at h; exact Fin.eq_of_val_eq h
        · exact Finset.subset_empty.mp <|
            Finset.disjoint_of_subset_left (h₄ _) Finset.sdiff_disjoint h₈ h₉
      · simp [Disjoint]; intro _ h₈ h₉; split at h₉
        · exact Finset.subset_empty.mp <|
            Finset.disjoint_of_subset_right (h₄ _) Finset.disjoint_sdiff h₈ h₉
        · omega

lemma partitions_card_eq_choose_mul_multinomial
    {V : Finset α} {r_list : Fin t → ℕ}
    : (partitions V r_list).card = V.card.choose (∑ x, r_list x) * Nat.multinomial .univ r_list
  := by
  induction t generalizing V
  case zero => simp [partitions]
  case succ t ih =>
  sorry
