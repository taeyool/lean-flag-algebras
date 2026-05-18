import LeanFlagAlgebras.Utils.Combinations
import LeanFlagAlgebras.Utils.MultinomialCoefficient

/-! # Labeled partitions of a finset

Shared utility for the finset of ways to pick `t` pairwise-disjoint subsets of `V` with
prescribed sizes `r_list : Fin t → ℕ` (`partitions'`, an equivalent recursive `partitions''`,
and `partitions`). The headline result `partition_card` evaluates the count as
`multinomialCoefficient r_list V.card`. Used to count labeled vertex configurations.
-/

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {t : ℕ}

/--
A `partition` of a `V` with respect to `r_list` is collection of parititons of subset of `V`. -/
def partitions' (V : Finset α) (r_list : Fin t → ℕ)
    : Finset (Fin t → Finset α)
  := (Finset.univ : Finset (Fin t → Finset α)).filter fun p =>
      (∀ i, p i ⊆ V ∧ (p i).card = r_list i) ∧
      (∀ i j, i ≠ j → Disjoint (p i) (p j))

@[simp]
lemma partitions'_empty_eq_of_isEmpty_of_eq_zero
    {r_list : Fin t → ℕ} (h : r_list = 0)
    : partitions' (∅ : Finset α) r_list = {fun _ ↦ ∅}
  := by
  ext a; simp [partitions', h]; constructor <;> intro h₁
  · obtain ⟨h₁, -⟩ := h₁; funext; exact h₁ _
  · subst h₁; tauto

@[simp]
lemma partitions'_of_isEmpty_of_nonzero
    {r_list : Fin t → ℕ} (h : r_list ≠ 0)
    : partitions' (∅ : Finset α) r_list = ∅
  := by
  ext a; simp [partitions']; intro h₁
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

lemma partitions'_one_eq_biUnion_filter_eq_card
    {V : Finset α} {r_list : Fin 1 → ℕ} :
    partitions' V r_list = (V.powerset.filter (·.card = r_list 0)).biUnion ({fun _ ↦ ·})
  := by
  ext f; simp [partitions']; constructor <;> intro h₁
  · use f 0, h₁
    funext; congr; exact Fin.fin_one_eq_zero _
  · obtain ⟨f, ⟨h₁, h₂⟩, rfl⟩ := h₁; simp [h₁, h₂]

lemma partitions'_one_card_eq_filter_eq_card
    {V : Finset α} {r_list : Fin 1 → ℕ} :
    (partitions' V r_list).card = (V.powerset.filter (·.card = r_list 0)).card
  := by
  rw [partitions'_one_eq_biUnion_filter_eq_card, Finset.card_biUnion] <;> simp
  intro s hs t ht h₁
  grind only

/-- Alternative definition of `partitions'`. -/
def partitions'' (V : Finset α) (r_list : Fin t → ℕ) : Finset (Fin t → Finset α) :=
  inner t V r_list
where
  inner (t : ℕ) (V : Finset α) (r_list : Fin t → ℕ) : Finset (Fin t → Finset α) :=
  match t with
  | 0 => if r_list = 0 then {fun _ ↦ ∅} else ∅
  | t + 1 =>
    let possible_subsets : Finset (Finset α) := (V.powerset.filter (·.card = r_list (.last _)))
    possible_subsets.biUnion fun s ↦ -- `s` is the subset of `V` with size `r_list (.last _)`.
      (inner t (V \ s) (r_list ·.castSucc)).image fun f x ↦ if h : x < t then f ⟨x, h⟩ else s

/-- The filter-based `partitions'` and the recursive `partitions''` describe the same finset. -/
lemma partitions'_eq_partitions''
    {V : Finset α} {r_list : Fin t → ℕ}
    : partitions' V r_list = partitions'' V r_list
  := by
  ext f; simp [partitions', partitions'']
  induction t generalizing V
  case zero => simp!; exact Finset.insert_eq_self.mp rfl
  case succ t ih =>
  simp [partitions''.inner]
  constructor <;> intro h₁
  · obtain ⟨h₁, h₃⟩ := h₁; obtain h₂ := (h₁ · |>.2); obtain h₁ := (h₁ · |>.1)
    use f (.last _); simp only [h₁, h₂, true_and]
    use (f ·.castSucc); constructor
    · rw [← ih];
      refine ⟨fun i ↦ ⟨fun a h₄ ↦ ?_, ?_⟩, fun i j h₄ ↦ h₃ i.castSucc j.castSucc (by simp [h₄])⟩
      · refine Finset.mem_sdiff.mpr ⟨h₁ _ h₄, (h₃ _ _ ?_).notMem_of_mem_left_finset h₄⟩
        simp only [Fin.castSucc_ne_last, not_false_eq_true]
      · tauto
    · simp; ext; split
      · rfl
      · exact Fin.last_le_iff.mp (not_lt.mp (by assumption)) ▸ .rfl
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

-- lemma partitions'_card_eq_choose_mul_multinomial
--     {V : Finset α} {r_list : Fin t → ℕ}
--     : (partitions' V r_list).card = V.card.choose (∑ x, r_list x) * Nat.multinomial .univ r_list
--   := by
--   induction t generalizing V
--   case zero => simp [partitions']
--   case succ t ih =>
--   sorry

/- Above is a WIP. -/

lemma sum_eq_sum_plus_last
    (f : Fin (t + 1) → ℕ) : ∑ i : Fin (t + 1), f i = (∑ i : Fin t, f i.castSucc) + (f (Fin.last t))
  :=
  Fin.sum_univ_castSucc f

lemma prod_eq_prod_mul_last
    (f : Fin (t + 1) → ℕ) : ∏ i : Fin (t + 1), f i = (∏ i : Fin t, f i.castSucc) * (f (Fin.last t))
  :=
  Fin.prod_univ_castSucc f

/-- Variant of `partitions'` carrying the extra (derivable) hypothesis that the union of the
parts is contained in `V`, kept explicit for proof convenience. -/
def partitions [Fintype α] [DecidableEq α] (V : Finset α) (r_list : Fin t → ℕ)
    : Finset (Fin t → Finset α)
  := (Finset.univ : Finset (Fin t → Finset α)).filter (fun p =>
      (∀ i, p i ⊆ V ∧ (p i).card = r_list i) ∧
      (∀ i j, i ≠ j → Disjoint (p i) (p j)) ∧
      (Finset.univ : Finset (Fin t)).biUnion p ⊆ V) -- Actually, this can be derived from the first property, but it was included for the convenience of the proof.

/-- Append one entry to `r_list`, set to the leftover `n - ∑ r_list`, so the extended list
sums to `n` (see `extend_r_list.sum`). -/
def extend_r_list
    (n : ℕ) (r_list : Fin t → ℕ)
    : Fin (t + 1) → ℕ
  := by
  intro i
  if h : i.val < t then exact r_list ⟨i.val, h⟩
  else exact n - ∑ j : Fin t, r_list j

lemma extend_r_list.sum
    (n : ℕ) (r_list : Fin t → ℕ) (h_r_list : ∑ i, r_list i ≤ n)
    : ∑ i : Fin (t + 1), extend_r_list n r_list i = n
  := by
  rw [sum_eq_sum_plus_last]
  simp only [extend_r_list, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_last,
    lt_self_iff_false]
  exact Nat.add_sub_of_le h_r_list

lemma extend_r_list.factorial_prod
    (n : ℕ) (r_list : Fin t → ℕ)
    : ∏ i, ((extend_r_list n r_list) i).factorial = (∏ i, (r_list i).factorial) * (n - ∑ j : Fin t, r_list j).factorial
  := by
  rw [prod_eq_prod_mul_last]
  simp only [extend_r_list, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_last,
    lt_self_iff_false]

/-- Headline count: the number of labeled disjoint-size partitions of `V` equals
`multinomialCoefficient r_list V.card`. -/
theorem partition_card
    (V : Finset α) (r_list : Fin t → ℕ)
    : (partitions V r_list).card = multinomialCoefficient r_list V.card := by
  dsimp only [multinomialCoefficient]
  split
  next h =>
    induction t with
    | zero =>
        simp only [partitions, IsEmpty.forall_iff, ne_eq, Finset.univ_eq_empty,
          Finset.biUnion_empty, Finset.empty_subset, and_self, Finset.univ_unique,
          Finset.filter_true, Finset.card_singleton, Finset.prod_empty, Finset.sum_empty, tsub_zero, one_mul]
        rw [Nat.div_self (Nat.factorial_pos V.card)]
    | succ t ih =>
        let r_list' : Fin t → ℕ := fun i => r_list i.castSucc
        have h_r_list'₁ : ∑ i : Fin t, r_list' i ≤ V.card := by
          have : ∑ i, r_list' i ≤ ∑ i, r_list i := by
            dsimp only [r_list']
            rw [sum_eq_sum_plus_last, le_add_iff_nonneg_right]
            exact Nat.zero_le (r_list (Fin.last t))
          exact this.trans h
        have h_r_list'₂ : ∑ i, r_list i = ∑ j, r_list' j + r_list (Fin.last t) :=  sum_eq_sum_plus_last r_list
        have h_r_list'₃ : ∏ i, (r_list i).factorial = (∏ i, (r_list' i).factorial) * (r_list (Fin.last t)).factorial := by
          rw [prod_eq_prod_mul_last]
        specialize ih r_list' h_r_list'₁
        let rest_part (p : Fin t → Finset α) := V \ (Finset.univ : Finset (Fin t)).biUnion p
        have card_eq₁ : (partitions V r_list).card = (Fintype.card (Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t)))) := by
          apply Finset.card_eq_of_equiv
          let f : {x // x ∈ partitions V r_list} → {x // x ∈ (Finset.univ : Finset (Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t))))} := by
            intro ⟨p, hp⟩
            let p' : (Fin t) → Finset α := fun i => p i.castSucc
            have hp' : p' ∈ partitions V r_list' := by
              simp only [partitions, ne_eq, Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const, Finset.mem_filter, true_and] at hp
              obtain ⟨hp₁, hp₂, hp₃⟩ := hp
              simp only [partitions, Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const, Finset.mem_filter,
                true_and, p', r_list']
              refine ⟨fun i ↦ hp₁ i.castSucc, fun i j hij ↦ ?_, fun i ↦ hp₃ i.castSucc⟩
              rw [ne_eq, ← Fin.castSucc_inj] at hij
              exact hp₂ i.castSucc j.castSucc hij
            let r := p (Fin.last t)
            have hr : r ∈ combinations (rest_part p') (r_list (Fin.last t)) := by
              simp only [combinations, Finset.mem_filter, Finset.mem_powerset]
              simp only [partitions, ne_eq, Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const, Finset.mem_filter, true_and] at hp
              obtain ⟨hp₁, hp₂, hp₃⟩ := hp
              refine ⟨fun x hx₁ ↦ Finset.mem_sdiff.mpr ⟨hp₃ (Fin.last t) hx₁, ?_⟩, (hp₁ (Fin.last t)).2⟩
              simp only [p', Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
              intro i
              have hi : i.castSucc ≠ Fin.last t := by
                simp only [ne_eq, Fin.castSucc_ne_last, not_false_eq_true]
              specialize hp₂ i.castSucc (Fin.last t) hi
              by_contra hx₂
              dsimp [r] at hx₁
              simp only [disjoint_iff, Finset.inf_eq_inter, Finset.bot_eq_empty] at hp₂
              have : x ∈ p i.castSucc ∩ p (Fin.last t) := by
                simp only [Finset.mem_inter]
                exact ⟨hx₂, hx₁⟩
              exact Finset.notMem_empty x <| hp₂ ▸ this
            use ⟨⟨p', hp'⟩, ⟨r, hr⟩⟩
            simp only [Finset.mem_univ]
          have f_inj : Function.Injective f := by
            intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ h_eq
            simp only [Subtype.mk.injEq]
            simp only [f, Subtype.mk.injEq, Sigma.mk.injEq] at h_eq
            obtain ⟨h_p, h_r⟩ := h_eq
            funext i
            by_cases hi : i.val < t
            · exact funext_iff.mp h_p ⟨i, hi⟩
            · rw [Fin.eq_last_of_not_lt hi]
              rw [Subtype.heq_iff_coe_eq] at h_r
              · exact h_r
              · intro r
                simp_all only [not_lt, r_list', rest_part]
          have f_surj : Function.Surjective f := by
            intro ⟨⟨⟨p, hp⟩, ⟨r, hr⟩⟩, h⟩
            simp only [partitions, ne_eq, Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const, Finset.mem_filter, true_and] at hp
            obtain ⟨hp₁, hp₂, hp₃⟩ := hp
            simp only [combinations, Finset.mem_filter, Finset.mem_powerset] at hr
            obtain ⟨hr₁, hr₂⟩ := hr
            have hr₃ : rest_part p ⊆ V := by simp only [Finset.sdiff_subset, rest_part]
            let x : Fin (t + 1) → Finset α := fun i => if h : i.val < t then p ⟨i.val, h⟩ else r
            have hx : x ∈ partitions V r_list := by
              simp only [partitions, ne_eq, Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const, Finset.mem_filter, true_and]
              constructor <;> try constructor
              · intro i; dsimp [x]; split
                next hi => exact hp₁ ⟨i, hi⟩
                next hi =>
                  rw [Fin.eq_last_of_not_lt hi]
                  constructor
                  · exact fun ⦃a⦄ a_1 ↦ hr₃ (hr₁ a_1)
                  · exact hr₂
              · intro i j hij; dsimp [x]; split
                next hi =>
                  split
                  next hj =>
                    apply hp₂ ⟨i, hi⟩ ⟨j, hj⟩
                    simp only [Fin.mk.injEq]
                    exact fun h => hij (Fin.val_inj.mp h)
                  next hj =>
                    refine Finset.disjoint_left.mpr ?_
                    intro x hx₁ hx₂
                    have hx₃ : x ∈ rest_part p := hr₁ hx₂
                    simp_all only [Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_biUnion, not_exists, rest_part]
                next hi =>
                  split
                  next hj =>
                    refine Finset.disjoint_right.mpr ?_
                    intro x hx₁ hx₂
                    have hx₃ : x ∈ rest_part p := hr₁ hx₂
                    simp_all only [Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_biUnion, not_exists, rest_part]
                  next hj =>
                    exfalso
                    rw [Fin.eq_last_of_not_lt hi, Fin.eq_last_of_not_lt hj] at hij
                    exact hij rfl
              · intro i; dsimp [x]; split
                next hi => exact hp₃ ⟨i, hi⟩
                next _ => exact fun ⦃a⦄ a_1 ↦ hr₃ (hr₁ a_1)
            use ⟨x, hx⟩
            simp only [f, Subtype.mk.injEq, Sigma.mk.injEq]
            constructor
            · funext i
              simp [x, i.2]
            · congr! with _ i
              · simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, x]
              · simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, x]
          exact Equiv.ofBijective f ⟨f_inj, f_surj⟩
        let parts := (V.card - ∑ j : Fin t, r_list' j).choose (r_list (Fin.last t))
        have card_eq₂ : (Fintype.card (Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t)))) = (partitions V r_list').card * parts := by
          rw [Fintype.card_sigma]
          have : ∀ p : partitions V r_list', Fintype.card { x // x ∈ combinations (rest_part ↑p) (r_list (Fin.last t)) } = parts := by
            intro ⟨p, hp⟩
            simp only [Fintype.card_coe, parts]
            simp only [partitions, ne_eq, Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const, Finset.mem_filter, true_and] at hp
            obtain ⟨hp₁, hp₂, hp₃⟩ := hp
            have card_eq : (rest_part p).card = V.card - ∑ j : Fin t, r_list' j := by
              dsimp only [rest_part]
              have h_bp₁ : Finset.univ.biUnion p ⊆ V := by
                simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const]
                exact hp₃
              have h_bp₂ : (Finset.univ.biUnion p).card = ∑ j, r_list' j := by
                rw [Finset.card_biUnion]
                · congr! with i hi
                  exact (hp₁ i).2
                · simp only [Finset.coe_univ]
                  intro i hi j hj hij
                  exact hp₂ i j hij
              rw [Finset.card_sdiff_of_subset h_bp₁, h_bp₂]
            rw [← card_eq]
            exact combinations_card (rest_part p) (r_list (Fin.last t))
          simp_all only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
        rw [card_eq₁, card_eq₂, ih]
        have factorial_calc : (∏ i, (r_list i).factorial) * (V.card - ∑ i, r_list i).factorial *
               ((V.card - ∑ j, r_list' j).factorial / ((r_list (Fin.last t)).factorial * (V.card - ∑ j, r_list' j - r_list (Fin.last t)).factorial))
               = (∏ i, (r_list' i).factorial) * (V.card - ∑ i, r_list' i).factorial
          := by
            rw [Nat.sub_sub, ← h_r_list'₂, ← Nat.mul_div_assoc]
            · nth_rw 3 [mul_comm]
              rw [mul_comm, ← mul_assoc, ← Nat.div_div_eq_div_mul, Nat.mul_div_assoc]
              · rw [Nat.div_self (Nat.factorial_pos (V.card - ∑ i, r_list i)), mul_one, Nat.mul_div_assoc]
                · nth_rw 2 [mul_comm]; congr
                  rw [h_r_list'₃, Nat.mul_div_assoc, Nat.div_self (Nat.factorial_pos (r_list (Fin.last t))), mul_one]
                  exact Nat.dvd_refl (r_list (Fin.last t)).factorial
                · rw [h_r_list'₃]
                  exact Nat.dvd_mul_left (r_list (Fin.last t)).factorial (∏ i, (r_list' i).factorial)
              · exact Nat.dvd_refl (V.card - ∑ i, r_list i).factorial
            · have : r_list (Fin.last t) ≤ V.card - ∑ j, r_list' j := by
                apply Nat.le_sub_of_add_le
                rwa [add_comm, ← h_r_list'₂]
              have := Nat.factorial_mul_factorial_dvd_factorial this
              rwa [Nat.sub_sub, ← h_r_list'₂] at this
        refine Eq.symm (Nat.eq_mul_of_div_eq_left ?_ ?_)
        · refine Nat.dvd_div_of_mul_dvd ?_
          dsimp only [parts]
          rw [Nat.choose_eq_factorial_div_factorial]
          · rw [factorial_calc]
            have := Nat.prod_factorial_dvd_factorial_sum Finset.univ (extend_r_list V.card r_list')
            rw [extend_r_list.sum V.card r_list' h_r_list'₁, extend_r_list.factorial_prod V.card r_list'] at this
            exact this
          · apply Nat.le_sub_of_add_le
            rwa [add_comm, ← h_r_list'₂]
        · have : (∏ i, (r_list i).factorial) * (V.card - ∑ i, r_list i).factorial * parts = ((∏ i, (r_list' i).factorial) * (V.card - ∑ i, r_list' i).factorial) := by
            dsimp only [parts]
            rw [Nat.choose_eq_factorial_div_factorial]
            · exact factorial_calc
            · apply Nat.le_sub_of_add_le
              rwa [add_comm, ← h_r_list'₂]
          rw [Nat.div_div_eq_div_mul, this]
  next h =>
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.notMem_empty, iff_false, partitions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨p_sub, p_disj, p_card⟩
    have card_le : (Finset.univ.biUnion x).card ≤ V.card := Finset.card_le_card p_card
    have card_bUnion : (Finset.univ.biUnion x).card = ∑ i : Fin t, (x i).card := Finset.card_biUnion (fun i _ j _ hij => p_disj i j hij)
    have card_sum : ∑ i : Fin t, (x i).card = ∑ i : Fin t, r_list i := Finset.sum_congr rfl (fun i _ => (p_sub i).2)
    rw [card_bUnion, card_sum] at card_le
    exact h card_le
