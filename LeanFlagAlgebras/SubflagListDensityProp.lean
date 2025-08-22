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

def partitions [Fintype α] [DecidableEq α] (V : Finset α) (r_list : Fin t → ℕ) : Finset (Fin t → Finset α)
  := (Finset.univ : Finset (Fin t → Finset α)).filter (fun p =>
      (∀ i, p i ⊆ V ∧ (p i).card = r_list i) ∧
      (∀ i j, i ≠ j → Disjoint (p i) (p j)) ∧
      (Finset.univ : Finset (Fin t)).biUnion p ⊆ V) -- Actually, this can be derived from the first property, but it was included for the convenience of the proof.

def extend_r_list
    (n : ℕ) (r_list : Fin t → ℕ)
    : Fin (t + 1) → ℕ
  := by
  intro i
  if h : i.val < t then
    exact r_list ⟨i.val, h⟩
  else
    exact n - ∑ j : Fin t, r_list j

lemma extend_r_list.sum_eq
    (n : ℕ) (r_list : Fin t → ℕ) (h_r_list : ∑ i, r_list i ≤ n)
    : ∑ i : Fin (t + 1), extend_r_list n r_list i = n
  := by
  dsimp [extend_r_list]
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte, lt_self_iff_false]
  have sum_eq : ∑ x ∈ Finset.range t, (if _ : x < t + 1 then if h_1 : x < t then r_list ⟨x, Eq.mpr_prop (Eq.refl (x < t)) h_1⟩ else n - ∑ j : Fin t, r_list j else 0) = ∑ j : Fin t, r_list j := by
    simp only [dite_eq_ite, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_bij (fun i _ => i) <;> try simp only [mem_range, imp_self, implies_true, exists_prop, exists_eq_right, imp_self, implies_true]
    intro i hi
    simp only [Nat.lt_add_right 1 hi, ↓reduceIte, hi, ↓reduceDIte]
  rw [sum_eq, Nat.add_sub_of_le h_r_list]

lemma extend_r_list.factorial_prod_eq
    (n : ℕ) (r_list : Fin t → ℕ)
    : ∏ i, ((extend_r_list n r_list) i).factorial = (∏ i, (r_list i).factorial) * (n - ∑ j : Fin t, r_list j).factorial
  := by
  dsimp [extend_r_list]
  rw [Finset.prod_fin_eq_prod_range, Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
  simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte, lt_self_iff_false, mul_eq_mul_right_iff]
  left
  apply Finset.prod_bij (fun i _ => i) <;> try simp only [mem_range, imp_self, implies_true, exists_prop, exists_eq_right, imp_self, implies_true]
  intro i hi
  simp only [Nat.lt_add_right 1 hi, hi, ↓reduceDIte]

  theorem partition_card
    [Fintype α] [DecidableEq α] (V : Finset α) (r_list : Fin t → ℕ) : (partitions V r_list).card = multinomialCoefficient r_list V.card := by
  dsimp only [multinomialCoefficient]
  split
  next h =>
    induction t with
    | zero =>
        simp only [partitions, IsEmpty.forall_iff, ne_eq, univ_eq_empty,
          biUnion_empty, empty_subset, and_self, univ_unique, filter_True, card_singleton,
          prod_empty, sum_empty, tsub_zero, one_mul]
        rw [Nat.div_self (Nat.factorial_pos #V)]
    | succ t ih =>
        let r_list' : Fin t → ℕ := fun i => r_list i.castSucc
        have h_r_list'₁ : ∑ i : Fin t, r_list' i ≤ V.card := by
          have : ∑ i, r_list' i ≤ ∑ i, r_list i := by
            dsimp [r_list']
            rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
            simp only [Fin.castSucc_mk, lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte]
            apply Nat.le_add_right_of_le
            apply Finset.sum_le_sum
            intro x hx
            rw [Finset.mem_range] at hx
            simp only [hx, Nat.lt_add_right 1 hx, ↓reduceDIte, Nat.le_refl]
          exact this.trans h
        have h_r_list'₂ : ∑ i, r_list i = ∑ j, r_list' j + r_list (Fin.last t) := by
          rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
          simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte]
          congr!
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_bij (fun i _ => i) <;> try simp only [mem_range, imp_self, implies_true, exists_prop, exists_eq_right, imp_self, implies_true]
          intro i hi
          simp only [Nat.lt_add_right 1 hi, ↓reduceDIte, hi, Fin.castSucc_mk, r_list']
        have h_r_list'₃ : ∏ i, (r_list i).factorial = (∏ i, (r_list' i).factorial) * (r_list (Fin.last t)).factorial := by
          rw [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
          simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte]
          congr!
          rw [Finset.prod_fin_eq_prod_range]
          apply Finset.prod_bij (fun i _ => i) <;> try simp only [mem_range, imp_self, implies_true, exists_prop, exists_eq_right, imp_self, implies_true]
          intro i hi
          simp only [Nat.lt_add_right 1 hi, ↓reduceDIte, hi, Fin.castSucc_mk, r_list']
        specialize ih r_list' h_r_list'₁
        let rest_part (p : Fin t → Finset α) := V \ (Finset.univ : Finset (Fin t)).biUnion p
        have card_eq₁ : (partitions V r_list).card = (Fintype.card (Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t)))) := by
          apply Finset.card_eq_of_equiv
          let f : {x // x ∈ partitions V r_list} → {x // x ∈ (Finset.univ : Finset (Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t))))} := by
            intro ⟨p, hp⟩
            let p' : (Fin t) → Finset α := fun i => p i.castSucc
            have hp' : p' ∈ partitions V r_list' := by
              simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter, true_and] at hp
              obtain ⟨hp₁, hp₂, hp₃⟩ := hp
              simp only [partitions, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter,
                true_and, p', r_list']
              constructor <;> try constructor
              · intro i
                exact hp₁ i.castSucc
              · intro i j hij
                rw [ne_eq, ← Fin.castSucc_inj] at hij
                exact hp₂ i.castSucc j.castSucc hij
              · intro i
                exact hp₃ i.castSucc
            let x₁ : {x // x ∈ partitions V r_list'} := ⟨p', hp'⟩
            let r := p (Fin.last t)
            have hr : r ∈ combinations (rest_part p') (r_list (Fin.last t)) := by
              simp only [combinations, mem_filter, mem_powerset]
              simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter, true_and] at hp
              obtain ⟨hp₁, hp₂, hp₃⟩ := hp
              constructor
              · intro x hx₁
                refine mem_sdiff.mpr ?_
                constructor
                · exact hp₃ (Fin.last t) hx₁
                · dsimp [p']
                  simp only [mem_biUnion, mem_univ, true_and, not_exists]
                  intro i
                  have hi : i.castSucc ≠ Fin.last t := by
                    simp only [ne_eq, Fin.castSucc_ne_last, not_false_eq_true]
                  specialize hp₂ i.castSucc (Fin.last t) hi
                  by_contra hx₂
                  dsimp [r] at hx₁
                  simp only [disjoint_iff, inf_eq_inter, bot_eq_empty] at hp₂
                  have : x ∈ p i.castSucc ∩ p (Fin.last t) := by
                    simp only [mem_inter]
                    exact ⟨hx₂, hx₁⟩
                  rw [hp₂] at this
                  exact Finset.notMem_empty x this
              · exact (hp₁ (Fin.last t)).2
            let x₂ : {x // x ∈ combinations (rest_part p') (r_list (Fin.last t))} := ⟨r, hr⟩
            let result : Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t)) := ⟨x₁, x₂⟩
            have : result ∈ univ := Finset.mem_univ _
            use result
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
            simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter, true_and] at hp
            obtain ⟨hp₁, hp₂, hp₃⟩ := hp
            simp only [combinations, mem_filter, mem_powerset] at hr
            obtain ⟨hr₁, hr₂⟩ := hr
            have hr₃ : rest_part p ⊆ V := by simp only [sdiff_subset, rest_part]
            let x : Fin (t + 1) → Finset α := fun i => if h : i.val < t then p ⟨i.val, h⟩ else r
            have hx : x ∈ partitions V r_list := by
              simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const, mem_filter, true_and]
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
                    refine disjoint_left.mpr ?_
                    intro x hx₁ hx₂
                    have hx₃ : x ∈ rest_part p := hr₁ hx₂
                    simp_all only [mem_univ, true_and, mem_sdiff, mem_biUnion, not_exists, rest_part]
                next hi =>
                  split
                  next hj =>
                    refine disjoint_right.mpr ?_
                    intro x hx₁ hx₂
                    have hx₃ : x ∈ rest_part p := hr₁ hx₂
                    simp_all only [mem_univ, true_and, mem_sdiff, mem_biUnion, not_exists, rest_part]
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
              · simp only [Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, x]
              · simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, x]
          exact Equiv.ofBijective f ⟨f_inj, f_surj⟩
        let parts := (V.card - ∑ j : Fin t, r_list' j).choose (r_list (Fin.last t))
        have card_eq₂ : (Fintype.card (Σ (S : (partitions V r_list')), combinations (rest_part S) (r_list (Fin.last t)))) = (partitions V r_list').card * parts := by
          rw [Fintype.card_sigma]
          have : ∀ p : partitions V r_list', Fintype.card { x // x ∈ combinations (rest_part ↑p) (r_list (Fin.last t)) } = parts := by
            intro ⟨p, hp⟩
            simp only [Fintype.card_coe, parts]
            simp only [partitions, ne_eq, biUnion_subset_iff_forall_subset, mem_univ, forall_const,
              mem_filter, true_and] at hp
            obtain ⟨hp₁, hp₂, hp₃⟩ := hp
            have card_eq : (rest_part p).card = V.card - ∑ j : Fin t, r_list' j := by
              dsimp [rest_part]
              have h_bp₁ : univ.biUnion p ⊆ V := by
                simp only [biUnion_subset_iff_forall_subset, mem_univ, forall_const]
                exact hp₃
              have h_bp₂ : (univ.biUnion p).card = ∑ j, r_list' j := by
                rw [card_biUnion]
                · congr! with i hi
                  exact (hp₁ i).2
                · simp only [coe_univ]
                  intro i hi j hj hij
                  exact hp₂ i j hij
              rw [card_sdiff h_bp₁, h_bp₂]
            rw [← card_eq]
            exact comb_card (rest_part p) (r_list (Fin.last t))
          simp_all only [univ_eq_attach, sum_const, card_attach, smul_eq_mul]
        rw [card_eq₁, card_eq₂, ih]
        have factorial_calc : (∏ i, (r_list i).factorial) * (#V - ∑ i, r_list i).factorial *
               ((#V - ∑ j, r_list' j).factorial / ((r_list (Fin.last t)).factorial * (#V - ∑ j, r_list' j - r_list (Fin.last t)).factorial))
               = (∏ i, (r_list' i).factorial) * (#V - ∑ i, r_list' i).factorial
          := by
            rw [Nat.sub_sub, ← h_r_list'₂, ← Nat.mul_div_assoc]
            · nth_rw 3 [mul_comm]
              rw [mul_comm, ← mul_assoc, ← Nat.div_div_eq_div_mul, Nat.mul_div_assoc]
              · rw [Nat.div_self (Nat.factorial_pos (#V - ∑ i, r_list i)), mul_one, Nat.mul_div_assoc]
                · nth_rw 2 [mul_comm]
                  congr
                  rw [h_r_list'₃, Nat.mul_div_assoc, Nat.div_self (Nat.factorial_pos (r_list (Fin.last t))), mul_one]
                  exact Nat.dvd_refl (r_list (Fin.last t)).factorial
                · rw [h_r_list'₃]
                  exact Nat.dvd_mul_left (r_list (Fin.last t)).factorial (∏ i, (r_list' i).factorial)
              · exact Nat.dvd_refl (#V - ∑ i, r_list i).factorial
            · have : r_list (Fin.last t) ≤ #V - ∑ j, r_list' j := by
                apply Nat.le_sub_of_add_le
                rwa [add_comm, ← h_r_list'₂]
              have := Nat.factorial_mul_factorial_dvd_factorial this
              rwa [Nat.sub_sub, ← h_r_list'₂] at this
        refine Eq.symm (Nat.eq_mul_of_div_eq_left ?_ ?_)
        · refine Nat.dvd_div_of_mul_dvd ?_
          dsimp [parts]
          rw [Nat.choose_eq_factorial_div_factorial]
          · rw [factorial_calc]
            have := Nat.prod_factorial_dvd_factorial_sum Finset.univ (extend_r_list V.card r_list')
            rw [extend_r_list.sum_eq V.card r_list' h_r_list'₁, extend_r_list.factorial_prod_eq V.card r_list'] at this
            exact this
          · apply Nat.le_sub_of_add_le
            rwa [add_comm, ← h_r_list'₂]
        · have : (∏ i, (r_list i).factorial) * (#V - ∑ i, r_list i).factorial * parts = ((∏ i, (r_list' i).factorial) * (#V - ∑ i, r_list' i).factorial) := by
            dsimp [parts]
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

omit [DecidableEq T] in
theorem labeledGraphListDensity_ge_zero
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : 0 ≤ labeledSubgraphListDensity Fl G := by
    dsimp [labeledSubgraphListDensity]
    apply div_nonneg <;> simp only [Nat.cast_nonneg]

omit [DecidableEq T] in
theorem labeledGraphListDensity_le_one
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity Fl G ≤ 1 := by
    dsimp [labeledSubgraphListDensity, labeledSubgraphListCount, setOfLabeledSubgraphListIsoHl]
    apply div_le_one_of_le₀
    · let VG := (Finset.univ : Finset W) \ G.type_verts.toFinset
      have h_VG : VG.card = G.size - σ.size := by
        simp only [VG, LabeledGraph.size, Finset.card_sdiff (Finset.subset_univ _)]
        rw [Set.toFinset_card, Finset.card_univ, LabeledGraph.type_verts_card_eq]
      let r_list : Fin t → ℕ := fun i => (Fl i).size - σ.size
      rw [← h_VG, ← partition_card VG (r_list), Nat.cast_le]
      let f : (Fin t → LabeledSubgraph σ G) → (Fin t → Finset W) := fun Gl i => (Gl i).subgraph.verts.toFinset \ G.type_verts.toFinset
      apply Finset.card_le_card_of_injOn f
      · rintro Gl hGl
        dsimp [partitions, f]
        apply Finset.mem_filter.mpr
        constructor
        · simp only [Finset.mem_univ]
        · simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hGl
          obtain ⟨_, hGl_iso, hGl_disj⟩ := hGl
          constructor
          · intro i
            simp only
            constructor
            · refine Finset.sdiff_subset_sdiff ?h.hf.right.left.left.hst fun ⦃a⦄ a ↦ a
              simp_all only [Finset.subset_univ]
            · have : G.type_verts.toFinset ⊆ (Gl i).subgraph.verts.toFinset := by
                simp only [Set.subset_toFinset, Set.coe_toFinset]
                exact labeledSubgraph_contain_type_verts G (Gl i)
              rw [Finset.card_sdiff this, Set.toFinset_card, Set.toFinset_card, LabeledGraph.type_verts_card_eq]
              dsimp [r_list]
              have size_eq := labeledGraphIso_size_eq (Gl i).coe (Fl i) (Classical.choice (hGl_iso i))
              exact congrFun (congrArg HSub.hSub size_eq) σ.size
          · constructor
            · intro i j hij
              simp only
              rw [Finset.disjoint_left]
              intro w h_wi h_wj
              rw [Finset.mem_sdiff] at h_wi h_wj
              obtain ⟨h_w_mem_i, h_w_not_type⟩ := h_wi
              obtain ⟨h_w_mem_j, _⟩ := h_wj
              rw [Set.mem_toFinset] at h_w_mem_i h_w_mem_j h_w_not_type
              have h_w_in_inter : w ∈ (Gl i).subgraph.verts \ G.type_verts ∩ ((Gl j).subgraph.verts \ G.type_verts) := by
                rw [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff]
                exact ⟨⟨h_w_mem_i, h_w_not_type⟩, ⟨h_w_mem_j, h_w_not_type⟩⟩
              rw [hGl_disj i j hij] at h_w_in_inter
              exact h_w_in_inter
            · simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, true_implies]
              intro i
              dsimp [VG]
              refine Finset.sdiff_subset_sdiff ?h.hf.right.intro.intro.right.right.hst fun ⦃a⦄ a ↦ a
              simp_all only [Finset.subset_univ]
      · intro Gl₁ hGl₁ Gl₂ hGl₂ h_eq
        rw [funext_iff] at h_eq
        dsimp [f] at h_eq
        simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hGl₁ hGl₂
        obtain ⟨hGl₁_ind, _, _⟩ := hGl₁
        obtain ⟨hGl₂_ind, _, _⟩ := hGl₂
        funext i
        apply labeledSubgraph_eq_from_subgraph_eq
        have hGl₁_i_ind := @hGl₁_ind i
        have hGl₂_i_ind := @hGl₂_ind i
        specialize h_eq i
        rw [← Set.toFinset_diff, ← Set.toFinset_diff, Set.toFinset_inj] at h_eq
        have h_eq_verts : (Gl₁ i).subgraph.verts = (Gl₂ i).subgraph.verts := by
          calc
            (Gl₁ i).subgraph.verts = (Gl₁ i).subgraph.verts \ G.type_verts ∪ G.type_verts := by exact (Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl₁ i))).symm
          _                        = (Gl₂ i).subgraph.verts \ G.type_verts ∪ G.type_verts := by rw [h_eq]
          _                        = (Gl₂ i).subgraph.verts := by exact (Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl₂ i)))
        calc
          (Gl₁ i).subgraph = inducedSubgraph G.graph (Gl₁ i).subgraph.verts := by exact inducedSubgraph_eq hGl₁_i_ind
          _                = inducedSubgraph G.graph (Gl₂ i).subgraph.verts := by rw [h_eq_verts]
          _                = (Gl₂ i).subgraph := by exact (inducedSubgraph_eq hGl₂_i_ind).symm
    · simp only [Nat.cast_nonneg]

omit [DecidableEq T] in
theorem quotLabeledGraphListDensity_ge_zero
    (Fl : QuotLabeledGraphList σ t Vl) (G :Flag σ W)
    : 0 ≤ quotLabeledSubgraphListDensity Fl G := by
    rcases Quot.exists_rep Fl with ⟨Flrep, hFlrep⟩
    rcases Quot.exists_rep G with ⟨Grep, hGrep⟩
    rw [← hFlrep, ← hGrep]
    apply labeledGraphListDensity_ge_zero

omit [DecidableEq T] in
theorem quotLabeledGraphListDensity_le_one
    (Fl : QuotLabeledGraphList σ t Vl) (G :Flag σ W)
    : quotLabeledSubgraphListDensity Fl G ≤ 1 := by
    rcases Quot.exists_rep Fl with ⟨Flrep, hFlrep⟩
    rcases Quot.exists_rep G with ⟨Grep, hGrep⟩
    rw [← hFlrep, ← hGrep]
    apply labeledGraphListDensity_le_one

omit [DecidableEq T] in
theorem flagListDensity_ge_zero
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : 0 ≤ flagListDensity Fl G := by
  dsimp [flagListDensity]
  apply quotLabeledGraphListDensity_ge_zero

omit [DecidableEq T] in
theorem flagListDensity_le_one
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G ≤ 1 := by
  dsimp [flagListDensity]
  apply quotLabeledGraphListDensity_le_one

omit [DecidableEq T] in
theorem flagListDensity₁_ge_zero
    (F : Flag σ V) (G : Flag σ W)
    : 0 ≤ flagDensity₁ F G := by
  apply flagListDensity_ge_zero

omit [DecidableEq T] in
theorem flagListDensity₁_le_one
    (F : Flag σ V) (G : Flag σ W)
    : flagDensity₁ F G ≤ 1 := by
  apply flagListDensity_le_one

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

theorem flagListDensity₂_prod_approx
    (F : Flag σ V) (F' : Flag σ U)
    : ∃ c ≥ 0, ∀ {W : Type} [Fintype W] [DecidableEq W] (G : Flag σ W),
    |flagDensity₂ F F' G - flagDensity₁ F G * flagDensity₁ F' G| ≤ c / G.out.size
  := by
  use (F.out.size + F'.out.size) ^ 2
  constructor; (apply sq_nonneg)
  intro W _ _ G
  let ⟨Frep, hFrep⟩ := Quotient.exists_rep F
  let ⟨F'rep, hF'rep⟩ := Quotient.exists_rep F'
  let ⟨Grep, hGrep⟩ := Quotient.exists_rep G
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F G]
  rw [← hFrep, ← hF'rep, ← hGrep]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂ Frep F'rep Grep]
  dsimp [subflagDensity, labeledSubgraphDensityLifted]
  have hFrep' : (⟦Frep⟧ : Quotient (labeledGraphSetoid σ V)).out.size = Frep.size := rfl
  have hGrep' : (⟦Grep⟧ : Quotient (labeledGraphSetoid σ W)).out.size = Grep.size := rfl
  rw [hFrep', hGrep']
  dsimp [labeledSubgraphDensity, labeledSubgraphListDensity] -- Is it possible to prove using cardinality....?

  let Ω := { v : Finset W × Finset W // v.1.card = Frep.size ∧ v.2.card = Frep.size}
  sorry
