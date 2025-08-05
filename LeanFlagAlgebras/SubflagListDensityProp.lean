import «LeanFlagAlgebras».SubgraphUtil
import «LeanFlagAlgebras».FlagDef
import «LeanFlagAlgebras».SubflagListDensity

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic

open FlagAlgebras
open LabeledSubgraph
open Classical
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
      (Finset.univ : Finset (Fin t)).biUnion p ⊆ V)

theorem choose_eq
    {n₁ n₂ m : ℕ} (h : n₁ = n₂)
    : n₁.choose m = n₂.choose m
  := by subst h; rfl

theorem choose_sequence_eq_factorial_div
    (n : ℕ) (r_list : Fin t → ℕ) (h_size : ∑ i : Fin t, r_list i ≤ n)
    : ∏ i : Fin t, (n - ∑ j : Fin i, r_list (j.castLE (by simp_all only [Fin.is_le']))).choose (r_list i) = Nat.factorial n / ((∏ i : Fin t, Nat.factorial (r_list i)) * Nat.factorial (n - ∑ i : Fin t, r_list i))
  := by
  induction t with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, tsub_zero, one_mul]
      rw [Nat.div_self (Nat.factorial_pos n)]
  | succ t ih =>
      have calc1 :  ∏ i : Fin (t + 1), (n - ∑ j : Fin ↑i, r_list (j.castLE (by simp_all only [Fin.is_le']))).choose (r_list i) =
      (∏ i : Fin t, (n - ∑ j : Fin ↑i, r_list (j.castLE (Nat.le_add_right_of_le Fin.is_le'))).choose (r_list i)) * ((n - ∑ j : Fin t, r_list j).choose (r_list t))
        := by
        rw [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
        simp only [lt_add_iff_pos_right, Fin.coe_eq_castSucc, Fin.natCast_eq_last]
        congr!
        rw [Finset.prod_fin_eq_prod_range]
        apply Finset.prod_bij (fun i _ => if _ : i < t then i else 0)
        · intro i hi
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi j hj hij
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi
          use i
          use hi
          simp_all only [Finset.mem_range, ↓reduceDIte]
        · intro i hi₁
          simp_all [↓reduceDIte]
          split
          next hi' h =>
            apply @_root_.choose_eq
            congr <;> try simp_all only [Finset.mem_range, ↓reduceIte]
            refine (Fin.heq_fun_iff ?h.e_a.h.e_5.h).mpr ?h.e_a.h.e_5.a
            · simp_all only [Finset.mem_range, ↓reduceIte]
            · intro i; rfl
          next _ hi₂ =>
            exfalso
            exact hi₂ (Nat.lt_add_right 1 hi₁)
      rw [calc1]; clear calc1
      let r_list' : Fin t → ℕ := fun i => r_list i
      have h_size' : ∑ i : Fin t, r_list' i ≤ n := by
        have : ∑ i : Fin t, r_list' i ≤ ∑ i : Fin (t + 1), r_list i := by
          dsimp [r_list']
          #check Finset.sum_fin_eq_sum_range
          #check Finset.sum_le_sum_of_subset
          sorry
        exact this.trans h_size
      have calc2 := ih r_list' h_size'
      dsimp [r_list'] at calc2
      have cast_simp : ∏ i : Fin t, (n - ∑ j : Fin ↑i, r_list (j.castLE (Nat.le_add_right_of_le Fin.is_le'))).choose (r_list ↑↑i) =
                       ∏ i : Fin t, (n - ∑ j : Fin ↑i, r_list ↑↑j).choose (r_list ↑↑i) := by
        sorry
      rw [cast_simp]
      rw [calc2]
      sorry

theorem partition_card
    [Fintype α] [DecidableEq α] (V : Finset α) (r_list : Fin t → ℕ) : (partitions V r_list).card = multinomialCoefficient r_list V.card := by
  dsimp [multinomialCoefficient]
  split
  next h =>
    rw [← choose_sequence_eq_factorial_div V.card r_list h]
    sorry
    -- let lV := V.toList
    -- apply Finset.card_eq_of_bijective
    -- · sorry
    -- · sorry
    -- · sorry
    -- · intro i hi
    --   sorry
  next h =>
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.not_mem_empty, iff_false, partitions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨p_sub, p_disj, p_card⟩
    have card_le : (Finset.univ.biUnion x).card ≤ V.card := Finset.card_le_card p_card
    have card_bUnion : (Finset.univ.biUnion x).card = ∑ i : Fin t, (x i).card := Finset.card_biUnion (fun i _ j _ hij => p_disj i j hij)
    have card_sum : ∑ i : Fin t, (x i).card = ∑ i : Fin t, r_list i := Finset.sum_congr rfl (fun i _ => (p_sub i).2)
    rw [card_bUnion, card_sum] at card_le
    exact h card_le

#check Finset.card_eq_of_bijective

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
    apply div_le_one_of_le
    · let VG := (Finset.univ : Finset W) \ G.type_verts.toFinset
      have hVG : VG.card = G.size - σ.size := by
        simp only [VG, LabeledGraph.size, Finset.card_sdiff (Finset.subset_univ _)]
        rw [Set.toFinset_card, Finset.card_univ, LabeledGraph.type_verts_card_eq]
      let r_list : Fin t → ℕ := fun i => (Fl i).size - σ.size
      have := partition_card VG (r_list)
      rw [hVG] at this
      rw [← this, Nat.cast_le]
      let f : (Fin t → LabeledSubgraph σ G) → (Fin t → Finset W) := fun Gl i => (Gl i).subgraph.verts.toFinset \ G.type_verts.toFinset
      apply Finset.card_le_card_of_injOn f
      · rintro Gl hGl
        dsimp [partitions, f]
        apply Finset.mem_filter.mpr
        constructor
        · simp only [Finset.mem_univ]
        · simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hGl
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
        rw [Function.funext_iff] at h_eq
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
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : ∃ k, |flagListDensity Fl G - ∏ i in Finset.univ, flagDensity₁ (Fl i) G| ≤ (∑ i in Finset.univ, (Fl i).out.size) ^ k / G.out.size
  := by
  use 2
  let Vs := Fin t → Finset W
  let Ω : Finset Vs := { Vs : Vs | ∀ i , (Vs i).card = (Fl i).out.size ∧ ∀ i, G.out.type_verts ⊆ (Vs i).toSet }
  let B : Finset Vs := { Vs : Vs | ∀ i j, i ≠ j → Disjoint (Vs i) (Vs j) }
  let B_c : Finset Vs := { Vs : Vs | ¬(∀ i j, i ≠ j → Disjoint (Vs i) (Vs j)) }
  let B_c_ij : Fin t → Fin t → Finset Vs := fun i j => { Vs : Vs | ¬ Disjoint (Vs i) (Vs j) }
  have : B_c.card ≤ ∑ i : Fin t, ∑ j : Fin t, (B_c_ij i j).card := sorry
  sorry

theorem flagListDensity₂_prod_approx
    (F : Flag σ V) (F' : Flag σ U) (G : Flag σ W)
    : ∃ k, |flagDensity₂ F F' G - flagDensity₁ F G * flagDensity₁ F' G| ≤ (F.out.size + F'.out.size) ^ k / G.out.size
  := by
  use 2
  let ⟨Frep, hFrep⟩ := Quotient.exists_rep F
  let ⟨F'rep, hF'rep⟩ := Quotient.exists_rep F'
  let ⟨Grep, hGrep⟩ := Quotient.exists_rep G
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F G]
  rw [← hFrep, ← hF'rep, ← hGrep]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂ Frep F'rep Grep]
  dsimp [subflagDensity, labeledSubgraphDensityLifted]
  have hFrep' : ⟦Frep⟧.out.size = Frep.size := rfl
  have hGrep' : ⟦Grep⟧.out.size = Grep.size := rfl
  rw [hFrep', hGrep']
  dsimp [labeledSubgraphDensity, labeledSubgraphListDensity] -- Is it possible to prove using cardinality....?

  let Ω := { v : Finset W × Finset W // v.1.card = Frep.size ∧ v.2.card = Frep.size}
  sorry
