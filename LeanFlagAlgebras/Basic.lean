import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Nonempty
import Mathlib.Data.Real.Basic


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

noncomputable def fintype_of_subgraph_set
      {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (p : Subgraph G → Prop) : Fintype { G' : Subgraph G | p G' } :=
  let subgraph_set := { G' : Subgraph G | p G' }
  let f : subgraph_set → Set V × Set (V × V) :=
    fun G' => (G'.val.verts, { (u, v) | G'.val.Adj u v })
  have f_inj : Function.Injective f := by
    intro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.val.verts = G2.val.verts := (Prod.ext_iff.mp h_eq).1
      exact Eq.to_iff (congrFun h_eq_verts u)
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact Eq.to_iff (congrFun h_eq_edges (u, v))
  Fintype.ofInjective f f_inj

noncomputable def subgraph_count
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  let p (G' : Subgraph G) : Prop := G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H)
  let iso_sub := { G' : Subgraph G | p G' }
  have : Fintype iso_sub := fintype_of_subgraph_set G p
  (Set.toFinset iso_sub).card

noncomputable def subgraph_density {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (H : SimpleGraph V) (G : SimpleGraph W) : ℚ :=
  let subgraph_cnt := subgraph_count H G
  let num_of_all_induced_subgraphs := (univ : Finset W).card.choose (univ : Finset V).card
  subgraph_cnt / num_of_all_induced_subgraphs

theorem subgraph_density_ge_0 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
          (H : SimpleGraph V) (G : SimpleGraph W)
          : 0 ≤ subgraph_density H G := by
  dsimp [subgraph_density]
  apply div_nonneg <;> simp

#check Finset.card_le_card_of_inj_on
#check comb_card
#check combinations
#check Set.toFinset
#check SimpleGraph.Subgraph.IsInduced
#check Equiv.ofBijective
#check Nonempty

open Classical

noncomputable def vert_iso_from_graph_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (H : SimpleGraph V) (G : SimpleGraph W) (G₀ : G.Subgraph)
  (hG₀_iso : Nonempty (Subgraph.coe G₀ ≃g H))
  : {x // x ∈ G₀.verts } ≃ V := by
    let g : Subgraph.coe G₀ ≃g H := Classical.choice hG₀_iso
    let f₀ : {x // x ∈ G₀.verts } → V := g
    have hf₀ : Function.Bijective f₀ := RelIso.bijective g
    exact Equiv.ofBijective f₀ hf₀

theorem subgraph_density_le_1 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
          (H : SimpleGraph V) (G : SimpleGraph W)
          : subgraph_density H G ≤ 1 := by
  dsimp [subgraph_density]
  dsimp [subgraph_count]
  apply div_le_one_of_le
  . have := comb_card (univ : Finset W) (univ : Finset V).card
    simp at this; rw [←this]; simp
    let induced_subgraphs_iso_to_H :=
      { G' : G.Subgraph | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
    let f : induced_subgraphs_iso_to_H → Finset W := fun G' =>
      have : Fintype G'.val.verts := Fintype.ofFinite G'.val.verts
      Set.toFinset G'.val.verts
    apply Finset.card_le_card_of_injOn f
    . rintro G' _
      dsimp [combinations, f]
      apply mem_filter.mpr
      constructor
      . simp
      . apply card_eq_of_equiv_fintype
        let ⟨_, hG'_iso⟩ := G'.property
        simp
        exact vert_iso_from_graph_iso H G G' hG'_iso
    . intro G₁ _ G₂ _ h_eq
      dsimp [f] at h_eq
      have h_eq_verts : G₁.val.verts = G₂.val.verts := by simp_all
      ext x y
      . simp_all
      . dsimp [induced_subgraphs_iso_to_H] at G₁ G₂
        constructor
        . have ⟨h₂, _⟩ := G₂.property
          dsimp [Subgraph.IsInduced] at h₂
          intro h₁
          have hx : x ∈ G₂.val.verts := by
            rw [← h_eq_verts]
            exact G₁.val.edge_vert h₁
          have hy : y ∈ G₂.val.verts := by
            rw [← h_eq_verts]
            exact G₁.val.edge_vert (G₁.val.adj_symm h₁)
          have h_adj : G.Adj x y :=
            Subgraph.Adj.adj_sub h₁
          exact h₂ hx hy h_adj
        . have ⟨h₁, _⟩ := G₁.property
          dsimp [Subgraph.IsInduced] at h₁
          intro h₂
          have hx : x ∈ G₁.val.verts := by
            rw [h_eq_verts]
            exact G₂.val.edge_vert h₂
          have hy : y ∈ G₁.val.verts := by
            rw [h_eq_verts]
            exact G₂.val.edge_vert (G₂.val.adj_symm h₂)
          have h_adj : G.Adj x y :=
            Subgraph.Adj.adj_sub h₂
          exact h₁ hx hy h_adj
  . simp

noncomputable def all_graphs_on_vertex_set
    (V : Type*) [Fintype V] [DecidableEq V] : Finset (SimpleGraph V) :=
  let all_graphs := { G : SimpleGraph V | true }
  have : Fintype all_graphs :=
    let f (G' : all_graphs) : Set (V × V) := { (u, v) | G'.val.Adj u v }
    have f_inj : Function.Injective f := by
      intro G1 G2 h_eq
      dsimp [f] at h_eq
      ext u v
      exact Eq.to_iff (congrFun h_eq (u, v))
    Fintype.ofInjective f f_inj
  Set.toFinset all_graphs

#check Equiv.symm

def graph_eqv {V : Type*} [Fintype V] [DecidableEq V] (G₀ G₁ : SimpleGraph V) : Prop :=
  Nonempty (G₀ ≃g G₁)

theorem graph_eqv.refl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    : graph_eqv G G := by
  exact instNonemptyOfInhabited

theorem graph_eqv.symm {V : Type*} [Fintype V] [DecidableEq V]
    : ∀ {G₀ G₁ : SimpleGraph V}, graph_eqv G₀ G₁ → graph_eqv G₁ G₀ := by
  intro G₀ G₁ h
  let ⟨f, hf⟩ := h
  let f_symm : V ≃ V := f.symm
  have hf_symm : ∀ {a b : V}, G₀.Adj (f_symm a) (f_symm b) ↔ G₁.Adj a b := by
    intro a b
    have := @hf (f.symm a) (f.symm b)
    simp [Equiv.apply_symm_apply] at this
    exact Iff.symm this
  exact ⟨f_symm, hf_symm⟩

theorem graph_eqv.trans {V : Type*} [Fintype V] [DecidableEq V]
    : ∀ {G₀ G₁ G₂ : SimpleGraph V}, graph_eqv G₀ G₁ → graph_eqv G₁ G₂ → graph_eqv G₀ G₂ := by
  intro G₀ G₁ G₂ h01 h12
  dsimp [graph_eqv] at h01 h12
  let ⟨f01, hf01⟩ := h01
  let ⟨f12, hf12⟩ := h12
  let f : V ≃ V := f01.trans f12
  have : ∀ {a b : V}, G₂.Adj (f a) (f b) ↔ G₀.Adj a b := by
    intro a b
    exact Iff.trans hf12 hf01
  exact ⟨f, this⟩

theorem is_equivalence {V : Type*} [Fintype V] [DecidableEq V]
    : Equivalence (@graph_eqv V _ _) :=
  { refl := graph_eqv.refl, symm := graph_eqv.symm, trans := graph_eqv.trans }

instance graphSetoid (V : Type*) [Fintype V] [DecidableEq V]
    : Setoid (SimpleGraph V) where
  r     := graph_eqv
  iseqv := is_equivalence

def QuotSimpleGraph (V : Type u) [Fintype V] [DecidableEq V] : Type u :=
  Quotient (graphSetoid V)

noncomputable instance quotSimpleGraphFintype (V : Type*) [Fintype V] [DecidableEq V]
    : Fintype (QuotSimpleGraph V) := Quotient.fintype (graphSetoid V)

lemma subgraph_density_respects_eqv_on_G
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G₀ G₁ : SimpleGraph W)
    (h_eqv : graph_eqv G₀ G₁)
    : subgraph_density H G₀ = subgraph_density H G₁ := by
  sorry

noncomputable def subgraph_density_lift_G
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) : QuotSimpleGraph W → ℚ := by
  apply Quot.lift (fun G : SimpleGraph W => subgraph_density H G)
  intro G₀ G₁ h_eqv
  exact subgraph_density_respects_eqv_on_G H G₀ G₁ h_eqv

lemma subgraph_density_lift_G_respects_eqv_on_H
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₀ H₁ : SimpleGraph V) (G : QuotSimpleGraph W)
    (h_eqv : graph_eqv H₀ H₁)
    : subgraph_density_lift_G H₀ G = subgraph_density_lift_G H₁ G := by
  sorry

-- quotient version of subgraph_density
noncomputable def subgraph_density_quot
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    : QuotSimpleGraph V → QuotSimpleGraph W → ℚ := by
  apply Quot.lift subgraph_density_lift_G
  intro H₀ H₁ h_eqv
  ext G
  exact subgraph_density_lift_G_respects_eqv_on_H H₀ H₁ G h_eqv

lemma sum_subgraph_counts
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (h_card : Fintype.card V ≤ Fintype.card W)
    : ∑ F in (all_graphs_on_vertex_set V), subgraph_count F G = (Fintype.card W).choose (Fintype.card V) := by
  dsimp [all_graphs_on_vertex_set, subgraph_count]
  let h := comb_card (univ : Finset W) (Fintype.card V)
  dsimp at h
  rw [← h]
  sorry

theorem sum_subgraph_densities_eq_one
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (h_card : Fintype.card V ≤ Fintype.card W)
    : ∑ F in (all_graphs_on_vertex_set V), subgraph_density F G = 1.0 := by
  dsimp [all_graphs_on_vertex_set, subgraph_density] ; simp
  let num_of_all_induced_subgraphs := (Fintype.card W).choose (Fintype.card V)
  have h_sum : ∀ m : ℕ,
    ∑ F : SimpleGraph V, subgraph_count F G / m
    = 1 / m * ∑ F : SimpleGraph V, subgraph_count F G := by sorry
  sorry
  -- rw [h_sum, Finset.sum_div]
  -- simp only [div_self]
  -- exact Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_of_lt (Finset.card_pos.mpr (Finset.nonempty_univ W))))

theorem subgraph_density_eq_sum_subgraph_densities
  {U V W : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (H : SimpleGraph V) (G : SimpleGraph W)
  (h_card : Fintype.card V ≤ Fintype.card U ∧ Fintype.card U ≤ Fintype.card W)
  : subgraph_density H G = ∑ F in (all_graphs_on_vertex_set U), subgraph_density H F * subgraph_density F G := by
  sorry


def FiniteSimpleGraph :=
  Σ (V : Type*) (_ : Fintype V), SimpleGraph V

@[ext]
structure RealTimesGraph where
  f : FiniteSimpleGraph → ℝ

instance : Add RealTimesGraph where
  add f g := ⟨fun G => f.f G + g.f G⟩


noncomputable def chain_sum {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (F : SimpleGraph V) (ℓ : ℕ) : RealTimesGraph := by
  constructor; intro G
  letI : Fintype G.1 := G.2.1
  letI : DecidableEq G.1 := Classical.decEq _
  exact if Fintype.card G.1 = ℓ then subgraph_density F G.2.2 else 0

-- all elements of the form F - ∑ p(F, G) * G
def chain_elements : Set (Set FiniteSimpleGraph → ℝ) :=
  sorry

-- linear subspace generated by chain_elements
def chain_subspace : Set (Set FiniteSimpleGraph → ℝ) :=
  sorry

-- equivalence relation on RealTimesGraph induced by chain_subspace
def chain_relation : (Set FiniteSimpleGraph → ℝ) → (Set FiniteSimpleGraph → ℝ) → Prop :=
  sorry
