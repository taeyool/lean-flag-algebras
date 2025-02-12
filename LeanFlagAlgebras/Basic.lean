import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Nonempty
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Logic.Unique


variable {α : Type} [DecidableEq α]

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
open Classical

variable {T U V W X : Type}
  [Fintype T] [DecidableEq T]
  [Fintype U] [DecidableEq U]
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  [Fintype X] [DecidableEq X]

noncomputable def subgraphFintype
    (G : SimpleGraph V) : Fintype (Subgraph G)
  :=
  let f : Subgraph G → Set V × Set (V × V) :=
    fun G' => (G'.verts, { (u, v) | G'.Adj u v })
  have f_inj : Function.Injective f := by
    intro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.verts = G2.verts := (Prod.ext_iff.mp h_eq).1
      exact Eq.to_iff (congrFun h_eq_verts u)
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact Eq.to_iff (congrFun h_eq_edges (u, v))
  Fintype.ofInjective f f_inj

noncomputable instance subgraphProdFintype
    (G : SimpleGraph V) : Fintype (Subgraph G × Subgraph G)
  := by
  have : Fintype (Subgraph G) := subgraphFintype G
  exact inferInstance

noncomputable instance subgraphSetFintype
    (G : SimpleGraph V) (p : Subgraph G → Prop)
    : Fintype { G' : Subgraph G | p G' } := by
  have : Fintype (Subgraph G) := subgraphFintype G
  exact inferInstance

noncomputable def subgraphCount
    (H : SimpleGraph V) (G : SimpleGraph W) : ℕ
  :=
  let p (G' : Subgraph G) : Prop := G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H)
  { G' : Subgraph G | p G' }.toFinset.card

noncomputable def subgraphDensity
    (H : SimpleGraph V) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraphCount H G
  let num_of_all_induced_subgraph := (univ : Finset W).card.choose (univ : Finset V).card
  subgraph_cnt / num_of_all_induced_subgraph

noncomputable def subgraphPairCount
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℕ
  :=
  let p (G₁ G₂ : Subgraph G) : Prop :=
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅
  { (G₁, G₂) : Subgraph G × Subgraph G | p G₁ G₂ }.toFinset.card

noncomputable def subgraphPairDensity
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraphPairCount H₁ H₂ G
  let W_card := Fintype.card W
  let V_card := Fintype.card V
  let U_card := Fintype.card U
  let num_of_all_induced_subgraphs := W_card.choose V_card * (W_card - V_card).choose U_card
  subgraph_cnt / num_of_all_induced_subgraphs

omit [DecidableEq V] [DecidableEq W] in
theorem subgraphDensity_ge_0
    (H : SimpleGraph V) (G : SimpleGraph W)
    : 0 ≤ subgraphDensity H G
  := by
  dsimp [subgraphDensity]
  apply div_nonneg <;> simp

noncomputable def vert_iso_from_graph_iso
    (H : SimpleGraph V) (G : SimpleGraph W) (G₀ : G.Subgraph)
    (hG₀_iso : Nonempty (Subgraph.coe G₀ ≃g H))
    : {x // x ∈ G₀.verts } ≃ V
  := by
  let g : Subgraph.coe G₀ ≃g H := Classical.choice hG₀_iso
  let f₀ : {x // x ∈ G₀.verts } → V := g
  have hf₀ : Function.Bijective f₀ := RelIso.bijective g
  exact Equiv.ofBijective f₀ hf₀

omit [DecidableEq V] [DecidableEq W] in
theorem subgraphDensity_le_1
    (H : SimpleGraph V) (G : SimpleGraph W)
    : subgraphDensity H G ≤ 1
  := by
  dsimp [subgraphDensity]
  dsimp [subgraphCount]
  apply div_le_one_of_le
  . have := comb_card (univ : Finset W) (univ : Finset V).card
    simp at this; rw [←this]; simp
    let induced_subgraphs_iso_to_H :=
      { G' : G.Subgraph | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
    let f : induced_subgraphs_iso_to_H → Finset W := fun G' => Set.toFinset G'.val.verts
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

def graph_eqv (G₀ G₁ : SimpleGraph V) : Prop
  :=
  Nonempty (G₀ ≃g G₁)

omit [Fintype V] [DecidableEq V] in
theorem graph_eqv.refl (G : SimpleGraph V)
    : graph_eqv G G
  := by
  exact instNonemptyOfInhabited

omit [Fintype V] [DecidableEq V] in
theorem graph_eqv.symm
    : ∀ {G₀ G₁ : SimpleGraph V}, graph_eqv G₀ G₁ → graph_eqv G₁ G₀
  := by
  intro G₀ G₁ h
  let ⟨f, hf⟩ := h
  let f_symm : V ≃ V := f.symm
  have hf_symm : ∀ {a b : V}, G₀.Adj (f_symm a) (f_symm b) ↔ G₁.Adj a b := by
    intro a b
    have := @hf (f.symm a) (f.symm b)
    simp [Equiv.apply_symm_apply] at this
    exact Iff.symm this
  exact ⟨f_symm, hf_symm⟩

omit [Fintype V] [DecidableEq V] in
theorem graph_eqv.trans
    : ∀ {G₀ G₁ G₂ : SimpleGraph V}, graph_eqv G₀ G₁ → graph_eqv G₁ G₂ → graph_eqv G₀ G₂
  := by
  intro G₀ G₁ G₂ h01 h12
  dsimp [graph_eqv] at h01 h12
  let ⟨f01, hf01⟩ := h01
  let ⟨f12, hf12⟩ := h12
  let f : V ≃ V := f01.trans f12
  have : ∀ {a b : V}, G₂.Adj (f a) (f b) ↔ G₀.Adj a b := by
    intro a b
    exact Iff.trans hf12 hf01
  exact ⟨f, this⟩

instance graphSetoid (V : Type) [Fintype V] [DecidableEq V]
    : Setoid (SimpleGraph V)
  where
    r     := graph_eqv
    iseqv := {
      refl  := graph_eqv.refl,
      symm  := graph_eqv.symm,
      trans := graph_eqv.trans
    }

def QuotSimpleGraph (V : Type) [Fintype V] [DecidableEq V] : Type :=
  Quotient (graphSetoid V)

noncomputable instance quotSimpleGraphFintype (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (QuotSimpleGraph V) := Quotient.fintype (graphSetoid V)

def subgraphOfIso {G₁ G₂ : SimpleGraph V} (φ : G₁ ≃g G₂) (H₁ : G₁.Subgraph) : G₂.Subgraph
  where
  verts := φ.toEquiv '' H₁.verts
  Adj u v := H₁.Adj (φ.toEquiv.symm u) (φ.toEquiv.symm v)
  adj_sub := by
    intro x y h1_adj
    have g1_adj := H₁.adj_sub h1_adj
    exact φ.symm.map_adj_iff.mp g1_adj
  edge_vert := by
    intro x _ h1_edge
    use (φ.symm x)
    exact ⟨H₁.edge_vert h1_edge, by simp⟩
  symm := by
    intro _ _ h_adj
    exact H₁.symm h_adj

def relOfSubgraph
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (H₀ : Subgraph G₀) (H₁ : Subgraph G₁) : Prop
  :=
  H₁.verts = φ '' H₀.verts
  ∧ ∀ (u v : V), H₁.Adj (φ u) (φ v) = H₀.Adj u v

def relOfPredOnSubgraph
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop) : Prop
  :=
  ∀ (H₀ : Subgraph G₀) (H₁ : Subgraph G₁), (relOfSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def predIsoH
    (H : SimpleGraph U) (G : SimpleGraph V)
    : Subgraph G → Prop
  :=
  fun G' => Nonempty (Subgraph.coe G' ≃g H)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype U] [DecidableEq U] in
lemma predIsoH_related
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : relOfPredOnSubgraph φ (predIsoH H G₀) (predIsoH H G₁)
  := by
  dsimp [relOfPredOnSubgraph, predIsoH, relOfSubgraph]
  rintro H₀ H₁ ⟨h_vert, h_adj⟩
  constructor
  . rintro ⟨f₀, h_iso₀⟩
    let f₁ (w : H₁.verts) : U := f₀ (H₀.vert (φ.symm ↑w) (by aesop))
    have h_bij₁ : Function.Bijective f₁ := by
      dsimp [Function.Bijective, f₁]
      constructor
      . intro w₀ w₁ h_eq
        simp_all only [eq_iff_iff, Subgraph.coe_adj, Subtype.forall, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
        obtain ⟨_, property₀⟩ := w₀
        obtain ⟨_, property₁⟩ := w₁
        simp_all only
      . intro u
        let w : H₁.verts := H₁.vert (φ (f₀.symm u)) (by aesop)
        use w
        simp_all only [eq_iff_iff, Subgraph.coe_adj, Subtype.forall, RelIso.symm_apply_apply, Subtype.coe_eta, Equiv.apply_symm_apply]
    have h_iso₁ : ∀ {w₀ w₁ : H₁.verts}, H.Adj (f₁ w₀) (f₁ w₁) ↔ H₁.Adj w₀ w₁ := by
      intro w₀ w₁; dsimp [f₁]
      simp_all only [eq_iff_iff, Subgraph.coe_adj, Subtype.forall, Multiset.bijective_iff_map_univ_eq_univ, f₁]
      obtain ⟨_, property₀⟩ := w₀
      obtain ⟨_, property₁⟩ := w₁
      simp_all only
      simp_all only [Set.mem_image]
      obtain ⟨_, h₀⟩ := property₀
      obtain ⟨_, h₁⟩ := property₁
      obtain ⟨_, right₀⟩ := h₀
      obtain ⟨_, right₁⟩ := h₁
      subst right₀ right₁
      simp_all only [RelIso.symm_apply_apply]
    exact ⟨Equiv.ofBijective f₁ h_bij₁, h_iso₁⟩
  . rintro ⟨f₁, h_iso₁⟩
    have h_vert_inv : φ.symm '' H₁.verts = H₀.verts := by
      simp_all
      ext1 x
      simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
    let f₀ (v : H₀.verts) : U := f₁ (H₁.vert (φ ↑v) (by aesop))
    have h_bij₀ : Function.Bijective f₀ := by
      dsimp [Function.Bijective, f₀]
      constructor
      . intro v₀ v₁ h_eq
        simp_all
        obtain ⟨_, property₀⟩ := v₀
        obtain ⟨_, property₁⟩ := v₁
        simp_all only
      . intro u
        have : φ.symm (f₁.symm u) ∈ H₀.verts := by rw [←h_vert_inv]; simp
        let v : H₀.verts := H₀.vert (φ.symm (f₁.symm u)) this
        use v
        simp_all only [eq_iff_iff, Subgraph.coe_adj, Subtype.forall, Set.mem_image, forall_exists_index, RelIso.apply_symm_apply, Subtype.coe_eta, Equiv.apply_symm_apply]
    have h_iso₀ : ∀ {v₀ v₁ : H₀.verts}, H.Adj (f₀ v₀) (f₀ v₁) ↔ H₀.Adj v₀ v₁ := by
      intro v₀ v₁
      dsimp [f₀]
      rw [←h_adj v₀ v₁, h_iso₁]
      simp_all only [eq_iff_iff, Subgraph.coe_adj, Subtype.forall, Set.mem_image, forall_exists_index, Multiset.bijective_iff_map_univ_eq_univ, f₀]
    exact ⟨Equiv.ofBijective f₀ h_bij₀, h_iso₀⟩

def inducedSubgraph
    (G : SimpleGraph V) (S : Set V) : { G' : Subgraph G // G'.IsInduced }
  :=
  let G' : Subgraph G := {
    verts := S
    Adj := fun (u v : V) => G.Adj u v ∧ u ∈ S ∧ v ∈ S
    adj_sub := by
      intro v w a
      simp_all only
    edge_vert := by
      intro v w a
      simp_all only
    symm := fun u v h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  }
  let h_induced : G'.IsInduced := by
    intro u v h_u h_v h_uv
    dsimp at *
    exact ⟨h_uv, h_u, h_v⟩
  ⟨G', h_induced⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma inducedSubgraph_related
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (H₀ : Subgraph G₀) (h_ind₀ : H₀.IsInduced)
    : relOfSubgraph φ H₀ (inducedSubgraph G₁ (φ '' H₀.verts))
  := by
  dsimp [relOfSubgraph, inducedSubgraph]; simp
  intro u v
  constructor
  . rintro ⟨h_uv, h_u, h_v⟩
    apply h_ind₀ h_u h_v
    exact (Iso.map_adj_iff φ).mp h_uv
  . intro h_uv_H₀
    have h_uv_G₀ : G₀.Adj u v := H₀.adj_sub h_uv_H₀
    have h_u_H₀ : u ∈ H₀.verts := H₀.edge_vert h_uv_H₀
    have h_v_H₀ : v ∈ H₀.verts := H₀.edge_vert (H₀.symm h_uv_H₀)
    exact ⟨(Iso.map_adj_iff φ).mpr h_uv_G₀, h_u_H₀, h_v_H₀⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma inducedSubgraph_pred_iff
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop) (h_rel : relOfPredOnSubgraph φ p₀ p₁)
    (H₀ : Subgraph G₀) (h_ind₀ : H₀.IsInduced)
    : p₀ H₀ ↔ p₁ (inducedSubgraph G₁ (φ '' H₀.verts))
  := by
  have h_rel' := h_rel H₀ (inducedSubgraph G₁ (φ '' H₀.verts))
  exact h_rel' (inducedSubgraph_related φ H₀ h_ind₀)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype U] [DecidableEq U] in
lemma inducedSubgraph_predIsoH_iff
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : ∀ (H₀ : Subgraph G₀),
        H₀.IsInduced → (predIsoH H G₀ H₀ ↔ predIsoH H G₁ (inducedSubgraph G₁ (φ '' H₀.verts)))
  := by
  intro H₀ h_ind₀
  exact inducedSubgraph_pred_iff φ (predIsoH H G₀) (predIsoH H G₁) (predIsoH_related φ H) H₀ h_ind₀

noncomputable def isoSetOfInducedSubgraph
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop)
    (h_rel : relOfPredOnSubgraph φ p₀ p₁) (h_rel_inv : relOfPredOnSubgraph φ.symm p₁ p₀)
    : { G' : Subgraph G₀ | G'.IsInduced ∧ p₀ G' } ≃ { G' : Subgraph G₁ | G'.IsInduced ∧ p₁ G'}
  :=
  let S₀ := { G' : Subgraph G₀ | G'.IsInduced ∧ p₀ G' }
  let S₁ := { G' : Subgraph G₁ | G'.IsInduced ∧ p₁ G' }
  let f (s₀ : S₀) : S₁ := by
    dsimp [S₀] at s₀
    let ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
    let H₁ := (inducedSubgraph G₁ (φ '' H₀.verts)).1
    let h_ind₁ : H₁.IsInduced := (inducedSubgraph G₁ (φ '' H₀.verts)).2
    have : relOfSubgraph φ H₀ H₁ := inducedSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let H₀ := (inducedSubgraph G₀ (φ.symm '' H₁.verts)).1
    let h_ind₀ : H₀.IsInduced := (inducedSubgraph G₀ (φ.symm '' H₁.verts)).2
    have : relOfSubgraph φ.symm H₁ H₀ := inducedSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv, inducedSubgraph]
      ext u v
      . simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
      . simp
        constructor
        . rintro ⟨h_uv, h_u, h_v⟩
          apply h_ind₀
          · simp_all only
          · simp_all only
          · simp_all only
        . rintro h_uv
          exact ⟨H₀.adj_sub h_uv, H₀.edge_vert h_uv, H₀.edge_vert (H₀.symm h_uv)⟩
    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv, inducedSubgraph]
      ext u v
      . simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_image, exists_exists_and_eq_and, RelIso.apply_symm_apply, exists_eq_right, S₀, S₁, f_inv, f]
      . simp
        constructor
        . rintro ⟨h_uv, h_u, h_v⟩
          simp_all only [Set.coe_setOf, Set.mem_setOf_eq, S₀, S₁, f_inv, f]
          apply h_ind₁
          · simp_all only
          · simp_all only
          · simp_all only
        . rintro h_uv
          exact ⟨H₁.adj_sub h_uv, H₁.edge_vert h_uv, H₁.edge_vert (H₁.symm h_uv)⟩
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedSubgraphPair
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop)
    (h_rel : relOfPredOnSubgraph φ p₀ p₁) (h_rel_inv : relOfPredOnSubgraph φ.symm p₁ p₀)
    (p₂ : Subgraph G₀ → Prop) (p₃ : Subgraph G₁ → Prop)
    (h_rel' : relOfPredOnSubgraph φ p₂ p₃) (h_rel_inv' : relOfPredOnSubgraph φ.symm p₃ p₂)
    : { (G, G') : Subgraph G₀ × Subgraph G₀ |
          G.IsInduced ∧ p₀ G ∧
          G'.IsInduced ∧ p₂ G' ∧
          G.verts ∩ G'.verts = ∅ }
      ≃
      { (G, G') : Subgraph G₁ × Subgraph G₁ |
          G.IsInduced ∧ p₁ G ∧
          G'.IsInduced ∧ p₃ G' ∧
          G.verts ∩ G'.verts = ∅ }
  :=
  let S₀ := { (G, G') : Subgraph G₀ × Subgraph G₀ |
                G.IsInduced ∧ p₀ G ∧ G'.IsInduced ∧ p₂ G' ∧ G.verts ∩ G'.verts = ∅ }
  let S₁ := { (G, G') : Subgraph G₁ × Subgraph G₁ |
                G.IsInduced ∧ p₁ G ∧ G'.IsInduced ∧ p₃ G' ∧ G.verts ∩ G'.verts = ∅ }
  let f (s₀ : S₀) : S₁ := by
    dsimp [S₀] at s₀
    let ⟨⟨H₀,H₂⟩, ⟨h_ind₀, h_p₀, h_ind₂, h_p₂, h_inter⟩⟩ := s₀
    let H₁ := (inducedSubgraph G₁ (φ '' H₀.verts)).1
    let h_ind₁ : H₁.IsInduced := (inducedSubgraph G₁ (φ '' H₀.verts)).2
    have : relOfSubgraph φ H₀ H₁ := inducedSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    let H₃ := (inducedSubgraph G₁ (φ '' H₂.verts)).1
    let h_ind₃ : H₃.IsInduced := (inducedSubgraph G₁ (φ '' H₂.verts)).2
    have : relOfSubgraph φ H₂ H₃ := inducedSubgraph_related φ H₂ h_ind₂
    have h_p₃ : p₃ H₃ := (h_rel' H₂ H₃ this).mp h_p₂
    have h_inter' : H₁.verts ∩ H₃.verts = ∅ := by
      have h_img₁ : H₁.verts = φ '' H₀.verts := (inducedSubgraph_related φ H₀ h_ind₀).1
      have h_img₂ : H₃.verts = φ '' H₂.verts := (inducedSubgraph_related φ H₂ h_ind₂).1
      rw [h_img₁, h_img₂]
      by_contra h_contra
      push_neg at h_contra
      obtain ⟨v, h_v₁, h_v₂⟩ := h_contra
      obtain ⟨v₁, hv₁⟩ := h_v₁
      obtain ⟨v₂, hv₂⟩ := h_v₂
      have v_eq : v₁ = v₂ := φ.injective (hv₁.2.trans hv₂.2.symm)
      have v_mem : v₁ ∈ H₀.verts ∩ H₂.verts := Set.mem_inter hv₁.1 (v_eq ▸ hv₂.1)
      rw [h_inter] at v_mem
      exact v_mem
    exact ⟨⟨H₁, H₃⟩, ⟨h_ind₁, h_p₁, h_ind₃, h_p₃, h_inter'⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨⟨H₁,H₃⟩, ⟨h_ind₁, h_p₁, h_ind₃, h_p₃, h_inter⟩⟩ := s₁
    let H₀ := (inducedSubgraph G₀ (φ.symm '' H₁.verts)).1
    let h_ind₀ : H₀.IsInduced := (inducedSubgraph G₀ (φ.symm '' H₁.verts)).2
    have : relOfSubgraph φ.symm H₁ H₀ := inducedSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    let H₂ := (inducedSubgraph G₀ (φ.symm '' H₃.verts)).1
    let h_ind₂ : H₂.IsInduced := (inducedSubgraph G₀ (φ.symm '' H₃.verts)).2
    have : relOfSubgraph φ.symm H₃ H₂ := inducedSubgraph_related φ.symm H₃ h_ind₃
    have h_p₂ : p₂ H₂ := (h_rel_inv' H₃ H₂ this).mp h_p₃
    have h_inter' : H₀.verts ∩ H₂.verts = ∅ := by
      have h_img₁ : H₀.verts = φ.symm '' H₁.verts := (inducedSubgraph_related φ.symm H₁ h_ind₁).1
      have h_img₂ : H₂.verts = φ.symm '' H₃.verts := (inducedSubgraph_related φ.symm H₃ h_ind₃).1
      rw [h_img₁, h_img₂]
      by_contra h_contra
      push_neg at h_contra
      obtain ⟨v, h_v₁, h_v₂⟩ := h_contra
      obtain ⟨v₁, hv₁⟩ := h_v₁
      obtain ⟨v₂, hv₂⟩ := h_v₂
      have v_eq : v₁ = v₂ := φ.symm.injective (hv₁.2.trans hv₂.2.symm)
      have v_mem : v₁ ∈ H₁.verts ∩ H₃.verts := Set.mem_inter hv₁.1 (v_eq ▸ hv₂.1)
      rw [h_inter] at v_mem
      exact v_mem
    exact ⟨⟨H₀, H₂⟩, ⟨h_ind₀, h_p₀, h_ind₂, h_p₂, h_inter'⟩⟩
let f_bij : Function.Bijective f := by
  have h_leftinv : Function.LeftInverse f_inv f := by
    rintro ⟨⟨H₀, H₂⟩, ⟨h_ind₀, h_p₀, h_ind₂, h_p₂, h_inter⟩⟩
    dsimp [f, f_inv, inducedSubgraph]
    ext u v
    · simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
    · simp
      constructor
      · rintro ⟨h_uv, h_u, h_v⟩
        apply h_ind₀ <;> simp_all only
      · rintro h_uv
        exact ⟨H₀.adj_sub h_uv, H₀.edge_vert h_uv, H₀.edge_vert (H₀.symm h_uv)⟩
    · simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
    · simp
      constructor
      · rintro ⟨h_uv, h_u, h_v⟩
        apply h_ind₂ <;> simp_all only
      · rintro h_uv
        exact ⟨H₂.adj_sub h_uv, H₂.edge_vert h_uv, H₂.edge_vert (H₂.symm h_uv)⟩
  have h_rightinv : Function.RightInverse f_inv f := by
    rintro ⟨⟨H₁, H₃⟩, ⟨h_ind₁, h_p₁, h_ind₃, h_p₃, h_inter⟩⟩
    dsimp [f, f_inv, inducedSubgraph]
    ext u v
    · simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_image, exists_exists_and_eq_and, RelIso.apply_symm_apply,
      exists_eq_right, S₀, S₁, f_inv, f]
    · simp
      constructor
      · rintro ⟨h_uv, h_u, h_v⟩
        apply h_ind₁ <;> simp_all only
      · rintro h_uv
        exact ⟨H₁.adj_sub h_uv, H₁.edge_vert h_uv, H₁.edge_vert (H₁.symm h_uv)⟩
    · simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_image, exists_exists_and_eq_and, RelIso.apply_symm_apply,
      exists_eq_right, S₀, S₁, f_inv, f]
    · simp
      constructor
      · rintro ⟨h_uv, h_u, h_v⟩
        apply h_ind₃ <;> simp_all only
      · rintro h_uv
        exact ⟨H₃.adj_sub h_uv, H₃.edge_vert h_uv, H₃.edge_vert (H₃.symm h_uv)⟩
  exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedSubgraphIsoH
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
      ≃
      { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  :=
  isoSetOfInducedSubgraph φ
    (predIsoH H G₀)
    (predIsoH H G₁)
    (predIsoH_related φ H)
    (predIsoH_related φ.symm H)

noncomputable def isoSetOfInducedSubgraphPairIsoH
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H₁ : SimpleGraph T) (H₂ : SimpleGraph U)
    : { (G, G') : Subgraph G₀ × Subgraph G₀ |
          G.IsInduced ∧ Nonempty (Subgraph.coe G ≃g H₁) ∧
          G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₂) ∧
          G.verts ∩ G'.verts = ∅ }
      ≃
      { (G, G') : Subgraph G₁ × Subgraph G₁ |
          G.IsInduced ∧ Nonempty (Subgraph.coe G ≃g H₁) ∧
          G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₂) ∧
          G.verts ∩ G'.verts = ∅ }
  :=
  isoSetOfInducedSubgraphPair φ
    (predIsoH H₁ G₀)
    (predIsoH H₁ G₁)
    (predIsoH_related φ H₁)
    (predIsoH_related φ.symm H₁)
    (predIsoH H₂ G₀)
    (predIsoH H₂ G₁)
    (predIsoH_related φ H₂)
    (predIsoH_related φ.symm H₂)

omit [DecidableEq V] [DecidableEq W] in
lemma subgraphDensity_respects_eqv_on_G
    (H : SimpleGraph V) {G₀ G₁ : SimpleGraph W} (h_eqv : graph_eqv G₀ G₁)
    : subgraphDensity H G₀ = subgraphDensity H G₁
  := by
  dsimp [subgraphDensity]
  dsimp [graph_eqv] at h_eqv
  let φ : G₀ ≃g G₁ := Classical.choice h_eqv
  let S₀ := { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let S₁ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphIsoH φ H
  have h_count : subgraphCount H G₀ = subgraphCount H G₁ := by
    dsimp [subgraphCount]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  rw [h_count]

noncomputable def subgraphDensityLifted
    (H : SimpleGraph V) : QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift (fun G : SimpleGraph W => subgraphDensity H G)
  intro _ _ h_eqv
  exact subgraphDensity_respects_eqv_on_G H h_eqv

noncomputable def isoSetOfInducedSubgraphInG
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph W} (φ : H₀ ≃g H₁) (G : SimpleGraph U)
    : { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₀) }
      ≃
      { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₁) }
  := by
  let h : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g H₀) ↔ Nonempty (Subgraph.coe G' ≃g H₁) := by
    intro G'
    constructor
    . intro ⟨h_iso₀⟩
      have h_iso₁ : Subgraph.coe G' ≃g H₁ := φ.comp h_iso₀
      exact Nonempty.intro h_iso₁
    . intro ⟨h_iso₁⟩
      have h_iso₀ : Subgraph.coe G' ≃g H₀ := φ.symm.comp h_iso₁
      exact Nonempty.intro h_iso₀
  have : { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₀) }
         = { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₁) } :=
    Set.sep_ext_iff.mpr fun x _ ↦ h x
  exact Equiv.setCongr this

omit [DecidableEq V] in
lemma subgraphDensityLifted_respects_eqv_on_H
    {H₀ H₁ : SimpleGraph V} (h_eqv : graph_eqv H₀ H₁) (G : QuotSimpleGraph W)
    : subgraphDensityLifted H₀ G = subgraphDensityLifted H₁ G
  := by
  dsimp [subgraphDensityLifted]
  dsimp [graph_eqv] at h_eqv
  congr
  ext Greg
  let φ : H₀ ≃g H₁ := Classical.choice h_eqv
  let S₀ := { G' : Subgraph Greg | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₀) }
  let S₁ := { G' : Subgraph Greg | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₁) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphInG φ Greg
  have h_count : subgraphDensity H₀ Greg = subgraphDensity H₁ Greg := by
    dsimp [subgraphDensity]
    dsimp [subgraphCount]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  exact h_count

noncomputable def quotSubgraphDensity
    : QuotSimpleGraph V → QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift subgraphDensityLifted
  intro _ _ h_eqv
  ext G
  exact subgraphDensityLifted_respects_eqv_on_H h_eqv G

theorem quotSubgraphDensity_ge_0
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : 0 ≤ quotSubgraphDensity H G
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraphDensity_ge_0

theorem quotSubgraphDensity_le_1
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : quotSubgraphDensity H G ≤ 1
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraphDensity_le_1

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairDensity_respects_eqv_on_G
    (H₁ : SimpleGraph U) (H₂ : SimpleGraph V) {G G' : SimpleGraph W} (h_eqv : graph_eqv G G')
    : subgraphPairDensity H₁ H₂ G = subgraphPairDensity H₁ H₂ G'
  := by
  dsimp [subgraphPairDensity]
  dsimp [graph_eqv] at h_eqv
  let φ : G ≃g G' := Classical.choice h_eqv
  let S₀ := { (G₁, G₂) : Subgraph G × Subgraph G |
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅ }
  let S₁ := { (G₁, G₂) : Subgraph G' × Subgraph G' |
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅ }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphPairIsoH φ H₁ H₂
  have h_count : subgraphPairCount H₁ H₂ G = subgraphPairCount H₁ H₂ G' := by
    dsimp [subgraphPairCount]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  rw [h_count]

noncomputable def subgraphPairDensityLifted
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) : QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift (fun G : SimpleGraph W => subgraphPairDensity H₁ H₂ G)
  intro _ _ h_eqv
  exact subgraphPairDensity_respects_eqv_on_G H₁ H₂ h_eqv

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] in
lemma subgraph_to_eqv_graph_iff
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph W} (φ : H₀ ≃g H₁) (G : SimpleGraph X)
    : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g H₀) ↔ Nonempty (Subgraph.coe G' ≃g H₁)
  := by
  intro G'
  constructor
  · intro ⟨h_iso⟩
    have h_iso' : Subgraph.coe G' ≃g H₁ := φ.comp h_iso
    exact Nonempty.intro h_iso'
  · intro ⟨h_iso⟩
    have h_iso' : Subgraph.coe G' ≃g H₀ := φ.symm.comp h_iso
    exact Nonempty.intro h_iso'

noncomputable def isoSetOfInducedSubgraphPairInG
    {S₀ : SimpleGraph T} {S₁ : SimpleGraph U} (ψ : S₀ ≃g S₁)
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph W} (φ : H₀ ≃g H₁)
    (G : SimpleGraph X)
    : { (G₁, G₂) : Subgraph G × Subgraph G |
          G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g S₀) ∧
          G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₀) ∧
          G₁.verts ∩ G₂.verts = ∅ }
      ≃
      { (G₁, G₂) : Subgraph G × Subgraph G |
          G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g S₁) ∧
          G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₁) ∧
          G₁.verts ∩ G₂.verts = ∅ }
  := by
  let h_S : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g S₀) ↔ Nonempty (Subgraph.coe G' ≃g S₁) :=
    subgraph_to_eqv_graph_iff ψ G
  let h_H : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g H₀) ↔ Nonempty (Subgraph.coe G' ≃g H₁) :=
    subgraph_to_eqv_graph_iff φ G
  have : { (G₁, G₂) : Subgraph G × Subgraph G |
      G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g S₀) ∧
      G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₀) ∧
      G₁.verts ∩ G₂.verts = ∅ }
      ≃ { (G₁, G₂) : Subgraph G × Subgraph G |
      G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g S₁) ∧
      G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₁) ∧
      G₁.verts ∩ G₂.verts = ∅ } := by
    apply Equiv.subtypeEquiv (Equiv.refl (Subgraph G × Subgraph G))
    intro x
    constructor
    · intro ⟨h₁, h₂, h₃, h₄, h₅⟩
      exact ⟨h₁, (h_S x.1).mp h₂, h₃, (h_H x.2).mp h₄, h₅⟩
    · intro ⟨h₁, h₂, h₃, h₄, h₅⟩
      exact ⟨h₁, (h_S x.1).mpr h₂, h₃, (h_H x.2).mpr h₄, h₅⟩
  exact this

omit [DecidableEq U] [DecidableEq V] in
lemma subgraphPairDensityLifted_respects_eqv
    {S₀ : SimpleGraph U} {S₁ : SimpleGraph U} (h_eqv_S : graph_eqv S₀ S₁)
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph V} (h_eqv_H : graph_eqv H₀ H₁)
    (G : QuotSimpleGraph W)
    : subgraphPairDensityLifted S₀ H₀ G = subgraphPairDensityLifted S₁ H₁ G
  := by
  dsimp [subgraphPairDensityLifted]
  dsimp [graph_eqv] at h_eqv_S h_eqv_H
  congr
  ext Greg
  let ψ : S₀ ≃g S₁ := Classical.choice h_eqv_S
  let φ : H₀ ≃g H₁ := Classical.choice h_eqv_H
  let X₀ := { (G', G'') : Subgraph Greg × Subgraph Greg |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g S₀) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H₀) ∧
                G'.verts ∩ G''.verts = ∅ }
  let X₁ := { (G', G'') : Subgraph Greg × Subgraph Greg |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g S₁) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H₁) ∧
                G'.verts ∩ G''.verts = ∅ }
  let h_iso_X₀_X₁ : X₀ ≃ X₁ := isoSetOfInducedSubgraphPairInG ψ φ Greg
  have h_count : subgraphPairDensity S₀ H₀ Greg = subgraphPairDensity S₁ H₁ Greg := by
    dsimp [subgraphPairDensity]
    dsimp [subgraphPairCount]
    have : Fintype.card X₀ = Fintype.card X₁ := Fintype.card_congr h_iso_X₀_X₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, X₀, X₁]
  exact h_count

noncomputable def quotSubgraphPairDensity
    : QuotSimpleGraph U → QuotSimpleGraph V → QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift₂ subgraphPairDensityLifted
  . intro S _ _ h_eqv_H
    ext G
    exact subgraphPairDensityLifted_respects_eqv (graph_eqv.refl S) h_eqv_H G
  . intro _ _ H h_eqv_S
    ext G
    exact subgraphPairDensityLifted_respects_eqv h_eqv_S (graph_eqv.refl H) G

lemma quotSubgraphPairDensity_comm
    (H₁ : QuotSimpleGraph U) (H₂ : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : quotSubgraphPairDensity H₁ H₂ G = quotSubgraphPairDensity H₂ H₁ G
  := by
  sorry

-- set of all graphs (up to isomorphism) on n vertices
def IsoSimpleGraphWithSize (n : ℕ) : Type
  := QuotSimpleGraph (Fin n)

instance (n : ℕ) : Inhabited (IsoSimpleGraphWithSize n) where
  default := ⟦emptyGraph (Fin n)⟧

instance : Unique (IsoSimpleGraphWithSize 0) where
  uniq := by
    intro G
    have : G = ⟦Quotient.out G⟧ := by simp only [Quotient.out_eq]
    rw [this]
    apply Quotient.sound
    let H := Quotient.out G
    show graph_eqv H (emptyGraph (Fin 0))
    have H_iso : H ≃g emptyGraph (Fin 0) :=
      ⟨Equiv.refl _, by
        intro u v
        exact False.elim (Fin.elim0 u)
      ⟩
    exact Nonempty.intro H_iso

noncomputable instance (n : ℕ) : Fintype (IsoSimpleGraphWithSize n)
  := quotSimpleGraphFintype (Fin n)

-- set of all graphs (up to isomorphism) on a finite vertex set
def IsoSimpleGraph : Type
  := Σ (n : ℕ), IsoSimpleGraphWithSize n

instance : One IsoSimpleGraph where
  one := ⟨0, (default : IsoSimpleGraphWithSize 0)⟩

abbrev GraphVector : Type
  := IsoSimpleGraph →₀ ℝ

noncomputable instance : HMul ℝ GraphVector GraphVector where
  hMul r g := r • g

noncomputable instance : AddCommGroup GraphVector
  := Finsupp.instAddCommGroup

noncomputable instance : AddCommMonoid GraphVector
  := Finsupp.instAddCommMonoid

noncomputable instance : Module ℝ GraphVector
  := Finsupp.module IsoSimpleGraph ℝ

noncomputable def basisElementFromGraph (G : IsoSimpleGraph) : GraphVector
  := Finsupp.single G 1

noncomputable instance : One GraphVector where
  one := basisElementFromGraph 1

lemma quotSubgraphPairDensity_one
    (H G : IsoSimpleGraph)
    : quotSubgraphPairDensity (1 : IsoSimpleGraph).2 H.2 G.2 = quotSubgraphDensity H.2 G.2
  := by
  sorry

noncomputable def finiteGraphModuleBasis : Basis IsoSimpleGraph ℝ GraphVector
  :=
  have h_indep : LinearIndependent ℝ basisElementFromGraph := by
    rw [linearIndependent_iff'']
    intro s f h_supp h_sum G
    by_cases hG : G ∈ s
    · have : (∑ i ∈ s, f i • basisElementFromGraph i) G = 0 := by
        simp [h_sum]
      rw [← this, sum_eq_sum_diff_singleton_add hG _]
      simp [basisElementFromGraph, Finset.sum_apply']
      rw [Finset.sum_eq_zero]
      intro H hH
      have hHG : H ≠ G := by
        simp_all only [Finsupp.coe_zero, Pi.zero_apply, mem_sdiff, mem_singleton, ne_eq, not_false_eq_true]
      exact Finsupp.single_apply_eq_zero.mpr fun a ↦ h_supp H fun _ ↦ hHG (id (Eq.symm a))
    · exact h_supp G hG
  have h_span : ∀ f, f ∈ Submodule.span ℝ (Set.range basisElementFromGraph) := by
    intro f
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use f
    ext G
    simp [basisElementFromGraph]
  Basis.mk h_indep (fun v _ ↦ h_span v)

-- GraphVector is a free ℝ-module generated by IsoSimpleGraph
instance : Module.Free ℝ GraphVector := by
  apply Module.Free.of_basis
  exact finiteGraphModuleBasis

noncomputable def densityGraphSum
    (G : IsoSimpleGraph) (ℓ : ℕ) : GraphVector
  :=
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ F in ℓ_graphs, (quotSubgraphDensity G.2 F) • basisElementFromGraph ⟨ℓ,F⟩

noncomputable def ZeroSet : Submodule ℝ GraphVector
  :=
  let f (G : IsoSimpleGraph) (ℓ : ℕ) := basisElementFromGraph G - densityGraphSum G ℓ
  let S (G : IsoSimpleGraph) := (f G) '' {ℓ | G.1 ≤ ℓ}
  Submodule.span ℝ (⋃₀ Set.range S)

lemma zeroset_closed_under_add
    (h₁ h₂ : GraphVector) (h₁_zero : h₁ ∈ ZeroSet) (h₂_zero : h₂ ∈ ZeroSet)
    : h₁ + h₂ ∈ ZeroSet
  := by
  apply Submodule.add_mem <;> assumption

lemma zeroset_closed_under_multiple_sum
    (S : Finset IsoSimpleGraph) (f : IsoSimpleGraph → GraphVector)
    (h_zero : ∀ G ∈ S, f G ∈ ZeroSet)
    : ∑ G ∈ S, f G ∈ ZeroSet
  := by
  apply Submodule.sum_mem
  assumption

lemma zeroset_closed_under_smul
    (r : ℝ) (h : GraphVector) (h_zero : h ∈ ZeroSet)
    : r • h ∈ ZeroSet
  := by
  apply SMulMemClass.smul_mem
  assumption

def graph_algebra_eqv (g h : GraphVector) : Prop
  :=
  g - h ∈ ZeroSet

theorem graph_algebra_eqv.refl
    (g : GraphVector) : graph_algebra_eqv g g
  := by
  rw [graph_algebra_eqv]
  simp

theorem graph_algebra_eqv.symm
    : ∀ {g h : GraphVector}, graph_algebra_eqv g h → graph_algebra_eqv h g
  :=
  sub_mem_comm_iff.mp

theorem graph_algebra_eqv.trans
    : ∀ {f g h : GraphVector}, graph_algebra_eqv f g → graph_algebra_eqv g h → graph_algebra_eqv f h
  := by
  intros f g h hfg hgh
  rw [graph_algebra_eqv] at *
  have : f - h = (f - g) + (g - h) := by simp
  rw [this]
  exact zeroset_closed_under_add (f - g) (g - h) hfg hgh

instance graphVectorSetoid
    : Setoid GraphVector
  where
    r     := graph_algebra_eqv
    iseqv := {
      refl := graph_algebra_eqv.refl,
      symm := graph_algebra_eqv.symm,
      trans := graph_algebra_eqv.trans
    }

abbrev GraphAlgebra : Type :=
  Quotient graphVectorSetoid

noncomputable instance : Add GraphAlgebra where
  add := by
    apply Quotient.map₂ (· + ·)
    intro f f' hf g g' hg
    show graph_algebra_eqv (f + g) (f' + g')
    dsimp [graph_algebra_eqv]
    have h := zeroset_closed_under_add (f - f') (g - g') hf hg
    have : f - f' + (g - g') = (f + g) - (f' + g') := sub_add_sub_comm f f' g g'
    rw [←this]
    exact h

noncomputable instance : HSMul ℝ GraphAlgebra GraphAlgebra where
  hSMul r := by
    apply Quotient.map (r • ·)
    intro g g' hg
    simp
    show graph_algebra_eqv (r • g) (r • g')
    dsimp [graph_algebra_eqv]
    rw [← smul_sub]
    apply zeroset_closed_under_smul
    exact hg

instance : Zero GraphAlgebra where
  zero := ⟦0⟧

noncomputable instance : One GraphAlgebra where
  one := ⟦1⟧

noncomputable instance : Neg GraphAlgebra where
  neg := ((-1 : ℝ) • ·)

noncomputable def graph_mul
    (H₁ H₂ : IsoSimpleGraph) : GraphVector
  :=
  let ℓ := H₁.1 + H₂.1
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ G in ℓ_graphs, (quotSubgraphPairDensity H₁.2 H₂.2 G) • basisElementFromGraph ⟨ℓ, G⟩

lemma graph_mul_comm
    (G H : IsoSimpleGraph) : graph_mul G H = graph_mul H G
  := by
  dsimp [graph_mul]
  rw [add_comm]
  apply Finset.sum_congr
  · rfl
  · intros
    simp [quotSubgraphPairDensity_comm]

noncomputable instance : Mul GraphVector where
  mul g h := ∑ G in g.support, ∑ H in h.support, ((g G) * (h H)) • graph_mul G H

lemma graphVector_mul_comm
    (g h : GraphVector) : g * h = h * g
  := by
  show ∑ G in g.support, ∑ H in h.support, _ = ∑ H in h.support, ∑ G in g.support, _
  rw [Finset.sum_comm]
  apply Finset.sum_congr
  · rfl
  · intros
    apply Finset.sum_congr
    · rfl
    · intros
      rw [mul_comm, graph_mul_comm]

lemma graphVector_left_distrib
    (f g h : GraphVector) : f * (g + h) = f * g + f * h
  := by
  sorry

lemma graphVector_right_distrib
    (f g h : GraphVector) : (f + g) * h = f * h + g * h
  := by
  simp [graphVector_mul_comm, graphVector_left_distrib]

lemma graphVector_mul_zero
    (g : GraphVector) {k : GraphVector} (hk : k ∈ ZeroSet) : g * k ∈ ZeroSet
  := by
  sorry

lemma graph_mul_one
    (G : IsoSimpleGraph) : graph_algebra_eqv (graph_mul G 1) (basisElementFromGraph G)
  := by
  sorry

lemma graphVector_mul_one
    (g : GraphVector) : graph_algebra_eqv (g * 1) g
  := by
  show ∑ G in g.support, ∑ H in (1 : GraphVector).support, _ - g ∈ ZeroSet
  have supp_singleton : Finsupp.support (1 : GraphVector) = {1} := by
    show Finsupp.support (basisElementFromGraph 1) = {1}
    dsimp [basisElementFromGraph]
    rw [Finsupp.support_single_ne_zero _ (by simp)]
  rw [Finset.sum_comm, supp_singleton, Finset.sum_singleton]
  have : ∀ G ∈ g.support, (g G * (1 : GraphVector) 1) • graph_mul G 1 - (g G) • basisElementFromGraph G ∈ ZeroSet := by
    intro G hG
    have : (1 : GraphVector) 1 = 1 := by
      show (basisElementFromGraph 1) 1 = 1
      simp [basisElementFromGraph]
    rw [this, mul_one, ← smul_sub]
    apply zeroset_closed_under_smul
    exact graph_mul_one G
  sorry

noncomputable instance : Mul GraphAlgebra where
  mul := by
    apply Quotient.map₂ (· * ·)
    intro g' g hg h' h hh
    show graph_algebra_eqv (g' * h') (g * h)
    dsimp [graph_algebra_eqv]
    let kg := g' - g
    let kh := h' - h
    have hkg : kg ∈ ZeroSet := hg
    have hkh : kh ∈ ZeroSet := hh
    have : g' * h' = (g + kg) * (h + kh) := by
      rw [← sub_add_cancel g' g, ← sub_add_cancel h' h]
      simp only [kg, kh, add_comm]
    rw [this]
    rw [graphVector_left_distrib, graphVector_right_distrib, graphVector_right_distrib]
    rw [add_assoc, add_sub_cancel_left]
    apply zeroset_closed_under_add
    · rw [graphVector_mul_comm]
      exact graphVector_mul_zero h hkg
    · apply zeroset_closed_under_add
      · exact graphVector_mul_zero g hkh
      · exact graphVector_mul_zero kg hkh

lemma graphAlgebra_mul_comm
    (g h : GraphAlgebra) : g * h = h * g
  := by
  rw [← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  rw [graphVector_mul_comm]

lemma graphAlgebra_left_distrib
    (f g h : GraphAlgebra) : f * (g + h) = f * g + f * h
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  rw [graphVector_left_distrib]

lemma graphAlgebra_mul_zero
    (g : GraphAlgebra) : g * 0 = 0
  := by
  rcases Quotient.exists_rep g with ⟨grep, hgrep⟩
  rw [← hgrep]
  apply Quotient.sound
  simp
  show grep * 0 - 0 ∈ ZeroSet
  rw [sub_zero]
  apply graphVector_mul_zero grep (by simp)

lemma graphAlgebra_mul_one
    (g : GraphAlgebra) : g * 1 = g
  := by
  rcases Quotient.exists_rep g with ⟨grep, hgrep⟩
  rw [← hgrep]
  apply Quotient.sound
  simp
  apply graphVector_mul_one

noncomputable instance : Ring GraphAlgebra where
  add := (· + ·)
  add_assoc a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c]
    apply Quotient.sound
    simp_all
    rw [add_assoc]
  zero := 0
  zero_add a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  add_zero a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  neg := -(·)
  add_comm a b := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    apply Quotient.sound
    simp
    rw [add_comm]
  neg_add_cancel a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp; rfl
  mul := (· * ·)
  mul_assoc := sorry
  zero_mul a := by
    rw [graphAlgebra_mul_comm]
    apply graphAlgebra_mul_zero
  mul_zero := graphAlgebra_mul_zero
  one := 1
  one_mul a := by
    rw [graphAlgebra_mul_comm]
    apply graphAlgebra_mul_one
  mul_one := graphAlgebra_mul_one
  left_distrib := graphAlgebra_left_distrib
  right_distrib a b c := by
    simp [graphAlgebra_mul_comm, graphAlgebra_left_distrib]
  nsmul n g := (n : ℝ) • g
  nsmul_zero g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  nsmul_succ n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul z g := (z : ℝ) • g
  zsmul_zero' g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  zsmul_succ' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul_neg' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [← neg_smul, neg_add_rev]

noncomputable instance : CommRing GraphAlgebra where
  mul_comm := graphAlgebra_mul_comm

noncomputable instance : Algebra ℝ GraphAlgebra where
  smul r g := r • g
  toFun r := r • 1
  map_zero' := by
    simp
    apply Quotient.sound
    simp; rfl
  map_one' := by
    simp
    apply Quotient.sound
    simp; rfl
  map_add' := by
    intros; simp
    apply Quotient.sound
    simp
    rw [add_smul]
  map_mul' := sorry
  smul_def' := sorry
  commutes' := by
    intros; simp
    rw [mul_comm]
