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

noncomputable def subgraph_fintype
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Fintype (Subgraph G) :=
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

noncomputable instance subgraph_set_fintype
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : Subgraph G → Prop) :
    Fintype { G' : Subgraph G | p G' } := by
  have : Fintype (Subgraph G) := subgraph_fintype G
  exact inferInstance

noncomputable def subgraph_count
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) : ℕ
  :=
  let p (G' : Subgraph G) : Prop := G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H)
  { G' : Subgraph G | p G' }.toFinset.card

noncomputable def subgraph_density
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraph_count H G
  let num_of_all_induced_subgraph := (univ : Finset W).card.choose (univ : Finset V).card
  subgraph_cnt / num_of_all_induced_subgraph

theorem subgraph_density_ge_0 {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
          (H : SimpleGraph V) (G : SimpleGraph W)
          : 0 ≤ subgraph_density H G := by
  dsimp [subgraph_density]
  apply div_nonneg <;> simp

noncomputable def vert_iso_from_graph_iso {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (H : SimpleGraph V) (G : SimpleGraph W) (G₀ : G.Subgraph)
  (hG₀_iso : Nonempty (Subgraph.coe G₀ ≃g H))
  : {x // x ∈ G₀.verts } ≃ V := by
    let g : Subgraph.coe G₀ ≃g H := Classical.choice hG₀_iso
    let f₀ : {x // x ∈ G₀.verts } → V := g
    have hf₀ : Function.Bijective f₀ := RelIso.bijective g
    exact Equiv.ofBijective f₀ hf₀

theorem subgraph_density_le_1 {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
          (H : SimpleGraph V) (G : SimpleGraph W)
          : subgraph_density H G ≤ 1
  := by
  dsimp [subgraph_density]
  dsimp [subgraph_count]
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

def graph_eqv {V : Type} [Fintype V] [DecidableEq V] (G₀ G₁ : SimpleGraph V) : Prop
  :=
  Nonempty (G₀ ≃g G₁)

theorem graph_eqv.refl {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    : graph_eqv G G
  := by
  exact instNonemptyOfInhabited

theorem graph_eqv.symm {V : Type} [Fintype V] [DecidableEq V]
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

theorem graph_eqv.trans {V : Type} [Fintype V] [DecidableEq V]
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
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (H₀ : Subgraph G₀) (H₁ : Subgraph G₁) : Prop
  :=
  H₁.verts = φ '' H₀.verts
  ∧ ∀ (u v : V), H₁.Adj (φ u) (φ v) = H₀.Adj u v

def relOfPredOnSubgraph
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop) : Prop
  :=
  ∀ (H₀ : Subgraph G₀) (H₁ : Subgraph G₁), (relOfSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def predIsoH
    {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (H : SimpleGraph U) (G : SimpleGraph V)
    : Subgraph G → Prop
  :=
  fun G' => Nonempty (Subgraph.coe G' ≃g H)

lemma predIsoH_related
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
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
    {V : Type} [DecidableEq V]
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

lemma inducedSubgraph_related
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
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

lemma inducedSubgraph_pred_iff
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop) (h_rel : relOfPredOnSubgraph φ p₀ p₁)
    (H₀ : Subgraph G₀) (h_ind₀ : H₀.IsInduced)
    : p₀ H₀ ↔ p₁ (inducedSubgraph G₁ (φ '' H₀.verts))
  := by
  have h_rel' := h_rel H₀ (inducedSubgraph G₁ (φ '' H₀.verts))
  exact h_rel' (inducedSubgraph_related φ H₀ h_ind₀)

lemma inducedSubgraph_predIsoH_iff
    {U V W: Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : ∀ (H₀ : Subgraph G₀),
        H₀.IsInduced → (predIsoH H G₀ H₀ ↔ predIsoH H G₁ (inducedSubgraph G₁ (φ '' H₀.verts)))
  := by
  intro H₀ h_ind₀
  exact inducedSubgraph_pred_iff φ (predIsoH H G₀) (predIsoH H G₁) (predIsoH_related φ H) H₀ h_ind₀

noncomputable def isoSetOfInducedSubgraph
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
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

noncomputable def isoSetOfInducedSubgraphIsoH
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
      ≃ { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  :=
  isoSetOfInducedSubgraph φ
    (predIsoH H G₀)
    (predIsoH H G₁)
    (predIsoH_related φ H)
    (predIsoH_related φ.symm H)

lemma subgraph_density_respects_eqv_on_G
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G₀ G₁ : SimpleGraph W)
    (h_eqv : graph_eqv G₀ G₁)
    : subgraph_density H G₀ = subgraph_density H G₁
  := by
  dsimp [subgraph_density]
  dsimp [graph_eqv] at h_eqv
  let φ : G₀ ≃g G₁ := Classical.choice h_eqv
  let S₀ := { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let S₁ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphIsoH φ H
  have h_count : subgraph_count H G₀ = subgraph_count H G₁ := by
    dsimp [subgraph_count]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  rw [h_count]

noncomputable def subgraph_density_lift_G
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) : QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift (fun G : SimpleGraph W => subgraph_density H G)
  intro G₀ G₁ h_eqv
  exact subgraph_density_respects_eqv_on_G H G₀ G₁ h_eqv

noncomputable def isoSetOfInducedSubgraphInG
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph W} (φ : H₀ ≃g H₁) (G : SimpleGraph U)
    : { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₀) }
      ≃ { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₁) }
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

lemma subgraph_density_lift_G_respects_eqv_on_H
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₀ H₁ : SimpleGraph V) (G : QuotSimpleGraph W)
    (h_eqv : graph_eqv H₀ H₁)
    : subgraph_density_lift_G H₀ G = subgraph_density_lift_G H₁ G
  := by
  dsimp [subgraph_density_lift_G]
  dsimp [graph_eqv] at h_eqv
  congr
  ext Greg
  let φ : H₀ ≃g H₁ := Classical.choice h_eqv
  let S₀ := { G' : Subgraph Greg | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₀) }
  let S₁ := { G' : Subgraph Greg | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₁) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphInG φ Greg
  have h_count : subgraph_density H₀ Greg = subgraph_density H₁ Greg := by
    dsimp [subgraph_density]
    dsimp [subgraph_count]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  exact h_count

noncomputable def subgraph_density_quot
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    : QuotSimpleGraph V → QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift subgraph_density_lift_G
  intro H₀ H₁ h_eqv
  ext G
  exact subgraph_density_lift_G_respects_eqv_on_H H₀ H₁ G h_eqv

theorem subgraph_density_quot_ge_0
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : 0 ≤ subgraph_density_quot H G
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraph_density_ge_0

theorem subgraph_density_quot_le_1
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : subgraph_density_quot H G ≤ 1
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraph_density_le_1

-- set of all graphs (up to isomorphism) on n vertices
def IsoSimpleGraphWithSize (n : ℕ) : Type
  := QuotSimpleGraph (Fin n)

noncomputable instance (n : ℕ) : Fintype (IsoSimpleGraphWithSize n)
  := quotSimpleGraphFintype (Fin n)

-- set of all graphs (up to isomorphism) on a finite vertex set
def IsoSimpleGraph : Type
  := Σ (n : ℕ), IsoSimpleGraphWithSize n

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

instance (n : ℕ) : Inhabited (IsoSimpleGraphWithSize n) where
  default := sorry

instance : Unique (IsoSimpleGraphWithSize 0) where
  uniq := sorry

theorem one_unique : ∃! _ : IsoSimpleGraphWithSize 0, true
  := by
  simp only [exists_unique_iff_exists, exists_const]

noncomputable instance : One GraphVector where
  one := basisElementFromGraph ⟨0, Classical.choose one_unique⟩

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
  ∑ F in ℓ_graphs, (subgraph_density_quot G.2 F) • basisElementFromGraph ⟨ℓ,F⟩

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

noncomputable instance subgraph_set_fintype'
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Fintype (Subgraph G × Subgraph G) := by
  have : Fintype (Subgraph G) := subgraph_fintype G
  exact inferInstance

noncomputable def subgraph_count'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℕ :=
  let p (G₁ G₂ : Subgraph G) : Prop :=
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅
  { (G₁, G₂) : Subgraph G × Subgraph G | p G₁ G₂ }.toFinset.card

noncomputable def subgraph_density'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℚ :=
  let subgraph_cnt := subgraph_count' H₁ H₂ G
  let W_card := Fintype.card W
  let V_card := Fintype.card V
  let U_card := Fintype.card U
  let num_of_all_induced_subgraphs := W_card.choose V_card * (W_card - V_card).choose U_card
  subgraph_cnt / num_of_all_induced_subgraphs

noncomputable def isoSetOfInducedSubgraphIsoH'
    {T U V W : Type} [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H₁ : SimpleGraph T) (H₂ : SimpleGraph U)
    : { (G, G') : Subgraph G₀ × Subgraph G₀ |
    G.IsInduced ∧ Nonempty (Subgraph.coe G ≃g H₁) ∧
    G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₂) ∧
    G.verts ∩ G'.verts = ∅ }
      ≃ { (G, G') : Subgraph G₁ × Subgraph G₁ |
    G.IsInduced ∧ Nonempty (Subgraph.coe G ≃g H₁) ∧
    G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₂) ∧
    G.verts ∩ G'.verts = ∅ }
  := by
  sorry

lemma subgraph_density_respects_eqv_on_G'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G G' : SimpleGraph W)
    (h_eqv : graph_eqv G G')
    : subgraph_density' H₁ H₂ G = subgraph_density' H₁ H₂ G' := by
  dsimp [subgraph_density']
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
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphIsoH' φ H₁ H₂
  have h_count : subgraph_count' H₁ H₂ G = subgraph_count' H₁ H₂ G' := by
    dsimp [subgraph_count']
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  rw [h_count]

noncomputable def subgraph_density_lift_G'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) : QuotSimpleGraph W → ℚ := by
  apply Quot.lift (fun G : SimpleGraph W => subgraph_density' H₁ H₂ G)
  intro G G' h_eqv
  exact subgraph_density_respects_eqv_on_G' H₁ H₂ G G' h_eqv

lemma subgraph_density_lift_G_respects_eqv_on_H₂'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ : SimpleGraph V) (H₂ H₂' : SimpleGraph U) (G : QuotSimpleGraph W)
    (h_eqv : graph_eqv H₂ H₂')
    : subgraph_density_lift_G' H₁ H₂ G = subgraph_density_lift_G' H₁ H₂' G := by
  sorry

noncomputable def subgraph_density_lift_G_H₁'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ : SimpleGraph V)
    : QuotSimpleGraph U → QuotSimpleGraph W → ℚ := by
  apply Quot.lift (fun H₂ : SimpleGraph U => subgraph_density_lift_G' H₁ H₂)
  intro H₂ H₂' h_eqv
  ext G
  exact subgraph_density_lift_G_respects_eqv_on_H₂' H₁ H₂ H₂' G h_eqv

lemma subgraph_density_lift_G_H₂_respects_eqv_on_H₁'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₁ H₁' : SimpleGraph V) (H₂ : QuotSimpleGraph U) (G : QuotSimpleGraph W)
    (h_eqv : graph_eqv H₁ H₁')
    : subgraph_density_lift_G_H₁' H₁ H₂ G = subgraph_density_lift_G_H₁' H₁' H₂ G := by
  sorry

noncomputable def subgraph_density_quot'
    {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    : QuotSimpleGraph V → QuotSimpleGraph U → QuotSimpleGraph W → ℚ := by
  apply Quot.lift subgraph_density_lift_G_H₁'
  intro H₁ H₁' h_eqv
  ext H₂ G
  exact subgraph_density_lift_G_H₂_respects_eqv_on_H₁' H₁ H₁' H₂ G h_eqv

noncomputable def graph_mul
    (H₁ H₂ : IsoSimpleGraph) : GraphVector :=
  let ℓ := H₁.1 + H₂.1
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ G in ℓ_graphs, (subgraph_density_quot' H₁.2 H₂.2 G) • basisElementFromGraph ⟨ℓ, G⟩

noncomputable instance : Mul GraphVector where
  mul g h := ∑ G in g.support, ∑ H in h.support, (g G) * (h H) • graph_mul G H

noncomputable instance : Mul GraphAlgebra where
  mul := by
    apply Quotient.map₂ (· * ·)
    intro g g' hg h h' hh
    simp
    sorry

noncomputable instance : Ring GraphAlgebra where
  add := (· + ·)
  add_assoc := sorry
  zero := 0
  zero_add := sorry
  add_zero := sorry
  neg := -(·)
  add_comm := sorry
  neg_add_cancel := sorry
  mul := (· * ·)
  mul_assoc := sorry
  zero_mul := sorry
  mul_zero := sorry
  one := 1
  one_mul := sorry
  mul_one := sorry
  left_distrib := sorry
  right_distrib := sorry
  nsmul n g := (n : ℝ) • g
  nsmul_zero := by
    intro g; simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  nsmul_succ := by
    intro n g; simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul z g := (z : ℝ) • g
  zsmul_zero' := by
    intro g; simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  zsmul_succ' := by
    intro n g; simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul_neg' := sorry

noncomputable instance : CommRing GraphAlgebra where
  mul_comm := sorry
