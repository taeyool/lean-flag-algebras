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

noncomputable instance subgraph_set_fintype
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : Subgraph G → Prop) :
    Fintype { G' : Subgraph G | p G' } :=
  let f : { G' : Subgraph G | p G' } → Set V × Set (V × V) :=
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
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  let p (G' : Subgraph G) : Prop := G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H)
  { G' : Subgraph G | p G' }.toFinset.card

noncomputable def subgraph_density {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (H : SimpleGraph V) (G : SimpleGraph W) : ℚ :=
  let subgraph_cnt := subgraph_count H G
  let num_of_all_induced_subgraphs := (univ : Finset W).card.choose (univ : Finset V).card
  subgraph_cnt / num_of_all_induced_subgraphs

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
          : subgraph_density H G ≤ 1 := by
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

def graph_eqv {V : Type} [Fintype V] [DecidableEq V] (G₀ G₁ : SimpleGraph V) : Prop :=
  Nonempty (G₀ ≃g G₁)

theorem graph_eqv.refl {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    : graph_eqv G G := by
  exact instNonemptyOfInhabited

theorem graph_eqv.symm {V : Type} [Fintype V] [DecidableEq V]
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

theorem graph_eqv.trans {V : Type} [Fintype V] [DecidableEq V]
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

theorem is_equivalence {V : Type} [Fintype V] [DecidableEq V]
    : Equivalence (@graph_eqv V _ _) :=
  { refl := graph_eqv.refl, symm := graph_eqv.symm, trans := graph_eqv.trans }

instance graphSetoid (V : Type) [Fintype V] [DecidableEq V]
    : Setoid (SimpleGraph V) where
  r     := graph_eqv
  iseqv := is_equivalence

def QuotSimpleGraph (V : Type) [Fintype V] [DecidableEq V] : Type :=
  Quotient (graphSetoid V)

noncomputable instance quotSimpleGraphFintype (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (QuotSimpleGraph V) := Quotient.fintype (graphSetoid V)

def subgraphOfIso {G₁ G₂ : SimpleGraph V} (φ : G₁ ≃g G₂) (H₁ : G₁.Subgraph) : G₂.Subgraph where
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

lemma subgraph_map_of_iso {G₁ G₂ : SimpleGraph W} (φ : G₁ ≃g G₂) (H : SimpleGraph V) :
  ∀ (H₁ : Subgraph G₁), ∃ (H₂ : Subgraph G₂),
  H₁.IsInduced ↔ H₂.IsInduced ∧
  (∀ H : SimpleGraph V, Nonempty (Subgraph.coe H₁ ≃g H) ↔ Nonempty (Subgraph.coe H₂ ≃g H)) := by
  intro H₁
  let H₂ := subgraphOfIso φ H₁
  use H₂
  apply Iff.intro
  · intro H1_ind
    constructor
    · unfold Subgraph.IsInduced
      unfold Subgraph.IsInduced at H1_ind
      intro x y x_verts y_verts x_adj


      sorry
    sorry
  -- · intro h_induced v₁ v₂ hv₁ hv₂ he
  --     obtain ⟨u₁, hu₁, hv₁'⟩ := φ.surj_on_image _ hv₁
  --     obtain ⟨u₂, hu₂, hv₂'⟩ := φ.surj_on_image _ hv₂
  --     rw [←hv₁', ←hv₂']
  --     exact h_induced u₁ u₂ hu₁ hu₂ (φ.inj_edge he)
  --   · intro h_induced v₁ v₂ hv₁ hv₂ he
  --     exact h_induced (φ v₁) (φ v₂)
  --       (mem_image_of_mem _ hv₁)
  --       (mem_image_of_mem _ hv₂)
  --       (φ.map_edge_mem he)
  sorry

def inducedSubgraph {V : Type} [DecidableEq V]
      (G : SimpleGraph V) (S : Set V) : { G' : Subgraph G // G'.IsInduced }
  :=
  let G' : Subgraph G := {
    verts := S
    Adj := fun (u v : V) => G.Adj u v ∧ u ∈ S ∧ v ∈ S
    adj_sub := by aesop
    edge_vert := by aesop
    symm := fun u v h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  }
  let h_induced : G'.IsInduced := by
    intro u v h_u h_v h_uv
    dsimp at *
    exact ⟨h_uv, h_u, h_v⟩
  ⟨G', h_induced⟩

noncomputable def mapOfInducedSubgraphs {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G₀ : SimpleGraph V) (G₁ : SimpleGraph W) (φ : G₀ ≃g G₁)
    : { G' : Subgraph G₀ | G'.IsInduced } → { G' : Subgraph G₁ | G'.IsInduced } :=
  fun ⟨G₀_sub, _⟩ => inducedSubgraph G₁ (φ '' G₀_sub.verts)

lemma inv_map_of_induced_subgraphs {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G₀ : SimpleGraph V) (G₁ : SimpleGraph W) (φ : G₀ ≃g G₁)
    : (mapOfInducedSubgraphs G₁ G₀ φ.symm) ∘ (mapOfInducedSubgraphs G₀ G₁ φ) = id := by
  ext ⟨G',h_ind_G'⟩ u v
  dsimp [mapOfInducedSubgraphs, inducedSubgraph]
  . aesop
  . dsimp [mapOfInducedSubgraphs, inducedSubgraph]
    simp
    constructor
    . rintro ⟨h_uv, h_u, h_v⟩
      dsimp [Subgraph.IsInduced] at h_ind_G'
      exact h_ind_G' h_u h_v h_uv
    . rintro h_uv
      exact ⟨G'.adj_sub h_uv, G'.edge_vert h_uv, G'.edge_vert (G'.symm h_uv)⟩

noncomputable def iso_subgraph_sets_from_iso_graphs {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (H : SimpleGraph V) (G₀ G₁ : SimpleGraph W) (φ : G₀ ≃g G₁)
      : { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
        ≃ { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  := by
  let g : { G' : Subgraph G₀ // G'.IsInduced } → {G' : Subgraph G₁ // G'.IsInduced} :=
    mapOfInducedSubgraphs G₀ G₁ φ
  let g_inv : { G' : Subgraph G₁ // G'.IsInduced } → {G' : Subgraph G₀ // G'.IsInduced} :=
    mapOfInducedSubgraphs G₁ G₀ φ.symm
  have g_bij : Function.Bijective g := by
    have h_leftinv : Function.LeftInverse g_inv g := by
      intro G'_ind
      dsimp [g, g_inv]
      exact congr_fun (inv_map_of_induced_subgraphs G₀ G₁ φ) G'_ind
    have h_rightinv : Function.RightInverse g_inv g := by
      intro G'_ind
      dsimp [g, g_inv]
      exact congr_fun (inv_map_of_induced_subgraphs G₁ G₀ φ.symm) G'_ind
    exact Function.bijective_iff_has_inverse.mpr ⟨g_inv, h_leftinv, h_rightinv⟩
  let S₀ := { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let S₁ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  have subgraph_mapping := subgraph_map_of_iso φ H
  let f (G' : S₀) : S₁ := by
    obtain mapped_subgraph := subgraph_mapping G'
    let H₂ := Classical.choose mapped_subgraph
    let h_mapped_subgraph := Classical.choose_spec mapped_subgraph
    use H₂
    constructor
    · obtain ⟨h_ind, _⟩ := h_mapped_subgraph.1 G'.property.1
      exact h_ind
    · obtain ⟨_, h_iso⟩ := h_mapped_subgraph.1 G'.property.1
      apply h_iso at H
      rw [<-H]
      exact G'.property.2
  have f_bij : Function.Bijective f := sorry
  exact Equiv.ofBijective f f_bij

lemma subgraph_density_respects_eqv_on_G
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) (G₀ G₁ : SimpleGraph W)
    (h_eqv : graph_eqv G₀ G₁)
    : subgraph_density H G₀ = subgraph_density H G₁ := by
  dsimp [subgraph_density]
  dsimp [graph_eqv] at h_eqv
  let φ : G₀ ≃g G₁ := Classical.choice h_eqv
  let S₀ := { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let S₁ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := iso_subgraph_sets_from_iso_graphs H G₀ G₁ φ
  have h_count : subgraph_count H G₀ = subgraph_count H G₁ := by
    dsimp [subgraph_count]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    aesop
  rw [h_count]

noncomputable def subgraph_density_lift_G
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : SimpleGraph V) : QuotSimpleGraph W → ℚ := by
  apply Quot.lift (fun G : SimpleGraph W => subgraph_density H G)
  intro G₀ G₁ h_eqv
  exact subgraph_density_respects_eqv_on_G H G₀ G₁ h_eqv

lemma subgraph_density_lift_G_respects_eqv_on_H
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H₀ H₁ : SimpleGraph V) (G : QuotSimpleGraph W)
    (h_eqv : graph_eqv H₀ H₁)
    : subgraph_density_lift_G H₀ G = subgraph_density_lift_G H₁ G := by
  sorry

-- quotient version of subgraph_density
noncomputable def subgraph_density_quot
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    : QuotSimpleGraph V → QuotSimpleGraph W → ℚ := by
  apply Quot.lift subgraph_density_lift_G
  intro H₀ H₁ h_eqv
  ext G
  exact subgraph_density_lift_G_respects_eqv_on_H H₀ H₁ G h_eqv

theorem subgraph_density_quot_ge_0
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : 0 ≤ subgraph_density_quot H G := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraph_density_ge_0

theorem subgraph_density_quot_le_1
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : subgraph_density_quot H G ≤ 1 := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraph_density_le_1

noncomputable def all_graphs_on_vertex_set
    (V : Type) [Fintype V] [DecidableEq V] : Finset (SimpleGraph V) :=
  Set.toFinset { G : SimpleGraph V | true }

lemma sum_subgraph_counts
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (h_card : Fintype.card V ≤ Fintype.card W)
    : ∑ F in (all_graphs_on_vertex_set V), subgraph_count F G = (Fintype.card W).choose (Fintype.card V) := by
  dsimp [all_graphs_on_vertex_set, subgraph_count]
  let h := comb_card (univ : Finset W) (Fintype.card V)
  dsimp at h
  rw [← h]
  sorry

theorem sum_subgraph_densities_eq_one
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
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
  {U V W : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (H : SimpleGraph V) (G : SimpleGraph W)
  (h_card : Fintype.card V ≤ Fintype.card U ∧ Fintype.card U ≤ Fintype.card W)
  : subgraph_density H G = ∑ F in (all_graphs_on_vertex_set U), subgraph_density H F * subgraph_density F G := by
  sorry

-- set of all graphs (up to isomorphism) on a finite vertex set
def FiniteSimpleGraph := Σ (n : ℕ), QuotSimpleGraph (Fin n)

-- free ℝ-module generated by FiniteSimpleGraph
abbrev FiniteGraphModule := FiniteSimpleGraph →₀ ℝ

noncomputable instance : AddCommGroup FiniteGraphModule := Finsupp.instAddCommGroup

noncomputable instance : AddCommMonoid FiniteGraphModule := Finsupp.instAddCommMonoid

noncomputable instance : Module ℝ FiniteGraphModule := Finsupp.module FiniteSimpleGraph ℝ

noncomputable def basis_element_from_graph : FiniteSimpleGraph → FiniteGraphModule
  := fun G => Finsupp.single G 1

#check Finsupp.sum

noncomputable def FiniteGraphModuleBasis : Basis (FiniteSimpleGraph) ℝ FiniteGraphModule :=
  have h_indep : LinearIndependent ℝ basis_element_from_graph := by
    rw [linearIndependent_iff'']
    intro s f h_supp h_sum G
    by_cases hG : G ∈ s
    · have : (∑ i ∈ s, f i • basis_element_from_graph i) G = 0 := by
        simp [h_sum]
      rw [← this, sum_eq_sum_diff_singleton_add hG _]
      simp [basis_element_from_graph, Finset.sum_apply']
      rw [Finset.sum_eq_zero]
      intro H hH
      have hHG : H ≠ G := by
        simp_all only [Finsupp.coe_zero, Pi.zero_apply, mem_sdiff, mem_singleton, ne_eq, not_false_eq_true]
      exact Finsupp.single_apply_eq_zero.mpr fun a ↦ h_supp H fun _ ↦ hHG (id (Eq.symm a))
    · exact h_supp G hG
  have h_span : ∀ f, f ∈ Submodule.span ℝ (Set.range basis_element_from_graph) := by
    intro f
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use f
    ext G
    simp [basis_element_from_graph]
  Basis.mk h_indep (fun v _ ↦ h_span v)

instance : Module.Free ℝ FiniteGraphModule := by
  apply Module.Free.of_basis
  exact FiniteGraphModuleBasis

noncomputable def ZeroSubspace : Submodule ℝ FiniteGraphModule :=
  Submodule.span ℝ {sorry}

noncomputable def GraphAlgebra : Module ℝ (FiniteGraphModule ⧸ ZeroSubspace) := inferInstance
