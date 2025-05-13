import «LeanFlagAlgebras».QuotientGraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Finset
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

noncomputable instance qualSubgraphFintype
    (G : SimpleGraph V) (p : Subgraph G → Prop)
    : Fintype { G₁ : Subgraph G | p G₁ } := by
  have : Fintype (Subgraph G) := subgraphFintype G
  exact inferInstance

noncomputable instance subgraphPairFintype
    (G : SimpleGraph V) : Fintype (Subgraph G × Subgraph G)
  := by
  have : Fintype (Subgraph G) := subgraphFintype G
  exact inferInstance

noncomputable instance qualifiedSubgraphPairFintype
    (G : SimpleGraph V) (p : Subgraph G × Subgraph G → Prop)
    : Fintype {⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} := by
  have : Fintype (Subgraph G × Subgraph G) := subgraphPairFintype G
  exact inferInstance

noncomputable instance qualifiedSubgraphPairProdSubgraphFintype
    (G : SimpleGraph V) (p : Subgraph G × Subgraph G → Prop)
    : Fintype ({⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} × Subgraph G) := by
  have fintypeQualPair : Fintype {⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} := qualifiedSubgraphPairFintype G p
  have fintypeSubgraph : Fintype (Subgraph G) := subgraphFintype G
  exact inferInstance

noncomputable instance doublyQualiedSubgraphPairProdSubgraphFintype
    (G : SimpleGraph V) (p : Subgraph G × Subgraph G → Prop) (q : Subgraph G × Subgraph G × Subgraph G → Prop)
    : Fintype {⟨⟨⟨G₁,G₂⟩,_⟩, G₃⟩ : {⟨G',G''⟩ : Subgraph G × Subgraph G | p ⟨G',G''⟩} × Subgraph G | q ⟨G₁,G₂,G₃⟩}
  := by
  have : Fintype ({⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} × Subgraph G) := qualifiedSubgraphPairProdSubgraphFintype G p
  exact inferInstance

noncomputable def subgraphSet (H : SimpleGraph V) (G : SimpleGraph W) : Finset (Subgraph G)
  :=
  let p (G' : Subgraph G) : Prop := G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H)
  { G' : Subgraph G | p G' }.toFinset

noncomputable def subgraphCount (H : SimpleGraph V) (G : SimpleGraph W) : ℕ
  :=
  (subgraphSet H G).card

noncomputable def subgraphDensity (H : SimpleGraph V) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraphCount H G
  let card_V := Fintype.card V
  let card_W := Fintype.card W
  let num_of_all_induced_subgraph := card_W.choose card_V
  subgraph_cnt / num_of_all_induced_subgraph

noncomputable def subgraphPairSet (H₁ : SimpleGraph U) (H₂ : SimpleGraph V) (G : SimpleGraph W) : Finset (Subgraph G × Subgraph G)
  :=
  let p (G₁ G₂ : Subgraph G) : Prop :=
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅
  { (G₁, G₂) : Subgraph G × Subgraph G | p G₁ G₂ }.toFinset

noncomputable def subgraphPairCount (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℕ
  :=
  (subgraphPairSet H₁ H₂ G).card

noncomputable def subgraphPairDensity
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraphPairCount H₁ H₂ G
  let W_card := Fintype.card W
  let V_card := Fintype.card V
  let U_card := Fintype.card U
  let num_of_all_induced_subgraphs := W_card.choose V_card * (W_card - V_card).choose U_card
  subgraph_cnt / num_of_all_induced_subgraphs

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairSet_card_each
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W}
    {G₁ G₂ : Subgraph G} (h : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G)
    : Fintype.card G₁.verts = Fintype.card U ∧ Fintype.card G₂.verts = Fintype.card V
  := by
  simp [subgraphPairSet] at h
  have ⟨_, h_G₁_H₁, _, h_G₂_H₂, _⟩ := h
  rw [Fintype.card_of_bijective (RelIso.bijective h_G₁_H₁.some)]
  rw [Fintype.card_of_bijective (RelIso.bijective h_G₂_H₂.some)]
  simp only [and_self]

omit [DecidableEq U] [DecidableEq V] in
lemma subgraphPairSet_card_union
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W}
    {G₁ G₂ : Subgraph G} (h : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G)
    : Fintype.card (G₁.verts ∪ G₂.verts).toFinset = Fintype.card U + Fintype.card V
  := by
  let ⟨h_G₁_card, h_G₂_card⟩ := subgraphPairSet_card_each h
  simp [subgraphPairSet] at h
  have ⟨_, _, _, _, h_G₁_G₂_disj⟩ := h
  calc
    Fintype.card (G₁.verts ∪ G₂.verts).toFinset
    _ = (G₁.verts ∪ G₂.verts).toFinset.card :=
          Fintype.card_coe (G₁.verts ∪ G₂.verts).toFinset
    _ = (G₁.verts.toFinset ∪ G₂.verts.toFinset).card := by
          simp
    _ =  G₁.verts.toFinset.card + G₂.verts.toFinset.card := by
          rw [Finset.card_union]
          have : G₁.verts.toFinset ∩ G₂.verts.toFinset = ∅ := by
            rw [←Set.toFinset_inter]
            exact Set.toFinset_eq_empty.mpr h_G₁_G₂_disj
          simp_all only [card_empty, tsub_zero]
    _ = Fintype.card U + Fintype.card V := by
          rw [←h_G₁_card, ←h_G₂_card]
          simp only [Set.toFinset_card]

omit [DecidableEq U] [DecidableEq V] in
lemma subgraphPairSet_card_union_Finset
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W}
    {G₁ G₂ : Subgraph G} (h : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G)
    : (G₁.verts ∪ G₂.verts).toFinset.card = Fintype.card U + Fintype.card V
  := by
  rw [←Fintype.card_coe (G₁.verts ∪ G₂.verts).toFinset]
  rw [subgraphPairSet_card_union h]

omit [DecidableEq V] [DecidableEq W] in
theorem subgraphDensity_ge_0
    (H : SimpleGraph V) (G : SimpleGraph W)
    : 0 ≤ subgraphDensity H G
  := by
  dsimp [subgraphDensity]
  apply div_nonneg <;> simp

def combinations [DecidableEq α] (V : Finset α) (ℓ : ℕ) : Finset (Finset α)
  := (V.powerset).filter fun W ↦ W.card = ℓ

theorem comb_card_aux
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

theorem comb_card
    [DecidableEq α] (V : Finset α) (ℓ : ℕ) : (combinations V ℓ).card = V.card.choose ℓ
  := by
  apply comb_card_aux V ℓ
  exact fun ⦃a⦄ a ↦ a

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
  dsimp [subgraphCount, subgraphSet]
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

omit [Fintype V] [DecidableEq V] in
lemma inducedSubgraph_verts
    (G : SimpleGraph V) (S : Set V) : ((inducedSubgraph G S) : Subgraph G).verts = S
  := by
  simp [inducedSubgraph]

omit [Fintype V] [DecidableEq V] in
lemma inducedSubgraph_mono
    {G : SimpleGraph V} {G₀ G₁ : Subgraph G}
    (h_G₁_ind : G₁.IsInduced) (h_sub : G₀.verts ⊆ G₁.verts)
    : G₀ ≤ G₁
  := by
  constructor
  . exact h_sub
  . intro u v h_uv_G₀
    have h_u_G₁ : u ∈ G₁.verts := h_sub (G₀.edge_vert h_uv_G₀)
    have h_v_G₁ : v ∈ G₁.verts := h_sub (G₀.edge_vert (G₀.symm h_uv_G₀))
    have h_uv_G : G.Adj u v := G₀.adj_sub h_uv_G₀
    exact h_G₁_ind h_u_G₁ h_v_G₁ h_uv_G

omit [Fintype V] [DecidableEq V] in
lemma inducedSubgraph_eq
    {G : SimpleGraph V} {G₀ : Subgraph G}
    (h_G₀_ind : G₀.IsInduced) : ⟨G₀, h_G₀_ind⟩ = (inducedSubgraph G G₀.verts)
  := by
  dsimp [inducedSubgraph]
  ext u v
  . exact Set.mem_def
  . constructor
    . intro h_uv_G₀
      have h_u_G₀ : u ∈ G₀.verts := G₀.edge_vert h_uv_G₀
      have h_v_G₀ : v ∈ G₀.verts := G₀.edge_vert (G₀.symm h_uv_G₀)
      have h_uv_G : G.Adj u v := G₀.adj_sub h_uv_G₀
      exact ⟨h_uv_G, h_u_G₀, h_v_G₀⟩
    . intro ⟨h_uv_G, h_u_G₀, h_v_G₀⟩
      exact h_G₀_ind h_u_G₀ h_v_G₀ h_uv_G

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
    dsimp [subgraphCount, subgraphSet]
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
lemma subgraphDensityLifted_respects_eqv
    (H₀ H₁ : SimpleGraph V) (h_eqv : graph_eqv H₀ H₁) (G : QuotSimpleGraph W)
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
    dsimp [subgraphCount, subgraphSet]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
  exact h_count

noncomputable def quotSubgraphDensity
    : QuotSimpleGraph V → QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift subgraphDensityLifted
  intro H₀ H₁ h_eqv
  ext G
  exact subgraphDensityLifted_respects_eqv H₀ H₁ h_eqv G

omit [DecidableEq V] in
lemma subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0
    {G : SimpleGraph V} {H : Subgraph G}
    : H = ⊥ ↔ Nonempty (H.coe ≃g (emptyGraph (Fin 0)))
  := by
  constructor
  . intro h_eq
    rw [h_eq]
    have f_iso : (⊥ : Subgraph G).verts ≃ Fin 0 := Fintype.equivFinOfCardEq (by simp)
    exact Nonempty.intro ⟨f_iso, by simp⟩
  . intro h_iso
    have h_verts : H.verts = ∅ := by
      ext u
      constructor
      . intro h_u
        let u' : Fin 0 := h_iso.some ⟨u, h_u⟩
        exact Fin.elim0 u'
      . exact False.elim
    simp_all [Subgraph.ext_iff, Set.ext_iff]
    ext u v
    simp
    intro h_uv
    have : u ∈ H.verts := H.edge_vert h_uv
    exact h_verts u this

lemma subgraphCount_empty
    (G : SimpleGraph (Fin n))
    : subgraphCount (emptyGraph (Fin 0)) G = 1
  := by
  simp [subgraphCount, subgraphSet]
  let S₀ := { G' : Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g (emptyGraph (Fin 0))) }
  let S₁ := { G' : Subgraph G | G' = ⊥ }
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    constructor
    · intro ⟨_, h_iso⟩
      rw [← subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0] at h_iso
      simp_all only [emptyGraph_eq_bot, Set.mem_setOf_eq, Subgraph.verts_bot, and_self, S₀, S₁]
    · intro h
      simp [S₁] at h
      constructor
      · subst h
        intro; simp
      · exact subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mp h
  show Fintype.card S₀ = 1
  have : Fintype.card S₁ = 1 := by
    simp_all only [emptyGraph_eq_bot, Set.setOf_eq_eq_singleton, Fintype.card_unique, S₀, S₁]
  rw [← this]; congr

lemma subgraphDensity_empty
    (G : SimpleGraph (Fin n)) : subgraphDensity (emptyGraph (Fin 0)) G = 1
  := by
  simp [subgraphDensity]
  simp [← subgraphCount_empty G]

lemma quotSubgraphDensity_empty
    (G : QuotSimpleGraph (Fin n)) : quotSubgraphDensity ⟦emptyGraph (Fin 0)⟧ G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hGrep]
  apply subgraphDensity_empty

omit [DecidableEq V] in
lemma iso_subset_of_finset_is_full
    {S : Set V} (f_iso : V ≃ ↑S) (u : V) : u ∈ S
  := by
  by_contra h_contra
  have h_card : Fintype.card S < Fintype.card V :=
    Fintype.card_subtype_lt h_contra
  have h_card' : Fintype.card V = Fintype.card S := by
    rw [Fintype.card_congr f_iso]
  simp_all

omit [DecidableEq V] in
lemma induced_full_subgraph_eq_top
    {G₀ G₁ : SimpleGraph V} {G' : Subgraph G₀}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃g G₁) → G' = ⊤
  := by
  intro ⟨h,f_iso⟩
  let f_iso_vertex : V ≃ ↑G'.verts := f_iso.some.toEquiv.symm
  ext u v
  . have h_u := iso_subset_of_finset_is_full f_iso_vertex u
    simp_all
  . have h_u := iso_subset_of_finset_is_full f_iso_vertex u
    have h_v := iso_subset_of_finset_is_full f_iso_vertex v
    constructor
    . apply G'.adj_sub
    . exact h h_u h_v

omit [DecidableEq V] in
lemma induced_subgraph_iso_G_iff_eq_top
    {G : SimpleGraph V} {G' : Subgraph G}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃g G) ↔ G' = ⊤
  := by
  constructor
  . exact induced_full_subgraph_eq_top
  · intro h
    constructor
    · subst h; intro; simp
    · rw [h]; exact Nonempty.intro SimpleGraph.Subgraph.topEquiv

omit [DecidableEq V] in
lemma subgraphCount_self
    (G : SimpleGraph V) : subgraphCount G G = 1
  := by
  simp [subgraphCount, subgraphSet]
  let S₀ := { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g G) }
  let S₁ : Finset (Subgraph G):= { ⊤ }
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    simp_all [S₀, S₁]
    exact induced_subgraph_iso_G_iff_eq_top
  show Fintype.card S₀ = 1
  calc
    Fintype.card S₀ = Fintype.card S₁ := by simp_all [h_S₀_S₁]
    _ = 1 := by simp

omit [DecidableEq V] in
lemma subgraphDensity_self
    (G : SimpleGraph V) : subgraphDensity G G = 1
  := by
  simp [subgraphDensity]
  exact subgraphCount_self G

lemma quotSubgraphDensity_self
    (G : QuotSimpleGraph (Fin n)) : quotSubgraphDensity G G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hGrep]
  apply subgraphDensity_self

omit [DecidableEq V] in
lemma subgraphCount_other
    {G₀ G₁ : SimpleGraph V} (h_neq : IsEmpty (G₀ ≃g G₁)) : subgraphCount G₀ G₁ = 0
  := by
  simp [subgraphCount, subgraphSet]
  rw [←not_nonempty_iff] at h_neq
  let S₀ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g G₀) }
  have h_S₀ : S₀ ⊆ ∅ := by
    intro G' ⟨h_ind_G', h_iso_G'⟩
    have f_iso_G₀_G' : G₀ ≃g G'.coe := h_iso_G'.some.symm
    have f_iso_G'_G₁ : G'.coe ≃g G₁ := by
      have : G' = ⊤ := induced_full_subgraph_eq_top ⟨h_ind_G', h_iso_G'⟩
      let g : (⊤ : Subgraph G₁).coe ≃g G₁ := SimpleGraph.Subgraph.topEquiv
      rw [←this] at g
      exact g
    have f_iso_G₀_G₁ : G₀ ≃g G₁ := Iso.comp f_iso_G'_G₁ f_iso_G₀_G'
    exact h_neq ⟨f_iso_G₀_G₁⟩
  show Fintype.card S₀ = 0
  simp_all only [Set.subset_empty_iff, Fintype.card_ofIsEmpty]

omit [DecidableEq V] in
lemma subgraphDensity_other
    {G₀ G₁ : SimpleGraph V} (h_neq : IsEmpty (G₀ ≃g G₁)) : subgraphDensity G₀ G₁ = 0
  := by
  dsimp [subgraphDensity]
  have := subgraphCount_other h_neq
  simp_all only [Nat.cast_zero, Nat.choose_self, Nat.cast_one, div_one]

lemma quotSubgraphDensity_other
    {G₀ G₁ : QuotSimpleGraph (Fin n)} (h_neq : G₀ ≠ G₁) : quotSubgraphDensity G₀ G₁ = 0
  := by
  rcases Quotient.exists_rep G₀ with ⟨G₀rep, hG₀rep⟩
  rcases Quotient.exists_rep G₁ with ⟨G₁rep, hG₁rep⟩
  rw [← hG₀rep, ← hG₁rep]
  have h_neq' : IsEmpty (G₀rep ≃g G₁rep) := by
    rw [←not_nonempty_iff]
    intro h_iso
    have h_eq : G₀ = G₁ := by
      rw [←hG₀rep, ←hG₁rep]
      exact Quotient.sound h_iso
    exact h_neq h_eq
  apply subgraphDensity_other h_neq'

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
    dsimp [subgraphPairCount, subgraphPairSet]
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
    dsimp [subgraphPairCount, subgraphPairSet]
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

omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairCount_comm
    (H : SimpleGraph U) (H' : SimpleGraph V) (G : SimpleGraph W)
    : subgraphPairCount H H' G = subgraphPairCount H' H G
  := by
  dsimp [subgraphPairCount, subgraphPairSet]
  let S₀ := { (G', G'') : Subgraph G × Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H') ∧
                G'.verts ∩ G''.verts = ∅ }
  let S₁ := { (G', G'') : Subgraph G × Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H') ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H) ∧
                G'.verts ∩ G''.verts = ∅ }
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    apply Equiv.subtypeEquiv (Equiv.prodComm (Subgraph G) (Subgraph G))
    intro ⟨G', G''⟩
    constructor <;>
    { intro ⟨h₁, h₂, h₃, h₄, h₅⟩
      let h₅' := by rw [Set.inter_comm] at h₅; exact h₅
      exact ⟨h₃, h₄, h₁, h₂, h₅'⟩ }
  have h_count : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]

lemma choose_pair_eq_factorial_div
    (n m k : ℕ) (h_size : m + k ≤ n)
    : n.choose m * (n - m).choose k = n.factorial / (m.factorial * k.factorial * (n - (m + k)).factorial)
  := by
  have h₁ : m ≤ n := Nat.le_of_add_right_le h_size
  have h₂ : k ≤ n - m := (Nat.le_sub_iff_add_le' h₁).mpr h_size
  repeat rw [Nat.choose_eq_factorial_div_factorial] <;> try assumption
  rw [← Nat.mul_div_assoc _ (Nat.factorial_mul_factorial_dvd_factorial h₂)]
  rw [Nat.mul_comm, ← Nat.mul_div_assoc _ (Nat.factorial_mul_factorial_dvd_factorial h₁)]
  rw [Nat.mul_comm (n - m).factorial, Nat.mul_comm m.factorial, ← Nat.div_div_eq_div_mul _ _ m.factorial]
  rw [Nat.mul_div_cancel _ (Nat.factorial_pos (n - m))]
  rw [Nat.div_div_eq_div_mul, Nat.sub_sub, Nat.mul_assoc]

lemma choose_pair_zero
    (n m k : ℕ) (h_size : m + k > n)
    : n.choose m * (n - m).choose k = 0
  := by
  by_cases hm : m > n
  · simp [Nat.choose_eq_zero_of_lt hm]
  · have hk : k > n - m := by
      apply @Nat.lt_of_add_lt_add_right _ _ m
      rw [Nat.sub_add_cancel (Nat.le_of_not_lt hm), Nat.add_comm]
      exact h_size
    simp [Nat.choose_eq_zero_of_lt hk]

lemma choose_pair_comm
    (n m k : ℕ)
    : n.choose m * (n - m).choose k = n.choose k * (n - k).choose m
  := by
  by_cases h_size : m + k ≤ n
  · simp [choose_pair_eq_factorial_div, h_size, Nat.add_comm, Nat.mul_comm]
  · have h_size' : m + k > n := Nat.not_le.mp h_size
    simp [choose_pair_zero, h_size', Nat.add_comm]

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairDensity_comm
    (H : SimpleGraph U) (H' : SimpleGraph V) (G : SimpleGraph W)
    : subgraphPairDensity H H' G = subgraphPairDensity H' H G
  := by
  dsimp [subgraphPairDensity]
  have h_count_comm : subgraphPairCount H H' G = subgraphPairCount H' H G := subgraphPairCount_comm H H' G
  rw [h_count_comm]; congr 1; apply congrArg Nat.cast
  simp [choose_pair_comm]

lemma quotSubgraphPairDensity_comm
    (H₁ : QuotSimpleGraph U) (H₂ : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : quotSubgraphPairDensity H₁ H₂ G = quotSubgraphPairDensity H₂ H₁ G
  := by
  rcases Quotient.exists_rep H₁ with ⟨H₁rep, hH₁rep⟩
  rcases Quotient.exists_rep H₂ with ⟨H₂rep, hH₂rep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hH₁rep, ← hH₂rep, ← hGrep]
  apply subgraphPairDensity_comm

lemma subgraphPairCount_empty
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphPairCount (emptyGraph (Fin 0)) H G = subgraphCount H G
  := by
  dsimp [subgraphPairCount, subgraphCount]
  let S₀ := { (G', G'') : Subgraph G × Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g (emptyGraph (Fin 0))) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H) ∧
                G'.verts ∩ G''.verts = ∅ }
  let S₁ := { G' : Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  show S₀.toFinset.card = S₁.toFinset.card
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    let f : Subgraph G × Subgraph G → Subgraph G :=
      fun ⟨_, G''⟩ => G''
    have h_f_S₀_S₁ : Set.MapsTo f S₀ S₁ :=
      fun ⟨_, G''⟩ ⟨_,_,h₃,h₄,_⟩ => ⟨h₃, h₄⟩
    have h_f_inj : Set.InjOn f S₀ := by
      intro ⟨G₀,G₁⟩ ⟨_,h₂,_,_⟩ ⟨G'₀,G'₁⟩ ⟨_,h₂',_,_⟩ h_eq
      dsimp [f] at h_eq
      simp [h_eq]
      have h_G₀ : G₀ = ⊥ := subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mpr h₂
      have h_G₀' : G'₀ = ⊥ := subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mpr h₂'
      rw [h_G₀, h_G₀']
    have h_f_surj : Set.SurjOn f S₀ S₁ := by
      intro G'' ⟨h₁,h₂⟩
      use ⟨⊥, G''⟩
      simp
      have h_bot_isinduced : (⊥ : Subgraph G).IsInduced := by
        dsimp [Subgraph.IsInduced]
        intro u _ h_u _ _
        exact False.elim h_u
      have h_bot_iso : Nonempty ((⊥ : Subgraph G).coe ≃g (emptyGraph (Fin 0))) :=
        subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mp rfl
      exact ⟨h_bot_isinduced, h_bot_iso, h₁, h₂, Disjoint.inter_eq fun _ a _ ↦ a⟩
    exact Set.BijOn.equiv f (Set.BijOn.mk h_f_S₀_S₁ h_f_inj h_f_surj)
  have h_count : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]

lemma subgraphPairDensity_empty
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphPairDensity (emptyGraph (Fin 0)) H G  = subgraphDensity H G
  := by
  dsimp [subgraphPairDensity, subgraphDensity]
  rw [← subgraphPairCount_empty H G]
  simp

lemma quotSubgraphPairDensity_empty
    (H : QuotSimpleGraph (Fin n)) (G : QuotSimpleGraph (Fin m))
    : quotSubgraphPairDensity ⟦emptyGraph (Fin 0)⟧ H G = quotSubgraphDensity H G
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hHrep, ← hGrep]
  apply subgraphPairDensity_empty

def subgraphFromIso
    {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (G₀ : Subgraph G)
    : Subgraph H
  where
    verts :=
      iso '' G₀.verts
    Adj := fun u v =>
      G₀.Adj (iso.symm u) (iso.symm v)
    adj_sub := by
      intro u v h_uv_G₀
      have h_uv : G.Adj (iso.symm u) (iso.symm v) := G₀.adj_sub h_uv_G₀
      exact (Iso.map_adj_iff iso.symm).mp h_uv
    edge_vert := by
      intro u v h_uv
      use (iso.symm u)
      simp
      exact G₀.edge_vert h_uv
    symm := by
      intro u v h_uv_G₀
      exact G₀.symm h_uv_G₀

def isoToSubgraphFromIso
    {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) (G₀ : Subgraph G)
    : Subgraph.coe G₀ ≃g Subgraph.coe (subgraphFromIso iso G₀)
  := by
  let H₀ : Subgraph H := subgraphFromIso iso G₀
  exact {
    toFun := fun u =>
      have : iso u ∈ H₀.verts := by dsimp [H₀, subgraphFromIso]; simp
      ⟨iso u, this⟩
    invFun := fun u =>
      have h_symm_u : iso.symm u ∈ iso.symm '' (iso '' G₀.verts) :=
        Set.mem_image_of_mem iso.symm u.property
      have : iso.symm u ∈ G₀.verts := by
        rw [← Set.image_comp] at h_symm_u
        simp at h_symm_u
        exact h_symm_u
      ⟨iso.symm u, this⟩
    left_inv := by
      intro u; simp
    right_inv := by
      intro u; simp
    map_rel_iff' := by
      intro u v; dsimp [subgraphFromIso]; simp
  }

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromIso_preserve_inducedness
    {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (G₀ : Subgraph G)
    : G₀.IsInduced → (subgraphFromIso iso G₀).IsInduced
  := by
  intro h_ind_G₀
  dsimp [Subgraph.IsInduced, subgraphFromIso] at *
  intro u v h_u_H h_v_H h_uv_H
  let h : ∀ {w : W}, (w ∈ iso '' G₀.verts) → (iso.symm w ∈ G₀.verts) := by
    intro w h_w
    obtain ⟨u', ⟨h_u', h_u'_w⟩⟩ := h_w
    subst h_u'_w
    rw [RelIso.symm_apply_apply]
    exact h_u'
  have h_u_G₀ : iso.symm u ∈ G₀.verts := h h_u_H
  have h_v_G₀ : iso.symm v ∈ G₀.verts := h h_v_H
  have h_uv_G : G.Adj (iso.symm u) (iso.symm v) := (Iso.map_adj_iff iso.symm).mpr h_uv_H
  exact h_ind_G₀ h_u_G₀ h_v_G₀ h_uv_G

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromIso_preserve_disjointedness
    {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (G₀ G₁ : Subgraph G) (h_disj : G₀.verts ∩ G₁.verts = ∅)
    : (subgraphFromIso iso G₀).verts ∩ (subgraphFromIso iso G₁).verts = ∅
  := by
  dsimp [subgraphFromIso]
  apply Set.eq_empty_of_subset_empty
  intro u ⟨h_u_G₀, h_u_G₁⟩
  have h_iso₀ : iso.symm u ∈ iso.symm '' (iso '' G₀.verts) := Set.mem_image_of_mem iso.symm h_u_G₀
  have h_iso₁ : iso.symm u ∈ iso.symm '' (iso '' G₁.verts) := Set.mem_image_of_mem iso.symm h_u_G₁
  have h_iso₀' : iso.symm u ∈ G₀.verts := by rw [← Set.image_comp] at h_iso₀; simp at h_iso₀; exact h_iso₀
  have h_iso₁' : iso.symm u ∈ G₁.verts := by rw [← Set.image_comp] at h_iso₁; simp at h_iso₁; exact h_iso₁
  have : iso.symm u ∈ ∅ := h_disj ▸ Set.mem_inter h_iso₀' h_iso₁'
  exact this

def subgraphFromOrder
    {G : SimpleGraph V} {G₀ G₁ : Subgraph G} (h_order : G₀ ≤ G₁)
    : Subgraph G₁.coe
  where
    verts := { u | u.1 ∈ G₀.verts }
    Adj := fun u v => G₀.Adj u.1 v.1
    adj_sub := by
      intro u v h_uv
      have : G₀.edgeSet ⊆ G₁.edgeSet := SimpleGraph.Subgraph.edgeSet_mono h_order
      exact Subgraph.mem_edgeSet.mp (this h_uv)
    edge_vert := by
      intro u v h_uv
      exact G₀.edge_vert h_uv
    symm := by
      intro u v h_uv
      exact G₀.symm h_uv

def isoToSubgraphFromOrder
    {G : SimpleGraph V} {G₀ G₁ : Subgraph G} (h_order : G₀ ≤ G₁)
    : Subgraph.coe G₀ ≃g Subgraph.coe (subgraphFromOrder h_order)
  :=
  let G₀' : Subgraph G₁.coe := subgraphFromOrder h_order
  {
    toFun := fun ⟨u, h_u_G₀⟩ =>
      have h_u_G₁ : u ∈ G₁.verts := SimpleGraph.Subgraph.verts_mono h_order h_u_G₀
      ⟨⟨u, h_u_G₁⟩, h_u_G₀⟩
    invFun := fun ⟨⟨u, _⟩, h_u_G₀'⟩ =>
      ⟨u, h_u_G₀'⟩
    left_inv := by
      intro u; exact rfl
    right_inv := by
      intro u; exact rfl
    map_rel_iff' := by
      intro u v; dsimp [G₀', subgraphFromOrder]; simp
  }

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromOrder_preserve_inducedness
    {G : SimpleGraph V} {G₀ G₁ : Subgraph G} (h_order : G₀ ≤ G₁)
    : G₀.IsInduced → (subgraphFromOrder h_order).IsInduced
  := by
  intro h_ind_G₀
  dsimp [Subgraph.IsInduced, subgraphFromOrder] at *
  intro u v h_u_G₀ h_v_G₀ h_uv_G₁
  exact h_ind_G₀ h_u_G₀ h_v_G₀ (G₁.adj_sub h_uv_G₁)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromOrder_preserve_disjointedness
    {G : SimpleGraph V} {G₀ G₁ G₂ : Subgraph G}
    (h_order_G₁ : G₁ ≤ G₀) (h_order_G₂ : G₂ ≤ G₀) (h_disj : G₁.verts ∩ G₂.verts = ∅)
    : (subgraphFromOrder h_order_G₁).verts ∩ (subgraphFromOrder h_order_G₂).verts = ∅
  := by
  dsimp [subgraphFromOrder]
  apply Set.eq_empty_of_subset_empty
  intro ⟨u, h_u_G₀⟩ h_u_G₁_G₂
  have : u ∈ G₁.verts ∩ G₂.verts := h_u_G₁_G₂
  have : u ∈ ∅ := h_disj ▸ this
  exact this

def subgraphByComposition
    {G : SimpleGraph V} (G₀ : Subgraph G) (G₁ : Subgraph (Subgraph.coe G₀))
    :  Subgraph G
  :=
  SimpleGraph.Subgraph.coeSubgraph G₁

def isoToSubgraphByComposition
    {G : SimpleGraph V} (G₀ : Subgraph G) (G₁ : Subgraph (Subgraph.coe G₀))
    :  Subgraph.coe G₁ ≃g Subgraph.coe (subgraphByComposition G₀ G₁)
  where
    toFun := fun u =>
      Set.imageFactorization Subtype.val G₁.verts u
    invFun := by
      intro ⟨u, h_u⟩
      dsimp [subgraphByComposition] at h_u
      simp at h_u
      exact ⟨⟨u, h_u.1⟩, h_u.2⟩
    left_inv := by
      intro u
      exact rfl
    right_inv := by
      intro u
      exact rfl
    map_rel_iff' := by
      intro u v
      dsimp [subgraphByComposition, Relation.Map]
      aesop

omit [Fintype V] [DecidableEq V] in
lemma subgraphByComposition_le
    {G : SimpleGraph V} (G₀ : Subgraph G) (G₁ : Subgraph (Subgraph.coe G₀))
    : subgraphByComposition G₀ G₁ ≤ G₀
  := by
  simp [subgraphByComposition]
  exact Subgraph.coeSubgraph_le G₁

def subgraphFromPartialIso
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g Subgraph.coe H₀) (G₁ : Subgraph G₀) : Subgraph H
  :=
  let H₁_pre := subgraphFromIso iso G₁
  subgraphByComposition H₀ H₁_pre

def isoToSubgraphFromPartialIso
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g Subgraph.coe H₀) (G₁ : Subgraph G₀)
    : Subgraph.coe G₁ ≃g Subgraph.coe (subgraphFromPartialIso iso G₁)
  :=
  let H₁_pre := subgraphFromIso iso G₁
  let h_iso_pre := isoToSubgraphFromIso iso G₁
  let h_iso_post := isoToSubgraphByComposition H₀ H₁_pre
  Iso.comp h_iso_post h_iso_pre

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromPartialIso_le
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g Subgraph.coe H₀) (G₁ : Subgraph G₀)
    : subgraphFromPartialIso iso G₁ ≤ H₀
  := by
  simp [subgraphFromPartialIso, subgraphByComposition_le]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromPartialIso_preserve_inducedness
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g Subgraph.coe H₀) (G₁ : Subgraph G₀)
    (h_ind_H₀ : H₀.IsInduced) (h_ind_G₁ : G₁.IsInduced)
    : (subgraphFromPartialIso iso G₁).IsInduced
  := by
  dsimp [Subgraph.IsInduced] at *
  intro u v h_u_H₁ h_v_H₁ h_uv_H
  dsimp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso, Relation.Map] at *
  simp at *
  obtain ⟨u₀, h_u₀_G₁_verts, h_u₀_u⟩ := h_u_H₁
  obtain ⟨v₀, h_v₀_G₁_verts, h_v₀_v⟩ := h_v_H₁
  have h_u_H₀ : u ∈ H₀.verts := by
    subst h_v₀_v h_u₀_u
    simp_all only [Subtype.coe_prop]
  have h_v_H₁ : v ∈ H₀.verts := by
    subst h_v₀_v h_u₀_u
    simp_all only [Subtype.coe_prop]
  have h_u₀v₀_G₀ : G₀.Adj u₀ v₀ := by
    apply iso.map_adj_iff.mp
    rw [Subgraph.coe_adj H₀ (iso u₀) (iso v₀)]
    rw [←h_u₀_u] at h_u_H₀ h_uv_H
    rw [←h_v₀_v] at h_v_H₁ h_uv_H
    exact h_ind_H₀ h_u_H₀ h_v_H₁ h_uv_H
  rw [←h_u₀_u, ←h_v₀_v]
  simp only [Subtype.coe_eta, RelIso.symm_apply_apply, Subtype.coe_prop, exists_const]
  exact h_ind_G₁ h_u₀_G₁_verts h_v₀_G₁_verts h_u₀v₀_G₀

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromPartialIso_preserve_disjointedness
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g Subgraph.coe H₀) (G₁ G₂ : Subgraph G₀) (h_disj : G₁.verts ∩ G₂.verts = ∅)
    : (subgraphFromPartialIso iso G₁).verts ∩ (subgraphFromPartialIso iso G₂).verts = ∅
  := by
  dsimp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso]
  apply Set.eq_empty_of_subset_empty
  intro u ⟨h_u_G₁, h_u_G₂⟩
  simp at h_u_G₁ h_u_G₂
  obtain ⟨u₁, h_u₁_G₁_verts, h_u₁_u⟩ := h_u_G₁
  obtain ⟨u₂, h_u₂_G₂_verts, h_u₂_u⟩ := h_u_G₂
  have h_u₁_G₁_G₂ : u₁ ∈ G₁.verts ∩ G₂.verts := by
    have h_iso_u₁_eq_iso_u₂: (iso u₁) = (iso u₂) := by
      rw [←h_u₂_u] at h_u₁_u
      exact SetCoe.ext h_u₁_u
    have : u₁ = u₂ :=
      calc
        u₁ = iso.symm (iso u₁) := Eq.symm (RelIso.symm_apply_apply iso u₁)
        _  = iso.symm (iso u₂) := by rw [h_iso_u₁_eq_iso_u₂]
        _  = u₂                := RelIso.symm_apply_apply iso u₂
    constructor
    . assumption
    . rw [this]; assumption
  have : u₁ ∈ ∅ := h_disj ▸ h_u₁_G₁_G₂
  exact this

omit [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma subgraphFromPartialIso_preserve_cover
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g Subgraph.coe H₀) (G₁ G₂ : Subgraph G₀)
    (h_cover : G₁.verts ∪ G₂.verts = (univ : Finset V))
    : H₀.verts = (subgraphFromPartialIso iso G₁).verts ∪ (subgraphFromPartialIso iso G₂).verts
  := by
  dsimp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso]
  ext u; simp
  constructor
  . intro h_u_H₀
    have h_iso_symm_u_V : (iso.symm ⟨u,h_u_H₀⟩) ∈ G₁.verts ∪ G₂.verts := by
      rw [h_cover]
      exact mem_univ (iso.symm ⟨u, h_u_H₀⟩)
    cases h_iso_symm_u_V with
    | inl h_u_G₁ =>
        apply Or.inl
        use (iso.symm ⟨u, h_u_H₀⟩)
        exact ⟨h_u_G₁, by simp⟩
    | inr h_u_G₂ =>
        apply Or.inr
        use (iso.symm ⟨u, h_u_H₀⟩)
        exact ⟨h_u_G₂, by simp⟩
  . intro h_u
    cases h_u with
    | inl h_u_G₁ =>
        obtain ⟨a₁, _, h_a₁_u⟩ := h_u_G₁
        rw [←h_a₁_u]; simp
    | inr h_u_G₂ =>
        obtain ⟨a₂, _, h_a₂_u⟩ := h_u_G₂
        rw [←h_a₂_u]; simp

noncomputable def getCanonicalQuotSimpleGraph
      (G : SimpleGraph V) (h_V_size : Fintype.card V = ℓ)
      : (F : QuotSimpleGraph (Fin ℓ)) × (F.out ≃g G)
  :=
  let f_iso : V ≃ Fin ℓ := Fintype.equivFinOfCardEq h_V_size
  let G' : SimpleGraph (Fin ℓ) := {
    Adj := fun u' v' => G.Adj (f_iso.symm u') (f_iso.symm v')
    symm := fun u' v' h_u'_v' => G.symm h_u'_v'
    loopless := fun u' => G.loopless (f_iso.symm u')
  }
  let φ : G' ≃g G := {
    toFun := f_iso.symm,
    invFun := f_iso,
    left_inv := by intro u'; simp
    right_inv := by intro u; simp
    map_rel_iff' := by intro u' v'; dsimp [G']; rfl
  }
  let φ' : ⟦G'⟧.out ≃g G' := by
    have h : graph_eqv ⟦G'⟧.out G' := by
      have := @Quotient.eq_mk_iff_out _ _ ⟦G'⟧ G'
      exact this.mp rfl
    rw [graph_eqv] at h
    exact h.some
  ⟨⟦G'⟧, φ'.trans φ⟩


lemma getCanonicalQuotSimpleGraph_self
    (F : QuotSimpleGraph (Fin ℓ))
    : (getCanonicalQuotSimpleGraph F.out (Fintype.card_fin ℓ)).fst = F
  := by
  obtain ⟨F', h_iso⟩ := getCanonicalQuotSimpleGraph F.out (Fintype.card_fin ℓ)
  show F' = F
  calc F'
    _  = ⟦F'.out⟧ := (Quotient.out_eq F').symm
    _  = ⟦F.out⟧  := by rw [Quotient.sound]; exact Nonempty.intro h_iso
    _  = F := Quotient.out_eq F

omit [DecidableEq V] [DecidableEq W] in
lemma getCanonicalQuotSimpleGraph_iso
    (G₀ : SimpleGraph V) (h_size₀ : Fintype.card V = ℓ)
    (G₁ : SimpleGraph W) (h_size₁ : Fintype.card W = ℓ)
    (h_iso : G₀ ≃g G₁)
    : (getCanonicalQuotSimpleGraph G₀ h_size₀).fst = (getCanonicalQuotSimpleGraph G₁ h_size₁).fst
  := by
  obtain ⟨H₀, h_iso₀⟩ := getCanonicalQuotSimpleGraph G₀ h_size₀
  obtain ⟨H₁, h_iso₁⟩ := getCanonicalQuotSimpleGraph G₁ h_size₁
  have h_iso_H₀_H₁ : H₀.out ≃g H₁.out := (h_iso₀.trans h_iso).trans h_iso₁.symm
  calc H₀
    _  = ⟦H₀.out⟧ := (Quotient.out_eq H₀).symm
    _  = ⟦H₁.out⟧ := by rw [Quotient.sound]; exact Nonempty.intro h_iso_H₀_H₁
    _  = H₁ := Quotient.out_eq H₁

lemma card_eq_imply_set_eq
    (A B : Finset (Fin ℓ)) (h_card_eq : A.card + B.card = ℓ) (h_disj : A ∩ B = ∅)
    : A ∪ B = univ
  := by
  have h_card_A_union_B : (A ∪ B).card = ℓ := by
    have : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr h_disj
    rw [Finset.card_union_of_disjoint this]
    assumption
  have h_compl_A_union_B_empty : (univ \ (A ∪ B)) = ∅ := by
    apply Finset.card_eq_zero.mp
    calc
      (univ \ (A ∪ B)).card
      _ = (univ : Finset (Fin ℓ)).card - (A ∪ B).card := Finset.card_sdiff (subset_univ (A ∪ B))
      _ = ℓ - (A ∪ B).card := by simp
      _ = ℓ - ℓ := by rw [h_card_A_union_B]
      _ = 0 := by simp
  exact (compl_eq_empty_iff (A ∪ B)).mp h_compl_A_union_B_empty


omit [DecidableEq V] [DecidableEq W] in
lemma subgraph_verts_card_from_iso_graph
    {G : SimpleGraph V} {G' : Subgraph G} {H : SimpleGraph (Fin ℓ)} (h_iso : G'.coe ≃g H)
    : Fintype.card G'.verts = ℓ
  :=
  calc
    Fintype.card G'.verts = Fintype.card (Fin ℓ) := Fintype.card_congr h_iso
    _ = ℓ := by simp

noncomputable def subgraphPairSet_iso_union_quotSimpleGraphSet
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ))
    : { (⟨⟨G₁,G₂⟩, _⟩, G₃) : subgraphPairSet H₁ H₂ G × Subgraph G
            | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts }
      ≃
      (F : QuotSimpleGraph (Fin ℓ₃)) × subgraphPairSet H₁ H₂ F.out × subgraphSet F.out G
  := by
  let S := { (⟨⟨G₁,G₂⟩, _⟩, G₃) : subgraphPairSet H₁ H₂ G × Subgraph G
            | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts}

  let S₀' := { (G₁, G₂, G₃) : Subgraph G × Subgraph G × Subgraph G
              | G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁)
                ∧ G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂)
                ∧ G₃.IsInduced ∧ (Fintype.card G₃.verts) = ℓ₃
                ∧ G₁.verts ∩ G₂.verts = ∅
                ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts }

  let S₁' := { (F, G₁, G₂, G₃) : QuotSimpleGraph (Fin ℓ₃) × Subgraph G × Subgraph G × Subgraph G
              | G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁)
                ∧ G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂)
                ∧ G₃.IsInduced ∧ (Fintype.card G₃.verts) = ℓ₃
                ∧ G₁.verts ∩ G₂.verts = ∅
                ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts
                ∧ Nonempty ((G₃ : Subgraph G).coe ≃g F.out) }

  let S₂' := { ⟨F, K₁, K₂, G₃⟩ : (F : QuotSimpleGraph (Fin ℓ₃)) × Subgraph F.out × Subgraph F.out × Subgraph G
              | K₁.IsInduced ∧ Nonempty (K₁.coe ≃g H₁)
                ∧ K₂.IsInduced ∧ Nonempty (K₂.coe ≃g H₂)
                ∧ G₃.IsInduced ∧ (Fintype.card G₃.verts) = ℓ₃
                ∧ K₁.verts ∩ K₂.verts = ∅
                ∧ Nonempty ((G₃ : Subgraph G).coe ≃g F.out) }

  let S₃' := (F : QuotSimpleGraph (Fin ℓ₃)) × subgraphPairSet H₁ H₂ F.out × subgraphSet F.out G

  let f_S_S₀'_fwd : S → S₀' := by
    intro ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    simp [subgraphPairSet] at h_G₁_G₂
    let ⟨h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₁_G₂_disj⟩ := h_G₁_G₂
    exact ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂_disj, h_G₁_G₂_G₃⟩

  have h_inj_S_S₀' : Function.Injective f_S_S₀'_fwd := by
    intro ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    intro ⟨⟨⟨⟨G₁', G₂'⟩, h_G₁'_G₂'⟩, G₃'⟩, h_G₃'_ind, h_G₃'_card, h_G₁'_G₂'_G₃'⟩
    intro h_eq
    simp_all [f_S_S₀'_fwd]
    split at h_eq
    split at h_eq
    simp_all

  have h_surj_S_S₀' : Function.Surjective f_S_S₀'_fwd := by
    intro ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂_disj, h_G₁_G₂_G₃⟩
    have h_G₁_G₂ : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G := by
      simp [subgraphPairSet]
      exact ⟨h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₁_G₂_disj⟩
    use ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    simp [f_S_S₀'_fwd]
    split
    simp

  let f_S_S₀' : S ≃ S₀' :=
    Equiv.ofBijective f_S_S₀'_fwd ⟨h_inj_S_S₀', h_surj_S_S₀'⟩

  let f_S₀'_S₁'_fwd : S₀' → S₁' :=
    fun ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃⟩ =>
      let ⟨F, f_iso_F_G₃⟩ := getCanonicalQuotSimpleGraph G₃.coe h_G₃_card
      ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, Nonempty.intro f_iso_F_G₃.symm⟩

  have h_inj_S₀'_S₁' : Function.Injective f_S₀'_S₁'_fwd := by
    intro ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃⟩
    intro ⟨⟨G₁', G₂', G₃'⟩, h_G₁'_ind, h_G₁'_H₁, h_G₂'_ind, h_G₂'_H₂, h_G₃'_ind, h_G₃'_card, h_G₁'_G₂', h_G₁'_G₂'_G₃'⟩
    intro h_eq
    simp [f_S₀'_S₁'_fwd] at h_eq
    simp
    exact h_eq.2

  have h_surj_S₀'_S₁' : Function.Surjective f_S₀'_S₁'_fwd := by
    intro ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, h_G₃_F⟩
    use ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃⟩
    simp [f_S₀'_S₁'_fwd]
    rw [←(getCanonicalQuotSimpleGraph_self F)]
    apply getCanonicalQuotSimpleGraph_iso
    exact h_G₃_F.some

  let f_S₀'_S₁' : S₀' ≃ S₁' :=
    Equiv.ofBijective f_S₀'_S₁'_fwd ⟨h_inj_S₀'_S₁', h_surj_S₀'_S₁'⟩

  let f_S₁'_S₂'_fwd : S₁' → S₂' := by
    intro ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, h_G₃_F⟩
    let f_G₃_Fout : G₃.coe ≃g F.out := h_G₃_F.some
    have h_G₁_verts_sub_G₃_verts : G₁.verts ⊆ G₃.verts := fun a h_a => h_G₁_G₂_G₃ (by simp [h_a])
    have h_G₂_verts_sub_G₃_verts : G₂.verts ⊆ G₃.verts := fun a h_a => h_G₁_G₂_G₃ (by simp [h_a])
    have h_G₁_le : G₁ ≤ G₃ := inducedSubgraph_mono h_G₃_ind h_G₁_verts_sub_G₃_verts
    have h_G₂_le : G₂ ≤ G₃ := inducedSubgraph_mono h_G₃_ind h_G₂_verts_sub_G₃_verts
    let G₁' := subgraphFromOrder h_G₁_le
    let G₂' := subgraphFromOrder h_G₂_le
    let f_iso_G₁_G₁' : G₁.coe ≃g G₁'.coe := isoToSubgraphFromOrder h_G₁_le
    let f_iso_G₂_G₂' : G₂.coe ≃g G₂'.coe := isoToSubgraphFromOrder h_G₂_le
    have h_G₁'_ind : G₁'.IsInduced := subgraphFromOrder_preserve_inducedness h_G₁_le h_G₁_ind
    have h_G₂'_ind : G₂'.IsInduced := subgraphFromOrder_preserve_inducedness h_G₂_le h_G₂_ind
    have h_G₁'_G₂'_disj : G₁'.verts ∩ G₂'.verts = ∅ := subgraphFromOrder_preserve_disjointedness h_G₁_le h_G₂_le h_G₁_G₂
    let K₁ := subgraphFromIso f_G₃_Fout G₁'
    let K₂ := subgraphFromIso f_G₃_Fout G₂'
    let f_iso_G₁'_K₁ : Subgraph.coe G₁' ≃g Subgraph.coe K₁ := isoToSubgraphFromIso f_G₃_Fout G₁'
    let f_iso_G₂'_K₂ : Subgraph.coe G₂' ≃g Subgraph.coe K₂ := isoToSubgraphFromIso f_G₃_Fout G₂'
    have h_K₁_ind : K₁.IsInduced := subgraphFromIso_preserve_inducedness f_G₃_Fout G₁' h_G₁'_ind
    have h_K₂_ind : K₂.IsInduced := subgraphFromIso_preserve_inducedness f_G₃_Fout G₂' h_G₂'_ind
    have h_K₁_K₂_disj : K₁.verts ∩ K₂.verts = ∅ := subgraphFromIso_preserve_disjointedness f_G₃_Fout G₁' G₂' h_G₁'_G₂'_disj
    let f_iso_K₁_H₁ : Subgraph.coe K₁ ≃g H₁ := (f_iso_G₁_G₁'.trans f_iso_G₁'_K₁).symm.trans h_G₁_H₁.some
    let f_iso_K₂_H₂ : Subgraph.coe K₂ ≃g H₂ := (f_iso_G₂_G₂'.trans f_iso_G₂'_K₂).symm.trans h_G₂_H₂.some
    exact ⟨⟨F, K₁, K₂, G₃⟩,
           h_K₁_ind, Nonempty.intro f_iso_K₁_H₁,
           h_K₂_ind, Nonempty.intro f_iso_K₂_H₂,
           h_G₃_ind, h_G₃_card,
           h_K₁_K₂_disj, h_G₃_F⟩

  have h_inj_S₁'_S₂' : Function.Injective f_S₁'_S₂'_fwd := by
    intro ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, h_G₃_F⟩
    intro ⟨⟨F', G₁', G₂', G₃'⟩, h_G₁'_ind, h_G₁'_H₁, h_G₂'_ind, h_G₂'_H₂, h_G₃'_ind, h_G₃'_card, h_G₁'_G₂', h_G₁'_G₂'_G₃', h_G₃'_F⟩
    intro h_eq
    simp [f_S₁'_S₂'_fwd, subgraphFromIso, subgraphFromOrder] at h_eq
    obtain ⟨h_F_F', h_eq'⟩ := h_eq
    subst h_F_F'
    simp_all only [heq_eq_eq, Prod.mk.injEq, Subgraph.mk.injEq, Subtype.mk.injEq, and_true, true_and]
    have : G₃ = G₃' := by simp_all
    subst this
    have : h_G₃_F = h_G₃'_F := by simp
    subst this

    have ⟨h_G₁_verts_G₃_verts, h_G₂_verts_G₃_verts⟩ : G₁.verts ⊆ G₃.verts ∧ G₂.verts ⊆ G₃.verts := by
      simp_all [h_G₁_G₂_G₃]
    have ⟨h_G₁'_verts_G₃_verts, h_G₂'_verts_G₃_verts⟩ : G₁'.verts ⊆ G₃.verts ∧ G₂'.verts ⊆ G₃.verts := by
      simp_all [h_G₁'_G₂'_G₃']
    have h_eq_verts : ∀ (G₀ G₀' : Subgraph G), G₀.verts ⊆ G₃.verts → G₀'.verts ⊆ G₃.verts
                        → h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀.verts} = h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀'.verts}
                        → G₀.verts = G₀'.verts
      := fun G₀ G₀' h_G₀_G₃ h_G₀'_G₃ h_G₀_G₀' =>
      calc
        G₀.verts = {u : G₃.verts | ↑u ∈ G₀.verts} := Eq.symm (Subtype.coe_image_of_subset h_G₀_G₃)
        _ = (h_G₃_F.some.symm ∘ h_G₃_F.some) '' {u : G₃.verts | ↑u ∈ G₀.verts} := by simp
        _ = (h_G₃_F.some.symm '' (h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀.verts})) :=
              congr rfl (Set.image_comp ⇑h_G₃_F.some.symm ⇑h_G₃_F.some {u | ↑u ∈ G₀.verts})
        _ = (h_G₃_F.some.symm '' (h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀'.verts})) :=
              congr rfl (congr rfl h_G₀_G₀')
        _ = (h_G₃_F.some.symm ∘ h_G₃_F.some) '' {u : G₃.verts | ↑u ∈ G₀'.verts} :=
              congr rfl (Eq.symm (Set.image_comp ⇑h_G₃_F.some.symm ⇑h_G₃_F.some {u | ↑u ∈ G₀'.verts}))
        _ = {u : G₃.verts | ↑u ∈ G₀'.verts} := by simp
        _ = G₀'.verts := Subtype.coe_image_of_subset h_G₀'_G₃
    have h_G₁_verts_G₁'_verts : G₁.verts = G₁'.verts :=
      h_eq_verts G₁ G₁' h_G₁_verts_G₃_verts h_G₁'_verts_G₃_verts (by simp_all)
    have h_G₂_verts_G₂'_verts : G₂.verts = G₂'.verts :=
      h_eq_verts G₂ G₂' h_G₂_verts_G₃_verts h_G₂'_verts_G₃_verts (by simp_all)

    have h_eq_ind_subgraph : ∀ (G₀ G₀' : Subgraph G), G₀.IsInduced → G₀'.IsInduced → G₀.verts = G₀'.verts → G₀ = G₀'
      := fun G₀ G₀' h_G₀_ind h_G₀'_ind h_G₀_G₀' =>
      calc
        G₀ = ↑(⟨G₀, h_G₀_ind⟩ : {G' : Subgraph G | G'.IsInduced}) := rfl
        _  = ↑(inducedSubgraph G G₀.verts) := by
                apply congrArg Subtype.val
                apply inducedSubgraph_eq
        _  = ↑(inducedSubgraph G G₀'.verts) := by
                rw [←h_G₀_G₀']
        _  = ↑(⟨G₀', h_G₀'_ind⟩ : {G' : Subgraph G | G'.IsInduced}) := by
                apply congrArg Subtype.val
                apply Eq.symm
                apply inducedSubgraph_eq
        _  = G₀' := rfl

    exact ⟨h_eq_ind_subgraph G₁ G₁' h_G₁_ind h_G₁'_ind h_G₁_verts_G₁'_verts,
           h_eq_ind_subgraph G₂ G₂' h_G₂_ind h_G₂'_ind h_G₂_verts_G₂'_verts⟩

  have h_surj_S₁'_S₂' : Function.Surjective f_S₁'_S₂'_fwd := by
    intro ⟨⟨F, K₁, K₂, G₃⟩,
          h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, h_G₃_card, h_K₁_K₂_disj, h_iso_G₃_Fout⟩
    let f_G₃_Fout : G₃.coe ≃g F.out := h_iso_G₃_Fout.some
    let G₁' := subgraphFromPartialIso f_G₃_Fout.symm K₁
    let G₂' := subgraphFromPartialIso f_G₃_Fout.symm K₂
    let h_G₁'_iso := isoToSubgraphFromPartialIso f_G₃_Fout.symm K₁
    let h_G₂'_iso := isoToSubgraphFromPartialIso f_G₃_Fout.symm K₂
    let h_G₁' : G₁'.coe ≃g H₁ := h_G₁'_iso.symm.trans h_iso_K₁_H₁.some
    let h_G₂' : G₂'.coe ≃g H₂ := h_G₂'_iso.symm.trans h_iso_K₂_H₂.some
    let h_G₁'_ind : G₁'.IsInduced := subgraphFromPartialIso_preserve_inducedness f_G₃_Fout.symm K₁ h_G₃_ind h_K₁_ind
    let h_G₂'_ind : G₂'.IsInduced := subgraphFromPartialIso_preserve_inducedness f_G₃_Fout.symm K₂ h_G₃_ind h_K₂_ind
    let h_G₁'_G₂'_disj : G₁'.verts ∩ G₂'.verts = ∅ := subgraphFromPartialIso_preserve_disjointedness f_G₃_Fout.symm K₁ K₂ h_K₁_K₂_disj
    have h_G₁'_verts_union_G₂'_verts : G₁'.verts ∪ G₂'.verts ⊆ G₃.verts := by
      have h_G₁'_le_G₃ : G₁'.verts ≤ G₃.verts := by dsimp [G₁']; apply Subgraph.verts_mono; apply subgraphFromPartialIso_le
      have h_G₂'_le_G₃ : G₂'.verts ≤ G₃.verts := by dsimp [G₂']; apply Subgraph.verts_mono; apply subgraphFromPartialIso_le
      simp_all
    use ⟨⟨F, G₁', G₂', G₃⟩,
          h_G₁'_ind, Nonempty.intro h_G₁', h_G₂'_ind, Nonempty.intro h_G₂',
          h_G₃_ind, h_G₃_card, h_G₁'_G₂'_disj, h_G₁'_verts_union_G₂'_verts, h_iso_G₃_Fout⟩
    simp [G₁', G₂', f_S₁'_S₂'_fwd]
    simp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso, subgraphFromOrder, Relation.Map]
    have : h_iso_G₃_Fout.some.symm.symm = h_iso_G₃_Fout.some := rfl
    constructor <;> ext u v <;> simp

  let f_S₁'_S₂' : S₁' ≃ S₂' :=
    Equiv.ofBijective f_S₁'_S₂'_fwd ⟨h_inj_S₁'_S₂', h_surj_S₁'_S₂'⟩

  let f_S₂'_S₃'_fwd : S₂' → S₃' := by
    intro ⟨⟨F, K₁, K₂, G₃⟩,
          h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, _, h_K₁_K₂_disj, h_iso_G₃_Fout⟩
    let h_K₁_K₂_Fout : ⟨K₁,K₂⟩ ∈ subgraphPairSet H₁ H₂ F.out := by
      simp [subgraphPairSet]
      exact ⟨h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_K₁_K₂_disj⟩
    let h_G₃_G : G₃ ∈ subgraphSet F.out G := by
      simp [subgraphSet]
      exact ⟨h_G₃_ind, h_iso_G₃_Fout⟩
    exact ⟨F, ⟨⟨K₁, K₂⟩, h_K₁_K₂_Fout⟩, ⟨G₃, h_G₃_G⟩⟩

  have h_inj_S₂'_S₃' : Function.Injective f_S₂'_S₃'_fwd := by
    intro ⟨⟨F, K₁, K₂, G₃⟩,
          h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, h_G₃_card, h_K₁_K₂_disj, h_iso_G₃_Fout⟩
    intro ⟨⟨F', K₁', K₂', G₃'⟩,
          h_K₁'_ind, h_iso_K₁'_H₁, h_K₂'_ind, h_iso_K₂'_H₂, h_G₃'_ind, h_G₃'_card, h_K₁'_K₂'_disj, h_iso_G₃'_Fout⟩
    intro h_eq
    dsimp [f_S₂'_S₃'_fwd] at h_eq
    rcases h_eq with ⟨h_F_F', h_eq'⟩
    simp

  have h_surj_S₂'_S₃' : Function.Surjective f_S₂'_S₃'_fwd := by
    intro ⟨F, ⟨⟨K₁, K₂⟩, h_K₁_K₂_Fout⟩, ⟨G₃, h_G₃_G⟩⟩
    simp [subgraphSet] at h_G₃_G
    obtain ⟨h_G₃_ind, h_iso_G₃_Fout⟩ := h_G₃_G
    simp [subgraphPairSet] at h_K₁_K₂_Fout
    obtain ⟨h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_K₁_K₂_disj⟩ := h_K₁_K₂_Fout
    have h_G₃_card : Fintype.card G₃.verts = ℓ₃ := by
      rw [←Fintype.card_fin ℓ₃]
      apply Fintype.card_of_bijective (RelIso.bijective h_iso_G₃_Fout.some)
    use ⟨⟨F, K₁, K₂, G₃⟩, h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, h_G₃_card, h_K₁_K₂_disj, h_iso_G₃_Fout⟩

  let f_S₂'_S₃' : S₂' ≃ S₃' :=
    Equiv.ofBijective f_S₂'_S₃'_fwd ⟨h_inj_S₂'_S₃', h_surj_S₂'_S₃'⟩

  exact (((f_S_S₀'.trans f_S₀'_S₁').trans f_S₁'_S₂').trans f_S₂'_S₃')

def multichoose (n m₁ m₂ : ℕ) : ℕ :=
  n.choose m₁ * (n - m₁).choose m₂

noncomputable def isoGraphCount (G : SimpleGraph V) : ℕ
  := { G' : SimpleGraph V | Nonempty (G' ≃g G) }.toFinset.card

noncomputable def graphCount (ℓ : ℕ) : ℕ
  := { G' : SimpleGraph (Fin ℓ) | True }.toFinset.card

lemma graphCount_gt_zero (ℓ : ℕ) : graphCount ℓ > 0
  := by
  simp [graphCount]
  exact NeZero.one_le

lemma graphCount_eq_sum_one (ℓ : ℕ) : graphCount ℓ = ∑ (G : SimpleGraph (Fin ℓ)), 1
  := by
  simp [graphCount]

lemma subgraphPairCount_eq_sum_count_prods
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ)) (hℓ₃_lb : ℓ₁ + ℓ₂ ≤ ℓ₃)
    : subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
      =
      ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G
  := by
  let S₀ := (G_pair : subgraphPairSet H₁ H₂ G)
           × { G₃ : Subgraph G | G₃.IsInduced
                                  ∧ Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂)
                                  ∧ (G_pair.val.1.verts ∪ G_pair.val.2.verts) ∩ G₃.verts = ∅ }
  let S₁ := { (⟨⟨G₁,G₂⟩, _⟩, G₃) : subgraphPairSet H₁ H₂ G × Subgraph G
                | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts }
  let S₂ := (F : QuotSimpleGraph (Fin ℓ₃)) × subgraphPairSet H₁ H₂ F.out × subgraphSet F.out G

  have fintypeSubgraphG : Fintype (Subgraph G) := subgraphFintype G

  let f_S₀_S₁_fwd : S₀ → S₁ := fun ⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃, _, h_G₃_card, h_G₁_G₂_G₃⟩ =>
    let G₃'_ind := inducedSubgraph G (G₁.verts ∪ G₂.verts ∪ G₃.verts)
    let G₃' := G₃'_ind.val
    let h_G₃'_ind : G₃'.IsInduced := G₃'_ind.property
    have h_G₃'_card : Fintype.card G₃'.verts = ℓ₃ := by
      calc
        Fintype.card G₃'.verts
        _ = ((G₁.verts ∪ G₂.verts).toFinset ∪ G₃.verts.toFinset).card := by
              simp [G₃', G₃'_ind, inducedSubgraph]
        _ = (G₁.verts ∪ G₂.verts).toFinset.card + G₃.verts.toFinset.card := by
              have : Disjoint (G₁.verts ∪ G₂.verts).toFinset G₃.verts.toFinset := by
                apply Finset.disjoint_iff_inter_eq_empty.mpr
                rw [←Set.toFinset_inter]
                exact Set.toFinset_eq_empty.mpr h_G₁_G₂_G₃
              exact Finset.card_union_of_disjoint this
        _ = (ℓ₁ + ℓ₂) + Fintype.card G₃.verts := by
              rw [subgraphPairSet_card_union_Finset h_G₁_G₂]
              simp only [Fintype.card_fin, Set.toFinset_card]
        _ = ℓ₃ := by
              rw [h_G₃_card]
              exact (Nat.add_sub_of_le hℓ₃_lb)
    have h_G₁_G₂_G₃' : G₁.verts ∪ G₂.verts ⊆ G₃'.verts := by
      simp [G₃', G₃'_ind, inducedSubgraph]
    ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃'⟩, h_G₃'_ind, h_G₃'_card, h_G₁_G₂_G₃'⟩

  have h_inj_S₀_S₁ : Function.Injective f_S₀_S₁_fwd := by
    intro ⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    intro ⟨⟨⟨G₁', G₂'⟩, h_G₁'_G₂'⟩, G₃', h_G₃'_ind, h_G₃'_card, h_G₁'_G₂'_G₃'⟩
    intro h_eq
    simp [f_S₀_S₁_fwd] at h_eq
    simp_all
    let ⟨⟨h_G₁_G₁', h_G₂_G₂'⟩, h_ind_ind'⟩ := h_eq
    subst h_G₁_G₁' h_G₂_G₂'
    have h_G₃_verts_eq_G₃'_verts : G₃.verts = G₃'.verts :=
      let G₁_G₂_G₃_ind := inducedSubgraph G (G₁.verts ∪ G₂.verts ∪ G₃.verts)
      let G₁'_G₂'_G₃'_ind := inducedSubgraph G (G₁.verts ∪ G₂.verts ∪ G₃'.verts)
      calc
        G₃.verts
        _ = ((G₁.verts ∪ G₂.verts) ∪ G₃.verts) \ (G₁.verts ∪ G₂.verts) := by
                apply Eq.symm; apply Set.union_diff_cancel_left; simp only [h_G₁_G₂_G₃, subset_refl]
        _ = (G₁_G₂_G₃_ind : Subgraph G).verts \ (G₁.verts ∪ G₂.verts) := by
                rw [inducedSubgraph_verts G (G₁.verts ∪ G₂.verts ∪ G₃.verts)]
        _ = (G₁'_G₂'_G₃'_ind : Subgraph G).verts \ (G₁.verts ∪ G₂.verts) := by
                rw [h_ind_ind']
        _ = ((G₁.verts ∪ G₂.verts) ∪ G₃'.verts) \ (G₁.verts ∪ G₂.verts) := by
                rw [inducedSubgraph_verts G (G₁.verts ∪ G₂.verts ∪ G₃'.verts)]
        _ = G₃'.verts := by
                apply Set.union_diff_cancel_left; simp only [h_G₁'_G₂'_G₃', subset_refl]
    have : (⟨G₃, h_G₃_ind⟩ : {G' : Subgraph G | G'.IsInduced })= ⟨G₃', h_G₃'_ind⟩ := by
      rw [inducedSubgraph_eq h_G₃_ind]
      rw [inducedSubgraph_eq h_G₃'_ind]
      rw [h_G₃_verts_eq_G₃'_verts]
    simp_all only [Subtype.mk.injEq]

  have h_surj_S₀_S₁ : Function.Surjective f_S₀_S₁_fwd := by
    intro ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    let G₃'_ind := inducedSubgraph G (G₃.verts \ (G₁.verts ∪ G₂.verts))
    let G₃' := G₃'_ind.val
    have h_G₃'_ind : G₃'.IsInduced := G₃'_ind.property
    have h_G₃'_verts : G₃'.verts = G₃.verts \ (G₁.verts ∪ G₂.verts) := by
      simp [G₃', G₃'_ind, inducedSubgraph]
    have h_G₃'_card : Fintype.card G₃'.verts = ℓ₃ - (ℓ₁ + ℓ₂) :=
      calc
        Fintype.card G₃'.verts
        _ = Fintype.card ↑(G₃.verts \ (G₁.verts ∪ G₂.verts)) := by
              simp [h_G₃'_verts]
        _ = (G₃.verts \ (G₁.verts ∪ G₂.verts)).toFinset.card := by
              apply Eq.symm; apply Set.toFinset_card
        _ = (G₃.verts.toFinset \ (G₁.verts ∪ G₂.verts).toFinset).card := by
              simp
        _ = G₃.verts.toFinset.card - (G₁.verts ∪ G₂.verts).toFinset.card := by
              apply Finset.card_sdiff
              exact Set.toFinset_subset_toFinset.mpr h_G₁_G₂_G₃
        _ = ℓ₃ - (ℓ₁ + ℓ₂) := by
              rw [subgraphPairSet_card_union_Finset h_G₁_G₂]
              rw [←h_G₃_card]
              simp only [Set.toFinset_card, Fintype.card_ofFinset, Fintype.card_fin]
    have h_G₁_G₂_G₃' : (G₁.verts ∪ G₂.verts) ∩ G₃'.verts = ∅ := by
      simp [h_G₃'_verts]
    use ⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃', h_G₃'_ind, h_G₃'_card, h_G₁_G₂_G₃'⟩
    simp [f_S₀_S₁_fwd]
    have : G₁.verts ∪ G₂.verts ∪ G₃'.verts = G₃.verts := by
      simp [h_G₃'_verts, h_G₁_G₂_G₃]
    rw [this]
    rw [←(inducedSubgraph_eq h_G₃_ind)]

  let f_S₀_S₁ : S₀ ≃ S₁ := Equiv.ofBijective f_S₀_S₁_fwd ⟨h_inj_S₀_S₁, h_surj_S₀_S₁⟩
  have h_S₀_card_eq_S₁_card : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr f_S₀_S₁

  let f_S₁_S₂ : S₁ ≃ S₂ := by dsimp [S₁, S₂]; apply subgraphPairSet_iso_union_quotSimpleGraphSet
  have h_S₁_card_eq_S₂_card : Fintype.card S₁ = Fintype.card S₂ := Fintype.card_congr f_S₁_S₂

  have h_S₀_card : Fintype.card S₀ = subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
    :=
    let f : subgraphPairSet H₁ H₂ G → ℕ :=
      fun G_pair =>
        Fintype.card { G₃ : Subgraph G |
          G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂)
          ∧ (G_pair.val.1.verts ∪ G_pair.val.2.verts) ∩ G₃.verts = ∅ }
    let g : subgraphPairSet H₁ H₂ G → ℕ :=
      fun _ => (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
    have h : ∀ (G_pair : subgraphPairSet H₁ H₂ G), f G_pair = g G_pair := by
      simp [f, g]
      intro G₁ G₂ h_G₁_G₂
      let S := { G₃ : Subgraph G | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂) ∧ (G₁.verts ∪ G₂.verts) ∩ G₃.verts = ∅ }
      let U := (G₁.verts ∪ G₂.verts)ᶜ
      have h_U_size : U.toFinset.card = ℓ - (ℓ₁ + ℓ₂) :=
        calc
          U.toFinset.card
          _ = (G₁.verts ∪ G₂.verts).toFinsetᶜ.card := by
                dsimp [U]; simp only [Set.toFinset_compl]
          _ = (Fintype.card (Fin ℓ)) - (G₁.verts ∪ G₂.verts).toFinset.card :=
                Finset.card_compl (G₁.verts ∪ G₂.verts).toFinset
          _ = ℓ - (ℓ₁ + ℓ₂):= by
                rw [subgraphPairSet_card_union_Finset h_G₁_G₂]
                simp only [Fintype.card_fin]
      let S' := powersetCard (ℓ₃ - (ℓ₁ + ℓ₂)) U.toFinset
      have h_iso_S_S' : S ≃ S' :=
        let f_S_S'_fwd : S → S' := fun ⟨G₃, _, h_G₃_card, h_G₁_G₂_G₃⟩ =>
          have h_G₃_verts_S' : G₃.verts.toFinset ∈ S' := by
            simp [S', U]
            rw [Set.union_inter_distrib_right G₁.verts G₂.verts G₃.verts] at h_G₁_G₂_G₃
            have ⟨h_G₁_G₃, h_G₂_G₃⟩ : G₁.verts ∩ G₃.verts = ∅ ∧ G₂.verts ∩ G₃.verts = ∅ :=
              Set.union_empty_iff.mp h_G₁_G₂_G₃
            have h_G₃_G₁' : G₃.verts ⊆ G₁.vertsᶜ := by
              have := (Set.inter_subset G₁.verts G₃.verts ∅).mp (by simp [h_G₁_G₃])
              rw [Set.union_empty] at this
              apply Set.subset_compl_comm.mp this
            have h_G₃_G₂' : G₃.verts ⊆ G₂.vertsᶜ := by
              have := (Set.inter_subset G₂.verts G₃.verts ∅).mp (by simp [h_G₂_G₃])
              rw [Set.union_empty] at this
              apply Set.subset_compl_comm.mp this
            constructor
            . exact ⟨h_G₃_G₁', h_G₃_G₂'⟩
            . rw [←h_G₃_card]; simp
          ⟨G₃.verts.toFinset, h_G₃_verts_S'⟩
        have h_S_S'_inj : Function.Injective f_S_S'_fwd := by
          intro ⟨G₃, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
          intro ⟨G₃', h_G₃'_ind, h_G₃'_card, h_G₁'_G₂'_G₃'⟩
          intro h_eq
          simp [f_S_S'_fwd] at h_eq
          simp
          have : (⟨G₃, h_G₃_ind⟩ : {G' : Subgraph G | G'.IsInduced }) = ⟨G₃', h_G₃'_ind⟩ := by
            rw [inducedSubgraph_eq h_G₃_ind]
            rw [inducedSubgraph_eq h_G₃'_ind]
            rw [h_eq]
          simp_all only [Subtype.mk.injEq]
        have h_S_S'_surj : Function.Surjective f_S_S'_fwd := by
          intro ⟨V₀, h₀⟩
          simp [S', U] at h₀
          let ⟨h_V₀_G₁_G₂, h_V₀_card⟩ := h₀
          let G₃_ind := inducedSubgraph G V₀
          let G₃ := G₃_ind.val
          have h_G₃_ind : G₃.IsInduced := G₃_ind.property
          have h_G₃_verts : G₃.verts = V₀ := by
            simp [G₃, G₃_ind, inducedSubgraph]
          have h_G₃_card : Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂) := by
            simp [h_G₃_verts, h_V₀_card]
          have h_G₁_G₂_G₃ : (G₁.verts ∪ G₂.verts) ∩ G₃.verts = ∅ := by
            simp [h_G₃_verts]
            rw [←Finset.compl_union G₁.verts.toFinset G₂.verts.toFinset] at h_V₀_G₁_G₂
            apply Set.subset_empty_iff.mp
            calc
              (G₁.verts ∪ G₂.verts) ∩ ↑V₀
              _ ⊆ (G₁.verts ∪ G₂.verts) ∩ ↑((G₁.verts.toFinset ∪ G₂.verts.toFinset)ᶜ) := by
                    apply Set.inter_subset_inter_right
                    exact h_V₀_G₁_G₂
              _ ⊆ (G₁.verts ∪ G₂.verts) ∩ (G₁.verts ∪ G₂.verts)ᶜ := by simp
              _ = ∅ := Set.inter_compl_self (G₁.verts ∪ G₂.verts)
          use ⟨G₃, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
          simp [f_S_S'_fwd, h_G₃_verts]
        Equiv.ofBijective f_S_S'_fwd ⟨h_S_S'_inj, h_S_S'_surj⟩
      have h_S_card_eq_S'_card : Fintype.card S = Fintype.card S' := Fintype.card_congr h_iso_S_S'
      have h_S'_card_eq_choose : Fintype.card S' = (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) :=
        calc
          Fintype.card S'
          _ = S'.card := by simp only [Fintype.card_coe]
          _ = (powersetCard (ℓ₃ - (ℓ₁ + ℓ₂)) U.toFinset).card := by dsimp [S']
          _ = U.toFinset.card.choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by apply card_powersetCard
          _ = (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by simp [h_U_size]
      rw [←h_S'_card_eq_choose]
      rw [←h_S_card_eq_S'_card]
      dsimp [S]
      simp only [Fintype.card_ofFinset]
    calc
      Fintype.card S₀
      _ = ∑ (G_pair : subgraphPairSet H₁ H₂ G), f G_pair := by simp only [S₀, f, Fintype.card_sigma]
      _ = ∑ (G_pair : subgraphPairSet H₁ H₂ G), g G_pair := by simp only [h]
      _ = ∑ (_ : subgraphPairSet H₁ H₂ G), (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by simp only [g]
      _ = subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by simp [subgraphPairCount]
  have h_S₂_card : Fintype.card S₂ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G
    := by
    simp only [S₂, subgraphPairCount, subgraphCount]
    simp only [Fintype.card_sigma, Fintype.card_coe, Fintype.card_prod]

  rw [←h_S₀_card, ←h_S₂_card]
  rw [h_S₀_card_eq_S₁_card, h_S₁_card_eq_S₂_card]


lemma subgraphPairDensity_eq_sum_density_prods
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ))
    (hℓ₃_lb : ℓ₁ + ℓ₂ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ ≤ ℓ)
    : subgraphPairDensity H₁ H₂ G
      =
      ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G
  :=
  let C : ℚ := (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
  let h_C_gt_0 : C > 0 := by
    have : ℓ₃ - (ℓ₁ + ℓ₂) ≤ ℓ - (ℓ₁ + ℓ₂) := by apply Nat.sub_le_sub_right hℓ₃_ub
    simp [C, Nat.choose_pos this]
  have h_C_self_div_eq_1 : ((C : ℚ) / (C : ℚ)) = 1 :=
    div_self (ne_of_gt h_C_gt_0)
  have h_C : (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C)
              = ((ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₃) : ℚ)
    :=
    calc
      ((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * ((ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))) := by
              simp [C]
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂ * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))) : ℚ) := by
              simp
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂ * ((ℓ - ℓ₁) - ℓ₂).choose ((ℓ₃ - ℓ₁) - ℓ₂)) : ℚ) := by
              have : ℓ - (ℓ₁ + ℓ₂) = (ℓ - ℓ₁) - ℓ₂ := Nat.sub_add_eq ℓ ℓ₁ ℓ₂
              rw [this]
              have : ℓ₃ - (ℓ₁ + ℓ₂) = (ℓ₃ - ℓ₁) - ℓ₂ := Nat.sub_add_eq ℓ₃ ℓ₁ ℓ₂
              rw [this]
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose (ℓ₃ - ℓ₁) * (ℓ₃ - ℓ₁).choose ℓ₂) : ℚ) := by
              rw [mul_assoc, mul_assoc]
              have h₀ : (ℓ₃ - ℓ₁) ≤ (ℓ - ℓ₁) := by apply Nat.sub_le_sub_right hℓ₃_ub
              have h₁ : ℓ₂ ≤ ℓ₃ - ℓ₁ := Nat.le_sub_of_add_le' hℓ₃_lb
              rw [Nat.choose_mul h₀ h₁]
      _ = (↑(ℓ.choose ℓ₃ * ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂) : ℚ) := by
              have h₀ : ℓ₃ ≤ ℓ := hℓ₃_ub
              have h₁ : ℓ₁ ≤ ℓ₃ :=
                calc
                  ℓ₁ ≤ ℓ₁ + ℓ₂ := Nat.le_add_right ℓ₁ ℓ₂
                  _ ≤ ℓ₃ := hℓ₃_lb
              rw [Nat.choose_mul h₀ h₁]
      _ = ((ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₃) : ℚ) := by
              simp only [mul_assoc, Nat.cast_mul, mul_comm]
  calc
    subgraphPairDensity H₁ H₂ G
    _ = ((subgraphPairCount H₁ H₂ G : ℚ) / (ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂)) * 1 := by
              simp [subgraphPairDensity]
    _ = ((subgraphPairCount H₁ H₂ G : ℚ) / (ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂)) * (C / C) := by
              simp [h_C_self_div_eq_1]
    _ = ((subgraphPairCount H₁ H₂ G : ℚ) * C) / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp [div_mul_div_comm (subgraphPairCount H₁ H₂ G : ℚ) ((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) C C]
    _ = (↑(subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))) : ℚ)
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp [C]
    _ = ((∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ)
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp [subgraphPairCount_eq_sum_count_prods H₁ H₂ G hℓ₃_lb]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₃)), ((subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ))
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)),
          ((subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ)
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              apply sum_div
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)),
          ((subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ)
          / ((ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₃) : ℚ) := by
              simp [h_C]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)),
          ((subgraphPairCount H₁ H₂ F.out : ℚ) / (ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂))
          * ((subgraphCount F.out G : ℚ) / ℓ.choose ℓ₃) := by
              simp only [div_mul_div_comm]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G := by
              simp [subgraphPairDensity, subgraphDensity]

lemma subgraphPairDensityLifted_eq_sum_density_prods
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ))
    (hℓ₃_lb : ℓ₁ + ℓ₂ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ ≤ ℓ)
    : subgraphPairDensity H₁ H₂ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * quotSubgraphDensity F ⟦G⟧
  := by

  have h₀ : ∀ {F : QuotSimpleGraph (Fin ℓ₃)}, quotSubgraphDensity F ⟦G⟧ = subgraphDensityLifted F.out ⟦G⟧
    := by
    intro F
    calc
      quotSubgraphDensity F ⟦G⟧
      _ = Quot.lift subgraphDensityLifted ?h F ⟦G⟧ := rfl
      _ = Quot.lift subgraphDensityLifted ?h ⟦F.out⟧ ⟦G⟧ := by simp
      _ = subgraphDensityLifted F.out ⟦G⟧ := rfl
    intro F₀ F₁ h_eqv; ext G''; exact subgraphDensityLifted_respects_eqv F₀ F₁ h_eqv G''
  have h_RHS₀ : ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * quotSubgraphDensity F ⟦G⟧
                = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * subgraphDensityLifted F.out ⟦G⟧
    := by simp [h₀]
  rw [h_RHS₀]

  have h₁ : ∀ {F : QuotSimpleGraph (Fin ℓ₃)}, subgraphDensityLifted F.out ⟦G⟧ = subgraphDensity F.out G
    := by
    intro F
    calc
      subgraphDensityLifted F.out ⟦G⟧
      _ = @Quot.lift _ graph_eqv _ (subgraphDensity F.out) ?h' ⟦G⟧ := rfl
      _ = subgraphDensity F.out G := rfl
    intro _ _ h_eqv; exact subgraphDensity_respects_eqv_on_G F.out h_eqv
  have h₂ : ∀ {F : QuotSimpleGraph (Fin ℓ₃)}, subgraphPairDensityLifted H₁ H₂ F = subgraphPairDensity H₁ H₂ F.out
    := by
    intro F
    calc
      subgraphPairDensityLifted H₁ H₂ F
      _ = Quot.lift (subgraphPairDensity H₁ H₂) ?h'' F := rfl
      _ = Quot.lift (subgraphPairDensity H₁ H₂) ?h'' ⟦F.out⟧ := by simp
      _ = subgraphPairDensity H₁ H₂ F.out := rfl
    intro F₀ F₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G H₁ H₂ h_eqv
  have h_RHS₁ : ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * subgraphDensityLifted F.out ⟦G⟧
                = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G
    := by simp [h₁,h₂]
  rw [h_RHS₁]

  show subgraphPairDensity H₁ H₂ G
       = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G
  exact subgraphPairDensity_eq_sum_density_prods H₁ H₂ G hℓ₃_lb hℓ₃_ub


theorem quotSubgraphPairDensity_eq_sum_density_prods
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₃ : ℕ} (hℓ₃_lb: ℓ₁ + ℓ₂ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ ≤ ℓ)
    : quotSubgraphPairDensity H₁ H₂ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphDensity F G
  := by
  rcases Quotient.exists_rep H₁ with ⟨H₁rep, hH₁rep⟩
  rcases Quotient.exists_rep H₂ with ⟨H₂rep, hH₂rep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hH₁rep, ← hH₂rep, ← hGrep]
  exact subgraphPairDensityLifted_eq_sum_density_prods H₁rep H₂rep Grep hℓ₃_lb hℓ₃_ub


theorem quotSubgraphDensity_eq_sum_density_prods
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₂ : ℕ} (hℓ₂_lb: ℓ₁ ≤ ℓ₂) (hℓ₂_ub : ℓ₂ ≤ ℓ)
    : quotSubgraphDensity H₁ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphDensity H₁ F * quotSubgraphDensity F G
  := by
  let H₀ : QuotSimpleGraph (Fin 0) := ⟦emptyGraph (Fin 0)⟧
  let h_lb : 0 + ℓ₁ ≤ ℓ₂ := by simp [hℓ₂_lb]

  have h_LHS : quotSubgraphPairDensity H₀ H₁ G = quotSubgraphDensity H₁ G :=
    quotSubgraphPairDensity_empty H₁ G
  rw [←h_LHS]

  have h : ∀ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphPairDensity H₀ H₁ F = quotSubgraphDensity H₁ F := by
    intro F
    rw [quotSubgraphPairDensity_empty H₁ F]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphDensity H₁ F * quotSubgraphDensity F G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphPairDensity H₀ H₁ F * quotSubgraphDensity F G := by
    simp [h]
  rw [h_RHS]

  exact quotSubgraphPairDensity_eq_sum_density_prods H₀ H₁ G h_lb hℓ₂_ub


/- Hongseok: The following definition of the triple density is a hack which would let us proceed but which we should fix at some point. -/
noncomputable def quotSubgraphTripleDensity
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph W)
    : ℚ
  :=
  ∑ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G


lemma quotSubgraphTripleDensity_empty
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (G : QuotSimpleGraph (Fin ℓ)) (hℓ : ℓ₁ + ℓ₂ ≤ ℓ)
    : quotSubgraphTripleDensity ⟦emptyGraph (Fin 0)⟧ H₁ H₂ G = quotSubgraphPairDensity H₁ H₂ G
  := by
  let H₀ : QuotSimpleGraph (Fin 0) := ⟦emptyGraph (Fin 0)⟧
  dsimp [quotSubgraphTripleDensity]
  apply Eq.symm
  show quotSubgraphPairDensity H₁ H₂ G
        = ∑ F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity H₀ F G

  have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₀ F G = quotSubgraphDensity F G := by
    intro F
    rw [quotSubgraphPairDensity_empty F]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity H₀ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphDensity F G := by
    simp [h]
  rw [h_RHS]

  exact quotSubgraphPairDensity_eq_sum_density_prods H₁ H₂ G (Nat.le_refl (ℓ₁ + ℓ₂)) hℓ

noncomputable def subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    : (F : QuotSimpleGraph (Fin ℓ₁₂))
        × (Fpair : subgraphPairSet H₁ H₂ F.out)
        × subgraphPairSet F.out H₃ G
        × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset
      ≃
      (F : QuotSimpleGraph (Fin ℓ₂₃))
        × subgraphPairSet H₂ H₃ F.out
        × (Gpair : subgraphPairSet F.out H₁ G)
        × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset
  := by

  let S₁ := (F : QuotSimpleGraph (Fin ℓ₁₂))
              × (Fpair : subgraphPairSet H₁ H₂ F.out)
              × subgraphPairSet F.out H₃ G
              × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset
  let S₂ := { ⟨X₁, X₂, X₃, X₄, X₅⟩ :  Finset (Fin ℓ) × Finset (Fin ℓ)
                                    × Finset (Fin ℓ) × Finset (Fin ℓ) × Finset (Fin ℓ)
                  | X₁ ∩ X₂ = ∅
                  ∧ (X₁ ∪ X₂) ∩ X₃ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅
                  ∧ X₁.card = ℓ₁
                  ∧ X₂.card = ℓ₂
                  ∧ X₃.card = ℓ₃
                  ∧ X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃)
                  ∧ X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ Nonempty ((inducedSubgraph G X₁).val.coe ≃g H₁)
                  ∧ Nonempty ((inducedSubgraph G X₂).val.coe ≃g H₂)
                  ∧ Nonempty ((inducedSubgraph G X₃).val.coe ≃g H₃) }
  let S₃ := (F : QuotSimpleGraph (Fin ℓ₂₃))
              × subgraphPairSet H₂ H₃ F.out
              × (Gpair : subgraphPairSet F.out H₁ G)
              × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset

  let f_S₁_S₂_fwd : S₁ → S₂ := by
    intro ⟨F, Fpair, Gpair, X⟩

    have h_Fpair := Fpair.property
    simp [subgraphPairSet] at h_Fpair
    obtain ⟨h_Fpair1_ind, h_Fpair1_H₁, h_Fpair2_ind, h_Fpair2_H₂, h_Fpair_disj⟩ := h_Fpair
    let f_Fpair1_H₁ : Fpair.val.1.coe ≃g H₁ := h_Fpair1_H₁.some
    let f_Fpair2_H₂ : Fpair.val.2.coe ≃g H₂ := h_Fpair2_H₂.some

    have h_Gpair := Gpair.property
    simp [subgraphPairSet] at h_Gpair
    obtain ⟨h_Gpair1_ind, h_Gpair1_Fout, h_Gpair2_ind, h_Gpair2_H₃, h_Gpair_disj⟩ := h_Gpair
    let g_Gpair1_Fout : Gpair.val.1.coe ≃g F.out := h_Gpair1_Fout.some
    let g_Gpair2_H₃ : Gpair.val.2.coe ≃g H₃:= h_Gpair2_H₃.some

    let X₁ : Finset (Fin ℓ) := ((Subtype.val ∘ g_Gpair1_Fout.symm) '' Fpair.val.1.verts).toFinset
    let X₂ : Finset (Fin ℓ) := ((Subtype.val ∘ g_Gpair1_Fout.symm) '' Fpair.val.2.verts).toFinset
    let X₃ : Finset (Fin ℓ) := ((Subtype.val ∘ g_Gpair2_H₃.symm) '' (univ : Finset (Fin ℓ₃))).toFinset
    let X₄ : Finset (Fin ℓ) := ((Subtype.val ∘ g_Gpair1_Fout.symm) '' X).toFinset
    let X₅ : Finset (Fin ℓ) := ((Subtype.val ∘ g_Gpair1_Fout.symm) '' (Fpair.val.1.verts ∪ Fpair.val.2.verts ∪ X)ᶜ).toFinset
    let h_X₁_X₂_disj : X₁ ∩ X₂ = ∅ := sorry
    exact ⟨⟨X₁, X₂, X₃, X₄, X₅⟩, h_X₁_X₂_disj, sorry⟩

  have h_f_S₁_S₂_inj : Function.Injective f_S₁_S₂_fwd := by sorry
  have h_f_S₁_S₂_surj : Function.Surjective f_S₁_S₂_fwd := by sorry
  let f_S₁_S₂ : S₁ ≃ S₂ := Equiv.ofBijective f_S₁_S₂_fwd ⟨h_f_S₁_S₂_inj, h_f_S₁_S₂_surj⟩

  let f_S₂_S₃_fwd : S₂ → S₃ := by sorry
  have h_f_S₂_S₃_inj : Function.Injective f_S₂_S₃_fwd := by sorry
  have h_f_S₂_S₃_surj : Function.Surjective f_S₂_S₃_fwd := by sorry
  let f_S₂_S₃ : S₂ ≃ S₃ := Equiv.ofBijective f_S₂_S₃_fwd ⟨h_f_S₂_S₃_inj, h_f_S₂_S₃_surj⟩

  exact f_S₁_S₂.trans f_S₂_S₃

lemma subgraphPairCount_sum_assoc
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out
          * subgraphPairCount F.out H₃ G
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out
          * subgraphPairCount F.out H₁ G
          * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  := by
  let f_LHS (F : QuotSimpleGraph (Fin ℓ₁₂)) :=
    (Fpair : subgraphPairSet H₁ H₂ F.out)
    × subgraphPairSet F.out H₃ G
    × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset
  let f_RHS (F : QuotSimpleGraph (Fin ℓ₂₃)) :=
    subgraphPairSet H₂ H₃ F.out
    × (Gpair : subgraphPairSet F.out H₁ G)
    × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset
  have h_iso : (F : QuotSimpleGraph (Fin ℓ₁₂)) × f_LHS F ≃ (F : QuotSimpleGraph (Fin ℓ₂₃)) × f_RHS F :=
    subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet
      H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h

  have h_LHS : ∀ (F : QuotSimpleGraph (Fin ℓ₁₂)),
                Fintype.card (f_LHS F)
                =
                subgraphPairCount H₁ H₂ F.out
                * subgraphPairCount F.out H₃ G
                * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
    := by
    intro F
    have h₁ : ∀ (Fpair : subgraphPairSet H₁ H₂ F.out),
                Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset)
                = (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
      := by
      intro Fpair
      calc
        Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset)
        _ = (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset).card := by
                simp only [Fintype.card_coe]
        _ = ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                apply card_powersetCard
        _ = (Fpair.val.1.verts ∪ Fpair.val.2.verts).toFinsetᶜ.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [Set.toFinset_compl]
        _ = (Fintype.card (Fin ℓ₁₂) - (Fpair.val.1.verts ∪ Fpair.val.2.verts).toFinset.card).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                rw [Finset.card_compl (Fpair.val.1.verts ∪ Fpair.val.2.verts).toFinset]
        _ = (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                rw [subgraphPairSet_card_union_Finset Fpair.property]
                simp only [Fintype.card_fin]
    calc
      Fintype.card (f_LHS F)
      _ = ∑ (Fpair : subgraphPairSet H₁ H₂ F.out),
            Fintype.card (subgraphPairSet F.out H₃ G)
            * Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset) := by
                simp only [f_LHS, Fintype.card_sigma, Fintype.card_prod]
      _ = ∑ (_ : subgraphPairSet H₁ H₂ F.out),
            Fintype.card (subgraphPairSet F.out H₃ G)
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                simp only [h₁]
      _ = Fintype.card (subgraphPairSet H₁ H₂ F.out)
          * (Fintype.card (subgraphPairSet F.out H₃ G) * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) := by
                simp only [univ_eq_attach, Fintype.card_coe, sum_const, card_attach, smul_eq_mul]
      _ = Fintype.card (subgraphPairSet H₁ H₂ F.out)
          * Fintype.card (subgraphPairSet F.out H₃ G)
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                apply Eq.symm; apply mul_assoc
      _ = subgraphPairCount H₁ H₂ F.out
          * subgraphPairCount F.out H₃ G
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                simp only [Fintype.card_coe, subgraphPairCount]

  have h_RHS : ∀ (F : QuotSimpleGraph (Fin ℓ₂₃)),
                Fintype.card (f_RHS F)
                =
                subgraphPairCount H₂ H₃ F.out
                * subgraphPairCount F.out H₁ G
                * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃))
    := by
    intro F
    have h₁' : ∀ (Gpair : subgraphPairSet F.out H₁ G),
                Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset)
                = (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃))
      := by
      intro Gpair
      calc
        Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset)
        _ = (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset).card := by
                simp only [Fintype.card_coe]
        _ = ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                apply card_powersetCard
        _ = (Gpair.val.1.verts ∪ Gpair.val.2.verts).toFinsetᶜ.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [Set.toFinset_compl]
        _ = (Fintype.card (Fin ℓ) - (Gpair.val.1.verts ∪ Gpair.val.2.verts).toFinset.card).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                rw [Finset.card_compl (Gpair.val.1.verts ∪ Gpair.val.2.verts).toFinset]
        _ = (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                rw [subgraphPairSet_card_union_Finset Gpair.property]
                simp only [add_comm, Fintype.card_fin]
    calc
      Fintype.card (f_RHS F)
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * ∑ (Gpair : subgraphPairSet F.out H₁ G),
              Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset) := by
                simp only [f_RHS, Fintype.card_sigma, Fintype.card_prod]
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * ∑ (_ : subgraphPairSet F.out H₁ G),
              (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [h₁']
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * (Fintype.card (subgraphPairSet F.out H₁ G) * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃))) := by
                simp only [Fintype.card_coe, univ_eq_attach, sum_const, card_attach, smul_eq_mul]
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * Fintype.card (subgraphPairSet F.out H₁ G)
          * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                apply Eq.symm; apply mul_assoc
      _ = subgraphPairCount H₂ H₃ F.out
          * subgraphPairCount F.out H₁ G
          * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [Fintype.card_coe, subgraphPairCount]

  calc
    ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), Fintype.card (f_LHS F) := by
              simp [h_LHS]
    _ = Fintype.card ((F : QuotSimpleGraph (Fin ℓ₁₂)) × f_LHS F) :=
              Eq.symm Fintype.card_sigma
    _ = Fintype.card ((F : QuotSimpleGraph (Fin ℓ₂₃)) × f_RHS F) :=
              Fintype.card_congr h_iso
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), Fintype.card (f_RHS F) :=
              Fintype.card_sigma
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G
            * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
              simp [h_RHS]


lemma choose_eq_factorial_div_factorial_rational
    {n k : ℕ} (h_k_n : k ≤ n) :
    (↑(n.choose k) : ℚ) = ((↑n.factorial / (↑k.factorial * ↑(n - k).factorial)) : ℚ)
  :=
  calc
    ↑(n.choose k)
    _ = (↑(n.factorial / (k.factorial * (n - k).factorial)) : ℚ) := by
        rw [Nat.choose_eq_factorial_div_factorial h_k_n]
    _ = (↑n.factorial / (↑k.factorial * ↑(n - k).factorial)) := by
        have h_dvd : (k.factorial * (n - k).factorial) ∣ n.factorial :=
          Nat.factorial_mul_factorial_dvd_factorial h_k_n
        simp only [h_dvd, Nat.cast_div_charZero, Nat.cast_mul]

lemma subgraphPairDensity_sum_assoc
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G
  :=
  let C₁₂ : ℚ := (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₁₂_gt_0 : C₁₂ > 0 := by
    have : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ₁₂ - (ℓ₁ + ℓ₂) :=
      calc
        ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂ + ℓ₃) := by apply Nat.sub_le_sub_left; linarith
        _ ≤ ℓ₁₂ - (ℓ₁ + ℓ₂) := add_tsub_add_le_tsub_right
    simp [C₁₂, Nat.choose_pos this]
  have h_C₁₂_self_div_eq_1 : C₁₂ / C₁₂ = 1 :=
    div_self (ne_of_gt h_C₁₂_gt_0)

  let C₂₃ : ℚ := (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₂₃_gt_0 : C₂₃ > 0 := by
    have : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ - (ℓ₁ + ℓ₂₃) := Nat.sub_le_sub_right hℓ₁₂_ub (ℓ₁ + ℓ₂₃)
    simp [C₂₃, Nat.choose_pos this]
  have h_C₂₃_self_div_eq_1 : C₂₃ / C₂₃ = 1 :=
    div_self (ne_of_gt h_C₂₃_gt_0)

  have h_C₁₂_C₂₃ : ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂
                    = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃ :=
    have h₁ : ℓ₁ ≤ ℓ₁₂ := by linarith
    have h₂ : ℓ₂ ≤ ℓ₁₂ - ℓ₁ := (Nat.le_sub_iff_add_le' h₁).mpr hℓ₁₂_lb
    have h₃ : ℓ₁₂ ≤ ℓ := by linarith
    have h₄ : ℓ₃ ≤ ℓ - ℓ₁₂ := (Nat.le_sub_iff_add_le' h₃).mpr hℓ₁₂_ub
    have h₅ : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ₁₂ - (ℓ₁ + ℓ₂) := by
      apply (Nat.le_sub_iff_add_le' hℓ₁₂_lb).mpr
      rw [←Nat.add_sub_assoc h (ℓ₁ + ℓ₂)]
      apply Nat.sub_le_of_le_add
      linarith
    have h₁' : ℓ₂ ≤ ℓ₂₃ := by linarith
    have h₂' : ℓ₃ ≤ ℓ₂₃ - ℓ₂ := (Nat.le_sub_iff_add_le' h₁').mpr hℓ₂₃_lb
    have h₃' : ℓ₂₃ ≤ ℓ := by linarith
    have h₄' : ℓ₁ ≤ ℓ - ℓ₂₃ := by apply (Nat.le_sub_iff_add_le' h₃').mpr; linarith
    have h₅' : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ - (ℓ₁ + ℓ₂₃) := by
      apply (Nat.le_sub_iff_add_le' hℓ₂₃_ub).mpr
      rw [←Nat.add_sub_assoc h (ℓ₁ + ℓ₂₃)]
      apply Nat.sub_le_of_le_add
      linarith
    calc
      ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂
      _ = ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
          * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                dsimp [C₁₂]
      _ = (↑ℓ₁₂.factorial / (↑ℓ₁.factorial * ↑(ℓ₁₂ - ℓ₁).factorial))
          * (↑(ℓ₁₂ - ℓ₁).factorial / (↑ℓ₂.factorial * ↑(ℓ₁₂ - ℓ₁ - ℓ₂).factorial))
          * (↑ℓ.factorial / (↑ℓ₁₂.factorial * ↑(ℓ - ℓ₁₂).factorial))
          * (↑(ℓ - ℓ₁₂).factorial / (↑ℓ₃.factorial * ↑(ℓ - ℓ₁₂ - ℓ₃).factorial))
          * (↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))).factorial)) := by
                rw [choose_eq_factorial_div_factorial_rational h₁]
                rw [choose_eq_factorial_div_factorial_rational h₂]
                rw [choose_eq_factorial_div_factorial_rational h₃]
                rw [choose_eq_factorial_div_factorial_rational h₄]
                rw [choose_eq_factorial_div_factorial_rational h₅]
      _ = (↑ℓ₁₂.factorial / (↑ℓ₁.factorial * ↑(ℓ₁₂ - ℓ₁).factorial))
          * (↑(ℓ₁₂ - ℓ₁).factorial / (↑ℓ₂.factorial * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial))
          * (↑ℓ.factorial / (↑ℓ₁₂.factorial * ↑(ℓ - ℓ₁₂).factorial))
          * (↑(ℓ - ℓ₁₂).factorial / (↑ℓ₃.factorial * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial))
          * (↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial)) := by
                have : ℓ₁₂ - ℓ₁ - ℓ₂ = ℓ₁₂ - (ℓ₁ + ℓ₂) := by exact Nat.sub_sub ℓ₁₂ ℓ₁ ℓ₂
                rw [this]
                have : ℓ - ℓ₁₂ - ℓ₃ = ℓ - (ℓ₁₂ + ℓ₃) := by exact Nat.sub_sub ℓ ℓ₁₂ ℓ₃
                rw [this]
                have : ℓ₁₂ - (ℓ₁ + ℓ₂) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ₂₃ - (ℓ₂ + ℓ₃) := by
                  refine Eq.symm (tsub_eq_tsub_of_add_eq_add ?h')
                  rw [←Nat.add_sub_assoc h ℓ₂₃]
                  apply Nat.sub_eq_of_eq_add
                  ring_nf
                  rw [←Nat.add_sub_assoc hℓ₁₂_lb (ℓ₂₃ + ℓ₃ + ℓ₁ + ℓ₂)]
                  refine Eq.symm (Nat.sub_eq_of_eq_add ?h'')
                  linarith
                rw [this]
      _ = (↑ℓ₁₂.factorial
            * ↑(ℓ₁₂ - ℓ₁).factorial
            * ↑ℓ.factorial
            * ↑(ℓ - ℓ₁₂).factorial
            * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial)
          / (↑ℓ₁.factorial
              * ↑(ℓ₁₂ - ℓ₁).factorial
              * ↑ℓ₂.factorial
              * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial
              * ↑ℓ₁₂.factorial
              * ↑(ℓ - ℓ₁₂).factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial) := by
                simp only [div_mul_div_comm, mul_assoc, Nat.cast_mul]
      _ = ↑ℓ.factorial
          / (↑ℓ₁.factorial
              * ↑ℓ₂.factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial) := by
              field_simp
              ring
        _ = ↑ℓ.factorial
          / (↑ℓ₂.factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial
              * ↑ℓ₁.factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial) := by
              ring
      _ = (↑ℓ₂₃.factorial
            * ↑(ℓ₂₃ - ℓ₂).factorial
            * ↑ℓ.factorial
            * ↑(ℓ - ℓ₂₃).factorial
            * ↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial)
          / (↑ℓ₂.factorial
              * ↑(ℓ₂₃ - ℓ₂).factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial
              * ↑ℓ₂₃.factorial
              * ↑(ℓ - ℓ₂₃).factorial
              * ↑ℓ₁.factorial
              * ↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial) := by
              field_simp
              ring
      _ = (↑ℓ₂₃.factorial / (↑ℓ₂.factorial * ↑(ℓ₂₃ - ℓ₂).factorial))
          * (↑(ℓ₂₃ - ℓ₂).factorial / (↑ℓ₃.factorial * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial))
          * (↑ℓ.factorial / (↑ℓ₂₃.factorial * ↑(ℓ - ℓ₂₃).factorial))
          * (↑(ℓ - ℓ₂₃).factorial / (↑ℓ₁.factorial * ↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial))
          * (↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial)) := by
              simp only [div_mul_div_comm, mul_assoc, Nat.cast_mul]
      _ = (↑ℓ₂₃.factorial / (↑ℓ₂.factorial * ↑(ℓ₂₃ - ℓ₂).factorial))
          * (↑(ℓ₂₃ - ℓ₂).factorial / (↑ℓ₃.factorial * ↑(ℓ₂₃ - ℓ₂ - ℓ₃).factorial))
          * (↑ℓ.factorial / (↑ℓ₂₃.factorial * ↑(ℓ - ℓ₂₃).factorial))
          * (↑(ℓ - ℓ₂₃).factorial / (↑ℓ₁.factorial * ↑(ℓ - ℓ₂₃ - ℓ₁).factorial))
          * (↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial * ↑(ℓ - (ℓ₁ + ℓ₂₃) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))).factorial)) := by
              have : ℓ₂₃ - ℓ₂ - ℓ₃ = ℓ₂₃ - (ℓ₂ + ℓ₃) := Nat.sub_sub ℓ₂₃ ℓ₂ ℓ₃
              rw [this]
              have : ℓ - ℓ₂₃ - ℓ₁ = ℓ - (ℓ₁ + ℓ₂₃) := Eq.symm (Nat.Simproc.sub_add_eq_comm ℓ ℓ₁ ℓ₂₃)
              rw [this]
              have : ℓ - (ℓ₁ + ℓ₂₃) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ - (ℓ₁₂ + ℓ₃) := by
                refine Eq.symm (tsub_eq_tsub_of_add_eq_add ?h)
                ring_nf
                rw [←Nat.add_sub_assoc h ℓ]
                apply Nat.sub_eq_of_eq_add
                ring_nf
                rw [←Nat.add_sub_assoc hℓ₂₃_ub _]
                refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
                linarith
              rw [this]
      _ = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
              rw [choose_eq_factorial_div_factorial_rational h₁']
              rw [choose_eq_factorial_div_factorial_rational h₂']
              rw [choose_eq_factorial_div_factorial_rational h₃']
              rw [choose_eq_factorial_div_factorial_rational h₄']
              rw [choose_eq_factorial_div_factorial_rational h₅']
      _ = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃ := by
              dsimp [C₂₃]

  calc
    ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairDensity H₁ H₂ F.out
            * subgraphPairDensity F.out H₃ G
            * (C₁₂ / C₁₂) := by
                simp only [h_C₁₂_self_div_eq_1, mul_one]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            (subgraphPairCount H₁ H₂ F.out / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂) : ℚ))
            * (subgraphPairCount F.out H₃ G / ((ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃) : ℚ))
            * (C₁₂ / C₁₂) := by
                simp only [subgraphPairDensity, Fintype.card_fin, Nat.cast_mul]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            (subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G * C₁₂)
            / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                simp only [div_mul_div_comm, mul_assoc]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G * C₁₂)
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                apply Eq.symm; apply sum_div
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out
            * subgraphPairCount F.out H₃ G
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)))
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
            * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, C₁₂]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G
            * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)))
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
            * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) : ℚ) := by
                rw [subgraphPairCount_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h]
    _  = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, C₂₃, C₁₂]
    _  = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
        / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃) : ℚ) := by
                rw [h_C₁₂_C₂₃]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          (subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
          / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃) : ℚ) := by
                apply sum_div
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          (subgraphPairCount H₂ H₃ F.out / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃) : ℚ))
          * (subgraphPairCount F.out H₁ G / ((ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁) : ℚ))
          * (C₂₃ / C₂₃) := by
                simp only [div_mul_div_comm, mul_assoc]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
                simp only [h_C₂₃_self_div_eq_1, mul_one, subgraphPairDensity, Fintype.card_fin, Nat.cast_mul]


lemma subgraphPairDensityLifted_sum_assoc'
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairDensityLifted H₁ H₂ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          subgraphPairDensityLifted H₂ H₃ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧
  := by
  have h₀ : ∀ {F : QuotSimpleGraph (Fin ℓ₁₂)},
              subgraphPairDensityLifted H₁ H₂ F * subgraphPairDensityLifted F.out H₃ ⟦G⟧
              = subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G := by
    intro F
    calc
      subgraphPairDensityLifted H₁ H₂ F * subgraphPairDensityLifted F.out H₃ ⟦G⟧
      _ = subgraphPairDensityLifted H₁ H₂ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧ := by simp only [Quotient.out_eq]
      _ = @Quot.lift _ graph_eqv _ (subgraphPairDensity H₁ H₂) ?h₀' ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₁ H₂ F.out * subgraphPairDensityLifted F.out H₃ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₁ H₂ F.out * @Quot.lift _ graph_eqv _ (subgraphPairDensity F.out H₃) ?h₀'' ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G := by rfl
    . intro F₀ F₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G H₁ H₂ h_eqv
    . intro G₀ G₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G F.out H₃ h_eqv
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensityLifted H₁ H₂ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧
              = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G := by
    simp only [Quotient.out_eq, h₀]
  rw [h_LHS]

  have h₁ : ∀ {F : QuotSimpleGraph (Fin ℓ₂₃)},
              subgraphPairDensityLifted H₂ H₃ F * subgraphPairDensityLifted F.out H₁ ⟦G⟧
              = subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
    intro F
    calc
      subgraphPairDensityLifted H₂ H₃ F * subgraphPairDensityLifted F.out H₁ ⟦G⟧
      _ = subgraphPairDensityLifted H₂ H₃ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧ := by simp only [Quotient.out_eq]
      _ = @Quot.lift _ graph_eqv _ (subgraphPairDensity H₂ H₃) ?h₁' ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₂ H₃ F.out * subgraphPairDensityLifted F.out H₁ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₂ H₃ F.out * @Quot.lift _ graph_eqv _ (subgraphPairDensity F.out H₁) ?h₁'' ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by rfl
    . intro F₀ F₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G H₂ H₃ h_eqv
    . intro G₀ G₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G F.out H₁ h_eqv
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensityLifted H₂ H₃ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧
              = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
    simp only [Quotient.out_eq, h₁]
  rw [h_RHS]

  exact subgraphPairDensity_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h


lemma quotSubgraphPairDensity_sum_assoc'
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity F H₁ G
  := by
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ ⟦F.out⟧ * quotSubgraphPairDensity ⟦F.out⟧ H₃ G
    := by simp
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity F H₁ G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ ⟦F.out⟧ * quotSubgraphPairDensity ⟦F.out⟧ H₁ G
    := by simp
  rw [h_LHS, h_RHS]

  rcases Quotient.exists_rep H₁ with ⟨H₁rep, hH₁rep⟩
  rcases Quotient.exists_rep H₂ with ⟨H₂rep, hH₂rep⟩
  rcases Quotient.exists_rep H₃ with ⟨H₃rep, hH₃rep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hH₁rep, ← hH₂rep, ← hH₃rep, ← hGrep]
  exact subgraphPairDensityLifted_sum_assoc' H₁rep H₂rep H₃rep Grep hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h


lemma quotSubgraphPairDensity_sum_assoc
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
  := by
  by_cases h_ge : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃
  {
    have h_comm : ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
                  = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity F H₁ G
      := quotSubgraphPairDensity_sum_assoc' H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h_ge
    rw [h_comm]
    have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₂₃))), quotSubgraphPairDensity F H₁ G = quotSubgraphPairDensity H₁ F G := by
      intro F
      rw [quotSubgraphPairDensity_comm F H₁ G]
    simp only [h]
  }
  {
    have h₀' : ∀ (F : QuotSimpleGraph (Fin (ℓ₂₃))),
               quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
                = quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity F H₁ G := by
        intro F
        rw [quotSubgraphPairDensity_comm F H₁ G, quotSubgraphPairDensity_comm H₂ H₃ F]
    have h_comm₀' :  ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
                   = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity F H₁ G := by
      simp [h₀']
    rw [h_comm₀']

    have h₁' : ∀ (F : QuotSimpleGraph (Fin (ℓ₁₂))), quotSubgraphPairDensity H₁ H₂ F = quotSubgraphPairDensity H₂ H₁ F := by
      intro F
      rw [quotSubgraphPairDensity_comm H₁ H₂ F]
    have h_comm₁' :  ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
                   = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₂ H₁ F * quotSubgraphPairDensity F H₃ G := by
      simp [h₁']
    rw [h_comm₁']

    have h_ge' : ℓ₂₃ + ℓ₁ ≥ ℓ₃ + ℓ₁₂ := by linarith [h_ge]
    have hℓ₃₂_lb : ℓ₃ + ℓ₂ ≤ ℓ₂₃ := by linarith [hℓ₂₃_lb]
    have hℓ₃₂_ub : ℓ₂₃ + ℓ₁ ≤ ℓ := by linarith [hℓ₂₃_ub]
    have hℓ₂₁_lb : ℓ₂ + ℓ₁ ≤ ℓ₁₂ := by linarith [hℓ₁₂_lb]
    have hℓ₂₁_ub : ℓ₃ + ℓ₁₂ ≤ ℓ := by linarith [hℓ₁₂_ub]
    have h_comm₂' :   ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity F H₁ G
                    = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₂ H₁ F * quotSubgraphPairDensity F H₃ G
      := quotSubgraphPairDensity_sum_assoc' H₃ H₂ H₁ G hℓ₃₂_lb hℓ₃₂_ub hℓ₂₁_lb hℓ₂₁_ub h_ge'
    rw [h_comm₂']
  }


lemma quotSubgraphTripleDensity_comm
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    (h : ℓ₁ + ℓ₂ + ℓ₃ ≤ ℓ)
    : quotSubgraphTripleDensity H₁ H₂ H₃ G = quotSubgraphTripleDensity H₂ H₃ H₁ G
  := by
  dsimp [quotSubgraphTripleDensity]

  have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₂ H₃ F = quotSubgraphPairDensity H₃ H₂ F := by
    intro F
    rw [quotSubgraphPairDensity_comm H₂ H₃ F]
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity H₁ F G
    := by
    simp [h]
  rw [h_LHS]

  have h' : ∀ (F : QuotSimpleGraph (Fin (ℓ₃ + ℓ₁))),
              quotSubgraphPairDensity H₃ H₁ F * quotSubgraphPairDensity H₂ F G
              = quotSubgraphPairDensity H₁ H₃ F * quotSubgraphPairDensity F H₂ G
    := by
    intro F
    rw [quotSubgraphPairDensity_comm H₃ H₁ F, quotSubgraphPairDensity_comm H₂ F G]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₃ + ℓ₁))), quotSubgraphPairDensity H₃ H₁ F * quotSubgraphPairDensity H₂ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₃ + ℓ₁))), quotSubgraphPairDensity H₁ H₃ F * quotSubgraphPairDensity F H₂ G
    := by
    simp [h']
  rw [h_RHS]

  let ℓ₁₃ := ℓ₃ + ℓ₁
  let ℓ₃₂ := ℓ₂ + ℓ₃
  have hℓ₁₃_lb : ℓ₁ + ℓ₃ ≤ ℓ₁₃ := by dsimp [ℓ₁₃]; linarith [h]
  have hℓ₁₃_ub : ℓ₁₃ + ℓ₂ ≤ ℓ := by dsimp [ℓ₁₃]; linarith [h]
  have hℓ₃₂_lb : ℓ₃ + ℓ₂ ≤ ℓ₃₂ := by dsimp [ℓ₃₂]; linarith [h]
  have hℓ₃₂_ub : ℓ₁ + ℓ₃₂ ≤ ℓ := by dsimp [ℓ₃₂]; linarith [h]
  rw [quotSubgraphPairDensity_sum_assoc H₁ H₃ H₂ G hℓ₁₃_lb hℓ₁₃_ub hℓ₃₂_lb hℓ₃₂_ub]


theorem quotSubgraphTripleDensity_eq_sum_density_prods
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₄ : ℕ} (hℓ₄_lb : ℓ₁ + ℓ₂ ≤ ℓ₄) (hℓ₄_ub : ℓ₄ + ℓ₃ ≤ ℓ)
    : quotSubgraphTripleDensity H₁ H₂ H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₄)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
  := by
  rw [quotSubgraphTripleDensity_comm H₁ H₂ H₃ G (by linarith [hℓ₄_lb, hℓ₄_ub])]
  rw [quotSubgraphTripleDensity_comm H₂ H₃ H₁ G (by linarith [hℓ₄_lb, hℓ₄_ub])]
  dsimp [quotSubgraphTripleDensity]

  have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₃ F G = quotSubgraphPairDensity F H₃ G := by
    intro F
    rw [quotSubgraphPairDensity_comm H₃ F G]
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity H₃ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
    := by
    simp [h]
  rw [h_LHS]

  let ℓ₁₂ := ℓ₁ + ℓ₂
  have hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂ := by simp only [le_refl, ℓ₁₂]
  have hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ := by dsimp [ℓ₁₂]; linarith [hℓ₄_lb, hℓ₄_ub]
  let ℓ₂₃ := ℓ₂ + ℓ₃
  have hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃ := by simp only [le_refl, ℓ₂₃]
  have hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ := by dsimp [ℓ₂₃]; linarith [hℓ₄_lb, hℓ₄_ub]
  rw [quotSubgraphPairDensity_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub]
  rw [quotSubgraphPairDensity_sum_assoc H₁ H₂ H₃ G hℓ₄_lb hℓ₄_ub hℓ₂₃_lb hℓ₂₃_ub]


theorem quotSubgraphPairDensity_eq_sum_density_prods'
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₃ : ℕ} (hℓ₃_lb : ℓ₁ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ + ℓ₂ ≤ ℓ)
    : quotSubgraphPairDensity H₁ H₂ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphDensity H₁ F * quotSubgraphPairDensity F H₂ G
  := by
  let H₀ : QuotSimpleGraph (Fin 0) := ⟦emptyGraph (Fin 0)⟧
  let h_lb : 0 + ℓ₁ ≤ ℓ₃ := by simp only [zero_add, hℓ₃_lb]

  have h_lb' : ℓ₁ + ℓ₂ ≤ ℓ := by linarith [hℓ₃_lb, hℓ₃_ub]
  have h_LHS : quotSubgraphTripleDensity H₀ H₁ H₂ G = quotSubgraphPairDensity H₁ H₂ G :=
    quotSubgraphTripleDensity_empty H₁ H₂ G h_lb'
  rw [←h_LHS]

  have h : ∀ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphPairDensity H₀ H₁ F = quotSubgraphDensity H₁ F := by
    intro F
    rw [quotSubgraphPairDensity_empty H₁ F]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphDensity H₁ F * quotSubgraphPairDensity F H₂ G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphPairDensity H₀ H₁ F * quotSubgraphPairDensity F H₂ G := by
    simp [h]
  rw [h_RHS]

  exact quotSubgraphTripleDensity_eq_sum_density_prods H₀ H₁ H₂ G h_lb hℓ₃_ub


alias density_chain_rule := quotSubgraphPairDensity_eq_sum_density_prods
alias density_chain_rule' := quotSubgraphPairDensity_eq_sum_density_prods'
alias density_chain_rule'' := quotSubgraphTripleDensity_eq_sum_density_prods
alias density_chain_rule''' := quotSubgraphDensity_eq_sum_density_prods
