import «LeanFlagAlgebras».QuotientGraph
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Order.BooleanAlgebra
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Defs
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

omit [DecidableEq V] in
lemma inducedSubgraph_eq_subgraphByComposition
    {G : SimpleGraph V} (G₀ : Subgraph G) (h_G₀_ind : G₀.IsInduced)
    (X₁ : Finset V) (h_X₁ : X₁ ⊆ G₀.verts.toFinset)
    : (inducedSubgraph G X₁).val
      =
      subgraphByComposition G₀ (inducedSubgraph G₀.coe {v : G₀.verts | v.val ∈ X₁}).val
  := by
    dsimp [subgraphByComposition, Subgraph.coeSubgraph, inducedSubgraph]
    ext u v
    . simp only [mem_coe, Subgraph.map_verts, Subgraph.hom_apply, Set.mem_image,
                  Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop',
                  nonempty_prop, exists_eq_right_right, iff_self_and]
      intro h_u_X₁
      exact Set.mem_toFinset.mp (h_X₁ h_u_X₁)
    . simp only [mem_coe, Subgraph.map_adj, Relation.Map, Subgraph.hom_apply,
                  Subtype.exists, exists_and_left, exists_prop', nonempty_prop]
      constructor
      . intro ⟨h_u_v, h_u_X₁, h_v_X₁⟩
        use u
        constructor
        . exact Set.mem_toFinset.mp (h_X₁ h_u_X₁)
        . use v
          have h_u_G₀ : u ∈ G₀.verts := Set.mem_toFinset.mp (h_X₁ h_u_X₁)
          have h_v_G₀ : v ∈ G₀.verts := Set.mem_toFinset.mp (h_X₁ h_v_X₁)
          simp only [h_u_X₁, h_v_X₁, and_self, and_true, h_v_G₀]
          exact h_G₀_ind h_u_G₀ h_v_G₀ h_u_v
      . rintro ⟨a, _, b, ⟨h_G₀_adj_a_b, h_a_X₁, h_b_X₁⟩, h_a_u, _, h_b_v⟩
        rw [←h_a_u, ←h_b_v]
        exact ⟨G₀.adj_sub h_G₀_adj_a_b, h_a_X₁, h_b_X₁⟩

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

omit [DecidableEq V] [DecidableEq W] in
lemma subgraph_verts_card_from_iso_graph
    {G : SimpleGraph V} {G' : Subgraph G} {H : SimpleGraph (Fin ℓ)} (h_iso : G'.coe ≃g H)
    : Fintype.card G'.verts = ℓ
  := by
  rw [←Fintype.card_fin ℓ]
  exact Fintype.card_congr h_iso

noncomputable def isoFromInducedSubgraphByPartialIso
    {F₀ : SimpleGraph U} {F₁ : Subgraph F₀} {G : SimpleGraph V} {G₀ : Subgraph G} {H₁ : SimpleGraph W}
    (iso_G₀_F₀ : Subgraph.coe G₀ ≃g F₀) (iso_F₁_H₁ : Subgraph.coe F₁ ≃g H₁)
    (h_F₁_ind : F₁.IsInduced) (h_G₀_ind : G₀.IsInduced)
    : (inducedSubgraph G ((Subtype.val ∘ iso_G₀_F₀.symm) '' F₁.verts).toFinset).val.coe ≃g H₁
  := by
    let X₁ := ((Subtype.val ∘ iso_G₀_F₀.symm) '' F₁.verts).toFinset
    let G₁ := subgraphFromPartialIso iso_G₀_F₀.symm F₁
    let g₁ : F₁.coe ≃g G₁.coe := isoToSubgraphFromPartialIso iso_G₀_F₀.symm F₁
    have : G₁ = ↑(inducedSubgraph G ((Subtype.val ∘ iso_G₀_F₀.symm) '' F₁.verts).toFinset) := by
      have h_G₁_vert_eq_X₁ : G₁.verts = ((Subtype.val ∘ iso_G₀_F₀.symm) '' F₁.verts).toFinset := by
        dsimp only [X₁, G₁]
        dsimp only [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso]
        simp only [Subgraph.map_verts, Subgraph.hom_apply, Set.image_image,
          Function.Embedding.coeFn_mk, Function.comp_apply, Set.toFinset_image, coe_image,
          Set.coe_toFinset]
      have h_G₁_ind : G₁.IsInduced :=
        subgraphFromPartialIso_preserve_inducedness iso_G₀_F₀.symm F₁ h_G₀_ind h_F₁_ind
      rw [←h_G₁_vert_eq_X₁]
      rw [←inducedSubgraph_eq h_G₁_ind]
    rw [←this]
    exact g₁.symm.trans iso_F₁_H₁
