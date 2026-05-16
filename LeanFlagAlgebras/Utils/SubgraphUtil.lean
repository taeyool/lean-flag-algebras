import «LeanFlagAlgebras».Utils.Combinations
import «LeanFlagAlgebras».Utils.QuotientGraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.BigOperators.Field

open Finset
open SimpleGraph
open Classical

variable {T U V W X : Type}
variable [Fintype T] [Fintype U] [Fintype V] [Fintype W] [Fintype X]

noncomputable instance subgraphFintype (G : SimpleGraph V) : Fintype (Subgraph G)
  :=
  let f : Subgraph G → Set V × Set (V × V) :=
    fun G' => (G'.verts, { (u, v) | G'.Adj u v })
  have f_inj : Function.Injective f := by
    intro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.verts = G2.verts := (Prod.ext_iff.mp h_eq).1
      exact (congrFun h_eq_verts u).to_iff
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact (congrFun h_eq_edges (u, v)).to_iff
  Fintype.ofInjective f f_inj

noncomputable instance qualifiedSubgraphFintype
    (G : SimpleGraph V) (p : Subgraph G → Prop)
    : Fintype { G₁ : Subgraph G | p G₁ } :=
  have : Fintype (Subgraph G) := subgraphFintype G
  inferInstance

noncomputable instance subgraphPairFintype
    (G : SimpleGraph V) : Fintype (Subgraph G × Subgraph G)
  :=
  have : Fintype (Subgraph G) := subgraphFintype G
  inferInstance

noncomputable instance qualifiedSubgraphPairFintype
    (G : SimpleGraph V) (p : Subgraph G × Subgraph G → Prop)
    : Fintype {⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} :=
  have : Fintype (Subgraph G × Subgraph G) := subgraphPairFintype G
  inferInstance

noncomputable instance qualifiedSubgraphPairProdSubgraphFintype
    (G : SimpleGraph V) (p : Subgraph G × Subgraph G → Prop)
    : Fintype ({⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} × Subgraph G) :=
  have : Fintype {⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} := qualifiedSubgraphPairFintype G p
  have : Fintype (Subgraph G) := subgraphFintype G
  inferInstance

noncomputable instance doublyQualifiedSubgraphPairProdSubgraphFintype
    (G : SimpleGraph V) (p : Subgraph G × Subgraph G → Prop) (q : Subgraph G × Subgraph G × Subgraph G → Prop)
    : Fintype {⟨⟨⟨G₁,G₂⟩,_⟩, G₃⟩ : {⟨G',G''⟩ : Subgraph G × Subgraph G | p ⟨G',G''⟩} × Subgraph G | q ⟨G₁,G₂,G₃⟩}
  :=
  have : Fintype ({⟨G₁,G₂⟩ : Subgraph G × Subgraph G | p ⟨G₁,G₂⟩} × Subgraph G) := qualifiedSubgraphPairProdSubgraphFintype G p
  inferInstance

def relOfSubgraph
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (H₀ : Subgraph G₀) (H₁ : Subgraph G₁) : Prop
  :=
  H₁.verts = φ '' H₀.verts
  ∧ ∀ (u v : V), H₁.Adj (φ u) (φ v) ↔ H₀.Adj u v

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

omit [Fintype V] [Fintype W] [Fintype U] in
lemma predIsoH_related
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : relOfPredOnSubgraph φ (predIsoH H G₀) (predIsoH H G₁)
  := by
  dsimp [relOfPredOnSubgraph, predIsoH, relOfSubgraph]
  rintro H₀ H₁ ⟨h_vert, h_adj⟩
  constructor
  . rintro ⟨f₀, _⟩
    let f₁ (w : H₁.verts) : U := f₀ (H₀.vert (φ.symm ↑w) (by
      obtain ⟨_, h⟩ := w
      obtain ⟨_, h₀, rfl⟩ := h_vert ▸ h
      simp only [h₀, RelIso.symm_apply_apply]))
    have h_bij₁ : Function.Bijective f₁ := by
      dsimp [Function.Bijective, f₁]
      constructor
      . intro w₀ w₁ h_eq
        simp_all only [Subgraph.coe_adj, Subtype.forall, EmbeddingLike.apply_eq_iff_eq,
          Subtype.mk.injEq]
        obtain ⟨_, _⟩ := w₀
        congr
      . intro u
        use H₁.vert (φ (f₀.symm u)) (by simp [h_vert])
        simp only [RelIso.symm_apply_apply, Subtype.coe_eta, Equiv.apply_symm_apply]
    have h_iso₁ : ∀ {w₀ w₁ : H₁.verts}, H.Adj (f₁ w₀) (f₁ w₁) ↔ H₁.Adj w₀ w₁ := by
      intro w₀ w₁; dsimp [f₁]
      simp_all only [Subgraph.coe_adj]
      obtain ⟨_, property₀⟩ := w₀
      obtain ⟨_, property₁⟩ := w₁
      rw [h_vert] at property₀ property₁
      obtain ⟨_, _, rfl⟩ := property₀
      obtain ⟨_, _, rfl⟩ := property₁
      simp_all only [RelIso.symm_apply_apply]
    exact ⟨Equiv.ofBijective f₁ h_bij₁, h_iso₁⟩
  . rintro ⟨f₁, h_iso₁⟩
    have h_vert_inv : φ.symm '' H₁.verts = H₀.verts := by
      ext1 x
      simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
    let f₀ (v : H₀.verts) : U := f₁ (H₁.vert (φ ↑v) (by aesop))
    have h_bij₀ : Function.Bijective f₀ := by
      dsimp [Function.Bijective, f₀]
      constructor
      . intro v₀ v₁ h_eq
        simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at h_eq
        obtain ⟨_, _⟩ := v₀
        congr
      . intro u
        use H₀.vert (φ.symm (f₁.symm u)) <| by rw [←h_vert_inv]; simp
        simp only [RelIso.apply_symm_apply, Subtype.coe_eta, Equiv.apply_symm_apply]
    have h_iso₀ : ∀ {v₀ v₁ : H₀.verts}, H.Adj (f₀ v₀) (f₀ v₁) ↔ H₀.Adj v₀ v₁ := by
      intro v₀ v₁
      dsimp [f₀]
      rw [←h_adj v₀ v₁, h_iso₁]
      simp_all only [Subgraph.coe_adj, Subtype.forall, Set.mem_image, forall_exists_index, f₀]
    exact ⟨Equiv.ofBijective f₀ h_bij₀, h_iso₀⟩

def inducedSubgraph
    (G : SimpleGraph V) (S : Set V) : G.Subgraph where
  verts := S
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  adj_sub a := a.1
  edge_vert a := a.2.1
  symm _ _ h := ⟨G.symm h.1, h.2.2, h.2.1⟩

omit [Fintype V] in
@[simp]
lemma inducedSubgraph_isInduced
    (G : SimpleGraph V) (S : Set V)
    : (inducedSubgraph G S).IsInduced
  := by
  intro u v h_u h_v h_adj
  simp only [inducedSubgraph] at *
  (repeat' constructor) <;> assumption

omit [Fintype V] in
@[simp]
lemma inducedSubgraph_verts
    (G : SimpleGraph V) (S : Set V) : (inducedSubgraph G S).verts = S
  := by
  simp [inducedSubgraph]

omit [Fintype V] in
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
    exact h_G₁_ind h_u_G₁ h_v_G₁ <| G₀.adj_sub h_uv_G₀

omit [Fintype V] in
lemma inducedSubgraph_eq
    {G : SimpleGraph V} {G₀ : Subgraph G}
    (h_G₀_ind : G₀.IsInduced) : G₀ = (inducedSubgraph G G₀.verts)
  := by
  dsimp [inducedSubgraph]
  ext u v
  . rfl
  . constructor
    . intro h_uv_G₀
      have h_u_G₀ : u ∈ G₀.verts := G₀.edge_vert h_uv_G₀
      have h_v_G₀ : v ∈ G₀.verts := G₀.edge_vert (G₀.symm h_uv_G₀)
      have h_uv_G : G.Adj u v := G₀.adj_sub h_uv_G₀
      exact ⟨h_uv_G, h_u_G₀, h_v_G₀⟩
    . intro ⟨h_uv_G, h_u_G₀, h_v_G₀⟩
      exact h_G₀_ind h_u_G₀ h_v_G₀ h_uv_G

omit [Fintype V] in
lemma inducedSubgraph_eq_verts
    {G : SimpleGraph V}
    {G₁ : Subgraph G} (hG₁ : G₁.IsInduced)
    {G₂ : Subgraph G} (hG₂ : G₂.IsInduced)
    (h : G₁.verts = G₂.verts) :
    G₁ = G₂ := by
  rw [inducedSubgraph_eq hG₁, inducedSubgraph_eq hG₂, h]

omit [Fintype V] [Fintype W] in
lemma inducedSubgraph_related
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (H₀ : Subgraph G₀) (h_ind₀ : H₀.IsInduced)
    : relOfSubgraph φ H₀ (inducedSubgraph G₁ (φ '' H₀.verts))
  := by
  dsimp [relOfSubgraph, inducedSubgraph]; simp
  intro u v
  constructor
  . rintro ⟨h_uv, h_u, h_v⟩
    exact h_ind₀ h_u h_v <| φ.map_adj_iff.mp h_uv
  . intro h_uv_H₀
    have h_uv_G₀ : G₀.Adj u v := H₀.adj_sub h_uv_H₀
    have h_u_H₀ : u ∈ H₀.verts := H₀.edge_vert h_uv_H₀
    have h_v_H₀ : v ∈ H₀.verts := H₀.edge_vert (H₀.symm h_uv_H₀)
    exact ⟨φ.map_adj_iff.mpr h_uv_G₀, h_u_H₀, h_v_H₀⟩

omit [Fintype V] [Fintype W] in
lemma inducedSubgraph_pred_iff
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁)
    (p₀ : Subgraph G₀ → Prop) (p₁ : Subgraph G₁ → Prop) (h_rel : relOfPredOnSubgraph φ p₀ p₁)
    (H₀ : Subgraph G₀) (h_ind₀ : H₀.IsInduced)
    : p₀ H₀ ↔ p₁ (inducedSubgraph G₁ (φ '' H₀.verts))
  := by
  have h_rel' := h_rel H₀ (inducedSubgraph G₁ (φ '' H₀.verts))
  exact h_rel' (inducedSubgraph_related φ H₀ h_ind₀)

omit [Fintype V] [Fintype W] [Fintype U] in
lemma inducedSubgraph_predIsoH_iff
    {G₀ : SimpleGraph V} {G₁ : SimpleGraph W} (φ : G₀ ≃g G₁) (H : SimpleGraph U)
    : ∀ (H₀ : Subgraph G₀),
        H₀.IsInduced → (predIsoH H G₀ H₀ ↔ predIsoH H G₁ (inducedSubgraph G₁ (φ '' H₀.verts)))
  :=
  inducedSubgraph_pred_iff φ (predIsoH H G₀) (predIsoH H G₁) (predIsoH_related φ H)

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
    let H₁ := inducedSubgraph G₁ (φ '' H₀.verts)
    have h_ind₁ : H₁.IsInduced := inducedSubgraph_isInduced G₁ (φ '' H₀.verts)
    have : relOfSubgraph φ H₀ H₁ := inducedSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let H₀ := inducedSubgraph G₀ (φ.symm '' H₁.verts)
    have h_ind₀ : H₀.IsInduced := inducedSubgraph_isInduced G₀ (φ.symm '' H₁.verts)
    have : relOfSubgraph φ.symm H₁ H₀ := inducedSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv, inducedSubgraph]
      ext u v
      . simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
      . simp only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]
        constructor
        . rintro ⟨h_uv, h_u, h_v⟩
          apply h_ind₀ <;> simp_all only
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
          apply h_ind₁ <;> simp_all only
        . rintro h_uv
          exact ⟨H₁.adj_sub h_uv, H₁.edge_vert h_uv, H₁.edge_vert (H₁.symm h_uv)⟩
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

@[simp]
lemma induced_disjoint_iff_image_disjoint
    {V : Type*} {G : SimpleGraph V} {W : Type*} {G' : SimpleGraph W} (φ : G ≃g G')
    (G₁ : Subgraph G) (G₂ : Subgraph G)
    : Disjoint (φ '' G₁.verts) (φ '' G₂.verts) ↔ Disjoint G₁.verts G₂.verts
  := Set.disjoint_image_iff φ.injective

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
    let H₁ := inducedSubgraph G₁ (φ '' H₀.verts)
    have h_ind₁ : H₁.IsInduced := inducedSubgraph_isInduced G₁ (φ '' H₀.verts)
    have : relOfSubgraph φ H₀ H₁ := inducedSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    let H₃ := inducedSubgraph G₁ (φ '' H₂.verts)
    have h_ind₃ : H₃.IsInduced := inducedSubgraph_isInduced G₁ (φ '' H₂.verts)
    have : relOfSubgraph φ H₂ H₃ := inducedSubgraph_related φ H₂ h_ind₂
    have h_p₃ : p₃ H₃ := (h_rel' H₂ H₃ this).mp h_p₂
    have h_inter' : H₁.verts ∩ H₃.verts = ∅ := by
      rw [(inducedSubgraph_related φ H₀ h_ind₀).1, (inducedSubgraph_related φ H₂ h_ind₂).1]
      have h := induced_disjoint_iff_image_disjoint φ H₀ H₂
      repeat rw [Set.disjoint_iff_inter_eq_empty] at h
      exact h.mpr h_inter
    exact ⟨⟨H₁, H₃⟩, ⟨h_ind₁, h_p₁, h_ind₃, h_p₃, h_inter'⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨⟨H₁,H₃⟩, ⟨h_ind₁, h_p₁, h_ind₃, h_p₃, h_inter⟩⟩ := s₁
    let H₀ := inducedSubgraph G₀ (φ.symm '' H₁.verts)
    have h_ind₀ : H₀.IsInduced := inducedSubgraph_isInduced G₀ (φ.symm '' H₁.verts)
    have : relOfSubgraph φ.symm H₁ H₀ := inducedSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    let H₂ := inducedSubgraph G₀ (φ.symm '' H₃.verts)
    have h_ind₂ : H₂.IsInduced := inducedSubgraph_isInduced G₀ (φ.symm '' H₃.verts)
    have : relOfSubgraph φ.symm H₃ H₂ := inducedSubgraph_related φ.symm H₃ h_ind₃
    have h_p₂ : p₂ H₂ := (h_rel_inv' H₃ H₂ this).mp h_p₃
    have h_inter' : H₀.verts ∩ H₂.verts = ∅ := by
      rw [(inducedSubgraph_related φ.symm H₁ h_ind₁).1, (inducedSubgraph_related φ.symm H₃ h_ind₃).1]
      have h := induced_disjoint_iff_image_disjoint φ.symm H₁ H₃
      repeat rw [Set.disjoint_iff_inter_eq_empty] at h
      exact h.mpr h_inter
    exact ⟨⟨H₀, H₂⟩, ⟨h_ind₀, h_p₀, h_ind₂, h_p₂, h_inter'⟩⟩
  let f_bij : Function.Bijective f := by
    refine Function.bijective_iff_has_inverse.mpr ⟨f_inv, ?_, ?_⟩ <;>
    rintro ⟨⟨H₀, H₁⟩, h_ind₀, h_p₀, h_ind₁, h_p₁, h_inter⟩ <;>
    dsimp [f, f_inv, inducedSubgraph] <;>
    ext u v <;>
    simp_all only [Set.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right] <;>
    constructor
    any_goals simp_all only [and_imp, RelIso.apply_symm_apply, exists_eq_right, implies_true]
    any_goals intro _ _ _
    any_goals apply h_ind₀
    any_goals apply h_ind₁
    any_goals simp_all only
    all_goals intro h_uv
    any_goals exact ⟨H₀.adj_sub h_uv, H₀.edge_vert h_uv, H₀.edge_vert (H₀.symm h_uv)⟩
    all_goals exact ⟨H₁.adj_sub h_uv, H₁.edge_vert h_uv, H₁.edge_vert (H₁.symm h_uv)⟩
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
  have h : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g H₀) ↔ Nonempty (Subgraph.coe G' ≃g H₁) := by
    intro G'
    constructor <;> rintro ⟨h_iso⟩ <;> refine Nonempty.intro ?_
    · exact φ.comp h_iso
    . exact φ.symm.comp h_iso
  exact Equiv.setCongr <| Set.sep_ext_iff.mpr fun x _ ↦ h x

lemma subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0
    {G : SimpleGraph V} {H : Subgraph G}
    : H = ⊥ ↔ Nonempty (H.coe ≃g (emptyGraph (Fin 0)))
  := by
  constructor
  . intro h_eq
    rw [h_eq]
    let f_iso : (⊥ : Subgraph G).verts ≃ Fin 0 := Fintype.equivFinOfCardEq (by simp)
    exact Nonempty.intro ⟨f_iso, by simp⟩
  . intro h_iso
    have h_verts : H.verts = ∅ := by
      ext u
      constructor
      . intro h_u
        exact Fin.elim0 (h_iso.some ⟨u, h_u⟩)
      . exact False.elim
    simp_all [Subgraph.ext_iff, Set.ext_iff]
    ext u v
    simp only [Subgraph.not_bot_adj, iff_false]
    intro h_uv
    exact h_verts u (H.edge_vert h_uv)

lemma iso_subset_of_finset_is_full
    {S : Set V} (f_iso : V ≃ ↑S) (u : V) : u ∈ S
  := by
  by_contra h_contra
  have h_card : Fintype.card S < Fintype.card V :=
    Fintype.card_subtype_lt h_contra
  have h_card' : Fintype.card V = Fintype.card S :=
    Fintype.card_congr f_iso
  omega

lemma induced_full_subgraph_eq_top
    {G₀ G₁ : SimpleGraph V} {G' : Subgraph G₀}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃g G₁) → G' = ⊤
  := by
  intro ⟨h,f_iso⟩
  let f_iso_vertex : V ≃ ↑G'.verts := f_iso.some.toEquiv.symm
  ext u v <;>
  have h_u := iso_subset_of_finset_is_full f_iso_vertex u
  . simp_all
  . have h_v := iso_subset_of_finset_is_full f_iso_vertex v
    constructor
    . exact G'.adj_sub
    . exact h h_u h_v

lemma induced_subgraph_iso_G_iff_eq_top
    {G : SimpleGraph V} {G' : Subgraph G}
    : G'.IsInduced ∧ Nonempty (G'.coe ≃g G) ↔ G' = ⊤
  := by
  constructor
  . exact induced_full_subgraph_eq_top
  · intro h
    constructor
    · subst h; intro; simp
    · rw [h]; exact Nonempty.intro SimpleGraph.Subgraph.topIso

omit [Fintype V] [Fintype W] [Fintype X] in
lemma subgraph_to_eqv_graph_iff
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph W} (φ : H₀ ≃g H₁) (G : SimpleGraph X)
    : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g H₀) ↔ Nonempty (Subgraph.coe G' ≃g H₁)
  := by
  intro G'
  constructor <;> refine fun ⟨h_iso⟩ ↦ Nonempty.intro ?_
  · exact φ.comp h_iso
  · exact φ.symm.comp h_iso

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
  have h_S : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g S₀) ↔ Nonempty (Subgraph.coe G' ≃g S₁) :=
    subgraph_to_eqv_graph_iff ψ G
  have h_H : ∀ G' : Subgraph G, Nonempty (Subgraph.coe G' ≃g H₀) ↔ Nonempty (Subgraph.coe G' ≃g H₁) :=
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
    constructor <;> intro ⟨h₁, h₂, h₃, h₄, h₅⟩
    · exact ⟨h₁, (h_S x.1).mp h₂, h₃, (h_H x.2).mp h₄, h₅⟩
    · exact ⟨h₁, (h_S x.1).mpr h₂, h₃, (h_H x.2).mpr h₄, h₅⟩
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
      exact ⟨G₀.edge_vert h_uv, RelIso.apply_symm_apply iso u⟩
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
      have : iso u ∈ H₀.verts := by dsimp [H₀, subgraphFromIso]; simp only [Set.mem_image,
        EmbeddingLike.apply_eq_iff_eq, exists_eq_right, Subtype.coe_prop]
      ⟨iso u, this⟩
    invFun := fun u =>
      have h_symm_u : iso.symm u ∈ iso.symm '' (iso '' G₀.verts) :=
        Set.mem_image_of_mem iso.symm u.property
      have : iso.symm u ∈ G₀.verts := by
        rw [← Set.image_comp] at h_symm_u
        simp only [Function.comp_apply, RelIso.symm_apply_apply, Set.image_id'] at h_symm_u
        exact h_symm_u
      ⟨iso.symm u, this⟩
    left_inv := by
      intro; simp only [RelIso.symm_apply_apply, Subtype.coe_eta]
    right_inv := by
      intro; simp only [RelIso.apply_symm_apply, Subtype.coe_eta]
    map_rel_iff' := by
      intro u v; dsimp [subgraphFromIso]; simp only [RelIso.symm_apply_apply]
  }

omit [Fintype V] [Fintype W] in
lemma subgraphFromIso_preserve_inducedness
    {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) (G₀ : Subgraph G) (h_ind_G₀ : G₀.IsInduced)
    : (subgraphFromIso iso G₀).IsInduced
  := by
  dsimp [Subgraph.IsInduced, subgraphFromIso] at *
  intro u h_u_H v h_v_H h_uv_H
  let h : ∀ {w : W}, (w ∈ iso '' G₀.verts) → (iso.symm w ∈ G₀.verts) := by
    intro w h_w
    obtain ⟨u', h_u', rfl⟩ := h_w
    rw [RelIso.symm_apply_apply]
    exact h_u'
  exact h_ind_G₀ (h h_u_H) (h h_v_H) <| (Iso.map_adj_iff iso.symm).mpr h_uv_H

omit [Fintype V] [Fintype W] in
lemma subgraphFromIso_preserve_disjointedness
    {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (G₀ G₁ : Subgraph G) (h_disj : G₀.verts ∩ G₁.verts = ∅)
    : (subgraphFromIso iso G₀).verts ∩ (subgraphFromIso iso G₁).verts = ∅
  := by
  dsimp [subgraphFromIso]
  apply Set.eq_empty_of_subset_empty
  rintro u ⟨h_u_G₀, h_u_G₁⟩
  have h_iso₀ : iso.symm u ∈ iso.symm '' (iso '' G₀.verts) := Set.mem_image_of_mem iso.symm h_u_G₀
  have h_iso₁ : iso.symm u ∈ iso.symm '' (iso '' G₁.verts) := Set.mem_image_of_mem iso.symm h_u_G₁
  have h_iso₀' : iso.symm u ∈ G₀.verts := by rw [← Set.image_comp] at h_iso₀; simp only [Function.comp_apply, RelIso.symm_apply_apply, Set.image_id'] at h_iso₀; exact h_iso₀
  have h_iso₁' : iso.symm u ∈ G₁.verts := by rw [← Set.image_comp] at h_iso₁; simp only [Function.comp_apply, RelIso.symm_apply_apply, Set.image_id'] at h_iso₁; exact h_iso₁
  exact (h_disj ▸ Set.mem_inter h_iso₀' h_iso₁').elim

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
      intro u v; dsimp [G₀', subgraphFromOrder]; simp only
  }

omit [Fintype V] [Fintype W] in
lemma subgraphFromOrder_preserve_inducedness
    {G : SimpleGraph V} {G₀ G₁ : Subgraph G} (h_order : G₀ ≤ G₁)
    : G₀.IsInduced → (subgraphFromOrder h_order).IsInduced
  := by
  intro h_ind_G₀
  dsimp [Subgraph.IsInduced, subgraphFromOrder] at *
  intro u h_u_G₀ v h_v_G₀ h_uv_G₁
  exact h_ind_G₀ h_u_G₀ h_v_G₀ (G₁.adj_sub h_uv_G₁)

omit [Fintype V] [Fintype W] in
lemma subgraphFromOrder_preserve_disjointedness
    {G : SimpleGraph V} {G₀ G₁ G₂ : Subgraph G}
    (h_order_G₁ : G₁ ≤ G₀) (h_order_G₂ : G₂ ≤ G₀) (h_disj : G₁.verts ∩ G₂.verts = ∅)
    : (subgraphFromOrder h_order_G₁).verts ∩ (subgraphFromOrder h_order_G₂).verts = ∅
  := by
  dsimp [subgraphFromOrder]
  apply Set.eq_empty_of_subset_empty
  rintro ⟨u, h_u_G₀⟩ h_u_G₁_G₂
  have : u ∈ G₁.verts ∩ G₂.verts := h_u_G₁_G₂
  exact (Set.notMem_empty _ (h_disj ▸ this)).elim

def subgraphByComposition
    {G : SimpleGraph V} (G₀ : Subgraph G) (G₁ : Subgraph G₀.coe)
    :  Subgraph G
  :=
  SimpleGraph.Subgraph.coeSubgraph G₁

def isoToSubgraphByComposition
    {G : SimpleGraph V} (G₀ : Subgraph G) (G₁ : Subgraph G₀.coe)
    :  G₁.coe ≃g (subgraphByComposition G₀ G₁).coe
  where
    toFun := fun u =>
      Set.imageFactorization Subtype.val G₁.verts u
    invFun := by
      intro ⟨u, h_u⟩
      simp [subgraphByComposition] at h_u
      exact ⟨⟨u, h_u.1⟩, h_u.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ by rfl
    map_rel_iff' := by
      rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
      dsimp [subgraphByComposition, Relation.Map]
      simp only [Subtype.exists, exists_and_right, exists_eq_right_right, exists_eq_right]
      refine ⟨fun ⟨_, _, h⟩ ↦h, fun h ↦ ⟨by assumption, by assumption, h⟩⟩

omit [Fintype V] in
lemma subgraphByComposition_le
    {G : SimpleGraph V} (G₀ : Subgraph G) (G₁ : Subgraph G₀.coe)
    : subgraphByComposition G₀ G₁ ≤ G₀
  :=
  G₀.coeSubgraph_le G₁

lemma inducedSubgraph_eq_subgraphByComposition
    {G : SimpleGraph V} (G₀ : Subgraph G) (h_G₀_ind : G₀.IsInduced)
    (X₁ : Finset V) (h_X₁ : X₁ ⊆ G₀.verts.toFinset)
    : inducedSubgraph G X₁
      =
      subgraphByComposition G₀ (inducedSubgraph G₀.coe {v : G₀.verts | v.val ∈ X₁})
  := by
    dsimp [subgraphByComposition, Subgraph.coeSubgraph, inducedSubgraph]
    ext u v
    all_goals simp only [mem_coe, Subgraph.map_verts, Subgraph.hom_apply, Set.mem_image,
      Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop', nonempty_prop,
      exists_eq_right_right, iff_self_and, Subgraph.map_adj, Relation.Map]
    · intro h_u_X₁
      exact Set.mem_toFinset.mp (h_X₁ h_u_X₁)
    . constructor
      . intro ⟨h_u_v, h_u_X₁, h_v_X₁⟩
        refine ⟨u, Set.mem_toFinset.mp (h_X₁ h_u_X₁), v, ?_⟩
        have h_u_G₀ : u ∈ G₀.verts := Set.mem_toFinset.mp (h_X₁ h_u_X₁)
        have h_v_G₀ : v ∈ G₀.verts := Set.mem_toFinset.mp (h_X₁ h_v_X₁)
        simp only [h_u_X₁, h_v_X₁, and_self, and_true, h_v_G₀]
        exact h_G₀_ind h_u_G₀ h_v_G₀ h_u_v
      . rintro ⟨a, _, b, ⟨h_G₀_adj_a_b, h_a_X₁, h_b_X₁⟩, h_a_u, _, h_b_v⟩
        rw [←h_a_u, ←h_b_v]
        exact ⟨G₀.adj_sub h_G₀_adj_a_b, h_a_X₁, h_b_X₁⟩

def subgraphFromPartialIso
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ : Subgraph G₀) : Subgraph H
  :=
  subgraphByComposition H₀ (subgraphFromIso iso G₁)

def isoToSubgraphFromPartialIso
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ : Subgraph G₀)
    : G₁.coe ≃g (subgraphFromPartialIso iso G₁).coe
  :=
  let H₁_pre := subgraphFromIso iso G₁
  let h_iso_pre := isoToSubgraphFromIso iso G₁
  let h_iso_post := isoToSubgraphByComposition H₀ H₁_pre
  h_iso_post.comp h_iso_pre

omit [Fintype V] [Fintype W] in
lemma subgraphFromPartialIso_le
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ : Subgraph G₀)
    : subgraphFromPartialIso iso G₁ ≤ H₀
  := by
  simp [subgraphFromPartialIso, subgraphByComposition_le]

omit [Fintype V] [Fintype W] in
lemma subgraphFromPartialIso_preserve_inducedness
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ : Subgraph G₀)
    (h_ind_H₀ : H₀.IsInduced) (h_ind_G₁ : G₁.IsInduced)
    : (subgraphFromPartialIso iso G₁).IsInduced
  := by
  dsimp [Subgraph.IsInduced] at *
  intro u h_u_H₁ v h_v_H₁ h_uv_H
  dsimp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso, Relation.Map] at *
  simp at *
  obtain ⟨u₀, h_u₀_G₁_verts, rfl⟩ := h_u_H₁
  obtain ⟨v₀, h_v₀_G₁_verts, rfl⟩ := h_v_H₁
  have h_u₀v₀_G₀ : G₀.Adj u₀ v₀ := by
    rw [← iso.map_adj_iff, H₀.coe_adj (iso u₀) (iso v₀)]
    refine h_ind_H₀ ?_ ?_ h_uv_H <;> exact Subtype.coe_prop _
  simp only [Subtype.coe_eta, RelIso.symm_apply_apply, Subtype.coe_prop, exists_const]
  exact h_ind_G₁ h_u₀_G₁_verts h_v₀_G₁_verts h_u₀v₀_G₀

omit [Fintype V] [Fintype W] in
lemma subgraphFromPartialIso_preserve_disjointedness
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ G₂ : Subgraph G₀) (h_disj : G₁.verts ∩ G₂.verts = ∅)
    : (subgraphFromPartialIso iso G₁).verts ∩ (subgraphFromPartialIso iso G₂).verts = ∅
  := by
  dsimp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso]
  apply Set.eq_empty_of_subset_empty
  intro u ⟨h_u_G₁, h_u_G₂⟩
  simp only [Set.mem_image, exists_exists_and_eq_and] at h_u_G₁ h_u_G₂
  obtain ⟨u₁, h_u₁_G₁_verts, h_u₁_u⟩ := h_u_G₁
  obtain ⟨u₂, h_u₂_G₂_verts, rfl⟩ := h_u_G₂
  have h_u₁_G₁_G₂ : u₁ ∈ G₁.verts ∩ G₂.verts := by
    have h_iso_u₁_eq_iso_u₂: (iso u₁) = (iso u₂) := SetCoe.ext h_u₁_u
    have : u₁ = u₂ :=
      calc
        u₁ = iso.symm (iso u₁) := Eq.symm (RelIso.symm_apply_apply iso u₁)
        _  = iso.symm (iso u₂) := by rw [h_iso_u₁_eq_iso_u₂]
        _  = u₂                := RelIso.symm_apply_apply iso u₂
    constructor <;> simp only [h_u₁_G₁_verts, this ▸ h_u₂_G₂_verts]
  exact (Set.notMem_empty _ (h_disj ▸ h_u₁_G₁_G₂)).elim

omit [Fintype W] in
lemma subgraphFromPartialIso_preserve_cover
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ G₂ : Subgraph G₀)
    (h_cover : G₁.verts ∪ G₂.verts = (univ : Finset V))
    : H₀.verts = (subgraphFromPartialIso iso G₁).verts ∪ (subgraphFromPartialIso iso G₂).verts
  := by
  dsimp [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso]
  ext u; simp
  constructor
  . intro h_u_H₀
    rcases (h_cover ▸ mem_univ _ : (iso.symm ⟨u,h_u_H₀⟩) ∈ G₁.verts ∪ G₂.verts) with h_u_G₁ | h_u_G₂
    · apply Or.inl
      use (iso.symm ⟨u, h_u_H₀⟩)
      exact ⟨h_u_G₁, by simp⟩
    · apply Or.inr
      use (iso.symm ⟨u, h_u_H₀⟩)
      exact ⟨h_u_G₂, by simp⟩
  . rintro (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> exact Subtype.coe_prop _

omit [Fintype W] in
lemma subgraphFromPartialIso_eq_inducedSubgraph
    {G₀ : SimpleGraph V} {H : SimpleGraph W} {H₀ : Subgraph H}
    (iso : G₀ ≃g H₀.coe) (G₁ : Subgraph G₀)
    (h_G₁_ind : G₁.IsInduced) (h_H₀_ind : H₀.IsInduced)
    : subgraphFromPartialIso iso G₁ = ↑(inducedSubgraph H ((Subtype.val ∘ iso) '' G₁.verts).toFinset)
  := by
    let H₁ := subgraphFromPartialIso iso G₁
    have h_H₁_vert_eq : H₁.verts = ((Subtype.val ∘ iso) '' G₁.verts).toFinset := by
      dsimp only [H₁]
      dsimp only [subgraphFromPartialIso, subgraphByComposition, subgraphFromIso]
      simp only [Subgraph.map_verts, Subgraph.hom_apply, Set.image_image,
          Function.comp_apply, Set.toFinset_image, coe_image,
          Set.coe_toFinset]
    have h_H₁_ind : H₁.IsInduced :=
        subgraphFromPartialIso_preserve_inducedness iso G₁ h_H₀_ind h_G₁_ind
    rw [←h_H₁_vert_eq, ←inducedSubgraph_eq h_H₁_ind]

noncomputable def getCanonicalQuotSimpleGraph
      (G : SimpleGraph V) (h_V_size : Fintype.card V = ℓ)
      : (F : QuotSimpleGraph (Fin ℓ)) × (F.out ≃g G)
  :=
  let f_iso : V ≃ Fin ℓ := Fintype.equivFinOfCardEq h_V_size
  let G' : SimpleGraph (Fin ℓ) := {
    Adj := fun u' v' => G.Adj (f_iso.symm u') (f_iso.symm v')
    symm := fun u' v' h_u'_v' ↦ G.symm h_u'_v'
    loopless := fun u' ↦ G.loopless (f_iso.symm u')
  }
  let φ : G' ≃g G := {
    toFun := f_iso.symm,
    invFun := f_iso,
    left_inv := by intro; rw [Equiv.apply_symm_apply]
    right_inv := by intro; rw [Equiv.symm_apply_apply]
    map_rel_iff' := by intro u' v'; dsimp [G']; rfl
  }
  let φ' : ⟦G'⟧.out ≃g G' := Nonempty.some ((@Quotient.eq_mk_iff_out _ _ ⟦G'⟧ G').mp rfl)
  ⟨⟦G'⟧, φ'.trans φ⟩

lemma getCanonicalQuotSimpleGraph_self
    (F : QuotSimpleGraph (Fin ℓ))
    : (getCanonicalQuotSimpleGraph F.out (Fintype.card_fin ℓ)).fst = F
  := by
  obtain ⟨F', h_iso⟩ := getCanonicalQuotSimpleGraph F.out (Fintype.card_fin ℓ)
  calc F'
    _  = ⟦F'.out⟧ := F'.out_eq.symm
    _  = ⟦F.out⟧  := Quotient.sound <| .intro h_iso
    _  = F := F.out_eq

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
    _  = ⟦H₀.out⟧ := H₀.out_eq.symm
    _  = ⟦H₁.out⟧ := Quotient.sound <| .intro h_iso_H₀_H₁
    _  = H₁ := H₁.out_eq

lemma subgraph_verts_card_from_iso_graph
    {G : SimpleGraph V} {G' : Subgraph G} {H : SimpleGraph (Fin ℓ)} (h_iso : G'.coe ≃g H)
    : Fintype.card G'.verts = ℓ
  :=
  Fintype.card_fin ℓ ▸ Fintype.card_congr h_iso

noncomputable def isoFromInducedSubgraphByPartialIso
    {F₀ : SimpleGraph U} {F₁ : Subgraph F₀} {G : SimpleGraph V} {G₀ : Subgraph G} {H₁ : SimpleGraph W}
    (iso_G₀_F₀ : Subgraph.coe G₀ ≃g F₀) (iso_F₁_H₁ : Subgraph.coe F₁ ≃g H₁)
    (h_F₁_ind : F₁.IsInduced) (h_G₀_ind : G₀.IsInduced)
    : (inducedSubgraph G ((Subtype.val ∘ iso_G₀_F₀.symm) '' F₁.verts).toFinset).coe ≃g H₁
  := by
    have : subgraphFromPartialIso iso_G₀_F₀.symm F₁
           = ↑(inducedSubgraph G ((Subtype.val ∘ iso_G₀_F₀.symm) '' F₁.verts).toFinset) :=
      subgraphFromPartialIso_eq_inducedSubgraph iso_G₀_F₀.symm F₁ h_F₁_ind h_G₀_ind
    rw [←this]
    let g₁ : F₁.coe ≃g (subgraphFromPartialIso iso_G₀_F₀.symm F₁).coe :=
      isoToSubgraphFromPartialIso iso_G₀_F₀.symm F₁
    exact g₁.symm.trans iso_F₁_H₁
