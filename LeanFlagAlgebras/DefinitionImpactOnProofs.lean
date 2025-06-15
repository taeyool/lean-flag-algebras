import «LeanFlagAlgebras».SubflagDensity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

open FlagAlgebras
open Classical

variable {T : Type} [Fintype T] [DecidableEq T] {σ : FlagType T}

variable {t : ℕ}
  {Vl : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl]
  {Vl' : Fin t → Type} [FintypeList Vl'] [DecidableEqList Vl']
  {V : Type} [Fintype V] [DecidableEq V]
  {W : Type} [Fintype W] [DecidableEq W]
  {U : Type} [Fintype U] [DecidableEq U]
  {U₁ : Type} [Fintype U₁] [DecidableEq U₁]
  {U₂ : Type} [Fintype U₂] [DecidableEq U₂]
  {U₃ : Type} [Fintype U₃] [DecidableEq U₃]

def labeledSubgraphListSet_ver_1
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
  : Set (∀ (_ : Fin t), LabeledSubgraph σ G) :=
  let ind (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (Gl i).IsInduced
  let p₁ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)
  -- main difference with ver_2
  let p₂ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅
  { Gl | ind Gl ∧ p₁ Gl ∧ p₂ Gl }

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma predIsoLabeledHl_related_indep_ver_1
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (Hl₁ : ∀ (_ : Fin t), LabeledSubgraph σ G₁)
    (v_rel :  ∀ (i : Fin t), (Hl₁ i).subgraph.verts = ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts)
    : ∀ (i j : Fin t), (((Hl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Hl₀ j).subgraph.verts \ G₀.type_verts) = ∅) →
      (((Hl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Hl₁ j).subgraph.verts \ G₁.type_verts) = ∅) := by
  intro i j h_empty
  by_contra h_nonempty
  push_neg at h_nonempty
  have h_nomempty_exists : ∃ w : W, w ∈ ((Hl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Hl₁ j).subgraph.verts \ G₁.type_verts) := h_nonempty
  obtain ⟨w, ⟨h_wi₁, h_wj₁⟩⟩ := h_nomempty_exists
  have h_w : ∀ (k : Fin t), w ∈ (Hl₁ k).subgraph.verts → φ.symm.graph_iso w ∈ (Hl₀ k).subgraph.verts := by
    intro k h_wk₁
    rw [v_rel k] at h_wk₁
    rw [Set.mem_image] at h_wk₁
    obtain ⟨w', ⟨h_wk₀, h_ww'⟩⟩ := h_wk₁
    rw [← h_ww']
    have := φ.graph_iso.left_inv' w'
    exact Set.mem_of_eq_of_mem this h_wk₀
  have h_w' : w ∉ G₁.type_verts → φ.symm.graph_iso w ∉ G₀.type_verts := by
    intro h_wk₁
    by_contra h_w'
    have : w ∈ G₁.type_verts := by
      have : ∃ t : T, φ.symm.graph_iso w = G₀.type_embed t := by
        unfold LabeledGraph.type_verts at h_w'
        obtain ⟨t, h_t⟩ := h_w'
        use t
        simp_all only [Set.mem_univ]
      obtain ⟨t, h_t⟩ := this
      rw [← φ.symm.type_preserve] at h_t
      simp at h_t
      rw [h_t]
      unfold LabeledGraph.type_verts
      exact Set.mem_image_of_mem (⇑G₁.type_embed) trivial
    exact h_wk₁ this
  have h_wi₀ : φ.symm.graph_iso w ∈ ((Hl₀ i).subgraph.verts \ G₀.type_verts) := Set.mem_diff_of_mem (h_w i h_wi₁.left) (h_w' h_wi₁.right)
  have h_wj₀ : φ.symm.graph_iso w ∈ ((Hl₀ j).subgraph.verts \ G₀.type_verts) := Set.mem_diff_of_mem (h_w j h_wj₁.left) (h_w' h_wj₁.right)
  have h_w_ij : φ.symm.graph_iso w ∈ ((Hl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Hl₀ j).subgraph.verts \ G₀.type_verts) := Set.mem_inter h_wi₀ h_wj₀
  simp_all only [Set.mem_empty_iff_false]

def labeledSubgraphListSet_ver_2
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
  : Set (∀ (_ : Fin t), LabeledSubgraph σ G) :=
  let ind (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (Gl i).IsInduced
  let p₁ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)
  -- main difference with ver_1
  let p₂ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = G.type_verts
  { Gl | ind Gl ∧ p₁ Gl ∧ p₂ Gl }

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma predIsoLabeledHl_related_indep_ver_2
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (Hl₁ : ∀ (_ : Fin t), LabeledSubgraph σ G₁)
    (v_rel :  ∀ (i : Fin t), (Hl₁ i).subgraph.verts = ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts)
    : ∀ (i j : Fin t), ((Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts = G₀.type_verts) →
      ((Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts = G₁.type_verts) := by
  intro i j h_vert₀
  ext u
  constructor
  · intro h_u
    obtain ⟨h_u1, h_u2⟩ := h_u
    have preimg_i : φ.graph_iso.symm u ∈ (Hl₀ i).subgraph.verts := by
      rw [v_rel i] at h_u1
      rw [Set.mem_image] at h_u1
      obtain ⟨v, hv_mem, hv_eq⟩ := h_u1
      rw [← hv_eq]
      exact Set.mem_of_eq_of_mem (φ.graph_iso.left_inv' v) hv_mem
    have preimg_j : φ.graph_iso.symm u ∈ (Hl₀ j).subgraph.verts := by
      rw [v_rel j] at h_u2
      rw [Set.mem_image] at h_u2
      obtain ⟨v, hv_mem, hv_eq⟩ := h_u2
      rw [← hv_eq]
      exact Set.mem_of_eq_of_mem (φ.graph_iso.left_inv' v) hv_mem
    have type_mem : φ.graph_iso.symm u ∈ G₀.type_verts := by
      have : φ.graph_iso.symm u ∈ (Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts := Set.mem_inter preimg_i preimg_j
      rw [h_vert₀] at this
      exact this
    obtain ⟨t, ⟨_, ht⟩⟩ := type_mem
    have img_eq : u = φ.graph_iso (G₀.type_embed t) := by
      rw [ht]
      exact (φ.graph_iso.right_inv' u).symm
    have preserve : φ.graph_iso (G₀.type_embed t) = G₁.type_embed t := by
      have := φ.type_preserve
      have : φ.graph_iso (G₀.type_embed t) = (φ.graph_iso ∘ G₀.type_embed) t := rfl
      rw [this, φ.type_preserve]
    rw [img_eq, preserve]
    dsimp [LabeledGraph.type_verts]
    exact Set.mem_image_of_mem (⇑G₁.type_embed) (Set.mem_univ t)
  · intro h_u
    obtain ⟨t, ⟨_, ht⟩⟩ := h_u
    have mem_i : u ∈ (Hl₁ i).subgraph.verts := by
      rw [← (Hl₁ i).embed_eq] at ht
      subst ht
      exact Subtype.coe_prop ((Hl₁ i).type_embed t)
    have mem_j : u ∈ (Hl₁ j).subgraph.verts := by
      rw [← (Hl₁ j).embed_eq] at ht
      subst ht
      exact Subtype.coe_prop ((Hl₁ j).type_embed t)
    exact Set.mem_inter mem_i mem_j

omit [Fintype V] [DecidableEq V] in
lemma inter_eq_subset_iff_diff_inter_empty
    {A B C : Set V} (hAC : C ⊆ A) (hBC : C ⊆ B)
    : A ∩ B = C ↔ (A \ C) ∩ (B \ C) = ∅ := by
  constructor
  · intro h
    subst h
    simp_all only [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
    ext1 x
    simp_all only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_true_eq_false,
        not_false_eq_true, implies_true]
  · intro h
    ext x
    constructor
    · intro h1
      by_contra h2
      have : x ∈ (A \ C) ∩ (B \ C) := by
        simp only [Set.mem_inter_iff, Set.mem_diff]
        exact ⟨⟨h1.1, h2⟩, ⟨h1.2, h2⟩⟩
      have : x ∉ (A \ C) ∩ (B \ C) := by rw [h]; simp
      contradiction
    · intro h1
      exact Set.mem_inter (hAC h1) (hBC h1)

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma predIsoLabeledHl_related_indep_ver_2_using_ver_1
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : ∀ (_ : Fin t), LabeledSubgraph σ G₀)
    (Hl₁ : ∀ (_ : Fin t), LabeledSubgraph σ G₁)
    (v_rel :  ∀ (i : Fin t), (Hl₁ i).subgraph.verts = ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts)
    : ∀ (i j : Fin t), ((Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts = G₀.type_verts) →
      ((Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts = G₁.type_verts) := by
  intro i j h
  have hAC : G₀.type_verts ⊆ (Hl₀ i).subgraph.verts := by
    intro x hx
    unfold LabeledGraph.type_verts at hx
    rw [Set.mem_image] at hx
    obtain ⟨t, ⟨_, ht⟩⟩ := hx
    rw [← (Hl₀ i).embed_eq] at ht
    subst ht
    simp_all only [Subtype.coe_prop]
  have hBC : G₀.type_verts ⊆ (Hl₀ j).subgraph.verts := by
    intro x hx
    unfold LabeledGraph.type_verts at hx
    rw [Set.mem_image] at hx
    obtain ⟨t, ⟨_, ht⟩⟩ := hx
    rw [← (Hl₀ j).embed_eq] at ht
    subst ht
    simp_all only [Subtype.coe_prop]
  have h1 := (inter_eq_subset_iff_diff_inter_empty hAC hBC).mp h
  have hAC' : G₁.type_verts ⊆ (Hl₁ i).subgraph.verts := by
    intro x hx
    unfold LabeledGraph.type_verts at hx
    rw [Set.mem_image] at hx
    obtain ⟨t, ⟨_, ht⟩⟩ := hx
    rw [← (Hl₁ i).embed_eq] at ht
    subst ht
    exact Subtype.coe_prop ((Hl₁ i).type_embed t)
  have hBC' : G₁.type_verts ⊆ (Hl₁ j).subgraph.verts := by
    intro x hx
    unfold LabeledGraph.type_verts at hx
    rw [Set.mem_image] at hx
    obtain ⟨t, ⟨_, ht⟩⟩ := hx
    rw [← (Hl₁ j).embed_eq] at ht
    subst ht
    exact Subtype.coe_prop ((Hl₁ j).type_embed t)
  have h2 := (inter_eq_subset_iff_diff_inter_empty hAC' hBC').mpr
  apply h2
  exact predIsoLabeledHl_related_indep_ver_1 φ Hl₀ Hl₁ v_rel i j h1
