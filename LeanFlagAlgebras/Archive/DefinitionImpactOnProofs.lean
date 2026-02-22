import «LeanFlagAlgebras».FlagAlgebra.SubflagDensity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Finset.Basic

open FlagAlgebras
open Classical

namespace Archive.DefinitionImpactOnProofs

variable {T : Type} [Fintype T] {σ : FlagType T}

variable {t : ℕ} {Vl : Fin t → Type} {Vl' : Fin t → Type}
  {V : Type} [Fintype V]
  {W : Type} [Fintype W]
  {U : Type} [Fintype U]
  {U₁ : Type} [Fintype U₁]
  {U₂ : Type} [Fintype U₂]
  {U₃ : Type} [Fintype U₃]

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

omit [Fintype T] [Fintype V] [Fintype W] in
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
    rw [v_rel k, Set.mem_image] at h_wk₁
    obtain ⟨w', ⟨h_wk₀, rfl⟩⟩ := h_wk₁
    exact Set.mem_of_eq_of_mem (φ.graph_iso.left_inv' w') h_wk₀
  have h_w' : w ∉ G₁.type_verts → φ.symm.graph_iso w ∉ G₀.type_verts := by
    rintro h_wk₁ ⟨t, -, h_t⟩
    apply h_wk₁
    simp only [← φ.symm.type_preserve, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h_t
    rw [← h_t]
    exact Set.mem_image_of_mem (⇑G₁.type_embed) trivial
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

omit [Fintype T] [Fintype V] [Fintype W] in
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
  · rintro ⟨h_u1, h_u2⟩
    have preimg_i : φ.graph_iso.symm u ∈ (Hl₀ i).subgraph.verts := by
      rw [v_rel i, Set.mem_image] at h_u1
      obtain ⟨v, hv_mem, rfl⟩ := h_u1
      exact Set.mem_of_eq_of_mem (φ.graph_iso.left_inv' v) hv_mem
    have preimg_j : φ.graph_iso.symm u ∈ (Hl₀ j).subgraph.verts := by
      rw [v_rel j, Set.mem_image] at h_u2
      obtain ⟨v, hv_mem, rfl⟩ := h_u2
      exact Set.mem_of_eq_of_mem (φ.graph_iso.left_inv' v) hv_mem
    have type_mem : φ.graph_iso.symm u ∈ G₀.type_verts := by
      have : φ.graph_iso.symm u ∈ (Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts := Set.mem_inter preimg_i preimg_j
      exact h_vert₀ ▸ this
    obtain ⟨t, ⟨-, ht⟩⟩ := type_mem
    have img_eq : u = (φ.graph_iso ∘ G₀.type_embed) t := by
      rw [Function.comp_apply, ht]
      exact (φ.graph_iso.right_inv' u).symm
    rw [img_eq, φ.type_preserve]
    exact Set.mem_image_of_mem (⇑G₁.type_embed) (Set.mem_univ t)
  · rintro ⟨t, -, ht⟩
    have mem_i : u ∈ (Hl₁ i).subgraph.verts := by
      rw [← (Hl₁ i).embed_eq] at ht
      subst ht
      exact Subtype.coe_prop ((Hl₁ i).type_embed t)
    have mem_j : u ∈ (Hl₁ j).subgraph.verts := by
      rw [← (Hl₁ j).embed_eq] at ht
      subst ht
      exact Subtype.coe_prop ((Hl₁ j).type_embed t)
    exact Set.mem_inter mem_i mem_j

omit [Fintype V] in
lemma inter_eq_subset_iff_diff_inter_empty
    {A B C : Set V} (hAC : C ⊆ A) (hBC : C ⊆ B)
    : A ∩ B = C ↔ (A \ C) ∩ (B \ C) = ∅ := by
  constructor <;> intro h
  · subst h
    rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff, ← Set.disjoint_iff_inter_eq_empty]
    exact disjoint_sdiff_sdiff
  · rw [Set.sdiff_inter_right_comm, Set.diff_eq_empty, Set.inter_subset, Set.compl_diff,
      Set.union_comm C, Set.union_assoc, Set.union_self, ← Set.inter_subset] at h
    exact subset_antisymm h (by tauto)

omit [Fintype T] [Fintype V] [Fintype W] in
lemma predIsoLabeledHl_related_indep_ver_2_using_ver_1
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (Hl₀ : Fin t → LabeledSubgraph σ G₀)
    (Hl₁ : Fin t → LabeledSubgraph σ G₁)
    (v_rel :  ∀ (i : Fin t), (Hl₁ i).subgraph.verts = ⇑φ.graph_iso '' (Hl₀ i).subgraph.verts)
    : ∀ (i j : Fin t), ((Hl₀ i).subgraph.verts ∩ (Hl₀ j).subgraph.verts = G₀.type_verts) →
      ((Hl₁ i).subgraph.verts ∩ (Hl₁ j).subgraph.verts = G₁.type_verts) := by
  intro i j h
  have hAC : G₀.type_verts ⊆ (Hl₀ i).subgraph.verts := by
    intro x hx
    obtain ⟨t, rfl⟩ := LabeledGraph.mem_type_verts.mp hx
    exact (Hl₀ i).embed_eq _ ▸ (Subtype.coe_prop _)
  have hBC : G₀.type_verts ⊆ (Hl₀ j).subgraph.verts := by
    intro x hx
    obtain ⟨t, rfl⟩ := LabeledGraph.mem_type_verts.mp hx
    exact (Hl₀ j).embed_eq _ ▸ (Subtype.coe_prop _)
  have h1 := (inter_eq_subset_iff_diff_inter_empty hAC hBC).mp h
  have hAC' : G₁.type_verts ⊆ (Hl₁ i).subgraph.verts := by
    intro x hx
    obtain ⟨t, rfl⟩ := LabeledGraph.mem_type_verts.mp hx
    exact (Hl₁ i).embed_eq _ ▸ (Subtype.coe_prop _)
  have hBC' : G₁.type_verts ⊆ (Hl₁ j).subgraph.verts := by
    intro x hx
    obtain ⟨t, rfl⟩ := LabeledGraph.mem_type_verts.mp hx
    exact (Hl₁ j).embed_eq _ ▸ (Subtype.coe_prop _)
  rw [inter_eq_subset_iff_diff_inter_empty hAC' hBC']
  exact predIsoLabeledHl_related_indep_ver_1 φ Hl₀ Hl₁ v_rel i j h1

end Archive.DefinitionImpactOnProofs
