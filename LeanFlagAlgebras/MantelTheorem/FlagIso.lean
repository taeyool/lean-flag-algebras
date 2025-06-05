import «LeanFlagAlgebras».MantelTheorem.FlagDefs

open FlagAlgebras

namespace MantelTheorem

lemma all_isomorphism_on_Fin3
    (φ : Fin 3 ≃ Fin 3)
    : (φ 0 = 0 ∧ φ 1 = 1 ∧ φ 2 = 2) ∨
      (φ 0 = 0 ∧ φ 1 = 2 ∧ φ 2 = 1) ∨
      (φ 0 = 1 ∧ φ 1 = 0 ∧ φ 2 = 2) ∨
      (φ 0 = 1 ∧ φ 1 = 2 ∧ φ 2 = 0) ∨
      (φ 0 = 2 ∧ φ 1 = 0 ∧ φ 2 = 1) ∨
      (φ 0 = 2 ∧ φ 1 = 1 ∧ φ 2 = 0)
  := by
  have inj_φ := Equiv.injective φ
  match h₀ : φ 0 with
  | 0 =>
    match h₁ : φ 1 with
    | 0 => have := @inj_φ 0 1 (Eq.trans h₀ h₁.symm); contradiction
    | 1 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 1 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
      | 2 => left; simp
    | 2 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 1 => right; left; simp
      | 2 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
  | 1 =>
    match h₁ : φ 1 with
    | 0 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
      | 1 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 2 => right; right; left; simp
    | 1 => have := @inj_φ 0 1 (Eq.trans h₀ h₁.symm); contradiction
    | 2 => match h₂ : φ 2 with
      | 0 => right; right; right; left; simp
      | 1 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 2 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
  | 2 =>
    match h₁ : φ 1 with
    | 0 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
      | 1 => right; right; right; right; left; simp
      | 2 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
    | 1 => match h₂ : φ 2 with
      | 0 => right; right; right; right; right; simp
      | 1 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
      | 2 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
    | 2 => have := @inj_φ 0 1 (Eq.trans h₀ h₁.symm); contradiction

lemma all_fun_from_Fin1_to_Fin3
    (f : Fin 1 → Fin 3)
    : f = (fun _ => 0) ∨ f = (fun _ => 1) ∨ f = (fun _ => 2)
  := by
  match h_f0 : f 0 with
  | 0 =>
    left
    apply funext
    intro
    simp_all only [Fin.fin_one_eq_zero, Fin.isValue]
  | 1 =>
    right; left
    apply funext
    intro
    simp_all only [Fin.fin_one_eq_zero, Fin.isValue]
  | 2 =>
    right; right
    apply funext
    intro
    simp_all only [Fin.fin_one_eq_zero, Fin.isValue]


/- graphs -/

lemma O3_E3_graph_not_iso
    : ¬ Nonempty (O3_graph ≃g E3_graph)
  := by
  intro h
  let φ := h.some
  rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  <;> simp at h₀ h₁ h₂
  · have : O3_graph.Adj 0 1 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁]
      simp
    contradiction
  · have : O3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 0 1 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁]
      simp
    contradiction
  · have : O3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction

lemma O3_P3_graph_not_iso
    : ¬ Nonempty (O3_graph ≃g P3_graph)
  := by
  intro h
  let φ := h.some
  rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  <;> simp at h₀ h₁ h₂
  · have : O3_graph.Adj 0 1 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁]
      simp
    contradiction
  · have : O3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 0 1 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁]
      simp
    contradiction
  · have : O3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction

lemma O3_K3_graph_not_iso
    : ¬ Nonempty (O3_graph ≃g K3_graph)
  := by
  intro h
  let φ := h.some
  rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  <;> simp at h₀ h₁ h₂
  · have : O3_graph.Adj 0 1 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁]
      simp
    contradiction
  · have : O3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 0 1 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁]
      simp
    contradiction
  · have : O3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : O3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction

lemma E3_P3_graph_not_iso
    : ¬ Nonempty (E3_graph ≃g P3_graph)
  := by
  intro h
  let φ := h.some
  rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  <;> simp at h₀ h₁ h₂
  · have : E3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction

lemma E3_K3_graph_not_iso
    : ¬ Nonempty (E3_graph ≃g K3_graph)
  := by
  intro h
  let φ := h.some
  rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  <;> simp at h₀ h₁ h₂
  · have : E3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 0 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : E3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction

lemma P3_K3_graph_not_iso
    : ¬ Nonempty (P3_graph ≃g K3_graph)
  := by
  intro h
  let φ := h.some
  rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  <;> simp at h₀ h₁ h₂
  · have : P3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : P3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : P3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : P3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : P3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction
  · have : P3_graph.Adj 1 2 := by
      rw [← SimpleGraph.Iso.map_adj_iff φ, h₁, h₂]
      simp
    contradiction

lemma threeVertexGraph_iso
    (G : SimpleGraph (Fin 3))
    : Nonempty (G ≃g O3_graph) ∨ Nonempty (G ≃g E3_graph) ∨ Nonempty (G ≃g P3_graph) ∨ Nonempty (G ≃g K3_graph)
  := by
  if h₀₁ : G.Adj 0 1 then
    if h₀₂ : G.Adj 0 2 then
      if h₁₂ : G.Adj 1 2 then -- K3 case
        right; right; right
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [K3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro; split) <;> simp at *
        }
      else -- P3 case
        right; right; left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
    else
      if h₁₂ : G.Adj 1 2 then -- P3 case
        right; right; left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
      else -- E3 case
        right; left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
  else
    if h₀₂ : G.Adj 0 2 then
      if h₁₂ : G.Adj 1 2 then -- P3 case
        right; right; left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
      else -- E3 case
        right; left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          invFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
    else
      if h₁₂ : G.Adj 1 2 then -- E3 case
        right; left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at h)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
      else -- O3 case
        left
        apply Nonempty.intro
        exact {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [O3_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;> contradiction
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at h)
        }


/- flags with empty type -/

lemma O3_E3_not_iso
    : ¬ O3_labeledGraph ∼f E3_labeledGraph
  := by
  intro h
  let φ := h.some.graph_iso
  exact O3_E3_graph_not_iso (Nonempty.intro φ)

lemma O3_P3_not_iso
    : ¬ O3_labeledGraph ∼f P3_labeledGraph
  := by
  intro h
  let φ := h.some.graph_iso
  exact O3_P3_graph_not_iso (Nonempty.intro φ)

lemma O3_K3_not_iso
    : ¬ O3_labeledGraph ∼f K3_labeledGraph
  := by
  intro h
  let φ := h.some.graph_iso
  exact O3_K3_graph_not_iso (Nonempty.intro φ)

lemma E3_P3_not_iso
    : ¬ E3_labeledGraph ∼f P3_labeledGraph
  := by
  intro h
  let φ := h.some.graph_iso
  exact E3_P3_graph_not_iso (Nonempty.intro φ)

lemma E3_K3_not_iso
    : ¬ E3_labeledGraph ∼f K3_labeledGraph
  := by
  intro h
  let φ := h.some.graph_iso
  exact E3_K3_graph_not_iso (Nonempty.intro φ)

lemma P3_K3_not_iso
    : ¬ P3_labeledGraph ∼f K3_labeledGraph
  := by
  intro h
  let φ := h.some.graph_iso
  exact P3_K3_graph_not_iso (Nonempty.intro φ)

def emptyTypeThreeVertexFlagSet : Finset (FlagWithSize ∅ₜ 3) where
  val := [O3_flag, E3_flag, P3_flag, K3_flag]
  nodup := by
    simp
    (repeat' constructor) <;> intro h
    · exact O3_E3_not_iso (Quotient.exact h)
    · exact O3_P3_not_iso (Quotient.exact h)
    · exact O3_K3_not_iso (Quotient.exact h)
    · exact E3_P3_not_iso (Quotient.exact h)
    · exact E3_K3_not_iso (Quotient.exact h)
    · exact P3_K3_not_iso (Quotient.exact h)

lemma emptyTypeThreeVertexLabeledGraph_eqv
    (G : LabeledGraph ∅ₜ (Fin 3))
    : G ∼f O3_labeledGraph ∨ G ∼f E3_labeledGraph ∨ G ∼f P3_labeledGraph ∨ G ∼f K3_labeledGraph
  := by
  rcases (threeVertexGraph_iso G.graph) with h | h | h | h
  <;> have φ := h.some
  · left
    apply Nonempty.intro
    exact {
      graph_iso := φ
      type_preserve := by
        funext i
        exact False.elim (Nat.not_succ_le_zero i.1 i.2)
    }
  · right; left
    apply Nonempty.intro
    exact {
      graph_iso := φ
      type_preserve := by
        funext i
        exact False.elim (Nat.not_succ_le_zero i.1 i.2)
    }
  · right; right; left
    apply Nonempty.intro
    exact {
      graph_iso := φ
      type_preserve := by
        funext i
        exact False.elim (Nat.not_succ_le_zero i.1 i.2)
    }
  · right; right; right
    apply Nonempty.intro
    exact {
      graph_iso := φ
      type_preserve := by
        funext i
        exact False.elim (Nat.not_succ_le_zero i.1 i.2)
    }

theorem emptyTypeThreeVertexFlagSet_eq_univ
    : emptyTypeThreeVertexFlagSet = Finset.univ
  := by
  ext F; constructor
  · intro _
    simp only [Finset.mem_univ]
  · intro _
    simp [emptyTypeThreeVertexFlagSet]
    rcases (emptyTypeThreeVertexLabeledGraph_eqv F.out) with h₀ | h₁ | h₂ | h₃
    · left
      rw [← F.out_eq]
      exact Quotient.sound h₀
    · right; left
      rw [← F.out_eq]
      exact Quotient.sound h₁
    · right; right; left
      rw [← F.out_eq]
      exact Quotient.sound h₂
    · right; right; right
      rw [← F.out_eq]
      exact Quotient.sound h₃


/- flags with singleton type -/

lemma O3₁_E3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 0
  := by
  sorry

lemma O3₁_E3₁'_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := by
  sorry

lemma O3₁_P3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := by
  sorry

lemma O3₁_P3₁'_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  sorry

lemma O3₁_K3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := by
  sorry

lemma E3₁_E3₁'_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := by
  sorry

lemma E3₁_P3₁_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := by
  sorry

lemma E3₁_P3₁'_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  sorry

lemma E3₁_K3₁_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := by
  sorry

lemma E3₁'_P3₁_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 0
  := by
  sorry

lemma E3₁'_P3₁'_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 1
  := by
  sorry

lemma E3₁'_K3₁_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f K3₁_labeledGraph 0
  := by
  sorry

lemma P3₁_P3₁'_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  sorry

lemma P3₁_K3₁_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := by
  sorry

lemma P3₁'_K3₁_not_iso
    : ¬ P3₁_labeledGraph 1 ∼f K3₁_labeledGraph 0
  := by
  sorry

def singletonTypeThreeVertexFlagSet : Finset (FlagWithSize Sₜ 3) where
  val := [O3₁_flag, E3₁_flag, E3₁'_flag, P3₁_flag, P3₁'_flag, K3₁_flag]
  nodup := by
    simp
    (repeat' constructor) <;> intro h <;> sorry

lemma temp
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g O3_graph)
    : G = O3₁_labeledGraph 0 ∨ G = O3₁_labeledGraph 1 ∨ G = O3₁_labeledGraph 2
  := by
  sorry

lemma singletonType_O3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g O3_graph)
    : G ∼f O3₁_labeledGraph 0
  := by
  sorry

lemma singletonType_E3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g E3_graph)
    : G ∼f E3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 2
  := by
  sorry

lemma singletonType_P3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g P3_graph)
    : G ∼f P3₁_labeledGraph 0 ∨ G ∼f P3₁_labeledGraph 1
  := by
  sorry

lemma singletonType_K3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g K3_graph)
    : G ∼f K3₁_labeledGraph 0
  := by
  sorry

lemma singletonTypeThreeVertexLabeledGraph_eqv
    (G : LabeledGraph Sₜ (Fin 3))
    : G ∼f O3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 2 ∨
      G ∼f P3₁_labeledGraph 0 ∨ G ∼f P3₁_labeledGraph 1 ∨ G ∼f K3₁_labeledGraph 0
  := by
  rcases (threeVertexGraph_iso G.graph) with h | h | h | h
  <;> have φ := h.some
  · left
    exact singletonType_O3_eqv G φ
  · rcases (singletonType_E3_eqv G φ) with h₀ | h₁
    · right; left
      exact h₀
    · right; right; left
      exact h₁
  · rcases (singletonType_P3_eqv G φ) with h₀ | h₁
    · right; right; right; left
      exact h₀
    · right; right; right; right; left
      exact h₁
  · right; right; right; right; right
    exact singletonType_K3_eqv G φ

lemma singletonTypeThreeVertexFlagSet_eq_univ
    : singletonTypeThreeVertexFlagSet = Finset.univ
  := by
  ext F; constructor
  · intro _
    simp only [Finset.mem_univ]
  · intro _
    simp [singletonTypeThreeVertexFlagSet]
    rcases (singletonTypeThreeVertexLabeledGraph_eqv F.out) with h₀ | h₁ | h₂ | h₃ | h₄ | h₅
    · left
      rw [← F.out_eq]
      exact Quotient.sound h₀
    · right; left
      rw [← F.out_eq]
      exact Quotient.sound h₁
    · right; right; left
      rw [← F.out_eq]
      exact Quotient.sound h₂
    · right; right; right; left
      rw [← F.out_eq]
      exact Quotient.sound h₃
    · right; right; right; right; left
      rw [← F.out_eq]
      exact Quotient.sound h₄
    · right; right; right; right; right
      rw [← F.out_eq]
      exact Quotient.sound h₅

end MantelTheorem
