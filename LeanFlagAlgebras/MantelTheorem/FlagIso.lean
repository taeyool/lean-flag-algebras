import «LeanFlagAlgebras».MantelTheorem.FlagDefs


open FlagAlgebras

namespace MantelTheorem

noncomputable instance {V : Type} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet := by
  classical
  exact Fintype.ofFinite G.edgeSet

lemma cards_of_edge_sets_of_iso_graphs_eq {V W : Type} [Fintype V] [Fintype W]
    {G₁ : SimpleGraph V} {G₂ : SimpleGraph W} (h : Nonempty (G₁ ≃g G₂))
    : Fintype.card (G₁.edgeSet) = Fintype.card (G₂.edgeSet)
  := by
  apply Fintype.card_congr
  exact SimpleGraph.Iso.mapEdgeSet h.some

@[simp]
theorem O2_graph_edgeSet : O2_graph.edgeSet = ∅ := by
  simp [O2_graph]

@[simp]
theorem O2_graph_edgeSet_card : Fintype.card (O2_graph.edgeSet) = 0 := by
  simp

@[simp]
theorem K2_graph_edgeSet : K2_graph.edgeSet = { Sym2.mk (0, 1) } := by
  ext e
  simp [K2_graph]
  revert e
  decide

@[simp]
theorem K2_graph_edgeSet_card : Fintype.card (K2_graph.edgeSet) = 1 := by
  simp

@[simp]
theorem O3_graph_edgeSet : O3_graph.edgeSet = ∅ := by
  simp [O3_graph]

@[simp]
theorem O3_graph_edgeSet_card : Fintype.card (O3_graph.edgeSet) = 0 := by
  simp

@[simp]
theorem E3_graph_edgeSet : E3_graph.edgeSet = { Sym2.mk (0, 1) } := by
  ext e
  obtain ⟨⟨u, v⟩, h_eq⟩ := Quot.exists_rep e
  rw [←h_eq]
  simp [E3_graph]
  constructor
  · intro h
    rcases h with (_ | _) <;> simp
  · intro h
    rcases h with (_ | _)
    . simp_all; exact E3_edge.e01
    . simp_all; exact E3_edge.e10

@[simp]
theorem E3_graph_edgeSet_card : Fintype.card (E3_graph.edgeSet) = 1 := by
  simp

@[simp]
theorem P3_graph_edgeSet : P3_graph.edgeSet = { Sym2.mk (0, 1), Sym2.mk (0, 2) } := by
  ext e
  obtain ⟨⟨u, v⟩, h_eq⟩ := Quot.exists_rep e
  rw [←h_eq]
  simp [P3_graph]
  constructor
  · intro h
    rcases h with (_ | _) <;> simp
  · intro h
    rcases h with ((_ | _) | (_ | _))
    . simp_all; exact P3_edge.e01
    . simp_all; exact P3_edge.e10
    . simp_all; exact P3_edge.e02
    . simp_all; exact P3_edge.e20

@[simp]
theorem P3_graph_edgeSet_card : Fintype.card (P3_graph.edgeSet) = 2 := by
  simp

@[simp]
theorem K3_graph_edgeSet : K3_graph.edgeSet = { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) } := by
  ext e
  simp [K3_graph]
  revert e
  decide

@[simp]
theorem K3_graph_edgeSet_card : Fintype.card (K3_graph.edgeSet) = 3 := by
  simp

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
      | 2 => left; simp only [Fin.isValue, and_self]
    | 2 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 1 => right; left; simp only [Fin.isValue, and_self]
      | 2 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
  | 1 =>
    match h₁ : φ 1 with
    | 0 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
      | 1 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 2 => right; right; left; simp only [Fin.isValue, and_self]
    | 1 => have := @inj_φ 0 1 (Eq.trans h₀ h₁.symm); contradiction
    | 2 => match h₂ : φ 2 with
      | 0 => right; right; right; left; simp only [Fin.isValue, and_self]
      | 1 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
      | 2 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
  | 2 =>
    match h₁ : φ 1 with
    | 0 => match h₂ : φ 2 with
      | 0 => have := @inj_φ 1 2 (Eq.trans h₁ h₂.symm); contradiction
      | 1 => right; right; right; right; left; simp only [Fin.isValue, and_self]
      | 2 => have := @inj_φ 0 2 (Eq.trans h₀ h₂.symm); contradiction
    | 1 => match h₂ : φ 2 with
      | 0 => right; right; right; right; right; simp only [Fin.isValue, and_self]
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
    funext x
    rwa [Fin.fin_one_eq_zero x]
  | 1 =>
    right; left
    funext x
    rwa [Fin.fin_one_eq_zero x]
  | 2 =>
    right; right
    funext x
    rwa [Fin.fin_one_eq_zero x]


/- graphs -/

lemma O3_E3_graph_not_iso
    : ¬ Nonempty (O3_graph ≃g E3_graph)
  := by
  intro h
  have := cards_of_edge_sets_of_iso_graphs_eq h
  rw [O3_graph_edgeSet_card, E3_graph_edgeSet_card] at this
  simp_all

lemma O3_P3_graph_not_iso
    : ¬ Nonempty (O3_graph ≃g P3_graph)
  := by
  intro h
  have := cards_of_edge_sets_of_iso_graphs_eq h
  rw [O3_graph_edgeSet_card, P3_graph_edgeSet_card] at this
  simp_all

lemma O3_K3_graph_not_iso
    : ¬ Nonempty (O3_graph ≃g K3_graph)
  := by
  intro h
  have := cards_of_edge_sets_of_iso_graphs_eq h
  rw [O3_graph_edgeSet_card, K3_graph_edgeSet_card] at this
  simp_all

lemma E3_P3_graph_not_iso
    : ¬ Nonempty (E3_graph ≃g P3_graph)
  := by
  intro h
  have := cards_of_edge_sets_of_iso_graphs_eq h
  rw [E3_graph_edgeSet_card, P3_graph_edgeSet_card] at this
  simp_all

lemma E3_K3_graph_not_iso
    : ¬ Nonempty (E3_graph ≃g K3_graph)
  := by
  intro h
  have := cards_of_edge_sets_of_iso_graphs_eq h
  rw [E3_graph_edgeSet_card, K3_graph_edgeSet_card] at this
  simp_all

lemma P3_K3_graph_not_iso
    : ¬ Nonempty (P3_graph ≃g K3_graph)
  := by
  intro h
  have := cards_of_edge_sets_of_iso_graphs_eq h
  rw [P3_graph_edgeSet_card, K3_graph_edgeSet_card] at this
  simp_all


syntax "prove_graph_iso" term "and" term ("using" term "and" term)? : tactic

macro_rules
| `(tactic| prove_graph_iso $source and $target) => `(tactic|
    {
      have : Nonempty ($source ≃g $target) := by
        apply Nonempty.intro
        have : $source = $target := by
          ext u v
          match u, v with
          | 0, 1 | 1, 0 | 2, 0 | 0, 2 | 1, 2 | 2, 1 | 0, 0 | 1, 1 | 2, 2
          => simp_all [SimpleGraph.adj_comm $source]
        rw [this]
      simp [this]
    })
| `(tactic| prove_graph_iso $source and $target using $map1 and $map2) => `(tactic|
    {
      have : Nonempty ($source ≃g $target) := by
        apply Nonempty.intro
        exact {
          toFun := $map1
          invFun := $map2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp_all
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp_all
          map_rel_iff' := by
            intros; simp; constructor <;> split <;> split <;> (intro h; simp_all [SimpleGraph.adj_comm $source])
        }
      simp [this]
    })

lemma threeVertexGraph_iso
    (G : SimpleGraph (Fin 3))
    : Nonempty (G ≃g O3_graph) ∨ Nonempty (G ≃g E3_graph) ∨ Nonempty (G ≃g P3_graph) ∨ Nonempty (G ≃g K3_graph)
  := by
  rcases (Classical.em (G.Adj 0 1)) with h₀₁ | h₀₁
  <;> rcases (Classical.em (G.Adj 0 2)) with h₀₂ | h₀₂
  <;> rcases (Classical.em (G.Adj 1 2)) with h₁₂ | h₁₂

  -- 1. K3 Case
  · prove_graph_iso G and K3_graph

  -- 2. P3 Case
  . prove_graph_iso G and P3_graph

  -- 3. P3 Case
  . prove_graph_iso G and P3_graph
      using (fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1) and (fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0)

  -- 4. E3 Case
  . prove_graph_iso G and E3_graph

  -- 5. P3 Case
  . prove_graph_iso G and P3_graph
      using (fun i => match i with | 0 => 2 | 2 => 0 | 1 => 1) and (fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0)

  -- 6. E3 Case
  . prove_graph_iso G and E3_graph
      using (fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1) and (fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1)

  -- 7. E3 Case
  . prove_graph_iso G and E3_graph
      using (fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1) and (fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0)

  -- 8. O3 Case
  . prove_graph_iso G and O3_graph

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


syntax "prove_labeled_graph_iso" term "and" term "using" term : tactic

macro_rules
| `(tactic| prove_labeled_graph_iso $source and $target using $map) => `(tactic|
    {
      have : $source ∼f $target := by
        apply Nonempty.intro
        exact {
          graph_iso := $map
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      simp [this]
    })

lemma emptyTypeThreeVertexLabeledGraph_eqv
    (G : LabeledGraph ∅ₜ (Fin 3))
    : G ∼f O3_labeledGraph ∨ G ∼f E3_labeledGraph ∨ G ∼f P3_labeledGraph ∨ G ∼f K3_labeledGraph
  := by
  rcases (threeVertexGraph_iso G.graph) with h | h | h | h
  · prove_labeled_graph_iso G and O3_labeledGraph using h.some
  · prove_labeled_graph_iso G and E3_labeledGraph using h.some
  · prove_labeled_graph_iso G and P3_labeledGraph using h.some
  · prove_labeled_graph_iso G and K3_labeledGraph using h.some

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

lemma graph_not_iso_implies_labeledGraph_not_iso
    {G H : LabeledGraph Sₜ (Fin 3)} (h : ¬ Nonempty (G.graph ≃g H.graph))
    : ¬ G ∼f H
  := by
  contrapose! h
  exact (Nonempty.intro h.some.graph_iso)

lemma O3₁_E3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [O3₁_labeledGraph, E3₁_labeledGraph]
  exact O3_E3_graph_not_iso

lemma O3₁_E3₁'_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [O3₁_labeledGraph, E3₁_labeledGraph]
  exact O3_E3_graph_not_iso

lemma O3₁_P3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [O3₁_labeledGraph, P3₁_labeledGraph]
  exact O3_P3_graph_not_iso

lemma O3₁_P3₁'_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [O3₁_labeledGraph, P3₁_labeledGraph]
  exact O3_P3_graph_not_iso

lemma O3₁_K3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [O3₁_labeledGraph, K3₁_labeledGraph]
  exact O3_K3_graph_not_iso

lemma E3₁_E3₁'_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := by
  intro h
  let φ := h.some
  let φG := φ.graph_iso
  have h₀ : φG 0 = 2 := by
    calc
      _ = φG ((E3₁_labeledGraph 0).type_embed 0) := rfl
      _ = (φG ∘ (E3₁_labeledGraph 0).type_embed) 0 := rfl
      _ = (E3₁_labeledGraph 2).type_embed 0 := by rw [φ.type_preserve]
      _ = 2 := rfl
  match h₁ : φG 1 with
  | 0 =>
      have : E3_graph.Adj 0 1 := by simp only [E3_graph_01]
      have : E3_graph.Adj (φG 0) (φG 1) := (SimpleGraph.Iso.map_adj_iff φG).mpr this
      have : ¬ E3_graph.Adj (φG 0) (φG 1) := by simp only [h₀, h₁, E3_graph_20, not_false_eq_true]
      contradiction
  | 1 =>
      have : E3_graph.Adj 0 1 := by simp only [E3_graph_01]
      have : E3_graph.Adj (φG 0) (φG 1) := (SimpleGraph.Iso.map_adj_iff φG).mpr this
      have : ¬ E3_graph.Adj (φG 0) (φG 1) := by simp only [h₀, h₁, E3_graph_21, not_false_eq_true]
      contradiction
  | 2 =>
      have : φG 0 = φG 1 := by rw [h₀, h₁]
      have : φG 0 ≠ φG 1 := by simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq,
        Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true]
      contradiction

lemma E3₁_P3₁_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [E3₁_labeledGraph, P3₁_labeledGraph]
  exact E3_P3_graph_not_iso

lemma E3₁_P3₁'_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [E3₁_labeledGraph, P3₁_labeledGraph]
  exact E3_P3_graph_not_iso

lemma E3₁_K3₁_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [E3₁_labeledGraph, K3₁_labeledGraph]
  exact E3_K3_graph_not_iso

lemma E3₁'_P3₁_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [E3₁_labeledGraph, P3₁_labeledGraph]
  exact E3_P3_graph_not_iso

lemma E3₁'_P3₁'_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 1
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [E3₁_labeledGraph, P3₁_labeledGraph]
  exact E3_P3_graph_not_iso

lemma E3₁'_K3₁_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f K3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [E3₁_labeledGraph, K3₁_labeledGraph]
  exact E3_K3_graph_not_iso

lemma P3₁_P3₁'_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  intro h
  let φ := h.some
  let φG := φ.graph_iso
  have h₀ : φG 0 = 1 := by
    calc
      _ = φG ((P3₁_labeledGraph 0).type_embed 0) := rfl
      _ = (φG ∘ (P3₁_labeledGraph 0).type_embed) 0 := rfl
      _ = (P3₁_labeledGraph 1).type_embed 0 := by rw [φ.type_preserve]
      _ = 1 := rfl
  match h₂ : φG.invFun 2 with
  | 0 =>
    have h' : φG 0 = 2 := by
      rw [← h₂]
      exact φG.right_inv 2
    rw [h₀] at h'
    contradiction
  | 1 =>
    have h' : φG 1 = 2 := by
      rw [← h₂]
      exact φG.right_inv 2
    have : P3_graph.Adj 0 1 := by simp only [P3_graph_01]
    have : P3_graph.Adj (φG 0) (φG 1) := (SimpleGraph.Iso.map_adj_iff φG).mpr this
    have : ¬ P3_graph.Adj (φG 0) (φG 1) := by simp only [h₀, h', P3_graph_12, not_false_eq_true]
    contradiction
  | 2 =>
    have h' : φG 2 = 2 := by
      nth_rw 1 [← h₂]
      exact φG.right_inv 2
    have : P3_graph.Adj 0 2 := by simp only [P3_graph_02]
    have : P3_graph.Adj (φG 0) (φG 2) := (SimpleGraph.Iso.map_adj_iff φG).mpr this
    have : ¬ P3_graph.Adj (φG 0) (φG 2) := by simp only [h₀, h', P3_graph_12, not_false_eq_true]
    contradiction

lemma P3₁_K3₁_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [P3₁_labeledGraph, K3₁_labeledGraph]
  exact P3_K3_graph_not_iso

lemma P3₁'_K3₁_not_iso
    : ¬ P3₁_labeledGraph 1 ∼f K3₁_labeledGraph 0
  := by
  apply graph_not_iso_implies_labeledGraph_not_iso
  simp only [P3₁_labeledGraph, K3₁_labeledGraph]
  exact P3_K3_graph_not_iso

def singletonTypeThreeVertexFlagSet : Finset (FlagWithSize Sₜ 3) where
  val := [O3₁_flag, E3₁_flag, E3₁'_flag, P3₁_flag, P3₁'_flag, K3₁_flag]
  nodup := by
    simp
    (repeat' constructor) <;> intro h
    · exact O3₁_E3₁_not_iso (Quotient.exact h)
    · exact O3₁_E3₁'_not_iso (Quotient.exact h)
    · exact O3₁_P3₁_not_iso (Quotient.exact h)
    · exact O3₁_P3₁'_not_iso (Quotient.exact h)
    · exact O3₁_K3₁_not_iso (Quotient.exact h)
    · exact E3₁_E3₁'_not_iso (Quotient.exact h)
    · exact E3₁_P3₁_not_iso (Quotient.exact h)
    · exact E3₁_P3₁'_not_iso (Quotient.exact h)
    · exact E3₁_K3₁_not_iso (Quotient.exact h)
    · exact E3₁'_P3₁_not_iso (Quotient.exact h)
    · exact E3₁'_P3₁'_not_iso (Quotient.exact h)
    · exact E3₁'_K3₁_not_iso (Quotient.exact h)
    · exact P3₁_P3₁'_not_iso (Quotient.exact h)
    · exact P3₁_K3₁_not_iso (Quotient.exact h)
    · exact P3₁'_K3₁_not_iso (Quotient.exact h)

lemma singletonType_O3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g O3_graph)
    : G ∼f O3₁_labeledGraph 0
  := by
  have h : ¬ G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2 := by
    rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁, h₂])
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := h
  apply Nonempty.intro
  match ht : G.type_embed 0 with
  | 0 => exact {
      graph_iso := {
        toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
        invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
        left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        map_rel_iff' := by
          dsimp [O3₁_labeledGraph]
          intros; constructor
          · split <;> (intro h; split at h) <;>
            (first | assumption | simp at h)
          · split <;> (intro h; split) <;>
            (first | contradiction | symm at h; contradiction | simp at *)
      }
      type_preserve := by
        simp [O3₁_labeledGraph]
        funext i
        simp [Fin.fin_one_eq_zero i]
        rw [ht]
    }
  | 1 => exact {
      graph_iso := {
        toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
        invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
        left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        map_rel_iff' := by
          dsimp [O3₁_labeledGraph]
          intros; constructor
          · split <;> (intro h; split at h) <;>
            (first | assumption | simp at h)
          · split <;> (intro h; split) <;>
            (first | contradiction | symm at h; contradiction | simp at *)
      }
      type_preserve := by
        simp [O3₁_labeledGraph]
        funext i
        simp [Fin.fin_one_eq_zero i]
        rw [ht]
    }
  | 2 => exact {
      graph_iso := {
        toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
        invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
        left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        map_rel_iff' := by
          dsimp [O3₁_labeledGraph]
          intros; constructor
          · split <;> (intro h; split at h) <;>
            (first | assumption | simp at h)
          · split <;> (intro h; split) <;>
            (first | contradiction | symm at h; contradiction | simp at *)
      }
      type_preserve := by
        simp [O3₁_labeledGraph]
        funext i
        simp [Fin.fin_one_eq_zero i]
        rw [ht]
    }

lemma singletonType_E3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g E3_graph)
    : G ∼f E3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 2
  := by
  have h : (G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2) ∨
      (¬ G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2) ∨
      (¬ G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2) := by
    rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁, h₂])
  rcases h with ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩
  · match ht : G.type_embed 0 with
    | 0 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 1 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 2 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
  · match ht : G.type_embed 0 with
    | 0 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          invFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 1 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          invFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 2 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
  · match ht : G.type_embed 0 with
    | 0 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 1 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
          invFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 2 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [E3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [E3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }

lemma singletonType_P3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g P3_graph)
    : G ∼f P3₁_labeledGraph 0 ∨ G ∼f P3₁_labeledGraph 1
  := by
  have h : (G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2) ∨
      (G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2) ∨
      (¬ G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2) := by
    rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁, h₂])
  rcases h with ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩
  · match ht : G.type_embed 0 with
    | 0 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 1 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 2 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          invFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
  · match ht : G.type_embed 0 with
    | 0 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 1 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 2 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
          invFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
  · match ht : G.type_embed 0 with
    | 0 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 1 =>
      right
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }
    | 2 =>
      left
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
          map_rel_iff' := by
            dsimp [P3₁_labeledGraph]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [P3₁_labeledGraph]
          funext i
          simp [Fin.fin_one_eq_zero i]
          rw [ht]
      }

lemma singletonType_K3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g K3_graph)
    : G ∼f K3₁_labeledGraph 0
  := by
  have h : G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2 := by
    rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁, h₂])
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := h
  apply Nonempty.intro
  match ht : G.type_embed 0 with
  | 0 => exact {
      graph_iso := {
        toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
        invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
        left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        map_rel_iff' := by
          dsimp [K3₁_labeledGraph]
          intros; constructor
          · split <;> (intro h; split at h) <;>
            (first | assumption | symm; assumption | simp at *)
          · split <;> (intro h; split) <;>
            (first | contradiction | simp at *)
      }
      type_preserve := by
        simp [K3₁_labeledGraph]
        funext i
        simp [Fin.fin_one_eq_zero i]
        rw [ht]
    }
  | 1 => exact {
      graph_iso := {
        toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
        invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
        left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        map_rel_iff' := by
          dsimp [K3₁_labeledGraph]
          intros; constructor
          · split <;> (intro h; split at h) <;>
            (first | assumption | symm; assumption | simp at *)
          · split <;> (intro h; split) <;>
            (first | contradiction | simp at *)
      }
      type_preserve := by
        simp [K3₁_labeledGraph]
        funext i
        simp [Fin.fin_one_eq_zero i]
        rw [ht]
    }
  | 2 => exact {
      graph_iso := {
        toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
        invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
        left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
        map_rel_iff' := by
          dsimp [K3₁_labeledGraph]
          intros; constructor
          · split <;> (intro h; split at h) <;>
            (first | assumption | symm; assumption | simp at *)
          · split <;> (intro h; split) <;>
            (first | contradiction | simp at *)
      }
      type_preserve := by
        simp [K3₁_labeledGraph]
        funext i
        simp [Fin.fin_one_eq_zero i]
        rw [ht]
    }

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
