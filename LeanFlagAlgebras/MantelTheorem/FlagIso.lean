import «LeanFlagAlgebras».MantelTheorem.FlagDefs
import Mathlib.Tactic.FinCases


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

syntax "prove_edgeSet_of" term "eq" term "using" "[" term,* "]": tactic

macro_rules
| `(tactic| prove_edgeSet_of $graph eq $target using [ $[$edge:term],* ]) => `(tactic|
    {
      show (SimpleGraph.edgeSet $graph) = $target
      dsimp [$graph:term]
      ext e
      { first
        | { simp; try { revert e; decide } }
        | { obtain ⟨⟨u, v⟩, h_eq⟩ := Quot.exists_rep e
            rw [←h_eq]
            simp
            constructor <;> {
              first
              | rintro (_ | _) <;> decide
              | rintro h; (rcases h <;> try (rename_i h; rcases h))
              <;> simp_all [$[$edge:term],*]
            }
          }
      }
    })

@[simp]
theorem O2_graph_edgeSet : O2_graph.edgeSet = ∅ := by
  prove_edgeSet_of O2_graph eq ∅ using []

@[simp]
theorem O2_graph_edgeSet_card : Fintype.card (O2_graph.edgeSet) = 0 := by
  simp

@[simp]
theorem K2_graph_edgeSet : K2_graph.edgeSet = { Sym2.mk (0, 1) } := by
  prove_edgeSet_of K2_graph eq { Sym2.mk (0, 1) } using []

@[simp]
theorem K2_graph_edgeSet_card : Fintype.card (K2_graph.edgeSet) = 1 := by
  simp

@[simp]
theorem O3_graph_edgeSet : O3_graph.edgeSet = ∅ := by
  prove_edgeSet_of O3_graph eq ∅ using []

@[simp]
theorem O3_graph_edgeSet_card : Fintype.card (O3_graph.edgeSet) = 0 := by
  simp

@[simp]
theorem E3_graph_edgeSet : E3_graph.edgeSet = { Sym2.mk (0, 1) } := by
  prove_edgeSet_of E3_graph eq { Sym2.mk (0, 1) } using [E3_edge.e01, E3_edge.e10]

@[simp]
theorem E3_graph_edgeSet_card : Fintype.card (E3_graph.edgeSet) = 1 := by
  simp

@[simp]
theorem P3_graph_edgeSet : P3_graph.edgeSet = { Sym2.mk (0, 1), Sym2.mk (0, 2) } := by
  prove_edgeSet_of P3_graph eq { Sym2.mk (0, 1), Sym2.mk (0, 2) } using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

@[simp]
theorem P3_graph_edgeSet_card : Fintype.card (P3_graph.edgeSet) = 2 := by
  simp

@[simp]
theorem K3_graph_edgeSet : K3_graph.edgeSet = { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) } := by
  prove_edgeSet_of K3_graph eq { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) } using []

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
  have h : ∀ i j : Fin 3, i ≠ j → φ i ≠ φ j :=
    fun i j h_ij h_eq ↦ h_ij (Equiv.injective φ h_eq)
  have h₀₁ := h 0 1 (by decide)
  have h₀₂ := h 0 2 (by decide)
  have h₁₂ := h 1 2 (by decide)
  omega

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


syntax "prove_threeVertexGraph_iso" term "and" term "using" term "and" term : tactic

macro_rules
| `(tactic| prove_threeVertexGraph_iso $source and $target using $map1 and $map2) => `(tactic|
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
  · prove_threeVertexGraph_iso G and K3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

  -- 2. P3 Case
  . prove_threeVertexGraph_iso G and P3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

  -- 3. P3 Case
  . prove_threeVertexGraph_iso G and P3_graph
      using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)

  -- 4. E3 Case
  . prove_threeVertexGraph_iso G and E3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

  -- 5. P3 Case
  . prove_threeVertexGraph_iso G and P3_graph
      using (fun | 0 => 2 | 2 => 0 | 1 => 1) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

  -- 6. E3 Case
  . prove_threeVertexGraph_iso G and E3_graph
      using (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)

  -- 7. E3 Case
  . prove_threeVertexGraph_iso G and E3_graph
      using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)

  -- 8. O3 Case
  . prove_threeVertexGraph_iso G and O3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

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


syntax "prove_emptyTypeThreeVertexLabeledGraph_eqv" term "and" term "using" term : tactic

macro_rules
| `(tactic| prove_emptyTypeThreeVertexLabeledGraph_eqv $source and $target using $map) => `(tactic|
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
  · prove_emptyTypeThreeVertexLabeledGraph_eqv G and O3_labeledGraph using h.some
  · prove_emptyTypeThreeVertexLabeledGraph_eqv G and E3_labeledGraph using h.some
  · prove_emptyTypeThreeVertexLabeledGraph_eqv G and P3_labeledGraph using h.some
  · prove_emptyTypeThreeVertexLabeledGraph_eqv G and K3_labeledGraph using h.some

theorem emptyTypeThreeVertexFlagSet_eq_univ
    : emptyTypeThreeVertexFlagSet = Finset.univ
  := by
  ext F; constructor
  · intro _
    exact Finset.mem_univ F
  · intro _
    simp [emptyTypeThreeVertexFlagSet]
    rcases (emptyTypeThreeVertexLabeledGraph_eqv F.out) with h | h | h | h
    · left
      rw [← F.out_eq]
      exact Quotient.sound h
    · right; left
      rw [← F.out_eq]
      exact Quotient.sound h
    · right; right; left
      rw [← F.out_eq]
      exact Quotient.sound h
    · right; right; right
      rw [← F.out_eq]
      exact Quotient.sound h


/- flags with singleton type -/

lemma graph_not_iso_implies_labeledGraph_not_iso
    {G H : LabeledGraph Sₜ (Fin 3)} (h : ¬ Nonempty (G.graph ≃g H.graph))
    : ¬ G ∼f H
  := fun h' ↦ h (Nonempty.intro h'.some.graph_iso)

lemma O3₁_E3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso O3_E3_graph_not_iso

lemma O3₁_E3₁'_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := graph_not_iso_implies_labeledGraph_not_iso O3_E3_graph_not_iso

lemma O3₁_P3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso O3_P3_graph_not_iso

lemma O3₁_P3₁'_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := graph_not_iso_implies_labeledGraph_not_iso O3_P3_graph_not_iso

lemma O3₁_K3₁_not_iso
    : ¬ O3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso O3_K3_graph_not_iso

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
  have : E3_graph.Adj 2 (φG 1) := by rw [←h₀]; exact (SimpleGraph.Iso.map_adj_iff φG).mpr E3_graph_01
  match h₁ : φG 1 with | 0 | 1 | 2 => rw [h₁] at this; simp_all

lemma E3₁_P3₁_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso E3_P3_graph_not_iso

lemma E3₁_P3₁'_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := graph_not_iso_implies_labeledGraph_not_iso E3_P3_graph_not_iso

lemma E3₁_K3₁_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso E3_K3_graph_not_iso

lemma E3₁'_P3₁_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso E3_P3_graph_not_iso

lemma E3₁'_P3₁'_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 1
  := graph_not_iso_implies_labeledGraph_not_iso E3_P3_graph_not_iso

lemma E3₁'_K3₁_not_iso
    : ¬ E3₁_labeledGraph 2 ∼f K3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso E3_K3_graph_not_iso

lemma P3₁_P3₁'_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := by
  intro h
  let φ := h.some.symm
  let φG := φ.graph_iso
  have h₀ : φG 1 = 0 := by
    calc
      _ = φG ((P3₁_labeledGraph 1).type_embed 0) := rfl
      _ = (φG ∘ (P3₁_labeledGraph 1).type_embed) 0 := rfl
      _ = (P3₁_labeledGraph 0).type_embed 0 := by rw [φ.type_preserve]
      _ = 0 := rfl
  have : P3_graph.Adj (φG 1) (φG 2) := by
    match h₂ : φG 2 with
    | 0 =>
        have : φG 1 = φG 2 := by rw [h₀, h₂]
        have := φG.injective this
        contradiction
    | 1 | 2 => rw [h₀]; simp_all
  have := (SimpleGraph.Iso.map_adj_iff φG).mp this
  simp_all [P3₁_labeledGraph]

lemma P3₁_K3₁_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso P3_K3_graph_not_iso

lemma P3₁'_K3₁_not_iso
    : ¬ P3₁_labeledGraph 1 ∼f K3₁_labeledGraph 0
  := graph_not_iso_implies_labeledGraph_not_iso P3_K3_graph_not_iso

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

syntax "prove_labeledGraph_equiv_on" term "with" term "and" term : tactic

macro_rules
| `(tactic| prove_labeledGraph_equiv_on $labeled_graph with $map1 and $map2) => `(tactic|
    {
      apply Nonempty.intro
      exact {
        graph_iso := {
          toFun := $map1
          invFun := $map2
          left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp_all
          right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp_all
          map_rel_iff' := by
            dsimp [$labeled_graph:term]
            intros; constructor
            · split <;> (intro h; split at h) <;>
              (first | assumption | symm; assumption | simp at *)
            · split <;> (intro h; split) <;>
              (first | contradiction | symm at h; contradiction | simp at *)
        }
        type_preserve := by
          simp [$labeled_graph:term]
          funext i
          simp_all [Fin.fin_one_eq_zero i]
      }
    })

lemma singletonType_O3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g O3_graph)
    : G ∼f O3₁_labeledGraph 0
  := by
  have h : ¬ G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2 := by
    rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁, h₂])
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := h
  match ht : G.type_embed 0 with
  | 0 => prove_labeledGraph_equiv_on O3₁_labeledGraph
           with (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
  | 1 => prove_labeledGraph_equiv_on O3₁_labeledGraph
           with (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
  | 2 => prove_labeledGraph_equiv_on O3₁_labeledGraph
           with (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

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
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
    | 1 =>
      left
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
    | 2 =>
      right
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
  · match ht : G.type_embed 0 with
    | 0 =>
      left
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)
    | 1 =>
      right
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)
    | 2 =>
      left
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 1 | 1 => 2 | 2 => 0) and (fun | 0 => 2 | 1 => 0 | 2 => 1)
  · match ht : G.type_embed 0 with
    | 0 =>
      right
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)
    | 1 =>
      left
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)
    | 2 =>
      left
      prove_labeledGraph_equiv_on E3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

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
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
    | 1 =>
      right
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
    | 2 =>
      right
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)
  · match ht : G.type_embed 0 with
    | 0 =>
      right
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
    | 1 =>
      left
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
    | 2 =>
      right
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)
  · match ht : G.type_embed 0 with
    | 0 =>
      right
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 1 | 1 => 2 | 2 => 0) and (fun | 0 => 2 | 1 => 0 | 2 => 1)
    | 1 =>
      right
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)
    | 2 =>
      left
      prove_labeledGraph_equiv_on P3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

lemma singletonType_K3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g K3_graph)
    : G ∼f K3₁_labeledGraph 0
  := by
  have h : G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2 := by
    rcases (all_isomorphism_on_Fin3 φ) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff φ, h₀, h₁, h₂])
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := h
  match ht : G.type_embed 0 with
  | 0 =>
      prove_labeledGraph_equiv_on K3₁_labeledGraph
        with (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
  | 1 =>
      prove_labeledGraph_equiv_on K3₁_labeledGraph
        with (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
  | 2 =>
      prove_labeledGraph_equiv_on K3₁_labeledGraph
        with (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

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
