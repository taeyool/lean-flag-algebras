import «LeanFlagAlgebras».Archive.MantelTheorem.FlagDefs
import Mathlib.Tactic.FinCases

/-!
# (Archived, older) Enumerated flag sets via explicit graph isomorphisms

ARCHIVED / SUPERSEDED — this file is **not** part of the build (its import is
commented out in `LeanFlagAlgebras.lean`). This is the *older* approach to
enumerating the non-isomorphic 3-vertex flags: it classifies every 3-vertex
graph up to isomorphism by hand (`threeVertexGraph_iso`), builds the explicit
isomorphisms via custom tactics, and proves the flag sets equal `Finset.univ`.
It was replaced by the shorter `Sym2`/`native_decide`-based `FlagIso.lean`, and
both are superseded by the active loader-generated flag sets.
-/

open FlagAlgebras

namespace Archive.MantelTheorem

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
  have h_const : f = (fun x => f 0) := by
    funext x
    rw [Fin.fin_one_eq_zero x]
  rw [h_const]
  match f 0 with | 0 | 1 | 2 => simp only [Fin.isValue, true_or, or_true]

/- graphs -/

noncomputable instance {V : Type} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

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

lemma diff_cards_of_edge_sets_imply_non_iso {V W : Type} [Fintype V] [Fintype W]
    (G₁ : SimpleGraph V) (G₂ : SimpleGraph W)
    : Fintype.card (G₁.edgeSet) ≠ Fintype.card (G₂.edgeSet) → ¬ Nonempty (G₁ ≃g G₂)
  := by
  contrapose!
  intro h
  apply Fintype.card_congr
  exact SimpleGraph.Iso.mapEdgeSet h.some

lemma O3_E3_graph_not_iso : ¬ Nonempty (O3_graph ≃g E3_graph)
  := diff_cards_of_edge_sets_imply_non_iso O3_graph E3_graph (by simp)

lemma O3_P3_graph_not_iso : ¬ Nonempty (O3_graph ≃g P3_graph)
  := diff_cards_of_edge_sets_imply_non_iso O3_graph P3_graph (by simp)

lemma O3_K3_graph_not_iso : ¬ Nonempty (O3_graph ≃g K3_graph)
  := diff_cards_of_edge_sets_imply_non_iso O3_graph K3_graph (by simp)

lemma E3_P3_graph_not_iso : ¬ Nonempty (E3_graph ≃g P3_graph)
  := diff_cards_of_edge_sets_imply_non_iso E3_graph P3_graph (by simp)

lemma E3_K3_graph_not_iso : ¬ Nonempty (E3_graph ≃g K3_graph)
  := diff_cards_of_edge_sets_imply_non_iso E3_graph K3_graph (by simp)

lemma P3_K3_graph_not_iso : ¬ Nonempty (P3_graph ≃g K3_graph)
  := diff_cards_of_edge_sets_imply_non_iso P3_graph K3_graph (by simp)

syntax "prove_graph_iso" term "and" term "using" term "and" term : tactic

macro_rules
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

/-- Every 3-vertex graph is isomorphic to exactly one of `O3`, `E3`, `P3`, `K3`
(the classification underlying the hand-built flag enumeration). -/
lemma threeVertexGraph_iso
    (G : SimpleGraph (Fin 3))
    : Nonempty (G ≃g O3_graph) ∨ Nonempty (G ≃g E3_graph) ∨ Nonempty (G ≃g P3_graph) ∨ Nonempty (G ≃g K3_graph)
  := by
  rcases (Classical.em (G.Adj 0 1)) with _ | _
  <;> rcases (Classical.em (G.Adj 0 2)) with _ | _
  <;> rcases (Classical.em (G.Adj 1 2)) with _ | _

  -- 1. K3 Case
  · prove_graph_iso G and K3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

  -- 2. P3 Case
  . prove_graph_iso G and P3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

  -- 3. P3 Case
  . prove_graph_iso G and P3_graph
      using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)

  -- 4. E3 Case
  . prove_graph_iso G and E3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

  -- 5. P3 Case
  . prove_graph_iso G and P3_graph
      using (fun | 0 => 2 | 2 => 0 | 1 => 1) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

  -- 6. E3 Case
  . prove_graph_iso G and E3_graph
      using (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)

  -- 7. E3 Case
  . prove_graph_iso G and E3_graph
      using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)

  -- 8. O3 Case
  . prove_graph_iso G and O3_graph
      using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)

/- labeledGraphs with empty type -/

lemma labeledGraph_not_iso_from_graph_not_iso
    {ℓ : ℕ} {σ : FlagType (Fin ℓ)} {V : Type} [Fintype V]
    {G₁ : LabeledGraph σ V} {G₂ : LabeledGraph σ V}
    (h : ¬ Nonempty (G₁.graph ≃g G₂.graph))
    : ¬ (G₁ ∼f G₂)
  := by
  intro h_G
  exact h (Nonempty.intro h_G.some.graph_iso)

@[simp]
lemma O3_E3_not_iso : ¬ O3_labeledGraph ∼f E3_labeledGraph
  := labeledGraph_not_iso_from_graph_not_iso O3_E3_graph_not_iso

@[simp]
lemma O3_P3_not_iso : ¬ O3_labeledGraph ∼f P3_labeledGraph
  := labeledGraph_not_iso_from_graph_not_iso O3_P3_graph_not_iso

@[simp]
lemma O3_K3_not_iso : ¬ O3_labeledGraph ∼f K3_labeledGraph
  := labeledGraph_not_iso_from_graph_not_iso O3_K3_graph_not_iso

@[simp]
lemma E3_P3_not_iso : ¬ E3_labeledGraph ∼f P3_labeledGraph
  := labeledGraph_not_iso_from_graph_not_iso E3_P3_graph_not_iso

@[simp]
lemma E3_K3_not_iso : ¬ E3_labeledGraph ∼f K3_labeledGraph
  := labeledGraph_not_iso_from_graph_not_iso E3_K3_graph_not_iso

@[simp]
lemma P3_K3_not_iso : ¬ P3_labeledGraph ∼f K3_labeledGraph
  := labeledGraph_not_iso_from_graph_not_iso P3_K3_graph_not_iso

syntax "prove_labeledGraph_iso_emptyType" term "and" term "using" term : tactic

macro_rules
| `(tactic| prove_labeledGraph_iso_emptyType $source and $target using $map) => `(tactic|
    {
      have : $source ∼f $target := by
        apply Nonempty.intro
        exact {
          graph_iso := $map
          type_preserve := by
            funext i
            apply False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      simp_all [this]
    })

lemma emptyTypeThreeVertexLabeledGraph_eqv
    (G : LabeledGraph ∅ₜ (Fin 3))
    : G ∼f O3_labeledGraph ∨ G ∼f E3_labeledGraph ∨ G ∼f P3_labeledGraph ∨ G ∼f K3_labeledGraph
  := by
  rcases (threeVertexGraph_iso G.graph) with h | h | h | h
  · prove_labeledGraph_iso_emptyType G and O3_labeledGraph using h.some
  · prove_labeledGraph_iso_emptyType G and E3_labeledGraph using h.some
  · prove_labeledGraph_iso_emptyType G and P3_labeledGraph using h.some
  · prove_labeledGraph_iso_emptyType G and K3_labeledGraph using h.some

syntax "prove_nodup_of_flagSet" : tactic

macro_rules
| `(tactic| prove_nodup_of_flagSet) => `(tactic|
    {
        simp
        (repeat' constructor) <;> {
          intro h
          have : _ ∼f _ := Quotient.exact h
          simp_all
        }
    })

syntax "prove_flagSet_eq_univ" term "on" term "using" term "and" "[" term,* "]" : tactic

macro_rules
| `(tactic| prove_flagSet_eq_univ $flag_set on $flag_type using $get_cases and [ $[$flag:term],* ]) => `(tactic|
    {
      dsimp [$flag_set:term]
      ext F; constructor
      · intro _
        exact Finset.mem_univ F
      · intro _
        (first
         | (rcases ($get_cases F.out) with h | h | h | h) <;> {
              have : (_ : $flag_type) = _ := Quotient.sound h
              simp_all [$[$flag:term],*]
           }
         | (rcases ($get_cases F.out) with h | h | h | h | h | h) <;> {
              have : (_ : $flag_type) = _ := Quotient.sound h
              simp_all [$[$flag:term],*]
           })
    })

def emptyTypeThreeVertexFlagSet : Finset (FlagWithSize ∅ₜ 3) where
  val := [O3_flag, E3_flag, P3_flag, K3_flag]
  nodup := by prove_nodup_of_flagSet

theorem emptyTypeThreeVertexFlagSet_eq_univ : emptyTypeThreeVertexFlagSet = Finset.univ
  := by
  prove_flagSet_eq_univ emptyTypeThreeVertexFlagSet on FlagAlgebras.Flag ∅ₜ (Fin 3)
    using emptyTypeThreeVertexLabeledGraph_eqv and [O3_flag, E3_flag, P3_flag, K3_flag]

/- labeledGraphs with singleton type -/

@[simp]
lemma O3₁_E3₁_not_iso : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso O3_E3_graph_not_iso

@[simp]
lemma O3₁_E3₁'_not_iso : ¬ O3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := labeledGraph_not_iso_from_graph_not_iso O3_E3_graph_not_iso

@[simp]
lemma O3₁_P3₁_not_iso : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso O3_P3_graph_not_iso

@[simp]
lemma O3₁_P3₁'_not_iso : ¬ O3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := labeledGraph_not_iso_from_graph_not_iso O3_P3_graph_not_iso

@[simp]
lemma O3₁_K3₁_not_iso : ¬ O3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso O3_K3_graph_not_iso

@[simp]
lemma E3₁_E3₁'_not_iso : ¬ E3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
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

@[simp]
lemma E3₁_P3₁_not_iso : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso E3_P3_graph_not_iso

@[simp]
lemma E3₁_P3₁'_not_iso : ¬ E3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := labeledGraph_not_iso_from_graph_not_iso E3_P3_graph_not_iso

@[simp]
lemma E3₁_K3₁_not_iso : ¬ E3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso E3_K3_graph_not_iso

@[simp]
lemma E3₁'_P3₁_not_iso : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso E3_P3_graph_not_iso

@[simp]
lemma E3₁'_P3₁'_not_iso : ¬ E3₁_labeledGraph 2 ∼f P3₁_labeledGraph 1
  := labeledGraph_not_iso_from_graph_not_iso E3_P3_graph_not_iso

@[simp]
lemma E3₁'_K3₁_not_iso : ¬ E3₁_labeledGraph 2 ∼f K3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso E3_K3_graph_not_iso

@[simp]
lemma P3₁_P3₁'_not_iso : ¬ P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
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

@[simp]
lemma P3₁_K3₁_not_iso : ¬ P3₁_labeledGraph 0 ∼f K3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso P3_K3_graph_not_iso

@[simp]
lemma P3₁'_K3₁_not_iso : ¬ P3₁_labeledGraph 1 ∼f K3₁_labeledGraph 0
  := labeledGraph_not_iso_from_graph_not_iso P3_K3_graph_not_iso

syntax "get_Adj_from_graph_iso_on_Fin3" term : tactic

macro_rules
| `(tactic| get_Adj_from_graph_iso_on_Fin3 $graph_iso:term) => `(tactic|
    {
      rcases (all_isomorphism_on_Fin3 $graph_iso) with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
      <;> (simp at h₀ h₁ h₂; simp [← SimpleGraph.Iso.map_adj_iff $graph_iso, h₀, h₁, h₂])
    })

syntax "prove_labeledGraph_iso_singletonType" term "and" term "on" term "using" term "and" term : tactic

macro_rules
| `(tactic| prove_labeledGraph_iso_singletonType $source and $target on $labeled_graph using $map1 and $map2) => `(tactic|
    {
      have : $source ∼f $target := by
        apply Nonempty.intro
        exact {
          graph_iso := by
            dsimp [$labeled_graph:term]
            exact {
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
            dsimp [$labeled_graph:term]
            funext i
            simp_all [Fin.fin_one_eq_zero i]
        }
      simp_all [this]
    })

lemma singletonType_O3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g O3_graph)
    : G ∼f O3₁_labeledGraph 0
  := by
  have h : ¬ G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2 := by get_Adj_from_graph_iso_on_Fin3 φ
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := h
  match ht : G.type_embed 0 with
  | 0 => prove_labeledGraph_iso_singletonType G and (O3₁_labeledGraph 0) on O3₁_labeledGraph
           using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
  | 1 => prove_labeledGraph_iso_singletonType G and (O3₁_labeledGraph 0) on O3₁_labeledGraph
           using (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
  | 2 => prove_labeledGraph_iso_singletonType G and (O3₁_labeledGraph 0) on O3₁_labeledGraph
           using (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

lemma singletonType_E3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g E3_graph)
    : G ∼f E3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 2
  := by
  have h : (G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2) ∨
      (¬ G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2) ∨
      (¬ G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2) := by get_Adj_from_graph_iso_on_Fin3 φ
  rcases h with ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩
  . match ht : G.type_embed 0 with
    | 0 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 0) on E3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
    | 1 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 0) on E3₁_labeledGraph
        using (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
    | 2 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 2) on E3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
  · match ht : G.type_embed 0 with
    | 0 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 0) on E3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)
    | 1 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 2) on E3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)
    | 2 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 0) on E3₁_labeledGraph
        using (fun | 0 => 1 | 1 => 2 | 2 => 0) and (fun | 0 => 2 | 1 => 0 | 2 => 1)
  · match ht : G.type_embed 0 with
    | 0 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 2) on E3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)
    | 1 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 0) on E3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)
    | 2 =>
      prove_labeledGraph_iso_singletonType G and (E3₁_labeledGraph 0) on E3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

lemma singletonType_P3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g P3_graph)
    : G ∼f P3₁_labeledGraph 0 ∨ G ∼f P3₁_labeledGraph 1
  := by
  have h : (G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ ¬ G.graph.Adj 1 2) ∨
      (G.graph.Adj 0 1 ∧ ¬ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2) ∨
      (¬ G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2) := by get_Adj_from_graph_iso_on_Fin3 φ
  rcases h with ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩ | ⟨h₀₁, h₀₂, h₁₂⟩
  · match ht : G.type_embed 0 with
    | 0 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 0) on P3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
    | 1 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 1) on P3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
    | 2 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 1) on P3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 2 | 2 => 1) and (fun | 0 => 0 | 1 => 2 | 2 => 1)
  · match ht : G.type_embed 0 with
    | 0 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 1) on P3₁_labeledGraph
        using (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
    | 1 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 0) on P3₁_labeledGraph
        using (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
    | 2 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 1) on P3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 0 | 2 => 1) and (fun | 0 => 1 | 1 => 2 | 2 => 0)
  · match ht : G.type_embed 0 with
    | 0 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 1) on P3₁_labeledGraph
        using (fun | 0 => 1 | 1 => 2 | 2 => 0) and (fun | 0 => 2 | 1 => 0 | 2 => 1)
    | 1 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 1) on P3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)
    | 2 =>
      prove_labeledGraph_iso_singletonType G and (P3₁_labeledGraph 0) on P3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

lemma singletonType_K3_eqv
    (G : LabeledGraph Sₜ (Fin 3)) (φ : G.graph ≃g K3_graph)
    : G ∼f K3₁_labeledGraph 0
  := by
  have h : G.graph.Adj 0 1 ∧ G.graph.Adj 0 2 ∧ G.graph.Adj 1 2 := by get_Adj_from_graph_iso_on_Fin3 φ
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := h
  match ht : G.type_embed 0 with
  | 0 =>
      prove_labeledGraph_iso_singletonType G and (K3₁_labeledGraph 0) on K3₁_labeledGraph
        using (fun | 0 => 0 | 1 => 1 | 2 => 2) and (fun | 0 => 0 | 1 => 1 | 2 => 2)
  | 1 =>
      prove_labeledGraph_iso_singletonType G and (K3₁_labeledGraph 0) on K3₁_labeledGraph
        using (fun | 0 => 1 | 1 => 0 | 2 => 2) and (fun | 0 => 1 | 1 => 0 | 2 => 2)
  | 2 =>
      prove_labeledGraph_iso_singletonType G and (K3₁_labeledGraph 0) on K3₁_labeledGraph
        using (fun | 0 => 2 | 1 => 1 | 2 => 0) and (fun | 0 => 2 | 1 => 1 | 2 => 0)

lemma singletonTypeThreeVertexLabeledGraph_eqv
    (G : LabeledGraph Sₜ (Fin 3))
    : G ∼f O3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 0 ∨ G ∼f E3₁_labeledGraph 2 ∨
      G ∼f P3₁_labeledGraph 0 ∨ G ∼f P3₁_labeledGraph 1 ∨ G ∼f K3₁_labeledGraph 0
  := by
  rcases (threeVertexGraph_iso G.graph) with h | h | h | h
  <;> have φ := h.some
  · simp [singletonType_O3_eqv G φ]
  · rcases (singletonType_E3_eqv G φ) with h' | h' <;> simp [h']
  · rcases (singletonType_P3_eqv G φ) with h' | h' <;> simp [h']
  · simp [singletonType_K3_eqv G φ]

def singletonTypeThreeVertexFlagSet : Finset (FlagWithSize Sₜ 3) where
  val := [O3₁_flag, E3₁_flag, E3₁'_flag, P3₁_flag, P3₁'_flag, K3₁_flag]
  nodup := by prove_nodup_of_flagSet

lemma singletonTypeThreeVertexFlagSet_eq_univ : singletonTypeThreeVertexFlagSet = Finset.univ
  := by
  prove_flagSet_eq_univ singletonTypeThreeVertexFlagSet on FlagAlgebras.Flag Sₜ (Fin 3)
    using singletonTypeThreeVertexLabeledGraph_eqv and [E3₁'_flag, E3₁_flag, K3₁_flag, O3₁_flag, P3₁'_flag, P3₁_flag]

end Archive.MantelTheorem
