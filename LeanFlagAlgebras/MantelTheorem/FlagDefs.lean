import «LeanFlagAlgebras».FlagOperators
import «LeanFlagAlgebras».Compute.Downward

open FlagAlgebras
open SimpleGraph

namespace MantelTheorem

/- flags with empty type -/

def O2_graph := emptyGraph (Fin 2)

def K2_graph := completeGraph (Fin 2)

def O3_graph := emptyGraph (Fin 3)

@[simp]
theorem O3_graph_01 : ¬ O3_graph.Adj 0 1 := by rintro (_ | _)

@[simp]
theorem O3_graph_10 : ¬ O3_graph.Adj 1 0 := by rintro (_ | _)

@[simp]
theorem O3_graph_02 : ¬ O3_graph.Adj 0 2 := by rintro (_ | _)

@[simp]
theorem O3_graph_20 : ¬ O3_graph.Adj 2 0 := by rintro (_ | _)

@[simp]
theorem O3_graph_12 : ¬ O3_graph.Adj 1 2 := by rintro (_ | _)

@[simp]
theorem O3_graph_21 : ¬ O3_graph.Adj 2 1 := by rintro (_ | _)

inductive E3_edge : Fin 3 → Fin 3 → Prop
  | e01 : E3_edge 0 1
  | e10 : E3_edge 1 0

def E3_graph : SimpleGraph (Fin 3) where
  Adj := E3_edge
  symm := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _)
    repeat' constructor
  loopless := by
    rintro (_ | _ | _) (_ | _)

@[simp]
theorem E3_graph_01 : E3_graph.Adj 0 1 := E3_edge.e01

@[simp]
theorem E3_graph_10 : E3_graph.Adj 1 0 := E3_edge.e10

@[simp]
theorem E3_graph_02 : ¬ E3_graph.Adj 0 2 := by rintro (_ | _)

@[simp]
theorem E3_graph_20 : ¬ E3_graph.Adj 2 0 := by rintro (_ | _)

@[simp]
theorem E3_graph_12 : ¬ E3_graph.Adj 1 2 := by rintro (_ | _)

@[simp]
theorem E3_graph_21 : ¬ E3_graph.Adj 2 1 := by rintro (_ | _)

inductive P3_edge : Fin 3 → Fin 3 → Prop
  | e01 : P3_edge 0 1
  | e10 : P3_edge 1 0
  | e02 : P3_edge 0 2
  | e20 : P3_edge 2 0

def P3_graph : SimpleGraph (Fin 3) where
  Adj := P3_edge
  symm := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _)
    repeat' constructor
  loopless := by
    rintro (_ | _ | _) (_ | _)

@[simp]
theorem P3_graph_01 : P3_graph.Adj 0 1 := P3_edge.e01

@[simp]
theorem P3_graph_10 : P3_graph.Adj 1 0 := P3_edge.e10

@[simp]
theorem P3_graph_02 : P3_graph.Adj 0 2 := P3_edge.e02

@[simp]
theorem P3_graph_20 : P3_graph.Adj 2 0 := P3_edge.e20

@[simp]
theorem P3_graph_12 : ¬ P3_graph.Adj 1 2 := by rintro (_ | _)

@[simp]
theorem P3_graph_21 : ¬ P3_graph.Adj 2 1 := by rintro (_ | _)

def K3_graph := completeGraph (Fin 3)

@[simp]
theorem K3_graph_01 : K3_graph.Adj 0 1 := by rintro (_ | _)

@[simp]
theorem K3_graph_10 : K3_graph.Adj 1 0 := by rintro (_ | _)

@[simp]
theorem K3_graph_02 : K3_graph.Adj 0 2 := by rintro (_ | _)

@[simp]
theorem K3_graph_20 : K3_graph.Adj 2 0 := by rintro (_ | _)

@[simp]
theorem K3_graph_12 : K3_graph.Adj 1 2 := by rintro (_ | _)

@[simp]
theorem K3_graph_21 : K3_graph.Adj 2 1 := by rintro (_ | _)

def O2_labeledGraph : LabeledGraph ∅ₜ (Fin 2) where
  graph := O2_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj O2_graph.Adj

def K2_labeledGraph : LabeledGraph ∅ₜ (Fin 2) where
  graph := K2_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj K2_graph.Adj

def O3_labeledGraph : LabeledGraph ∅ₜ (Fin 3) where
  graph := O3_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj O3_graph.Adj

def E3_labeledGraph : LabeledGraph ∅ₜ (Fin 3) where
  graph := E3_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj E3_graph.Adj

def P3_labeledGraph : LabeledGraph ∅ₜ (Fin 3) where
  graph := P3_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj P3_graph.Adj

def K3_labeledGraph : LabeledGraph ∅ₜ (Fin 3) where
  graph := K3_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj K3_graph.Adj

@[simp]
theorem O2_labeledGraph_size : O2_labeledGraph.size = 2 := Fintype.card_fin 2

@[simp]
theorem K2_labeledGraph_size : K2_labeledGraph.size = 2 := Fintype.card_fin 2

@[simp]
theorem O3_labeledGraph_size : O3_labeledGraph.size = 3 := Fintype.card_fin 3

@[simp]
theorem E3_labeledGraph_size : E3_labeledGraph.size = 3 := Fintype.card_fin 3

@[simp]
theorem P3_labeledGraph_size : P3_labeledGraph.size = 3 := Fintype.card_fin 3

@[simp]
theorem K3_labeledGraph_size : K3_labeledGraph.size = 3 := Fintype.card_fin 3

def O2_flag : Flag ∅ₜ (Fin 2) :=
  ⟦O2_labeledGraph⟧

def K2_flag : Flag ∅ₜ (Fin 2) :=
  ⟦K2_labeledGraph⟧

def O3_flag : Flag ∅ₜ (Fin 3) :=
  ⟦O3_labeledGraph⟧

def E3_flag : Flag ∅ₜ (Fin 3) :=
  ⟦E3_labeledGraph⟧

def P3_flag : Flag ∅ₜ (Fin 3) :=
  ⟦P3_labeledGraph⟧

def K3_flag : Flag ∅ₜ (Fin 3) :=
  ⟦K3_labeledGraph⟧

/-- a non-edge -/
noncomputable def O2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, O2_flag⟩⟧

/-- an edge -/
noncomputable def K2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, K2_flag⟩⟧

/-- an empty graph with 3 vertices -/
noncomputable def O3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, O3_flag⟩⟧

/-- an edge and an isolated vertex -/
noncomputable def E3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, E3_flag⟩⟧

/-- a path of length 2 (3 vertices) -/
noncomputable def P3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, P3_flag⟩⟧

/-- a complete graph with 3 vertices -/
noncomputable def K3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, K3_flag⟩⟧

/- flags with singleton type -/

def singletonType : FlagType (Fin 1) := emptyGraph (Fin 1)

alias Sₜ := singletonType

@[simp]
theorem singletonType_size : Sₜ.size = 1 := Fintype.card_fin 1

@[simp]
def create_Sₜ_labeledGraph {ℓ : ℕ} (G : SimpleGraph (Fin ℓ)) (label_idx : Fin ℓ) : LabeledGraph Sₜ (Fin ℓ) where
  graph := G
  type_embed := {
    toFun := fun _ => label_idx
    inj' := Function.injective_of_subsingleton fun _ => label_idx
    map_rel_iff' := by intros; simp only [Function.Embedding.coeFn_mk, SimpleGraph.irrefl, false_iff]; exact id
  }

def O2₁_labeledGraph (label_idx : Fin 2) : LabeledGraph Sₜ (Fin 2) :=
  create_Sₜ_labeledGraph O2_graph label_idx

def K2₁_labeledGraph (label_idx : Fin 2) : LabeledGraph Sₜ (Fin 2) :=
  create_Sₜ_labeledGraph K2_graph label_idx

def O3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_Sₜ_labeledGraph O3_graph label_idx

def E3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_Sₜ_labeledGraph E3_graph label_idx

def P3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_Sₜ_labeledGraph P3_graph label_idx

def K3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_Sₜ_labeledGraph K3_graph label_idx

@[simp]
theorem O2₁_labeledGraph_size (label_idx : Fin 2)
    : (O2₁_labeledGraph label_idx).size = 2
  := Fintype.card_fin 2

@[simp]
theorem K2₁_labeledGraph_size (label_idx : Fin 2)
    : (K2₁_labeledGraph label_idx).size = 2
  := Fintype.card_fin 2

@[simp]
theorem O3₁_labeledGraph_size (label_idx : Fin 3)
    : (O3₁_labeledGraph label_idx).size = 3
  := Fintype.card_fin 3

@[simp]
theorem E3₁_labeledGraph_size (label_idx : Fin 3)
    : (E3₁_labeledGraph label_idx).size = 3
  := Fintype.card_fin 3

@[simp]
theorem P3₁_labeledGraph_size (label_idx : Fin 3)
    : (P3₁_labeledGraph label_idx).size = 3
  := Fintype.card_fin 3

@[simp]
theorem K3₁_labeledGraph_size (label_idx : Fin 3)
    : (K3₁_labeledGraph label_idx).size = 3
  := Fintype.card_fin 3

def O2₁_flag : Flag Sₜ (Fin 2) :=
  ⟦O2₁_labeledGraph 0⟧

def K2₁_flag : Flag Sₜ (Fin 2) :=
  ⟦K2₁_labeledGraph 0⟧

def O3₁_flag : Flag Sₜ (Fin 3) :=
  ⟦O3₁_labeledGraph 0⟧

def E3₁_flag : Flag Sₜ (Fin 3) :=
  ⟦E3₁_labeledGraph 0⟧

def E3₁'_flag : Flag Sₜ (Fin 3) :=
  ⟦E3₁_labeledGraph 2⟧

def P3₁_flag : Flag Sₜ (Fin 3) :=
  ⟦P3₁_labeledGraph 0⟧

def P3₁'_flag : Flag Sₜ (Fin 3) :=
  ⟦P3₁_labeledGraph 1⟧

def K3₁_flag : Flag Sₜ (Fin 3) :=
  ⟦K3₁_labeledGraph 0⟧

/-- a non-edge with one labeled vertex -/
noncomputable def O2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, O2₁_flag⟩⟧

/-- an edge with one labeled vertex -/
noncomputable def K2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, K2₁_flag⟩⟧

/-- an empty graph with one labeled vertex -/
noncomputable def O3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, O3₁_flag⟩⟧

/-- an edge with one labeled vertex and an isolated vertex -/
noncomputable def E3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, E3₁_flag⟩⟧

/-- an edge and an isolated vertex with a label -/
noncomputable def E3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, E3₁'_flag⟩⟧

/-- a path of length 2 (3 vertices) with the middle vertex labeled -/
noncomputable def P3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, P3₁_flag⟩⟧

/-- a path of length 2 (3 vertices) where one of the endpoints is labeled -/
noncomputable def P3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, P3₁'_flag⟩⟧

/-- a complete graph with one labeled vertex -/
noncomputable def K3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, K3₁_flag⟩⟧


/- Sym2 version of labeledGraphs -/

open Compute

syntax "prove_labeledGraph_eq_labeledSym2Graph" term "and" term "on" term ("using" "[" term,* "]")?: tactic

macro_rules
| `(tactic| prove_labeledGraph_eq_labeledSym2Graph $labeled_G and $labeledSym_G on $G) => `(tactic|
    {
      simp only [$labeled_G:term, $G:term, $labeledSym_G:term, LabeledSym2Graph.toLabeledGraph]
      congr
      . ext u v; simp; try (revert u v; decide)
      . ext u v; simp; try (revert u v; decide)
    })
| `(tactic| prove_labeledGraph_eq_labeledSym2Graph $labeled_G and $labeledSym_G on $G using [ $[$edge:term],* ]) => `(tactic|
    {
      simp only [$labeled_G:term, $G:term, $labeledSym_G:term, LabeledSym2Graph.toLabeledGraph]
      congr
      · ext u v
        simp
        constructor
        . rintro ⟨h, _⟩; (rcases h <;> try (rename_i h; rcases h))
          <;> simp_all [$[$edge:term],*]
        . rintro (_ | _) <;> decide
      · ext u v
        simp
        constructor
        . rintro ⟨h, _⟩; (rcases h <;> try (rename_i h; rcases h))
          <;> simp_all [$[$edge:term],*]
        . rintro (_ | _) <;> decide
      try (exact proof_irrel_heq _ _)
    })

def O2_labeledSym2Graph : LabeledSym2Graph ∅ₜ 2 where
  edges := ∅
  edges_valid := by aesop
  type_embed := RelEmbedding.ofIsEmpty _ _

lemma O2_eq : O2_labeledSym2Graph.toLabeledGraph = O2_labeledGraph := by
  prove_labeledGraph_eq_labeledSym2Graph O2_labeledGraph and O2_labeledSym2Graph on O2_graph

def K2_labeledSym2Graph : LabeledSym2Graph ∅ₜ 2 where
  edges := { Sym2.mk (0, 1) }
  edges_valid := by aesop
  type_embed := RelEmbedding.ofIsEmpty _ _

lemma K2_eq : K2_labeledSym2Graph.toLabeledGraph = K2_labeledGraph := by
  prove_labeledGraph_eq_labeledSym2Graph K2_labeledGraph and K2_labeledSym2Graph on K2_graph

def O3_labeledSym2Graph : LabeledSym2Graph ∅ₜ 3 where
  edges := ∅
  edges_valid := by aesop
  type_embed := RelEmbedding.ofIsEmpty _ _

lemma O3_eq : O3_labeledSym2Graph.toLabeledGraph = O3_labeledGraph := by
  prove_labeledGraph_eq_labeledSym2Graph O3_labeledGraph and O3_labeledSym2Graph on O3_graph

def E3_labeledSym2Graph : LabeledSym2Graph ∅ₜ 3 where
  edges := { Sym2.mk (0, 1) }
  edges_valid := by aesop
  type_embed := RelEmbedding.ofIsEmpty _ _

lemma E3_eq : E3_labeledSym2Graph.toLabeledGraph = E3_labeledGraph := by
  prove_labeledGraph_eq_labeledSym2Graph E3_labeledGraph and E3_labeledSym2Graph on E3_graph
    using [E3_edge.e01, E3_edge.e10]

def P3_labeledSym2Graph : LabeledSym2Graph ∅ₜ 3 where
  edges := { Sym2.mk (0, 1), Sym2.mk (0, 2) }
  edges_valid := by aesop
  type_embed := RelEmbedding.ofIsEmpty _ _

lemma P3_eq : P3_labeledSym2Graph.toLabeledGraph = P3_labeledGraph := by
  prove_labeledGraph_eq_labeledSym2Graph P3_labeledGraph and P3_labeledSym2Graph on P3_graph
    using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

def K3_labeledSym2Graph : LabeledSym2Graph ∅ₜ 3 where
  edges := { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) }
  edges_valid := by aesop
  type_embed := RelEmbedding.ofIsEmpty _ _

lemma K3_eq : K3_labeledSym2Graph.toLabeledGraph = K3_labeledGraph := by
  prove_labeledGraph_eq_labeledSym2Graph K3_labeledGraph and K3_labeledSym2Graph on K3_graph

instance : DecidableRel Sₜ.Adj := by
  intro a b
  exact .isFalse (by aesop)

def O2₁_labeledSym2Graph : LabeledSym2Graph Sₜ 2 where
  edges := ∅
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma O2₁_eq : O2₁_labeledSym2Graph.toLabeledGraph = O2₁_labeledGraph 0 := by
  simp [O2₁_labeledGraph, O2_graph, O2₁_labeledSym2Graph, LabeledSym2Graph.toLabeledGraph]
  congr
  · ext u v; simp
  · aesop

def K2₁_labeledSym2Graph : LabeledSym2Graph Sₜ 2 where
  edges := { Sym2.mk (0, 1) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun x ↦ match x with
      | 0 => 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma K2₁_eq : K2₁_labeledSym2Graph.toLabeledGraph = K2₁_labeledGraph 0 := by
  simp only [K2₁_labeledGraph, K2_graph, K2₁_labeledSym2Graph, LabeledSym2Graph.toLabeledGraph]
  congr
  . ext u v; simp; revert u v; decide
  . ext u v; simp; revert u v; decide
  . aesop
  try exact proof_irrel_heq _ _

def O3₁_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := ∅
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma O3₁_eq : O3₁_labeledSym2Graph.toLabeledGraph = O3₁_labeledGraph 0 := by
  simp only [O3₁_labeledGraph, O3_graph, O3₁_labeledSym2Graph, LabeledSym2Graph.toLabeledGraph]
  congr
  . ext u v; simp
  . ext u v; simp
  . aesop
  try exact proof_irrel_heq _ _

def E3₁_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := { Sym2.mk (0, 1) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma E3₁_eq : E3₁_labeledSym2Graph.toLabeledGraph = E3₁_labeledGraph 0 := by
  prove_labeledGraph_eq_labeledSym2Graph E3₁_labeledGraph and E3₁_labeledSym2Graph on E3_graph
    using [E3_edge.e01, E3_edge.e10]

def E3₁'_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := { Sym2.mk (0, 1) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 2
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma E3₁'_eq : E3₁'_labeledSym2Graph.toLabeledGraph = E3₁_labeledGraph 2 := by
  prove_labeledGraph_eq_labeledSym2Graph E3₁_labeledGraph and E3₁'_labeledSym2Graph on E3_graph
    using [E3_edge.e01, E3_edge.e10]

def P3₁_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := { Sym2.mk (0, 1), Sym2.mk (0, 2) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma P3₁_eq : P3₁_labeledSym2Graph.toLabeledGraph = P3₁_labeledGraph 0 := by
  prove_labeledGraph_eq_labeledSym2Graph P3₁_labeledGraph and P3₁_labeledSym2Graph on P3_graph
    using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

def P3₁'_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := { Sym2.mk (0, 1), Sym2.mk (0, 2) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 1
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma P3₁'_eq : P3₁'_labeledSym2Graph.toLabeledGraph = P3₁_labeledGraph 1 := by
  prove_labeledGraph_eq_labeledSym2Graph P3₁_labeledGraph and P3₁'_labeledSym2Graph on P3_graph
    using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

def K3₁_labeledSym2Graph : LabeledSym2Graph Sₜ 3 where
  edges := { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) }
  edges_valid := by aesop
  type_embed := {
    toFun := fun _ ↦ 0
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

lemma K3₁_eq : K3₁_labeledSym2Graph.toLabeledGraph = K3₁_labeledGraph 0 := by
  simp only [K3₁_labeledGraph, K3_graph, K3₁_labeledSym2Graph, LabeledSym2Graph.toLabeledGraph]
  congr
  · ext u v; simp; revert u v; decide
  · ext u v; simp; revert u v; decide
  · aesop
  try exact proof_irrel_heq _ _

end MantelTheorem
