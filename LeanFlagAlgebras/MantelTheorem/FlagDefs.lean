import «LeanFlagAlgebras».FlagOperators

open FlagAlgebras

namespace MantelTheorem

/- flags with empty type -/

def O2_graph := emptyGraph (Fin 2)

def K2_graph := completeGraph (Fin 2)

def O3_graph := emptyGraph (Fin 3)

@[simp]
theorem O3_graph_01 : ¬ O3_graph.Adj 0 1 := by rintro (_ | _ | _)

@[simp]
theorem O3_graph_10 : ¬ O3_graph.Adj 1 0 := by rintro (_ | _ | _)

@[simp]
theorem O3_graph_02 : ¬ O3_graph.Adj 0 2 := by rintro (_ | _ | _)

@[simp]
theorem O3_graph_20 : ¬ O3_graph.Adj 2 0 := by rintro (_ | _ | _)

@[simp]
theorem O3_graph_12 : ¬ O3_graph.Adj 1 2 := by rintro (_ | _ | _)

@[simp]
theorem O3_graph_21 : ¬ O3_graph.Adj 2 1 := by rintro (_ | _ | _)

inductive E3_edge : Fin 3 → Fin 3 → Prop
  | e01 : E3_edge 0 1
  | e10 : E3_edge 1 0

def E3_graph : SimpleGraph (Fin 3) where
  Adj := E3_edge
  symm := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _ | _)
    repeat' constructor
  loopless := by
    rintro (_ | _ | _) (_ | _ | _)

@[simp]
theorem E3_graph_01 : E3_graph.Adj 0 1 := E3_edge.e01

@[simp]
theorem E3_graph_10 : E3_graph.Adj 1 0 := E3_edge.e10

@[simp]
theorem E3_graph_02 : ¬ E3_graph.Adj 0 2 := by rintro (_ | _ | _)

@[simp]
theorem E3_graph_20 : ¬ E3_graph.Adj 2 0 := by rintro (_ | _ | _)

@[simp]
theorem E3_graph_12 : ¬ E3_graph.Adj 1 2 := by rintro (_ | _ | _)

@[simp]
theorem E3_graph_21 : ¬ E3_graph.Adj 2 1 := by rintro (_ | _ | _)

inductive P3_edge : Fin 3 → Fin 3 → Prop
  | e01 : P3_edge 0 1
  | e10 : P3_edge 1 0
  | e02 : P3_edge 0 2
  | e20 : P3_edge 2 0

def P3_graph : SimpleGraph (Fin 3) where
  Adj := P3_edge
  symm := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _ | _)
    repeat' constructor
  loopless := by
    rintro (_ | _ | _) (_ | _ | _)

@[simp]
theorem P3_graph_01 : P3_graph.Adj 0 1 := P3_edge.e01

@[simp]
theorem P3_graph_10 : P3_graph.Adj 1 0 := P3_edge.e10

@[simp]
theorem P3_graph_02 : P3_graph.Adj 0 2 := P3_edge.e02

@[simp]
theorem P3_graph_20 : P3_graph.Adj 2 0 := P3_edge.e20

@[simp]
theorem P3_graph_12 : ¬ P3_graph.Adj 1 2 := by rintro (_ | _ | _)

@[simp]
theorem P3_graph_21 : ¬ P3_graph.Adj 2 1 := by rintro (_ | _ | _)

def K3_graph := completeGraph (Fin 3)

@[simp]
theorem K3_graph_01 : K3_graph.Adj 0 1 := by rintro (_ | _ | _)

@[simp]
theorem K3_graph_10 : K3_graph.Adj 1 0 := by rintro (_ | _ | _)

@[simp]
theorem K3_graph_02 : K3_graph.Adj 0 2 := by rintro (_ | _ | _)

@[simp]
theorem K3_graph_20 : K3_graph.Adj 2 0 := by rintro (_ | _ | _)

@[simp]
theorem K3_graph_12 : K3_graph.Adj 1 2 := by rintro (_ | _ | _)

@[simp]
theorem K3_graph_21 : K3_graph.Adj 2 1 := by rintro (_ | _ | _)

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
theorem singletonType_size : Sₜ.size = 1 := by
  dsimp [emptyType, FlagType.size]

def O2₁_labeledGraph (label_idx : Fin 2) : LabeledGraph Sₜ (Fin 2) where
  graph := O2_graph
  type_embed := {
      toFun := fun _ => label_idx
      inj' := Function.injective_of_subsingleton fun _ => label_idx
      map_rel_iff' := by intros; simp; exact id
    }

def K2₁_labeledGraph (label_idx : Fin 2) : LabeledGraph Sₜ (Fin 2) where
  graph := K2_graph
  type_embed := {
      toFun := fun _ => label_idx
      inj' := Function.injective_of_subsingleton fun _ => label_idx
      map_rel_iff' := by intros; simp; exact id
    }

def O3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) where
  graph := O3_graph
  type_embed := {
      toFun := fun _ => label_idx
      inj' := Function.injective_of_subsingleton fun _ => label_idx
      map_rel_iff' := by intros; simp; exact id
    }

def E3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) where
  graph := E3_graph
  type_embed := {
      toFun := fun _ => label_idx
      inj' := Function.injective_of_subsingleton fun _ => label_idx
      map_rel_iff' := by intros; simp; exact id
    }

def P3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) where
  graph := P3_graph
  type_embed := {
      toFun := fun _ => label_idx
      inj' := Function.injective_of_subsingleton fun _ => label_idx
      map_rel_iff' := by intros; simp; exact id
    }

def K3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) where
  graph := K3_graph
  type_embed := {
      toFun := fun _ => label_idx
      inj' := Function.injective_of_subsingleton fun _ => label_idx
      map_rel_iff' := by intros; simp; exact id
    }

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

end MantelTheorem
