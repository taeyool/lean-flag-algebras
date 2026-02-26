import «LeanFlagAlgebras».FlagAlgebra.FlagOperators
import «LeanFlagAlgebras».Archive.Compute.Basic

open Lean
open Elab
open Command

open FlagAlgebras
open SimpleGraph
namespace Archive.MantelTheorem


/- flags with empty type -/

def K1_graph := completeGraph (Fin 1)

def O2_graph := emptyGraph (Fin 2)

def K2_graph := completeGraph (Fin 2)

def O3_graph := emptyGraph (Fin 3)

def K3_graph := completeGraph (Fin 3)

def O4_graph := emptyGraph (Fin 4)

def K4_graph := completeGraph (Fin 4)

def O5_graph := emptyGraph (Fin 5)

def K5_graph := completeGraph (Fin 5)

/- Macro for generating non-adjacency lemmas for empty graphs
 - (i) The generated lemmas are called `<empty_graph_name>_<i><j>` for distinct vertices `i`, `j`
 - (ii) These lemmas are used by the simp tactic.
 -/

syntax (name := mkNonAdjLemmasForEmptyGraph) "mk_non_adj_lemmas_for_empty_graph" ident num : command

@[command_elab mkNonAdjLemmasForEmptyGraph]
def elabMkNonAdjLemmasForEmptyGraph : CommandElab := fun stx => do
  let graphName := stx[1].getId
  let n ← match stx[2].isNatLit? with
    | some n => pure n
    | none => throwErrorAt stx[2] "expected a natural number literal"
  let graphTerm : TSyntax `term := mkIdent graphName
  let graphNameStr := graphName.toString
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        let thmName := mkIdent (Name.mkSimple s!"{graphNameStr}_{i}{j}")
        let iLit := Syntax.mkNumLit (toString i)
        let jLit := Syntax.mkNumLit (toString j)
        elabCommand <| ← `(
          @[simp] lemma $thmName : ¬ SimpleGraph.Adj $graphTerm $iLit $jLit := by rintro (_ | _)
        )

/- Instantiations of `<mk_non_adj_lemmas_for_empty_graph>` with O2_graph, O3_graph, O4_graph, O5_graph -/

mk_non_adj_lemmas_for_empty_graph O2_graph 2

mk_non_adj_lemmas_for_empty_graph O3_graph 3

mk_non_adj_lemmas_for_empty_graph O4_graph 4

mk_non_adj_lemmas_for_empty_graph O5_graph 5


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

inductive E4_edge : Fin 4 → Fin 4 → Prop
  | e01 : E4_edge 0 1
  | e10 : E4_edge 1 0

def E4_graph : SimpleGraph (Fin 4) where
  Adj := E4_edge
  symm := by
    rintro (_ | _ | _ | _) (_ | _ | _ | _) (_ | _ | _ | _)
    repeat' constructor
  loopless := by
    rintro (_ | _ | _ | _) (_ | _ | _ | _)

inductive E5_edge : Fin 5 → Fin 5 → Prop
  | e01 : E5_edge 0 1
  | e10 : E5_edge 1 0

def E5_graph : SimpleGraph (Fin 5) where
  Adj := E5_edge
  symm := by
    rintro (_ | _ | _ | _ | _) (_ | _ | _ | _ | _) (_ | _ | _ | _ | _)
    repeat' constructor
  loopless := by
    rintro (_ | _ | _ | _ | _) (_ | _ | _ | _ | _)

@[simp]
theorem E3_graph_01 : E3_graph.Adj 0 1 := E3_edge.e01

@[simp]
theorem E3_graph_10 : E3_graph.Adj 1 0 := E3_edge.e10

@[simp]
theorem E4_graph_01 : E4_graph.Adj 0 1 := E4_edge.e01

@[simp]
theorem E4_graph_10 : E4_graph.Adj 1 0 := E4_edge.e10

@[simp]
theorem E5_graph_01 : E5_graph.Adj 0 1 := E5_edge.e01

@[simp]
theorem E5_graph_10 : E5_graph.Adj 1 0 := E5_edge.e10

/- Macro for generating non-adjacency lemmas for one-edge graphs
 - (i) The generated lemmas are called `<one_edge_graph_name>_<i><j>` for distinct vertices `i`, `j`
 - (ii) These lemmas are used by the simp tactic.
 -/

syntax (name := mkNonAdjLemmasForOneEdgeGraph) "mk_non_adj_lemmas_for_one_edge_graph" ident num : command

@[command_elab mkNonAdjLemmasForOneEdgeGraph]
def elabMkNonAdjLemmasForOneEdgeGraph : CommandElab := fun stx => do
  let graphName := stx[1].getId
  let n ← match stx[2].isNatLit? with
    | some n => pure n
    | none => throwErrorAt stx[2] "expected a natural number literal"
  let graphTerm : TSyntax `term := mkIdent graphName
  let graphNameStr := graphName.toString
  for i in [0:n] do
    for j in [0:n] do
      if i ≠ j ∧ ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then
        let thmName := mkIdent (Name.mkSimple s!"{graphNameStr}_{i}{j}")
        let iLit := Syntax.mkNumLit (toString i)
        let jLit := Syntax.mkNumLit (toString j)
        elabCommand <| ← `(
          @[simp] lemma $thmName : ¬ SimpleGraph.Adj $graphTerm $iLit $jLit := by rintro (_ | _)
        )

/- Instantiations of `<mk_non_adj_lemmas_for_one_edge_graph>` with E3_graph, E4_graph, E5_graph -/

mk_non_adj_lemmas_for_one_edge_graph E3_graph 3

mk_non_adj_lemmas_for_one_edge_graph E4_graph 4

mk_non_adj_lemmas_for_one_edge_graph E5_graph 5


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

instance : DecidableRel ∅ₜ.Adj := by
  intro a b
  exact .isFalse (by aesop)

def K1_labeledGraph : LabeledGraph ∅ₜ (Fin 1) where
  graph := K1_graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj K1_graph.Adj

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
theorem K1_labeledGraph_size : K1_labeledGraph.size = 1 := Fintype.card_fin 1

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

def K1_flag : Flag ∅ₜ (Fin 1) := ⟦K1_labeledGraph⟧

def O2_flag : Flag ∅ₜ (Fin 2) := ⟦O2_labeledGraph⟧

def K2_flag : Flag ∅ₜ (Fin 2) := ⟦K2_labeledGraph⟧

def O3_flag : Flag ∅ₜ (Fin 3) := ⟦O3_labeledGraph⟧

def E3_flag : Flag ∅ₜ (Fin 3) := ⟦E3_labeledGraph⟧

def P3_flag : Flag ∅ₜ (Fin 3) := ⟦P3_labeledGraph⟧

def K3_flag : Flag ∅ₜ (Fin 3) := ⟦K3_labeledGraph⟧

/-- a single-vertex graph -/
noncomputable def K1 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨1, K1_flag⟩⟧

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

instance : DecidableRel Sₜ.Adj := by
  intro a b
  exact .isFalse (by aesop)

@[simp]
def create_singletonType_labeledGraph {ℓ : ℕ} (G : SimpleGraph (Fin ℓ)) (label_idx : Fin ℓ) : LabeledGraph Sₜ (Fin ℓ) where
  graph := G
  type_embed := {
    toFun := fun _ => label_idx
    inj' := Function.injective_of_subsingleton fun _ => label_idx
    map_rel_iff' := by intros; simp only [Function.Embedding.coeFn_mk, SimpleGraph.irrefl, false_iff]; exact id
  }

def K1₁_labeledGraph : LabeledGraph Sₜ (Fin 1) :=
  create_singletonType_labeledGraph K1_graph 0

def O2₁_labeledGraph (label_idx : Fin 2) : LabeledGraph Sₜ (Fin 2) :=
  create_singletonType_labeledGraph O2_graph label_idx

def K2₁_labeledGraph (label_idx : Fin 2) : LabeledGraph Sₜ (Fin 2) :=
  create_singletonType_labeledGraph K2_graph label_idx

def O3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_singletonType_labeledGraph O3_graph label_idx

def E3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_singletonType_labeledGraph E3_graph label_idx

def P3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_singletonType_labeledGraph P3_graph label_idx

def K3₁_labeledGraph (label_idx : Fin 3) : LabeledGraph Sₜ (Fin 3) :=
  create_singletonType_labeledGraph K3_graph label_idx

@[simp]
theorem K1₁_labeledGraph_size
    : K1₁_labeledGraph.size = 1
  := Fintype.card_fin 1

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

def K1₁_flag : Flag Sₜ (Fin 1) :=
  ⟦K1₁_labeledGraph⟧

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

/-- one vertex graph with the vertex labeled -/
noncomputable def K1₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨1, K1₁_flag⟩⟧

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

@[simp]
def create_emptyType_sym2LabeledGraph {ℓ : ℕ}
      (edges : Finset (Sym2 (Fin ℓ))) (h : ∀ e ∈ edges, ¬e.IsDiag)
      : Sym2LabeledGraph ∅ₜ ℓ where
  edges := edges
  edges_valid := h
  type_embed := RelEmbedding.ofIsEmpty _ _

@[simp]
def create_singletonType_sym2LabeledGraph {ℓ : ℕ}
      (edges : Finset (Sym2 (Fin ℓ))) (h : ∀ e ∈ edges, ¬e.IsDiag) (label_idx : Fin ℓ)
      : Sym2LabeledGraph Sₜ ℓ where
  edges := edges
  edges_valid := h
  type_embed := {
    toFun := fun _ ↦ label_idx
    inj' := by
      intro a b h
      aesop
    map_rel_iff' := by
      intro a b
      aesop
  }

syntax "prove_labeledGraph_eq_sym2LabeledGraph" term "and" term "on" term "using" "[" term,* "]": tactic

-- prove $labeledSym_G.toLabeledGraph = $labeled_G
-- when both represent $G with the same labeling
--      and $G's edges are given by the list ($[$edge:term],*)
macro_rules
| `(tactic| prove_labeledGraph_eq_sym2LabeledGraph $labeled_G and $labeledSym_G on $G using [ $[$edge:term],* ]) => `(tactic|
    {
      simp only [$labeled_G:term, $G:term, $labeledSym_G:term,
        Sym2LabeledGraph.toLabeledGraph, create_emptyType_sym2LabeledGraph, create_singletonType_sym2LabeledGraph]
      congr
      · ext u v
        simp
        try {
          first
          | { revert u v; decide }
          | { aesop }
          | { constructor
              . rintro ⟨h, _⟩; (rcases h <;> try (rename_i h; rcases h))
                <;> simp_all [$[$edge:term],*]
              . rintro (_ | _) <;> decide }
        }
      · ext u v
        simp
        try {
          first
          | { revert u v; decide }
          | { aesop }
          | { constructor
              . rintro ⟨h, _⟩; (rcases h <;> try (rename_i h; rcases h))
                <;> simp_all [$[$edge:term],*]
              . rintro (_ | _) <;> decide }
        }
      try (exact proof_irrel_heq _ _)
    })

def K1_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 1 :=
  create_emptyType_sym2LabeledGraph ∅ (by aesop)

lemma K1_labeledGraph_eq : K1_sym2LabeledGraph.toLabeledGraph = K1_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph K1_labeledGraph and K1_sym2LabeledGraph on K1_graph
    using []

def O2_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 2 :=
  create_emptyType_sym2LabeledGraph ∅ (by aesop)

lemma O2_labeledGraph_eq : O2_sym2LabeledGraph.toLabeledGraph = O2_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph O2_labeledGraph and O2_sym2LabeledGraph on O2_graph
    using []

def K2_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 2 :=
  create_emptyType_sym2LabeledGraph { Sym2.mk (0, 1) } (by aesop)

lemma K2_labeledGraph_eq : K2_sym2LabeledGraph.toLabeledGraph = K2_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph K2_labeledGraph and K2_sym2LabeledGraph on K2_graph
    using []

def O3_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 3 :=
  create_emptyType_sym2LabeledGraph ∅ (by aesop)

lemma O3_labeledGraph_eq : O3_sym2LabeledGraph.toLabeledGraph = O3_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph O3_labeledGraph and O3_sym2LabeledGraph on O3_graph
    using []

def E3_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 3 :=
  create_emptyType_sym2LabeledGraph { Sym2.mk (0, 1) } (by aesop)

lemma E3_labeledGraph_eq : E3_sym2LabeledGraph.toLabeledGraph = E3_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph E3_labeledGraph and E3_sym2LabeledGraph on E3_graph
    using [E3_edge.e01, E3_edge.e10]

def P3_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 3 :=
  create_emptyType_sym2LabeledGraph { Sym2.mk (0, 1), Sym2.mk (0, 2) } (by aesop)

lemma P3_labeledGraph_eq : P3_sym2LabeledGraph.toLabeledGraph = P3_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph P3_labeledGraph and P3_sym2LabeledGraph on P3_graph
    using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

def K3_sym2LabeledGraph : Sym2LabeledGraph ∅ₜ 3 :=
  create_emptyType_sym2LabeledGraph { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) } (by aesop)

lemma K3_labeledGraph_eq : K3_sym2LabeledGraph.toLabeledGraph = K3_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph K3_labeledGraph and K3_sym2LabeledGraph on K3_graph
    using []

def K1₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 1 :=
  create_singletonType_sym2LabeledGraph {} (by aesop) 0

lemma K1₁_labeledGraph_eq : K1₁_sym2LabeledGraph.toLabeledGraph = K1₁_labeledGraph := by
  prove_labeledGraph_eq_sym2LabeledGraph K1₁_labeledGraph and K1₁_sym2LabeledGraph on K1_graph
    using []

def O2₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 2 :=
  create_singletonType_sym2LabeledGraph {} (by aesop) 0

lemma O2₁_labeledGraph_eq : O2₁_sym2LabeledGraph.toLabeledGraph = O2₁_labeledGraph 0 := by
  prove_labeledGraph_eq_sym2LabeledGraph O2₁_labeledGraph and O2₁_sym2LabeledGraph on O2_graph
    using []

def K2₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 2 :=
  create_singletonType_sym2LabeledGraph { Sym2.mk (0, 1) } (by aesop) 0

lemma K2₁_labeledGraph_eq : K2₁_sym2LabeledGraph.toLabeledGraph = K2₁_labeledGraph 0 := by
  prove_labeledGraph_eq_sym2LabeledGraph K2₁_labeledGraph and K2₁_sym2LabeledGraph on K2_graph
    using []

def O3₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 3 :=
  create_singletonType_sym2LabeledGraph {} (by aesop) 0

lemma O3₁_labeledGraph_eq : O3₁_sym2LabeledGraph.toLabeledGraph = O3₁_labeledGraph 0 := by
  prove_labeledGraph_eq_sym2LabeledGraph O3₁_labeledGraph and O3₁_sym2LabeledGraph on O3_graph
    using []

def E3₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 3 :=
  create_singletonType_sym2LabeledGraph { Sym2.mk (0, 1) } (by aesop) 0

lemma E3₁_labeledGraph_eq : E3₁_sym2LabeledGraph.toLabeledGraph = E3₁_labeledGraph 0 := by
  prove_labeledGraph_eq_sym2LabeledGraph E3₁_labeledGraph and E3₁_sym2LabeledGraph on E3_graph
    using [E3_edge.e01, E3_edge.e10]

def E3₁'_sym2LabeledGraph : Sym2LabeledGraph Sₜ 3 :=
  create_singletonType_sym2LabeledGraph { Sym2.mk (0, 1) } (by aesop) 2

lemma E3₁'_labeledGraph_eq : E3₁'_sym2LabeledGraph.toLabeledGraph = E3₁_labeledGraph 2 := by
  prove_labeledGraph_eq_sym2LabeledGraph E3₁_labeledGraph and E3₁'_sym2LabeledGraph on E3_graph
    using [E3_edge.e01, E3_edge.e10]

def P3₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 3 :=
  create_singletonType_sym2LabeledGraph { Sym2.mk (0, 1), Sym2.mk (0, 2) } (by aesop) 0

lemma P3₁_labeledGraph_eq : P3₁_sym2LabeledGraph.toLabeledGraph = P3₁_labeledGraph 0 := by
  prove_labeledGraph_eq_sym2LabeledGraph P3₁_labeledGraph and P3₁_sym2LabeledGraph on P3_graph
    using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

def P3₁'_sym2LabeledGraph : Sym2LabeledGraph Sₜ 3 :=
  create_singletonType_sym2LabeledGraph { Sym2.mk (0, 1), Sym2.mk (0, 2) } (by aesop) 1

lemma P3₁'_labeledGraph_eq : P3₁'_sym2LabeledGraph.toLabeledGraph = P3₁_labeledGraph 1 := by
  prove_labeledGraph_eq_sym2LabeledGraph P3₁_labeledGraph and P3₁'_sym2LabeledGraph on P3_graph
    using [P3_edge.e01, P3_edge.e10, P3_edge.e02, P3_edge.e20]

def K3₁_sym2LabeledGraph : Sym2LabeledGraph Sₜ 3 :=
  create_singletonType_sym2LabeledGraph { Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2) } (by aesop) 0

lemma K3₁_labeledGraph_eq : K3₁_sym2LabeledGraph.toLabeledGraph = K3₁_labeledGraph 0 := by
  prove_labeledGraph_eq_sym2LabeledGraph K3₁_labeledGraph and K3₁_sym2LabeledGraph on K3_graph
    using []

syntax "prove_flag_eq_sym2Flag" term "using" term: tactic

macro_rules
| `(tactic| prove_flag_eq_sym2Flag $Sym2F using $labeled_eq) => `(tactic|
    {
      dsimp [$Sym2F:term, Sym2Flag.toFlag, Sym2LabeledGraph.toFlag]
      rw [$labeled_eq:term]
      rfl
    })

def K1_Sym2Flag : Sym2Flag ∅ₜ 1 :=
  ⟦K1_sym2LabeledGraph⟧

lemma K1_eq : K1_Sym2Flag.toFlag = K1_flag := by
  prove_flag_eq_sym2Flag K1_Sym2Flag using K1_labeledGraph_eq

def O2_Sym2Flag : Sym2Flag ∅ₜ 2 :=
  ⟦O2_sym2LabeledGraph⟧

lemma O2_eq : O2_Sym2Flag.toFlag = O2_flag := by
  prove_flag_eq_sym2Flag O2_Sym2Flag using O2_labeledGraph_eq

def K2_Sym2Flag : Sym2Flag ∅ₜ 2 :=
  ⟦K2_sym2LabeledGraph⟧

lemma K2_eq : K2_Sym2Flag.toFlag = K2_flag := by
  prove_flag_eq_sym2Flag K2_Sym2Flag using K2_labeledGraph_eq

def O3_Sym2Flag : Sym2Flag ∅ₜ 3 :=
  ⟦O3_sym2LabeledGraph⟧

lemma O3_eq : O3_Sym2Flag.toFlag = O3_flag := by
  prove_flag_eq_sym2Flag O3_Sym2Flag using O3_labeledGraph_eq

def E3_Sym2Flag : Sym2Flag ∅ₜ 3 :=
  ⟦E3_sym2LabeledGraph⟧

lemma E3_eq : E3_Sym2Flag.toFlag = E3_flag := by
  prove_flag_eq_sym2Flag E3_Sym2Flag using E3_labeledGraph_eq

def P3_Sym2Flag : Sym2Flag ∅ₜ 3 :=
  ⟦P3_sym2LabeledGraph⟧

lemma P3_eq : P3_Sym2Flag.toFlag = P3_flag := by
  prove_flag_eq_sym2Flag P3_Sym2Flag using P3_labeledGraph_eq

def K3_Sym2Flag : Sym2Flag ∅ₜ 3 :=
  ⟦K3_sym2LabeledGraph⟧

lemma K3_eq : K3_Sym2Flag.toFlag = K3_flag := by
  prove_flag_eq_sym2Flag K3_Sym2Flag using K3_labeledGraph_eq

def K1₁_Sym2Flag : Sym2Flag Sₜ 1 :=
  ⟦K1₁_sym2LabeledGraph⟧

lemma K1₁_eq : K1₁_Sym2Flag.toFlag = K1₁_flag := by
  prove_flag_eq_sym2Flag K1₁_Sym2Flag using K1₁_labeledGraph_eq

def O2₁_Sym2Flag : Sym2Flag Sₜ 2 :=
  ⟦O2₁_sym2LabeledGraph⟧

lemma O2₁_eq : O2₁_Sym2Flag.toFlag = O2₁_flag := by
  prove_flag_eq_sym2Flag O2₁_Sym2Flag using O2₁_labeledGraph_eq

def K2₁_Sym2Flag : Sym2Flag Sₜ 2 :=
  ⟦K2₁_sym2LabeledGraph⟧

lemma K2₁_eq : K2₁_Sym2Flag.toFlag = K2₁_flag := by
  prove_flag_eq_sym2Flag K2₁_Sym2Flag using K2₁_labeledGraph_eq

def O3₁_Sym2Flag : Sym2Flag Sₜ 3 :=
  ⟦O3₁_sym2LabeledGraph⟧

lemma O3₁_eq : O3₁_Sym2Flag.toFlag = O3₁_flag := by
  prove_flag_eq_sym2Flag O3₁_Sym2Flag using O3₁_labeledGraph_eq

def E3₁_Sym2Flag : Sym2Flag Sₜ 3 :=
  ⟦E3₁_sym2LabeledGraph⟧

lemma E3₁_eq : E3₁_Sym2Flag.toFlag = E3₁_flag := by
  prove_flag_eq_sym2Flag E3₁_Sym2Flag using E3₁_labeledGraph_eq

def E3₁'_Sym2Flag : Sym2Flag Sₜ 3 :=
  ⟦E3₁'_sym2LabeledGraph⟧

lemma E3₁'_eq : E3₁'_Sym2Flag.toFlag = E3₁'_flag := by
  prove_flag_eq_sym2Flag E3₁'_Sym2Flag using E3₁'_labeledGraph_eq

def P3₁_Sym2Flag : Sym2Flag Sₜ 3 :=
  ⟦P3₁_sym2LabeledGraph⟧

lemma P3₁_eq : P3₁_Sym2Flag.toFlag = P3₁_flag := by
  prove_flag_eq_sym2Flag P3₁_Sym2Flag using P3₁_labeledGraph_eq

def P3₁'_Sym2Flag : Sym2Flag Sₜ 3 :=
  ⟦P3₁'_sym2LabeledGraph⟧

lemma P3₁'_eq : P3₁'_Sym2Flag.toFlag = P3₁'_flag := by
  prove_flag_eq_sym2Flag P3₁'_Sym2Flag using P3₁'_labeledGraph_eq

def K3₁_Sym2Flag : Sym2Flag Sₜ 3 :=
  ⟦K3₁_sym2LabeledGraph⟧

lemma K3₁_eq : K3₁_Sym2Flag.toFlag = K3₁_flag := by
  prove_flag_eq_sym2Flag K3₁_Sym2Flag using K3₁_labeledGraph_eq

end Archive.MantelTheorem
