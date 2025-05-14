import «LeanFlagAlgebras».PositiveHom

open FlagAlgebras

/- flags with empty type -/

def O2_graph := emptyGraph (Fin 2)

def K2_graph := completeGraph (Fin 2)

def O3_graph := emptyGraph (Fin 3)

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

def K3_graph := completeGraph (Fin 3)

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

noncomputable def O2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, ⟦O2_labeledGraph⟧⟩⟧

noncomputable def K2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, ⟦K2_labeledGraph⟧⟩⟧

noncomputable def O3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦O3_labeledGraph⟧⟩⟧

noncomputable def E3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦E3_labeledGraph⟧⟩⟧

noncomputable def P3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦P3_labeledGraph⟧⟩⟧

noncomputable def K3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦K3_labeledGraph⟧⟩⟧

/- flags with singleton type -/

def singletonType : FlagType (Fin 1) := emptyGraph (Fin 1)

alias Sₜ := singletonType

def O2₁_labeledGraph : LabeledGraph Sₜ (Fin 2) where
  graph := O2_graph
  type_embed := {
      toFun := fun _ => 0
      inj' := Function.injective_of_subsingleton fun _ => 0
      map_rel_iff' := by intros; simp; exact id
    }

def K2₁_labeledGraph : LabeledGraph Sₜ (Fin 2) where
  graph := K2_graph
  type_embed := {
      toFun := fun _ => 0
      inj' := Function.injective_of_subsingleton fun _ => 0
      map_rel_iff' := by intros; simp; exact id
    }

def O3₁_labeledGraph : LabeledGraph Sₜ (Fin 3) where
  graph := O3_graph
  type_embed := {
      toFun := fun _ => 0
      inj' := Function.injective_of_subsingleton fun _ => 0
      map_rel_iff' := by intros; simp; exact id
    }

def E3₁_labeledGraph : LabeledGraph Sₜ (Fin 3) where
  graph := E3_graph
  type_embed := {
      toFun := fun _ => 0
      inj' := Function.injective_of_subsingleton fun _ => 0
      map_rel_iff' := by intros; simp; exact id
    }

def E3₁'_labeledGraph : LabeledGraph Sₜ (Fin 3) where
  graph := E3_graph
  type_embed := {
      toFun := fun _ => 2
      inj' := Function.injective_of_subsingleton fun _ => 2
      map_rel_iff' := by intros; simp; exact id
    }

def P3₁_labeledGraph : LabeledGraph Sₜ (Fin 3) where
  graph := P3_graph
  type_embed := {
      toFun := fun _ => 0
      inj' := Function.injective_of_subsingleton fun _ => 0
      map_rel_iff' := by intros; simp; exact id
    }

def P3₁'_labeledGraph : LabeledGraph Sₜ (Fin 3) where
  graph := P3_graph
  type_embed := {
      toFun := fun _ => 1
      inj' := Function.injective_of_subsingleton fun _ => 1
      map_rel_iff' := by intros; simp; exact id
    }

def K3₁_labeledGraph : LabeledGraph Sₜ (Fin 3) where
  graph := K3_graph
  type_embed := {
      toFun := fun _ => 0
      inj' := Function.injective_of_subsingleton fun _ => 0
      map_rel_iff' := by intros; simp; exact id
    }

noncomputable def O2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, ⟦O2₁_labeledGraph⟧⟩⟧

noncomputable def K2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, ⟦K2₁_labeledGraph⟧⟩⟧

noncomputable def O3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦O3₁_labeledGraph⟧⟩⟧

noncomputable def E3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦E3₁_labeledGraph⟧⟩⟧

noncomputable def E3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦E3₁'_labeledGraph⟧⟩⟧

noncomputable def P3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦P3₁_labeledGraph⟧⟩⟧

noncomputable def P3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦P3₁'_labeledGraph⟧⟩⟧

noncomputable def K3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦K3₁_labeledGraph⟧⟩⟧

/- downward operations -/

lemma unlabel_O3₁
    : unlabel ⟦O3₁_labeledGraph⟧ = ⟦O3_labeledGraph⟧
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph O3₁_labeledGraph := by
      apply unlabeledGraph_iso
      exact Quotient.mk_out O3₁_labeledGraph
    _ ∼f O3_labeledGraph := by
      dsimp [unlabeledGraph, O3₁_labeledGraph, O3_labeledGraph]
      apply flagEqv.refl

lemma downwardNormalizingFactor_O3₁
    : downwardNormalizingFactor ⟦O3₁_labeledGraph⟧ = 1
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount]
  sorry

lemma downwardFlagVectorQuot_O3₁
    : downwardFlagVector (unitVector ⟨3, ⟦O3₁_labeledGraph⟧⟩) = unitVector ⟨3, ⟦O3_labeledGraph⟧⟩
  := by
  simp [downwardFlagVector, downwardFlag]
  simp [unlabel_O3₁, downwardNormalizingFactor_O3₁]

lemma downward_O3₁
    : ⟦O3₁⟧₀ = O3
  := by
  dsimp [O3₁, downward, O3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_O3₁]

/- proof of Mantel's theorem -/

theorem mantel_theorem
    : K2 ≤ (1 / 2) • 1 + K3
  :=
  sorry
