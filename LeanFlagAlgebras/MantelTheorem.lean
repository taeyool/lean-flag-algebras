import «LeanFlagAlgebras».PositiveHom

open FlagAlgebras

namespace MantelTheorem

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

/-- a non-edge -/
noncomputable def O2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, ⟦O2_labeledGraph⟧⟩⟧

/-- an edge -/
noncomputable def K2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, ⟦K2_labeledGraph⟧⟩⟧

/-- an empty graph with 3 vertices -/
noncomputable def O3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦O3_labeledGraph⟧⟩⟧

/-- an edge and an isolated vertex -/
noncomputable def E3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦E3_labeledGraph⟧⟩⟧

/-- a path of length 2 (3 vertices) -/
noncomputable def P3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦P3_labeledGraph⟧⟩⟧

/-- a complete graph with 3 vertices -/
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

/-- a non-edge with one labeled vertex -/
noncomputable def O2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, ⟦O2₁_labeledGraph⟧⟩⟧

/-- an edge with one labeled vertex -/
noncomputable def K2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, ⟦K2₁_labeledGraph⟧⟩⟧

/-- an empty graph with one labeled vertex -/
noncomputable def O3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦O3₁_labeledGraph⟧⟩⟧

/-- an edge with one labeled vertex and an isolated vertex -/
noncomputable def E3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦E3₁_labeledGraph⟧⟩⟧

/-- an edge and an isolated vertex with a label -/
noncomputable def E3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦E3₁'_labeledGraph⟧⟩⟧

/-- a path of length 2 (3 vertices) with the middle vertex labeled -/
noncomputable def P3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦P3₁_labeledGraph⟧⟩⟧

/-- a path of length 2 (3 vertices) where one of the endpoints is labeled -/
noncomputable def P3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦P3₁'_labeledGraph⟧⟩⟧

/-- a complete graph with one labeled vertex -/
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

@[simp]
theorem downward_O3₁
    : ⟦O3₁⟧₀ = O3
  := by
  dsimp [O3₁, downward, O3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_O3₁]

lemma unlabel_E3₁
    : unlabel ⟦E3₁_labeledGraph⟧ = ⟦E3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_E3₁
    : downwardNormalizingFactor ⟦E3₁_labeledGraph⟧ = 2 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_E3₁
    : downwardFlagVector (unitVector ⟨3, ⟦E3₁_labeledGraph⟧⟩) = (2 / 3 : ℝ) • unitVector ⟨3, ⟦E3_labeledGraph⟧⟩
  := by
  simp [downwardFlagVector, downwardFlag]
  simp [unlabel_E3₁, downwardNormalizingFactor_E3₁]

@[simp]
theorem downward_E3₁
    : ⟦E3₁⟧₀ = (2 / 3 : ℝ) • E3
  := by
  dsimp [E3₁, downward, E3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_E3₁]
  rfl

lemma unlabel_E3₁'
    : unlabel ⟦E3₁'_labeledGraph⟧ = ⟦E3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_E3₁'
    : downwardNormalizingFactor ⟦E3₁'_labeledGraph⟧ = 1 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_E3₁'
    : downwardFlagVector (unitVector ⟨3, ⟦E3₁'_labeledGraph⟧⟩) = (1 / 3 : ℝ) • unitVector ⟨3, ⟦E3_labeledGraph⟧⟩
  := by
  simp [downwardFlagVector, downwardFlag]
  simp [unlabel_E3₁', downwardNormalizingFactor_E3₁']

@[simp]
theorem downward_E3₁'
    : ⟦E3₁'⟧₀ = (1 / 3 : ℝ) • E3
  := by
  dsimp [E3₁', downward, E3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_E3₁']
  rfl

lemma unlabel_P3₁
    : unlabel ⟦P3₁_labeledGraph⟧ = ⟦P3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_P3₁
    : downwardNormalizingFactor ⟦P3₁_labeledGraph⟧ = 1 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_P3₁
    : downwardFlagVector (unitVector ⟨3, ⟦P3₁_labeledGraph⟧⟩) = (1 / 3 : ℝ) • unitVector ⟨3, ⟦P3_labeledGraph⟧⟩
  := by
  simp [downwardFlagVector, downwardFlag]
  simp [unlabel_P3₁, downwardNormalizingFactor_P3₁]

@[simp]
theorem downward_P3₁
    : ⟦P3₁⟧₀ = (1 / 3 : ℝ) • P3
  := by
  dsimp [P3₁, downward, P3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_P3₁]
  rfl

lemma unlabel_P3₁'
    : unlabel ⟦P3₁'_labeledGraph⟧ = ⟦P3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_P3₁'
    : downwardNormalizingFactor ⟦P3₁'_labeledGraph⟧ = 2 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_P3₁'
    : downwardFlagVector (unitVector ⟨3, ⟦P3₁'_labeledGraph⟧⟩) = (2 / 3 : ℝ) • unitVector ⟨3, ⟦P3_labeledGraph⟧⟩
  := by
  simp [downwardFlagVector, downwardFlag]
  simp [unlabel_P3₁', downwardNormalizingFactor_P3₁']

@[simp]
theorem downward_P3₁'
    : ⟦P3₁'⟧₀ = (2 / 3 : ℝ) • P3
  := by
  dsimp [P3₁', downward, P3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_P3₁']
  rfl

lemma unlabel_K3₁
    : unlabel ⟦K3₁_labeledGraph⟧ = ⟦K3_labeledGraph⟧
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph K3₁_labeledGraph := by
      apply unlabeledGraph_iso
      exact Quotient.mk_out K3₁_labeledGraph
    _ ∼f K3_labeledGraph := by
      dsimp [unlabeledGraph, K3₁_labeledGraph, K3_labeledGraph]
      apply flagEqv.refl

lemma downwardNormalizingFactor_K3₁
    : downwardNormalizingFactor ⟦K3₁_labeledGraph⟧ = 1
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount]
  sorry

lemma downwardFlagVectorQuot_K3₁
    : downwardFlagVector (unitVector ⟨3, ⟦K3₁_labeledGraph⟧⟩) = unitVector ⟨3, ⟦K3_labeledGraph⟧⟩
  := by
  simp [downwardFlagVector, downwardFlag]
  simp [unlabel_K3₁, downwardNormalizingFactor_K3₁]

@[simp]
theorem downward_K3₁
    : ⟦K3₁⟧₀ = K3
  := by
  dsimp [K3₁, downward, K3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_K3₁]

/- proof of Mantel's theorem -/

theorem mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  sorry

end MantelTheorem
