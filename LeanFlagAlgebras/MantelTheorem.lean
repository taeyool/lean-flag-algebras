import «LeanFlagAlgebras».PositiveHom
import Mathlib.Tactic.FinCases

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

/-- a non-edge with one labeled vertex -/
noncomputable def O2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, ⟦O2₁_labeledGraph 0⟧⟩⟧

/-- an edge with one labeled vertex -/
noncomputable def K2₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨2, ⟦K2₁_labeledGraph 0⟧⟩⟧

/-- an empty graph with one labeled vertex -/
noncomputable def O3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦O3₁_labeledGraph 0⟧⟩⟧

/-- an edge with one labeled vertex and an isolated vertex -/
noncomputable def E3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦E3₁_labeledGraph 0⟧⟩⟧

/-- an edge and an isolated vertex with a label -/
noncomputable def E3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦E3₁_labeledGraph 2⟧⟩⟧

/-- a path of length 2 (3 vertices) with the middle vertex labeled -/
noncomputable def P3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦P3₁_labeledGraph 0⟧⟩⟧

/-- a path of length 2 (3 vertices) where one of the endpoints is labeled -/
noncomputable def P3₁' : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦P3₁_labeledGraph 1⟧⟩⟧

/-- a complete graph with one labeled vertex -/
noncomputable def K3₁ : FlagAlgebra Sₜ :=
  ⟦unitVector ⟨3, ⟦K3₁_labeledGraph 0⟧⟩⟧

/- downward operations -/

lemma unlabel_O3₁
    : unlabel ⟦O3₁_labeledGraph 0⟧ = ⟦O3_labeledGraph⟧
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (O3₁_labeledGraph 0) := by
      apply unlabeledGraph_iso
      exact Quotient.mk_out (O3₁_labeledGraph 0)
    _ ∼f O3_labeledGraph := by
      dsimp [unlabeledGraph, O3₁_labeledGraph, O3_labeledGraph]
      apply flagEqv.refl

def isoSet_O3₁
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {O3₁_labeledGraph 0, O3₁_labeledGraph 1, O3₁_labeledGraph 2}

instance : FintypeExist isoSet_O3₁
    := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑isoSet_O3₁) }

lemma isoSet_O3₁_card
    : isoSet_O3₁.toFinset.card = 3
  := by
  classical
  refine Finset.card_eq_three.mpr ?_
  use O3₁_labeledGraph 0, O3₁_labeledGraph 1, O3₁_labeledGraph 2
  have : O3₁_labeledGraph 0 ≠ O3₁_labeledGraph 1 := by
    simp [O3₁_labeledGraph]
    exact ne_of_beq_false rfl
  have : O3₁_labeledGraph 0 ≠ O3₁_labeledGraph 2 := by
    simp [O3₁_labeledGraph]
    exact ne_of_beq_false rfl
  have : O3₁_labeledGraph 1 ≠ O3₁_labeledGraph 2 := by
    simp [O3₁_labeledGraph]
    exact ne_of_beq_false rfl
  repeat' constructor <;> try assumption
  simp [isoSet_O3₁]

def O3₁_labeledGraph_0_1_iso
    : O3₁_labeledGraph 0 ≃f O3₁_labeledGraph 1 where
  graph_iso := {
    toFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
    invFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
    left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    map_rel_iff' := by intros; simp; rfl
  }
  type_preserve := by simp; rfl

def O3₁_labeledGraph_0_2_iso
    : O3₁_labeledGraph 0 ≃f O3₁_labeledGraph 2 where
  graph_iso := {
    toFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
    invFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
    left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    map_rel_iff' := by intros; simp; rfl
  }
  type_preserve := by simp; rfl

lemma fun_Fin1_Fin3
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

lemma type_embed_HEq
    {T V : Type} {σ : FlagType T} {G G' : SimpleGraph V} {f : σ ↪g G} {f' : σ ↪g G'}
    (hG : G = G') (hf : f.toFun = f'.toFun)
    : HEq f f'
  := by
  subst hG
  simp
  exact RelEmbedding.ext_iff.mpr (congrFun hf)

lemma isoLabeledGraphSetWithSameGraph_O3₁_eq_isoSet_O3₁_card
    : isoLabeledGraphSetWithSameGraph (O3₁_labeledGraph 0) = isoSet_O3₁
  := by
  dsimp [isoLabeledGraphSetWithSameGraph, isoSet_O3₁]
  ext H; constructor
  · intro h
    simp; simp [O3₁_labeledGraph] at h
    obtain ⟨h_graph, _⟩ := h
    rcases fun_Fin1_Fin3 H.type_embed with h₀ | (h₁ | h₂)
    · left
      ext1
      · simp [O3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [O3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · right; left
      ext1
      · simp [O3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [O3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · right; right
      ext1
      · simp [O3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [O3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
  · intro h
    rcases h with h₀ | (h₁ | h₂)
    · subst h₀
      simp
      exact flagEqv.refl (O3₁_labeledGraph 0)
    · subst h₁
      simp; constructor
      · dsimp [O3₁_labeledGraph]
      · exact Nonempty.intro O3₁_labeledGraph_0_1_iso
    · subst h₂
      simp; constructor
      · dsimp [O3₁_labeledGraph]
      · exact Nonempty.intro O3₁_labeledGraph_0_2_iso

lemma isoLabeledGraphSetWithSameGraph_O3₁_card
    : (isoLabeledGraphSetWithSameGraph (O3₁_labeledGraph 0)).toFinset.card = 3
  := by
  calc
    _ = isoSet_O3₁.toFinset.card := by
      simp [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_O3₁_eq_isoSet_O3₁_card]
    _ = 3 := isoSet_O3₁_card

lemma downwardNormalizingFactor_O3₁
    : downwardNormalizingFactor ⟦O3₁_labeledGraph 0⟧ = 1
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_O3₁_card, this]
  rfl

lemma downwardFlagVectorQuot_O3₁
    : downwardFlagVector (unitVector ⟨3, ⟦O3₁_labeledGraph 0⟧⟩) = unitVector ⟨3, ⟦O3_labeledGraph⟧⟩
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
    : unlabel ⟦E3₁_labeledGraph 0⟧ = ⟦E3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_E3₁
    : downwardNormalizingFactor ⟦E3₁_labeledGraph 0⟧ = 2 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_E3₁
    : downwardFlagVector (unitVector ⟨3, ⟦E3₁_labeledGraph 0⟧⟩) = (2 / 3 : ℝ) • unitVector ⟨3, ⟦E3_labeledGraph⟧⟩
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
    : unlabel ⟦E3₁_labeledGraph 2⟧ = ⟦E3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_E3₁'
    : downwardNormalizingFactor ⟦E3₁_labeledGraph 2⟧ = 1 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_E3₁'
    : downwardFlagVector (unitVector ⟨3, ⟦E3₁_labeledGraph 2⟧⟩) = (1 / 3 : ℝ) • unitVector ⟨3, ⟦E3_labeledGraph⟧⟩
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
    : unlabel ⟦P3₁_labeledGraph 0⟧ = ⟦P3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_P3₁
    : downwardNormalizingFactor ⟦P3₁_labeledGraph 0⟧ = 1 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_P3₁
    : downwardFlagVector (unitVector ⟨3, ⟦P3₁_labeledGraph 0⟧⟩) = (1 / 3 : ℝ) • unitVector ⟨3, ⟦P3_labeledGraph⟧⟩
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
    : unlabel ⟦P3₁_labeledGraph 1⟧ = ⟦P3_labeledGraph⟧
  := by
  sorry

lemma downwardNormalizingFactor_P3₁'
    : downwardNormalizingFactor ⟦P3₁_labeledGraph 1⟧ = 2 / 3
  := by
  sorry

lemma downwardFlagVectorQuot_P3₁'
    : downwardFlagVector (unitVector ⟨3, ⟦P3₁_labeledGraph 1⟧⟩) = (2 / 3 : ℝ) • unitVector ⟨3, ⟦P3_labeledGraph⟧⟩
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
    : unlabel ⟦K3₁_labeledGraph 0⟧ = ⟦K3_labeledGraph⟧
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (K3₁_labeledGraph 0) := by
      apply unlabeledGraph_iso
      exact Quotient.mk_out (K3₁_labeledGraph 0)
    _ ∼f K3_labeledGraph := by
      dsimp [unlabeledGraph, K3₁_labeledGraph, K3_labeledGraph]
      apply flagEqv.refl

lemma downwardNormalizingFactor_K3₁
    : downwardNormalizingFactor ⟦K3₁_labeledGraph 0⟧ = 1
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount]
  sorry

lemma downwardFlagVectorQuot_K3₁
    : downwardFlagVector (unitVector ⟨3, ⟦K3₁_labeledGraph 0⟧⟩) = unitVector ⟨3, ⟦K3_labeledGraph⟧⟩
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
