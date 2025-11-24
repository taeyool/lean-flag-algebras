import «LeanFlagAlgebras».MantelTheorem.FlagIso
import Mathlib.Tactic.FinCases

open FlagAlgebras
open Classical

namespace MantelTheorem

/- downward operations -/

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

/-- downward of O3₁ -/

lemma unlabel_O3₁
    : unlabel O3₁_flag = O3_flag
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (O3₁_labeledGraph 0) := by
      apply unlabeledGraph_iso
      exact flagEqv.refl (O3₁_labeledGraph 0)
    _ ∼f O3_labeledGraph := by
      dsimp [unlabeledGraph]
      apply flagEqv.refl

def isoSet_O3₁
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {O3₁_labeledGraph 0, O3₁_labeledGraph 1, O3₁_labeledGraph 2}

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
      simp only [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_O3₁_eq_isoSet_O3₁_card]
    _ = 3 := isoSet_O3₁_card

lemma downwardNormalizingFactor_O3₁
    : downwardNormalizingFactor O3₁_flag = 1
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph, O3₁_flag]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_O3₁_card, this]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

lemma downwardFlagVectorQuot_O3₁
    : downwardFlagVector (unitVector ⟨3, O3₁_flag⟩) = unitVector ⟨3, O3_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_O3₁, downwardNormalizingFactor_O3₁]

theorem downward_O3₁
    : ⟦O3₁⟧₀ = O3
  := by
  dsimp [O3₁, downward, O3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_O3₁]

/-- downward of E3₁ -/

lemma unlabel_E3₁
    : unlabel E3₁_flag = E3_flag
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (E3₁_labeledGraph 0) := by
      apply unlabeledGraph_iso
      exact flagEqv.refl (E3₁_labeledGraph 0)
    _ ∼f E3_labeledGraph := by
      dsimp [unlabeledGraph]
      apply flagEqv.refl

def isoSet_E3₁
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {E3₁_labeledGraph 0, E3₁_labeledGraph 1}

lemma isoSet_E3₁_card
    : isoSet_E3₁.toFinset.card = 2
  := by
  classical
  refine Finset.card_eq_two.mpr ?_
  use E3₁_labeledGraph 0, E3₁_labeledGraph 1
  have : E3₁_labeledGraph 0 ≠ E3₁_labeledGraph 1 := by
    simp [E3₁_labeledGraph]
    exact ne_of_beq_false rfl
  repeat' constructor <;> try assumption
  simp [isoSet_E3₁]

def E3₁_labeledGraph_0_1_iso
    : E3₁_labeledGraph 0 ≃f E3₁_labeledGraph 1 where
  graph_iso := {
    toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
    invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
    left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    map_rel_iff' := by
      simp [E3₁_labeledGraph]
      intros; constructor
      · split <;> (intro h; split at h) <;> simp at *
      · split <;> (intro; split) <;> simp at *
  }
  type_preserve := by simp; rfl

lemma E3₁_labeledGraph_0_2_not_iso
    : ¬ E3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2
  := E3₁_E3₁'_not_iso

lemma E3₁_labeledGraph_1_2_not_iso
    : ¬ E3₁_labeledGraph 1 ∼f E3₁_labeledGraph 2
  := by
  intro h
  have : E3₁_labeledGraph 0 ∼f E3₁_labeledGraph 2 := by
    calc
      _ ∼f E3₁_labeledGraph 1 := Nonempty.intro E3₁_labeledGraph_0_1_iso
      _ ∼f E3₁_labeledGraph 2 := h
  exact False.elim (E3₁_labeledGraph_0_2_not_iso this)

lemma isoLabeledGraphSetWithSameGraph_E3₁_eq_isoSet_E3₁_card
    : isoLabeledGraphSetWithSameGraph (E3₁_labeledGraph 0) = isoSet_E3₁
  := by
  dsimp [isoLabeledGraphSetWithSameGraph, isoSet_E3₁]
  ext H; constructor
  · intro h
    simp
    obtain ⟨h_graph, h_iso⟩ := h
    simp [E3₁_labeledGraph] at h_graph
    rcases fun_Fin1_Fin3 H.type_embed with h₀ | (h₁ | h₂)
    · left
      ext1
      · simp [E3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [E3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · right
      ext1
      · simp [E3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [E3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · have hH : H = E3₁_labeledGraph 2 := by
        ext1
        · simp [E3₁_labeledGraph, h_graph]
        · simp [E3₁_labeledGraph]
          exact type_embed_HEq (id (Eq.symm h_graph)) h₂
      rw [hH] at h_iso
      exact False.elim (E3₁_labeledGraph_0_2_not_iso h_iso)
  · intro h
    rcases h with h₀ | h₁
    · subst h₀
      simp
      exact flagEqv.refl (E3₁_labeledGraph 0)
    · subst h₁
      simp; constructor
      · dsimp [E3₁_labeledGraph]
      · exact Nonempty.intro E3₁_labeledGraph_0_1_iso

lemma isoLabeledGraphSetWithSameGraph_E3₁_card
    : (isoLabeledGraphSetWithSameGraph (E3₁_labeledGraph 0)).toFinset.card = 2
  := by
  calc
    _ = isoSet_E3₁.toFinset.card := by
      simp only [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_E3₁_eq_isoSet_E3₁_card]
    _ = 2 := isoSet_E3₁_card

lemma downwardNormalizingFactor_E3₁
    : downwardNormalizingFactor E3₁_flag = 2 / 3
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph, E3₁_flag]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_E3₁_card, this]
  rfl

lemma downwardFlagVectorQuot_E3₁
    : downwardFlagVector (unitVector ⟨3, E3₁_flag⟩) = (2 / 3 : ℝ) • unitVector ⟨3, E3_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_E3₁, downwardNormalizingFactor_E3₁]

theorem downward_E3₁
    : ⟦E3₁⟧₀ = (2 / 3 : ℝ) • E3
  := by
  dsimp [E3₁, downward, E3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_E3₁]
  rfl

/-- downward of E3₁' -/

lemma unlabel_E3₁'
    : unlabel E3₁'_flag = E3_flag
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (E3₁_labeledGraph 2) := by
      apply unlabeledGraph_iso
      exact flagEqv.refl (E3₁_labeledGraph 2)
    _ ∼f E3_labeledGraph := by
      dsimp [unlabeledGraph]
      apply flagEqv.refl

def isoSet_E3₁'
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {E3₁_labeledGraph 2}

lemma isoSet_E3₁'_card
    : isoSet_E3₁'.toFinset.card = 1
  := by
  apply Finset.card_eq_one.mpr
  use E3₁_labeledGraph 2
  simp [isoSet_E3₁']

lemma isoLabeledGraphSetWithSameGraph_E3₁'_eq_isoSet_E3₁'_card
    : isoLabeledGraphSetWithSameGraph (E3₁_labeledGraph 2) = isoSet_E3₁'
  := by
  dsimp [isoLabeledGraphSetWithSameGraph, isoSet_E3₁']
  ext H; constructor
  · intro h
    simp
    obtain ⟨h_graph, h_iso⟩ := h
    simp [E3₁_labeledGraph] at h_graph
    rcases fun_Fin1_Fin3 H.type_embed with h₀ | (h₁ | h₂)
    · have hH : H = E3₁_labeledGraph 0 := by
        ext1
        · simp [E3₁_labeledGraph, h_graph]
        · simp [E3₁_labeledGraph]
          exact type_embed_HEq (id (Eq.symm h_graph)) h₀
      rw [hH] at h_iso
      exact False.elim (E3₁_labeledGraph_0_2_not_iso h_iso.symm)
    · have hH : H = E3₁_labeledGraph 1 := by
        ext1
        · simp [E3₁_labeledGraph, h_graph]
        · simp [E3₁_labeledGraph]
          exact type_embed_HEq (id (Eq.symm h_graph)) h₁
      rw [hH] at h_iso
      exact False.elim (E3₁_labeledGraph_1_2_not_iso h_iso.symm)
    · ext1
      · simp [E3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [E3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
  · intro h
    simp at *
    simp [h]
    exact flagEqv.refl (E3₁_labeledGraph 2)

lemma isoLabeledGraphSetWithSameGraph_E3₁'_card
    : (isoLabeledGraphSetWithSameGraph (E3₁_labeledGraph 2)).toFinset.card = 1
  := by
  calc
    _ = isoSet_E3₁'.toFinset.card := by
      simp only [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_E3₁'_eq_isoSet_E3₁'_card]
    _ = 1 := isoSet_E3₁'_card

lemma downwardNormalizingFactor_E3₁'
    : downwardNormalizingFactor E3₁'_flag = 1 / 3
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph, E3₁'_flag]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_E3₁'_card, this]
  rfl

lemma downwardFlagVectorQuot_E3₁'
    : downwardFlagVector (unitVector ⟨3, E3₁'_flag⟩) = (1 / 3 : ℝ) • unitVector ⟨3, E3_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_E3₁', downwardNormalizingFactor_E3₁']

theorem downward_E3₁'
    : ⟦E3₁'⟧₀ = (1 / 3 : ℝ) • E3
  := by
  dsimp [E3₁', downward, E3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_E3₁']
  rfl

/-- downward of P3₁ -/

lemma unlabel_P3₁
    : unlabel P3₁_flag = P3_flag
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (P3₁_labeledGraph 0) := by
      apply unlabeledGraph_iso
      exact flagEqv.refl (P3₁_labeledGraph 0)
    _ ∼f P3_labeledGraph := by
      dsimp [unlabeledGraph]
      apply flagEqv.refl

def isoSet_P3₁
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {P3₁_labeledGraph 0}

lemma isoSet_P3₁_card
    : isoSet_P3₁.toFinset.card = 1
  := by
  apply Finset.card_eq_one.mpr
  use P3₁_labeledGraph 0
  simp [isoSet_P3₁]

def P3₁_labeledGraph_1_2_iso
    : P3₁_labeledGraph 1 ≃f P3₁_labeledGraph 2 where
  graph_iso := {
    toFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
    invFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
    left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    map_rel_iff' := by
      simp [P3₁_labeledGraph]
      intros; constructor
      · split <;> (intro h; split at h) <;> simp at *
      · split <;> (intro; split) <;> simp at *
  }
  type_preserve := by simp; rfl

lemma P3₁_labeledGraph_0_1_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1
  := P3₁_P3₁'_not_iso

lemma P3₁_labeledGraph_0_2_not_iso
    : ¬ P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 2
  := by
  intro h
  have : P3₁_labeledGraph 0 ∼f P3₁_labeledGraph 1 := by
    calc
      _ ∼f P3₁_labeledGraph 2 := h
      _ ∼f P3₁_labeledGraph 1 := Nonempty.intro P3₁_labeledGraph_1_2_iso.symm
  exact False.elim (P3₁_labeledGraph_0_1_not_iso this)

lemma isoLabeledGraphSetWithSameGraph_P3₁_eq_isoSet_P3₁_card
    : isoLabeledGraphSetWithSameGraph (P3₁_labeledGraph 0) = isoSet_P3₁
  := by
  dsimp [isoLabeledGraphSetWithSameGraph, isoSet_P3₁]
  ext H; constructor
  · intro h
    simp
    obtain ⟨h_graph, h_iso⟩ := h
    simp [P3₁_labeledGraph] at h_graph
    rcases fun_Fin1_Fin3 H.type_embed with h₀ | (h₁ | h₂)
    · ext1
      · simp [P3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [P3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · have hH : H = P3₁_labeledGraph 1 := by
        ext1
        · simp [P3₁_labeledGraph, h_graph]
        · simp [P3₁_labeledGraph]
          exact type_embed_HEq (id (Eq.symm h_graph)) h₁
      rw [hH] at h_iso
      exact False.elim (P3₁_labeledGraph_0_1_not_iso h_iso)
    · have hH : H = P3₁_labeledGraph 2 := by
        ext1
        · simp [P3₁_labeledGraph, h_graph]
        · simp [P3₁_labeledGraph]
          exact type_embed_HEq (id (Eq.symm h_graph)) h₂
      rw [hH] at h_iso
      exact False.elim (P3₁_labeledGraph_0_2_not_iso h_iso)
  · intro h
    simp at *
    simp [h]
    exact flagEqv.refl (P3₁_labeledGraph 0)

lemma isoLabeledGraphSetWithSameGraph_P3₁_card
    : (isoLabeledGraphSetWithSameGraph (P3₁_labeledGraph 0)).toFinset.card = 1
  := by
  calc
    _ = isoSet_P3₁.toFinset.card := by
      simp only [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_P3₁_eq_isoSet_P3₁_card]
    _ = 1 := isoSet_P3₁_card

lemma downwardNormalizingFactor_P3₁
    : downwardNormalizingFactor P3₁_flag = 1 / 3
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph, P3₁_flag]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_P3₁_card, this]
  rfl

lemma downwardFlagVectorQuot_P3₁
    : downwardFlagVector (unitVector ⟨3, P3₁_flag⟩) = (1 / 3 : ℝ) • unitVector ⟨3, P3_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_P3₁, downwardNormalizingFactor_P3₁]

theorem downward_P3₁
    : ⟦P3₁⟧₀ = (1 / 3 : ℝ) • P3
  := by
  dsimp [P3₁, downward, P3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_P3₁]
  rfl

/-- downward of P3₁' -/

lemma unlabel_P3₁'
    : unlabel P3₁'_flag = P3_flag
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (P3₁_labeledGraph 1) := by
      apply unlabeledGraph_iso
      exact flagEqv.refl (P3₁_labeledGraph 1)
    _ ∼f P3_labeledGraph := by
      dsimp [unlabeledGraph]
      apply flagEqv.refl

def isoSet_P3₁'
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {P3₁_labeledGraph 1, P3₁_labeledGraph 2}

lemma isoSet_P3₁'_card
    : isoSet_P3₁'.toFinset.card = 2
  := by
  classical
  refine Finset.card_eq_two.mpr ?_
  use P3₁_labeledGraph 1, P3₁_labeledGraph 2
  have : P3₁_labeledGraph 1 ≠ P3₁_labeledGraph 2 := by
    simp [P3₁_labeledGraph]
    exact ne_of_beq_false rfl
  repeat' constructor <;> try assumption
  simp [isoSet_P3₁']

lemma isoLabeledGraphSetWithSameGraph_P3₁'_eq_isoSet_P3₁'_card
    : isoLabeledGraphSetWithSameGraph (P3₁_labeledGraph 1) = isoSet_P3₁'
  := by
  dsimp [isoLabeledGraphSetWithSameGraph, isoSet_P3₁']
  ext H; constructor
  · intro h
    simp
    obtain ⟨h_graph, h_iso⟩ := h
    simp [P3₁_labeledGraph] at h_graph
    rcases fun_Fin1_Fin3 H.type_embed with h₀ | (h₁ | h₂)
    · have hH : H = P3₁_labeledGraph 0 := by
        ext1
        · simp [P3₁_labeledGraph, h_graph]
        · simp [P3₁_labeledGraph]
          exact type_embed_HEq (id (Eq.symm h_graph)) h₀
      rw [hH] at h_iso
      exact False.elim (P3₁_labeledGraph_0_1_not_iso h_iso.symm)
    · left
      ext1
      · simp [P3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [P3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · right
      ext1
      · simp [P3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [P3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
  · intro h
    rcases h with h₀ | h₁
    · subst h₀
      simp
      exact flagEqv.refl (P3₁_labeledGraph 1)
    · subst h₁
      simp; constructor
      · dsimp [P3₁_labeledGraph]
      · exact Nonempty.intro P3₁_labeledGraph_1_2_iso

lemma isoLabeledGraphSetWithSameGraph_P3₁'_card
    : (isoLabeledGraphSetWithSameGraph (P3₁_labeledGraph 1)).toFinset.card = 2
  := by
  calc
    _ = isoSet_P3₁'.toFinset.card := by
      simp only [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_P3₁'_eq_isoSet_P3₁'_card]
    _ = 2 := isoSet_P3₁'_card

lemma downwardNormalizingFactor_P3₁'
    : downwardNormalizingFactor P3₁'_flag = 2 / 3
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph, P3₁'_flag]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_P3₁'_card, this]
  rfl

lemma downwardFlagVectorQuot_P3₁'
    : downwardFlagVector (unitVector ⟨3, P3₁'_flag⟩) = (2 / 3 : ℝ) • unitVector ⟨3, P3_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_P3₁', downwardNormalizingFactor_P3₁']

theorem downward_P3₁'
    : ⟦P3₁'⟧₀ = (2 / 3 : ℝ) • P3
  := by
  dsimp [P3₁', downward, P3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_P3₁']
  rfl

/-- downward of K3₁ -/

lemma unlabel_K3₁
    : unlabel K3₁_flag = K3_flag
  := by
  dsimp [unlabel]
  apply Quotient.sound
  calc
    _ ∼f unlabeledGraph (K3₁_labeledGraph 0) := by
      apply unlabeledGraph_iso
      exact flagEqv.refl (K3₁_labeledGraph 0)
    _ ∼f K3_labeledGraph := by
      dsimp [unlabeledGraph]
      apply flagEqv.refl

def isoSet_K3₁
    : Set (LabeledGraph Sₜ (Fin 3))
  :=
  {K3₁_labeledGraph 0, K3₁_labeledGraph 1, K3₁_labeledGraph 2}

lemma isoSet_K3₁_card
    : isoSet_K3₁.toFinset.card = 3
  := by
  classical
  refine Finset.card_eq_three.mpr ?_
  use K3₁_labeledGraph 0, K3₁_labeledGraph 1, K3₁_labeledGraph 2
  have : K3₁_labeledGraph 0 ≠ K3₁_labeledGraph 1 := by
    simp [K3₁_labeledGraph]
    exact ne_of_beq_false rfl
  have : K3₁_labeledGraph 0 ≠ K3₁_labeledGraph 2 := by
    simp [K3₁_labeledGraph]
    exact ne_of_beq_false rfl
  have : K3₁_labeledGraph 1 ≠ K3₁_labeledGraph 2 := by
    simp [K3₁_labeledGraph]
    exact ne_of_beq_false rfl
  repeat' constructor <;> try assumption
  simp [isoSet_K3₁]

def K3₁_labeledGraph_0_1_iso
    : K3₁_labeledGraph 0 ≃f K3₁_labeledGraph 1 where
  graph_iso := {
    toFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
    invFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
    left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    map_rel_iff' := by
      intros; simp [K3₁_labeledGraph]
      constructor
      · split <;> (intro h; split at h) <;> simp at *
      · split <;> (intro; split) <;> simp at *
  }
  type_preserve := by simp; rfl

def K3₁_labeledGraph_0_2_iso
    : K3₁_labeledGraph 0 ≃f K3₁_labeledGraph 2 where
  graph_iso := {
    toFun := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
    invFun := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
    left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
    map_rel_iff' := by
      intros; simp [K3₁_labeledGraph]
      constructor
      · split <;> (intro h; split at h) <;> simp at *
      · split <;> (intro; split) <;> simp at *
  }
  type_preserve := by simp; rfl

lemma isoLabeledGraphSetWithSameGraph_K3₁_eq_isoSet_K3₁_card
    : isoLabeledGraphSetWithSameGraph (K3₁_labeledGraph 0) = isoSet_K3₁
  := by
  dsimp [isoLabeledGraphSetWithSameGraph, isoSet_K3₁]
  ext H; constructor
  · intro h
    simp; simp [K3₁_labeledGraph] at h
    obtain ⟨h_graph, _⟩ := h
    rcases fun_Fin1_Fin3 H.type_embed with h₀ | (h₁ | h₂)
    · left
      ext1
      · simp [K3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [K3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · right; left
      ext1
      · simp [K3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [K3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
    · right; right
      ext1
      · simp [K3₁_labeledGraph, h_graph]
      · apply type_embed_HEq
        · dsimp [K3₁_labeledGraph]
          rw [h_graph]
        · simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
          rfl
  · intro h
    rcases h with h₀ | (h₁ | h₂)
    · subst h₀
      simp
      exact flagEqv.refl (K3₁_labeledGraph 0)
    · subst h₁
      simp; constructor
      · dsimp [K3₁_labeledGraph]
      · exact Nonempty.intro K3₁_labeledGraph_0_1_iso
    · subst h₂
      simp; constructor
      · dsimp [K3₁_labeledGraph]
      · exact Nonempty.intro K3₁_labeledGraph_0_2_iso

lemma isoLabeledGraphSetWithSameGraph_K3₁_card
    : (isoLabeledGraphSetWithSameGraph (K3₁_labeledGraph 0)).toFinset.card = 3
  := by
  calc
    _ = isoSet_K3₁.toFinset.card := by
      simp only [Set.toFinset_card]
      apply Fintype.card_congr
      rw [isoLabeledGraphSetWithSameGraph_K3₁_eq_isoSet_K3₁_card]
    _ = 3 := isoSet_K3₁_card

lemma downwardNormalizingFactor_K3₁
    : downwardNormalizingFactor K3₁_flag = 1
  := by
  dsimp [downwardNormalizingFactor, isomorphismCount, downwardNormalizingFactor_labeledGraph, K3₁_flag]
  have : Nat.factorial 3 / 2 = 3 := rfl
  rw [isoLabeledGraphSetWithSameGraph_K3₁_card, this]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

lemma downwardFlagVectorQuot_K3₁
    : downwardFlagVector (unitVector ⟨3, K3₁_flag⟩) = unitVector ⟨3, K3_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_K3₁, downwardNormalizingFactor_K3₁]

theorem downward_K3₁
    : ⟦K3₁⟧₀ = K3
  := by
  dsimp [K3₁, downward, K3, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_K3₁]

end MantelTheorem
