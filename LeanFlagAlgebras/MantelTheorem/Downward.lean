import «LeanFlagAlgebras».MantelTheorem.FlagIso
import «LeanFlagAlgebras».Compute.Downward
import Mathlib.Tactic.FinCases

open FlagAlgebras
open Classical
open Compute

namespace MantelTheorem

/- downward operations -/

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

lemma downwardNormalizingFactor_labeledGraph_O3₁
    : downwardNormalizingFactor_labeledGraph (O3₁_labeledGraph 0) = 1
  := by
  rw [← O3₁_eq, downwardNormalizingFactor_labeledGraph_eq]
  native_decide

lemma downwardNormalizingFactor_O3₁
    : downwardNormalizingFactor O3₁_flag = 1
  := by
  dsimp [downwardNormalizingFactor, O3₁_flag]
  exact downwardNormalizingFactor_labeledGraph_O3₁

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

lemma downwardNormalizingFactor_labeledGraph_E3₁
    : downwardNormalizingFactor_labeledGraph (E3₁_labeledGraph 0) = 2 / 3
  := by
  rw [← E3₁_eq, downwardNormalizingFactor_labeledGraph_eq]
  native_decide

lemma downwardNormalizingFactor_E3₁
    : downwardNormalizingFactor E3₁_flag = 2 / 3
  := by
  dsimp [downwardNormalizingFactor, E3₁_flag]
  exact downwardNormalizingFactor_labeledGraph_E3₁

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

lemma downwardNormalizingFactor_labeledGraph_E3₁'
    : downwardNormalizingFactor_labeledGraph (E3₁_labeledGraph 2) = 1 / 3
  := by
  rw [← E3₁'_eq, downwardNormalizingFactor_labeledGraph_eq]
  native_decide

lemma downwardNormalizingFactor_E3₁'
    : downwardNormalizingFactor E3₁'_flag = 1 / 3
  := by
  dsimp [downwardNormalizingFactor, E3₁'_flag]
  exact downwardNormalizingFactor_labeledGraph_E3₁'

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

lemma downwardNormalizingFactor_labeledGraph_P3₁
    : downwardNormalizingFactor_labeledGraph (P3₁_labeledGraph 0) = 1 / 3
  := by
  rw [← P3₁_eq, downwardNormalizingFactor_labeledGraph_eq]
  native_decide

lemma downwardNormalizingFactor_P3₁
    : downwardNormalizingFactor P3₁_flag = 1 / 3
  := by
  dsimp [downwardNormalizingFactor, P3₁_flag]
  exact downwardNormalizingFactor_labeledGraph_P3₁

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

lemma downwardNormalizingFactor_labeledGraph_P3₁'
    : downwardNormalizingFactor_labeledGraph (P3₁_labeledGraph 1) = 2 / 3
  := by
  rw [← P3₁'_eq, downwardNormalizingFactor_labeledGraph_eq]
  native_decide

lemma downwardNormalizingFactor_P3₁'
    : downwardNormalizingFactor P3₁'_flag = 2 / 3
  := by
  dsimp [downwardNormalizingFactor, P3₁'_flag]
  exact downwardNormalizingFactor_labeledGraph_P3₁'

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

lemma downwardNormalizingFactor_labeledGraph_K3₁
    : downwardNormalizingFactor_labeledGraph (K3₁_labeledGraph 0) = 1
  := by
  rw [← K3₁_eq, downwardNormalizingFactor_labeledGraph_eq]
  native_decide

lemma downwardNormalizingFactor_K3₁
    : downwardNormalizingFactor K3₁_flag = 1
  := by
  dsimp [downwardNormalizingFactor, K3₁_flag]
  exact downwardNormalizingFactor_labeledGraph_K3₁

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
