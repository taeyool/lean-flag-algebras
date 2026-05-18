import «LeanFlagAlgebras».Archive.MantelTheorem.FlagDefs
import «LeanFlagAlgebras».Archive.Compute.Downward

/-!
# (Archived) Downward (unlabeling) of the hand-written Mantel flags

ARCHIVED / SUPERSEDED — this file is **not** part of the build (its import is
commented out in `LeanFlagAlgebras.lean`). It computes the downward (unlabel)
images of the singleton-typed flags `K1₁`, `K2₁`, `O3₁`, `E3₁`, `E3₁'`, `P3₁`,
`P3₁'`, `K3₁` from `Archive/MantelTheorem/FlagDefs.lean` in the empty-type flag
algebra. Superseded by the active `LeanFlagAlgebras/MantelTheorem/` development.
-/

open FlagAlgebras
open Classical
open Archive.Compute

namespace Archive.MantelTheorem

/-- downward of K1₁ -/

lemma unlabel_K1₁
    : unlabel K1₁_flag = K1_flag
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_K1₁
    : downwardNormalizingFactor K1₁_flag = 1
  := by
  rw [← K1₁_eq, downwardNormalizingFactor_eq]
  native_decide

lemma downwardFlagVectorQuot_K1₁
    : downwardFlagVector (unitVector ⟨1, K1₁_flag⟩) = unitVector ⟨1, K1_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_K1₁, downwardNormalizingFactor_K1₁]

theorem downward_K1₁
    : ⟦K1₁⟧₀ = K1
  := by
  dsimp [K1₁, downward, K1, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_K1₁]

/-- downward of K2₁ -/

lemma unlabel_K2₁
    : unlabel K2₁_flag = K2_flag
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_K2₁
    : downwardNormalizingFactor K2₁_flag = 1
  := by
  rw [← K2₁_eq, downwardNormalizingFactor_eq]
  native_decide

lemma downwardFlagVectorQuot_K2₁
    : downwardFlagVector (unitVector ⟨2, K2₁_flag⟩) = unitVector ⟨2, K2_flag⟩
  := by
  simp [downwardFlagVector, downwardFlag, linearExtension]
  simp [unlabel_K2₁, downwardNormalizingFactor_K2₁]

theorem downward_K2₁
    : ⟦K2₁⟧₀ = K2
  := by
  dsimp [K2₁, downward, K2, downwardFlagVectorQuot]
  rw [downwardFlagVectorQuot_K2₁]

/-- downward of O3₁ -/

lemma unlabel_O3₁
    : unlabel O3₁_flag = O3_flag
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_O3₁
    : downwardNormalizingFactor O3₁_flag = 1
  := by
  rw [← O3₁_eq, downwardNormalizingFactor_eq]
  native_decide

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
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_E3₁
    : downwardNormalizingFactor E3₁_flag = 2 / 3
  := by
  rw [← E3₁_eq, downwardNormalizingFactor_eq]
  native_decide

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
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_E3₁'
    : downwardNormalizingFactor E3₁'_flag = 1 / 3
  := by
  rw [← E3₁'_eq, downwardNormalizingFactor_eq]
  native_decide

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
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_P3₁
    : downwardNormalizingFactor P3₁_flag = 1 / 3
  := by
  rw [← P3₁_eq, downwardNormalizingFactor_eq]
  native_decide

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
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_P3₁'
    : downwardNormalizingFactor P3₁'_flag = 2 / 3
  := by
  rw [← P3₁'_eq, downwardNormalizingFactor_eq]
  native_decide

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
  :=
  Quotient.sound (flagEqv.refl _)

lemma downwardNormalizingFactor_K3₁
    : downwardNormalizingFactor K3₁_flag = 1
  := by
  rw [← K3₁_eq, downwardNormalizingFactor_eq]
  native_decide

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

end Archive.MantelTheorem
