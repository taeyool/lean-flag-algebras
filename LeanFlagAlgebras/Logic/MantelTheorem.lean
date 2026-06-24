import LeanFlagAlgebras.Logic.Tactic
import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.MantelTheorem.MantelTheorem

/-! # Mantel's theorem inside the assertion DSL

Worked examples and the restatement of Mantel's theorem within the `FlagLogic` DSL,
exercising the `prove_flag_expand_with_forbidden_flag` /
`prove_flag_mul_with_forbidden_flag` tactics. The headline result `Mantel_theorem`
derives the edge-density bound `K2 ≤ₐ (1/2) • 1` from forbidding the triangle `K3`,
together with a downward-entailment lemma transferring DSL entailments to unlabelings.
-/

open FlagAlgebras
open MantelTheorem
open MeasureTheory

namespace FlagLogic

example : FlagAlgebra_3_0_0_3 =ₐ 0
    ⊢ₐ FlagAlgebra_2_0_0_1 =ₐ (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
  := by
  prove_flag_expand_with_forbidden_flag 3

example : FlagAlgebra_3_0_0_3 =ₐ 0
    ⊢ₐ FlagAlgebra_2_0_0_1 =ₐ (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
  := by
  prove_flag_expand_with_forbidden_flag 3

example : FlagAlgebra_3_1_0_5 =ₐ 0
    ⊢ₐ FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_0 =ₐ FlagAlgebra_3_1_0_2 + FlagAlgebra_3_1_0_0
  := by
  prove_flag_mul_with_forbidden_flag 3

example : FlagAlgebra_3_1_0_5 =ₐ 0
    ⊢ₐ FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_1
          =ₐ (1 / 2 : ℝ) • FlagAlgebra_3_1_0_1 + (1 / 2 : ℝ) • FlagAlgebra_3_1_0_4
  := by
  prove_flag_mul_with_forbidden_flag 3

example : FlagAlgebra_3_1_0_5 =ₐ 0
    ⊢ₐ FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_0
          =ₐ (1 / 2 : ℝ) • FlagAlgebra_3_1_0_4 + (1 / 2 : ℝ) • FlagAlgebra_3_1_0_1
  := by
  prove_flag_mul_with_forbidden_flag 3

example : FlagAlgebra_3_1_0_5 =ₐ 0
    ⊢ₐ FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1 =ₐ FlagAlgebra_3_1_0_3
  := by
  prove_flag_mul_with_forbidden_flag 3

/-- A DSL entailment `⟦basisVector ⟨n, F⟩⟧ =ₐ 0 ⊢ₐ f =ₐ f'` descends to the unlabelings:
forbidding the unlabeled flag entails the unlabeled equality `⟦f⟧₀ =ₐ ⟦f'⟧₀`. -/
theorem downward_entails_eq_of_forbid_unlabel_zero
    {n₀ n : ℕ} {σ : FlagType (Fin n₀)} {F : FlagWithSize σ n} {f f' : FlagAlgebra σ}
    (h : ⟦basisVector ⟨n, F⟩⟧ =ₐ 0 ⊢ₐ f =ₐ f')
    : ⟦basisVector ⟨n, unlabel F⟩⟧ =ₐ 0 ⊢ₐ ⟦f⟧₀ =ₐ ⟦f'⟧₀
  := by
  let F_typed : FinFlag σ := ⟨n, F⟩
  let F_untyped : FinFlag ∅ₜ := ⟨n, unlabel F⟩
  have hF_zero : ⟦basisVector F_typed⟧ =ᵢ[F_untyped] 0 := by
    refine Forbid.basisVector_inducedForbidEq_zero F_untyped F_typed ?_
    change 0 < flagDensity₁ (unlabel F) (unlabel F)
    rw [flagDensity_self]
    norm_num
  have h_forbid : f =ᵢ[F_untyped] f' := by
    intro φ₀ hσ hF_forbid
    let A : Set (PositiveHomSpace σ) := {φ | φ ⟦basisVector F_typed⟧ = φ 0}
    let B : Set (PositiveHomSpace σ) := {φ | φ f = φ f'}
    have hA : ℙ[φ₀] A = 1 := by
      simpa [A] using hF_zero φ₀ hσ hF_forbid
    have hsubset : A ⊆ B := by
      intro φ hφ
      exact h (PositiveHomSpace.toPosHom φ) (by simpa [A, F_typed] using hφ)
    apply le_antisymm
    · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) B
    · calc
        1 = ℙ[φ₀] A := by simpa using hA.symm
        _ ≤ ℙ[φ₀] B := ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset
  have h_down_forbid : ⟦f⟧₀ =ᵢ[F_untyped]₀ ⟦f'⟧₀ :=
    (Forbid.inducedForbidEq_emptyType_iff_inducedForbidEq F_untyped ⟦f⟧₀ ⟦f'⟧₀).2
      (Forbid.downward_inducedForbidEq_equal_flags h_forbid)
  intro φ hF
  exact h_down_forbid φ (by simpa [F_untyped] using hF)

/-- Mantel's theorem in the DSL: forbidding the triangle `K3` entails the edge-density
bound `K2 ≤ₐ (1/2) • 1` over the empty type. -/
theorem Mantel_theorem
    : K3 =ₐ (0 : FlagAlgebra ∅ₜ) ⊢ₐ K2 ≤ₐ (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  dsimp only [K2, K3]
  intro φ h
  simp only [Assert.eval_le, Assert.eval_eq] at *
  rw [PositiveHom.map_smul, PositiveHom.map_one, mul_one]
  rw [PositiveHom.map_zero] at h
  exact Mantel_theorem' φ h

end FlagLogic
