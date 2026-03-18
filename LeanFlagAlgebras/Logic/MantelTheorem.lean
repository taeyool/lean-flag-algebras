import LeanFlagAlgebras.Logic.Tactic
import LeanFlagAlgebras.MantelTheorem.MantelTheorem

open FlagAlgebras
open MantelTheorem

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

theorem temp
    {n₀ n : ℕ} {σ : FlagType (Fin n₀)} {F : FlagWithSize σ n} {f f' : FlagAlgebra σ}
    (h : ⟦unitVector ⟨n, F⟩⟧ =ₐ 0 ⊢ₐ f =ₐ f')
    : ⟦unitVector ⟨n, unlabel F⟩⟧ =ₐ 0 ⊢ₐ ⟦f⟧₀ =ₐ ⟦f'⟧₀
  := by
  sorry

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
