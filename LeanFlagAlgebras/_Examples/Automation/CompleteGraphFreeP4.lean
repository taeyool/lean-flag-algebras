module

public import LeanFlagAlgebras.Automation.CompleteGraphFreeP4

@[expose] public section

example : FlagAlgebra_3_2_0_0 * FlagAlgebra_3_2_0_3 =
    (1 / 2 : ℝ) • FlagAlgebra_4_2_0_5 + (1 / 2 : ℝ) • FlagAlgebra_4_2_0_10
  := by
  dsimp only [FlagAlgebra_3_2_0_0, FlagAlgebra_3_2_0_3]
  rw [basisVector_quot_mul_eq_flagMul_quot]
  simp [flagMul, flagMulWithSize]
  rw [Finset.sum_eq_multiset_sum, ← flagSet_4_2_0_eq_univ, flagSet_4_2_0_val_eq]
  simp [add_quot, smul_quot]
  rfl
