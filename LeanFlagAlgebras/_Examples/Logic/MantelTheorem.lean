module

public import LeanFlagAlgebras.Logic.MantelTheorem

@[expose] public section

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
