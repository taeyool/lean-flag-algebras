module

public import LeanFlagAlgebras.Archive.OldFlagPipeline.Lemmas_old

@[expose] public section

/- Expansion of K2 on 3-vertex empty type flags -/
example : FlagAlgebra_2_0_0_1 = (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + (1 : ℝ) • FlagAlgebra_3_0_0_3 + (0 : ℝ) • FlagAlgebra_3_0_0_0 + (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
  := by
  flag_expand 3

/- K2₁ = (1 / 2) • E3₁ + P3₁ + (1 / 2) • P3₁' + K3₁ -/
example : FlagAlgebra_2_1_0_1 = (1 / 2 : ℝ) • FlagAlgebra_3_1_0_1 + FlagAlgebra_3_1_0_3
    + (1 / 2 : ℝ) • FlagAlgebra_3_1_0_4 + FlagAlgebra_3_1_0_5
  := by
  flag_expand 3

