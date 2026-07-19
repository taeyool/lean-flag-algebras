module

public import LeanFlagAlgebras.FlagAlgebra.FlagSequence

@[expose] public section

example (a b : ℚ) (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  simp_all only [Rat.cast_le]
