module

public import «LeanFlagAlgebras».Archive.MantelTheorem.FlagDensity
public import «LeanFlagAlgebras».Archive.MantelTheorem.FlagIso

@[export] public section

/-!
# (Archived) Flag-product identities for the Mantel flags

ARCHIVED / SUPERSEDED — this file is **not** part of the build (its import is
commented out in `LeanFlagAlgebras.lean`). It proves the three singleton-typed
flag-product identities needed for the early Mantel's-theorem proof
(`O2₁ * O2₁`, `O2₁ * K2₁`, `K2₁ * K2₁`) via a custom tactic. Superseded by the
active `LeanFlagAlgebras/MantelTheorem/FlagMul.lean`.
-/

open FlagAlgebras

namespace Archive.MantelTheorem

syntax "prove_eq_of_flag_mul_on_three_vertices" : tactic

macro_rules
| `(tactic| prove_eq_of_flag_mul_on_three_vertices) => `(tactic|
    {
      apply Quotient.sound
      simp [flagVector_mul_eq_nested_sum, flagMul, flagMulWithSize]
      rw [Finset.sum_eq_multiset_sum, ← singletonTypeThreeVertexFlagSet_eq_univ]
      simp [singletonTypeThreeVertexFlagSet_val_eq]
    })

theorem mul_O2₁_O2₁ : O2₁ * O2₁ = O3₁ + E3₁'
  := by prove_eq_of_flag_mul_on_three_vertices

theorem mul_O2₁_K2₁ : O2₁ * K2₁ = (1 / 2 : ℝ) • E3₁ + (1 / 2 : ℝ) • P3₁'
  := by prove_eq_of_flag_mul_on_three_vertices

theorem mul_K2₁_K2₁ : K2₁ * K2₁ = P3₁ + K3₁
  := by prove_eq_of_flag_mul_on_three_vertices

end Archive.MantelTheorem
