import LeanFlagAlgebras.MantelTheorem.FlagMul
import LeanFlagAlgebras.FlagAlgebra.RandomHom
import LeanFlagAlgebras.Automation.FlagExpand

/-! # Mantel's theorem: auxiliary lemmas

Flag-algebra identities used to assemble the Mantel's theorem proof: expansions
of small flags on 1- and 3-vertex graphs (both unconditionally and conditioned
on the triangle `K₃` having density `0`), the normalizations `K0 = 1` and
`K1₁ = 1`, and the key downward-projected square identity
`⟦(O2₁ - K2₁)²⟧₀ = O3 - (1/3)·E3 - (1/3)·P3 + K3`, which supplies the
positive-semidefinite certificate for the density bound. -/

open FlagAlgebras Compute

namespace MantelTheorem

/- K2 = (1 / 3) • E3 + (2 / 3) • P3 + K3 -/
lemma expand_K2_on_three_vertex_graphs
    : FlagAlgebra_2_0_0_1 = (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
        + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3
  := by
  flag_expand 3

/- If φ K3 = 0, then φ K2 = (1 / 3) • φ E3 + (2 / 3) • φ P3 -/
lemma expand_K2_on_three_vertex_without_K3
    : ∀ (φ : PositiveHom ∅ₜ), φ FlagAlgebra_3_0_0_3 = 0
        → φ FlagAlgebra_2_0_0_1 = (1 / 3 : ℝ) • φ FlagAlgebra_3_0_0_1
          + (2 / 3 : ℝ) • φ FlagAlgebra_3_0_0_2
  := by
  flag_expand_forbid 3

/- Expansion of K2 on 3-vertex empty type flags -/
example : FlagAlgebra_2_0_0_1 = (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + (1 : ℝ) • FlagAlgebra_3_0_0_3 + (0 : ℝ) • FlagAlgebra_3_0_0_0 + (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
  := by
  flag_expand 3

/- K2₁ = (1 / 2) • E3₁ + P3₁ + (1 / 2) • P3₁' + K3₁ -/
example : FlagAlgebra_2_1_0_1 = (1 / 2 : ℝ) • FlagAlgebra_3_1_0_1 + FlagAlgebra_3_1_0_3
    + (1 / 2 : ℝ) • FlagAlgebra_3_1_0_4 + FlagAlgebra_3_1_0_5
  := by
  flag_expand 3

/- If φ K3₁ = 0, then φ K2₁ = (1 / 2) • φ E3₁ + φ P3₁ + (1 / 2) • φ P3₁' -/
lemma expand_K2₁_on_three_vertex_without_K3
    : ∀ (φ : FlagAlgebras.PositiveHom FlagType_1_0), φ FlagAlgebra_3_1_0_5 = 0
        → φ FlagAlgebra_2_1_0_1 = (1 / 2 : ℝ) • φ FlagAlgebra_3_1_0_1
          + φ FlagAlgebra_3_1_0_3 + (1 / 2 : ℝ) • φ FlagAlgebra_3_1_0_4
  := by
  flag_expand_forbid 3

/- K0 = 1 -/
lemma K0_eq_one
    : FlagAlgebra_0_0_0_0 = 1
  := by
  apply Quotient.sound
  show _ ∼v basisVector ⟨0, default⟩
  congr!
  exact Unique.uniq instUniqueFlagWithSize Flag_0_0_0_0

/- 1 = K1 -/
lemma expand_1_on_one_vertex_graphs
    : 1 = FlagAlgebra_1_0_0_0
  := by
  rw [← K0_eq_one]
  flag_expand 1

/- 1 = O3 + E3 + P3 + K3 -/
lemma expand_1_on_three_vertex_graphs
    : 1 = FlagAlgebra_3_0_0_0 + FlagAlgebra_3_0_0_1 + FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3
  := by
  rw [← K0_eq_one]
  flag_expand 3

/- If φ K3 = 0, then φ 1 = φ O3 + φ E3 + φ P3 -/
lemma expand_1_on_three_vertex_graphs_without_K3
    : ∀ (φ : FlagAlgebras.PositiveHom ∅ₜ), φ FlagAlgebra_3_0_0_3 = 0
        → φ 1 = φ FlagAlgebra_3_0_0_0 + φ FlagAlgebra_3_0_0_1 + φ FlagAlgebra_3_0_0_2
  := by
  rw [← K0_eq_one]
  flag_expand_forbid 3

/- K1₁ = 1 -/
lemma K1₁_eq_one
    : FlagAlgebra_1_1_0_0 = 1
  := by
  apply Quotient.sound
  show _ ∼v basisVector ⟨1, default⟩
  congr!
  exact Unique.uniq instUniqueFlagWithSize Flag_1_1_0_0

/- ⟦(O2₁ - K2₁)²⟧₀ = O3 - (1 / 3) • E3 - (1 / 3) • P3 + K3 -/
lemma FlagAlgebra_2_1_0_0_minus_FlagAlgebra_2_1_0_1_square_downward
  : ⟦(FlagAlgebra_2_1_0_0 - FlagAlgebra_2_1_0_1) * (FlagAlgebra_2_1_0_0 - FlagAlgebra_2_1_0_1)⟧₀
    = FlagAlgebra_3_0_0_0 - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
      - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3
  := by
  calc
  _ = ⟦FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_0
    - 2 • (FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_1)
    + FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀ := by
      congr
      rw [two_smul]
      ring
  _ = ⟦FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_0
    - (2 : ℝ) • (FlagAlgebra_2_1_0_0 * FlagAlgebra_2_1_0_1)
    + FlagAlgebra_2_1_0_1 * FlagAlgebra_2_1_0_1⟧₀ := rfl
  _ = ⟦FlagAlgebra_3_1_0_0 + FlagAlgebra_3_1_0_2 - FlagAlgebra_3_1_0_1
    - FlagAlgebra_3_1_0_4 + FlagAlgebra_3_1_0_3 + FlagAlgebra_3_1_0_5⟧₀ := by
        congr 1
        simp [mul_FlagAlgebra_2_1_0_0_FlagAlgebra_2_1_0_0,
          mul_FlagAlgebra_2_1_0_0_FlagAlgebra_2_1_0_1,
          mul_FlagAlgebra_2_1_0_1_FlagAlgebra_2_1_0_1]
        ring
  _ = ⟦FlagAlgebra_3_1_0_0⟧₀ + ⟦FlagAlgebra_3_1_0_2⟧₀ - ⟦FlagAlgebra_3_1_0_1⟧₀
    - ⟦FlagAlgebra_3_1_0_4⟧₀ + ⟦FlagAlgebra_3_1_0_3⟧₀ + ⟦FlagAlgebra_3_1_0_5⟧₀ := by
      simp only [downward_add, downward_sub]
  _ = FlagAlgebra_3_0_0_0
    - ((2 / 3 : ℝ) • FlagAlgebra_3_0_0_1 - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1)
    - ((2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2)
    + FlagAlgebra_3_0_0_3 := by
        simp; ring
  _ = FlagAlgebra_3_0_0_0 - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
    - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3 := by
        simp only [← sub_smul]
        norm_num

end MantelTheorem
