import Mathlib.Tactic.FieldSimp
import «LeanFlagAlgebras».PositiveHom
import «LeanFlagAlgebras».MantelTheorem.Downward
import «LeanFlagAlgebras».MantelTheorem.FlagMuls

open FlagAlgebras

namespace MantelTheorem

/- proof of Mantel's theorem -/

lemma O2₁_minus_K2₁_square_downward
    : ⟦(O2₁ - K2₁) ^ 2⟧₀ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3
  := by
  calc
    _ = ⟦O2₁ * O2₁ - 2 • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := by congr; sorry
    _ = ⟦O2₁ * O2₁ - (2 : ℝ) • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := rfl
    _ = ⟦O3₁ + E3₁' - E3₁ - P3₁' + P3₁ + K3₁⟧₀ := by simp; ring_nf
    _ = _ := sorry

theorem mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  sorry

end MantelTheorem
