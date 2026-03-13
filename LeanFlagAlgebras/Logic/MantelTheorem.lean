import LeanFlagAlgebras.Logic.Defs
import LeanFlagAlgebras.MantelTheorem.MantelTheorem

open FlagAlgebras
open MantelTheorem

namespace FlagLogic

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

theorem Mantel_theorem
    : K3 =ₐ (0 : FlagAlgebra ∅ₜ) ⊢ₐ K2 ≤ₐ (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  intro φ h
  simp only [Assert.eval_le, Assert.eval_eq] at *
  rw [PositiveHom.map_smul, PositiveHom.map_one, mul_one]
  rw [PositiveHom.map_zero] at h
  exact Mantel_theorem' φ h

end FlagLogic
