import LeanFlagAlgebras.FlagAlgebra.Compute.FastIso

namespace FlagAlgebras.Compute

example {n : ℕ} {G₁ G₂ : Sym2Graph n} (h : isEmptyIsoFast_bool G₁ G₂ = true) : G₁ ∼sf G₂ := by
  simp [isEmptyIsoFast_bool] at h
  sorry

end FlagAlgebras.Compute
