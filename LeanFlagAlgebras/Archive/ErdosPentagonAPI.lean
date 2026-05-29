import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.FlagMulReduce
import LeanFlagAlgebras.ErdosPentagon.FlagDef
import LeanFlagAlgebras.ErdosPentagon.FlagMul
import LeanFlagAlgebras.API.FlagSumSort

/-! # API.ErdosPentagonAPI — the Erdős pentagon problem via the API layer

Per-problem density-bound proof on the API automation layer. The headline
result `ErdosPentagon_flagAlgebra_API` is the Erdős pentagon bound: in K₃-free
graphs the density of `C₅` (the 5-cycle) is at most `24/625`:

  `C5.toFlagAlgebra ≤[K3.toFinFlag] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)`.

The proof adds three PSD quadratic-form (SOS) certificate terms built from the
matrices `P_real`, `Q_real`, `R_real` and flag vectors `v₀`, `v₁`, `v₂` (all
imported from `ErdosPentagon.FlagDef` / `ErdosPentagon.FlagMul`), then discharges
the goal with the API tactics. -/

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix

namespace ErdosPentagonAPI

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **Erdős pentagon bound.** In K₃-free graphs the `C₅` density is at most
`24/625`. Proved by adding the three PSD quadratic-form (SOS) terms from
`P_real`/`v₀`, `Q_real`/`v₁`, `R_real`/`v₂` and reducing with the API tactics. -/
theorem ErdosPentagon_flagAlgebra_API
    : C5.toFlagAlgebra ≤[K3.toFinFlag] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : C5.toFlagAlgebra ≤[K3.toFinFlag]
            C5.toFlagAlgebra + ⟦flagQuadraticForm P_real v₀⟧₀
                             + ⟦flagQuadraticForm Q_real v₁⟧₀
                             + ⟦flagQuadraticForm R_real v₂⟧₀ := by
    apply forbidLE_add_QuadraticForm R_real R_real_posSemidef v₂
    apply forbidLE_add_QuadraticForm Q_real Q_real_posSemidef v₁
    apply forbidLE_add_QuadraticForm P_real P_real_posSemidef v₀
    exact forbidLE_refl K3.toFinFlag C5.toFlagAlgebra
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 5)))

  rw [C5_toFlagAlgebra_eq]
  simp [flagQuadraticForm, v₀, P_real, ratMatrixToReal, P, Fin.sum_univ_eight, add_assoc]
  simp [v₁, Q_real, ratMatrixToReal, Q, Fin.sum_univ_six, add_assoc]
  simp [v₂, R_real, ratMatrixToReal, R, Fin.sum_univ_five, add_assoc]
  reduce_downward_flagmul

  expand_one_at 5

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end ErdosPentagonAPI
