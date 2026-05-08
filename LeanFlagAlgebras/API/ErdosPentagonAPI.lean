import LeanFlagAlgebras.API.Basic
import LeanFlagAlgebras.API.ReduceFlagMul
import LeanFlagAlgebras.ErdosPentagon.FlagDef
import LeanFlagAlgebras.ErdosPentagon.FlagMul
import LeanFlagAlgebras.Utils.SortTactic

open FlagAlgebras Forbid FlagAlgebras.API
open SimpleGraph Matrix

namespace ErdosPentagon

generate_unitVector_lemmas 5 34

set_option maxHeartbeats 0
set_option maxRecDepth 1500

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
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_expand K3.toFinFlag 5)))

  rw [C5_toFlagAlgebra_eq]
  simp [flagQuadraticForm, v₀, P_real, ratMatrixToReal, P, Fin.sum_univ_eight, add_assoc]
  simp [v₁, Q_real, ratMatrixToReal, Q, Fin.sum_univ_six, add_assoc]
  simp [v₂, R_real, ratMatrixToReal, R, Fin.sum_univ_five, add_assoc]
  reduce_downward_flagmul

  expand_one_at 5

  simp [smul_smul, downward_add, downward_smul]
  norm_num
  simp only [neg_add, neg_neg, sub_eq_add_neg, ← neg_smul, add_assoc]
  conv =>
    rhs
    ac_sort_at
  simp only [← add_assoc, ← add_smul]
  norm_num

  flag_nonneg

end ErdosPentagon
