module

public import LeanFlagAlgebras.Automation.Basic
public import LeanFlagAlgebras.Automation.FlagMulReduce
public import LeanFlagAlgebras.Automation.FlagSumSort
public import LeanFlagAlgebras.Automation.Matrix.PosSemiDef
public import LeanFlagAlgebras.Flags.Densities.MulLoader_old
public import LeanFlagAlgebras.Flags.Densities.DensityLoader_old
public import LeanFlagAlgebras.MantelTheorem.Lemmas
public import LeanFlagAlgebras.Forbid.CommonGraphs

@[expose] public section

/-! # Automation.MantelTheoremAPI — Mantel's theorem via the Automation layer

Per-problem density-bound proof on the Automation layer. The headline
result `Mantel_flagAlgebra_API` is the flag-algebra form of Mantel's theorem:
in K₃-free graphs the edge density (`FlagAlgebra_2_0_0_1`) is at most `1/2`:

  `FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)`.

The certificate uses a single 2×2 PSD matrix `M` (shown positive semidefinite
via an explicit LDLᵀ factorization, rational then cast to ℝ) together with the
auxiliary equality `K2_expand_under_forbid` that rewrites the edge density on
three vertices, after dropping the K₃ term which vanishes under the forbidden
subgraph. The goal is then discharged with the Automation tactics. -/

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix

namespace MantelTheoremAPI

/-- The SDP certificate matrix (rational, 2×2); paired with `v` over the
σ = `FlagType_1_0` type. -/
def M : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), (-1 / 2: ℚ);
    (-1 / 2 : ℚ), (1 / 2 : ℚ)]
noncomputable def M_real : Matrix (Fin 2) (Fin 2) ℝ :=
  ratMatrixToReal M

def dM : Fin 2 → ℚ :=
  ![(1 / 2 : ℚ), 0]
def LM : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 : ℚ), 0;
   (-1 : ℚ), (1 : ℚ)]
lemma dM_nonneg (i : Fin 2) : 0 ≤ dM i := by
  fin_cases i <;> norm_num [dM]
lemma M_eq_LDL : M = LM * Matrix.diagonal dM * LMᵀ := by
  decide +kernel
theorem M_posSemidef : M.PosSemidef := by
  exact posSemidef_of_LDLt dM_nonneg M_eq_LDL
lemma dM_real_nonneg (i : Fin 2) : 0 ≤ (dM i : ℝ) := by
  exact_mod_cast dM_nonneg i
lemma M_real_eq_LDL :
    M_real = (ratMatrixToReal LM * Matrix.diagonal (fun i => (dM i : ℝ))) * (ratMatrixToReal LM)ᵀ := by
  calc
    M_real = ratMatrixToReal (LM * Matrix.diagonal dM * LMᵀ) := by
      simp [M_real, ratMatrixToReal, M_eq_LDL]
    _ = (ratMatrixToReal LM * Matrix.diagonal (fun i => (dM i : ℝ))) * (ratMatrixToReal LM)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `M_real` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem M_real_posSemidef : M_real.PosSemidef := by
  exact posSemidef_of_LDLt_real dM_real_nonneg M_real_eq_LDL

/-- Label type for the quadratic form: the single-vertex type. -/
def σ : FlagType (Fin 1) := FlagType_1_0
/-- Flag vector paired with `M` (the two σ-type 2-vertex flags). -/
noncomputable def v : FlagAlgebraVec σ 2 := ![
  FlagAlgebra_2_1_0_0, FlagAlgebra_2_1_0_1
]

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_3_K3_free_indices.json"
load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_3_1_0_from_2_1_0_forbid_K3.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_3_1_0_from_2_1_0_forbid_K3.json"

/-- Under the K₃-forbid relation, the edge density `FlagAlgebra_2_0_0_1` equals
`(1/3)·FlagAlgebra_3_0_0_1 + (2/3)·FlagAlgebra_3_0_0_2`: the 3-vertex expansion
of an edge with the K₃ term dropped (it vanishes since K₃ is forbidden). -/
lemma K2_expand_under_forbid
    : FlagAlgebra_2_0_0_1 =[K3.toFinFlag] (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
  := by
  have h_unit : (FlagAlgebra_3_0_0_3 : FlagAlgebra ∅ₜ) = ⟦unitVector (⟨3, Flag_3_0_0_3⟩ : FinFlag ∅ₜ)⟧
    := (Quotient.out_inj.mp rfl).symm
  have hK3_zero : (FlagAlgebra_3_0_0_3 : FlagAlgebra ∅ₜ) =[K3.toFinFlag] 0 := by
    rw [h_unit]
    apply unitVector_forbidEq_zero
    rw [unlabel_emptyType]
    exact lt_of_le_of_ne
      (flagListDensity₁_ge_zero K3.toFinFlag.2 Flag_3_0_0_3)
      (Ne.symm flagDensity1_K3_Flag_3_0_0_3_ne_zero)
  have h_eq : FlagAlgebra_2_0_0_1 =[K3.toFinFlag]
      (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3 :=
    forbidEq_of_eq MantelTheorem.expand_K2_on_three_vertex_graphs
  rw [forbidEq_rw_right_add_left hK3_zero, add_zero] at h_eq
  exact h_eq

set_option maxHeartbeats 0
set_option maxRecDepth 1500

/-- **Mantel's theorem (flag-algebra form).** In K₃-free graphs the edge
density is at most `1/2`. Proved by adding the PSD quadratic-form (SOS) term
from `M_real`/`v`, expanding the edge density via `K2_expand_under_forbid`, and
reducing with the Automation tactics. -/
theorem Mantel_flagAlgebra_API
    : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have quadraticForm_trans : FlagAlgebra_2_0_0_1 ≤[K3.toFinFlag]
            FlagAlgebra_2_0_0_1 + ⟦flagQuadraticForm M_real v⟧₀
    := by
    apply forbidLE_add_QuadraticForm M_real M_real_posSemidef v
    exact forbidLE_refl K3.toFinFlag FlagAlgebra_2_0_0_1
  apply forbidLE_trans quadraticForm_trans
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_forbidExpand_one K3.toFinFlag 3)))

  rw [forbidLE_rw_left_add_right K2_expand_under_forbid]
  simp [flagQuadraticForm, v, M_real, ratMatrixToReal, M, Fin.sum_univ_two, add_assoc]
  reduce_downward_flagmul

  expand_one_at 3

  simp [smul_smul, downward_add, downward_smul]
  flagsum_ac_sort_rhs_pipeline

  apply forbidLE_of_le
  flag_nonneg

end MantelTheoremAPI
