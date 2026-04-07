import LeanFlagAlgebras.ErdosPentagon.FlagMul
import LeanFlagAlgebras.Forbid.Basic

open FlagAlgebras

namespace ErdosPentagon

example
    : flagQuadraticForm R_real v₂ ≥ 0
  :=
  flagQuadraticForm_nonneg R_real R_real_posSemidef v₂

example
    : (FlagAlgebra_4_3_2_0 * FlagAlgebra_4_3_2_0 : FlagAlgebra _) =[K3]
      ((1 : ℝ) • FlagAlgebra_5_3_2_0 + (1 : ℝ) • FlagAlgebra_5_3_2_4)
  := by
  frw [flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_0]
  simp
  simpa using (Forbid.forbidEq_refl K3
    ((1 : ℝ) • FlagAlgebra_5_3_2_0 + (1 : ℝ) • FlagAlgebra_5_3_2_4))

example
    : ((1512 / 625 : ℝ) •
    (FlagAlgebra_4_3_2_0 * FlagAlgebra_4_3_2_0 : FlagAlgebra _)) =[K3]
      ((1512 / 625 : ℝ) • ((1 : ℝ) • FlagAlgebra_5_3_2_0 + (1 : ℝ) • FlagAlgebra_5_3_2_4))
  := by
  have hmul := Forbid.forbidEq_smul (c := (1512 / 625 : ℝ))
    flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_0
  frw [hmul]
  simpa using (Forbid.forbidEq_refl K3
    ((1512 / 625 : ℝ) • ((1 : ℝ) • FlagAlgebra_5_3_2_0 + (1 : ℝ) • FlagAlgebra_5_3_2_4)))

example
    : flagQuadraticForm R_real v₂ =[K3]
        (1512 / 625 : ℝ) • FlagAlgebra_5_3_2_0 +
        - (380 / 625 : ℝ) • FlagAlgebra_5_3_2_1
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_2
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_3
        + (1512 / 625 : ℝ) • FlagAlgebra_5_3_2_4
        + (192 / 625 : ℝ) • FlagAlgebra_5_3_2_5
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_8
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_9
        - (380 / 625 : ℝ) • FlagAlgebra_5_3_2_10
        + (475 / 625 : ℝ) • FlagAlgebra_5_3_2_11
        + (475 / 625 : ℝ) • FlagAlgebra_5_3_2_12
        - (376 / 625 : ℝ) • FlagAlgebra_5_3_2_13
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_15
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_16
        - (2 / 625 : ℝ) • FlagAlgebra_5_3_2_29
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_30
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_31
        - (93 / 625 : ℝ) • FlagAlgebra_5_3_2_32
        - (93 / 625 : ℝ) • FlagAlgebra_5_3_2_33
        - (376 / 625 : ℝ) • FlagAlgebra_5_3_2_34
        - (2 / 625 : ℝ) • FlagAlgebra_5_3_2_53
        + (190 / 625 : ℝ) • FlagAlgebra_5_3_2_54
  := by
  simp [flagQuadraticForm, v₂, R_real, ratMatrixToReal, R, Fin.sum_univ_five, add_assoc]
  have h1 := Forbid.forbidEq_smul (c := (1512 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_0
  rw [Forbid.forbidEq_rw_left_add_right h1, Forbid.forbidEq_move_add_left_iff]
  have h3 := Forbid.forbidEq_smul (c := (568 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_2
  rw [Forbid.forbidEq_rw_left_add_right h3, Forbid.forbidEq_move_add_left_iff]
  have h2 := Forbid.forbidEq_smul (c := (-76 / 125 : ℝ)) flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_1
  rw [Forbid.forbidEq_rw_left_add_right h2, Forbid.forbidEq_move_add_left_iff]
  have h4 := Forbid.forbidEq_smul (c := (568 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_3
  rw [Forbid.forbidEq_rw_left_add_right h4, Forbid.forbidEq_move_add_left_iff]
  have h5 := Forbid.forbidEq_smul (c := (-376 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_6
  rw [Forbid.forbidEq_rw_left_add_right h5, Forbid.forbidEq_move_add_left_iff]
  have h6 := Forbid.forbidEq_smul (c := (568 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_2_FlagAlgebra_4_3_2_0
  rw [Forbid.forbidEq_rw_left_add_right h6, Forbid.forbidEq_move_add_left_iff]
  have h7 := Forbid.forbidEq_smul (c := (19 / 25 : ℝ)) flagMul_FlagAlgebra_4_3_2_2_FlagAlgebra_4_3_2_2
  rw [Forbid.forbidEq_rw_left_add_right h7, Forbid.forbidEq_move_add_left_iff]
  have h8 := Forbid.forbidEq_smul (c := (-191 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_2_FlagAlgebra_4_3_2_1
  rw [Forbid.forbidEq_rw_left_add_right h8, Forbid.forbidEq_move_add_left_iff]
  have h9 := Forbid.forbidEq_smul (c := (-93 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_2_FlagAlgebra_4_3_2_6
  rw [Forbid.forbidEq_rw_left_add_right h9, Forbid.forbidEq_move_add_left_iff]
  have h10 := Forbid.forbidEq_smul (c := (-76 / 125 : ℝ)) flagMul_FlagAlgebra_4_3_2_1_FlagAlgebra_4_3_2_0
  rw [Forbid.forbidEq_rw_left_add_right h10, Forbid.forbidEq_move_add_left_iff]
  have h11 := Forbid.forbidEq_smul (c := (-191 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_1_FlagAlgebra_4_3_2_2
  rw [Forbid.forbidEq_rw_left_add_right h11, Forbid.forbidEq_move_add_left_iff]
  have h12 := Forbid.forbidEq_smul (c := (192 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_1_FlagAlgebra_4_3_2_1
  rw [Forbid.forbidEq_rw_left_add_right h12, Forbid.forbidEq_move_add_left_iff]
  have h13 := Forbid.forbidEq_smul (c := (-191 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_1_FlagAlgebra_4_3_2_3
  rw [Forbid.forbidEq_rw_left_add_right h13, Forbid.forbidEq_move_add_left_iff]
  have h14 := Forbid.forbidEq_smul (c := (-2 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_1_FlagAlgebra_4_3_2_6
  rw [Forbid.forbidEq_rw_left_add_right h14, Forbid.forbidEq_move_add_left_iff]
  have h15 := Forbid.forbidEq_smul (c := (568 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_3_FlagAlgebra_4_3_2_0
  rw [Forbid.forbidEq_rw_left_add_right h15, Forbid.forbidEq_move_add_left_iff]
  have h16 := Forbid.forbidEq_smul (c := (-191 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_3_FlagAlgebra_4_3_2_1
  rw [Forbid.forbidEq_rw_left_add_right h16, Forbid.forbidEq_move_add_left_iff]
  have h17 := Forbid.forbidEq_smul (c := (19 / 25 : ℝ)) flagMul_FlagAlgebra_4_3_2_3_FlagAlgebra_4_3_2_3
  rw [Forbid.forbidEq_rw_left_add_right h17, Forbid.forbidEq_move_add_left_iff]
  have h18 := Forbid.forbidEq_smul (c := (-93 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_3_FlagAlgebra_4_3_2_6
  rw [Forbid.forbidEq_rw_left_add_right h18, Forbid.forbidEq_move_add_left_iff]
  have h19 := Forbid.forbidEq_smul (c := (-376 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_6_FlagAlgebra_4_3_2_0
  rw [Forbid.forbidEq_rw_left_add_right h19, Forbid.forbidEq_move_add_left_iff]
  have h20 := Forbid.forbidEq_smul (c := (-93 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_6_FlagAlgebra_4_3_2_2
  rw [Forbid.forbidEq_rw_left_add_right h20, Forbid.forbidEq_move_add_left_iff]
  have h21 := Forbid.forbidEq_smul (c := (-2 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_6_FlagAlgebra_4_3_2_1
  rw [Forbid.forbidEq_rw_left_add_right h21, Forbid.forbidEq_move_add_left_iff]
  have h22 := Forbid.forbidEq_smul (c := (-93 / 625 : ℝ)) flagMul_FlagAlgebra_4_3_2_6_FlagAlgebra_4_3_2_3
  rw [Forbid.forbidEq_rw_left_add_right h22, Forbid.forbidEq_move_add_left_iff]
  have h23 := Forbid.forbidEq_smul (c := (38 / 125 : ℝ)) flagMul_FlagAlgebra_4_3_2_6_FlagAlgebra_4_3_2_6
  rw [Forbid.forbidEq_rw_left h23, Forbid.forbidEq_move_term_left_iff]

  apply Forbid.forbidEq_of_eq
  simp [smul_smul]
  norm_num
  ring_nf
  simp [add_assoc]
  have : (2 :  FlagAlgebra FlagType_3_2) = ((2 : ℝ) • (1 : FlagAlgebra FlagType_3_2)) := by
    rw [two_smul]
    norm_num
  repeat rw [this]
  repeat rw [mul_smul_comm]
  simp [smul_smul]
  norm_num
  ring_nf

theorem ErdosPentagon
    : C5 ≤[K3] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end ErdosPentagon
