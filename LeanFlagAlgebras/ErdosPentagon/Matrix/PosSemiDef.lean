import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Matrix

namespace ErdosPentagon

theorem posSemidef_of_eq_mul_diagonal_mul_transpose
    {n : ℕ} {M L : Matrix (Fin n) (Fin n) ℚ} {d : Fin n → ℚ}
    (hd : ∀ i, 0 ≤ d i) (hM : M = L * Matrix.diagonal d * Lᵀ)
    : M.PosSemidef
  := by
  have hdiag : (Matrix.diagonal d).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.isHermitian_diagonal d
    · intro x
      simp only [dotProduct, Pi.star_apply, star_trivial, mulVec, diagonal, of_apply, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_nonneg ?_
      intro i hi
      have hterm : x i * (d i * x i) = d i * (x i) ^ 2 := by ring
      rw [hterm]
      exact mul_nonneg (hd i) (sq_nonneg (x i))
  have hLDL : (L * Matrix.diagonal d * Lᵀ).PosSemidef := by
    have h := hdiag.conjTranspose_mul_mul_same Lᵀ
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, mul_assoc] using h
  simpa [hM] using hLDL

theorem posSemidef_of_eq_mul_diagonal_mul_transpose_real
    {n : ℕ} {M L : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hM : M = L * Matrix.diagonal d * Lᵀ)
    : M.PosSemidef
  := by
  have hdiag : (Matrix.diagonal d).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.isHermitian_diagonal d
    · intro x
      simp only [dotProduct, Pi.star_apply, star_trivial, mulVec, diagonal, of_apply, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_nonneg ?_
      intro i hi
      have hterm : x i * (d i * x i) = d i * (x i) ^ 2 := by ring
      rw [hterm]
      exact mul_nonneg (hd i) (sq_nonneg (x i))
  have hLDL : (L * Matrix.diagonal d * Lᵀ).PosSemidef := by
    have h := hdiag.conjTranspose_mul_mul_same Lᵀ
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, mul_assoc] using h
  simpa [hM] using hLDL

noncomputable def ratMatrixToReal {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ)
    : Matrix (Fin n) (Fin n) ℝ :=
  M.map (Rat.castHom ℝ)

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(24 / 625 : ℚ), (-36 / 625 : ℚ), (-36 / 625 : ℚ), (24 / 625 : ℚ), (-36 / 625 : ℚ), (24 / 625 : ℚ), (24 / 625 : ℚ), (-36 / 625 : ℚ);
     (-36 / 625 : ℚ), (277 / 625 : ℚ), (97 / 625 : ℚ), (-79 / 625 : ℚ), (97 / 625 : ℚ), (-79 / 625 : ℚ), (-259 / 625 : ℚ), (54 / 625 : ℚ);
     (-36 / 625 : ℚ), (97 / 625 : ℚ), (277 / 625 : ℚ), (-79 / 625 : ℚ), (97 / 625 : ℚ), (-259 / 625 : ℚ), (-79 / 625 : ℚ), (54 / 625 : ℚ);
     (24 / 625 : ℚ), (-79 / 625 : ℚ), (-79 / 625 : ℚ), (247 / 625 : ℚ), (-259 / 625 : ℚ), (67 / 625 : ℚ), (67 / 625 : ℚ), (-36 / 625 : ℚ);
     (-36 / 625 : ℚ), (97 / 625 : ℚ), (97 / 625 : ℚ), (-259 / 625 : ℚ), (277 / 625 : ℚ), (-79 / 625 : ℚ), (-79 / 625 : ℚ), (54 / 625 : ℚ);
     (24 / 625 : ℚ), (-79 / 625 : ℚ), (-259 / 625 : ℚ), (67 / 625 : ℚ), (-79 / 625 : ℚ), (247 / 625 : ℚ), (67 / 625 : ℚ), (-36 / 625 : ℚ);
     (24 / 625 : ℚ), (-259 / 625 : ℚ), (-79 / 625 : ℚ), (67 / 625 : ℚ), (-79 / 625 : ℚ), (67 / 625 : ℚ), (247 / 625 : ℚ), (-36 / 625 : ℚ);
     (-36 / 625 : ℚ), (54 / 625 : ℚ), (54 / 625 : ℚ), (-36 / 625 : ℚ), (54 / 625 : ℚ), (-36 / 625 : ℚ), (-36 / 625 : ℚ), (54 / 625 : ℚ)]

noncomputable def P_real : Matrix (Fin 8) (Fin 8) ℝ :=
  ratMatrixToReal P

def dP : Fin 8 → ℚ :=
  ![(24 / 625 : ℚ), (223 / 625 : ℚ), (9576 / 27875 : ℚ), (5562 / 16625 : ℚ), 0, 0, 0, 0]

def LP : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0, 0, 0;
     (-3 / 2 : ℚ), 1, 0, 0, 0, 0, 0, 0;
     (-3 / 2 : ℚ), (43 / 223 : ℚ), 1, 0, 0, 0, 0, 0;
     (1 : ℚ), (-43 / 223 : ℚ), (-43 / 266 : ℚ), 1, 0, 0, 0, 0;
     (-3 / 2 : ℚ), (43 / 223 : ℚ), (43 / 266 : ℚ), (-1 : ℚ), 1, 0, 0, 0;
     (1 : ℚ), (-43 / 223 : ℚ), (-1 : ℚ), 0, 0, 1, 0, 0;
     (1 : ℚ), (-1 : ℚ), 0, 0, 0, 0, 1, 0;
     (-3 / 2 : ℚ), 0, 0, 0, 0, 0, 0, 1]

lemma dP_nonneg (i : Fin 8) : 0 ≤ dP i := by
  fin_cases i <;> norm_num [dP]

lemma P_eq_LDL : P = LP * Matrix.diagonal dP * LPᵀ := by
  native_decide

theorem P_posSemidef : P.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose dP_nonneg P_eq_LDL

lemma dP_real_nonneg (i : Fin 8) : 0 ≤ (dP i : ℝ) := by
  exact_mod_cast dP_nonneg i

lemma P_real_eq_LDL :
    P_real = (ratMatrixToReal LP * Matrix.diagonal (fun i => (dP i : ℝ))) * (ratMatrixToReal LP)ᵀ := by
  calc
    P_real = ratMatrixToReal (LP * Matrix.diagonal dP * LPᵀ) := by
      simp [P_real, ratMatrixToReal, P_eq_LDL]
    _ = (ratMatrixToReal LP * Matrix.diagonal (fun i => (dP i : ℝ))) * (ratMatrixToReal LP)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]

theorem P_real_posSemidef : P_real.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real dP_real_nonneg P_real_eq_LDL


-- LDLᵀ generated for Q, size=6, diagonal nonnegative=True
def Q : Matrix (Fin 6) (Fin 6) ℚ :=
  !![(432 / 625 : ℚ), (-1551 / 2500 : ℚ), (-1551 / 2500 : ℚ), (-327 / 625 : ℚ), (687 / 2500 : ℚ), (687 / 2500 : ℚ);
   (-1551 / 2500 : ℚ), (584 / 625 : ℚ), (371 / 1250 : ℚ), (227 / 625 : ℚ), (2557 / 2500 : ℚ), (-1021 / 625 : ℚ);
   (-1551 / 2500 : ℚ), (371 / 1250 : ℚ), (584 / 625 : ℚ), (227 / 625 : ℚ), (-1021 / 625 : ℚ), (2557 / 2500 : ℚ);
   (-327 / 625 : ℚ), (227 / 625 : ℚ), (227 / 625 : ℚ), (432 / 625 : ℚ), (-127 / 1250 : ℚ), (-127 / 1250 : ℚ);
   (687 / 2500 : ℚ), (2557 / 2500 : ℚ), (-1021 / 625 : ℚ), (-127 / 1250 : ℚ), (3816 / 625 : ℚ), (-3606 / 625 : ℚ);
   (687 / 2500 : ℚ), (-1021 / 625 : ℚ), (2557 / 2500 : ℚ), (-127 / 1250 : ℚ), (-3606 / 625 : ℚ), (3816 / 625 : ℚ)]

noncomputable def Q_real : Matrix (Fin 6) (Fin 6) ℝ :=
  ratMatrixToReal Q

def dQ : Fin 6 → ℚ :=
  ![(432 / 625 : ℚ), (181223 / 480000 : ℚ), (22474603 / 113264375 : ℚ), (1805308 / 17624375 : ℚ), (3219791 / 7970000 : ℚ), 0]

def LQ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0, 0;
   (-517 / 576 : ℚ), (1 : ℚ), 0, 0, 0, 0;
   (-517 / 576 : ℚ), (-124825 / 181223 : ℚ), (1 : ℚ), 0, 0, 0;
   (-109 / 144 : ℚ), (-51076 / 181223 : ℚ), (-25538 / 28199 : ℚ), (1 : ℚ), 0, 0;
   (229 / 576 : ℚ), (609337 / 181223 : ℚ), (-8235 / 3188 : ℚ), 0, (1 : ℚ), 0;
   (229 / 576 : ℚ), (-95105 / 25889 : ℚ), (5047 / 3188 : ℚ), 0, (-1 : ℚ), (1 : ℚ)]

lemma dQ_nonneg (i : Fin 6) : 0 ≤ dQ i := by
  fin_cases i <;> norm_num [dQ]

lemma Q_eq_LDL : Q = LQ * Matrix.diagonal dQ * LQᵀ := by
  native_decide

theorem Q_posSemidef : Q.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose dQ_nonneg Q_eq_LDL

lemma dQ_real_nonneg (i : Fin 6) : 0 ≤ (dQ i : ℝ) := by
  exact_mod_cast dQ_nonneg i

lemma Q_real_eq_LDL :
    Q_real = (ratMatrixToReal LQ * Matrix.diagonal (fun i => (dQ i : ℝ))) * (ratMatrixToReal LQ)ᵀ := by
  calc
    Q_real = ratMatrixToReal (LQ * Matrix.diagonal dQ * LQᵀ) := by
      simp [Q_real, ratMatrixToReal, Q_eq_LDL]
    _ = (ratMatrixToReal LQ * Matrix.diagonal (fun i => (dQ i : ℝ))) * (ratMatrixToReal LQ)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]

theorem Q_real_posSemidef : Q_real.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real dQ_real_nonneg Q_real_eq_LDL

-- LDLᵀ generated for R, size=5, diagonal nonnegative=True
def R : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1512 / 625 : ℚ), (568 / 625 : ℚ), (-76 / 125 : ℚ), (568 / 625 : ℚ), (-376 / 625 : ℚ);
   (568 / 625 : ℚ), (19 / 25 : ℚ), (-191 / 625 : ℚ), 0, (-93 / 625 : ℚ);
   (-76 / 125 : ℚ), (-191 / 625 : ℚ), (192 / 625 : ℚ), (-191 / 625 : ℚ), (-2 / 625 : ℚ);
   (568 / 625 : ℚ), 0, (-191 / 625 : ℚ), (19 / 25 : ℚ), (-93 / 625 : ℚ);
   (-376 / 625 : ℚ), (-93 / 625 : ℚ), (-2 / 625 : ℚ), (-93 / 625 : ℚ), (38 / 125 : ℚ)]

noncomputable def R_real : Matrix (Fin 5) (Fin 5) ℝ :=
  ratMatrixToReal R

def dR : Fin 5 → ℚ :=
  ![(1512 / 625 : ℚ), (49447 / 118125 : ℚ), (173261 / 1236175 : ℚ), 0, 0]

def LR : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1 : ℚ), 0, 0, 0, 0;
   (71 / 189 : ℚ), (1 : ℚ), 0, 0, 0;
   (-95 / 378 : ℚ), (-9119 / 49447 : ℚ), (1 : ℚ), 0, 0;
   (71 / 189 : ℚ), (-40328 / 49447 : ℚ), (-1 : ℚ), (1 : ℚ), 0;
   (-47 / 189 : ℚ), (9119 / 49447 : ℚ), (-1 : ℚ), 0, (1 : ℚ)]

lemma dR_nonneg (i : Fin 5) : 0 ≤ dR i := by
  fin_cases i <;> norm_num [dR]

lemma R_eq_LDL : R = LR * Matrix.diagonal dR * LRᵀ := by
  native_decide

theorem R_posSemidef : R.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose dR_nonneg R_eq_LDL

lemma dR_real_nonneg (i : Fin 5) : 0 ≤ (dR i : ℝ) := by
  exact_mod_cast dR_nonneg i

lemma R_real_eq_LDL :
    R_real = (ratMatrixToReal LR * Matrix.diagonal (fun i => (dR i : ℝ))) * (ratMatrixToReal LR)ᵀ := by
  calc
    R_real = ratMatrixToReal (LR * Matrix.diagonal dR * LRᵀ) := by
      simp [R_real, ratMatrixToReal, R_eq_LDL]
    _ = (ratMatrixToReal LR * Matrix.diagonal (fun i => (dR i : ℝ))) * (ratMatrixToReal LR)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]

theorem R_real_posSemidef : R_real.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real dR_real_nonneg R_real_eq_LDL

end ErdosPentagon
