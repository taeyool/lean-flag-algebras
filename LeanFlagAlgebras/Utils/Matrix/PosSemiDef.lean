import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Positive semidefiniteness from an LDLᵀ factorization

Shared utility supplying the criterion `M = L * diagonal d * Lᵀ` with `d ≥ 0 ⟹ M.PosSemidef`,
over both `ℚ` and `ℝ`, plus a `ℚ → ℝ` matrix cast. Used to discharge the PSD side-condition of
sum-of-squares (SOS) certificates produced by the flag-algebra solver.
-/

open Matrix

/-- If `M = L * diagonal d * Lᵀ` with every `d i ≥ 0`, then `M` is positive semidefinite
(rational entries). -/
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

/-- Real-entry version of `posSemidef_of_eq_mul_diagonal_mul_transpose`. -/
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

/-- Cast a rational matrix to the corresponding real matrix entrywise. -/
noncomputable def ratMatrixToReal {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ)
    : Matrix (Fin n) (Fin n) ℝ :=
  M.map (Rat.castHom ℝ)
