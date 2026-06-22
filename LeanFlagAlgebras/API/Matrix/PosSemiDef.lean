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
theorem posSemidef_of_LDLt
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

/-- Real-entry version of `posSemidef_of_LDLt`. -/
theorem posSemidef_of_LDLt_real
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

/-- From a **rational** LDLᵀ factorization `M = L * diagonal d * Lᵀ` with `d ≥ 0`, the real
cast `ratMatrixToReal M` is positive semidefinite. This bundles the `ℚ → ℝ` plumbing
(`exact_mod_cast` of the nonnegativity, and `map`-distributes-over-product for the equality) so
SDP-certificate emitters need only supply the rational `(d_nonneg, eq_LDL)` pair. -/
theorem posSemidef_real_of_LDLt
    {n : ℕ} {M L : Matrix (Fin n) (Fin n) ℚ} {d : Fin n → ℚ}
    (hd : ∀ i, 0 ≤ d i) (hM : M = L * Matrix.diagonal d * Lᵀ)
    : (ratMatrixToReal M).PosSemidef
  := by
  have hd' : ∀ i, (0 : ℝ) ≤ (d i : ℝ) := fun i => by exact_mod_cast hd i
  refine posSemidef_of_LDLt_real (L := ratMatrixToReal L) (d := fun i => (d i : ℝ))
    (fun i => hd' i) ?_
  calc
    ratMatrixToReal M = ratMatrixToReal (L * Matrix.diagonal d * Lᵀ) := by rw [hM]
    _ = (ratMatrixToReal L * Matrix.diagonal (fun i => (d i : ℝ))) * (ratMatrixToReal L)ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]

/-- Close a `(ratMatrixToReal M).PosSemidef` goal from the concrete rational LDLᵀ data.
`psd_real_ldlt M L d` discharges the two side goals of `posSemidef_real_of_LDLt`: the
diagonal nonnegativity by `fin_cases`/`norm_num`, and the factorization equality by
`decide +kernel`. The goal may be stated through any definitional wrapper of
`ratMatrixToReal M` (e.g. a `def M_real := ratMatrixToReal M`). -/
syntax (name := psdRealLdlt) "psd_real_ldlt" ppSpace ident ppSpace ident ppSpace ident : tactic

macro_rules
  | `(tactic| psd_real_ldlt $M:ident $L:ident $d:ident) =>
    `(tactic|
        refine posSemidef_real_of_LDLt (M := $M) (L := $L) (d := $d) ?_ ?_ <;>
          first
            | (intro i; fin_cases i <;> norm_num [$d:ident])
            | decide +kernel)
