import LeanFlagAlgebras.FlagAlgebra.RandomHom
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace FlagAlgebras

abbrev FlagAlgebraVec {n₀ : ℕ} (σ : FlagType (Fin n₀)) (n : ℕ)
  := Fin n → FlagAlgebra σ

noncomputable def flagQuadraticForm
    {σ : FlagType (Fin n₀)} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : FlagAlgebraVec σ n)
    : FlagAlgebra σ
  :=
  ∑ i, ∑ j, (M i j) • (v i * v j)

theorem flagQuadraticForm_nonneg
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : flagQuadraticForm M v ≥ 0
  := by
  rw [ge_iff_le, le_def, sub_zero]
  intro φ
  simp [flagQuadraticForm, PositiveHom.map_sum, PositiveHom.map_smul, PositiveHom.map_mul]
  let v₀ : Fin n →₀ ℝ := {
    support := { i | φ (v i) ≠ 0 },
    toFun i := φ (v i),
    mem_support_toFun := by simp
  }
  let h := hM.2 v₀
  simp [v₀, Finsupp.sum] at h
  have h_unfilter_inner :
      ∀ i : Fin n,
        (∑ j with ¬φ (v j) = 0, φ (v i) * M i j * φ (v j))
          = ∑ j, φ (v i) * M i j * φ (v j) := by
    intro i
    refine Finset.sum_subset (by intro y hy; simp) ?_
    intro y _ hy_not
    have hy0 : φ (v y) = 0 := by
      simp at hy_not
      exact hy_not
    simp [hy0]
  have h_unfilter_outer :
      (∑ i with ¬φ (v i) = 0, ∑ j with ¬φ (v j) = 0, φ (v i) * M i j * φ (v j))
        = ∑ i, ∑ j, φ (v i) * M i j * φ (v j) := by
    calc
      _ = ∑ i with ¬φ (v i) = 0, ∑ j, φ (v i) * M i j * φ (v j) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact h_unfilter_inner i
      _ = ∑ i, ∑ j, φ (v i) * M i j * φ (v j) := by
        refine Finset.sum_subset (by intro i hi; simp) ?_
        intro i _ hi_not
        have hi0 : φ (v i) = 0 := by
          simp at hi_not
          exact hi_not
        simp [hi0]
  rw [h_unfilter_outer] at h
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

theorem flagQuadraticForm_downward_nonneg
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : ⟦flagQuadraticForm M v⟧₀ ≥ 0
  := by
  simp only [ge_iff_le, le_def, sub_zero]
  apply downward_preserve_semanticCone
  simpa using flagQuadraticForm_nonneg M hM v

end FlagAlgebras
