import LeanFlagAlgebras.FlagAlgebra.FlagSequence
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Flag-algebra evaluations as a dense subalgebra of `C(X_σ)`

For the support-closure criterion (paper §4) we need that the flag-algebra elements,
viewed as continuous functions on the homomorphism space `X_σ = PositiveHomSpace σ`,
are sup-norm dense in `C(X_σ, ℝ)`.  This is Razborov's use of Stone–Weierstrass
(`[Razborov2007, Proposition 3.7]`).

We package the evaluation `f ↦ (χ ↦ χ f)` as an `ℝ`-algebra homomorphism
`evalAlgHom : FlagAlgebra σ →ₐ[ℝ] C(X_σ, ℝ)`, show its range separates points (distinct
homomorphisms disagree on some flag), and conclude density via Mathlib's
`subalgebra_topologicalClosure_eq_top_of_separatesPoints`.  The headline consequence is
`exists_flag_near`: every continuous function on `X_σ` is uniformly approximable by a
flag-algebra element.
-/

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Evaluation as a continuous function on `X_σ` -/

/-- `χ ↦ χ k`, written as a sum over the support of a chosen representative; this exposes
the evaluation as a finite combination of the (continuous) coordinate maps `χ ↦ χ.val F`. -/
lemma toPosHom_apply_eq_sum (k : FlagAlgebra σ) :
    (fun ψ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom ψ) k)
      = (fun ψ => ∑ F ∈ k.out.support, k.out F * ψ.val F) := by
  funext ψ
  conv_lhs => rw [← Quotient.out_eq k, flagVector_eq_sum_basisVector k.out]
  rw [sum_quot, PositiveHom.map_sum]
  simp only [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector]

/-- The evaluation `χ ↦ χ f` is continuous on `X_σ`. -/
lemma continuous_eval (f : FlagAlgebra σ) :
    Continuous (fun ψ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom ψ) f) := by
  rw [toPosHom_apply_eq_sum f]
  apply continuous_finset_sum
  intro F _
  exact Continuous.mul continuous_const ((FinFlag.continuous F).comp continuous_subtype_val)

/-- The flag-algebra element `f` as a continuous real function on `X_σ`. -/
noncomputable def evalContinuousMap (f : FlagAlgebra σ) : C(PositiveHomSpace σ, ℝ) :=
  ⟨fun ψ => (PositiveHomSpace.toPosHom ψ) f, continuous_eval f⟩

@[simp]
lemma evalContinuousMap_apply (f : FlagAlgebra σ) (ψ : PositiveHomSpace σ) :
    evalContinuousMap f ψ = (PositiveHomSpace.toPosHom ψ) f := rfl

/-- Evaluation as an `ℝ`-algebra homomorphism into `C(X_σ, ℝ)`. -/
noncomputable def evalAlgHom : FlagAlgebra σ →ₐ[ℝ] C(PositiveHomSpace σ, ℝ) where
  toFun := evalContinuousMap
  map_one' := by ext ψ; simp
  map_mul' f g := by ext ψ; simpa using PositiveHom.map_mul (PositiveHomSpace.toPosHom ψ) f g
  map_zero' := by ext ψ; simp
  map_add' f g := by ext ψ; simpa using PositiveHom.map_add (PositiveHomSpace.toPosHom ψ) f g
  commutes' r := by
    ext ψ
    show (PositiveHomSpace.toPosHom ψ) (algebraMap ℝ (FlagAlgebra σ) r) = _
    rw [Algebra.algebraMap_eq_smul_one, PositiveHom.map_smul, PositiveHom.map_one, mul_one,
      Algebra.algebraMap_eq_smul_one]
    simp

@[simp]
lemma evalAlgHom_apply (f : FlagAlgebra σ) (ψ : PositiveHomSpace σ) :
    evalAlgHom f ψ = (PositiveHomSpace.toPosHom ψ) f := rfl

/-- The subalgebra of `C(X_σ, ℝ)` of flag-algebra evaluations. -/
noncomputable def evalSubalgebra (σ : FlagType (Fin n₀)) : Subalgebra ℝ C(PositiveHomSpace σ, ℝ) :=
  evalAlgHom.range

/-- Distinct homomorphisms disagree on some flag, so the evaluation subalgebra
separates points. -/
lemma evalSubalgebra_separatesPoints : (evalSubalgebra σ).SeparatesPoints := by
  intro x y hxy
  have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hF : ∃ F, x.val F ≠ y.val F := by
    by_contra h
    push_neg at h
    exact hval (DFunLike.ext _ _ h)
  obtain ⟨F, hF⟩ := hF
  refine ⟨⇑(evalContinuousMap (⟦basisVector F⟧ : FlagAlgebra σ)),
    ⟨evalContinuousMap ⟦basisVector F⟧, ⟨⟦basisVector F⟧, rfl⟩, rfl⟩, ?_⟩
  show (PositiveHomSpace.toPosHom x) ⟦basisVector F⟧ ≠ (PositiveHomSpace.toPosHom y) ⟦basisVector F⟧
  rw [PositiveHomSpace.toPosHom_basisVector, PositiveHomSpace.toPosHom_basisVector]
  exact hF

/-- **Stone–Weierstrass for flag algebras**: the evaluation subalgebra is dense in
`C(X_σ, ℝ)`. -/
lemma evalSubalgebra_dense : (evalSubalgebra σ).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    evalSubalgebra_separatesPoints

/-- Every continuous function on `X_σ` is uniformly within `ε` of some flag-algebra
element (the ε-form of Stone–Weierstrass used in the support-closure criterion). -/
theorem exists_flag_near (H : PositiveHomSpace σ → ℝ) (hH : Continuous H) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : FlagAlgebra σ, ∀ χ : PositiveHomSpace σ, |(PositiveHomSpace.toPosHom χ) f - H χ| < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (evalSubalgebra σ) evalSubalgebra_separatesPoints H hH ε hε
  obtain ⟨f, hf⟩ := g.2
  refine ⟨f, fun χ => ?_⟩
  have hval := hg χ
  rw [Real.norm_eq_abs] at hval
  have hgx : (g : PositiveHomSpace σ → ℝ) χ = (PositiveHomSpace.toPosHom χ) f := by
    rw [← hf]; rfl
  rwa [hgx] at hval

end FlagAlgebras.MetaTheory
