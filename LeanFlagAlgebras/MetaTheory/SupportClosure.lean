import LeanFlagAlgebras.MetaTheory.MeasureSupport
import LeanFlagAlgebras.MetaTheory.EvalAlgebra
import LeanFlagAlgebras.MetaTheory.ConstrainedClass
import LeanFlagAlgebras.FlagAlgebra.RandomHom
import Mathlib.Topology.UrysohnsLemma

/-! # Support passes to random extensions, and the support-closure criterion

This is the Lean counterpart of paper §2's `lem:support-passes-general` and the whole of §4.

* A `Constraint` packages the forbidden `σ`-flags and the forbidden graphs (empty-type
  flags), linked by the fact that a forbidden flag *unlabels* to a forbidden graph.
* `support_passes` (`lem:support-passes-general`): a random extension `ℙ[φ₀]` of a
  constrained unlabelled limit `φ₀ ∈ Q₀` is almost surely constrained, i.e. its support
  lies in `Q_σ`.
* `Sσ`, `RootPlantable` (`def:root-planting`): `S_σ` is the closure of the union of supports
  of admissible random extensions; the triple is root-plantable when `S_σ = Q_σ`.
* `support_criterion` (`thm:support-criterion`): quotient non-negativity always implies
  ensemble non-negativity, and the two are equivalent for *every* `f` iff the triple is
  root-plantable.  The hard direction uses Urysohn's lemma in the compact metric space `X_σ`
  together with the Stone–Weierstrass density of `EvalAlgebra`.
-/

open MeasureTheory

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- A positive homomorphism, viewed as a point of the homomorphism space `X_σ`. -/
noncomputable def posHomPoint (φ : PositiveHom σ) : PositiveHomSpace σ :=
  ⟨φ.coe, φ, rfl⟩

@[simp]
lemma posHomPoint_val_apply (φ : PositiveHom σ) (F : FinFlag σ) :
    (posHomPoint φ).val F = φ ⟦basisVector F⟧ :=
  φ.coe_flag F

/-- A constraint: forbidden `σ`-flags and forbidden graphs, linked by unlabelling. -/
structure Constraint (σ : FlagType (Fin n₀)) where
  /-- The forbidden `σ`-flags (underlying graph leaves the hereditary subclass). -/
  forbσ : FinFlag σ → Prop
  /-- The forbidden graphs (empty-type flags). -/
  forb0 : FinFlag ∅ₜ → Prop
  /-- A forbidden `σ`-flag unlabels to a forbidden graph. -/
  unlabel_forb : ∀ F : FinFlag σ, forbσ F → forb0 ⟨F.1, unlabel F.2⟩

/-- The downward image of a single flag is a non-negative multiple of its unlabelling. -/
lemma downward_basisVector (F : FinFlag σ) :
    downward (⟦basisVector F⟧ : FlagAlgebra σ)
      = (downwardNormalizingFactor F.2 : ℝ) • (⟦basisVector ⟨F.1, unlabel F.2⟩⟧ : FlagAlgebra ∅ₜ) := by
  show downwardFlagVectorQuot (basisVector F) = _
  dsimp only [downwardFlagVectorQuot]
  rw [downwardFlagVector_basisVector]
  dsimp only [downwardFlag]
  rw [rat_smul_eq_real_smul, smul_quot]

/-- For a forbidden flag `F`, almost every random extension assigns it density `0`. -/
lemma forbidden_ae_zero (T : Constraint σ) {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) (hσ : φ₀ ⟨σ⟩₀ > 0)
    {F : FinFlag σ} (hF : T.forbσ F) :
    ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)), χ.val F = 0 := by
  -- the underlying graph is a forbidden graph, hence killed by `φ₀ ∈ Q₀`
  have hzero0 : φ₀ (⟦basisVector ⟨F.1, unlabel F.2⟩⟧ : FlagAlgebra ∅ₜ) = 0 := by
    have hmem := (mem_Qσ_iff T.forb0 (posHomPoint φ₀)).mp hφ₀ ⟨F.1, unlabel F.2⟩ (T.unlabel_forb F hF)
    rwa [posHomPoint_val_apply] at hmem
  have hdown0 : φ₀ (downward (⟦basisVector F⟧ : FlagAlgebra σ)) = 0 := by
    rw [downward_basisVector, PositiveHom.map_smul, hzero0, mul_zero]
  -- the evaluation `χ ↦ χ ⟦basisVector F⟧` is non-negative, continuous, and has zero integral
  set g : PositiveHomSpace σ → ℝ := fun χ => (PositiveHomSpace.toPosHom χ) ⟦basisVector F⟧ with hg
  have fpos : ∀ χ, 0 ≤ g χ := fun χ => positiveHom_basisVector_ge_zero _ F
  have hint : Integrable g (ℙ[φ₀] : Measure (PositiveHomSpace σ)) :=
    BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact (evalContinuousMap (⟦basisVector F⟧ : FlagAlgebra σ)))
  have hf0 : ∫ χ, g χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)) = 0 := by
    simp only [hg]
    rw [probMeasure_extend_emptyType_positiveHom_spec hσ (⟦basisVector F⟧ : FlagAlgebra σ),
      hdown0, zero_div]
  have hae := (integral_eq_zero_iff_of_nonneg fpos hint).mp hf0
  filter_upwards [hae] with χ hχ
  have hχ0 : g χ = 0 := hχ
  rw [← PositiveHomSpace.toPosHom_basisVector]
  exact hχ0

/-- **Support passes to random extensions** (`lem:support-passes-general`): if `φ₀` is a
constrained unlabelled limit with `φ₀⟨σ⟩₀ > 0`, then the random extension `ℙ[φ₀]` is
supported on `Q_σ`. -/
theorem support_passes (T : Constraint σ) {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) (hσ : φ₀ ⟨σ⟩₀ > 0) :
    (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support ⊆ Qσ T.forbσ := by
  refine Measure.support_subset_of_isClosed (Qσ_isClosed T.forbσ) ?_
  have hae : ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)), ∀ F : FinFlag σ, T.forbσ F → χ.val F = 0 := by
    rw [ae_all_iff]
    intro F
    by_cases hF : T.forbσ F
    · filter_upwards [forbidden_ae_zero T hφ₀ hσ hF] with χ hχ _ using hχ
    · filter_upwards with χ hcon using absurd hcon hF
  have hset : Qσ T.forbσ = {χ : PositiveHomSpace σ | ∀ F, T.forbσ F → χ.val F = 0} := by
    ext χ; exact mem_Qσ_iff T.forbσ χ
  rw [hset]; exact hae

/-! ## The root-planting set and the criterion -/

/-- The root-planting set `S_σ` (`def:root-planting`): the closure of the union of supports
of admissible random extensions of constrained unlabelled limits. -/
def Sσ (T : Constraint σ) : Set (PositiveHomSpace σ) :=
  closure (⋃ (φ₀ : PositiveHom ∅ₜ) (_ : posHomPoint φ₀ ∈ Qσ T.forb0) (hσ : φ₀ ⟨σ⟩₀ > 0),
            (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support)

/-- Root-plantability: `S_σ = Q_σ`. -/
def RootPlantable (T : Constraint σ) : Prop := Sσ T = Qσ T.forbσ

/-- One always has `S_σ ⊆ Q_σ` (`lem:support-passes-general`). -/
theorem Sσ_subset_Qσ (T : Constraint σ) : Sσ T ⊆ Qσ T.forbσ := by
  refine closure_minimal ?_ (Qσ_isClosed T.forbσ)
  refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
  exact support_passes T hφ₀ hσ

/-- Quotient non-negativity (condition (a)): `f ≥ 0` on `Q_σ`. -/
def QuotientNonneg (T : Constraint σ) (f : FlagAlgebra σ) : Prop :=
  ∀ χ ∈ Qσ T.forbσ, 0 ≤ (PositiveHomSpace.toPosHom χ) f

/-- Ensemble non-negativity (condition (b)): `f ≥ 0` almost surely under every admissible
random extension. -/
def EnsembleNonneg (T : Constraint σ) (f : FlagAlgebra σ) : Prop :=
  ∀ (φ₀ : PositiveHom ∅ₜ), posHomPoint φ₀ ∈ Qσ T.forb0 → ∀ (hσ : φ₀ ⟨σ⟩₀ > 0),
    (ℙ[φ₀] : Measure (PositiveHomSpace σ)) {χ | 0 ≤ (PositiveHomSpace.toPosHom χ) f} = 1

/-- **Quotient semantics implies ensemble semantics** (soundness, always holds). -/
theorem quotient_implies_ensemble (T : Constraint σ) (f : FlagAlgebra σ)
    (h : QuotientNonneg T f) : EnsembleNonneg T f := by
  intro φ₀ hφ₀ hσ
  rw [ae_nonneg_iff_nonneg_on_support _ (continuous_eval f)]
  intro χ hχ
  exact h χ (support_passes T hφ₀ hσ hχ)

/-- **Support-closure criterion** (`thm:support-criterion`): quotient and ensemble
semantics agree for *every* `f` iff the triple is root-plantable. -/
theorem support_criterion (T : Constraint σ) :
    (∀ f : FlagAlgebra σ, QuotientNonneg T f ↔ EnsembleNonneg T f) ↔ RootPlantable T := by
  constructor
  · -- equivalence for all `f` forces `S_σ = Q_σ`
    intro hequiv
    refine Set.Subset.antisymm (Sσ_subset_Qσ T) ?_
    by_contra hcon
    rw [Set.not_subset] at hcon
    obtain ⟨ψ, hψQ, hψS⟩ := hcon
    -- Urysohn directly in the compact metric space `X_σ`
    obtain ⟨u, hu0, hu1, _⟩ := exists_continuous_zero_one_of_isClosed (X := PositiveHomSpace σ)
      isClosed_closure (isClosed_singleton (x := ψ))
      (Set.disjoint_singleton_right.mpr hψS)
    -- `H = 1 - 2u`: `H = 1` on `S_σ`, `H ψ = -1`
    set H : PositiveHomSpace σ → ℝ := fun χ => 1 - 2 * u χ with hH
    have hHcont : Continuous H := continuous_const.sub (continuous_const.mul u.continuous)
    obtain ⟨f, hf⟩ := exists_flag_near H hHcont (ε := 1/3) (by norm_num)
    -- `f` is ensemble-nonneg (positive on `S_σ`) but quotient-negative (negative at `ψ ∈ Q_σ`)
    have hEns : EnsembleNonneg T f := by
      intro φ₀ hφ₀ hσ
      rw [ae_nonneg_iff_nonneg_on_support _ (continuous_eval f)]
      intro χ hχ
      have hχS : χ ∈ Sσ T :=
        subset_closure (Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ₀,
          Set.mem_iUnion.mpr ⟨hσ, hχ⟩⟩⟩)
      have huχ : u χ = 0 := by simpa using hu0 hχS
      have hHχ : H χ = 1 := by simp only [hH, huχ, mul_zero, sub_zero]
      have hbound := hf χ
      rw [hHχ, abs_lt] at hbound
      linarith [hbound.1]
    have hNotQuot : ¬ QuotientNonneg T f := by
      intro hQ
      have hpos := hQ ψ hψQ
      have huψ : u ψ = 1 := by simpa using hu1 rfl
      have hHψ : H ψ = -1 := by simp only [hH, huψ]; norm_num
      have hbound := hf ψ
      rw [hHψ, abs_lt] at hbound
      linarith [hbound.2]
    exact hNotQuot ((hequiv f).mpr hEns)
  · -- root-plantability gives the equivalence
    intro hRP f
    refine ⟨quotient_implies_ensemble T f, ?_⟩
    intro hE χ hχ
    have hχS : χ ∈ Sσ T := by rw [hRP]; exact hχ
    have hcl : IsClosed {χ : PositiveHomSpace σ | 0 ≤ (PositiveHomSpace.toPosHom χ) f} :=
      isClosed_le continuous_const (continuous_eval f)
    have hsub : (⋃ (φ₀ : PositiveHom ∅ₜ) (_ : posHomPoint φ₀ ∈ Qσ T.forb0) (hσ : φ₀ ⟨σ⟩₀ > 0),
        (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support)
          ⊆ {χ : PositiveHomSpace σ | 0 ≤ (PositiveHomSpace.toPosHom χ) f} := by
      refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
      intro χ' hχ'
      exact (ae_nonneg_iff_nonneg_on_support _ (continuous_eval f)).mp (hE φ₀ hφ₀ hσ) χ' hχ'
    exact (closure_minimal hsub hcl) hχS

end FlagAlgebras.MetaTheory
