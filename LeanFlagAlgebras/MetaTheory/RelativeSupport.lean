import LeanFlagAlgebras.MetaTheory.DownwardAverage

/-! # Relative ensemble semantics: the relative support `S_σ(Y)` (paper §11, `sec:relative`)

Paper §11.2 ("Relative ensemble enhancements").  Instead of forming a quotient algebra for
a (possibly non-hereditary) further constraint, fix an arbitrary set `Y` of admissible
unlabelled limits and define the *relative labelled support*

  `S_σ(Y) = closure (⋃ {φ₀ | posHomPoint φ₀ ∈ Y, φ₀⟨σ⟩₀ > 0} supp ℙ[φ₀])`.

Relative ensemble positivity asks for non-negativity on `S_σ(Y)` only.  This module gives:

* `relSσ` — the relative support (`S_σ(Y)` of the paper);
* `Sσ_eq_relSσ` — taking `Y = Q₀` recovers the absolute root-planting set `S_σ`;
* `relative_soundness` (`prop:relative-soundness`) — `f ≥ 0` on `S_σ(Y)` implies
  `φ₀ ⟦f⟧₀ ≥ 0` for every `φ₀ ∈ Y`;
* `RelEnsembleNonneg`, `relative_criterion` (`prop:relative-criterion`) — the relative
  support-closure criterion, which — in contrast with the absolute
  `thm:support-criterion` — holds *unconditionally* (no root-plantability needed:
  both directions are the "easy" directions, no Urysohn function is required).

Formalisation notes.  The paper takes `Y ⊆ Q₀` nonempty; neither hypothesis is needed for
any statement in this module, so `Y : Set (PositiveHomSpace ∅ₜ)` is arbitrary (the
absolute theory is the instance `Y = Qσ T.forb0`).  Membership of a base limit
`φ₀ : PositiveHom ∅ₜ` in `Y` is phrased as `posHomPoint φ₀ ∈ Y`, matching the `Sσ` /
`Qσ` conventions of `SupportClosure.lean`.
-/

open MeasureTheory

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ}

/-- **The relative labelled support** `S_σ(Y)` (paper §11.2): the closure of the union of
the supports of the random extensions `ℙ[φ₀]` over the admissible base limits `φ₀ ∈ Y`
with positive type density.  For `Y = Qσ forb0` this is the root-planting set `Sσ`. -/
def relSσ (Y : Set (PositiveHomSpace ∅ₜ)) (σ : FlagType (Fin n₀)) :
    Set (PositiveHomSpace σ) :=
  closure (⋃ (φ₀ : PositiveHom ∅ₜ) (_ : posHomPoint φ₀ ∈ Y) (hσ : φ₀ ⟨σ⟩₀ > 0),
            (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support)

/-- The relative support is closed. -/
lemma relSσ_isClosed (Y : Set (PositiveHomSpace ∅ₜ)) (σ : FlagType (Fin n₀)) :
    IsClosed (relSσ Y σ) :=
  isClosed_closure

/-- The relative support is monotone in the constraint set. -/
lemma relSσ_mono {Y Y' : Set (PositiveHomSpace ∅ₜ)} (hYY' : Y ⊆ Y')
    (σ : FlagType (Fin n₀)) : relSσ Y σ ⊆ relSσ Y' σ := by
  apply closure_mono
  refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
  intro χ hχ
  exact Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hYY' hφ₀, Set.mem_iUnion.mpr ⟨hσ, hχ⟩⟩⟩

/-- The support of an admissible random extension of a base limit in `Y` is contained in
the relative support (mirror of `support_subset_Sσ`). -/
lemma support_subset_relSσ {Y : Set (PositiveHomSpace ∅ₜ)} {σ : FlagType (Fin n₀)}
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hσ : φ₀ ⟨σ⟩₀ > 0) :
    (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support ⊆ relSσ Y σ := by
  intro χ hχ
  exact subset_closure (Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ₀,
    Set.mem_iUnion.mpr ⟨hσ, hχ⟩⟩⟩)

/-- **Taking `Y = Q₀` recovers the absolute theory** (paper §11.2, "Taking `Y = Q_0`
recovers the absolute theory"): the relative support of the full constrained quotient set
is the root-planting set `S_σ` of `def:root-planting`. -/
theorem Sσ_eq_relSσ {σ : FlagType (Fin n₀)} (T : Constraint σ) :
    Sσ T = relSσ (Qσ T.forb0) σ :=
  rfl

/-- `φ₀ ⟨σ⟩₀ ≥ 0`: the type flag is a single basis flag, so its value is non-negative
(private mirror of the helper in `DownwardAverage.lean`). -/
private lemma type_eval_nonneg {σ : FlagType (Fin n₀)} (φ₀ : PositiveHom ∅ₜ) :
    0 ≤ φ₀ ⟨σ⟩₀ :=
  positiveHom_basisVector_ge_zero φ₀ ⟨n₀, σ.toEmptyTypeFlag⟩

/-- **Relative ensemble soundness** (`prop:relative-soundness`): if `f ∈ A^σ` is
non-negative on the relative support `S_σ(Y)`, then its unlabelled average is
non-negative at every base limit in `Y`. -/
theorem relative_soundness {Y : Set (PositiveHomSpace ∅ₜ)} {σ : FlagType (Fin n₀)}
    {f : FlagAlgebra σ}
    (hf : ∀ χ ∈ relSσ Y σ, 0 ≤ (PositiveHomSpace.toPosHom χ) f)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) :
    0 ≤ φ₀ (⟦f⟧₀ : FlagAlgebra ∅ₜ) := by
  rcases eq_or_lt_of_le (type_eval_nonneg (σ := σ) φ₀) with hσ0 | hσpos
  · -- degenerate base limit: the average vanishes
    rw [downward_eval_eq_zero_of_degenerate hσ0.symm f]
  · -- non-degenerate: evaluate through the random extension
    have hσ : φ₀ ⟨σ⟩₀ > 0 := hσpos
    have h1pos : φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) > 0 :=
      positiveHom_one_downward_pos hσ
    have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ f
    rw [eq_div_iff (ne_of_gt h1pos)] at hspec
    have hint : 0 ≤ ∫ (χ : PositiveHomSpace σ), (PositiveHomSpace.toPosHom χ) f
        ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [Measure.support_mem_ae] with χ hχ
      exact hf χ (support_subset_relSσ hφ₀ hσ hχ)
    rw [← hspec]
    exact mul_nonneg hint (posHom_one_downward_nonneg φ₀)

/-- Relative ensemble non-negativity (condition (b) of `prop:relative-criterion`):
`f ≥ 0` almost surely under the random extension of every admissible base limit in `Y`. -/
def RelEnsembleNonneg (Y : Set (PositiveHomSpace ∅ₜ)) {σ : FlagType (Fin n₀)}
    (f : FlagAlgebra σ) : Prop :=
  ∀ (φ₀ : PositiveHom ∅ₜ), posHomPoint φ₀ ∈ Y → ∀ (hσ : φ₀ ⟨σ⟩₀ > 0),
    (ℙ[φ₀] : Measure (PositiveHomSpace σ)) {χ | 0 ≤ (PositiveHomSpace.toPosHom χ) f} = 1

/-- **Relative support-closure criterion** (`prop:relative-criterion`): non-negativity on
the relative support is equivalent to relative ensemble non-negativity — for *every* `Y`,
unconditionally (the relative analogue of root-plantability is automatic; contrast
`thm:support-criterion`). -/
theorem relative_criterion (Y : Set (PositiveHomSpace ∅ₜ)) {σ : FlagType (Fin n₀)}
    (f : FlagAlgebra σ) :
    (∀ χ ∈ relSσ Y σ, 0 ≤ (PositiveHomSpace.toPosHom χ) f) ↔ RelEnsembleNonneg Y f := by
  constructor
  · -- (a) ⇒ (b): reduce a.e. non-negativity to non-negativity on the support
    intro h φ₀ hφ₀ hσ
    rw [ae_nonneg_iff_nonneg_on_support _ (continuous_eval f)]
    intro χ hχ
    exact h χ (support_subset_relSσ hφ₀ hσ hχ)
  · -- (b) ⇒ (a): the union of supports lies in the closed set `{χ | 0 ≤ χ f}`
    intro hE χ hχ
    have hcl : IsClosed {χ : PositiveHomSpace σ | 0 ≤ (PositiveHomSpace.toPosHom χ) f} :=
      isClosed_le continuous_const (continuous_eval f)
    have hsub : (⋃ (φ₀ : PositiveHom ∅ₜ) (_ : posHomPoint φ₀ ∈ Y) (hσ : φ₀ ⟨σ⟩₀ > 0),
        (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support)
          ⊆ {χ : PositiveHomSpace σ | 0 ≤ (PositiveHomSpace.toPosHom χ) f} := by
      refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
      intro χ' hχ'
      exact (ae_nonneg_iff_nonneg_on_support _ (continuous_eval f)).mp (hE φ₀ hφ₀ hσ) χ' hχ'
    exact (closure_minimal hsub hcl) hχ

end FlagAlgebras.MetaTheory
