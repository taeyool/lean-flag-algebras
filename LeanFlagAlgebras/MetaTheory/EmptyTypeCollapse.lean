import LeanFlagAlgebras.MetaTheory.DownwardAverage
import LeanFlagAlgebras.MetaTheory.MeasureUniqueness
import LeanFlagAlgebras.MetaTheory.HeredClass

/-! # The empty-type collapse (paper §10, `prop:empty-type` and `cor:confined`)

At the empty type the random rooting carries no information: the random extension of any
`φ₀ ∈ Q₀` is the Dirac measure at `φ₀` itself, so `S_∅ = Q_∅ = Q₀` and the empty type is
*always* root-plantable — quotient and ensemble semantics coincide for every element of
the empty-type algebra.  Consequently (`cor:confined`) no density bound in `A⁰[T₁]` is
ensemble-true but quotient-false: every failure of the quotient/ensemble correspondence
happens at a non-empty type.

* `emptyType_flagType_eq_one` — `⟨∅ₜ⟩₀ = 1`, so every `φ₀` is admissible at the empty
  type (`posHom_emptyType_flagType_pos`).
* `extend_emptyType_eq_dirac` — `Ext_∅(φ₀) = δ_{φ₀}` (`prop:empty-type`, first claim).
  The paper's variance computation is packaged here as the moment-uniqueness theorem
  `measure_eq_of_integral_flag_eq`: both measures integrate every flag evaluation to
  `φ₀ f`, because `downward` is the identity at the empty type (`downward_emptyType`).
* `Sσ_emptyType_eq` — `S_∅ = Q₀`.
* `emptyType_rootPlantable` — `(T₀, T₁, ∅)` is always root-plantable
  (`prop:empty-type`, second claim); `heredClass_emptyType_rootPlantable` is the form for
  a hereditary class.
* `emptyType_quotient_iff_ensemble` and `ensemble_implies_quotient_emptyType`
  (`cor:confined`) — the two semantics coincide on `A⁰`; in particular an ensemble-true
  bound is quotient-true.

The `Constraint ∅ₜ` hypothesis `hforb : ∀ F, T.forbσ F ↔ T.forb0 F` says the two
forbidden predicates of the constraint agree at the empty type — automatic for the
constraint of a hereditary class (`HeredClass.constraintOf`), where both say "the
underlying graph leaves the class" (`unlabel_emptyType`).
-/

open MeasureTheory
open scoped Topology

namespace FlagAlgebras.MetaTheory

/-! ## Every base limit is admissible at the empty type -/

/-- At the empty type, the unlabelled type density is the unit: `⟨∅ₜ⟩₀ = 1`.

Proof route: `one_downward_eq` at `σ := ∅ₜ` reads
`⟦1⟧₀ = dnf(emptyFlag ∅ₜ) • ⟨∅ₜ⟩₀`; the left side is `1` by `downward_emptyType` and the
weight is `1` by `downwardNormalizingFactor_emptyType`. -/
lemma emptyType_flagType_eq_one : (⟨∅ₜ⟩₀ : FlagAlgebra ∅ₜ) = 1 := by
  have h := one_downward_eq (σ := (∅ₜ : FlagType (Fin 0)))
  rw [downward_emptyType, downwardNormalizingFactor_emptyType, Rat.cast_one, one_smul] at h
  exact h.symm

/-- Every unlabelled limit is admissible at the empty type: `φ₀ ⟨∅ₜ⟩₀ = 1 > 0`. -/
lemma posHom_emptyType_flagType_pos (φ₀ : PositiveHom ∅ₜ) : φ₀ ⟨∅ₜ⟩₀ > 0 := by
  rw [emptyType_flagType_eq_one, PositiveHom.map_one]
  exact one_pos

/-! ## The random extension at the empty type is a Dirac measure -/

/-- **The empty-type extension is Dirac** (`prop:empty-type`, first claim):
`Ext_∅(φ₀) = δ_{φ₀}` for every `φ₀`.

Proof route: `measure_eq_of_integral_flag_eq` applied to `ℙ[φ₀]` and the Dirac
probability measure at `posHomPoint φ₀`.  The left integrals are
`φ₀ ⟦f⟧₀ / φ₀ ⟦1⟧₀ = φ₀ f` (`probMeasure_extend_emptyType_positiveHom_spec`,
`downward_emptyType`, `PositiveHom.map_one`); the right integrals are
`(toPosHom (posHomPoint φ₀)) f = φ₀ f` (`integral_dirac'` with
`(continuous_eval f).stronglyMeasurable`, then `toPosHom_posHomPoint`). -/
theorem extend_emptyType_eq_dirac (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨∅ₜ⟩₀ > 0) :
    (ℙ[φ₀] : Measure (PositiveHomSpace ∅ₜ)) = Measure.dirac (posHomPoint φ₀) := by
  have hdirac : IsProbabilityMeasure
      (Measure.dirac (posHomPoint φ₀) : Measure (PositiveHomSpace ∅ₜ)) :=
    Measure.dirac.isProbabilityMeasure
  have key : (ℙ[φ₀] : ProbabilityMeasure (PositiveHomSpace ∅ₜ))
      = ⟨Measure.dirac (posHomPoint φ₀), hdirac⟩ := by
    apply measure_eq_of_integral_flag_eq
    intro f
    rw [ProbabilityMeasure.coe_mk, probMeasure_extend_emptyType_positiveHom_spec hσ f,
      downward_emptyType, downward_emptyType, PositiveHom.map_one, div_one,
      integral_dirac' (fun χ : PositiveHomSpace ∅ₜ => (PositiveHomSpace.toPosHom χ) f)
        (posHomPoint φ₀) ((continuous_eval f).stronglyMeasurable)]
    show φ₀ f = (PositiveHomSpace.toPosHom (posHomPoint φ₀)) f
    rw [toPosHom_posHomPoint]
  calc (ℙ[φ₀] : Measure (PositiveHomSpace ∅ₜ))
      = ((⟨Measure.dirac (posHomPoint φ₀), hdirac⟩ :
          ProbabilityMeasure (PositiveHomSpace ∅ₜ)) : Measure (PositiveHomSpace ∅ₜ)) :=
        congrArg ProbabilityMeasure.toMeasure key
    _ = Measure.dirac (posHomPoint φ₀) := rfl

/-- The support of a Dirac measure on the homomorphism space is the singleton of its
point (the space is metrizable, hence T1). -/
lemma support_dirac_eq_singleton (χ : PositiveHomSpace σ) :
    (Measure.dirac χ : Measure (PositiveHomSpace σ)).support = {χ} := by
  -- ⊇: `Measure.mem_support_iff_forall`; any neighbourhood of `χ` has Dirac measure `1`
  --    (`Measure.dirac_apply_of_mem`).
  -- ⊆: if `χ' ≠ χ`, the open set `{χ}ᶜ` is a neighbourhood of `χ'` of Dirac measure `0`
  --    (`Measure.dirac_apply'` on the measurable complement of the closed singleton).
  ext χ'
  rw [Measure.mem_support_iff_forall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hmem : ({χ}ᶜ : Set (PositiveHomSpace σ)) ∈ 𝓝 χ' :=
      isClosed_singleton.isOpen_compl.mem_nhds (Set.mem_compl_singleton_iff.mpr hne)
    have h0 : (Measure.dirac χ : Measure (PositiveHomSpace σ)) {χ}ᶜ = 0 := by
      rw [Measure.dirac_apply' _ isClosed_singleton.measurableSet.compl]
      exact Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Set.mem_singleton χ)) 1
    have hpos := h _ hmem
    rw [h0] at hpos
    exact absurd hpos (lt_irrefl 0)
  · rintro rfl U hU
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
    exact zero_lt_one

/-! ## `S_∅ = Q₀` and root-plantability -/

variable (T : Constraint (∅ₜ : FlagType (Fin 0)))

/-- **The root-planting set collapses at the empty type**: `S_∅ = Q₀`.

Proof route: by `extend_emptyType_eq_dirac` + `support_dirac_eq_singleton`, the union in
the definition of `Sσ` is `{posHomPoint φ₀ : posHomPoint φ₀ ∈ Q₀}`, which equals
`Qσ T.forb0` (⊇ uses `φ₀ := toPosHom χ` with `posHomPoint_toPosHom` and
`posHom_emptyType_flagType_pos`); the two inclusions are closed off with
`closure_minimal` (against `Qσ_isClosed`) and `subset_closure` respectively. -/
theorem Sσ_emptyType_eq : Sσ T = Qσ T.forb0 := by
  refine Set.Subset.antisymm ?_ ?_
  · -- `S_∅ ⊆ Q₀`: every admissible support is the singleton of its (constrained) base point.
    refine closure_minimal ?_ (Qσ_isClosed T.forb0)
    refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
    rw [extend_emptyType_eq_dirac φ₀ hσ, support_dirac_eq_singleton]
    exact Set.singleton_subset_iff.mpr hφ₀
  · -- `Q₀ ⊆ S_∅`: a constrained point is in the support of its own (Dirac) extension.
    intro χ hχ
    have hσχ : (PositiveHomSpace.toPosHom χ) ⟨∅ₜ⟩₀ > 0 :=
      posHom_emptyType_flagType_pos _
    have hmem : posHomPoint (PositiveHomSpace.toPosHom χ) ∈ Qσ T.forb0 := by
      rw [posHomPoint_toPosHom]; exact hχ
    have hsupp : χ ∈ (ℙ[PositiveHomSpace.toPosHom χ] :
        Measure (PositiveHomSpace ∅ₜ)).support := by
      rw [extend_emptyType_eq_dirac _ hσχ, support_dirac_eq_singleton, posHomPoint_toPosHom]
      exact rfl
    exact subset_closure (Set.mem_iUnion.mpr ⟨PositiveHomSpace.toPosHom χ,
      Set.mem_iUnion.mpr ⟨hmem, Set.mem_iUnion.mpr ⟨hσχ, hsupp⟩⟩⟩)

/-- **`prop:empty-type`**: the empty type is always root-plantable, provided the two
forbidden predicates of the constraint agree at the empty type (as they do for any
hereditary class). -/
theorem emptyType_rootPlantable (hforb : ∀ F : FinFlag ∅ₜ, T.forbσ F ↔ T.forb0 F) :
    RootPlantable T := by
  -- `RootPlantable T` unfolds to `Sσ T = Qσ T.forbσ`; rewrite via `Sσ_emptyType_eq` and
  -- identify `Qσ T.forbσ = Qσ T.forb0` through `mem_Qσ_iff` and `hforb`.
  show Sσ T = Qσ T.forbσ
  rw [Sσ_emptyType_eq T]
  ext χ
  rw [mem_Qσ_iff, mem_Qσ_iff]
  exact ⟨fun h F hF => h F ((hforb F).mp hF), fun h F hF => h F ((hforb F).mpr hF)⟩

/-- **`prop:empty-type`, semantic form**: quotient and ensemble semantics coincide for
every element of the empty-type algebra. -/
theorem emptyType_quotient_iff_ensemble (hforb : ∀ F : FinFlag ∅ₜ, T.forbσ F ↔ T.forb0 F)
    (f : FlagAlgebra ∅ₜ) : QuotientNonneg T f ↔ EnsembleNonneg T f :=
  (support_criterion T).mpr (emptyType_rootPlantable T hforb) f

/-- **`cor:confined`**: no density bound in the empty-type algebra is ensemble-true but
quotient-false; every failure of the quotient/ensemble correspondence occurs at a
non-empty type. -/
theorem ensemble_implies_quotient_emptyType
    (hforb : ∀ F : FinFlag ∅ₜ, T.forbσ F ↔ T.forb0 F)
    (f : FlagAlgebra ∅ₜ) (hf : EnsembleNonneg T f) : QuotientNonneg T f :=
  (emptyType_quotient_iff_ensemble T hforb f).mpr hf

/-- The two forbidden predicates of a hereditary class's constraint agree at the empty
type (`unlabel_emptyType`). -/
lemma heredClass_emptyType_forb_iff (hc : HeredClass) (F : FinFlag ∅ₜ) :
    (hc.constraintOf ∅ₜ).forbσ F ↔ (hc.constraintOf ∅ₜ).forb0 F := by
  show ¬ hc.underlyingMem (unlabel F.2) ↔ ¬ hc.underlyingMem F.2
  rw [unlabel_emptyType]

/-- **`prop:empty-type` for a hereditary class**: the constraint of any hereditary class
is root-plantable at the empty type. -/
theorem heredClass_emptyType_rootPlantable (hc : HeredClass) :
    RootPlantable (hc.constraintOf ∅ₜ) :=
  emptyType_rootPlantable _ (heredClass_emptyType_forb_iff hc)

end FlagAlgebras.MetaTheory
