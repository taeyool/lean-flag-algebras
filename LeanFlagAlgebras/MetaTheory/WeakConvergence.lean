import LeanFlagAlgebras.FlagAlgebra.RandomHom
import LeanFlagAlgebras.MetaTheory.MeasureUniqueness

/-! # Weak convergence of σ-rooting measures of an arbitrary convergent flag sequence

The random-extension measure `ℙ[φ₀]` on `PositiveHomSpace σ` is, by construction
(`exists_probMeasure_extend_emptyType_positiveHom`), built from *one particular*
flag sequence converging to `φ₀`: tightness/Prokhorov gives *a* weakly convergent
subsequence, and its limit is comap'd onto `PositiveHomSpace σ`.

For the clone-root-plantability theorem we need the stronger statement that the rooting
measures of an **arbitrary** flag sequence `s` converging to `φ₀` converge weakly to
`ℙ[φ₀]` — there is no freedom to pass to a subsequence, because the sequence is supplied
by the blow-up construction.

The proof is Approach 1 ("every subsequential limit is `ℙ[φ₀]`"):

* On the compact metric space `ProbabilityMeasure (FlagDensitySpace σ)`, every subsequence
  of `s.toProbMeasureSeq hs` has a further weakly convergent sub-subsequence
  (`flagDensitySpace_probMeasure_isSeqCompact`).
* The hypothesis of the integral-identification lemma
  `tendsto_integral_flagDensitySpace_of_converge_flagSeq` is `ConvergesTo s φ₀.coe`, which
  holds for our `s` and (via `convergesTo_comp_of_strictMono`) for every subsequence. Hence
  the verbatim argument of `exists_probMeasure_extend_emptyType_positiveHom` identifies the
  comap onto `PositiveHomSpace σ` of any such sub-subsequential limit with `ℙ[φ₀]`
  (`measure_eq_of_integral_flag_eq`), and so the limit on `FlagDensitySpace σ` is the
  inclusion-pushforward `(ℙ[φ₀]).map Subtype.val`.
* A sequence in a compact metric space all of whose subsequential limits equal a single
  point converges to that point (`tendsto_of_subseq_tendsto`).

## Target form chosen

We state convergence on the ambient compact space `FlagDensitySpace σ`, to the
**inclusion-pushforward** `(ℙ[φ₀]).map Subtype.val` of the random extension. This is the
honest object: each term `(s n).toProbMeasure` is the density profile of a *finite* flag and
is **not** supported on `PositiveHomSpace σ`, so a per-term comap onto `PositiveHomSpace σ`
would not be a probability measure. The inclusion `Subtype.val : PositiveHomSpace σ →
FlagDensitySpace σ` is a measurable embedding, so this weak-limit statement is directly
usable with a Portmanteau argument on `PositiveHomSpace σ`. The headline result is
`tendsto_rootingMeasure_extend`.
-/

open MeasureTheory Filter Topology

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- The inclusion-pushforward of the random extension `ℙ[φ₀]` to the ambient density-profile
space `FlagDensitySpace σ`, i.e. `ℙ[φ₀]` viewed as a probability measure on
`FlagDensitySpace σ` concentrated on `PositiveHomSpace σ`. This is the weak limit of the
σ-rooting measures. -/
noncomputable def rootingMeasureFDS
    (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    : ProbabilityMeasure (FlagDensitySpace σ) :=
  (probMeasure_extend_emptyType_positiveHom φ₀ hσ).map
    (measurable_subtype_coe (p := fun a => a ∈ PositiveHomSpace σ)).aemeasurable

/-- If a probability measure on `FlagDensitySpace σ` has `PositiveHomSpace σ`-mass one, then the
complement is a genuine (ENNReal) null set. -/
private theorem ennreal_compl_positiveHomSpace_null
    {ℙ_fd : ProbabilityMeasure (FlagDensitySpace σ)} (hsupp : ℙ_fd (PositiveHomSpace σ) = 1) :
    (ℙ_fd : Measure (FlagDensitySpace σ)) (PositiveHomSpace σ)ᶜ = 0 := by
  rw [measure_compl positiveHomSpace_measurable (measure_ne_top _ _)]
  have h1 : (ℙ_fd : Measure (FlagDensitySpace σ)) (PositiveHomSpace σ) = 1 := by
    rw [← ENNReal.coe_one, ← hsupp]
    exact (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ℙ_fd _).symm
  rw [h1, measure_univ, tsub_self]

/-! ## Identifying a subsequential limit -/

/-- Any weak limit `ℙ_fd` on `FlagDensitySpace σ` of a subsequence `s.toProbMeasureSeq hs ∘ ϕ`
of an arbitrary flag sequence converging to `φ₀` is the inclusion-pushforward of `ℙ[φ₀]`.

The proof replicates `exists_probMeasure_extend_emptyType_positiveHom`: the subsequence still
converges to `φ₀`, so the integral-identification lemma applies, the limit is supported on
`PositiveHomSpace σ`, its comap there satisfies the defining flag-integral identity, and is
therefore equal to `ℙ[φ₀]` by uniqueness. -/
private theorem subseq_limit_eq_rootingMeasureFDS
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0)
    {s : FlagSeq ∅ₜ} (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    (hconv : ConvergesTo s φ₀.coe)
    {ϕ : ℕ → ℕ} (hϕ : StrictMono ϕ)
    {ℙ_fd : ProbabilityMeasure (FlagDensitySpace σ)}
    (hℙ : Tendsto (s.toProbMeasureSeq hs ∘ ϕ) atTop (𝓝 ℙ_fd)) :
    ℙ_fd = rootingMeasureFDS φ₀ hσ := by
  -- The subsequence still converges to `φ₀` and still has positive σ-density.
  have hconv' : ConvergesTo (s ∘ ϕ) φ₀.coe := convergesTo_comp_of_strictMono hϕ hconv
  have hs' : ∀ n, flagDensity₁ σ.toEmptyTypeFlag ((s ∘ ϕ) n).2 > 0 := fun n => hs (ϕ n)
  -- Rewrite the subsequence of measures as the measure sequence of `s ∘ ϕ`.
  have hℙ' : Tendsto (FlagSeq.toProbMeasureSeq (s ∘ ϕ) hs') atTop (𝓝 ℙ_fd) := by
    have : FlagSeq.toProbMeasureSeq (s ∘ ϕ) hs' = s.toProbMeasureSeq hs ∘ ϕ := by
      funext n; rfl
    rw [this]; exact hℙ
  -- The limit is supported on `PositiveHomSpace σ`.
  have hsupp : ℙ_fd (PositiveHomSpace σ) = 1 :=
    flagSeq_limit_measure_support_positiveHomSpace hconv'.1 hs' hℙ'
  -- The comap onto `PositiveHomSpace σ` is a probability measure (support fact above).
  let ℙ' : ProbabilityMeasure (PositiveHomSpace σ) := {
    val := Measure.comap Subtype.val ℙ_fd
    property := {
      measure_univ := by
        rw [Measure.comap_apply]
        · have h1 : (1 : ENNReal) = ((1 : NNReal) : ENNReal) := rfl
          rw [h1, ← hsupp]
          simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq,
            ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        · exact Subtype.val_injective
        · intro S hS
          exact MeasurableSet.subtype_image positiveHomSpace_measurable hS
        · exact MeasurableSet.univ
    }
  }
  -- `ℙ'` satisfies the defining flag-integral identity of `ℙ[φ₀]`.
  have hℙ'_spec : ∀ (f : FlagAlgebra σ),
      ∫ φ, (PositiveHomSpace.toPosHom φ) f ∂(ℙ' : Measure (PositiveHomSpace σ))
        = (φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) := by
    intro f
    rcases Quotient.exists_rep f with ⟨frep, rfl⟩
    rw [flagVector_eq_sum_basisVector frep]
    simp_rw [sum_quot, downward_sum, PositiveHom.map_sum, Finset.sum_div]
    have hint : ∀ F ∈ frep.support,
        Integrable (fun φ ↦ (PositiveHomSpace.toPosHom φ) ⟦frep F • basisVector F⟧) ℙ' := by
      intro F hF
      constructor
      · apply Measurable.aestronglyMeasurable
        apply Measurable.eval
        rw [measurable_pi_iff]
        intro g
        rcases Quotient.exists_rep g with ⟨grep, rfl⟩
        rw [flagVector_eq_sum_basisVector grep]
        simp_rw [sum_quot, PositiveHom.map_sum]
        apply Finset.measurable_sum grep.support
        intro G hG
        simp_rw [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector]
        apply Measurable.const_mul
        apply Measurable.comp (flagDensitySpace_eval_measurable G) measurable_subtype_coe
      · apply @HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (abs (frep F))
        apply Eventually.of_forall
        intro φ
        rw [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_basisVector, mul_comm]
        simp only [norm_mul, Real.norm_eq_abs]
        apply mul_le_of_le_one_left (abs_nonneg (frep F))
        have hφ := flagDensitySpace_mem_Icc_zero_one φ F
        simp only [Set.mem_Icc] at hφ
        rw [abs_le]
        constructor <;> linarith
    rw [integral_finset_sum frep.support hint]
    apply Finset.sum_congr rfl
    intro F hF
    simp_rw [smul_quot, downward_smul, PositiveHom.map_smul, ← mul_div, integral_const_mul]
    congr
    have hℙF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hℙ' F.toBoundedContinuousFun
    have h' := tendsto_integral_flagDensitySpace_of_converge_flagSeq hσ hconv' hs' F
    rw [← tendsto_nhds_unique hℙF h']
    simp_rw [PositiveHomSpace.toPosHom_basisVector]
    dsimp only [ProbabilityMeasure.coe_mk, ℙ']
    rw [integral_subtype_comap (@positiveHomSpace_measurable _ σ) (fun a ↦ a F)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    -- The integrand vanishes off `PositiveHomSpace σ`, almost surely under `ℙ_fd`: indeed the
    -- set `{x | x ∉ PHS → x F = 0}` contains `PHS`, which already has measure one.
    rw [Filter.eventually_iff,
      mem_ae_iff_prob_eq_one₀ (NullMeasurableSet.of_compl
        (NullMeasurableSet.of_null (by
          rw [Set.compl_setOf]
          apply measure_mono_null (t := (PositiveHomSpace σ)ᶜ)
          · intro x hx
            simp only [Set.mem_setOf_eq, not_forall] at hx
            exact hx.1
          · exact ennreal_compl_positiveHomSpace_null hsupp)))]
    rw [← ENNReal.toNNReal_eq_one_iff]
    apply le_antisymm (ProbabilityMeasure.apply_le_one ℙ_fd _)
    rw [← hsupp]
    apply ProbabilityMeasure.apply_mono ℙ_fd
    intro x hx
    simp only [Set.mem_setOf_eq]
    exact fun hxc => absurd hx hxc
  -- Uniqueness: `ℙ' = ℙ[φ₀]`.
  have hℙ'_eq : ℙ' = ℙ[φ₀] := by
    apply measure_eq_of_integral_flag_eq
    intro f
    rw [hℙ'_spec f, probMeasure_extend_emptyType_positiveHom_spec hσ f]
  -- Push forward back to the ambient space: `ℙ_fd = (ℙ').map Subtype.val`.
  have hmeas : MeasurableSet (PositiveHomSpace σ) := positiveHomSpace_measurable
  have hround : ℙ_fd = ℙ'.map (measurable_subtype_coe (p := fun a => a ∈ PositiveHomSpace σ)).aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    dsimp only [ProbabilityMeasure.coe_mk, ℙ']
    rw [map_comap_subtype_coe hmeas]
    -- `ℙ_fd` is supported on `PositiveHomSpace σ`, so restricting changes nothing.
    symm
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have hset : {a | ¬ a ∈ PositiveHomSpace σ} = (PositiveHomSpace σ)ᶜ := rfl
    rw [hset]
    exact ennreal_compl_positiveHomSpace_null hsupp
  rw [hround, hℙ'_eq]
  rfl

/-! ## The weak-limit theorem -/

/-- **Weak convergence of σ-rooting measures (Approach 1).**

For an arbitrary flag sequence `s` converging to `φ₀` with every term having positive
σ-density, the σ-rooting probability measures `s.toProbMeasureSeq hs` on
`FlagDensitySpace σ` converge weakly to `rootingMeasureFDS φ₀ hσ`, the inclusion-pushforward
of the random extension `ℙ[φ₀]`.

This is the missing weak-limit input to `thm:clone-root-plantable`: combined with the fact
that `Subtype.val : PositiveHomSpace σ → FlagDensitySpace σ` is a measurable embedding, it
yields "the rooting measures converge to `ℙ[φ₀]`" in a form usable with Portmanteau on
`PositiveHomSpace σ`. -/
theorem tendsto_rootingMeasure_extend
    {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨σ⟩₀ > 0)
    (s : FlagSeq ∅ₜ) (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    (hconv : ConvergesTo s φ₀.coe) :
    Tendsto (s.toProbMeasureSeq hs) atTop (𝓝 (rootingMeasureFDS φ₀ hσ)) := by
  -- It suffices to show every subsequence has a further subsequence tending to the limit.
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- `ns : ℕ → ℕ` is an arbitrary index map with `Tendsto ns atTop atTop`.
  -- First make the index strictly monotone: extract `ms₀` so that `ns ∘ ms₀` is strictMono.
  obtain ⟨ms₀, _, hns_ms₀_mono⟩ := strictMono_subseq_of_tendsto_atTop hns
  -- Sequential compactness of the probability measures on `FlagDensitySpace σ`: the sequence
  -- `k ↦ s.toProbMeasureSeq hs (ns (ms₀ k))` has a weakly convergent subsequence.
  have hcompact := @flagDensitySpace_probMeasure_isSeqCompact _ σ
  obtain ⟨ℙ_fd, _, ms₁, hms₁_mono, hms₁_lim⟩ :=
    hcompact (x := fun k => s.toProbMeasureSeq hs (ns (ms₀ k))) (fun _ => trivial)
  -- The total index `ϕ = n ↦ ns (ms₀ (ms₁ n))` is strictly monotone.
  have hϕ_mono : StrictMono (fun n => ns (ms₀ (ms₁ n))) :=
    hns_ms₀_mono.comp hms₁_mono
  -- The convergent sub-subsequence equals `s.toProbMeasureSeq hs ∘ ϕ`.
  have hℙ_fd : Tendsto (s.toProbMeasureSeq hs ∘ (fun n => ns (ms₀ (ms₁ n)))) atTop (𝓝 ℙ_fd) :=
    hms₁_lim
  -- By the identification lemma the limit is `rootingMeasureFDS`.
  have hlimeq : ℙ_fd = rootingMeasureFDS φ₀ hσ :=
    subseq_limit_eq_rootingMeasureFDS hσ hs hconv hϕ_mono hℙ_fd
  refine ⟨fun n => ms₀ (ms₁ n), ?_⟩
  rw [← hlimeq]
  exact hms₁_lim

end FlagAlgebras.MetaTheory
