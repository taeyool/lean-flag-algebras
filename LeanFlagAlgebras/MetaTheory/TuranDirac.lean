import LeanFlagAlgebras.MetaTheory.TuranAut
import LeanFlagAlgebras.MetaTheory.RelativeSupport
import LeanFlagAlgebras.MetaTheory.EmptyTypeCollapse
import LeanFlagAlgebras.MetaTheory.WeakConvergence
import Mathlib.MeasureTheory.Measure.DiracProba

/-! # The Turán extension measures are Dirac (paper §11.5 supporting layer)

If every term of a convergent in-class flag sequence has a UNIQUE `σ`-labelling
(`labelExtensions` a subsingleton, `TuranAut`), each finite rooting measure is a Dirac;
rooting-measure weak convergence (`tendsto_rootingMeasure_extend`) then forces the
extension measure of the limit to be a Dirac too — `diracProba` is a closed topological
embedding on the compact metric `FlagDensitySpace σ`
(`Mathlib.MeasureTheory.Measure.DiracProba`), so a weak limit of Diracs is a Dirac and the
underlying points converge.  Hence the relative support of the singleton constraint set is
a single point whose profile is the limit of the (constant-per-term) finite profiles.

This module also fixes, once and for all, a CHOICE of the balanced complete `r`-partite
limit `turanLimit r hr` together with its witnessing subsequence (re-running
`TuranLimit.exists_turan_limit`'s construction with the sequence exposed).
-/

open MeasureTheory Filter SimpleGraph
open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Finite rooting measures with a unique labelling are Dirac -/

/-- If all `σ`-labellings of `F` coincide, the rooting measure of `F` is the Dirac at the
(unique) labelling's density profile. -/
lemma toProbMeasure_eq_dirac_of_subsingleton (F : FinFlag ∅ₜ)
    (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0)
    {G : FlagWithSize σ F.1} (hG : G ∈ labelExtensions F.2 σ)
    (hsing : ∀ G₁ ∈ labelExtensions F.2 σ, ∀ G₂ ∈ labelExtensions F.2 σ, G₁ = G₂) :
    (F.toProbMeasure hF : Measure (FlagDensitySpace σ))
      = Measure.dirac (funFromFlagWithSizeToFlagDensitySpace σ F.1 G) := by
  -- `hsing` + `hG` make `labelExtensions F.2 σ = {G}` (`Finset.eq_singleton_iff_unique_mem`).
  -- `toProbMeasure_apply_eq_dnf_ratio` (RootingUniform) then gives, for any measurable set
  -- `A`, the filtered dnf-sum over the singleton as `dnf G` or `0` according to whether the
  -- profile of `G` lies in `A`, with total `dnf G`; equality of the two probability
  -- measures follows from equality of their `toReal` values on every measurable set.
  have hL : labelExtensions F.2 σ = {G} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hG, fun b hb => hsing b hb G hG⟩
  have hdnf : (0 : ℝ) < (downwardNormalizingFactor G : ℝ) := by
    exact_mod_cast downwardNormalizingFactor_pos G
  refine Measure.ext fun A hA => ?_
  have hratio := toProbMeasure_apply_eq_dnf_ratio F hF A
  rw [hL, Finset.filter_singleton, Finset.sum_singleton] at hratio
  by_cases hmem : funFromFlagWithSizeToFlagDensitySpace σ F.1 G ∈ A
  · rw [if_pos hmem, Finset.sum_singleton, div_self (ne_of_gt hdnf)] at hratio
    rw [(ENNReal.toReal_eq_one_iff _).mp hratio, Measure.dirac_apply' _ hA,
      Set.indicator_of_mem hmem]
    rfl
  · rw [if_neg hmem, Finset.sum_empty, zero_div] at hratio
    have h0 : (F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hratio).resolve_right (measure_ne_top _ _)
    rw [h0, Measure.dirac_apply' _ hA, Set.indicator_of_notMem hmem]

/-! ## Weak limits of Diracs, and Dirac-ness of the extension -/

/-- **The extension measure of a limit with unique labellings is Dirac**: given a
convergent sequence with positive type densities whose terms all have a unique
`σ`-labelling `Gsel n`, the extension measure `ℙ[φ]` is the Dirac at a point `χ`, and the
finite profiles converge to `χ`'s profile coordinatewise. -/
theorem extend_eq_dirac_of_labelExtensions_subsingleton
    {s : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ}
    (hconv : ConvergesTo s φ.coe) (hσ : φ ⟨σ⟩₀ > 0)
    (hs : ∀ n, flagDensity₁ σ.toEmptyTypeFlag (s n).2 > 0)
    (Gsel : ∀ n, FlagWithSize σ (s n).1)
    (hGsel : ∀ n, Gsel n ∈ labelExtensions (s n).2 σ)
    (hsing : ∀ n, ∀ G₁ ∈ labelExtensions (s n).2 σ,
      ∀ G₂ ∈ labelExtensions (s n).2 σ, G₁ = G₂) :
    ∃ χ : PositiveHomSpace σ,
      (ℙ[φ] : Measure (PositiveHomSpace σ)) = Measure.dirac χ ∧
      ∀ F : FinFlag σ,
        Tendsto (fun n => (flagDensity₁ F.2 (Gsel n) : ℝ)) atTop (𝓝 (χ.val F)) := by
  classical
  set xseq : ℕ → FlagDensitySpace σ :=
    fun n => funFromFlagWithSizeToFlagDensitySpace σ (s n).1 (Gsel n)
  -- 1. each finite rooting measure is the Dirac at its unique labelling's profile
  have hterm : ∀ n, s.toProbMeasureSeq hs n = diracProba (xseq n) := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    exact toProbMeasure_eq_dirac_of_subsingleton (s n) (hs n) (hGsel n) (hsing n)
  -- 2. weak convergence of the Diracs to the pushforward of `ℙ[φ]`
  have hlim : Tendsto (fun n => diracProba (xseq n)) atTop (𝓝 (rootingMeasureFDS φ hσ)) :=
    (tendsto_congr hterm).mp (tendsto_rootingMeasure_extend hσ s hs hconv)
  -- 3. the range of `diracProba` is compact (continuous image of a compact space), hence
  --    closed in the T2 space of probability measures, so the weak limit is a Dirac
  have hclosed : IsClosed (Set.range (diracProba :
      FlagDensitySpace σ → ProbabilityMeasure (FlagDensitySpace σ))) :=
    (isCompact_range continuous_diracProba).isClosed
  obtain ⟨x, hdp⟩ : rootingMeasureFDS φ hσ ∈ Set.range (diracProba :
      FlagDensitySpace σ → ProbabilityMeasure (FlagDensitySpace σ)) :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => Set.mem_range_self _)
  -- 4. `diracProba` is a topological embedding, so the profiles converge to `x`
  have hxlim : Tendsto xseq atTop (𝓝 x) := by
    refine isEmbedding_diracProba.tendsto_nhds_iff.mpr ?_
    show Tendsto (fun n => diracProba (xseq n)) atTop (𝓝 (diracProba x))
    rw [hdp]
    exact hlim
  -- 5. the `Subtype.val`-pushforward of `ℙ[φ]` is the Dirac at `x`
  have hmap : (ℙ[φ] : Measure (PositiveHomSpace σ)).map Subtype.val = Measure.dirac x := by
    have hcoe : (rootingMeasureFDS φ hσ : Measure (FlagDensitySpace σ))
        = (ℙ[φ] : Measure (PositiveHomSpace σ)).map Subtype.val :=
      ProbabilityMeasure.toMeasure_map _ _
    have hPMeq : (rootingMeasureFDS φ hσ : Measure (FlagDensitySpace σ))
        = Measure.dirac x := congrArg ProbabilityMeasure.toMeasure hdp.symm
    rw [← hcoe, hPMeq]
  -- 6. `x` carries full mass on the measurable `PositiveHomSpace σ`, so it lies on it
  have hxmem : x ∈ PositiveHomSpace σ := by
    by_contra hx
    have h1 : (Measure.dirac x : Measure (FlagDensitySpace σ)) (PositiveHomSpace σ) = 1 := by
      rw [← hmap, Measure.map_apply measurable_subtype_coe positiveHomSpace_measurable,
        Subtype.coe_preimage_self, measure_univ]
    rw [Measure.dirac_apply' x positiveHomSpace_measurable, Set.indicator_of_notMem hx] at h1
    exact zero_ne_one h1
  refine ⟨⟨x, hxmem⟩, ?_, ?_⟩
  · -- pull the pushforward identity back through the measurable embedding `Subtype.val`
    have hemb : MeasurableEmbedding (Subtype.val : PositiveHomSpace σ → FlagDensitySpace σ) :=
      MeasurableEmbedding.subtype_coe positiveHomSpace_measurable
    have hdcast : (Measure.dirac (⟨x, hxmem⟩ : PositiveHomSpace σ)).map Subtype.val
        = Measure.dirac x := Measure.map_dirac measurable_subtype_coe _
    calc (ℙ[φ] : Measure (PositiveHomSpace σ))
        = ((ℙ[φ] : Measure (PositiveHomSpace σ)).map Subtype.val).comap Subtype.val :=
          (hemb.comap_map _).symm
      _ = ((Measure.dirac (⟨x, hxmem⟩ : PositiveHomSpace σ)).map Subtype.val).comap
            Subtype.val := by rw [hmap, hdcast]
      _ = Measure.dirac ⟨x, hxmem⟩ := hemb.comap_map _
  · -- coordinatewise convergence: continuous coordinate evaluations of `xₙ → x`
    intro F
    have hval : Continuous (fun a : FlagDensitySpace σ => a.val F) :=
      (continuous_apply F).comp continuous_subtype_val
    exact (hval.tendsto x).comp hxlim

/-- The relative support of a singleton constraint set with a Dirac extension is the
singleton of the Dirac point. -/
theorem relSσ_singleton_of_extend_dirac {φ : PositiveHom ∅ₜ} {χ : PositiveHomSpace σ}
    (hσ : φ ⟨σ⟩₀ > 0)
    (hdirac : (ℙ[φ] : Measure (PositiveHomSpace σ)) = Measure.dirac χ) :
    relSσ {posHomPoint φ} σ = {χ} := by
  -- Unfold `relSσ`.  Any `φ₀` in the union's index has `posHomPoint φ₀ = posHomPoint φ`,
  -- hence `φ₀.coe = φ.coe` (congrArg on `.val` + `posHomPoint`'s definition), hence
  -- `φ₀ u = φ u` for every `u` (a hom is determined by its profile — evaluate through
  -- `PositiveHom.coe_flag`/linearity: two homs equal on all `⟦basisVector F⟧` agree on
  -- the span; if a packaged lemma is missing, prove `ℙ[φ₀] = ℙ[φ]` instead via
  -- `measure_eq_of_integral_flag_eq` + the extension spec, whose right-hand sides only
  -- involve `φ₀ ⟦f⟧₀ / φ₀ ⟦1⟧₀` — values determined by the profile).
  -- So every summand support is `(Measure.dirac χ).support = {χ}`
  -- (`support_dirac_eq_singleton`, EmptyTypeCollapse), the union over the (nonempty —
  -- witness `φ` itself with `hσ`) index is `{χ}`, and `closure {χ} = {χ}`
  -- (`isClosed_singleton.closure_eq`).
  apply Set.Subset.antisymm
  · -- every summand support is `{χ}`, and the singleton is closed
    refine closure_minimal ?_ isClosed_singleton
    refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ =>
      Set.iUnion_subset fun hσ' => ?_
    have heq : posHomPoint φ₀ = posHomPoint φ := hφ₀
    have hcoe : φ₀ = φ := PositiveHom.coe_injective (Subtype.ext_iff.mp heq)
    have hd : (probMeasure_extend_emptyType_positiveHom φ₀ hσ' :
        Measure (PositiveHomSpace σ)) = Measure.dirac χ := by
      subst hcoe
      exact hdirac
    rw [hd, support_dirac_eq_singleton]
  · -- `χ` is in the support of its own (Dirac) extension, indexed by `φ` itself
    intro y hy
    have hyχ : y = χ := hy
    subst hyχ
    have hsupp : y ∈ (ℙ[φ] : Measure (PositiveHomSpace σ)).support := by
      rw [hdirac, support_dirac_eq_singleton]
      exact rfl
    exact support_subset_relSσ (Set.mem_singleton _) hσ hsupp

/-! ## The chosen Turán limit, with its subsequence exposed -/

/-- The balanced complete `r`-partite limit: a fixed choice of a constrained limit of the
Turán flag sequence along a strictly monotone subsequence, packaged with everything the
Dirac machinery needs.  (Re-runs `exists_turan_limit`'s construction — subsequence
extraction + `flagSeq_limit_mem_positiveHom` — with the sequence data exposed.) -/
theorem exists_turan_limit_with_seq (r : ℕ) (hr : 2 ≤ r) :
    ∃ (ϕ : ℕ → ℕ) (φ : PositiveHom ∅ₜ),
      StrictMono ϕ ∧
      ConvergesTo (turanFlagSeq r ∘ ϕ) φ.coe ∧
      posHomPoint φ ∈ Qσ (constraintOf (cliqueFreeClass (r + 1)) ∅ₜ).forb0 ∧
      φ ρ = ((r : ℝ) - 1) / r := by
  -- Same construction as `exists_turan_limit` (TuranLimit.lean) — subsequence extraction via
  -- `increasing_flagSeq_contain_convergent_subseq`, limit hom via
  -- `flagSeq_limit_mem_positiveHom`, in-class membership, and the `ρ`-value via the
  -- edge-density limit along the subsequence — but with `ϕ` and the `ConvergesTo` witness
  -- kept in the statement rather than discarded.
  have hinc : Increases (turanFlagSeq r) := by
    apply increases_of_consecutive_lt
    intro n
    show r * (n + 1) < r * (n + 2)
    have h0 : 0 < r := by omega
    calc r * (n + 1) < r * (n + 1) + r := by omega
      _ = r * (n + 2) := by ring
  obtain ⟨a, ϕ, hmono, hconv⟩ :=
    increasing_flagSeq_contain_convergent_subseq (turanFlagSeq r) hinc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (turanFlagSeq r ∘ ϕ) hconv
  obtain ⟨-, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  refine ⟨ϕ, φ, hmono, ?_, ?_, ?_⟩
  · -- the subsequence converges to `φ`'s profile
    rw [hφ]
    exact hconv
  · -- constrainedness: each flag's graph is `CliqueFree (r+1)`, so every forbidden flag
    -- has density `0` along the sequence, hence value `0` in the limit
    rw [mem_Qσ_iff]
    intro D hD
    rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
    have hzero : ∀ k, flagDensitySeq (turanFlagSeq r ∘ ϕ) k D = 0 := by
      intro k
      show (flagDensity₁ D.2 (turanFlagSeq r (ϕ k)).2 : ℝ) = 0
      exact_mod_cast
        (cliqueFreeClass (r + 1)).toHeredClass.forbiddenFree_of_mem (σ := ∅ₜ)
          (turanGraph (r * (ϕ k + 1)) r)
          (turanFlagSeq_cliqueFree r (by omega) (ϕ k)) D hD
    have hlim : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ ϕ) k D) atTop
        (𝓝 (a D)) := hpt D
    rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
    exact hlim.symm
  · -- the `ρ`-value: `φ ρ` is the unlabelled-edge density coefficient of the limit
    -- (the normaliser is `1` by §9.2), the limit of the Turán edge densities
    have hedgeunlabel : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, unlabelledEdgeFlag⟩ :=
      rfl
    have hρval : φ ρ
        = (downwardNormalizingFactor edgeFF.2 : ℝ) * φ.coe ⟨2, unlabelledEdgeFlag⟩ := by
      show φ (downward e) = _
      rw [e, downward_basisVector, PositiveHom.map_smul, hedgeunlabel, ← PositiveHom.coe_flag]
    rw [downwardNormalizingFactor_edge_eq_one] at hρval
    have hcoe : φ.coe ⟨2, unlabelledEdgeFlag⟩ = a ⟨2, unlabelledEdgeFlag⟩ := by rw [hφ]
    have h1 : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ ϕ) k ⟨2, unlabelledEdgeFlag⟩)
        atTop (𝓝 (a ⟨2, unlabelledEdgeFlag⟩)) := hpt _
    have h2 : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ ϕ) k ⟨2, unlabelledEdgeFlag⟩)
        atTop (𝓝 (((r : ℝ) - 1) / r)) :=
      (turanFlagSeq_edge_density_tendsto r hr).comp hmono.tendsto_atTop
    have huniq : a ⟨2, unlabelledEdgeFlag⟩ = ((r : ℝ) - 1) / r := tendsto_nhds_unique h1 h2
    rw [hρval, hcoe, huniq]
    norm_num

/-- The chosen witnessing subsequence. -/
noncomputable def turanSubseq (r : ℕ) (hr : 2 ≤ r) : ℕ → ℕ :=
  (exists_turan_limit_with_seq r hr).choose

/-- **The balanced complete `r`-partite limit** (a fixed choice). -/
noncomputable def turanLimit (r : ℕ) (hr : 2 ≤ r) : PositiveHom ∅ₜ :=
  (exists_turan_limit_with_seq r hr).choose_spec.choose

/-- Specification of `turanSubseq`/`turanLimit`. -/
lemma turanLimit_spec (r : ℕ) (hr : 2 ≤ r) :
    StrictMono (turanSubseq r hr) ∧
    ConvergesTo (turanFlagSeq r ∘ turanSubseq r hr) (turanLimit r hr).coe ∧
    posHomPoint (turanLimit r hr) ∈ Qσ (constraintOf (cliqueFreeClass (r + 1)) ∅ₜ).forb0 ∧
    (turanLimit r hr) ρ = ((r : ℝ) - 1) / r :=
  (exists_turan_limit_with_seq r hr).choose_spec.choose_spec

/-- The chosen limit lies in the Turán slice. -/
lemma turanLimit_mem_slice (r : ℕ) (hr : 2 ≤ r) :
    posHomPoint (turanLimit r hr) ∈ turanSlice r := by
  -- `posHomPoint_mem_eqSlice` from `turanLimit_spec`, as in `turanSlice_nonempty`.
  obtain ⟨-, -, hQ, hρ⟩ := turanLimit_spec r hr
  exact posHomPoint_mem_eqSlice.mpr ⟨hQ, hρ⟩

end FlagAlgebras.MetaTheory
