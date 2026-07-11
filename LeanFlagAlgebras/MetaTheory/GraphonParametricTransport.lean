import LeanFlagAlgebras.MetaTheory.GraphonKernelTransport
import LeanFlagAlgebras.MetaTheory.GraphonRepresentation

/-! # The parametric rooted transport and the top-endpoint recovery (Cor 106)

The general-`r` form of the rooted transport in `GraphonKernelTransport.lean`, formalising
`cor:top-endpoint-recovery` (Cor 106) of `paper.tex` together with the `R_τ⁻` kernel
functional.  The classical inputs are, as everywhere, explicit named hypotheses (`hZykov` —
the non-equality Zykov bound — and, in the `_of_rep_exists` form, Lovász–Szegedy existence).

* `parametricP4_graphon_Rtau_eq_zero` / `parametricP4_graphon_Reta_eq_zero` — the general-`r`
  transports: for a graphon whose `φ_W` lies in the parametric slice `Y_r`, the two local
  equations hold a.e., i.e. `R_τ(r) = R_η(r) = 0` (the general-`r` form of the
  `k4freeP4_graphon_*` theorems; only the slice equations change, the measure-theoretic
  chain is `r`-free).
* `Graphon.RtauMinus` — the `r`-independent kernel functional
  `R_τ⁻(W) = ∫∫ W(x,y)(d(x) − d(y))² `, with its a.e. characterisation.
* `graphonHom_f₂_eq_RtauMinus` — **the hom→kernel bridge for the τ⁻ square, with no new
  density computations**: `φ_W(f₂) = R_τ⁻(W)`, via the extension-measure spec at the edge
  type applied to `f := (a_τ − b_τ)²`, the measure identification
  `rootedViewMeasure_eq_extend`, and the dictionary `a_τ − b_τ = d(u) − d(v)`.
* `parametricP4_graphon_RtauMinus_le` — the kernel-level third clause of Thm 112(i):
  `p₂(r)·R_τ⁻(W) ≤ Δ` for `K_{r+1}`-free-consistent `φ_W` (from `parametricP4_sq_bounds`
  through the bridge); `parametricP4_graphon_RtauMinus_eq_zero` — exact vanishing on the
  slice (where `Δ = 0`).
* `parametricP4_graphon_top_endpoint_rigidity` — **the kernel-level Cor 106**: slice
  membership + the single scalar pin `edgeDensity = α_r⁺` identify `W` a.e. with the
  balanced complete `r`-partite graphon (`Graphon.slice_rigidity` with all three hypotheses
  discharged; the pin is NOT derivable from membership at `r ≥ 4` — `moments_interval` only
  confines it to `[α_r⁻, α_r⁺]` — which is exactly the paper's point).
* `parametricP4_top_endpoint_of_represents` / `_of_rep_exists` — the paper-verbatim forms,
  quantified over representatives (no existence input) and conditional on `hrep`
  respectively, in the style of `GraphonRepresentation.lean`.

Stated at `3 ≤ r` (the paper fixes `r ≥ 4` because `r = 3` is already covered
unconditionally by `thm:k4free-p4-tripartite`; the wider range is a benign generalisation).
All slice-consuming theorems are Tier-2.
-/

open MeasureTheory unitInterval
open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open CompleteGraphFreeP4

/-! ## Private infrastructure: local re-derivations of upstream-private lemmas -/

/-- On a probability space, a measurable function squeezed between two constants is
integrable (local copy of the workhorse used throughout `MetaTheory/`). -/
private lemma integrable_of_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-- `FlagType_2_1.Adj 0 1` holds (the `τ` type is an edge; local re-derivation of the
private idiom of `GraphonKernelTransport.lean`). -/
private lemma tau_adj01 : FlagType_2_1.Adj 0 1 :=
  (FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff Sym2FlagType_2_1 0 1).mpr (by decide)

/-- `¬ FlagType_2_0.Adj 0 1` (the `η` type is a non-edge). -/
private lemma eta_not_adj01 : ¬ FlagType_2_0.Adj 0 1 := fun h =>
  absurd ((FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff Sym2FlagType_2_0 0 1).mp h)
    (by decide)

/-- Strict positivity of `p₂` for `r ≥ 3` (local copy of the `ParametricP4Slice.lean`
private lemma; the API exports only `p₂_nonneg`). -/
private lemma p₂_pos (r : ℕ) (hr : 3 ≤ r) : 0 < CompleteGraphFreeP4.p₂ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := CompleteGraphFreeP4.denom_factor_pos r hr
  unfold CompleteGraphFreeP4.p₂
  apply div_pos
  · nlinarith [sq_nonneg ((r : ℝ) - 3)]
  · linarith

/-! ## The `R_τ⁻` kernel functional -/

namespace Graphon

/-- The `r`-independent τ⁻ square error: `R_τ⁻(W) = ∫∫ W(x,y)(d(x) − d(y))²`
(`prop:k4free-p4-certificate-stability`; the kernel form of the certificate square `f₂`). -/
noncomputable def RtauMinus (G : Graphon) : ℝ :=
  ∫ z : I × I, G.W z.1 z.2 * (G.deg z.1 - G.deg z.2) ^ 2

lemma RtauMinus_nonneg (G : Graphon) : 0 ≤ G.RtauMinus :=
  integral_nonneg fun z => mul_nonneg (G.nonneg z.1 z.2) (sq_nonneg _)

/-- `R_τ⁻` vanishes iff the degrees agree across almost every edge. -/
theorem RtauMinus_eq_zero_iff_ae (G : Graphon) :
    G.RtauMinus = 0 ↔ ∀ᵐ z : I × I, G.W z.1 z.2 = 0 ∨ G.deg z.1 = G.deg z.2 := by
  have hmeas : Measurable (fun z : I × I => G.W z.1 z.2 * (G.deg z.1 - G.deg z.2) ^ 2) :=
    G.measurable.mul
      (((G.measurable_deg.comp measurable_fst).sub (G.measurable_deg.comp measurable_snd)).pow_const 2)
  have hint : Integrable (fun z : I × I => G.W z.1 z.2 * (G.deg z.1 - G.deg z.2) ^ 2) :=
    integrable_of_bounds (a := 0) (b := 1) hmeas
      (fun z => mul_nonneg (G.nonneg z.1 z.2) (sq_nonneg _))
      (fun z => by
        have h1 := G.deg_nonneg z.1; have h2 := G.deg_le_one z.1
        have h3 := G.deg_nonneg z.2; have h4 := G.deg_le_one z.2
        nlinarith [G.le_one z.1 z.2, G.nonneg z.1 z.2])
  have hnn : (0 : I × I → ℝ) ≤ fun z : I × I => G.W z.1 z.2 * (G.deg z.1 - G.deg z.2) ^ 2 :=
    fun z => mul_nonneg (G.nonneg z.1 z.2) (sq_nonneg _)
  have hR : G.RtauMinus = ∫ z : I × I, G.W z.1 z.2 * (G.deg z.1 - G.deg z.2) ^ 2 := rfl
  rw [hR, integral_eq_zero_iff_of_nonneg hnn hint]
  constructor
  · intro h
    filter_upwards [h] with z hz
    simp only [Pi.zero_apply] at hz
    rcases mul_eq_zero.mp hz with h' | h'
    · exact Or.inl h'
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp h'))
  · intro h
    filter_upwards [h] with z hz
    rcases hz with h' | h'
    · simp [h']
    · simp [h']

end Graphon

/-! ## The general-`r` transports -/

variable {r : ℕ} (hr : 3 ≤ r)
variable (hZykov : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
    φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3)

include hr hZykov in
/-- **The `τ`-transport at general `r`**: `R_τ(r) = 0` for any graphon whose `φ_W` lies in
the parametric slice (the general-`r` form of `k4freeP4_graphon_Rtau_eq_zero`, with
`parametricP4_tau_equation` in place of the `r = 3` slice equation; the measure-theoretic
chain — `support_subset_relSσ`, `rootedViewMeasure_eq_extend`, `ae_of_ae_map`,
`ae_withDensity_iff`, the kernel dictionary — is unchanged). -/
theorem parametricP4_graphon_Rtau_eq_zero (W : Graphon)
    (hστ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ parametricP4Slice r) :
    W.Rtau r = 0 := by
  rw [W.Rtau_eq_zero_iff_ae]
  have hae1 : ∀ᵐ χ ∂ (ℙ[graphonHom W] : Measure (PositiveHomSpace FlagType_2_1)),
      ((r : ℝ) - 2) * ((PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1
          + (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2)
        = 2 * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 := by
    filter_upwards [Measure.support_mem_ae] with χ hχ
    exact parametricP4_tau_equation hr hZykov χ (support_subset_relSσ hmem hστ hχ)
  rw [← rootedViewMeasure_eq_extend W FlagType_2_1 hστ] at hae1
  unfold rootedViewMeasure at hae1
  have hcne : (ENNReal.ofReal (rootMass W FlagType_2_1))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [Measure.ae_ennreal_smul_measure_iff hcne] at hae1
  have hae2 := ae_of_ae_map (measurable_rootedViewPoint W FlagType_2_1).aemeasurable hae1
  have hmeasf : Measurable (fun z : I × I => ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2)) :=
    (measurable_rootWeight W FlagType_2_1).ennreal_ofReal
  have hae3 := (ae_withDensity_iff hmeasf).mp hae2
  filter_upwards [hae3] with z hz
  by_cases hadm : RootAdmissible W FlagType_2_1 z.1 z.2
  · right
    have hne : ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hadm).ne'
    have heq := hz hne
    rw [rootedViewPoint_of_admissible W FlagType_2_1 z hadm, toPosHom_posHomPoint] at heq
    rw [graphonRootedHom_a_tau, graphonRootedHom_b_tau, graphonRootedHom_g_tau] at heq
    unfold Graphon.ellTau
    linarith [heq]
  · left
    unfold RootAdmissible at hadm
    unfold rootWeight adjWeight at hadm
    rw [if_pos tau_adj01] at hadm
    linarith [not_lt.mp hadm, W.nonneg z.1 z.2]

include hr hZykov in
/-- **The `η`-transport at general `r`**: `R_η(r) = 0` on the parametric slice. -/
theorem parametricP4_graphon_Reta_eq_zero (W : Graphon)
    (hση : (graphonHom W) ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ parametricP4Slice r) :
    W.Reta r = 0 := by
  rw [W.Reta_eq_zero_iff_ae]
  have hae1 : ∀ᵐ χ ∂ (ℙ[graphonHom W] : Measure (PositiveHomSpace FlagType_2_0)),
      ((r : ℝ) - 1) * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0
        = (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 := by
    filter_upwards [Measure.support_mem_ae] with χ hχ
    exact parametricP4_eta_equation hr hZykov χ (support_subset_relSσ hmem hση hχ)
  rw [← rootedViewMeasure_eq_extend W FlagType_2_0 hση] at hae1
  unfold rootedViewMeasure at hae1
  have hcne : (ENNReal.ofReal (rootMass W FlagType_2_0))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [Measure.ae_ennreal_smul_measure_iff hcne] at hae1
  have hae2 := ae_of_ae_map (measurable_rootedViewPoint W FlagType_2_0).aemeasurable hae1
  have hmeasf : Measurable (fun z : I × I => ENNReal.ofReal (rootWeight W FlagType_2_0 z.1 z.2)) :=
    (measurable_rootWeight W FlagType_2_0).ennreal_ofReal
  have hae3 := (ae_withDensity_iff hmeasf).mp hae2
  filter_upwards [hae3] with z hz
  by_cases hadm : RootAdmissible W FlagType_2_0 z.1 z.2
  · right
    have hne : ENNReal.ofReal (rootWeight W FlagType_2_0 z.1 z.2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hadm).ne'
    have heq := hz hne
    rw [rootedViewPoint_of_admissible W FlagType_2_0 z hadm, toPosHom_posHomPoint] at heq
    rw [graphonRootedHom_z_eta, graphonRootedHom_g_eta] at heq
    unfold Graphon.ellEta
    linarith [heq]
  · left
    unfold RootAdmissible at hadm
    unfold rootWeight adjWeight at hadm
    rw [if_neg eta_not_adj01] at hadm
    have h1 := W.le_one z.1 z.2
    linarith [not_lt.mp hadm]

/-! ## The hom→kernel bridge for the `τ⁻` square -/

/-- **The `f₂` bridge**: `φ_W(f₂) = R_τ⁻(W)`.

Proof route (no new density computations): `f₂ = ⟦l₂²⟧₀` with
`l₂ = a_τ − b_τ : FlagAlgebra FlagType_2_1`; the extension-measure spec
(`probMeasure_extend_emptyType_positiveHom_spec`) at `f := l₂ * l₂` gives
`∫ χ (l₂ * l₂) dℙ[φ_W] = φ_W⟦l₂²⟧₀ / φ_W⟦1⟧₀`; homs are multiplicative, so the integrand is
`(χ l₂)²`; transport the integral through `rootedViewMeasure_eq_extend` to the weighted
pair integral `(1/rootMass) ∫∫ rootWeight(u,v) · ((graphonRootedHom …) l₂)² du dv`; the
dictionary (`graphonRootedHom_a_tau` − `graphonRootedHom_b_tau`) evaluates
`(graphonRootedHom W FlagType_2_1 u v h) l₂ = deg u − deg v` on the admissible set, and
`rootWeight` at the edge type is `W(u,v)` (the type has an edge); finally
`φ_W⟦1⟧₀ = rootMass` (`one_downward_eq` + `dnf_emptyFlag_two` + `rootMass_eq_typeFlag`)
cancels the normalisation. -/
theorem graphonHom_f₂_eq_RtauMinus (W : Graphon)
    (hστ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0) :
    (graphonHom W) CompleteGraphFreeP4.f₂ = W.RtauMinus := by
  set l₂ : FlagAlgebra FlagType_2_1 :=
    (1 : ℝ) • FlagAlgebra_3_2_1_1 - (1 : ℝ) • FlagAlgebra_3_2_1_2 with hl2def
  have hf2eq : CompleteGraphFreeP4.f₂ = ⟦l₂ * l₂⟧₀ := by
    dsimp only [CompleteGraphFreeP4.f₂]
    rw [← hl2def, pow_two]
  have hden : (graphonHom W) ⟦(1 : FlagAlgebra FlagType_2_1)⟧₀ = rootMass W FlagType_2_1 := by
    rw [one_downward_eq, PositiveHom.map_smul, ← rootMass_eq_typeFlag, dnf_emptyFlag_two]
    norm_num
  have hmR : rootMass W FlagType_2_1 > 0 := by rw [rootMass_eq_typeFlag]; exact hστ
  have hmRne : rootMass W FlagType_2_1 ≠ 0 := ne_of_gt hmR
  have hspec0 := probMeasure_extend_emptyType_positiveHom_spec hστ (l₂ * l₂)
  rw [hden] at hspec0
  rw [← rootedViewMeasure_eq_extend W FlagType_2_1 hστ] at hspec0
  set c : ENNReal := ENNReal.ofReal (rootMass W FlagType_2_1) with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef, ne_eq, ENNReal.ofReal_eq_zero]; linarith
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcinv_toReal : c⁻¹.toReal = (rootMass W FlagType_2_1)⁻¹ := by
    rw [hcdef, ENNReal.toReal_inv, ENNReal.toReal_ofReal hmR.le]
  set ν : Measure (I × I) :=
    (volume : Measure (I × I)).withDensity
      (fun z => ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2)) with hνdef
  have hmeasφ : Measurable (rootedViewPoint W FlagType_2_1) :=
    measurable_rootedViewPoint W FlagType_2_1
  have haemeasφ : AEMeasurable (rootedViewPoint W FlagType_2_1) ν := hmeasφ.aemeasurable
  have hρmeas : Measurable (fun z : I × I => ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2)) :=
    (measurable_rootWeight W FlagType_2_1).ennreal_ofReal
  have hcont : Continuous (fun χ : PositiveHomSpace FlagType_2_1 =>
      ((PositiveHomSpace.toPosHom χ) l₂) ^ 2) := (continuous_eval l₂).pow 2
  have haesm : AEStronglyMeasurable
      (fun χ : PositiveHomSpace FlagType_2_1 => ((PositiveHomSpace.toPosHom χ) l₂) ^ 2)
      (Measure.map (rootedViewPoint W FlagType_2_1) ν) :=
    hcont.aestronglyMeasurable
  have hRM : W.RtauMinus = ∫ z : I × I, W.W z.1 z.2 * (W.deg z.1 - W.deg z.2) ^ 2 := rfl
  have hpointwise : ∀ z : I × I,
      (ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2)).toReal
        • ((PositiveHomSpace.toPosHom (rootedViewPoint W FlagType_2_1 z)) l₂) ^ 2
      = W.W z.1 z.2 * (W.deg z.1 - W.deg z.2) ^ 2 := by
    intro z
    by_cases hadm : RootAdmissible W FlagType_2_1 z.1 z.2
    · have hrootW : rootWeight W FlagType_2_1 z.1 z.2 = W.W z.1 z.2 := by
        show adjWeight W (FlagType_2_1.Adj 0 1) z.1 z.2 = W.W z.1 z.2
        unfold adjWeight; rw [if_pos tau_adj01]
      have hval : (graphonRootedHom W FlagType_2_1 z.1 z.2 hadm) l₂
          = W.deg z.1 - W.deg z.2 := by
        rw [hl2def, PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_smul,
          one_mul, one_mul, graphonRootedHom_a_tau, graphonRootedHom_b_tau]
        ring
      rw [smul_eq_mul, rootedViewPoint_of_admissible W FlagType_2_1 z hadm,
        toPosHom_posHomPoint, hval, hrootW, ENNReal.toReal_ofReal (W.nonneg z.1 z.2)]
    · have hrootW0 : rootWeight W FlagType_2_1 z.1 z.2 = 0 :=
        le_antisymm (not_lt.mp hadm) (rootWeight_nonneg W FlagType_2_1 z.1 z.2)
      have hW0 : W.W z.1 z.2 = 0 := by
        have hh : rootWeight W FlagType_2_1 z.1 z.2 = W.W z.1 z.2 := by
          show adjWeight W (FlagType_2_1.Adj 0 1) z.1 z.2 = W.W z.1 z.2
          unfold adjWeight; rw [if_pos tau_adj01]
        rw [hh] at hrootW0; exact hrootW0
      rw [hrootW0, hW0]; simp
  have hLHS : ∫ χ, (PositiveHomSpace.toPosHom χ) (l₂ * l₂)
      ∂(rootedViewMeasure W FlagType_2_1) = (rootMass W FlagType_2_1)⁻¹ * W.RtauMinus := by
    show ∫ χ, (PositiveHomSpace.toPosHom χ) (l₂ * l₂)
        ∂((c⁻¹) • Measure.map (rootedViewPoint W FlagType_2_1) ν) = _
    have heqfun : (fun χ : PositiveHomSpace FlagType_2_1 =>
          (PositiveHomSpace.toPosHom χ) (l₂ * l₂))
        = fun χ => ((PositiveHomSpace.toPosHom χ) l₂) ^ 2 := by
      funext χ; rw [PositiveHom.map_mul, ← pow_two]
    rw [heqfun, integral_smul_measure, integral_map haemeasφ haesm, hνdef,
      integral_withDensity_eq_integral_toReal_smul hρmeas
        (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top)),
      funext hpointwise, ← hRM, smul_eq_mul, hcinv_toReal]
  rw [hLHS] at hspec0
  rw [← hf2eq] at hspec0
  rw [div_eq_inv_mul] at hspec0
  exact (mul_left_cancel₀ (inv_ne_zero hmRne) hspec0).symm

include hr hZykov in
/-- **The kernel-level third clause of Thm 112(i)**: `p₂(r) · R_τ⁻(W) ≤ Δ` for any graphon
whose `φ_W` is `K_{r+1}`-free-consistent (from the hom-level `parametricP4_sq_bounds`
through the `f₂` bridge). -/
theorem parametricP4_graphon_RtauMinus_le (W : Graphon)
    (hστ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0)
    (hQ : posHomPoint (graphonHom W) ∈ Qσ (krFreeForb0 r)) :
    p₂ r * W.RtauMinus
      ≤ 12 * (((r : ℝ) - 1) / r) ^ 3
        - (graphonHom W) CompleteGraphFreeP4.P4_density := by
  have h := (parametricP4_sq_bounds hr hZykov (graphonHom W) hQ).2.1
  rwa [graphonHom_f₂_eq_RtauMinus W hστ] at h

include hr hZykov in
/-- **Exact vanishing on the slice**: `R_τ⁻(W) = 0` when `φ_W` lies in the parametric slice
(where the deficit `Δ` is zero: slice membership pins the `P₄` density, so
`parametricP4_graphon_RtauMinus_le` squeezes against `RtauMinus_nonneg`; `p₂ r > 0`). -/
theorem parametricP4_graphon_RtauMinus_eq_zero (W : Graphon)
    (hστ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ parametricP4Slice r) :
    W.RtauMinus = 0 := by
  obtain ⟨hQ, hval⟩ := posHomPoint_mem_eqSlice.mp hmem
  have hle := parametricP4_graphon_RtauMinus_le hr hZykov W hστ hQ
  rw [hval] at hle
  have hp2 : 0 < p₂ r := p₂_pos r hr
  have hnonneg := W.RtauMinus_nonneg
  have hprod_nonneg : 0 ≤ p₂ r * W.RtauMinus := mul_nonneg hp2.le hnonneg
  have hprod_zero : p₂ r * W.RtauMinus = 0 := le_antisymm (by linarith) hprod_nonneg
  exact (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt hp2)

/-! ## The top-endpoint recovery (Cor 106) -/

include hr hZykov in
/-- **The kernel-level Cor 106** (`cor:top-endpoint-recovery`): for a graphon whose `φ_W`
lies in the parametric slice `Y_r`, the single scalar pin `edgeDensity = α_r⁺` — in place
of the Zykov equality case — identifies `W` a.e. with the balanced complete `r`-partite
graphon. -/
theorem parametricP4_graphon_top_endpoint_rigidity (W : Graphon)
    (hστ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0)
    (hση : (graphonHom W) ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ parametricP4Slice r)
    (hp : W.edgeDensity = Graphon.alphaPlus r) :
    ∃ P : I → Fin r, Measurable P
      ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / r))
      ∧ ∀ᵐ z : I × I, W.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 :=
  W.slice_rigidity r hr
    (parametricP4_graphon_Rtau_eq_zero hr hZykov W hστ hmem)
    (parametricP4_graphon_Reta_eq_zero hr hZykov W hση hmem) hp

include hr hZykov in
/-- **The paper-verbatim Cor 106, unconditionally**: every graphon representing a point of
the parametric slice with edge density `(r−1)/r` — both root types of positive mass — is
a.e. the balanced complete `r`-partite graphon.  The quantifier runs over representatives,
so no representation-existence input is needed (the pattern of
`k4free_p4_tripartite_of_represents`). -/
theorem parametricP4_top_endpoint_of_represents {W : Graphon} {φ₀ : PositiveHom ∅ₜ}
    (hW : ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F)
    (hστ : φ₀ ⟨FlagType_2_1⟩₀ > 0) (hση : φ₀ ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint φ₀ ∈ parametricP4Slice r)
    (hρ : φ₀.coe ⟨2, unlabelledEdgeFlag⟩ = ((r : ℝ) - 1) / r) :
    ∃ P : I → Fin r, Measurable P
      ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / r))
      ∧ ∀ᵐ z : I × I, W.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 := by
  have hpt := posHomPoint_eq_of_graphonProfileFun_eq hW
  have htypeτ : (graphonHom W) ⟨FlagType_2_1⟩₀ = φ₀ ⟨FlagType_2_1⟩₀ := by
    show (graphonHom W).coe _ = φ₀.coe _
    rw [graphonHom_coe]; exact hW _
  have htypeη : (graphonHom W) ⟨FlagType_2_0⟩₀ = φ₀ ⟨FlagType_2_0⟩₀ := by
    show (graphonHom W).coe _ = φ₀.coe _
    rw [graphonHom_coe]; exact hW _
  have hedge : W.edgeDensity = Graphon.alphaPlus r := by
    rw [← graphonHom_edge W]
    have h1 : (graphonHom W).coe (⟨2, unlabelledEdgeFlag⟩ : FinFlag ∅ₜ)
        = φ₀.coe ⟨2, unlabelledEdgeFlag⟩ := by
      rw [graphonHom_coe]; exact hW _
    rw [h1, hρ]
    rfl
  refine parametricP4_graphon_top_endpoint_rigidity hr hZykov W ?_ ?_ ?_ hedge
  · rw [htypeτ]; exact hστ
  · rw [htypeη]; exact hση
  · rw [hpt]; exact hmem

include hr hZykov in
/-- The existence form of Cor 106, conditional on the Lovász–Szegedy existence input
`hrep` (the sole representation-existence classical input this result needs). -/
theorem parametricP4_top_endpoint_of_rep_exists
    (hrep : ∀ φ₀ : PositiveHom ∅ₜ, ∃ W : Graphon,
        ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F)
    {φ₀ : PositiveHom ∅ₜ}
    (hστ : φ₀ ⟨FlagType_2_1⟩₀ > 0) (hση : φ₀ ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint φ₀ ∈ parametricP4Slice r)
    (hρ : φ₀.coe ⟨2, unlabelledEdgeFlag⟩ = ((r : ℝ) - 1) / r) :
    ∃ W : Graphon, (∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F)
      ∧ ∃ P : I → Fin r, Measurable P
          ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / r))
          ∧ ∀ᵐ z : I × I, W.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 := by
  obtain ⟨W, hW⟩ := hrep φ₀
  exact ⟨W, hW, parametricP4_top_endpoint_of_represents hr hZykov hW hστ hση hmem hρ⟩

end FlagAlgebras.MetaTheory
