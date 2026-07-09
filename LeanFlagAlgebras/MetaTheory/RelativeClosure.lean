import LeanFlagAlgebras.MetaTheory.RelativeSupport
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Closing the constraint set does not change the relative support (paper §11,
`lem:relative-closure`)

The two structural ingredients and the headline lemma:

* `extend_tendsto` — the random-extension assignment `φ ↦ ℙ[φ]` is weakly continuous
  where the type density is positive: if base limits `χs t → posHomPoint φ₀` and all type
  densities are positive, the extension measures converge weakly.  (Stone–Weierstrass:
  flag evaluations are dense in `C(X_σ)` by `exists_flag_near`; on flag evaluations the
  integral is the ratio `φ ⟦f⟧₀ / φ ⟦1⟧₀` by the extension spec, an evaluation-continuous
  function of the base point with positive denominator.)
* `support_subset_closure_iUnion_support` — supports are lower semicontinuous along weak
  convergence: `supp P₀ ⊆ closure (⋃ t, supp (P t))` (portmanteau on open balls).
* `relSσ_closure_eq` (`lem:relative-closure`) — `S_σ(closure Y) = S_σ(Y)`; closedness
  hypotheses on constraint sets can therefore be dropped throughout §11.
-/

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- Convergence of the flag-evaluation integrals: for a fixed `f : FlagAlgebra σ`, the
integral of the evaluation `χ ↦ χ f` against the random extensions of the base points
`χs t` converges to the corresponding integral against `ℙ[φ₀]`.  This is the
"flag evaluations first" step of `extend_tendsto`: on flag evaluations the integral is
the ratio `φ ⟦f⟧₀ / φ ⟦1⟧₀` (extension spec), an evaluation-continuous function of the
base point with positive limit denominator. -/
private lemma tendsto_integral_eval {χs : ℕ → PositiveHomSpace ∅ₜ} {φ₀ : PositiveHom ∅ₜ}
    (hconv : Tendsto χs atTop (𝓝 (posHomPoint φ₀)))
    (hpos : ∀ t, (PositiveHomSpace.toPosHom (χs t)) ⟨σ⟩₀ > 0) (hσ : φ₀ ⟨σ⟩₀ > 0)
    (f : FlagAlgebra σ) :
    Tendsto
      (fun t => ∫ χ : PositiveHomSpace σ, (PositiveHomSpace.toPosHom χ) f
        ∂(probMeasure_extend_emptyType_positiveHom
            (PositiveHomSpace.toPosHom (χs t)) (hpos t) : Measure (PositiveHomSpace σ)))
      atTop
      (𝓝 (∫ χ : PositiveHomSpace σ, (PositiveHomSpace.toPosHom χ) f
        ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)))) := by
  -- numerator: `t ↦ (toPosHom (χs t)) ⟦f⟧₀` converges to `φ₀ ⟦f⟧₀`
  have hnum : Tendsto
      (fun t => (PositiveHomSpace.toPosHom (χs t)) (⟦f⟧₀ : FlagAlgebra ∅ₜ)) atTop
      (𝓝 (φ₀ (⟦f⟧₀ : FlagAlgebra ∅ₜ))) := by
    have h := ((continuous_eval (⟦f⟧₀ : FlagAlgebra ∅ₜ)).tendsto (posHomPoint φ₀)).comp hconv
    simp only [Function.comp_def, toPosHom_posHomPoint] at h
    exact h
  -- denominator: `t ↦ (toPosHom (χs t)) ⟦1⟧₀` converges to `φ₀ ⟦1⟧₀`
  have hden : Tendsto
      (fun t => (PositiveHomSpace.toPosHom (χs t)) (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ))
      atTop (𝓝 (φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ))) := by
    have h := ((continuous_eval (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ)).tendsto
      (posHomPoint φ₀)).comp hconv
    simp only [Function.comp_def, toPosHom_posHomPoint] at h
    exact h
  have h1pos : (0 : ℝ) < φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) :=
    positiveHom_one_downward_pos hσ
  -- rewrite both sides through the extension spec and conclude with `Tendsto.div`
  have heq : (fun t => ∫ χ : PositiveHomSpace σ, (PositiveHomSpace.toPosHom χ) f
        ∂(probMeasure_extend_emptyType_positiveHom
            (PositiveHomSpace.toPosHom (χs t)) (hpos t) : Measure (PositiveHomSpace σ)))
      = fun t => (PositiveHomSpace.toPosHom (χs t)) (⟦f⟧₀ : FlagAlgebra ∅ₜ)
          / (PositiveHomSpace.toPosHom (χs t)) (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) :=
    funext fun t => probMeasure_extend_emptyType_positiveHom_spec (hpos t) f
  rw [heq, probMeasure_extend_emptyType_positiveHom_spec hσ f]
  exact hnum.div hden (ne_of_gt h1pos)

/-- If a flag evaluation `χ ↦ χ f` is uniformly within `ε` of a bounded continuous `g`,
then their integrals against any probability measure are within `ε` of each other. -/
private lemma dist_integral_eval_le {f : FlagAlgebra σ} {g : PositiveHomSpace σ →ᵇ ℝ} {ε : ℝ}
    (hf : ∀ χ : PositiveHomSpace σ, |(PositiveHomSpace.toPosHom χ) f - g χ| < ε)
    (Q : ProbabilityMeasure (PositiveHomSpace σ)) :
    dist
      (∫ χ : PositiveHomSpace σ, (PositiveHomSpace.toPosHom χ) f
        ∂(Q : Measure (PositiveHomSpace σ)))
      (∫ χ : PositiveHomSpace σ, g χ ∂(Q : Measure (PositiveHomSpace σ))) ≤ ε := by
  have hint_f : Integrable (fun χ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom χ) f)
      (Q : Measure (PositiveHomSpace σ)) :=
    BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact (evalContinuousMap f))
  have hint_g : Integrable (fun χ : PositiveHomSpace σ => g χ)
      (Q : Measure (PositiveHomSpace σ)) :=
    BoundedContinuousFunction.integrable _ g
  rw [Real.dist_eq, ← integral_sub hint_f hint_g]
  have hae : ∀ᵐ χ ∂(Q : Measure (PositiveHomSpace σ)),
      ‖(PositiveHomSpace.toPosHom χ) f - g χ‖ ≤ ε :=
    Eventually.of_forall fun χ => by rw [Real.norm_eq_abs]; exact le_of_lt (hf χ)
  have h := norm_integral_le_of_norm_le_const hae
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

/-- ε/3 triangle-inequality bookkeeping in a metric space of reals. -/
private lemma dist_lt_of_three {a b c d ε : ℝ}
    (h1 : dist a b ≤ ε / 3) (h2 : dist a c < ε / 3) (h3 : dist c d ≤ ε / 3) :
    dist b d < ε := by
  have t1 := dist_triangle b a d
  have t2 := dist_triangle a c d
  have e1 := dist_comm b a
  linarith

/-- **Weak continuity of the random extension** on the positive-type-density region: if
base limits `χs t` converge to `posHomPoint φ₀` in `X₀` and every type density is
positive (including the limit's), then the random extensions converge weakly. -/
theorem extend_tendsto {χs : ℕ → PositiveHomSpace ∅ₜ} {φ₀ : PositiveHom ∅ₜ}
    (hconv : Tendsto χs atTop (𝓝 (posHomPoint φ₀)))
    (hpos : ∀ t, (PositiveHomSpace.toPosHom (χs t)) ⟨σ⟩₀ > 0) (hσ : φ₀ ⟨σ⟩₀ > 0) :
    Tendsto
      (fun t => probMeasure_extend_emptyType_positiveHom
        (σ := σ) (PositiveHomSpace.toPosHom (χs t)) (hpos t))
      atTop (𝓝 (ℙ[φ₀])) := by
  -- Route (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` + ε/3):
  -- 1. Reduce to: for every `g : PositiveHomSpace σ →ᵇ ℝ`,
  --    `∫ g ∂P_t → ∫ g ∂P₀`  (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`).
  -- 2. FLAG EVALUATIONS FIRST: for a fixed `f : FlagAlgebra σ`, the spec
  --    `probMeasure_extend_emptyType_positiveHom_spec` gives
  --    `∫ χ, χ f ∂P_t = (toPosHom (χs t)) ⟦f⟧₀ / (toPosHom (χs t)) ⟦1⟧₀`.
  --    Both numerator and denominator are continuous in the base point
  --    (`continuous_eval` at type `∅ₜ`, composed with `hconv`), the denominator limit
  --    `φ₀ ⟦1⟧₀` is positive (`positiveHom_one_downward_pos hσ`), and
  --    `toPosHom (posHomPoint φ₀) = φ₀` (`toPosHom_posHomPoint`); `Tendsto.div` closes.
  -- 3. ε/3 UPGRADE: given `g` and `ε > 0`, `exists_flag_near g.continuous` (with `ε/3`)
  --    provides `f` with `∀ χ, |χ f - g χ| < ε/3`; for ANY probability measure `Q`,
  --    `|∫ g ∂Q - ∫ χ f ∂Q| ≤ ε/3` (`norm_integral_le_of_norm_le_const` on the
  --    difference, integrability from `BoundedContinuousFunction.integrable` /
  --    `mkOfCompact (evalContinuousMap f)`).  Combine with step 2 through
  --    `Metric.tendsto_atTop` (real distance = abs) and the triangle inequality.
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun g => ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨f, hf⟩ := exists_flag_near (fun χ => g χ) g.continuous hε3
  have hf' : ∀ χ : PositiveHomSpace σ,
      |(PositiveHomSpace.toPosHom χ) f - g χ| < ε / 3 := hf
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (tendsto_integral_eval hconv hpos hσ f) (ε / 3) hε3
  refine ⟨N, fun t ht => ?_⟩
  show dist
      (∫ χ : PositiveHomSpace σ, g χ
        ∂(probMeasure_extend_emptyType_positiveHom
            (PositiveHomSpace.toPosHom (χs t)) (hpos t) : Measure (PositiveHomSpace σ)))
      (∫ χ : PositiveHomSpace σ, g χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ))) < ε
  exact dist_lt_of_three
    (dist_integral_eval_le hf'
      (probMeasure_extend_emptyType_positiveHom (PositiveHomSpace.toPosHom (χs t)) (hpos t)))
    (hN t ht)
    (dist_integral_eval_le hf' (ℙ[φ₀]))

/-- **Supports are lower semicontinuous along weak convergence**: if probability measures
`P t` converge weakly to `P₀` on the compact metric space `X_σ`, every point of
`supp P₀` is a limit of points of the supports `supp (P t)`. -/
theorem support_subset_closure_iUnion_support
    {P : ℕ → ProbabilityMeasure (PositiveHomSpace σ)}
    {P₀ : ProbabilityMeasure (PositiveHomSpace σ)}
    (h : Tendsto P atTop (𝓝 P₀)) :
    (P₀ : Measure (PositiveHomSpace σ)).support
      ⊆ closure (⋃ t, (P t : Measure (PositiveHomSpace σ)).support) := by
  -- Route (portmanteau on balls):
  -- Fix `χ ∈ supp P₀` and `ε > 0`; by `Metric.mem_closure_iff` it suffices to find a
  -- point of some `supp (P t)` within `ε` of `χ`.  `U := Metric.ball χ ε` is open and
  -- contains `χ`, so `0 < P₀ U` (membership in `Measure.support`; see
  -- `Mathlib/MeasureTheory/Measure/Support.lean` for the API, e.g. the neighbourhood
  -- characterisation of `Measure.support` — `μ.support` is defined via
  -- `∃ᶠ u in (𝓝 x).smallSets, 0 < μ u`, and open-set positivity lemmas live there).
  -- Portmanteau (`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, applied to the
  -- open `U`) gives `P₀ U ≤ liminf (fun t => P t U)`, so some `t` has `0 < P t U`.
  -- Since `P t (supp (P t))ᶜ = 0` (`Measure.measure_compl_support`; the space is compact
  -- metric, hence hereditarily Lindelöf), `U` must meet `supp (P t)`
  -- (else `U ⊆ (supp)ᶜ` would force `P t U = 0`).  That intersection point witnesses
  -- `Metric.mem_closure_iff`.  Mind ℝ≥0∞ / ℝ≥0 coercions in the portmanteau statement.
  intro χ hχ
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hUopen : IsOpen (Metric.ball χ ε) := Metric.isOpen_ball
  have hpos₀ : 0 < (P₀ : Measure (PositiveHomSpace σ)) (Metric.ball χ ε) :=
    (Measure.mem_support_iff_forall χ).mp hχ _ (hUopen.mem_nhds (Metric.mem_ball_self hε))
  have hliminf := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hUopen
  have hfreq : ∀ᶠ t in atTop,
      0 < (P t : Measure (PositiveHomSpace σ)) (Metric.ball χ ε) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hpos₀ hliminf)
  obtain ⟨t, ht⟩ := hfreq.exists
  obtain ⟨y, hyU, hySupp⟩ := Measure.nonempty_inter_support_of_pos ht
  exact ⟨y, Set.mem_iUnion.mpr ⟨t, hySupp⟩, by rw [dist_comm]; exact Metric.mem_ball.mp hyU⟩

/-- **Closing the constraint set does not change the support**
(`lem:relative-closure`): `S_σ(closure Y) = S_σ(Y)`. -/
theorem relSσ_closure_eq (Y : Set (PositiveHomSpace ∅ₜ)) (σ : FlagType (Fin n₀)) :
    relSσ (closure Y) σ = relSσ Y σ := by
  -- `⊇` is `relSσ_mono subset_closure`.  For `⊆`, by `closure_minimal` (+
  -- `relSσ_isClosed`) it suffices to show each generating support
  -- `supp ℙ[φ₀]`, `posHomPoint φ₀ ∈ closure Y`, `hσ : φ₀ ⟨σ⟩₀ > 0`, is inside
  -- `relSσ Y σ`:
  -- * `mem_closure_iff_seq_limit` gives `χs : ℕ → PositiveHomSpace ∅ₜ` with
  --   `χs t ∈ Y` and `χs t → posHomPoint φ₀`.
  -- * Evaluation at `⟨σ⟩₀` is continuous (`continuous_eval`), and
  --   `toPosHom (posHomPoint φ₀) ⟨σ⟩₀ = φ₀ ⟨σ⟩₀ > 0` (`toPosHom_posHomPoint`), so
  --   EVENTUALLY `toPosHom (χs t) ⟨σ⟩₀ > 0`; shift the sequence by that threshold `N`
  --   (`fun t => χs (t + N)`, `Filter.tendsto_add_atTop_iff_nat` keeps convergence,
  --   membership in `Y` is preserved) to assume positivity for ALL `t`.
  -- * `extend_tendsto` + `support_subset_closure_iUnion_support` give
  --   `supp ℙ[φ₀] ⊆ closure (⋃ t, supp P_t)`; each `supp P_t ⊆ relSσ Y σ` by
  --   `support_subset_relSσ` (with `posHomPoint (toPosHom (χs (t+N))) = χs (t+N) ∈ Y`
  --   via `posHomPoint_toPosHom`), so the closure is inside the closed `relSσ Y σ`
  --   (`closure_minimal` + `relSσ_isClosed`).
  refine Set.Subset.antisymm ?_ (relSσ_mono subset_closure σ)
  refine closure_minimal ?_ (relSσ_isClosed Y σ)
  refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
  -- approximate the base limit from inside `Y`
  obtain ⟨χs, hχsY, hχs_conv⟩ := mem_closure_iff_seq_limit.mp hφ₀
  -- eventual positivity of the type density along the sequence
  have hev : ∀ᶠ t in atTop, 0 < (PositiveHomSpace.toPosHom (χs t)) ⟨σ⟩₀ := by
    have h := ((continuous_eval (⟨σ⟩₀ : FlagAlgebra ∅ₜ)).tendsto (posHomPoint φ₀)).comp hχs_conv
    simp only [Function.comp_def, toPosHom_posHomPoint] at h
    exact h.eventually (eventually_gt_nhds hσ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- shift by the threshold `N` to get positivity everywhere
  have hconv' : Tendsto (fun t => χs (t + N)) atTop (𝓝 (posHomPoint φ₀)) :=
    (tendsto_add_atTop_iff_nat N).mpr hχs_conv
  have hpos' : ∀ t, (PositiveHomSpace.toPosHom (χs (t + N))) ⟨σ⟩₀ > 0 :=
    fun t => hN (t + N) (Nat.le_add_left N t)
  -- weak convergence of the extensions, then lower semicontinuity of supports
  have htend := extend_tendsto hconv' hpos' hσ
  refine (support_subset_closure_iUnion_support htend).trans
    (closure_minimal (Set.iUnion_subset fun t => ?_) (relSσ_isClosed Y σ))
  have hmem : posHomPoint (PositiveHomSpace.toPosHom (χs (t + N))) ∈ Y := by
    rw [posHomPoint_toPosHom]
    exact hχsY (t + N)
  exact support_subset_relSσ hmem (hpos' t)

end FlagAlgebras.MetaTheory
