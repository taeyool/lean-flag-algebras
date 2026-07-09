import LeanFlagAlgebras.MetaTheory.RelativeSupport

/-! # Relative complementary slackness (paper §11.3, `thm:relative-slackness`)

The general workhorse of paper §11: a certificate

  `φ₀ h + ∑ i, λᵢ · φ₀ ⟦fᵢ⟧₀ + φ₀ n ≤ c    (φ₀ ∈ Y)`

with each `fᵢ` non-negative on the relative support `S_{σᵢ}(Y)` and `n` non-negative on
`Y` yields, at every `φ₀ ∈ Y`:

* `relative_slackness_soundness` — soundness `φ₀ h ≤ c`;
* `relative_slackness_approx` / `_term` / `_slack` — approximate slackness: writing
  `Δ = c - φ₀ h`, `∑ᵢ λᵢ·φ₀ ⟦fᵢ⟧₀ + φ₀ n ≤ Δ`, hence `φ₀ ⟦fᵢ⟧₀ ≤ Δ/λᵢ`, `φ₀ n ≤ Δ`;
* `relative_slackness_exact_slack` / `_exact_term` / `_exact_ae` — exact slackness on the
  equality slice `φ₀ h = c`: every term vanishes, and `ψ(fᵢ) = 0` for
  `ℙ[φ₀]`-almost-every `ψ`;
* `relative_slackness_global` — global vanishing: if every `φ₀ ∈ Y` attains the bound,
  `fᵢ = 0` identically on `S_{σᵢ}(Y)`.

Plus the quantitative bridge (paper `lem:relative-cauchy-schwarz`,
`cor:sos-first-moments`) and the compactness stability upgrade
(`prop:unique-slice-stability`):

* `downward_sq_eval_nonneg`, `downward_cauchy_schwarz` — Razborov's Cauchy–Schwarz
  `(φ₀ ⟦l·g⟧₀)² ≤ φ₀ ⟦l²⟧₀ · φ₀ ⟦g²⟧₀`, re-proved through the extension measure;
* `certificate_first_moment_sq_bound` (+ `_one`) — certificates control first moments at
  rate `√Δ`, stated in the square-free form `(φ₀ ⟦l·g⟧₀)² ≤ (Δ/λᵢ) · φ₀ ⟦g²⟧₀` (the
  paper's `√` form is equivalent; squares avoid `Real.sqrt` plumbing);
* `unique_slice_stability` — a slice consisting of a single limit upgrades to a
  qualitative stability statement by compactness alone (stated for an ARBITRARY index
  family of density equations — the paper's countability hypothesis is unnecessary).

The certificate is indexed by `i : Fin m` with per-index label counts `k i`, types
`σs i : FlagType (Fin (k i))` and labelled elements `fs i : FlagAlgebra (σs i)` — the
paper's finitely many `(σᵢ, λᵢ, fᵢ)`.
-/

open MeasureTheory Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ}

/-! ## The slackness theorem -/

section Slackness

variable {Y : Set (PositiveHomSpace ∅ₜ)}
  {m : ℕ} {k : Fin m → ℕ} {σs : ∀ i, FlagType (Fin (k i))}
  {fs : ∀ i, FlagAlgebra (σs i)} {lam : Fin m → ℝ}
  {h n : FlagAlgebra ∅ₜ} {c : ℝ}

/-- **Soundness** (`thm:relative-slackness` (1)): dropping the non-negative certificate
terms leaves `φ₀ h ≤ c`. -/
theorem relative_slackness_soundness
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) :
    φ₀ h ≤ c := by
  -- Each `φ₀ ⟦fs i⟧₀ ≥ 0` by `relative_soundness` (RelativeSupport) with `hf i`; the sum
  -- is non-negative (`Finset.sum_nonneg`, `mul_nonneg (hlam i).le`); add `hn`, then
  -- `linarith` against `hcert φ₀ hφ₀`.
  have hsum : 0 ≤ ∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hlam i).le (relative_soundness (hf i) hφ₀)
  have hn' := hn φ₀ hφ₀
  linarith [hcert φ₀ hφ₀]

/-- **Approximate slackness, aggregate form** (`thm:relative-slackness` (2)): the whole
certificate correction is bounded by the slack `Δ = c - φ₀ h`. -/
theorem relative_slackness_approx
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) :
    (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c - φ₀ h := by
  -- Pure rearrangement of `hcert φ₀ hφ₀` (`linarith`).
  linarith [hcert φ₀ hφ₀]

/-- **Approximate slackness, per-term form** (`thm:relative-slackness` (2)):
`φ₀ ⟦fᵢ⟧₀ ≤ Δ/λᵢ` for each `i`. -/
theorem relative_slackness_term
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (i : Fin m) :
    φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ) ≤ (c - φ₀ h) / lam i := by
  -- Drop all other (non-negative) summands from `relative_slackness_approx`
  -- (`Finset.single_le_sum` on `j ↦ lam j * φ₀ ⟦fs j⟧₀`, then `le_div_iff₀ (hlam i)`).
  have happrox := relative_slackness_approx hcert hφ₀
  have hn' := hn φ₀ hφ₀
  have hsingle : lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)
      ≤ ∑ j, lam j * φ₀ (⟦fs j⟧₀ : FlagAlgebra ∅ₜ) :=
    Finset.single_le_sum
      (fun j _ => mul_nonneg (hlam j).le (relative_soundness (hf j) hφ₀))
      (Finset.mem_univ i)
  rw [le_div_iff₀ (hlam i)]
  linarith

/-- **Approximate slackness, slack-term form** (`thm:relative-slackness` (2)):
`φ₀ n ≤ Δ`. -/
theorem relative_slackness_slack
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) :
    φ₀ n ≤ c - φ₀ h := by
  -- Drop the (non-negative) certificate sum from `relative_slackness_approx`.
  have happrox := relative_slackness_approx hcert hφ₀
  have hsum : 0 ≤ ∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hlam i).le (relative_soundness (hf i) hφ₀)
  linarith

/-- **Exact slackness, slack term** (`thm:relative-slackness` (3)): on the equality slice
the unlabelled slack term vanishes. -/
theorem relative_slackness_exact_slack
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hattain : φ₀ h = c) :
    φ₀ n = 0 := by
  -- `relative_slackness_slack` gives `φ₀ n ≤ 0`; `hn` gives `≥ 0`.
  have hle := relative_slackness_slack hlam hf hcert hφ₀
  rw [hattain, sub_self] at hle
  exact le_antisymm hle (hn φ₀ hφ₀)

/-- **Exact slackness, certificate terms** (`thm:relative-slackness` (3)): on the
equality slice every averaged certificate term vanishes. -/
theorem relative_slackness_exact_term
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hattain : φ₀ h = c) (i : Fin m) :
    φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ) = 0 := by
  -- `relative_slackness_term` with `Δ = 0` (`hattain`) gives `≤ 0`;
  -- `relative_soundness` (with `hf i`) gives `≥ 0`.
  have hle := relative_slackness_term hlam hf hn hcert hφ₀ i
  rw [hattain, sub_self, zero_div] at hle
  exact le_antisymm hle (relative_soundness (hf i) hφ₀)

/-- **Exact slackness, almost-sure form** (`thm:relative-slackness` (3)): on the equality
slice, if the type density is positive, then `ψ (fᵢ) = 0` for almost every random
extension `ψ ∼ ℙ[φ₀]`. -/
theorem relative_slackness_exact_ae
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hattain : φ₀ h = c) (i : Fin m)
    (hσi : φ₀ ⟨σs i⟩₀ > 0) :
    ∀ᵐ ψ ∂(ℙ[φ₀] : Measure (PositiveHomSpace (σs i))),
      (PositiveHomSpace.toPosHom ψ) (fs i) = 0 := by
  -- `ψ (fs i)` is a.e. non-negative (`Measure.support_mem_ae` + `support_subset_relSσ`
  -- + `hf i`) with zero mean: by `probMeasure_extend_emptyType_positiveHom_spec` and
  -- `relative_slackness_exact_term`, `∫ ψ, ψ (fs i) ∂ℙ[φ₀] = 0 / φ₀ ⟦1⟧₀ = 0`.
  -- A non-negative integrable (`BoundedContinuousFunction.integrable` via
  -- `mkOfCompact (evalContinuousMap _)`) function with zero integral vanishes a.e.
  -- (`integral_eq_zero_iff_of_nonneg_ae`); compare `forbidden_ae_zero` (SupportClosure).
  set gfun : PositiveHomSpace (σs i) → ℝ :=
    fun χ => (PositiveHomSpace.toPosHom χ) (fs i) with hgdef
  have hnonneg : ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace (σs i))), 0 ≤ gfun χ := by
    filter_upwards [Measure.support_mem_ae] with χ hχ
    exact hf i χ (support_subset_relSσ hφ₀ hσi hχ)
  have hint : Integrable gfun (ℙ[φ₀] : Measure (PositiveHomSpace (σs i))) :=
    BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact (evalContinuousMap (fs i)))
  have hzero : ∫ χ, gfun χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace (σs i))) = 0 := by
    simp only [hgdef]
    rw [probMeasure_extend_emptyType_positiveHom_spec hσi (fs i),
      relative_slackness_exact_term hlam hf hn hcert hφ₀ hattain i, zero_div]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hae] with χ hχ
  exact hχ

/-- A continuous function that is a.e. non-negative under a probability measure is
non-negative on every point of the support (one direction of
`ae_nonneg_iff_nonneg_on_support`, with the a.e. hypothesis phrased as an `∀ᵐ`). -/
private lemma nonneg_on_support_of_ae_nonneg {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [HereditarilyLindelofSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Continuous g)
    (hae : ∀ᵐ x ∂μ, 0 ≤ g x) : ∀ x ∈ μ.support, 0 ≤ g x := by
  refine (ae_nonneg_iff_nonneg_on_support μ hg).mp ?_
  rw [← prob_compl_eq_zero_iff (isClosed_le continuous_const hg).measurableSet,
    Set.compl_setOf]
  exact ae_iff.mp hae

/-- A continuous function that vanishes a.e. under a probability measure vanishes on
every point of the support (apply `nonneg_on_support_of_ae_nonneg` to `g` and `-g`). -/
private lemma eq_zero_on_support_of_ae_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [HereditarilyLindelofSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Continuous g)
    (hae : ∀ᵐ x ∂μ, g x = 0) : ∀ x ∈ μ.support, g x = 0 := by
  have hpos : ∀ x ∈ μ.support, 0 ≤ g x :=
    nonneg_on_support_of_ae_nonneg μ hg
      (by filter_upwards [hae] with x hx; exact hx.ge)
  have hneg : ∀ x ∈ μ.support, 0 ≤ -g x :=
    nonneg_on_support_of_ae_nonneg μ hg.neg
      (by filter_upwards [hae] with x hx; simp [hx])
  intro x hx
  have h1 := hpos x hx
  have h2 := hneg x hx
  linarith

/-- **Global vanishing** (`thm:relative-slackness` (4)): if every `φ₀ ∈ Y` attains
`φ₀ h = c`, then each certificate term vanishes identically on its relative support. -/
theorem relative_slackness_global
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    (hall : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → φ₀ h = c) (i : Fin m) :
    ∀ χ ∈ relSσ Y (σs i), (PositiveHomSpace.toPosHom χ) (fs i) = 0 := by
  -- The vanishing locus `{χ | χ (fs i) = 0}` is closed (`isClosed_eq (continuous_eval _)
  -- continuous_const`).  Every generating support lands in it: for `φ₀` with
  -- `posHomPoint φ₀ ∈ Y` and `φ₀ ⟨σs i⟩₀ > 0`, `relative_slackness_exact_ae` (via
  -- `hall`) gives `ψ (fs i) = 0` a.e.; apply `ae_nonneg_iff_nonneg_on_support`
  -- (MeasureSupport) to `fs i` AND `- fs i` (both continuous, both a.e. non-negative)
  -- to get vanishing ON the support.  Then `closure_minimal` extends to `relSσ`.
  have hcl : IsClosed {ψ : PositiveHomSpace (σs i) |
      (PositiveHomSpace.toPosHom ψ) (fs i) = 0} :=
    isClosed_eq (continuous_eval (fs i)) continuous_const
  have hsub : relSσ Y (σs i)
      ⊆ {ψ : PositiveHomSpace (σs i) | (PositiveHomSpace.toPosHom ψ) (fs i) = 0} := by
    unfold relSσ
    refine closure_minimal ?_ hcl
    refine Set.iUnion_subset fun φ₁ => Set.iUnion_subset fun hφ₁ =>
      Set.iUnion_subset fun hσ => fun ψ hψ => ?_
    exact eq_zero_on_support_of_ae_eq_zero _ (continuous_eval (fs i))
      (relative_slackness_exact_ae hlam hf hn hcert hφ₁ (hall φ₁ hφ₁) i hσ) ψ hψ
  exact fun χ hχ => hsub hχ

/-- **Exact slackness, square instance** (paper `rem:cs-shape`): for the standard
certificate term `fᵢ = l·l`, the almost-sure vanishing reads `ψ(l) = 0` almost surely
(evaluations are multiplicative, so `ψ(l·l) = ψ(l)² = 0` forces `ψ(l) = 0`). -/
theorem relative_slackness_exact_ae_sq
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hattain : φ₀ h = c) (i : Fin m)
    {l : FlagAlgebra (σs i)} (hfi : fs i = l * l) (hσi : φ₀ ⟨σs i⟩₀ > 0) :
    ∀ᵐ ψ ∂(ℙ[φ₀] : Measure (PositiveHomSpace (σs i))),
      (PositiveHomSpace.toPosHom ψ) l = 0 := by
  filter_upwards [relative_slackness_exact_ae hlam hf hn hcert hφ₀ hattain i hσi] with ψ hψ
  rw [hfi, PositiveHom.map_mul] at hψ
  exact mul_self_eq_zero.mp hψ

/-- **Global vanishing, square instance** (paper `rem:cs-shape`): for the standard
certificate term `fᵢ = l·l`, global vanishing reads `l = 0` identically on the relative
support `S_{σᵢ}(Y)`. -/
theorem relative_slackness_global_sq
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    (hall : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → φ₀ h = c) (i : Fin m)
    {l : FlagAlgebra (σs i)} (hfi : fs i = l * l) :
    ∀ χ ∈ relSσ Y (σs i), (PositiveHomSpace.toPosHom χ) l = 0 := by
  intro χ hχ
  have hvan := relative_slackness_global hlam hf hn hcert hall i χ hχ
  rw [hfi, PositiveHom.map_mul] at hvan
  exact mul_self_eq_zero.mp hvan

end Slackness

/-! ## Cauchy–Schwarz for unlabelled averages (`lem:relative-cauchy-schwarz`) -/

variable {σ : FlagType (Fin n₀)}

/-- The unlabelled average of a square is non-negative at every base limit. -/
theorem downward_sq_eval_nonneg (φ₀ : PositiveHom ∅ₜ) (f : FlagAlgebra σ) :
    0 ≤ φ₀ (⟦f * f⟧₀ : FlagAlgebra ∅ₜ) := by
  -- Degenerate type: `downward_eval_eq_zero_of_degenerate`.  Otherwise the spec writes
  -- `φ₀ ⟦f*f⟧₀ = φ₀ ⟦1⟧₀ · ∫ ψ, ψ (f*f)` with `ψ (f*f) = (ψ f)^2 ≥ 0`
  -- (`PositiveHom.map_mul`, `mul_self_nonneg`); `integral_nonneg` + `mul_nonneg` +
  -- `posHom_one_downward_nonneg` finish.  (Alternatively: `downward_preserve_semanticCone`.)
  -- We take the alternative route: `square_downward_nonneg` (RandomHom) already puts
  -- `⟦f·f⟧₀` in the semantic cone, and evaluating the cone membership at `φ₀` finishes.
  have hcone := square_downward_nonneg (σ := σ) f
  rw [ge_iff_le, le_def, sub_zero] at hcone
  exact hcone φ₀

/-- **Cauchy–Schwarz for unlabelled averages** (`lem:relative-cauchy-schwarz`; Razborov's
Cauchy–Schwarz, re-proved through the extension measure): for every base limit `φ₀` and
all `l, g ∈ A^σ`,

  `(φ₀ ⟦l·g⟧₀)² ≤ φ₀ ⟦l·l⟧₀ · φ₀ ⟦g·g⟧₀`. -/
theorem downward_cauchy_schwarz (φ₀ : PositiveHom ∅ₜ) (l g : FlagAlgebra σ) :
    (φ₀ (⟦l * g⟧₀ : FlagAlgebra ∅ₜ)) ^ 2
      ≤ φ₀ (⟦l * l⟧₀ : FlagAlgebra ∅ₜ) * φ₀ (⟦g * g⟧₀ : FlagAlgebra ∅ₜ) := by
  -- Discriminant route (no measure theory needed beyond `downward_sq_eval_nonneg`):
  -- for every `t : ℝ`, `0 ≤ φ₀ ⟦(l + t•g)·(l + t•g)⟧₀`.  Expand
  -- `(l + t•g)·(l + t•g) = l·l + (2*t)•(l·g) + (t*t)•(g·g)` (CommRing +
  -- `smul_mul_assoc`/`mul_smul_comm`/`mul_comm l g`), push through
  -- `downward_add`/`downward_smul` and `PositiveHom.map_add`/`map_smul` to get
  -- `0 ≤ A + B·t + C·t²` with `A = φ₀ ⟦l·l⟧₀`, `B = 2·φ₀ ⟦l·g⟧₀`, `C = φ₀ ⟦g·g⟧₀`.
  -- `discrim_le_zero` (Mathlib.Algebra.QuadraticDiscriminant) yields `B² - 4AC ≤ 0`,
  -- i.e. the claim (`nlinarith`/`linarith` for the final algebra).
  -- Even shorter: `square_downward_mul_ge_mul_downward_square` (RandomHom, itself proved
  -- through the extension measure) gives the inequality in the semantic cone; evaluate
  -- the cone membership at `φ₀` and split the products with `PositiveHom.map_mul`.
  have hcone := square_downward_mul_ge_mul_downward_square l g
  rw [ge_iff_le, le_def] at hcone
  have hφ := hcone φ₀
  rw [PositiveHom.map_sub, PositiveHom.map_mul, PositiveHom.map_mul] at hφ
  rw [pow_two]
  linarith

/-! ## Certificates control first moments at rate `√Δ` (`cor:sos-first-moments`) -/

section FirstMoments

variable {Y : Set (PositiveHomSpace ∅ₜ)}
  {m : ℕ} {k : Fin m → ℕ} {σs : ∀ i, FlagType (Fin (k i))}
  {fs : ∀ i, FlagAlgebra (σs i)} {lam : Fin m → ℝ}
  {h n : FlagAlgebra ∅ₜ} {c : ℝ}

/-- **Certificates control first moments** (`cor:sos-first-moments`, square form): if the
`i`-th certificate term is the square `fᵢ = l·l`, then for every test element `g`,

  `(φ₀ ⟦l·g⟧₀)² ≤ (Δ/λᵢ) · φ₀ ⟦g·g⟧₀`,   `Δ = c - φ₀ h`.

(The paper's `√Δ` form follows by taking square roots; the squared form avoids
`Real.sqrt` and is what downstream stability arguments consume.) -/
theorem certificate_first_moment_sq_bound
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y)
    {i : Fin m} {l : FlagAlgebra (σs i)} (hfi : fs i = l * l)
    (g : FlagAlgebra (σs i)) :
    (φ₀ (⟦l * g⟧₀ : FlagAlgebra ∅ₜ)) ^ 2
      ≤ ((c - φ₀ h) / lam i) * φ₀ (⟦g * g⟧₀ : FlagAlgebra ∅ₜ) := by
  -- Chain `downward_cauchy_schwarz` with `relative_slackness_term` (rewritten by `hfi`),
  -- multiplying by `φ₀ ⟦g·g⟧₀ ≥ 0` (`downward_sq_eval_nonneg`, `mul_le_mul_of_nonneg_right`).
  have hterm := relative_slackness_term hlam hf hn hcert hφ₀ i
  rw [hfi] at hterm
  calc (φ₀ (⟦l * g⟧₀ : FlagAlgebra ∅ₜ)) ^ 2
      ≤ φ₀ (⟦l * l⟧₀ : FlagAlgebra ∅ₜ) * φ₀ (⟦g * g⟧₀ : FlagAlgebra ∅ₜ) :=
        downward_cauchy_schwarz φ₀ l g
    _ ≤ ((c - φ₀ h) / lam i) * φ₀ (⟦g * g⟧₀ : FlagAlgebra ∅ₜ) :=
        mul_le_mul_of_nonneg_right hterm (downward_sq_eval_nonneg φ₀ g)

/-- **First-moment bound, `g = 1` instance** (`cor:sos-first-moments`, final display):
`(φ₀ ⟦l⟧₀)² ≤ Δ/λᵢ`. -/
theorem certificate_first_moment_sq_bound_one
    (hlam : ∀ i, 0 < lam i)
    (hf : ∀ i, ∀ χ ∈ relSσ Y (σs i), 0 ≤ (PositiveHomSpace.toPosHom χ) (fs i))
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, lam i * φ₀ (⟦fs i⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y)
    {i : Fin m} {l : FlagAlgebra (σs i)} (hfi : fs i = l * l) :
    (φ₀ (⟦l⟧₀ : FlagAlgebra ∅ₜ)) ^ 2 ≤ (c - φ₀ h) / lam i := by
  -- `certificate_first_moment_sq_bound` with `g = 1`: `l * 1 = l` (`mul_one`),
  -- `φ₀ ⟦1·1⟧₀ = φ₀ ⟦1⟧₀ ∈ [0,1]` (`one_mul`, `posHom_one_downward_nonneg`/`_le_one`),
  -- and `0 ≤ Δ/λᵢ` from `relative_slackness_soundness` + `div_nonneg`.
  have hbound := certificate_first_moment_sq_bound hlam hf hn hcert hφ₀ hfi
    (1 : FlagAlgebra (σs i))
  rw [mul_one, mul_one] at hbound
  have hΔ : 0 ≤ (c - φ₀ h) / lam i :=
    div_nonneg
      (sub_nonneg.mpr (relative_slackness_soundness hlam hf hn hcert hφ₀))
      (hlam i).le
  calc (φ₀ (⟦l⟧₀ : FlagAlgebra ∅ₜ)) ^ 2
      ≤ ((c - φ₀ h) / lam i)
          * φ₀ (⟦(1 : FlagAlgebra (σs i))⟧₀ : FlagAlgebra ∅ₜ) := hbound
    _ ≤ ((c - φ₀ h) / lam i) * 1 :=
        mul_le_mul_of_nonneg_left (posHom_one_downward_le_one φ₀) hΔ
    _ = (c - φ₀ h) / lam i := mul_one _

end FirstMoments

/-! ## Unique slices give qualitative stability (`prop:unique-slice-stability`) -/

/-- **Unique slices give qualitative stability** (`prop:unique-slice-stability`): if the
slice of a closed set `Z ⊆ X₀` cut out by density equations `φ (hs j) = cs j` is the
single point `φ*`, then every sequence in `Z` whose densities converge to the `cs j`
converges to `φ*`.  (Stated for an arbitrary index family `J`; the paper's countability
assumption is unnecessary — only compactness of `X₀` is used.) -/
theorem unique_slice_stability {Z : Set (PositiveHomSpace ∅ₜ)} (hZ : IsClosed Z)
    {J : Type} (hs : J → FlagAlgebra ∅ₜ) (cs : J → ℝ) {φstar : PositiveHomSpace ∅ₜ}
    (huniq : {φ ∈ Z | ∀ j, (PositiveHomSpace.toPosHom φ) (hs j) = cs j} = {φstar})
    {seq : ℕ → PositiveHomSpace ∅ₜ} (hseq : ∀ t, seq t ∈ Z)
    (hconv : ∀ j, Tendsto (fun t => (PositiveHomSpace.toPosHom (seq t)) (hs j))
      atTop (𝓝 (cs j))) :
    Tendsto seq atTop (𝓝 φstar) := by
  -- `tendsto_of_subseq_tendsto` (atTop on ℕ is countably generated): every subsequence
  -- `seq ∘ ns` (with `Tendsto ns atTop atTop`) has, by compactness of
  -- `PositiveHomSpace ∅ₜ` (`CompactSpace.tendsto_subseq`), a convergent sub-subsequence
  -- with limit `φ`.  `φ ∈ Z` (`hZ.mem_of_tendsto`), and for each `j` continuity of the
  -- evaluation (`continuous_eval (hs j)`) plus uniqueness of limits along the
  -- sub-subsequence of `hconv j` gives `φ (hs j) = cs j`.  So `φ` lies in the slice,
  -- which is `{φstar}` (`huniq`), i.e. `φ = φstar`.
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φlim, ms, hms, hφ⟩ := CompactSpace.tendsto_subseq fun t => seq (ns t)
  have hmem : φlim ∈ Z :=
    hZ.mem_of_tendsto hφ (Eventually.of_forall fun t => hseq (ns (ms t)))
  have hslice : ∀ j, (PositiveHomSpace.toPosHom φlim) (hs j) = cs j := by
    intro j
    have hsubtend : Tendsto (fun t => ns (ms t)) atTop atTop :=
      hns.comp hms.tendsto_atTop
    have h1 : Tendsto (fun t => (PositiveHomSpace.toPosHom (seq (ns (ms t)))) (hs j))
        atTop (𝓝 (cs j)) := (hconv j).comp hsubtend
    have h2 : Tendsto (fun t => (PositiveHomSpace.toPosHom (seq (ns (ms t)))) (hs j))
        atTop (𝓝 ((PositiveHomSpace.toPosHom φlim) (hs j))) :=
      ((continuous_eval (hs j)).tendsto φlim).comp hφ
    exact tendsto_nhds_unique h2 h1
  have heqstar : φlim = φstar := by
    have hmem2 : φlim ∈ {φ ∈ Z | ∀ j, (PositiveHomSpace.toPosHom φ) (hs j) = cs j} :=
      ⟨hmem, hslice⟩
    rw [huniq] at hmem2
    exact hmem2
  exact ⟨ms, heqstar ▸ hφ⟩

end FlagAlgebras.MetaTheory
