import LeanFlagAlgebras.MetaTheory.RelativeSupport
import LeanFlagAlgebras.MetaTheory.ConstrainedRep
import LeanFlagAlgebras.MetaTheory.StarWitness
import LeanFlagAlgebras.MetaTheory.WeakConvergence
import LeanFlagAlgebras.MetaTheory.RootingUniform
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # The relative planted set and relative root-plantability (paper §11.4,
`def:relative-plantability`, `prop:relative-plantability`)

A point `χ ∈ X_σ` is a **`Y`-planted view** for a hereditary class `hc` if it is the density
limit of finite `σ`-flags whose underlying graphs are in the class and converge (as unlabelled
flags) to a base limit in `closure Y`.  `relQσ hc Y σ` collects the `Y`-planted views — the
views obtained by planting the roots *anywhere*, including at exceptional vertices — while
`relSσ Y σ` keeps only the views a random rooting sees.  `(Y, σ)` is **relatively
root-plantable** when the two agree.

Headlines (`prop:relative-plantability`):
* `relQσ_isClosed` — `Q_σ(Y)` is closed (diagonal argument);
* `relQσ_subset_Qσ` — planted views are constrained: `Q_σ(Y) ⊆ Q_σ`;
* `relSσ_subset_relQσ` — random rooting sees only planted views: `S_σ(Y) ⊆ Q_σ(Y)`
  (finite rooting distributions converge weakly to the extension measure);
* `relQσ_Q0_eq` — `Q_σ(Q₀) = Q_σ`, so relative root-plantability at `Y = Q₀` is
  root-plantability (`relativelyRootPlantable_Q0_iff`);
* `relQσ_nonneg_implies_relEnsemble`, `relative_planted_criterion` — part (ii): non-negativity
  on `Q_σ(Y)` implies relative ensemble semantics, and the two are equivalent for every `f`
  iff `(Y, σ)` is relatively root-plantable.
-/

open MeasureTheory Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## The definition -/

/-- The underlying unlabelled flag sequence of a `σ`-flag sequence. -/
noncomputable def unlabelSeq (Gs : FlagSeq σ) : FlagSeq ∅ₜ :=
  fun t => ⟨(Gs t).1, unlabel (Gs t).2⟩

/-- **The relative planted set** `Q_σ(Y)` (paper `def:relative-plantability`): the set of
`Y`-planted views — density limits of finite `σ`-flags whose underlying graphs lie in the
hereditary class and converge, as unlabelled flags, to a base limit in `closure Y`. -/
def relQσ (hc : HeredClass) (Y : Set (PositiveHomSpace ∅ₜ)) (σ : FlagType (Fin n₀)) :
    Set (PositiveHomSpace σ) :=
  {χ | ∃ (Gs : FlagSeq σ) (φ : PositiveHom ∅ₜ),
      ConvergesTo Gs (PositiveHomSpace.toPosHom χ).coe ∧
      (∀ t, hc.underlyingMem (unlabel (Gs t).2)) ∧
      ConvergesTo (unlabelSeq Gs) φ.coe ∧
      posHomPoint φ ∈ closure Y}

/-- **Relative root-plantability** (paper `def:relative-plantability`): the random-rooting
support exhausts the planted views. -/
def RelativelyRootPlantable (hc : HeredClass) (Y : Set (PositiveHomSpace ∅ₜ))
    (σ : FlagType (Fin n₀)) : Prop :=
  relSσ Y σ = relQσ hc Y σ

/-! ## Small bridges -/

/-- A forbidden `σ`-flag has density `0` in any flag whose underlying graph is in the class
(`FinFlag` form of `flagDensity_forbidden_eq_zero_of_mem`, lifted over the quotient via
`HeredClass.underlyingMem`). -/
lemma flagDensity_forbidden_eq_zero_of_underlyingMem (hc : HeredClass)
    (G : FinFlag σ) (hG : hc.underlyingMem (unlabel G.2))
    (F : FinFlag σ) (hF : (hc.constraintOf σ).forbσ F) :
    flagDensity₁ F.2 G.2 = 0 := by
  -- Induct on the quotient `G.2` (`Quotient.induction_on` / `Quotient.exists_rep`); on a
  -- representative `Grep : LabeledGraph σ (Fin G.1)`, `hG` becomes `hc.Mem Grep.graph` by
  -- `HeredClass.underlyingMem_unlabel_mk`, and `flagDensity_forbidden_eq_zero_of_mem`
  -- (StarWitness) closes.
  rcases Quotient.exists_rep G.2 with ⟨Grep, hGrep⟩
  rw [← hGrep] at hG ⊢
  rw [hc.underlyingMem_unlabel_mk] at hG
  exact flagDensity_forbidden_eq_zero_of_mem hc Grep hG F hF

/-- A limit of in-class unlabelled flags is a constrained limit: if `sH : FlagSeq ∅ₜ` has all
its flags in the class and converges to `φ.coe`, then `posHomPoint φ ∈ Q₀`.  (Public analogue
of the private `flagSeqLimit_mem_Q0` in `FinitePlanting`.) -/
lemma flagSeqLimit_mem_Q0_of_underlyingMem (hc : HeredClass)
    {sH : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ} (hconv : ConvergesTo sH φ.coe)
    (hmem : ∀ t, hc.underlyingMem (sH t).2) :
    posHomPoint φ ∈ Qσ (hc.constraintOf ∅ₜ).forb0 := by
  -- `mem_Qσ_iff`; for forbidden `D` (i.e. `¬ underlyingMem D.2`), the density of `D` in each
  -- `sH t` is `0`: positive density would embed `D`'s underlying graph into the in-class
  -- graph `sH t`, contradicting heredity — this is
  -- `flagDensity_forbidden_eq_zero_of_underlyingMem` at the empty type (note at `∅ₜ`,
  -- `(hc.constraintOf ∅ₜ).forb0 D = ¬ hc.underlyingMem D.2` and `unlabel` is the identity on
  -- empty-type flags — see `FlagOperators` for the identity lemma, or use
  -- `(hc.constraintOf ∅ₜ).forbσ`-vs-`forb0` defeq).  Then `χ.val D = lim 0 = 0` via
  -- `flagSeq_convergesTo_iff` and `tendsto_nhds_unique` against the constant sequence.
  rw [mem_Qσ_iff]
  intro D hD
  rw [posHomPoint_val_apply, ← φ.coe_flag D]
  have hzero : ∀ k, flagDensitySeq sH k D = 0 := by
    intro k
    show (flagDensity₁ D.2 (sH k).2 : ℝ) = 0
    have hG : hc.underlyingMem (unlabel (sH k).2) := by
      rw [unlabel_emptyType]; exact hmem k
    have hforb : (hc.constraintOf ∅ₜ).forbσ D := by
      show ¬ hc.underlyingMem (unlabel D.2)
      rw [unlabel_emptyType]
      exact hD
    rw [flagDensity_forbidden_eq_zero_of_underlyingMem hc (sH k) hG D hforb, Rat.cast_zero]
  have hlim : Tendsto (fun k => flagDensitySeq sH k D) atTop (𝓝 (φ.coe D)) :=
    (flagSeq_convergesTo_iff.mp hconv).2 D
  rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-! ## Structure of the planted set: `prop:relative-plantability` (i) -/

/-- Planted views are constrained: `Q_σ(Y) ⊆ Q_σ`. -/
theorem relQσ_subset_Qσ (hc : HeredClass) (Y : Set (PositiveHomSpace ∅ₜ)) :
    relQσ hc Y σ ⊆ Qσ (hc.constraintOf σ).forbσ := by
  -- `mem_Qσ_iff`: for forbidden `F`, `χ.val F` is the limit of the densities
  -- `flagDensity₁ F.2 (Gs t).2`, each `0` by
  -- `flagDensity_forbidden_eq_zero_of_underlyingMem`; `tendsto_nhds_unique` with the constant
  -- `0` sequence.  Mind the glue between `(PositiveHomSpace.toPosHom χ).coe F` and
  -- `χ.val F` (`PositiveHom.coe_flag` / `posHomPoint_val_apply` — see how
  -- `flagSeqLimit_mem_Q0` in `FinitePlanting` handles this at `∅ₜ`, and the ℝ-vs-ℚ cast of
  -- `flagDensity₁` in `flagDensitySeq`).
  rintro χ ⟨Gs, φ, hconv, hmem, -, -⟩
  rw [mem_Qσ_iff]
  intro F hF
  rw [← PositiveHomSpace.toPosHom_basisVector χ F, ← PositiveHom.coe_flag]
  have hzero : ∀ n, flagDensitySeq Gs n F = 0 := by
    intro n
    show (flagDensity₁ F.2 (Gs n).2 : ℝ) = 0
    rw [flagDensity_forbidden_eq_zero_of_underlyingMem hc (Gs n) (hmem n) F hF, Rat.cast_zero]
  have hlim : Tendsto (fun n => flagDensitySeq Gs n F) atTop
      (𝓝 ((PositiveHomSpace.toPosHom χ).coe F)) :=
    (flagSeq_convergesTo_iff.mp hconv).2 F
  rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-- Profile convergence in the metric space `FlagDensitySpace σ` is the raw pi-space
`Tendsto` bundled by `ConvergesTo` (private bridge over `tendsto_subtype_rng`). -/
private lemma tendsto_flagDensitySeq'_iff {s : FlagSeq σ} {a : FlagDensitySpace σ} :
    Tendsto (flagDensitySeq' s) atTop (𝓝 a) ↔
      Tendsto (flagDensitySeq s) atTop (𝓝 (a : FinFlag σ → ℝ)) :=
  tendsto_subtype_rng

/-- `ConvergesTo` is stable under composition with a strictly monotone index map
(generic-limit version of `convergesTo_comp_of_strictMono`). -/
private lemma convergesTo_comp {s : FlagSeq σ} {a : FinFlag σ → ℝ}
    {ϕ : ℕ → ℕ} (hϕ : StrictMono ϕ) (h : ConvergesTo s a) : ConvergesTo (s ∘ ϕ) a :=
  ⟨h.1.comp hϕ, h.2.comp hϕ.tendsto_atTop⟩

/-- `Q_σ(Y)` is a closed subset of `X_σ` (the diagonal argument). -/
theorem relQσ_isClosed (hc : HeredClass) (Y : Set (PositiveHomSpace ∅ₜ)) :
    IsClosed (relQσ hc Y σ) := by
  -- Sequential closedness in the compact metric `X_σ` (`IsSeqClosed.isClosed` /
  -- `isClosed_of_closure_subset` via `mem_closure_iff_seq_limit`).  Given `χk → χ` with
  -- witnesses `(Gs_k, φ_k)`:
  -- * choose `t_k` with (a) `dist` in `FlagDensitySpace σ` between the profile of
  --   `Gs_k t_k` and `χk`'s profile `< 1/(k+1)` (possible since the profile sequence tends to
  --   it — `Metric.tendsto_atTop`), (b) the unlabelled profile within `1/(k+1)` of
  --   `φ_k.coe`'s profile, and (c) the size `(Gs_k t_k).1` strictly larger than the size
  --   chosen at step `k-1` (sizes tend to `∞` by `Increases`; choose recursively —
  --   `Nat.rec` or `Filter.eventually_atTop` intersection of three eventually-conditions).
  -- * `posHomPoint φ_k ∈ closure Y`, a closed subset of the compact `PositiveHomSpace ∅ₜ`,
  --   hence sequentially compact: extract `φ_{k_j} → φ∞` with `posHomPoint φ∞ ∈ closure Y`.
  --   (Work with the points `posHomPoint φ_k`; recover `φ∞` via `PositiveHomSpace.toPosHom`
  --   and the roundtrips `toPosHom_posHomPoint`/`posHomPoint_toPosHom`.)
  -- * the diagonal sequence `j ↦ Gs_{k_j} t_{k_j}` then witnesses `χ ∈ relQσ`: profiles
  --   converge to `χ`'s profile (triangle inequality through `χ_{k_j}`), sizes strictly
  --   increase (`Increases` via the recursive choice), membership is inherited pointwise, and
  --   the unlabelled profiles converge to `φ∞.coe` (triangle through `φ_{k_j}`, using that
  --   convergence in `PositiveHomSpace ∅ₜ` is convergence of the `.val` profiles).
  -- Mind: `ConvergesTo` bundles `Increases` + `Tendsto` of `flagDensitySeq` — build both.
  have hseq : IsSeqClosed (relQσ hc Y σ) := by
    intro χs χ hmemQ hlim
    simp only [relQσ, Set.mem_setOf_eq] at hmemQ ⊢
    choose Gs φf h1 h2 h3 h4 using hmemQ
    -- val-level limit of the points
    have hlim' : Tendsto (fun k => (χs k).val) atTop (𝓝 χ.val) := tendsto_subtype_rng.mp hlim
    -- per-stage profile convergence, in the metric space `FlagDensitySpace`
    have hprof : ∀ k, Tendsto (flagDensitySeq' (Gs k)) atTop (𝓝 ((χs k).val)) := by
      intro k
      have hcoe : (PositiveHomSpace.toPosHom (χs k)).coe = (χs k).val :=
        Classical.choose_spec (χs k).property
      have h := (h1 k).2
      rw [hcoe] at h
      exact tendsto_flagDensitySeq'_iff.mpr h
    have hprof0 : ∀ k, Tendsto (flagDensitySeq' (unlabelSeq (Gs k))) atTop (𝓝 ((φf k).coe)) :=
      fun k => tendsto_flagDensitySeq'_iff.mpr (h3 k).2
    -- stage-`k` index selection: close to both targets, with size above any given floor
    have hsel : ∀ k m : ℕ, ∃ t : ℕ,
        dist (flagDensitySeq' (Gs k) t) ((χs k).val) < 1 / (k + 1) ∧
        dist (flagDensitySeq' (unlabelSeq (Gs k)) t) ((φf k).coe) < 1 / (k + 1) ∧
        m < ((Gs k) t).1 := by
      intro k m
      have hk : (0:ℝ) < 1 / (k + 1) := by positivity
      obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp (hprof k) _ hk
      obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp (hprof0 k) _ hk
      obtain ⟨N3, hN3⟩ := (h1 k).1.eventually_gt m
      refine ⟨max N1 (max N2 N3), hN1 _ (le_max_left _ _), hN2 _ ?_, hN3 _ ?_⟩
      · exact le_trans (le_max_left N2 N3) (le_max_right _ _)
      · exact le_trans (le_max_right N2 N3) (le_max_right _ _)
    choose sel hsel1 hsel2 hsel3 using hsel
    -- recursive diagonal indices, forcing strictly increasing sizes
    set T : ℕ → ℕ :=
      fun k => Nat.rec (motive := fun _ => ℕ) (sel 0 0)
        (fun k ih => sel (k + 1) ((Gs k ih).1)) k with hT
    have hd1 : ∀ k, dist (flagDensitySeq' (Gs k) (T k)) ((χs k).val) < 1 / (k + 1) := by
      intro k
      cases k with
      | zero => exact hsel1 0 0
      | succ k => exact hsel1 (k + 1) ((Gs k (T k)).1)
    have hd2 : ∀ k, dist (flagDensitySeq' (unlabelSeq (Gs k)) (T k)) ((φf k).coe)
        < 1 / (k + 1) := by
      intro k
      cases k with
      | zero => exact hsel2 0 0
      | succ k => exact hsel2 (k + 1) ((Gs k (T k)).1)
    have hsz : StrictMono (fun k => ((Gs k) (T k)).1) := by
      apply strictMono_nat_of_lt_succ
      intro k
      exact hsel3 (k + 1) ((Gs k (T k)).1)
    -- extract a convergent subsequence of the base points, staying in `closure Y`
    obtain ⟨ψlim, κ, hκmono, hκlim⟩ :=
      CompactSpace.tendsto_subseq (fun k => posHomPoint (φf k))
    have hψY : ψlim ∈ closure Y :=
      isClosed_closure.mem_of_tendsto hκlim (Eventually.of_forall fun j => h4 (κ j))
    have hφcoe : Tendsto (fun j => (φf (κ j)).coe) atTop
        (𝓝 ((PositiveHomSpace.toPosHom ψlim).coe)) := by
      have hval := tendsto_subtype_rng.mp hκlim
      have hcoe : (PositiveHomSpace.toPosHom ψlim).coe = ψlim.val :=
        Classical.choose_spec ψlim.property
      rw [hcoe]
      exact hval
    -- the diagonal sequence
    set Ds : FlagSeq σ := fun j => Gs (κ j) (T (κ j)) with hDs
    have hjκ : ∀ j : ℕ, (1:ℝ) / (κ j + 1) ≤ 1 / (j + 1) := by
      intro j
      apply one_div_le_one_div_of_le (by positivity)
      have hle : (j:ℝ) ≤ (κ j : ℝ) := by exact_mod_cast hκmono.id_le j
      linarith
    have hone : Tendsto (fun j : ℕ => 1 / ((j:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    -- profiles of the diagonal converge to `χ`
    have htend1 : Tendsto (flagDensitySeq' Ds) atTop (𝓝 χ.val) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hbound : ∀ j, dist (flagDensitySeq' Ds j) χ.val
          ≤ 1 / (j + 1) + dist ((χs (κ j)).val) χ.val := by
        intro j
        have htri : dist (flagDensitySeq' Ds j) χ.val
            ≤ dist (flagDensitySeq' Ds j) ((χs (κ j)).val) + dist ((χs (κ j)).val) χ.val :=
          dist_triangle _ _ _
        have h1' : dist (flagDensitySeq' Ds j) ((χs (κ j)).val) < 1 / ((κ j : ℝ) + 1) :=
          hd1 (κ j)
        have h2' := hjκ j
        linarith
      refine squeeze_zero (fun j => dist_nonneg) hbound ?_
      have hz2 : Tendsto (fun j => dist ((χs (κ j)).val) χ.val) atTop (𝓝 0) :=
        (tendsto_iff_dist_tendsto_zero.mp hlim').comp hκmono.tendsto_atTop
      simpa using hone.add hz2
    -- unlabelled profiles of the diagonal converge to `ψlim`
    have htend0 : Tendsto (flagDensitySeq' (unlabelSeq Ds)) atTop
        (𝓝 ((PositiveHomSpace.toPosHom ψlim).coe)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hbound : ∀ j, dist (flagDensitySeq' (unlabelSeq Ds) j)
            ((PositiveHomSpace.toPosHom ψlim).coe)
          ≤ 1 / (j + 1)
            + dist ((φf (κ j)).coe) ((PositiveHomSpace.toPosHom ψlim).coe) := by
        intro j
        have htri := dist_triangle (flagDensitySeq' (unlabelSeq Ds) j) ((φf (κ j)).coe)
          ((PositiveHomSpace.toPosHom ψlim).coe)
        have h1' : dist (flagDensitySeq' (unlabelSeq Ds) j) ((φf (κ j)).coe)
            < 1 / ((κ j : ℝ) + 1) := hd2 (κ j)
        have h2' := hjκ j
        linarith
      refine squeeze_zero (fun j => dist_nonneg) hbound ?_
      have hz2 : Tendsto
          (fun j => dist ((φf (κ j)).coe) ((PositiveHomSpace.toPosHom ψlim).coe))
          atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hφcoe
      simpa using hone.add hz2
    -- assemble the witness
    refine ⟨Ds, PositiveHomSpace.toPosHom ψlim, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
    · exact hsz.comp hκmono
    · have hcoe : (PositiveHomSpace.toPosHom χ).coe = χ.val :=
        Classical.choose_spec χ.property
      rw [hcoe]
      exact tendsto_flagDensitySeq'_iff.mp htend1
    · intro t
      exact h2 (κ t) (T (κ t))
    · exact hsz.comp hκmono
    · exact tendsto_flagDensitySeq'_iff.mp htend0
    · rw [posHomPoint_toPosHom]
      exact hψY
  exact hseq.isClosed

/-- Tail shift: `ConvergesTo` survives dropping the first `N` terms. -/
private lemma convergesTo_tail {s : FlagSeq σ} {a : FinFlag σ → ℝ}
    (h : ConvergesTo s a) (N : ℕ) : ConvergesTo (fun m => s (m + N)) a :=
  ⟨fun i j hij => h.1 (show i + N < j + N by omega),
    (tendsto_add_atTop_iff_nat N).mpr h.2⟩

/-- Positive rooting-measure mass on a set yields a label extension whose density profile
lies in the set (via the labelling-count ratio `toProbMeasure_apply_eq_dnf_ratio`). -/
private lemma exists_labelExtension_of_pos_measure (F : FinFlag ∅ₜ)
    (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0) (A : Set (FlagDensitySpace σ))
    (hpos : 0 < (F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A) :
    ∃ F' ∈ labelExtensions F.2 σ, funFromFlagWithSizeToFlagDensitySpace σ F.1 F' ∈ A := by
  classical
  by_contra hcon
  push_neg at hcon
  have hzero : ((F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A).toReal = 0 := by
    rw [toProbMeasure_apply_eq_dnf_ratio F hF A,
      Finset.filter_false_of_mem (fun F' hF' => hcon F' hF'), Finset.sum_empty, zero_div]
  have hne : ((F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _))
  exact hne hzero

/-- The support of an admissible random extension consists of `Y`-planted views (the heavy
step of `prop:relative-plantability` (i)): finite rooting distributions of an in-class
sequence converging to `φ₀` converge weakly to the extension measure, so every support point
is approximated by finite rooted views. -/
theorem support_subset_relQσ (hc : HeredClass) {Y : Set (PositiveHomSpace ∅ₜ)}
    (hY : Y ⊆ Qσ (hc.constraintOf ∅ₜ).forb0)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hσ : φ₀ ⟨σ⟩₀ > 0) :
    (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support ⊆ relQσ hc Y σ := by
  -- Route (the paper's proof, with the repo's rooting-measure machinery):
  -- 1. `hY hφ₀ : posHomPoint φ₀ ∈ Qσ forb0`; `exists_constrained_flagSeq_limit φ₀
  --    (hc.constraintOf ∅ₜ).forb0` (with `mem_Qσ_iff` supplying the vanishing hypothesis,
  --    mind `posHomPoint_val_apply`/`coe_flag` glue) gives `s : FlagSeq ∅ₜ` with
  --    `ConvergesTo s φ₀.coe` and every `s t` forbidden-density-free.
  -- 2. Each `s t` is IN CLASS: if `¬ hc.underlyingMem (s t).2` then `s t` is itself a
  --    forbidden flag with `flagDensity₁ (s t).2 (s t).2 = 1 ≠ 0` (`flagDensity_self`,
  --    SubflagListDensity) — contradiction.
  -- 3. Positivity tail: `flagDensity₁ σ.toEmptyTypeFlag (s n).2 → φ₀ ⟨σ⟩₀ > 0` (the
  --    density-profile coordinate at `⟨n₀, σ.toEmptyTypeFlag⟩`; mind ℚ→ℝ casts), so it is
  --    eventually positive; replace `s` by the tail `fun n => s (n + N)`
  --    (`ConvergesTo` and membership survive; see how `CloneClosed`/`FinitePlanting` obtain
  --    their positive-density sequences, or reuse a tail lemma if one exists).
  -- 4. `tendsto_rootingMeasure_extend hσ s' hs' hconv'` gives
  --    `P_n := s'.toProbMeasureSeq hs' ⇒ rootingMeasureFDS φ₀ hσ` on `FlagDensitySpace σ`.
  -- 5. Fix `ψ ∈ supp ℙ[φ₀]`.  Then `(ψ : FlagDensitySpace σ) ∈ supp (rootingMeasureFDS φ₀ hσ)`:
  --    `rootingMeasureFDS` is the pushforward along `Subtype.val`, so an open `U ∋ ψ.val` has
  --    `(map val ℙ) U = ℙ (val ⁻¹' U) > 0` (`Measure.map_apply`, `val⁻¹U` open ∋ ψ,
  --    membership-in-support characterisation from `Mathlib/MeasureTheory/Measure/Support.lean`).
  -- 6. For each `k`, `U_k := Metric.ball ψ.val (1/(k+1))` is open with positive limit
  --    measure; portmanteau (`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) makes
  --    `P_n U_k > 0` frequently; choose a STRICTLY INCREASING `n_k` with `P_{n_k} U_k > 0`
  --    (recursive choice from `∃ᶠ`).
  -- 7. Positive `P_{n_k}`-measure of `U_k` yields a labelled flag: use
  --    `toProbMeasure_apply_eq_labeling_ratio` (`RootingUniform`) — the measure of a set is a
  --    ratio of labelling counts, so a positive measure gives a labelling
  --    `F'_k ∈ labelExtensions (s' (n_k)) σ` whose density profile
  --    (`funFromFlagWithSizeToFlagDensitySpace`) lies in `U_k`.
  -- 8. The witness sequence `Gs k := ⟨(s' (n_k)).1, F'_k⟩ : FinFlag σ` (labelled flags of the
  --    in-class graphs): `unlabelSeq Gs = fun k => s' (n_k)` (labelExtensions means
  --    `unlabel F'_k = (s' (n_k)).2`), which `ConvergesTo φ₀.coe` (subsequence along the
  --    strictly monotone `n_k`); membership transfers; profiles tend to `ψ.val` (distance
  --    `< 1/(k+1)`); sizes increase.  `posHomPoint φ₀ ∈ closure Y` by `subset_closure hφ₀`.
  -- Assemble `ψ ∈ relQσ hc Y σ` (mind the `(toPosHom ψ).coe` vs `ψ.val` glue).
  -- Step 1: a forbidden-free flag sequence converging to `φ₀`.
  have hvan : ∀ D : FinFlag ∅ₜ, (hc.constraintOf ∅ₜ).forb0 D → φ₀.coe D = 0 := by
    intro D hD
    have h := (mem_Qσ_iff (hc.constraintOf ∅ₜ).forb0 (posHomPoint φ₀)).mp (hY hφ₀) D hD
    rwa [posHomPoint_val_apply, ← PositiveHom.coe_flag] at h
  obtain ⟨s, hconv_s, hff⟩ :=
    exists_constrained_flagSeq_limit φ₀ (hc.constraintOf ∅ₜ).forb0 hvan
  -- Step 2: every term of `s` has its underlying graph in the class.
  have hmem_s : ∀ t, hc.underlyingMem (s t).2 := by
    intro t
    by_contra hnot
    have h0 : flagDensity₁ (s t).2 (s t).2 = 0 := hff t ⟨(s t).1, (s t).2⟩ hnot
    rw [flagDensity_self] at h0
    exact one_ne_zero h0
  -- Step 3: the type density is eventually positive; pass to the tail.
  have hσR : (0:ℝ) < φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩ := by
    rw [PositiveHom.coe_flag]
    exact hσ
  have hev : ∀ᶠ m in atTop, 0 < flagDensitySeq s m ⟨n₀, σ.toEmptyTypeFlag⟩ :=
    ((flagSeq_convergesTo_iff.mp hconv_s).2 ⟨n₀, σ.toEmptyTypeFlag⟩).eventually
      (eventually_gt_nhds hσR)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set s' : FlagSeq ∅ₜ := fun m => s (m + N) with hs'def
  have hconv' : ConvergesTo s' φ₀.coe := convergesTo_tail hconv_s N
  have hs'pos : ∀ m, flagDensity₁ σ.toEmptyTypeFlag (s' m).2 > 0 := by
    intro m
    have h' : (0:ℝ) < ((flagDensity₁ σ.toEmptyTypeFlag (s (m + N)).2 : ℚ) : ℝ) :=
      hN (m + N) (Nat.le_add_left N m)
    show flagDensity₁ σ.toEmptyTypeFlag (s (m + N)).2 > 0
    exact_mod_cast h'
  have hmem' : ∀ m, hc.underlyingMem (s' m).2 := fun m => hmem_s (m + N)
  -- Step 4: weak convergence of the rooting measures to the extension measure.
  have htendP : Tendsto (FlagSeq.toProbMeasureSeq s' hs'pos) atTop
      (𝓝 (rootingMeasureFDS φ₀ hσ)) :=
    tendsto_rootingMeasure_extend hσ s' hs'pos hconv'
  -- Fix a support point.
  intro ψ hψ
  -- Step 5: every ball around `ψ.val` has positive limit measure.
  have hball_pos : ∀ r : ℝ, 0 < r →
      0 < (rootingMeasureFDS φ₀ hσ : Measure (FlagDensitySpace σ)) (Metric.ball ψ.val r) := by
    intro r hr
    have hmap : (rootingMeasureFDS φ₀ hσ : Measure (FlagDensitySpace σ)) (Metric.ball ψ.val r)
        = (ℙ[φ₀] : Measure (PositiveHomSpace σ)) (Subtype.val ⁻¹' Metric.ball ψ.val r) := by
      simp only [rootingMeasureFDS]
      rw [ProbabilityMeasure.toMeasure_map,
        Measure.map_apply measurable_subtype_coe measurableSet_ball]
    rw [hmap]
    have hopen : IsOpen (Subtype.val ⁻¹' Metric.ball ψ.val r : Set (PositiveHomSpace σ)) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    exact (Measure.mem_support_iff_forall ψ).mp hψ _
      (hopen.mem_nhds (Metric.mem_ball_self hr))
  -- Step 6: positive finite rooting mass on shrinking balls, along strictly increasing indices.
  have hev_ball : ∀ k : ℕ, ∀ᶠ m in atTop,
      0 < (FlagSeq.toProbMeasureSeq s' hs'pos m : Measure (FlagDensitySpace σ))
            (Metric.ball ψ.val (1 / (k + 1))) := by
    intro k
    have hr : (0:ℝ) < 1 / (k + 1) := by positivity
    have hliminf :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto htendP
        (Metric.isOpen_ball (x := ψ.val) (ε := 1 / (k + 1)))
    exact eventually_lt_of_lt_liminf (lt_of_lt_of_le (hball_pos _ hr) hliminf)
  have hchoice : ∀ k m : ℕ, ∃ j, m < j ∧
      0 < (FlagSeq.toProbMeasureSeq s' hs'pos j : Measure (FlagDensitySpace σ))
            (Metric.ball ψ.val (1 / (k + 1))) :=
    fun k m => ((eventually_gt_atTop m).and (hev_ball k)).exists
  choose sel hsel1 hsel2 using hchoice
  set idx : ℕ → ℕ :=
    fun k => Nat.rec (motive := fun _ => ℕ) (sel 0 0) (fun k ih => sel (k + 1) ih) k with hidx
  have hidx_mono : StrictMono idx := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact hsel1 (k + 1) (idx k)
  have hidx_pos : ∀ k,
      0 < (FlagSeq.toProbMeasureSeq s' hs'pos (idx k) : Measure (FlagDensitySpace σ))
            (Metric.ball ψ.val (1 / (k + 1))) := by
    intro k
    cases k with
    | zero => exact hsel2 0 0
    | succ k => exact hsel2 (k + 1) (idx k)
  -- Step 7: extract, for each `k`, a labelled flag whose profile lies in the ball.
  have hflag : ∀ k, ∃ F' ∈ labelExtensions (s' (idx k)).2 σ,
      funFromFlagWithSizeToFlagDensitySpace σ (s' (idx k)).1 F'
        ∈ Metric.ball ψ.val (1 / (k + 1)) :=
    fun k => exists_labelExtension_of_pos_measure (s' (idx k)) (hs'pos (idx k)) _ (hidx_pos k)
  choose Fk hFk_mem hFk_ball using hflag
  -- Step 8: the witness sequence of labelled flags of the in-class graphs.
  set GsW : FlagSeq σ := fun k => ⟨(s' (idx k)).1, Fk k⟩ with hGsW
  have hunlabel : ∀ k, unlabel (Fk k) = (s' (idx k)).2 := by
    intro k
    have h := hFk_mem k
    dsimp only [labelExtensions] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hunlabSeq : unlabelSeq GsW = s' ∘ idx := by
    funext k
    show (⟨(s' (idx k)).1, unlabel (Fk k)⟩ : FinFlag ∅ₜ) = s' (idx k)
    rw [hunlabel k]
    rfl
  have hdist : ∀ k, dist (flagDensitySeq' GsW k) ψ.val < 1 / (k + 1) := by
    intro k
    have hball := hFk_ball k
    rw [Metric.mem_ball] at hball
    exact hball
  have htendW : Tendsto (flagDensitySeq' GsW) atTop (𝓝 ψ.val) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => (hdist k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [relQσ, Set.mem_setOf_eq]
  refine ⟨GsW, φ₀, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hconv'.1.comp hidx_mono
  · have hcoe : (PositiveHomSpace.toPosHom ψ).coe = ψ.val := Classical.choose_spec ψ.property
    rw [hcoe]
    exact tendsto_flagDensitySeq'_iff.mp htendW
  · intro t
    show hc.underlyingMem (unlabel (Fk t))
    rw [hunlabel t]
    exact hmem' (idx t)
  · rw [hunlabSeq]
    exact convergesTo_comp hidx_mono hconv'
  · exact subset_closure hφ₀

/-- Random rooting sees only planted views: `S_σ(Y) ⊆ Q_σ(Y)`
(`prop:relative-plantability` (i)). -/
theorem relSσ_subset_relQσ (hc : HeredClass) {Y : Set (PositiveHomSpace ∅ₜ)}
    (hY : Y ⊆ Qσ (hc.constraintOf ∅ₜ).forb0) :
    relSσ Y σ ⊆ relQσ hc Y σ := by
  -- `closure_minimal` (with `relQσ_isClosed`) over the generating union, each support handled
  -- by `support_subset_relQσ` (mirror the `Set.iUnion_subset` dance of `Sσ_subset_Qσ`).
  refine closure_minimal ?_ (relQσ_isClosed hc Y)
  refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
  exact support_subset_relQσ hc hY hφ₀ hσ

/-- `Q_σ(Q₀) = Q_σ` (`prop:relative-plantability` (i), last clause). -/
theorem relQσ_Q0_eq (hc : HeredClass) :
    relQσ hc (Qσ (hc.constraintOf ∅ₜ).forb0) σ = Qσ (hc.constraintOf σ).forbσ := by
  -- `⊆` is `relQσ_subset_Qσ`.  For `⊇`, fix `χ ∈ Qσ forbσ`:
  -- * `exists_constrained_flagSeq_limit (PositiveHomSpace.toPosHom χ) (hc.constraintOf σ).forbσ`
  --   (vanishing from `mem_Qσ_iff` + glue) gives `Gs : FlagSeq σ`, `ConvergesTo Gs (toPosHom χ).coe`,
  --   all `Gs t` forbidden-density-free;
  -- * in-class: `HeredClass.mem_of_forbiddenFree` (F1) on a `Quotient` representative of
  --   `(Gs t).2`, then `HeredClass.underlyingMem_unlabel_mk`;
  -- * the unlabelled sequence `unlabelSeq Gs` `Increases` (same sizes); extract a convergent
  --   subsequence (`increasing_flagSeq_contain_convergent_subseq` at `∅ₜ`), get its limit hom
  --   `φ` via `flagSeq_limit_mem_positiveHom`;
  -- * `posHomPoint φ ∈ Qσ forb0` by `flagSeqLimit_mem_Q0_of_underlyingMem` (membership of the
  --   subsequence flags is inherited), and `Qσ` is closed so it equals its closure
  --   (`IsClosed.closure_eq` with `Qσ_isClosed` — the `closure Y` clause);
  -- * the same subsequence of `Gs` still converges to `χ` (`ConvergesTo` composed with a
  --   `StrictMono`, cf. `increasing_flagSeq_contain_convergent_subseq`'s own composition).
  refine Set.Subset.antisymm (relQσ_subset_Qσ hc _) ?_
  intro χ hχ
  -- a forbidden-free flag sequence converging to `χ`
  have hvan : ∀ F : FinFlag σ, (hc.constraintOf σ).forbσ F →
      (PositiveHomSpace.toPosHom χ).coe F = 0 := by
    intro F hF
    have hcoe : (PositiveHomSpace.toPosHom χ).coe = χ.val := Classical.choose_spec χ.property
    rw [hcoe]
    exact (mem_Qσ_iff (hc.constraintOf σ).forbσ χ).mp hχ F hF
  obtain ⟨Gs, hconv, hff⟩ :=
    exists_constrained_flagSeq_limit (PositiveHomSpace.toPosHom χ) (hc.constraintOf σ).forbσ hvan
  -- every term of `Gs` has its underlying graph in the class
  have hmem : ∀ t, hc.underlyingMem (unlabel (Gs t).2) := by
    intro t
    rcases Quotient.exists_rep (Gs t).2 with ⟨Grep, hGrep⟩
    rw [← hGrep, hc.underlyingMem_unlabel_mk]
    exact hc.mem_of_forbiddenFree Grep (fun F hF => by rw [hGrep]; exact hff t F hF)
  -- the unlabelled sequence increases; extract a convergent subsequence and its limit hom
  have hinc : Increases (unlabelSeq Gs) := hconv.1
  obtain ⟨a, ϕ, hϕ, hconv0⟩ := increasing_flagSeq_contain_convergent_subseq (unlabelSeq Gs) hinc
  obtain ⟨φ, hφcoe⟩ := flagSeq_limit_mem_positiveHom (unlabelSeq Gs ∘ ϕ) hconv0
  -- the base limit is constrained
  have hmemQ0 : posHomPoint φ ∈ Qσ (hc.constraintOf ∅ₜ).forb0 := by
    refine flagSeqLimit_mem_Q0_of_underlyingMem hc (sH := unlabelSeq Gs ∘ ϕ) ?_ ?_
    · rw [hφcoe]; exact hconv0
    · intro t; exact hmem (ϕ t)
  -- assemble the witness
  simp only [relQσ, Set.mem_setOf_eq]
  refine ⟨Gs ∘ ϕ, φ, convergesTo_comp hϕ hconv, fun t => hmem (ϕ t), ?_, ?_⟩
  · show ConvergesTo (unlabelSeq Gs ∘ ϕ) φ.coe
    rw [hφcoe]
    exact hconv0
  · rw [(Qσ_isClosed _).closure_eq]
    exact hmemQ0

/-- **Relative root-plantability at `Y = Q₀` is root-plantability**
(`prop:relative-plantability` (i), consequence). -/
theorem relativelyRootPlantable_Q0_iff (hc : HeredClass) :
    RelativelyRootPlantable hc (Qσ (hc.constraintOf ∅ₜ).forb0) σ
      ↔ RootPlantable (hc.constraintOf σ) := by
  -- Unfold both sides; rewrite with `Sσ_eq_relSσ` (note
  -- `(hc.constraintOf σ).forb0 = (hc.constraintOf ∅ₜ).forb0` — check defeq; if not
  -- syntactically equal, add the one-line bridging `rfl`/`show`) and `relQσ_Q0_eq`.
  have hS : relSσ (Qσ (hc.constraintOf ∅ₜ).forb0) σ = Sσ (hc.constraintOf σ) := rfl
  unfold RelativelyRootPlantable RootPlantable
  rw [relQσ_Q0_eq hc, hS]

/-! ## The relative planted criterion: `prop:relative-plantability` (ii) -/

/-- Non-negativity on the planted set implies relative ensemble semantics. -/
theorem relQσ_nonneg_implies_relEnsemble (hc : HeredClass) {Y : Set (PositiveHomSpace ∅ₜ)}
    (hY : Y ⊆ Qσ (hc.constraintOf ∅ₜ).forb0) (f : FlagAlgebra σ)
    (hf : ∀ χ ∈ relQσ hc Y σ, 0 ≤ (PositiveHomSpace.toPosHom χ) f) :
    RelEnsembleNonneg Y f := by
  -- Restrict `hf` along `relSσ_subset_relQσ` and apply `relative_criterion`.
  exact (relative_criterion Y f).mp fun χ hχ => hf χ (relSσ_subset_relQσ hc hY hχ)

/-- **The relative planted criterion** (`prop:relative-plantability` (ii)): non-negativity on
`Q_σ(Y)` and relative ensemble semantics agree for *every* `f` iff `(Y, σ)` is relatively
root-plantable. -/
theorem relative_planted_criterion (hc : HeredClass) {Y : Set (PositiveHomSpace ∅ₜ)}
    (hY : Y ⊆ Qσ (hc.constraintOf ∅ₜ).forb0) :
    (∀ f : FlagAlgebra σ,
        (∀ χ ∈ relQσ hc Y σ, 0 ≤ (PositiveHomSpace.toPosHom χ) f) ↔ RelEnsembleNonneg Y f)
      ↔ RelativelyRootPlantable hc Y σ := by
  -- Mirror `support_criterion` (SupportClosure) with `Qσ → relQσ hc Y σ`,
  -- `Sσ → relSσ Y σ`, `EnsembleNonneg → RelEnsembleNonneg` (via `relative_criterion`):
  -- * (⇐) given equality of the two sets, both sides of each iff coincide by
  --   `relative_criterion`.
  -- * (⇒) `Set.Subset.antisymm (relSσ_subset_relQσ hc hY)`; for the reverse inclusion,
  --   `by_contra` a point `ψ ∈ relQσ \ relSσ`; Urysohn in the compact metric `X_σ`
  --   (`exists_continuous_zero_one_of_isClosed`, `relSσ_isClosed`, `{ψ}` closed, disjoint);
  --   `H := 1 - 2u`, `exists_flag_near` at `ε := 1/3`; the resulting `f` satisfies
  --   `RelEnsembleNonneg Y f` (its evaluation is `≥ 1/3 > 0` on `relSσ`, then
  --   `relative_criterion`) yet is negative at `ψ ∈ relQσ` — contradicting the `f`-instance
  --   of the hypothesis.  Copy the structure of `support_criterion` lines 143–178.
  constructor
  · -- equivalence for all `f` forces `S_σ(Y) = Q_σ(Y)`
    intro hequiv
    refine Set.Subset.antisymm (relSσ_subset_relQσ hc hY) ?_
    by_contra hcon
    rw [Set.not_subset] at hcon
    obtain ⟨ψ, hψQ, hψS⟩ := hcon
    -- Urysohn directly in the compact metric space `X_σ`
    obtain ⟨u, hu0, hu1, _⟩ := exists_continuous_zero_one_of_isClosed (X := PositiveHomSpace σ)
      (relSσ_isClosed Y σ) (isClosed_singleton (x := ψ))
      (Set.disjoint_singleton_right.mpr hψS)
    -- `H = 1 - 2u`: `H = 1` on `S_σ(Y)`, `H ψ = -1`
    set H : PositiveHomSpace σ → ℝ := fun χ => 1 - 2 * u χ with hH
    have hHcont : Continuous H := continuous_const.sub (continuous_const.mul u.continuous)
    obtain ⟨f, hf⟩ := exists_flag_near H hHcont (ε := 1/3) (by norm_num)
    -- `f` is relatively ensemble-nonneg (positive on `S_σ(Y)`)…
    have hEns : RelEnsembleNonneg Y f := by
      rw [← relative_criterion]
      intro χ hχ
      have huχ : u χ = 0 := by simpa using hu0 hχ
      have hHχ : H χ = 1 := by simp only [hH, huχ, mul_zero, sub_zero]
      have hbound := hf χ
      rw [hHχ, abs_lt] at hbound
      linarith [hbound.1]
    -- …but negative at `ψ ∈ Q_σ(Y)`
    have hNotQuot : ¬ (∀ χ ∈ relQσ hc Y σ, 0 ≤ (PositiveHomSpace.toPosHom χ) f) := by
      intro hQ
      have hpos := hQ ψ hψQ
      have huψ : u ψ = 1 := by simpa using hu1 rfl
      have hHψ : H ψ = -1 := by simp only [hH, huψ]; norm_num
      have hbound := hf ψ
      rw [hHψ, abs_lt] at hbound
      linarith [hbound.2]
    exact hNotQuot ((hequiv f).mpr hEns)
  · -- relative root-plantability gives the equivalence
    intro hRP f
    refine ⟨relQσ_nonneg_implies_relEnsemble hc hY f, ?_⟩
    intro hE χ hχ
    have hχS : χ ∈ relSσ Y σ := by rw [hRP]; exact hχ
    exact (relative_criterion Y f).mpr hE χ hχS

end FlagAlgebras.MetaTheory
