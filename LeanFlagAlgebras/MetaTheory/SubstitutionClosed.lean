import LeanFlagAlgebras.MetaTheory.SubstitutionSequence
import LeanFlagAlgebras.MetaTheory.SubstitutionEstimate
import LeanFlagAlgebras.MetaTheory.ConstrainedRep
import LeanFlagAlgebras.MetaTheory.HeredClass
import LeanFlagAlgebras.MetaTheory.CapstoneShared
import LeanFlagAlgebras.MetaTheory.WeakConvergence
import LeanFlagAlgebras.MetaTheory.BinomialRatio

/-! # The substitution-root-plantability theorem (paper §6–§7)

This is the §6–§7 analogue of `clone_root_plantable` (`thm:true-clone-root-plantable` /
`thm:substitution-root-plantable`).  For a hereditary class `hc` (no clone-closure assumption) and a
nontrivial type `σ`, given a *within-class blow-up closure* hypothesis `hclosure` — every member `Γ`
has, for every `M`, a within-class family `W` whose uniform `(M+1)`-generalised blow-up
`subBlowup Γ W` stays in the class — the constraint `hc.constraintOf σ` is root-plantable.

The proof follows the same line as the §5 capstone (`CloneClosed.lean`), replacing the independent
blow-up with `subBlowup Γ (Wf M)` and the §5 sequence/estimate lemmas with their `…_sub` analogues:
the asymptotic planted-estimate gap has the same `1 − ρ` form, so the arithmetic carries over
verbatim.  All the §5 measure-theoretic / topological infrastructure
(`toProbMeasure_apply_eq_labeling_ratio`, `cyl`, `isClosed_cyl`,
`mem_closure_of_forall_finset_cylinder`, `rhoInf`, the labelling-count lemmas, `transportLabeled`,
…) is reused directly from `CloneClosed.lean`.
-/

open MeasureTheory Filter Topology
open SimpleGraph

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

attribute [local instance] Classical.propDecidable

open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- σ-type density of every generalised blow-up flag is positive (a uniform `1/n^{n₀}` lower
bound), the generalised-blow-up analogue of `blowupFlagSeq_type_pos`. -/
theorem blowupFlagSeq_sub_type_pos {n : ℕ} (hn : 0 < n) {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ)
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq_sub Γ Wf M).2 > 0 := by
  have h := flagDensity_type_blowupFlagSeq_sub_lower hn θ Wf M
  have hpos : (0 : ℚ) < 1 / (n ^ n₀) := by positivity
  exact lt_of_lt_of_le hpos h

/-- σ-embeddings into the generalised blow-up biject with the ordered induced embeddings
`blowupEmbeddings_sub` (an embedding is exactly an injective, adjacency-reflecting vertex map),
the generalised-blow-up analogue of `embeddingEquivBlowupEmbeddings`. -/
private def embeddingEquivBlowupEmbeddings_sub {n : ℕ} (Γ : SimpleGraph (Fin n))
    (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) :
    (σ ↪g subBlowup Γ W) ≃ {g // g ∈ blowupEmbeddings_sub Γ σ m W} where
  toFun e := ⟨(e : Fin n₀ → Σ v : Fin n, Fin (m v)), by
    simp only [blowupEmbeddings_sub, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e.injective, fun i j => (e.map_adj_iff).symm⟩⟩
  invFun g := ⟨⟨g.1, by
    have hg := g.2
    simp only [blowupEmbeddings_sub, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact hg.1⟩, by
    intro i j
    have hg := g.2
    simp only [blowupEmbeddings_sub, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact (hg.2 i j).symm⟩
  left_inv e := by rfl
  right_inv g := by rfl

/-- **Per-`M` step of the planted-mass cylinder bound (generalised).**  Given the planted-estimate
gap bound on every coordinate of `Fs` at the uniform clone size `M+1`, the σ-rooting measure of the
closed cylinder centered at the base profile is at least the planted fraction `(1/(2n))^{n₀}`,
the generalised-blow-up analogue of `planted_cylinder_mass_step`. -/
private theorem planted_cylinder_mass_step_sub {n : ℕ} (hn : 0 < n) (hn₀ : 0 < n₀)
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ) (Fs : Finset (FinFlag σ)) {δ : ℝ} (_hδ : 0 < δ)
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ)
    (hM_gap : ∀ Fi ∈ Fs, (1 : ℝ) - (((M + 1 : ℕ) ^ (Fi.1 - n₀) * ((n - n₀).choose (Fi.1 - n₀)) : ℚ)
          / (((n * (M + 1) - n₀).choose (Fi.1 - n₀))) : ℝ) ≤ δ) :
    (1 / (2 * n : ℝ)) ^ n₀ ≤
      (((blowupFlagSeq_sub Γ Wf M).toProbMeasure (blowupFlagSeq_sub_type_pos hn θ Wf M)
          : Measure (FlagDensitySpace σ))
          (cyl Fs (fun Fi => (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n)) : ℝ)) δ)).toReal := by
  classical
  set N : ℕ := n * (M + 1) with hN
  set m : Fin n → ℕ := fun _ => M + 1 with hm
  set K : SimpleGraph (Fin N) := subBlowupGraphFin Γ Wf M with hK
  set F_M : FinFlag ∅ₜ := blowupFlagSeq_sub Γ Wf M with hFM
  -- The center profile and cylinder.
  set base : FinFlag σ → ℝ :=
    fun Fi => (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n)) : ℝ) with hbase
  set C : Set (FlagDensitySpace σ) := cyl Fs base δ with hC
  -- The representative host graph and its iso to `K`.
  set host' : SimpleGraph (Fin F_M.1) := (Quotient.out F_M.2).graph with hhost'
  have hF_M1 : F_M.1 = N := rfl
  -- `out F_M.2 ∼f Krep` where `Krep` is `K` with the empty-type embedding.
  set Krep : LabeledGraph ∅ₜ (Fin N) :=
    {graph := K, type_embed := RelEmbedding.ofIsEmpty (∅ₜ).Adj K.Adj} with hKrep
  have hFM2 : F_M.2 = (graphFlag K) := rfl
  have hgraphFlag : graphFlag K = (⟦Krep⟧ : Flag ∅ₜ (Fin N)) := rfl
  have hout_eq : (⟦Quotient.out F_M.2⟧ : Flag ∅ₜ (Fin N)) = (⟦Krep⟧ : Flag ∅ₜ (Fin N)) := by
    rw [Quotient.out_eq]; rw [hFM2, hgraphFlag]
  have hout_iso : (Quotient.out F_M.2) ≈ Krep := Quotient.exact hout_eq
  obtain ⟨ψhost⟩ := hout_iso
  -- The host iso `host' ≃g K`.
  have eHostK : host' ≃g K := ψhost.graph_iso
  -- The presentation iso `K ≃g subBlowup Γ (Wf M)`.
  have eKB' : K ≃g subBlowup Γ (Wf M) := (subBlowupGraphFin_iso Γ Wf M).symm
  -- Apply the count-ratio formula.
  rw [toProbMeasure_apply_eq_labeling_ratio F_M (blowupFlagSeq_sub_type_pos hn θ Wf M) C]
  -- Abbreviate the numerator/denominator labeling counts.
  set numSet := Finset.univ.filter (fun H : LabeledGraph σ (Fin F_M.1) =>
      H.graph = host' ∧ funFromFlagWithSizeToFlagDensitySpace σ F_M.1 (⟦H⟧ : FlagWithSize σ F_M.1) ∈ C)
    with hnumSet
  set denSet := Finset.univ.filter (fun H : LabeledGraph σ (Fin F_M.1) => H.graph = host')
    with hdenSet
  -- Profile membership in `C` unfolds to the cylinder condition.
  have hprofile : ∀ H : LabeledGraph σ (Fin F_M.1),
      (funFromFlagWithSizeToFlagDensitySpace σ F_M.1 (⟦H⟧ : FlagWithSize σ F_M.1) ∈ C)
        ↔ ∀ Fi ∈ Fs, |(flagDensity₁ Fi.2 (⟦H⟧ : Flag σ (Fin F_M.1)) : ℝ) - base Fi| ≤ δ := by
    intro H
    rw [hC, cyl, Set.mem_setOf_eq]
    rfl
  -- (1) The denominator is the number of σ-embeddings into the blow-up presentation.
  have hden_eq : denSet.card = (blowupEmbeddings_sub Γ σ m (Wf M)).card := by
    rw [hdenSet, card_labelings_eq_card_embeddings host']
    rw [← Fintype.card_coe (blowupEmbeddings_sub Γ σ m (Wf M))]
    apply Fintype.card_congr
    have eHostB' : host' ≃g subBlowup Γ (Wf M) := eHostK.trans eKB'
    have e1 : (σ ↪g host') ≃ (σ ↪g subBlowup Γ (Wf M)) := embeddingIsoCongr eHostB'
    have e3 : (σ ↪g subBlowup Γ (Wf M)) ≃ {g // g ∈ blowupEmbeddings_sub Γ σ m (Wf M)} :=
      embeddingEquivBlowupEmbeddings_sub (σ := σ) Γ m (Wf M)
    exact e1.trans e3
  -- (2) Planted embeddings inject into the numerator labelings.
  have hplanted_inj : (plantedEmbeddings m θ).card ≤ numSet.card := by
    -- The composed iso `(subBlowup Γ (Wf M)) ≃g host'`.
    have eB'Host : (subBlowup Γ (Wf M)) ≃g host' := (eHostK.trans eKB').symm
    -- Map each clone choice `cc` to the transported labelling of `host'`.
    rw [plantedEmbeddings_card m θ]
    -- The number of clone choices.
    have hcard_choices : (∏ i, m (θ i)) = Fintype.card (∀ i : Fin n₀, Fin (m (θ i))) := by
      rw [Fintype.card_pi]; simp
    rw [hcard_choices, ← Fintype.card_coe numSet]
    -- An injection `(∀ i, Fin (m (θ i))) ↪ numSet`.
    apply Fintype.card_le_of_injective
      (fun cc => ⟨transportLabeled (G := subBlowupLabeledGraph m (Wf M) θ cc) eB'Host, by
        rw [hnumSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, rfl, ?_⟩
        rw [hprofile]
        intro Fi hFi
        -- The transported labelling is `≃f` the Σ-planted labelled graph `subBlowupLabeledGraph`.
        have hiso : (transportLabeled (G := subBlowupLabeledGraph m (Wf M) θ cc) eB'Host)
            ≃f (subBlowupLabeledGraph m (Wf M) θ cc) :=
          (transportLabeled_iso (G := subBlowupLabeledGraph m (Wf M) θ cc) eB'Host).symm
        have hdens : (flagDensity₁ Fi.2
              (⟦transportLabeled (G := subBlowupLabeledGraph m (Wf M) θ cc) eB'Host⟧
                : Flag σ (Fin F_M.1)) : ℝ)
            = (flagDensity₁ Fi.2 (⟦subBlowupLabeledGraph m (Wf M) θ cc⟧
                : Flag σ (Σ v : Fin n, Fin (m v))) : ℝ) := by
          have h := flagDensity₁_respect_eqv Fi hiso
          exact_mod_cast h
        rw [hdens]
        -- Planted estimate: density within `1 − ρ` of the base density.
        have hpe := planted_estimate_sub m (Wf M) θ cc (Quotient.out Fi.2) (M + 1) (fun v _ => rfl)
        -- Rewrite the base profile and the estimate's flags to the `Fi.2` / `baseLabeledGraph` form.
        have hFi2out : (⟦Quotient.out Fi.2⟧ : Flag σ (Fin Fi.1)) = Fi.2 := Quotient.out_eq Fi.2
        rw [hFi2out] at hpe
        have hbase_eq : base Fi
            = (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n)) : ℝ) := rfl
        rw [hbase_eq]
        -- The planted-estimate gap is `≤ δ` by hypothesis.
        have hgapb := hM_gap Fi hFi
        -- The denominator `∑ _v, (M+1) = n*(M+1)`.
        have hsum : (∑ _v : Fin n, (M + 1)) = n * (M + 1) := by
          simp [Finset.sum_const, Finset.card_univ]
        rw [hsum] at hpe
        -- Cast the rational estimate to ℝ.
        have hpe' : |(flagDensity₁ Fi.2
              (⟦subBlowupLabeledGraph m (Wf M) θ cc⟧ : Flag σ (Σ v : Fin n, Fin (m v))) : ℝ)
            - (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n)) : ℝ)|
            ≤ (1 : ℝ) - (((M + 1 : ℕ) ^ (Fi.1 - n₀) * ((n - n₀).choose (Fi.1 - n₀)) : ℚ)
                / (((n * (M + 1)) - n₀).choose (Fi.1 - n₀))) := by
          have hq : ((|flagDensity₁ Fi.2
                (⟦subBlowupLabeledGraph m (Wf M) θ cc⟧ : Flag σ (Σ v : Fin n, Fin (m v)))
              - flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n))| : ℚ) : ℝ)
              ≤ (((1 : ℚ) - ((M + 1 : ℕ) ^ (Fi.1 - n₀) * ((n - n₀).choose (Fi.1 - n₀)) : ℚ)
                  / (((n * (M + 1)) - n₀).choose (Fi.1 - n₀)) : ℚ) : ℝ) := by
            exact_mod_cast hpe
          rw [Rat.cast_abs, Rat.cast_sub] at hq
          push_cast at hq ⊢
          convert hq using 2
        calc |(flagDensity₁ Fi.2 (⟦subBlowupLabeledGraph m (Wf M) θ cc⟧
                : Flag σ (Σ v : Fin n, Fin (m v))) : ℝ)
              - (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n)) : ℝ)|
            ≤ _ := hpe'
          _ ≤ δ := hgapb⟩)
      ?_
    -- injectivity of `cc ↦ transported labelling`
    intro cc₁ cc₂ heq
    -- Equality of the subtype values gives equality of the underlying labellings.
    have heq' : transportLabeled (G := subBlowupLabeledGraph m (Wf M) θ cc₁) eB'Host
        = transportLabeled (G := subBlowupLabeledGraph m (Wf M) θ cc₂) eB'Host := Subtype.ext_iff.mp heq
    -- Hence their type-embedding functions agree.
    have hte : (fun i => eB'Host ((⟨θ i, cc₁ i⟩ : Σ v : Fin n, Fin (m v))))
        = (fun i => eB'Host ((⟨θ i, cc₂ i⟩ : Σ v : Fin n, Fin (m v)))) := by
      have := congrArg (fun H : LabeledGraph σ (Fin F_M.1) =>
        (H.type_embed : Fin n₀ → Fin F_M.1)) heq'
      simpa only [transportLabeled, subBlowupLabeledGraph, SimpleGraph.Embedding.coe_comp,
        Function.comp_apply, subBlowupPlantedEmb, SimpleGraph.Iso.toEmbedding,
        RelIso.coe_toRelEmbedding] using this
    funext i
    have h2 := congrFun hte i
    have h3 : (⟨θ i, cc₁ i⟩ : Σ v : Fin n, Fin (m v)) = ⟨θ i, cc₂ i⟩ := eB'Host.injective h2
    exact eq_of_heq (Sigma.mk.inj_iff.mp h3).2
  -- (3) Conclude via `planted_mass_sub`.
  have hn0Q : (0 : ℚ) < n := by exact_mod_cast hn
  have hmθ : ∀ i, m (θ i) = M + 1 := fun i => rfl
  have hsumN : ((∑ _v : Fin n, (M + 1) : ℕ) : ℚ) = (n : ℚ) * (M + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast; ring
  have hpm := planted_mass_sub m (Wf M) θ (lam := (n₀ : ℚ) / n) (by positivity) hn₀
    (fun v => Nat.le_add_left 1 M) (fun i => by
      rw [hmθ i, hsumN]
      have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
      have hN0 : (0 : ℚ) < n₀ := by exact_mod_cast hn₀
      have hge : ((n₀ : ℚ) / n) / (2 * n₀) * ((n : ℚ) * ((M : ℚ) + 1)) ≤ ((M : ℚ) + 1) := by
        rw [show ((n₀ : ℚ) / n) / (2 * n₀) * ((n : ℚ) * ((M : ℚ) + 1)) = ((M : ℚ) + 1) / 2 by
          field_simp]
        have hMpos : (0 : ℚ) ≤ (M : ℚ) + 1 := by positivity
        linarith
      have hcast : (((M : ℕ) + 1 : ℕ) : ℚ) = (M : ℚ) + 1 := by push_cast; ring
      rw [hcast]
      convert hge using 2)
  -- Identify `lam/(2·n₀) = 1/(2n)`.
  have hlam_eq : ((n₀ : ℚ) / n) / (2 * n₀) = 1 / (2 * n) := by
    have hN0 : (n₀ : ℚ) ≠ 0 := by exact_mod_cast hn₀.ne'
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [hlam_eq] at hpm
  -- Cast the ℚ ratio bound to ℝ.
  have hpmR : (1 / (2 * (n : ℝ))) ^ n₀
      ≤ ((plantedEmbeddings m θ).card : ℝ) / ((blowupEmbeddings_sub Γ σ m (Wf M)).card : ℝ) := by
    have hcast : (((1 / (2 * (n : ℚ))) ^ n₀ : ℚ) : ℝ)
        ≤ ((((plantedEmbeddings m θ).card : ℚ) / ((blowupEmbeddings_sub Γ σ m (Wf M)).card : ℚ)) : ℝ) := by
      exact_mod_cast hpm
    push_cast at hcast
    exact hcast
  -- The denominator is positive (a planted embedding exists).
  have hden_pos : (0 : ℝ) < (denSet.card : ℝ) := by
    rw [hden_eq]
    have hp0 : 0 < (plantedEmbeddings m θ).card := by
      rw [plantedEmbeddings_card]
      exact Finset.prod_pos (fun i _ => Nat.succ_pos M)
    have hbpos : 0 < (blowupEmbeddings_sub Γ σ m (Wf M)).card :=
      lt_of_lt_of_le hp0 (Finset.card_le_card (plantedEmbeddings_subset_sub m (Wf M) θ))
    exact_mod_cast hbpos
  -- Combine: the actual ratio dominates the planted ratio.
  refine le_trans hpmR ?_
  rw [hden_eq]
  rw [hden_eq] at hden_pos
  exact div_le_div_of_nonneg_right (by exact_mod_cast hplanted_inj) hden_pos.le

/-- **The planted-mass cylinder bound (generalised).**  The generalised-blow-up analogue of
`planted_cylinder_mass`.  For the uniform generalised blow-up sequence of an in-class base `Γ` with `σ`-embedding `θ`, if the
cylinder radius `δ` accommodates the asymptotic planted-estimate gap on every coordinate of `Fs`,
then the σ-rooting measure of the closed cylinder centered at the *base* density profile carries,
for all large `M`, a positive mass bounded below by the planted fraction `(1/(2n))^{n₀}`. -/
private theorem planted_cylinder_mass_sub {n : ℕ} (hn : 0 < n) (hn₀ : 0 < n₀)
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ)
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1)))
    (Fs : Finset (FinFlag σ)) {δ : ℝ} (hδ : 0 < δ)
    (hacc : ∀ Fi ∈ Fs, (1 : ℝ) - rhoInf n₀ n (Fi.1 - n₀) < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M in atTop,
      c ≤ (((blowupFlagSeq_sub Γ Wf M).toProbMeasure (blowupFlagSeq_sub_type_pos hn θ Wf M)
          : Measure (FlagDensitySpace σ))
          (cyl Fs (fun Fi => (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin n)) : ℝ)) δ)).toReal := by
  classical
  -- The planted fraction lower bound.
  refine ⟨(1 / (2 * n : ℝ)) ^ n₀, by positivity, ?_⟩
  -- For each coordinate `Fi ∈ Fs`, the planted-estimate ratio eventually drops the gap below `δ`.
  have hρ_event : ∀ Fi ∈ Fs, ∀ᶠ M in atTop,
      (1 : ℝ) - (((M + 1 : ℕ) ^ (Fi.1 - n₀) * ((n - n₀).choose (Fi.1 - n₀)) : ℚ)
          / (((n * (M + 1) - n₀).choose (Fi.1 - n₀))) : ℝ) ≤ δ := by
    intro Fi hFi
    set r := Fi.1 - n₀ with hr
    have hr1 : 1 ≤ r ∨ r = 0 := by omega
    -- The ratio tends to `ρ_∞(n, r)` as the clone size `→ ∞`.
    have hlim : Tendsto (fun M : ℕ =>
        (((M + 1 : ℕ) ^ r * ((n - n₀).choose r) : ℚ) / (((n * (M + 1) - n₀).choose r)) : ℝ))
        atTop (𝓝 (rhoInf n₀ n r)) := by
      rcases hr1 with hr1 | hr0
      · have hq := rho_tendsto_atTop n n₀ r hr1 hn
        have hq' := hq.comp (tendsto_add_atTop_nat 1)
        have hcast := (Rat.continuous_coe_real.tendsto
          (((n - n₀).descFactorial r : ℚ) / ((n : ℚ) ^ r))).comp hq'
        have hlimeq : (((((n - n₀).descFactorial r : ℚ) / ((n : ℚ) ^ r)) : ℚ) : ℝ)
            = rhoInf n₀ n r := by simp only [rhoInf]; push_cast; ring
        rw [hlimeq] at hcast
        refine hcast.congr (fun M => ?_)
        simp only [Function.comp_apply]
        push_cast
        rfl
      · have hconst : ∀ M : ℕ,
            (((M + 1 : ℕ) ^ r * ((n - n₀).choose r) : ℚ) / (((n * (M + 1) - n₀).choose r)) : ℝ)
              = rhoInf n₀ n r := by
          intro M
          simp only [hr0, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, div_one, rhoInf,
            Nat.descFactorial_zero]
          norm_num
        rw [tendsto_congr hconst]
        exact tendsto_const_nhds
    -- The gap tends to `1 − ρ_∞(n, r) < δ`, hence is `< δ` and `≤ δ` eventually.
    have hgap : Tendsto (fun M : ℕ =>
        (1 : ℝ) - (((M + 1 : ℕ) ^ r * ((n - n₀).choose r) : ℚ)
          / (((n * (M + 1) - n₀).choose r)) : ℝ)) atTop (𝓝 (1 - rhoInf n₀ n r)) :=
      tendsto_const_nhds.sub hlim
    have hlt : (1 : ℝ) - rhoInf n₀ n r < δ := hacc Fi hFi
    filter_upwards [hgap.eventually (eventually_lt_nhds hlt)] with M hM
    exact hM.le
  -- Combine over the finite set `Fs`.
  have hρ_all : ∀ᶠ M in atTop, ∀ Fi ∈ Fs,
      (1 : ℝ) - (((M + 1 : ℕ) ^ (Fi.1 - n₀) * ((n - n₀).choose (Fi.1 - n₀)) : ℚ)
          / (((n * (M + 1) - n₀).choose (Fi.1 - n₀))) : ℝ) ≤ δ :=
    (eventually_all_finset Fs).mpr hρ_event
  -- Now prove the per-`M` ratio lower bound.
  filter_upwards [hρ_all] with M hM_gap
  exact planted_cylinder_mass_step_sub hn hn₀ θ Fs hδ Wf M hM_gap

/-! ## The substitution-root-plantability theorem -/

/-- **Substitution-root-plantability** (`thm:true-clone-root-plantable` /
`thm:substitution-root-plantable`).  For any hereditary graph class `hc` with the within-class
blow-up closure hypothesis `hclosure` and any nontrivial type `σ`, the constraint `hc.constraintOf σ`
is root-plantable: `S_σ = Q_σ`.  This is the generalised-blow-up form of `clone_root_plantable`,
using `subBlowup Γ (Wf M)` for an `hclosure`-supplied within-class family `Wf` in place of the §5
independent blow-up. -/
theorem subst_root_plantable (hc : HeredClass) {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀)
    (hclosure : ∀ {n : ℕ} (Γ : SimpleGraph (Fin n)), hc.Mem Γ → ∀ (M : ℕ),
        ∃ (W : ∀ _v : Fin n, SimpleGraph (Fin (M + 1))), hc.Mem (subBlowup Γ W)) :
    RootPlantable (hc.constraintOf σ) := by
  -- It suffices to prove `Q_σ ⊆ S_σ` (the reverse holds always).
  refine Set.Subset.antisymm (Sσ_subset_Qσ _) ?_
  intro ψ hψQ
  -- `ψ` vanishes on every forbidden σ-flag.
  rw [mem_Qσ_iff] at hψQ
  set ψh : PositiveHom σ := PositiveHomSpace.toPosHom ψ with hψh
  have hψh_coe : ∀ F : FinFlag σ, ψh.coe F = ψ.val F := by
    intro F
    rw [PositiveHom.coe_flag, PositiveHomSpace.toPosHom_basisVector]
  have hψh_forb : ∀ F : FinFlag σ, (hc.constraintOf σ).forbσ F → ψh.coe F = 0 := by
    intro F hF; rw [hψh_coe]; exact hψQ F hF
  -- Constrained representation: a forbidden-free flag sequence converging to `ψh`.
  obtain ⟨s, hconv_s, hff⟩ :=
    exists_constrained_flagSeq_limit ψh (hc.constraintOf σ).forbσ hψh_forb
  -- Reduce membership in the closure `S_σ` to the cylinder criterion.
  apply mem_closure_of_forall_finset_cylinder
  intro Fs ε hε
  -- `ε/10`-scale splits so the triangle inequalities give `< ε`.
  set η : ℝ := ε / 10 with hη
  have hη_pos : 0 < η := by rw [hη]; positivity
  -- The sizes `(s t).1` tend to `+∞`.
  have hsize_atTop : Tendsto (fun t => (s t).1) atTop atTop :=
    (flagSeq_convergesTo_iff.mp hconv_s).1.tendsto_atTop
  -- Choose `t` so that the densities are close and the planted gap is `< ε/2`.
  obtain ⟨t, ht_dens, ht_acc⟩ : ∃ t, (∀ Fi ∈ Fs, |flagDensity₁ Fi.2 (s t).2 - ψ.val Fi| < η) ∧
      (∀ Fi ∈ Fs, (1 : ℝ) - rhoInf n₀ (s t).1 (Fi.1 - n₀) < ε / 2) := by
    have hconv := (flagSeq_convergesTo_iff.mp hconv_s).2
    have hev : ∀ Fi : FinFlag σ, ∀ᶠ t in atTop, |flagDensity₁ Fi.2 (s t).2 - ψ.val Fi| < η := by
      intro Fi
      have hlim : Tendsto (fun t => (flagDensity₁ Fi.2 (s t).2 : ℝ)) atTop (𝓝 (ψ.val Fi)) := by
        have h := hconv Fi
        rw [hψh_coe Fi] at h
        exact h
      have hmetric := (Metric.tendsto_atTop.mp hlim) η hη_pos
      obtain ⟨N, hN⟩ := hmetric
      filter_upwards [eventually_ge_atTop N] with t ht
      have := hN t ht
      rwa [Real.dist_eq] at this
    have hev2 : ∀ Fi : FinFlag σ,
        ∀ᶠ t in atTop, (1 : ℝ) - rhoInf n₀ (s t).1 (Fi.1 - n₀) < ε / 2 := by
      intro Fi
      have hρ : Tendsto (fun N => rhoInf n₀ N (Fi.1 - n₀)) atTop (𝓝 1) := by
        have hq := rho_inf_tendsto_one n₀ (Fi.1 - n₀)
        have hcast : Tendsto (fun N : ℕ =>
            ((((N - n₀).descFactorial (Fi.1 - n₀) : ℚ) / ((N : ℚ) ^ (Fi.1 - n₀)) : ℚ) : ℝ))
            atTop (𝓝 ((1 : ℚ) : ℝ)) :=
          (Rat.continuous_coe_real.tendsto (1 : ℚ)).comp hq
        rw [Rat.cast_one] at hcast
        refine hcast.congr (fun N => ?_)
        simp only [rhoInf]
        push_cast
        ring
      have hgt : Tendsto (fun t => rhoInf n₀ (s t).1 (Fi.1 - n₀)) atTop (𝓝 1) :=
        hρ.comp hsize_atTop
      have := (hgt.const_sub (1 : ℝ))
      simp only [sub_self] at this
      have hδpos : (0 : ℝ) < ε / 2 := by positivity
      exact this.eventually (eventually_lt_nhds hδpos)
    have hcomb := ((eventually_all_finset Fs).mpr (fun Fi _ => hev Fi)).and
      ((eventually_all_finset Fs).mpr (fun Fi _ => hev2 Fi))
    obtain ⟨t, ht1, ht2⟩ := hcomb.exists
    exact ⟨t, fun Fi hFi => ht1 Fi hFi, fun Fi hFi => ht2 Fi hFi⟩
  -- The `t`-th flag's underlying graph is in the class and contains a σ-copy.
  set G_t : LabeledGraph σ (Fin (s t).1) := (s t).2.out with hG_t
  have hG_t_quot : (⟦G_t⟧ : Flag σ (Fin (s t).1)) = (s t).2 := Quotient.out_eq _
  set Γ : SimpleGraph (Fin (s t).1) := G_t.graph with hΓ
  set θ : σ ↪g Γ := G_t.type_embed with hθ
  have hn_pos : 0 < (s t).1 := by
    have := fin_card_le_of_embedding θ
    omega
  have hΓmem : hc.Mem Γ := by
    apply hc.mem_of_forbiddenFree G_t
    intro F hF
    rw [hG_t_quot]
    exact hff t F hF
  -- Identify the `t`-th flag with the base flag of `θ`.
  have hbase_eq : (s t).2 = (⟦baseLabeledGraph θ⟧ : Flag σ (Fin (s t).1)) := by
    rw [← hG_t_quot]; rfl
  -- Obtain the within-class blow-up family from the closure hypothesis.
  choose Wf hWf using (fun M => hclosure Γ hΓmem M)
  -- Blow-up base limit `φ₀`.
  obtain ⟨ϕ, φ₀, hϕ, hconvφ⟩ := exists_blowup_limit_sub hn_pos Γ Wf
  have hφ0Q : posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0 :=
    blowup_limit_mem_Q0_sub hc hWf hconvφ
  have hφ0σ : φ₀ ⟨σ⟩₀ > 0 := blowup_limit_type_pos_sub hn_pos θ hconvφ
  -- The blow-up flag sequence `sB` and its rooting measures `P`.
  set sB : FlagSeq ∅ₜ := blowupFlagSeq_sub Γ Wf ∘ ϕ with hsB
  let hsBpos : ∀ M, flagDensity₁ σ.toEmptyTypeFlag (sB M).2 > 0 :=
    fun M => blowupFlagSeq_sub_type_pos hn_pos θ Wf (ϕ M)
  set P : ℕ → ProbabilityMeasure (FlagDensitySpace σ) := sB.toProbMeasureSeq hsBpos with hP
  -- Weak convergence of the rooting measures to `rootingMeasureFDS φ₀ hφ0σ`.
  have hPweak : Tendsto P atTop (𝓝 (rootingMeasureFDS φ₀ hφ0σ)) :=
    tendsto_rootingMeasure_extend hφ0σ sB hsBpos hconvφ
  -- The closed cylinder, centered at the base profile (= the `t`-th flag's densities).
  set base : FinFlag σ → ℝ := fun Fi =>
    (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin (s t).1)) : ℝ) with hbase
  set C : Set (FlagDensitySpace σ) := cyl Fs base (ε / 2) with hC
  have hCclosed : IsClosed C := isClosed_cyl Fs base (ε / 2)
  -- The planted-mass cylinder lower bound: eventually `(blowup measure)(C) ≥ c > 0`.
  obtain ⟨c, hc_pos, hc_event⟩ := planted_cylinder_mass_sub hn_pos hn₀ θ Wf Fs (δ := ε / 2)
    (by positivity) ht_acc
  -- Pass the event to the subsequence `ϕ` (which tends to `atTop`).
  have hc_event_sub : ∀ᶠ M in atTop,
      c ≤ (((blowupFlagSeq_sub Γ Wf (ϕ M)).toProbMeasure
            (blowupFlagSeq_sub_type_pos hn_pos θ Wf (ϕ M))
          : Measure (FlagDensitySpace σ)) (cyl Fs
            (fun Fi => (flagDensity₁ Fi.2 (⟦baseLabeledGraph θ⟧ : Flag σ (Fin (s t).1)) : ℝ))
            (ε / 2))).toReal :=
    hϕ.tendsto_atTop.eventually hc_event
  -- Portmanteau: `limsup (P M)(C) ≤ rootingMeasureFDS(C)`.
  have hlimsup : (atTop.limsup fun M => (P M : Measure (FlagDensitySpace σ)) C)
      ≤ (rootingMeasureFDS φ₀ hφ0σ : Measure (FlagDensitySpace σ)) C :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hPweak hCclosed
  -- Eventually `(P M)(C) ≥ ENNReal.ofReal c`, hence the limsup is `≥ ENNReal.ofReal c`.
  have hc_event' : ∀ᶠ M in atTop, ENNReal.ofReal c ≤ (P M : Measure (FlagDensitySpace σ)) C := by
    filter_upwards [hc_event_sub] with M hM
    -- `P M = (blowupFlagSeq_sub Γ Wf (ϕ M)).toProbMeasure (hsBpos M)`, definitionally.
    show ENNReal.ofReal c ≤ ((blowupFlagSeq_sub Γ Wf (ϕ M)).toProbMeasure (hsBpos M)
        : Measure (FlagDensitySpace σ)) C
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hM
  have hge : ENNReal.ofReal c ≤ atTop.limsup fun M => (P M : Measure (FlagDensitySpace σ)) C :=
    le_limsup_of_frequently_le (hc_event'.frequently) (by isBoundedDefault)
  have hroot_ge : ENNReal.ofReal c ≤ (rootingMeasureFDS φ₀ hφ0σ : Measure (FlagDensitySpace σ)) C :=
    le_trans hge hlimsup
  -- `rootingMeasureFDS = (ℙ[φ₀]).map Subtype.val`, so `rootingMeasureFDS(C) = ℙ[φ₀](val⁻¹' C)`.
  have hmap : (rootingMeasureFDS φ₀ hφ0σ : Measure (FlagDensitySpace σ)) C
      = (ℙ[φ₀] : Measure (PositiveHomSpace σ)) (Subtype.val ⁻¹' C) := by
    rw [rootingMeasureFDS, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_subtype_coe) hCclosed.measurableSet]
  -- The preimage cylinder in `PositiveHomSpace σ`.
  set CP : Set (PositiveHomSpace σ) := Subtype.val ⁻¹' C with hCP
  have hCPclosed : IsClosed CP := hCclosed.preimage continuous_subtype_val
  have hCP_pos : (0 : ENNReal) < (ℙ[φ₀] : Measure (PositiveHomSpace σ)) CP := by
    rw [hmap] at hroot_ge
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc_pos) hroot_ge
  -- The support of `ℙ[φ₀]` meets `CP`, so we get `χ ∈ support ∩ CP`.
  obtain ⟨χ, hχsupp, hχCP⟩ :
      ∃ χ, χ ∈ (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support ∧ χ ∈ CP := by
    by_contra hcon
    push_neg at hcon
    have hsub : CP ⊆ (ℙ[φ₀] : Measure (PositiveHomSpace σ)).supportᶜ := by
      intro χ hχ
      exact fun hχs => hcon χ hχs hχ
    have hzero : (ℙ[φ₀] : Measure (PositiveHomSpace σ)) CP = 0 :=
      measure_mono_null hsub (Measure.measure_compl_support)
    rw [hzero] at hCP_pos
    exact lt_irrefl 0 hCP_pos
  -- `χ ∈ A` (the support-union) and `|χ.val Fi − ψ.val Fi| < ε` on `Fs`.
  refine ⟨χ, ?_, ?_⟩
  · -- `χ` lies in the support of an admissible random extension.
    exact Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ0Q,
      Set.mem_iUnion.mpr ⟨hφ0σ, hχsupp⟩⟩⟩
  · -- Triangle inequality.
    intro Fi hFi
    have hχbase : |χ.val Fi - base Fi| ≤ ε / 2 := hχCP Fi hFi
    have hbase_t : base Fi = (flagDensity₁ Fi.2 (s t).2 : ℝ) := by
      rw [hbase, hbase_eq]
    have ht := ht_dens Fi hFi
    calc |χ.val Fi - ψ.val Fi|
        ≤ |χ.val Fi - base Fi| + |base Fi - ψ.val Fi| := abs_sub_le _ _ _
      _ ≤ ε / 2 + |base Fi - ψ.val Fi| := by linarith [hχbase]
      _ = ε / 2 + |flagDensity₁ Fi.2 (s t).2 - ψ.val Fi| := by rw [hbase_t]
      _ < ε / 2 + η := by linarith [ht]
      _ < ε := by rw [hη]; linarith

end FlagAlgebras.MetaTheory
