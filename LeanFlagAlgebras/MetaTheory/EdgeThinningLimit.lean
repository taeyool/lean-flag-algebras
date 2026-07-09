import LeanFlagAlgebras.MetaTheory.EdgeThinning
import LeanFlagAlgebras.MetaTheory.ConstrainedRep

/-! # The edge-thinned constrained limit `φ₀^λ` (paper §9.4)

From a constrained unlabelled limit `φ₀ ∈ Q₀` of positive `σ`-density and a thinning parameter
`λ ∈ (0,1]`, we build the **edge-thinned limit** `φ₀^λ ∈ Q₀`:

* take a representing sequence `G_n → φ₀` of in-class graphs (`exists_constrained_flagSeq_limit`);
* for each `n`, the deterministic realization (`exists_thinned_realization`) gives an in-class
  spanning subgraph `H_n ≤ G_n` whose densities track the edge-thinning expectations within `1/n`
  (over flags of size `≤ n`);
* a convergent subsequence of `H_n` has a limit `φ₀^λ`, which lies in `Q₀`
  (the `H_n` are in-class, so forbidden-free) and inherits two bounds:
  the σ-density lower bound `φ₀^λ⟨σ⟩₀ ≥ λ^{e(σ)}·φ₀⟨σ⟩₀` (from `thinExpectDensity_type_ge`), keeping it
  positive, and the per-flag upper bound `φ₀^λ(M) ≤ C·λ^{e(M)}` (from `thinExpectDensity_le_pow`),
  which drives every "new-edge" flag to `0` as `λ → 0`.

These two bounds are exactly what `NoInteriorThinning` needs to push the random extensions of `φ₀^λ`
to the deterministic `{0,1}`-valued boolean point as `λ → 0`.
-/

open Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ}

/-- `graphFlag` of the underlying graph of the chosen representative of an unlabelled flag returns the
flag itself. -/
private lemma graphFlag_out_graph {N : ℕ} (X : Flag ∅ₜ (Fin N)) :
    graphFlag (X.out.graph) = X := by
  conv_rhs => rw [← Quotient.out_eq X]
  apply Quotient.sound
  refine ⟨{ graph_iso := SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
  funext z; exact Fin.elim0 z

/-- A forbidden-free unlabelled flag (zero density of every `forb0`-forbidden flag) has its underlying
graph in the class. -/
private theorem mem_out_graph_of_forb0 (hc : HeredClass) (σ : FlagType (Fin n₀))
    {N : ℕ} (X : Flag ∅ₜ (Fin N))
    (hff : ∀ D : FinFlag ∅ₜ, (hc.constraintOf σ).forb0 D → flagDensity₁ D.2 X = 0) :
    hc.Mem X.out.graph := by
  apply hc.mem_of_forbiddenFree X.out
  intro F hF
  rw [Quotient.out_eq]
  apply hff F
  have hF' : ¬ hc.underlyingMem (unlabel F.2) := hF
  rw [unlabel_emptyType] at hF'
  exact hF'

/-- **The base limit lies in `Q₀`.**  If every term of a convergent flag sequence `sH` is
forbidden-free, the limit `φ₀` kills every forbidden flag, so `posHomPoint φ₀ ∈ Qσ T.forb0`. -/
private theorem flagSeqLimit_mem_Q0 {σ : FlagType (Fin n₀)} (T : Constraint σ)
    {sH : FlagSeq ∅ₜ} {φ₀ : PositiveHom ∅ₜ} (hconv : ConvergesTo sH φ₀.coe)
    (hff : ∀ k, ∀ D : FinFlag ∅ₜ, T.forb0 D → flagDensity₁ D.2 (sH k).2 = 0) :
    posHomPoint φ₀ ∈ Qσ T.forb0 := by
  rw [mem_Qσ_iff]
  intro D hD
  rw [posHomPoint_val_apply, ← φ₀.coe_flag D]
  have hlim : Tendsto (fun k => flagDensitySeq sH k D) atTop (𝓝 (φ₀.coe D)) :=
    (flagSeq_convergesTo_iff.mp hconv).2 D
  have hzero : ∀ k, flagDensitySeq sH k D = 0 := by
    intro k
    show (flagDensity₁ D.2 (sH k).2 : ℝ) = 0
    rw [hff k D hD, Rat.cast_zero]
  rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-- One edge-thinning realization: a host graph `H` in the class whose induced densities of flags of
size `≤ k` track the edge-thinning expectations of the base graph `G` within `1/(k+1)`. -/
private structure ThinData (hc : HeredClass) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (k : ℕ)
    {Nh : ℕ} (G : SimpleGraph (Fin Nh)) where
  H : SimpleGraph (Fin Nh)
  memH : hc.Mem H
  close : ∀ M : FinFlag ∅ₜ, M.1 ≤ k →
    |(flagDensity₁ M.2 (graphFlag H) : ℝ) - thinExpectDensity lam h0 h1 G M| ≤ 1 / ((k : ℝ) + 1)

/-- **The edge-thinned constrained limit** (`§9.4`).  Given a constrained unlabelled limit
`φ₀ ∈ Q₀` with positive `σ`-density and `λ ∈ (0,1]` for an edge-deletion-closed hereditary class,
there is a constrained unlabelled limit `φlam ∈ Q₀` with:

* `φlam ⟨σ⟩₀ ≥ λ^{e(σ)}·φ₀⟨σ⟩₀` (still positive, so `σ`-rooting of `φlam` is admissible);
* `φlam(M) ≤ C(C(|M|,2), e(M))·λ^{e(M)}` for every graph flag `M` (so flags with `≥ 1` edge vanish as
  `λ → 0`).
-/
theorem exists_thinned_limit (hc : HeredClass) (hedc : EdgeDeletionClosed hc)
    (σ : FlagType (Fin n₀))
    (φ₀ : PositiveHom ∅ₜ) (hφ₀Q : posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∃ φlam : PositiveHom ∅ₜ,
      posHomPoint φlam ∈ Qσ (hc.constraintOf σ).forb0 ∧
      lam ^ (σ.edgeFinset.card) * φ₀ ⟨σ⟩₀ ≤ φlam ⟨σ⟩₀ ∧
      ∀ M : FinFlag ∅ₜ,
        φlam.coe M
          ≤ ((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
              * lam ^ (M.2.out.graph.edgeFinset.card) := by
  classical
  -- Step 1: forbidden-vanishing of `φ₀` from membership in `Q₀`.
  have hforb0 : ∀ D : FinFlag ∅ₜ, (hc.constraintOf σ).forb0 D → φ₀.coe D = 0 := by
    intro D hD
    have hmem := (mem_Qσ_iff (hc.constraintOf σ).forb0 (posHomPoint φ₀)).mp hφ₀Q D hD
    rw [posHomPoint_val_apply] at hmem
    rw [PositiveHom.coe_flag]
    exact hmem
  -- Step 1b: a constrained representing sequence `s → φ₀` of forbidden-free flags.
  obtain ⟨s, hconv_s, hff⟩ :=
    exists_constrained_flagSeq_limit φ₀ (hc.constraintOf σ).forb0 hforb0
  have hs_strictMono : StrictMono (fun n => (s n).1) := hconv_s.1
  -- Step 2: realization thresholds `N₀ k` for resolution `k`, tolerance `1/(k+1)`.
  have hreal : ∀ k : ℕ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ G : SimpleGraph (Fin N), hc.Mem G →
      ∃ H : SimpleGraph (Fin N), H ≤ G ∧ hc.Mem H ∧ ∀ M : FinFlag ∅ₜ, M.1 ≤ k →
        |(flagDensity₁ M.2 (graphFlag H) : ℝ) - thinExpectDensity lam h0.le h1 G M|
          ≤ 1 / ((k : ℝ) + 1) :=
    fun k => exists_thinned_realization hc hedc lam h0 h1 k (1 / ((k : ℝ) + 1)) (by positivity)
  choose N₀ hN₀ using hreal
  -- Step 2b: a strictly increasing index `sN k ≥ N₀ k` into `s`.
  set sN : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup N₀ + k with hsN
  have hsN_ge : ∀ k, N₀ k ≤ sN k := by
    intro k
    have h := Finset.le_sup (f := N₀) (Finset.self_mem_range_succ k)
    show N₀ k ≤ (Finset.range (k + 1)).sup N₀ + k
    omega
  have hsN_mono : StrictMono sN := by
    apply strictMono_nat_of_lt_succ
    intro k
    show (Finset.range (k + 1)).sup N₀ + k < (Finset.range (k + 1 + 1)).sup N₀ + (k + 1)
    have hmono : (Finset.range (k + 1)).sup N₀ ≤ (Finset.range (k + 1 + 1)).sup N₀ :=
      Finset.sup_mono (Finset.range_subset_range.mpr (Nat.le_succ _))
    omega
  -- Step 2c: per-index realization data over the base graph `(s (sN k)).2.out.graph`.
  have hthindata_ne : ∀ k, Nonempty (ThinData hc lam h0.le h1 k ((s (sN k)).2.out.graph)) := by
    intro k
    have hmemG : hc.Mem ((s (sN k)).2.out.graph) :=
      mem_out_graph_of_forb0 hc σ (s (sN k)).2 (fun D hD => hff (sN k) D hD)
    obtain ⟨H, _, hH_mem, hH_close⟩ :=
      hN₀ k ((s (sN k)).1) (le_trans (hsN_ge k) (hs_strictMono.id_le (sN k)))
        ((s (sN k)).2.out.graph) hmemG
    exact ⟨H, hH_mem, hH_close⟩
  set thindata : ∀ k, ThinData hc lam h0.le h1 k ((s (sN k)).2.out.graph) :=
    fun k => Classical.choice (hthindata_ne k) with hthindata
  -- Step 3: the increasing flag sequence of host graphs and a convergent subsequence.
  set sH : FlagSeq ∅ₜ := fun k => ⟨(s (sN k)).1, graphFlag (thindata k).H⟩ with hsHdef
  have hsH_inc : Increases sH := hs_strictMono.comp hsN_mono
  obtain ⟨a, ϕ, hϕ_mono, hconv_a⟩ := increasing_flagSeq_contain_convergent_subseq sH hsH_inc
  obtain ⟨φlam, hφlam⟩ := flagSeq_limit_mem_positiveHom (sH ∘ ϕ) hconv_a
  set sHϕ : FlagSeq ∅ₜ := sH ∘ ϕ with hsHϕ
  have hconv_sHϕ : ConvergesTo sHϕ φlam.coe := hφlam ▸ hconv_a
  -- Common limit facts.
  have hϕ_atTop : Tendsto ϕ atTop atTop := hϕ_mono.tendsto_atTop
  have hsubseq : Tendsto (fun k => sN (ϕ k)) atTop atTop := hsN_mono.tendsto_atTop.comp hϕ_atTop
  have hrecip : Tendsto (fun k => (1 : ℝ) / ((ϕ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hϕ_atTop
  -- The two `⟨σ⟩₀`-as-density rewrites.
  have hφ₀val : φ₀ ⟨σ⟩₀ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩ := by
    show φ₀ ⟦basisVector ⟨n₀, σ.toEmptyTypeFlag⟩⟧ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩
    rw [φ₀.coe_flag]
  have hφlamval : φlam ⟨σ⟩₀ = φlam.coe ⟨n₀, σ.toEmptyTypeFlag⟩ := by
    show φlam ⟦basisVector ⟨n₀, σ.toEmptyTypeFlag⟩⟧ = φlam.coe ⟨n₀, σ.toEmptyTypeFlag⟩
    rw [φlam.coe_flag]
  refine ⟨φlam, ?_, ?_, ?_⟩
  · -- Step 4: the limit lies in `Q₀` (each host graph is in-class, hence forbidden-free).
    apply flagSeqLimit_mem_Q0 (hc.constraintOf σ) hconv_sHϕ
    intro k D hD
    show flagDensity₁ D.2 (graphFlag (thindata (ϕ k)).H) = 0
    exact hc.forbiddenFree_of_mem (thindata (ϕ k)).H (thindata (ϕ k)).memH D hD
  · -- Step 5: the `σ`-density lower bound.
    rw [hφ₀val, hφlamval]
    have hs_F₀ : Tendsto
        (fun n => (flagDensity₁ (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2 (s n).2 : ℝ)) atTop
        (𝓝 (φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩)) :=
      (flagSeq_convergesTo_iff.mp hconv_s).2 ⟨n₀, σ.toEmptyTypeFlag⟩
    have hs_F₀_sub : Tendsto
        (fun k => (flagDensity₁ (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2 (s (sN (ϕ k))).2 : ℝ))
        atTop (𝓝 (φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩)) := hs_F₀.comp hsubseq
    have htype_mul := hs_F₀_sub.const_mul (lam ^ σ.edgeFinset.card)
    have hf_conv : Tendsto
        (fun k => lam ^ σ.edgeFinset.card
            * (flagDensity₁ (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2 (s (sN (ϕ k))).2 : ℝ)
            - (1 : ℝ) / ((ϕ k : ℝ) + 1)) atTop
        (𝓝 (lam ^ σ.edgeFinset.card * φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩)) := by
      have h := htype_mul.sub hrecip
      simpa only [sub_zero] using h
    have hg_conv : Tendsto
        (fun k => (flagDensity₁ (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2
            (graphFlag (thindata (ϕ k)).H) : ℝ)) atTop
        (𝓝 (φlam.coe ⟨n₀, σ.toEmptyTypeFlag⟩)) :=
      (flagSeq_convergesTo_iff.mp hconv_sHϕ).2 ⟨n₀, σ.toEmptyTypeFlag⟩
    refine le_of_tendsto_of_tendsto hf_conv hg_conv ?_
    filter_upwards [hϕ_atTop.eventually_ge_atTop n₀] with k hk
    have hclose := (thindata (ϕ k)).close ⟨n₀, σ.toEmptyTypeFlag⟩ hk
    rw [abs_le] at hclose
    have htype := thinExpectDensity_type_ge σ lam h0.le h1 ((s (sN (ϕ k))).2.out.graph)
    rw [graphFlag_out_graph (s (sN (ϕ k))).2] at htype
    linarith [hclose.1, htype]
  · -- Step 6: the per-flag upper bound.
    intro M
    have hg_convM : Tendsto
        (fun k => (flagDensity₁ M.2 (graphFlag (thindata (ϕ k)).H) : ℝ)) atTop
        (𝓝 (φlam.coe M)) :=
      (flagSeq_convergesTo_iff.mp hconv_sHϕ).2 M
    have hh_conv : Tendsto
        (fun k => ((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
            * lam ^ (M.2.out.graph.edgeFinset.card) + (1 : ℝ) / ((ϕ k : ℝ) + 1)) atTop
        (𝓝 (((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
            * lam ^ (M.2.out.graph.edgeFinset.card))) := by
      have hconst : Tendsto (fun _ : ℕ => ((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
          * lam ^ (M.2.out.graph.edgeFinset.card)) atTop
          (𝓝 (((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
            * lam ^ (M.2.out.graph.edgeFinset.card))) := tendsto_const_nhds
      simpa only [add_zero] using hconst.add hrecip
    refine le_of_tendsto_of_tendsto hg_convM hh_conv ?_
    filter_upwards [hϕ_atTop.eventually_ge_atTop M.1] with k hk
    have hclose := (thindata (ϕ k)).close M hk
    rw [abs_le] at hclose
    have hle := thinExpectDensity_le_pow lam h0.le h1 ((s (sN (ϕ k))).2.out.graph) M
    linarith [hclose.2, hle]

end FlagAlgebras.MetaTheory
