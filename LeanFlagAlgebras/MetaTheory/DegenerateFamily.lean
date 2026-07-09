import LeanFlagAlgebras.MetaTheory.C4Free

/-! # A general subquadratic edge-degeneracy criterion (paper §9.1, `cor:degenerate-family`)

`cor:degenerate-family` lists four hereditary classes that are edge-degenerate — hence not
root-plantable at the one-vertex type (`thm:degenerate-obstruction`, since each contains all stars):

  (i)   `K_{s,t}`-subgraph-free graphs (Kővári–Sós–Turán, `ex(n,K_{s,t}) = O(n^{2−1/s})`);
  (ii)  `C_{2k}`-subgraph-free graphs (Bondy–Simonovits, `ex(n,C_{2k}) = O(n^{1+1/k})`);
  (iii) forests / bounded-average-degree classes (`O(n)` edges);
  (iv)  planar graphs (`≤ 3n − 6` edges).

All four share one mechanism: a **subquadratic edge bound** `e(G) ≤ f(|G|)` with `f(N)/N² → 0`.  This
file isolates that mechanism as `edgeDegenerate_of_subquadratic`; the four families are then
instances via their extremal bounds.  Only the `C₄ = K_{2,2}` case has its bound proved from scratch
here (`c4FreeClass_edgeDegenerate` / `c4free_card_edges_sq_le`); the deeper extremal estimates for
(i) with `s ≥ 3`, (ii) and (iv) are classical results outside the current Mathlib, so those
instances are stated at the level of the criterion rather than re-proved.
-/

open Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-- The factor `N² / C(N,2) = 2·N/(N-1) → 2` as `N → ∞`.  Used to turn `f N / N² → 0` into
`f N / C(N,2) → 0`. -/
private lemma choose_two_ratio_tendsto :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 / (N.choose 2 : ℝ)) atTop (𝓝 2) := by
  have h1 : Tendsto (fun N : ℝ => N / (N - 1)) atTop (𝓝 1) := by
    have hcongr : (fun N : ℝ => N / (N - 1))
        =ᶠ[atTop] (fun N : ℝ => (1 - N⁻¹)⁻¹) := by
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hN0 : N ≠ 0 := by positivity
      have hN1 : N - 1 ≠ 0 := by intro h; apply hN.ne'; linarith
      field_simp
    rw [tendsto_congr' hcongr]
    have hden : Tendsto (fun N : ℝ => 1 - N⁻¹) atTop (𝓝 (1 - 0)) :=
      Tendsto.const_sub _ tendsto_inv_atTop_zero
    have hres : Tendsto (fun N : ℝ => (1 - N⁻¹)⁻¹) atTop (𝓝 (1 - 0)⁻¹) :=
      hden.inv₀ (by norm_num)
    simpa using hres
  have hsqueeze : Tendsto (fun N : ℝ => 2 * (N / (N - 1))) atTop (𝓝 (2 * 1)) :=
    h1.const_mul 2
  rw [mul_one] at hsqueeze
  have hcomp : Tendsto (fun N : ℕ => 2 * ((N : ℝ) / ((N : ℝ) - 1))) atTop (𝓝 2) :=
    hsqueeze.comp tendsto_natCast_atTop_atTop
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hchoose : (N.choose 2 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := Nat.cast_choose_two (K := ℝ) N
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hN1ne : (N : ℝ) - 1 ≠ 0 := by intro h; apply hN1.ne'; linarith
  rw [hchoose]
  field_simp

/-- **General edge-degeneracy criterion** (the principle behind `cor:degenerate-family`).  A
hereditary class whose `N`-vertex members satisfy a subquadratic edge bound `e(G) ≤ f N` with
`f N / N² → 0` is edge-degenerate.  (Mirror of `c4FreeClass_edgeDegenerate`, with the `C₄` counting
bound replaced by the abstract bound: the unlabelled-edge density `e(G)/C(N,2) ≤ f N / C(N,2) → 0`
by a direct squeeze.) -/
theorem edgeDegenerate_of_subquadratic (hc : HeredClass) (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / (N : ℝ) ^ 2) atTop (𝓝 0))
    (hbound : ∀ {N : ℕ} (G : SimpleGraph (Fin N)), hc.Mem G →
      (G.edgeFinset.card : ℝ) ≤ f N) :
    EdgeDegenerate hc := by
  intro φ₀ hφ₀
  -- Reduce `φ₀ ρ` to the unlabelled-edge density via `downward_basisVector`.
  have hedgeunlabel : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, unlabelledEdgeFlag⟩ := rfl
  have hρ : φ₀ ρ
      = (downwardNormalizingFactor edgeFF.2 : ℝ) * φ₀.coe ⟨2, unlabelledEdgeFlag⟩ := by
    show φ₀ (downward e) = _
    rw [e, downward_basisVector, PositiveHom.map_smul, hedgeunlabel, ← PositiveHom.coe_flag]
  -- It suffices to show the unlabelled-edge density coefficient is zero.
  suffices h : φ₀.coe ⟨2, unlabelledEdgeFlag⟩ = 0 by rw [hρ, h, mul_zero]
  -- The forbidden-flag hypothesis from membership in `Q₀`.
  set forb0 := (hc.constraintOf vtype).forb0 with hforb0def
  have hforb : ∀ F : FinFlag ∅ₜ, forb0 F → φ₀.coe F = 0 := by
    intro F hF
    have hmem := (mem_Qσ_iff forb0 (posHomPoint φ₀)).mp hφ₀ F hF
    rw [posHomPoint_val_apply] at hmem
    rw [PositiveHom.coe_flag]
    exact hmem
  -- Constrained flag sequence representing `φ₀`.
  obtain ⟨s, hconv, hff⟩ := exists_constrained_flagSeq_limit φ₀ forb0 hforb
  rw [flagSeq_convergesTo_iff] at hconv
  obtain ⟨hinc, hconvF⟩ := hconv
  have hlim := hconvF ⟨2, unlabelledEdgeFlag⟩
  set L : ℝ := φ₀.coe ⟨2, unlabelledEdgeFlag⟩ with hLdef
  -- Each component's unlabelled-edge density is `e(G_t)/C(N_t,2)`.
  have hdensity : ∀ t, flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩
      = ((((s t).2.out.graph).edgeFinset.card : ℚ) / ((s t).1).choose 2 : ℝ) := by
    intro t
    show (flagDensity₁ unlabelledEdgeFlag (s t).2 : ℝ) = _
    have hgf : (s t).2 = graphFlag ((s t).2.out.graph) := by
      conv_lhs => rw [← Quotient.out_eq (s t).2]
      show (⟦(s t).2.out⟧ : Flag ∅ₜ _) = ⟦_⟧
      apply Quotient.sound
      refine ⟨{ graph_iso := SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
      funext z; exact Fin.elim0 z
    have hval : flagDensity₁ unlabelledEdgeFlag (s t).2
        = (((s t).2.out.graph).edgeFinset.card : ℚ) / ((s t).1).choose 2 := by
      conv_lhs => rw [hgf]
      exact flagDensity_unlabelledEdge_eq ((s t).2.out.graph)
    rw [hval]; push_cast; ring
  -- Each representing graph is in the class.
  have hmem : ∀ t, hc.Mem ((s t).2.out.graph) := by
    intro t
    apply HeredClass.mem_of_forbiddenFree hc ((s t).2.out)
    intro F hForb
    have hForb0 : forb0 F := by
      show ¬ hc.underlyingMem F.2
      have hfb : ¬ hc.underlyingMem (unlabel F.2) := hForb
      rwa [unlabel_emptyType] at hfb
    have hzero := hff t F hForb0
    rwa [← Quotient.out_eq (s t).2] at hzero
  -- The density `d_t = e(G_t)/C(N_t,2)` is nonneg and bounded by `f N_t / C(N_t,2)`.
  have hdnn : ∀ t, (0 : ℝ) ≤ flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩ := by
    intro t
    rw [hdensity t]
    have hge : (0 : ℚ) ≤ (((s t).2.out.graph).edgeFinset.card : ℚ) / ((s t).1).choose 2 := by
      positivity
    exact_mod_cast hge
  have hdle : ∀ t, flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩
      ≤ f ((s t).1) / (((s t).1).choose 2 : ℝ) := by
    intro t
    rw [hdensity t]
    push_cast
    have hnum : ((((s t).2.out.graph).edgeFinset.card : ℝ)) ≤ f ((s t).1) :=
      hbound _ (hmem t)
    have hden0 : (0 : ℝ) ≤ (((s t).1).choose 2 : ℝ) := by positivity
    exact div_le_div_of_nonneg_right hnum hden0
  -- The upper bound `f N_t / C(N_t,2) → 0`, via `f N / N² → 0` and `N² / C(N,2) → 2`.
  have hub_N : Tendsto (fun N : ℕ => f N / (N.choose 2 : ℝ)) atTop (𝓝 0) := by
    have hprod : Tendsto
        (fun N : ℕ => (f N / (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 / (N.choose 2 : ℝ)))
        atTop (𝓝 (0 * 2)) :=
      hf.mul choose_two_ratio_tendsto
    rw [zero_mul] at hprod
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hchoose : (N.choose 2 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := Nat.cast_choose_two (K := ℝ) N
    have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have hc2pos : (0 : ℝ) < (N.choose 2 : ℝ) := by rw [hchoose]; positivity
    field_simp
  have hNtop : Tendsto (fun t => ((s t).1 : ℕ)) atTop atTop :=
    hinc.tendsto_atTop
  have hub : Tendsto (fun t => f ((s t).1) / ((((s t).1).choose 2) : ℝ))
      atTop (𝓝 0) := hub_N.comp hNtop
  -- Squeeze the linear density between `0` and the upper bound `→ 0`.
  have hd0 : Tendsto (fun t => flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩)
      atTop (𝓝 0) :=
    squeeze_zero hdnn hdle hub
  -- Uniqueness of limits forces `L = 0`.
  exact tendsto_nhds_unique hlim hd0

end FlagAlgebras.MetaTheory
