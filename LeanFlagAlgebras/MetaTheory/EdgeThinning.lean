import LeanFlagAlgebras.MetaTheory.NoInterior
import LeanFlagAlgebras.MetaTheory.LabeledCount
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

/-! # Random edge-thinning of a finite graph (paper §9.4, probabilistic core)

This module is the probabilistic engine behind `thm:no-interior` (`NoInterior.lean`): the
edge-thinning measure on a finite graph, the expected induced densities of flags in the thinned
graph, and a deterministic realization (second-moment method) producing, for large `N`, an in-class
spanning subgraph whose induced densities all sit near those expectations.

* `ThinCoins N` / `thinMeasure` — one independent Bernoulli(`λ`) coin per potential edge.
* `thinGraph G ω` — keep edge `{a,b}` iff it is present in `G` *and* its coin is `true`; this is a
  spanning subgraph (`thinGraph_le`), hence in-class for any edge-deletion-closed class
  (`thinGraph_mem`).
* `thinExpectDensity` — the expected induced density of a flag, with `[0,1]` bounds, a first-moment
  upper bound (`thinExpectDensity_le_pow`) and a `σ`-type lower bound (`thinExpectDensity_type_ge`).
* `exists_thinned_realization` — the second-moment realization.
-/

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal NNReal

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The coin space and the Bernoulli product measure -/

/-- Coin space: one Bernoulli(`λ`) coin per unordered pair (potential edge). -/
abbrev ThinCoins (N : ℕ) : Type := Sym2 (Fin N) → Bool

/-- The `ℝ≥0` clamp of `λ` used by `PMF.bernoulli` (valid once `0 ≤ λ`). -/
private noncomputable def lamNN (lam : ℝ) : ℝ≥0 := lam.toNNReal

private lemma lamNN_le_one {lam : ℝ} (h1 : lam ≤ 1) : lamNN lam ≤ 1 := by
  rw [lamNN, Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
  exact h1

/-- Bernoulli(`λ`) product measure on the coins (`λ` clamped to `[0,1]` via the PMF). -/
noncomputable def thinMeasure (N : ℕ) (lam : ℝ) (_h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Measure (ThinCoins N) :=
  Measure.pi (fun _ : Sym2 (Fin N) => (PMF.bernoulli (lamNN lam) (lamNN_le_one h1)).toMeasure)

instance thinMeasure_isProbabilityMeasure (N : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    IsProbabilityMeasure (thinMeasure N lam h0 h1) := by
  unfold thinMeasure
  infer_instance

/-! ## The thinned graph -/

/-- The thinned graph: keep edge `{a,b}` iff it was present in `G` *and* its coin is `true`. -/
def thinGraph {N : ℕ} (G : SimpleGraph (Fin N)) (ω : ThinCoins N) : SimpleGraph (Fin N) where
  Adj a b := G.Adj a b ∧ ω s(a, b)
  symm := fun a b ⟨hab, hc⟩ => ⟨hab.symm, by rwa [Sym2.eq_swap]⟩
  loopless := fun a ⟨h, _⟩ => G.loopless a h

@[simp] lemma thinGraph_adj {N : ℕ} (G : SimpleGraph (Fin N)) (ω : ThinCoins N) (a b : Fin N) :
    (thinGraph G ω).Adj a b ↔ G.Adj a b ∧ ω s(a, b) := Iff.rfl

/-- `thinGraph G ω ≤ G`: the thinned graph is a spanning subgraph. -/
theorem thinGraph_le {N : ℕ} (G : SimpleGraph (Fin N)) (ω : ThinCoins N) : thinGraph G ω ≤ G :=
  fun _ _ h => h.1

/-! ## Expected induced density -/

/-- The expected induced density of flag `M` in the thinned graph. -/
noncomputable def thinExpectDensity (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) : ℝ :=
  ∫ ω, (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ) ∂(thinMeasure N lam h0 h1)

/-! ## Infrastructure: density as a subset-indicator average -/

/-- Canonical `∅ₜ`-labelled representative of a graph; `graphFlag G = ⟦graphFlagRep G⟧` by `rfl`. -/
private def graphFlagRep {N : ℕ} (G : SimpleGraph (Fin N)) : LabeledGraph ∅ₜ (Fin N) where
  graph := G
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj

/-- `S` induces (a copy of) `M` in `G'`: the labelled subgraph of `G'` induced on `S` is isomorphic
to the chosen representative `M.2.out`.  Matches the filter predicate of
`flagDensity₁_eq_subset_count_div`. -/
private def inducesAt (M : FinFlag ∅ₜ) {N : ℕ} (G' : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    Prop :=
  ∃ (h : (graphFlagRep G').type_verts ⊆ (↑S : Set (Fin N))),
    Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G') (↑S) h).coe ≃f M.2.out)

/-- The empty type embeds nowhere, so the root set is contained in any subset. -/
private lemma emptyType_verts_subset {N : ℕ} (G' : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    (graphFlagRep G').type_verts ⊆ (↑S : Set (Fin N)) := by
  intro x hx
  rw [LabeledGraph.mem_type_verts] at hx
  obtain ⟨t, _⟩ := hx
  exact t.elim0

/-- Flag density of `M` in `G'` as a normalized subset count of `inducesAt`. -/
private lemma density_eq_count {N : ℕ} (G' : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) :
    (flagDensity₁ M.2 (graphFlag G') : ℝ)
      = ((Finset.univ.filter (fun S : Finset (Fin N) => inducesAt M G' S)).card : ℝ)
          / (N.choose M.1 : ℝ) := by
  have h := flagDensity₁_eq_subset_count_div (M.2.out) (graphFlagRep G')
  rw [Quotient.out_eq] at h
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero] at h
  have hgf : graphFlag G' = (⟦graphFlagRep G'⟧ : Flag ∅ₜ (Fin N)) := rfl
  have hfe : (Finset.univ.filter (fun S : Finset (Fin N) =>
      ∃ (hh : (graphFlagRep G').type_verts ⊆ (↑S : Set (Fin N))),
        Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G') (↑S) hh).coe
          ≃f M.2.out)))
      = Finset.univ.filter (fun S : Finset (Fin N) => inducesAt M G' S) :=
    Finset.filter_congr (fun S _ => Iff.rfl)
  rw [hgf, h, hfe]
  push_cast
  ring

/-! ## The box (cylinder) measure of a coin event -/

/-- The event that every coin in a finite set `T` lands `true`. -/
private def coinBox {N : ℕ} (T : Finset (Sym2 (Fin N))) : Set (ThinCoins N) :=
  {ω | ∀ e ∈ T, ω e = true}

/-- The Bernoulli product measure of the coin box `{∀ e ∈ T, ω e = true}` is `λ^{|T|}`. -/
private lemma coinBox_measure_toReal (N : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (T : Finset (Sym2 (Fin N))) :
    (thinMeasure N lam h0 h1 (coinBox T)).toReal = lam ^ T.card := by
  have hset : coinBox T
      = Set.pi Set.univ (fun e : Sym2 (Fin N) => if e ∈ T then ({true} : Set Bool) else Set.univ) := by
    ext ω
    simp only [coinBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro hω e
      by_cases he : e ∈ T
      · simp [he, hω e he]
      · simp [he]
    · intro hω e he
      have := hω e
      simp only [he, if_true, Set.mem_singleton_iff] at this
      exact this
  rw [thinMeasure, hset, Measure.pi_pi]
  have hfac : ∀ e : Sym2 (Fin N),
      ((PMF.bernoulli (lamNN lam) (lamNN_le_one h1)).toMeasure)
          (if e ∈ T then ({true} : Set Bool) else Set.univ)
        = (if e ∈ T then (lamNN lam : ℝ≥0∞) else 1) := by
    intro e
    by_cases he : e ∈ T
    · simp only [he, if_true]
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true), PMF.bernoulli_apply]
      rfl
    · simp only [he, if_false]
      exact measure_univ
  rw [Finset.prod_congr rfl (fun e _ => hfac e), ← Finset.prod_filter, Finset.filter_univ_mem,
    Finset.prod_const, ENNReal.toReal_pow]
  have hco : ((lamNN lam : ℝ≥0∞)).toReal = lam := by
    rw [ENNReal.coe_toReal]
    simp only [lamNN]
    exact Real.coe_toNNReal lam h0
  rw [hco]

/-! ## The coin-restriction bridge -/

/-- Adjacency in the labelled subgraph of `G` induced on `S`: two vertices of `↑S` are adjacent iff
they are `G`-adjacent. -/
private lemma coe_induced_adj {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (h : (graphFlagRep G).type_verts ⊆ (↑S : Set (Fin N))) (a b : ↑(↑S : Set (Fin N))) :
    (LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G) (↑S) h).coe.graph.Adj a b
      ↔ G.Adj a.val b.val := by
  rw [LabeledSubgraph.coe_adj_iff]
  simp only [LabeledSubgraph.inducedLabeledSubgraph, SimpleGraph.Subgraph.induce, Subgraph.top_adj, graphFlagRep]
  constructor
  · exact fun hh => hh.2.2
  · exact fun hh => ⟨a.2, b.2, hh⟩

/-- If two graphs have the same adjacency relation on `S`, the same subsets of `S` induce `M`. -/
private lemma inducesAt_of_adj_agree {N : ℕ} {G₁ G₂ : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (hadj : ∀ a ∈ S, ∀ b ∈ S, (G₁.Adj a b ↔ G₂.Adj a b)) (M : FinFlag ∅ₜ)
    (h : inducesAt M G₂ S) : inducesAt M G₁ S := by
  obtain ⟨_, ⟨f₂⟩⟩ := h
  refine ⟨emptyType_verts_subset G₁ S, ⟨?_⟩⟩
  -- the identity-on-vertices iso between the two induced coe-graphs
  have e : (LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G₁) (↑S)
      (emptyType_verts_subset G₁ S)).coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G₂) (↑S)
        (emptyType_verts_subset G₂ S)).coe := by
    refine { graph_iso := ⟨Equiv.refl _, ?_⟩, type_preserve := ?_ }
    · intro a b
      show (LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G₂) (↑S)
            (emptyType_verts_subset G₂ S)).coe.graph.Adj a b
          ↔ (LabeledSubgraph.inducedLabeledSubgraph (graphFlagRep G₁) (↑S)
            (emptyType_verts_subset G₁ S)).coe.graph.Adj a b
      rw [coe_induced_adj G₂ S _ a b, coe_induced_adj G₁ S _ a b]
      exact (hadj a.val (Finset.mem_coe.mp a.2) b.val (Finset.mem_coe.mp b.2)).symm
    · funext t; exact t.elim0
  exact LabeledGraphIso.trans e f₂

/-! ## Edge count of the induced pattern -/

/-- A subset inducing `M` yields a graph iso between the induced subgraph and `M`'s representative. -/
private lemma exists_iso_of_inducesAt {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {M : FinFlag ∅ₜ} (h : inducesAt M G S) :
    Nonempty (((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe ≃g M.2.out.graph) := by
  obtain ⟨_, ⟨f⟩⟩ := h
  exact ⟨f.graph_iso⟩

/-- The chosen representative of the `σ`-type flag has underlying graph isomorphic to `σ`. -/
private lemma iso_out_sigma {n₀ : ℕ} (σ : FlagType (Fin n₀)) :
    Nonempty ((⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2.out.graph ≃g σ) := by
  have hq : (⟦(⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2.out⟧ : Flag ∅ₜ (Fin n₀))
      = ⟦graphFlagRep σ⟧ := by
    rw [Quotient.out_eq]; rfl
  obtain ⟨φ⟩ := Quotient.exact hq
  exact ⟨φ.graph_iso⟩

/-- `coinsWithin G S`: the `G`-edges with both endpoints in `S`, viewed as coins. -/
private noncomputable def coinsWithin {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    Finset (Sym2 (Fin N)) :=
  ((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe.edgeFinset.image (Sym2.map Subtype.val)

/-- If `S` induces `σ`, the number of `G`-edges inside `S` equals `e(σ)`. -/
private lemma coinsWithin_card_eq {n₀ : ℕ} (σ : FlagType (Fin n₀)) {N : ℕ}
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (h : inducesAt (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ) G S) :
    (coinsWithin G S).card = σ.edgeFinset.card := by
  rw [coinsWithin, Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  obtain ⟨g1⟩ := exists_iso_of_inducesAt h
  obtain ⟨g2⟩ := iso_out_sigma σ
  exact (show ((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe ≃g σ from g1.trans g2).card_edgeFinset_eq

/-- Membership characterization of `coinsWithin`. -/
private lemma mem_coinsWithin {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (e : Sym2 (Fin N)) :
    e ∈ coinsWithin G S ↔ ∃ a b, a ∈ S ∧ b ∈ S ∧ G.Adj a b ∧ e = s(a, b) := by
  rw [coinsWithin, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxe⟩
    rw [mem_edgeFinset] at hx
    induction x with
    | _ u v =>
      rw [mem_edgeSet, Subgraph.coe_adj] at hx
      obtain ⟨huS, hvS, hadj⟩ := hx
      refine ⟨u.val, v.val, Finset.mem_coe.mp huS, Finset.mem_coe.mp hvS, hadj, ?_⟩
      rw [← hxe, Sym2.map_pair_eq]
  · rintro ⟨a, b, ha, hb, hadj, rfl⟩
    have haS : a ∈ (↑S : Set (Fin N)) := Finset.mem_coe.mpr ha
    have hbS : b ∈ (↑S : Set (Fin N)) := Finset.mem_coe.mpr hb
    refine ⟨s(⟨a, haS⟩, ⟨b, hbS⟩), ?_, by rw [Sym2.map_pair_eq]⟩
    rw [mem_edgeFinset, mem_edgeSet, Subgraph.coe_adj]
    exact ⟨haS, hbS, hadj⟩

/-- `coinsWithin` is monotone in the graph. -/
private lemma coinsWithin_mono {N : ℕ} {G₁ G₂ : SimpleGraph (Fin N)} (h : G₁ ≤ G₂)
    (S : Finset (Fin N)) : coinsWithin G₁ S ⊆ coinsWithin G₂ S := by
  intro e he
  rw [mem_coinsWithin] at he ⊢
  obtain ⟨a, b, ha, hb, hadj, heq⟩ := he
  exact ⟨a, b, ha, hb, h hadj, heq⟩

/-- If `S` induces `M`, the number of `G'`-edges inside `S` equals `e(M)`. -/
private lemma coinsWithin_card_eq' {N : ℕ} {G' : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {M : FinFlag ∅ₜ} (h : inducesAt M G' S) :
    (coinsWithin G' S).card = M.2.out.graph.edgeFinset.card := by
  rw [coinsWithin, Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  obtain ⟨g1⟩ := exists_iso_of_inducesAt h
  exact g1.card_edgeFinset_eq

/-- The induced subgraph on `S` has `|S|` vertices. -/
private lemma card_induced_verts {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    Fintype.card (↑((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).verts) = S.card := by
  rw [← Set.toFinset_card]
  simp

/-- The number of edges inside `S` is at most `C(|S|, 2)`. -/
private lemma coinsWithin_card_le {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    (coinsWithin G S).card ≤ S.card.choose 2 := by
  rw [coinsWithin, Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  calc ((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe.edgeFinset.card
      ≤ (Fintype.card (↑((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).verts)).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two
    _ = S.card.choose 2 := by rw [card_induced_verts]

/-- A subset inducing `M` has exactly `M.1` vertices. -/
private lemma inducesAt_card {N : ℕ} {G' : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {M : FinFlag ∅ₜ} (h : inducesAt M G' S) : S.card = M.1 := by
  obtain ⟨g⟩ := exists_iso_of_inducesAt h
  have hc := Fintype.card_congr g.toEquiv
  rw [Fintype.card_fin, card_induced_verts] at hc
  exact hc

/-- If all `G`-edges inside `S` keep their coins, then the thinned graph still induces `M` on `S`
(it agrees with `G` on `S`). -/
private lemma coinBox_within_subset {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {M : FinFlag ∅ₜ} (hG : inducesAt M G S) {ω : ThinCoins N}
    (hω : ω ∈ coinBox (coinsWithin G S)) : inducesAt M (thinGraph G ω) S := by
  refine inducesAt_of_adj_agree ?_ M hG
  intro a ha b hb
  rw [thinGraph_adj]
  refine ⟨fun hh => hh.1, fun hab => ⟨hab, ?_⟩⟩
  have haS : a ∈ (↑S : Set (Fin N)) := Finset.mem_coe.mpr ha
  have hbS : b ∈ (↑S : Set (Fin N)) := Finset.mem_coe.mpr hb
  have hmem : s(a, b) ∈ coinsWithin G S := by
    rw [coinsWithin, Finset.mem_image]
    refine ⟨s(⟨a, haS⟩, ⟨b, hbS⟩), ?_, by rw [Sym2.map_pair_eq]⟩
    rw [mem_edgeFinset, mem_edgeSet, Subgraph.coe_adj]
    exact ⟨haS, hbS, hab⟩
  have hω' : ∀ e ∈ coinsWithin G S, ω e = true := hω
  exact hω' s(a, b) hmem

/-- If `S` has the wrong cardinality, no thinning induces `M` on `S`. -/
private lemma thinA_empty_of_card_ne {N : ℕ} {G : SimpleGraph (Fin N)} {M : FinFlag ∅ₜ}
    {S : Finset (Fin N)} (hS : S.card ≠ M.1) :
    {ω : ThinCoins N | inducesAt M (thinGraph G ω) S} = ∅ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact fun hω => hS (inducesAt_card hω)

/-- **First-moment, per subset.**  The probability that `S` induces `M` in the thinned graph is at
most `C(C(|S|,2), e(M)) · λ^{e(M)}` (a union bound over the `e(M)`-edge patterns inside `S`). -/
private lemma thinA_measure_le (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) (S : Finset (Fin N)) :
    (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal
      ≤ ((S.card.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
          * lam ^ (M.2.out.graph.edgeFinset.card) := by
  set q := M.2.out.graph.edgeFinset.card with hq
  have hsub : {ω | inducesAt M (thinGraph G ω) S}
      ⊆ ⋃ T ∈ (coinsWithin G S).powersetCard q, coinBox T := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hTmem : coinsWithin (thinGraph G ω) S ∈ (coinsWithin G S).powersetCard q := by
      rw [Finset.mem_powersetCard]
      exact ⟨coinsWithin_mono (thinGraph_le G ω) S, coinsWithin_card_eq' hω⟩
    have hbox : ω ∈ coinBox (coinsWithin (thinGraph G ω) S) := by
      show ∀ e ∈ coinsWithin (thinGraph G ω) S, ω e = true
      intro e he
      rw [mem_coinsWithin] at he
      obtain ⟨a, b, _, _, hadj, rfl⟩ := he
      exact ((thinGraph_adj G ω a b).mp hadj).2
    exact Set.mem_biUnion hTmem hbox
  have hbound : thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}
      ≤ ∑ T ∈ (coinsWithin G S).powersetCard q, thinMeasure N lam h0 h1 (coinBox T) :=
    le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
  have hfin : (∑ T ∈ (coinsWithin G S).powersetCard q,
      thinMeasure N lam h0 h1 (coinBox T)) ≠ ⊤ := by
    rw [← lt_top_iff_ne_top]
    exact ENNReal.sum_lt_top.mpr (fun T _ => measure_lt_top _ _)
  calc (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal
      ≤ (∑ T ∈ (coinsWithin G S).powersetCard q,
          thinMeasure N lam h0 h1 (coinBox T)).toReal := ENNReal.toReal_mono hfin hbound
    _ = ∑ T ∈ (coinsWithin G S).powersetCard q,
          (thinMeasure N lam h0 h1 (coinBox T)).toReal :=
        ENNReal.toReal_sum (fun T _ => measure_ne_top _ _)
    _ = ∑ _T ∈ (coinsWithin G S).powersetCard q, lam ^ q := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [coinBox_measure_toReal, (Finset.mem_powersetCard.mp hT).2]
    _ = ((coinsWithin G S).card.choose q : ℝ) * lam ^ q := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    _ ≤ ((S.card.choose 2).choose q : ℝ) * lam ^ q := by
        gcongr
        exact coinsWithin_card_le G S

/-- The number of `k`-subsets of `Fin N` is `C(N, k)`. -/
private lemma card_filter_card_eq {N : ℕ} (k : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)).card = N.choose k := by
  have hset : (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k))
      = (Finset.univ : Finset (Fin N)).powersetCard k := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ## The expected density as a sum of event probabilities -/

/-- `thinExpectDensity` is the normalized sum, over `M.1`-subsets `S`, of the probability that `S`
induces `M` in the thinned graph. -/
private lemma thinExpectDensity_eq_sum (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) :
    thinExpectDensity lam h0 h1 G M
      = (∑ S : Finset (Fin N),
          (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal)
        / (N.choose M.1 : ℝ) := by
  rw [thinExpectDensity]
  simp_rw [density_eq_count]
  rw [integral_div]
  congr 1
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_finset_sum _ (fun S _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro S _
  rw [show (fun ω => (if inducesAt M (thinGraph G ω) S then (1 : ℝ) else 0))
        = Set.indicator {ω | inducesAt M (thinGraph G ω) S} (fun _ => 1) from ?_]
  · rw [integral_indicator_const _ ((Set.toFinite _).measurableSet)]
    simp [measureReal_def]
  · funext ω
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]

/-! ## The public theorems -/

/-- **(1) In-class.**  If the class is edge-deletion-closed, the thinned graph of an in-class graph is
again in the class. -/
theorem thinGraph_mem {N : ℕ} (hc : HeredClass) (hedc : EdgeDeletionClosed hc)
    {G : SimpleGraph (Fin N)} (hG : hc.Mem G) (ω : ThinCoins N) :
    hc.Mem (thinGraph G ω) :=
  hedc (thinGraph_le G ω) hG

/-- **(2a) Non-negativity.** -/
theorem thinExpectDensity_nonneg (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) :
    0 ≤ thinExpectDensity lam h0 h1 G M := by
  apply integral_nonneg
  intro ω
  simp only [Pi.zero_apply]
  exact_mod_cast flagListDensity₁_ge_zero M.2 (graphFlag (thinGraph G ω))

/-- **(2b) Upper bound by `1`.** -/
theorem thinExpectDensity_le_one (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) :
    thinExpectDensity lam h0 h1 G M ≤ 1 := by
  calc thinExpectDensity lam h0 h1 G M
      ≤ ∫ _ω, (1 : ℝ) ∂(thinMeasure N lam h0 h1) := by
        apply integral_mono Integrable.of_finite (integrable_const 1)
        intro ω
        dsimp only
        exact_mod_cast flagListDensity₁_le_one M.2 (graphFlag (thinGraph G ω))
    _ = 1 := by simp

/-- **(3) First-moment upper bound.**  A copy of `M` needs all `q := e(M)` of its edges to survive
(each with probability `λ`), so the expected density is `O(λ^q)`.  (The displayed `N`-independent
constant accounts for the finitely many labelled `q`-edge patterns inside an `M.1`-subset; the bare
`λ^q` of the informal statement is the per-copy probability, not the induced density.) -/
theorem thinExpectDensity_le_pow (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) (M : FinFlag ∅ₜ) :
    thinExpectDensity lam h0 h1 G M
      ≤ ((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
        * lam ^ (M.2.out.graph.edgeFinset.card) := by
  set q := M.2.out.graph.edgeFinset.card with hq
  set c : ℝ := ((M.1.choose 2).choose q : ℝ) * lam ^ q with hc
  have hcnn : 0 ≤ c := by rw [hc]; positivity
  rw [thinExpectDensity_eq_sum]
  have hnum : (∑ S : Finset (Fin N),
      (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal)
        ≤ (N.choose M.1 : ℝ) * c := by
    calc (∑ S : Finset (Fin N),
          (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal)
        ≤ ∑ S : Finset (Fin N), (if S.card = M.1 then c else 0) := by
          apply Finset.sum_le_sum
          intro S _
          by_cases hS : S.card = M.1
          · rw [if_pos hS]
            calc (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal
                ≤ ((S.card.choose 2).choose q : ℝ) * lam ^ q := thinA_measure_le lam h0 h1 G M S
              _ = c := by rw [hc, hS]
          · rw [if_neg hS, thinA_empty_of_card_ne hS, measure_empty, ENNReal.toReal_zero]
      _ = (N.choose M.1 : ℝ) * c := by
          rw [← Finset.sum_filter, Finset.sum_const, card_filter_card_eq, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (N.choose M.1) with hD | hD
  · rw [hD]; simp only [Nat.cast_zero, div_zero]; exact hcnn
  · rw [div_le_iff₀ (by exact_mod_cast hD)]
    calc (∑ S : Finset (Fin N),
          (thinMeasure N lam h0 h1 {ω | inducesAt M (thinGraph G ω) S}).toReal)
        ≤ (N.choose M.1 : ℝ) * c := hnum
      _ = c * (N.choose M.1 : ℝ) := by ring

/-- **(4) `σ`-type lower bound.**  Each `σ`-inducing subset of `G` keeps its `σ`-pattern with
probability `≥ λ^{e(σ)}` (the non-edges survive automatically, since thinning only deletes), so the
expected `σ`-density dominates `λ^{e(σ)}` times the deterministic `σ`-density of `G`. -/
theorem thinExpectDensity_type_ge {n₀ : ℕ} (σ : FlagType (Fin n₀))
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {N : ℕ} (G : SimpleGraph (Fin N)) :
    lam ^ (σ.edgeFinset.card)
        * (flagDensity₁ (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2 (graphFlag G) : ℝ)
      ≤ thinExpectDensity lam h0 h1 G ⟨n₀, σ.toEmptyTypeFlag⟩ := by
  rw [thinExpectDensity_eq_sum, density_eq_count, ← mul_div_assoc]
  gcongr
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : inducesAt (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ) G S
  · simp only [hS, if_true, Nat.cast_one, mul_one]
    have hsub : coinBox (coinsWithin G S)
        ⊆ {ω | inducesAt (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ) (thinGraph G ω) S} :=
      fun ω hω => coinBox_within_subset hS hω
    calc lam ^ σ.edgeFinset.card
        = (thinMeasure N lam h0 h1 (coinBox (coinsWithin G S))).toReal := by
          rw [coinBox_measure_toReal, coinsWithin_card_eq σ hS]
      _ ≤ (thinMeasure N lam h0 h1
            {ω | inducesAt (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ) (thinGraph G ω) S}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  · simp only [hS, if_false, Nat.cast_zero, mul_zero]
    exact ENNReal.toReal_nonneg

/-! ## Second-moment infrastructure for the realization theorem -/

/-- The `[0,1]`-valued indicator that the subset `S` induces the flag `M` in the thinned graph. -/
private noncomputable def thinInd (M : FinFlag ∅ₜ) {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (ω : ThinCoins N) : ℝ :=
  if inducesAt M (thinGraph G ω) S then 1 else 0

private lemma thinInd_nonneg (M : FinFlag ∅ₜ) {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (ω : ThinCoins N) : 0 ≤ thinInd M G S ω := by
  simp only [thinInd]; split <;> norm_num

private lemma thinInd_le_one (M : FinFlag ∅ₜ) {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (ω : ThinCoins N) : thinInd M G S ω ≤ 1 := by
  simp only [thinInd]; split <;> norm_num

/-- `thinInd` depends only on the coins inside `S`. -/
private lemma thinInd_factor (M : FinFlag ∅ₜ) {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) {ω ω' : ThinCoins N}
    (h : ∀ e ∈ coinsWithin G S, ω e = ω' e) : thinInd M G S ω = thinInd M G S ω' := by
  have hadj : ∀ a ∈ S, ∀ b ∈ S, ((thinGraph G ω).Adj a b ↔ (thinGraph G ω').Adj a b) := by
    intro a ha b hb
    rw [thinGraph_adj, thinGraph_adj]
    by_cases hG : G.Adj a b
    · have hmem : s(a, b) ∈ coinsWithin G S := by
        rw [mem_coinsWithin]; exact ⟨a, b, ha, hb, hG, rfl⟩
      rw [h _ hmem]
    · simp [hG]
  have hiff : inducesAt M (thinGraph G ω) S ↔ inducesAt M (thinGraph G ω') S :=
    ⟨fun hh => inducesAt_of_adj_agree (fun a ha b hb => (hadj a ha b hb).symm) M hh,
     fun hh => inducesAt_of_adj_agree (fun a ha b hb => hadj a ha b hb) M hh⟩
  simp only [thinInd]
  by_cases hc : inducesAt M (thinGraph G ω) S
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun hh => hc (hiff.mpr hh))]

/-- Two coin-blocks intersect only if the subsets share at least two vertices. -/
private lemma coinsWithin_inter_ge {N : ℕ} {G : SimpleGraph (Fin N)} {S S' : Finset (Fin N)}
    (h : ¬ Disjoint (coinsWithin G S) (coinsWithin G S')) : 2 ≤ (S ∩ S').card := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨e, heS, heS'⟩ := h
  rw [mem_coinsWithin] at heS
  obtain ⟨a, b, haS, hbS, hab, rfl⟩ := heS
  rw [mem_coinsWithin] at heS'
  obtain ⟨c, d, hcS', hdS', _, he⟩ := heS'
  have hmem : a ∈ S' ∧ b ∈ S' := by
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hcS', hdS'⟩
    · exact ⟨hdS', hcS'⟩
  have haI : a ∈ S ∩ S' := Finset.mem_inter.mpr ⟨haS, hmem.1⟩
  have hbI : b ∈ S ∩ S' := Finset.mem_inter.mpr ⟨hbS, hmem.2⟩
  calc 2 = ({a, b} : Finset (Fin N)).card := (Finset.card_pair hab.ne).symm
    _ ≤ (S ∩ S').card := Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haI
        · exact hbI)

/-- The number of `k`-subsets of `Fin N` containing a fixed `T` (with `|T| ≤ k`). -/
private lemma card_filter_superset {N k : ℕ} (T : Finset (Fin N)) (hT : T.card ≤ k) :
    (((Finset.univ : Finset (Fin N)).powersetCard k).filter (fun S => T ⊆ S)).card
      = (N - T.card).choose (k - T.card) := by
  have hbij : (((Finset.univ : Finset (Fin N)).powersetCard k).filter (fun S => T ⊆ S)).card
      = ((Finset.univ \ T).powersetCard (k - T.card)).card := by
    refine Finset.card_nbij' (fun S => S \ T) (fun U => U ∪ T) ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
      obtain ⟨⟨_, hScard⟩, hTS⟩ := hS
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hTS, hScard]
    · intro U hU
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hU
      obtain ⟨hUsub, hUcard⟩ := hU
      have hdisj : Disjoint U T := by
        rw [Finset.disjoint_left]
        intro x hxU hxT
        exact (Finset.mem_sdiff.mp (hUsub hxU)).2 hxT
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_union_of_disjoint hdisj, hUcard,
        Nat.sub_add_cancel hT]⟩, Finset.subset_union_right⟩
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
      exact Finset.sdiff_union_of_subset hS.2
    · intro U hU
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hU
      have hdisj : Disjoint U T := by
        rw [Finset.disjoint_left]
        intro x hxU hxT
        exact (Finset.mem_sdiff.mp (hU.1 hxU)).2 hxT
      exact Finset.union_sdiff_cancel_right hdisj
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ T),
    Finset.card_univ, Fintype.card_fin]

/-- `C(|S ∩ S'|, 2)` counts the `2`-subsets contained in both `S` and `S'`. -/
private lemma card_inter_choose_two {N : ℕ} (S S' : Finset (Fin N)) :
    (S ∩ S').card.choose 2
      = (((Finset.univ : Finset (Fin N)).powersetCard 2).filter
          (fun T => T ⊆ S ∧ T ⊆ S')).card := by
  rw [← Finset.card_powersetCard]
  congr 1
  ext T
  rw [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
  exact ⟨fun ⟨hsub, hcard⟩ => ⟨⟨Finset.subset_univ T, hcard⟩, hsub⟩,
         fun ⟨⟨_, hcard⟩, hsub⟩ => ⟨hsub, hcard⟩⟩

/-- Counting bound: the number of overlapping `k`-subset pairs, weighted by `C(N,2)`, is dominated by
`C(k,2)² · C(N,k)²` (an equality for `k ≥ 2` via the subset-of-subset identity). -/
private lemma count_choose_le (N k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (S ∩ S').card.choose 2)
        * (N.choose 2)
      ≤ (k.choose 2) ^ 2 * (N.choose k) ^ 2 := by
  rcases lt_or_ge k 2 with hk2 | hk2
  · have hzero : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (S ∩ S').card.choose 2) = 0 := by
      refine Finset.sum_eq_zero (fun S hS => Finset.sum_eq_zero (fun S' _ => ?_))
      apply Nat.choose_eq_zero_of_lt
      have hSc : S.card = k := (Finset.mem_powersetCard.mp hS).2
      have hle : (S ∩ S').card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
      omega
    rw [hzero, Nat.zero_mul]
    exact Nat.zero_le _
  · have hcount : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (S ∩ S').card.choose 2)
        = (N.choose 2) * ((N - 2).choose (k - 2)) ^ 2 := by
      calc (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
              ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (S ∩ S').card.choose 2)
          = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
              ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
                  (if T ⊆ S ∧ T ⊆ S' then 1 else 0) := by
            refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun S' _ => ?_))
            rw [card_inter_choose_two, Finset.card_filter]
        _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
              ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
                ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                  (if T ⊆ S ∧ T ⊆ S' then 1 else 0) :=
            Finset.sum_congr rfl (fun S _ => Finset.sum_comm)
        _ = ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
              ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                  (if T ⊆ S ∧ T ⊆ S' then 1 else 0) := Finset.sum_comm
        _ = ∑ _T ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
              ((N - 2).choose (k - 2)) * ((N - 2).choose (k - 2)) := by
            refine Finset.sum_congr rfl (fun T hT => ?_)
            have hTcard : T.card = 2 := (Finset.mem_powersetCard.mp hT).2
            have hfac : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                  (if T ⊆ S ∧ T ⊆ S' then (1 : ℕ) else 0))
                = (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                    (if T ⊆ S then (1 : ℕ) else 0))
                  * (∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                    (if T ⊆ S' then (1 : ℕ) else 0)) := by
              rw [Finset.sum_mul_sum]
              refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun S' _ => ?_))
              by_cases h1 : T ⊆ S <;> by_cases h2 : T ⊆ S' <;> simp [h1, h2]
            rw [hfac]
            have haT : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
                (if T ⊆ S then (1 : ℕ) else 0)) = (N - 2).choose (k - 2) := by
              rw [← Finset.card_filter, card_filter_superset T (by rw [hTcard]; exact hk2), hTcard]
            rw [haT]
        _ = ((Finset.univ : Finset (Fin N)).powersetCard 2).card * ((N - 2).choose (k - 2)) ^ 2 := by
            rw [Finset.sum_const, smul_eq_mul, ← pow_two]
        _ = (N.choose 2) * ((N - 2).choose (k - 2)) ^ 2 := by
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcount]
    have hid : N.choose 2 * ((N - 2).choose (k - 2)) = N.choose k * (k.choose 2) :=
      (Nat.choose_mul hk2).symm
    have heq : (N.choose 2 * ((N - 2).choose (k - 2)) ^ 2) * (N.choose 2)
        = (k.choose 2) ^ 2 * (N.choose k) ^ 2 := by
      calc (N.choose 2 * ((N - 2).choose (k - 2)) ^ 2) * (N.choose 2)
          = (N.choose 2 * ((N - 2).choose (k - 2))) ^ 2 := by ring
        _ = (N.choose k * (k.choose 2)) ^ 2 := by rw [hid]
        _ = (k.choose 2) ^ 2 * (N.choose k) ^ 2 := by ring
    exact le_of_eq heq

private lemma thinInd_memLp (M : FinFlag ∅ₜ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {N : ℕ}
    (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    MemLp (thinInd M G S) 2 (thinMeasure N lam h0 h1) := by
  apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [thinInd_nonneg M G S ω], by linarith [thinInd_le_one M G S ω]⟩

/-- **Block independence (§9.4 key lemma).**  If the coin-blocks of `S` and `S'` are disjoint, the
indicators `thinInd … S` and `thinInd … S'` are independent under the product Bernoulli measure. -/
private lemma thinInd_indepFun (M : FinFlag ∅ₜ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {N : ℕ}
    (G : SimpleGraph (Fin N)) {S S' : Finset (Fin N)}
    (hdisj : Disjoint (coinsWithin G S) (coinsWithin G S')) :
    IndepFun (thinInd M G S) (thinInd M G S') (thinMeasure N lam h0 h1) := by
  classical
  have hcoord : iIndepFun (fun (e : Sym2 (Fin N)) (ω : ThinCoins N) => ω e)
      (thinMeasure N lam h0 h1) :=
    iIndepFun_pi
      (μ := fun _ : Sym2 (Fin N) => (PMF.bernoulli (lamNN lam) (lamNN_le_one h1)).toMeasure)
      (X := fun _ : Sym2 (Fin N) => (id : Bool → Bool)) (fun _ => aemeasurable_id)
  have hfacS : thinInd M G S
      = (fun r : ↥(coinsWithin G S) → Bool =>
          thinInd M G S (fun e => if h : e ∈ coinsWithin G S then r ⟨e, h⟩ else false))
        ∘ (fun ω (i : ↥(coinsWithin G S)) => ω ↑i) := by
    funext ω
    simp only [Function.comp_apply]
    refine thinInd_factor M G S ?_
    intro e he
    rw [dif_pos he]
  have hfacS' : thinInd M G S'
      = (fun r : ↥(coinsWithin G S') → Bool =>
          thinInd M G S' (fun e => if h : e ∈ coinsWithin G S' then r ⟨e, h⟩ else false))
        ∘ (fun ω (i : ↥(coinsWithin G S')) => ω ↑i) := by
    funext ω
    simp only [Function.comp_apply]
    refine thinInd_factor M G S' ?_
    intro e he
    rw [dif_pos he]
  rw [hfacS, hfacS']
  exact (hcoord.indepFun_finset (coinsWithin G S) (coinsWithin G S') hdisj
    (fun e => measurable_pi_apply e)).comp (measurable_of_finite _) (measurable_of_finite _)

/-- **Per-pair covariance bound.**  Vanishing covariance when the blocks are disjoint, otherwise the
`[0,1]`-bound `1 ≤ C(|S ∩ S'|, 2)`. -/
private lemma thinInd_cov_le (M : FinFlag ∅ₜ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {N : ℕ}
    (G : SimpleGraph (Fin N)) (S S' : Finset (Fin N)) :
    cov[thinInd M G S, thinInd M G S'; thinMeasure N lam h0 h1]
      ≤ ((S ∩ S').card.choose 2 : ℝ) := by
  have hMS := thinInd_memLp M lam h0 h1 G S
  have hMS' := thinInd_memLp M lam h0 h1 G S'
  by_cases hdisj : Disjoint (coinsWithin G S) (coinsWithin G S')
  · rw [(thinInd_indepFun M lam h0 h1 G hdisj).covariance_eq_zero hMS hMS']
    positivity
  · have h2 : 2 ≤ (S ∩ S').card := coinsWithin_inter_ge hdisj
    have hchoose : (1 : ℝ) ≤ ((S ∩ S').card.choose 2 : ℝ) := by
      have h1n : (1 : ℕ) ≤ (S ∩ S').card.choose 2 := Nat.choose_pos h2
      exact_mod_cast h1n
    have hprod : (thinMeasure N lam h0 h1)[thinInd M G S * thinInd M G S'] ≤ 1 := by
      rw [show (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂(thinMeasure N lam h0 h1) by simp]
      apply integral_mono (hMS.integrable_mul hMS') (integrable_const 1)
      intro ω
      simp only [Pi.mul_apply]
      nlinarith [thinInd_nonneg M G S ω, thinInd_le_one M G S ω,
        thinInd_nonneg M G S' ω, thinInd_le_one M G S' ω]
    have hnn : 0 ≤ (thinMeasure N lam h0 h1)[thinInd M G S]
        * (thinMeasure N lam h0 h1)[thinInd M G S'] :=
      mul_nonneg (integral_nonneg (fun ω => thinInd_nonneg M G S ω))
        (integral_nonneg (fun ω => thinInd_nonneg M G S' ω))
    rw [covariance_eq_sub hMS hMS']
    linarith [hprod, hnn, hchoose]

/-- **Variance bound.**  `Var[X_M] ≤ C(M.1, 2)² / C(N, 2) = O(1/N²)`. -/
private lemma thinVar_le (M : FinFlag ∅ₜ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {N : ℕ}
    (G : SimpleGraph (Fin N)) (hN2 : 2 ≤ N) (hMN : M.1 < N) :
    variance (fun ω => (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ))
        (thinMeasure N lam h0 h1)
      ≤ (M.1.choose 2 : ℝ) ^ 2 / (N.choose 2 : ℝ) := by
  have hDpos : (0 : ℝ) < (N.choose M.1 : ℝ) := by exact_mod_cast Nat.choose_pos (le_of_lt hMN)
  have hN2pos : (0 : ℝ) < (N.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hN2
  set P := (Finset.univ : Finset (Fin N)).powersetCard M.1 with hP
  have hXrw : (fun ω => (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ))
      = (fun ω => (1 / (N.choose M.1 : ℝ)) * ∑ S ∈ P, thinInd M G S ω) := by
    funext ω
    rw [density_eq_count]
    have hcardeq : (((Finset.univ : Finset (Finset (Fin N))).filter
          (fun S => inducesAt M (thinGraph G ω) S)).card : ℝ)
        = ∑ S ∈ P, thinInd M G S ω := by
      have h1' : (((Finset.univ : Finset (Finset (Fin N))).filter
            (fun S => inducesAt M (thinGraph G ω) S)).card : ℝ)
          = ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))), thinInd M G S ω := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        simp only [thinInd]
        by_cases h : inducesAt M (thinGraph G ω) S <;> simp [h]
      rw [h1']
      refine (Finset.sum_subset (Finset.subset_univ P) (fun S _ hSP => ?_)).symm
      have hnot : ¬ inducesAt M (thinGraph G ω) S := by
        intro hind
        apply hSP
        rw [hP]
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, inducesAt_card hind⟩
      simp only [thinInd]
      exact if_neg hnot
    rw [hcardeq]; ring
  rw [hXrw, variance_const_mul, variance_fun_sum' (fun S _ => thinInd_memLp M lam h0 h1 G S)]
  have hcovsum : (∑ S ∈ P, ∑ S' ∈ P,
        cov[thinInd M G S, thinInd M G S'; thinMeasure N lam h0 h1])
      ≤ ∑ S ∈ P, ∑ S' ∈ P, ((S ∩ S').card.choose 2 : ℝ) :=
    Finset.sum_le_sum (fun S _ => Finset.sum_le_sum
      (fun S' _ => thinInd_cov_le M lam h0 h1 G S S'))
  refine le_trans (mul_le_mul_of_nonneg_left hcovsum (by positivity)) ?_
  have hcast : (∑ S ∈ P, ∑ S' ∈ P, ((S ∩ S').card.choose 2 : ℝ))
      = ((∑ S ∈ P, ∑ S' ∈ P, (S ∩ S').card.choose 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, show (1 / (N.choose M.1 : ℝ)) ^ 2
        * ((∑ S ∈ P, ∑ S' ∈ P, (S ∩ S').card.choose 2 : ℕ) : ℝ)
      = ((∑ S ∈ P, ∑ S' ∈ P, (S ∩ S').card.choose 2 : ℕ) : ℝ) / (N.choose M.1 : ℝ) ^ 2 from by ring]
  rw [hP, div_le_div_iff₀ (pow_pos hDpos 2) hN2pos]
  have hnat := count_choose_le N M.1
  calc ((∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard M.1,
          ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard M.1,
            (S ∩ S').card.choose 2 : ℕ) : ℝ) * (N.choose 2 : ℝ)
      = (((∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard M.1,
          ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard M.1,
            (S ∩ S').card.choose 2) * (N.choose 2) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (((M.1.choose 2) ^ 2 * (N.choose M.1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (M.1.choose 2 : ℝ) ^ 2 * (N.choose M.1 : ℝ) ^ 2 := by push_cast; ring

private lemma sub_one_le_choose_two (N : ℕ) : N - 1 ≤ N.choose 2 := by
  rcases N with _ | _ | n
  · simp
  · simp
  · show n + 1 ≤ (n + 2).choose 2
    rw [Nat.choose_two_right]
    show n + 1 ≤ (n + 2) * (n + 2 - 1) / 2
    rw [show n + 2 - 1 = n + 1 from rfl, Nat.le_div_iff_mul_le Nat.zero_lt_two]
    nlinarith [Nat.zero_le n]

/-- **(5) Deterministic realization (second-moment method).**  For large `N`, every in-class graph
`G` on `Fin N` has an in-class spanning subgraph `H` whose induced densities of all flags of size
`≤ m` are within `ε` of the edge-thinning expectations.  Obtained by a Chebyshev/union-bound argument:
each density `X_M(ω)` is an average of indicators `1_S` whose pairwise covariances vanish unless
`|S ∩ S'| ≥ 2`, giving `Var[X_M] = O(1/N)`. -/
theorem exists_thinned_realization (hc : HeredClass) (hedc : EdgeDeletionClosed hc)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (G : SimpleGraph (Fin N)), hc.Mem G →
      ∃ H : SimpleGraph (Fin N), H ≤ G ∧ hc.Mem H ∧
        ∀ M : FinFlag ∅ₜ, M.1 ≤ m →
          |(flagDensity₁ M.2 (graphFlag H) : ℝ) - thinExpectDensity lam h0.le h1 G M| ≤ ε := by
  classical
  -- The finite collection of flag-classes of size `≤ m`.
  set 𝓜 : Finset (FinFlag ∅ₜ) :=
    (Finset.range (m + 1)).biUnion
      (fun n => (Finset.univ : Finset (FlagWithSize ∅ₜ n)).image (fun F => (⟨n, F⟩ : FinFlag ∅ₜ)))
    with h𝓜def
  have hmem𝓜 : ∀ M : FinFlag ∅ₜ, M ∈ 𝓜 ↔ M.1 ≤ m := by
    intro M
    rw [h𝓜def]
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, hn, F, rfl⟩
      exact Nat.lt_succ_iff.mp hn
    · intro hM
      exact ⟨M.1, by omega, M.2, rfl⟩
  set Cnum : ℝ := (𝓜.card : ℝ) * (m.choose 2 : ℝ) ^ 2 with hCnumdef
  refine ⟨max (max (m + 1) 2) (⌈Cnum / ε ^ 2⌉₊ + 2), fun N hN G hG => ?_⟩
  have hNm1 : m + 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : ⌈Cnum / ε ^ 2⌉₊ + 2 ≤ N := le_trans (le_max_right _ _) hN
  set μ := thinMeasure N lam h0.le h1 with hμdef
  have hN2pos : (0 : ℝ) < (N.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hN2
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  -- Chebyshev's inequality per flag.
  have hCheb : ∀ M ∈ 𝓜,
      μ {ω | ε ≤ |(flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)
                - thinExpectDensity lam h0.le h1 G M|}
        ≤ ENNReal.ofReal ((m.choose 2 : ℝ) ^ 2 / ((N.choose 2 : ℝ) * ε ^ 2)) := by
    intro M hM
    have hMm : M.1 ≤ m := (hmem𝓜 M).mp hM
    have hMN : M.1 < N := lt_of_le_of_lt hMm (by omega)
    have hXmem : MemLp (fun ω => (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)) 2 μ := by
      apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
      filter_upwards with ω
      simp only [Real.norm_eq_abs, abs_le]
      have hge : (0 : ℝ) ≤ (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ) := by
        exact_mod_cast flagListDensity₁_ge_zero M.2 (graphFlag (thinGraph G ω))
      have hle : (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ) ≤ 1 := by
        exact_mod_cast flagListDensity₁_le_one M.2 (graphFlag (thinGraph G ω))
      exact ⟨by linarith, hle⟩
    have hEX : μ[fun ω => (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)]
        = thinExpectDensity lam h0.le h1 G M := rfl
    have hVar : variance (fun ω => (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)) μ
        ≤ (m.choose 2 : ℝ) ^ 2 / (N.choose 2 : ℝ) := by
      rw [hμdef]
      refine le_trans (thinVar_le M lam h0.le h1 G hN2 hMN) ?_
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hN2pos)
      have hcast : (M.1.choose 2 : ℝ) ≤ (m.choose 2 : ℝ) := by
        exact_mod_cast Nat.choose_le_choose 2 hMm
      have hpos : (0 : ℝ) ≤ (M.1.choose 2 : ℝ) := Nat.cast_nonneg _
      nlinarith [hcast, hpos]
    calc μ {ω | ε ≤ |(flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)
                - thinExpectDensity lam h0.le h1 G M|}
        ≤ ENNReal.ofReal
            (variance (fun ω => (flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)) μ / ε ^ 2) := by
          rw [← hEX]
          exact meas_ge_le_variance_div_sq hXmem hε
      _ ≤ ENNReal.ofReal ((m.choose 2 : ℝ) ^ 2 / ((N.choose 2 : ℝ) * ε ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← div_div]
          exact div_le_div_of_nonneg_right hVar (le_of_lt hε2)
  -- Union bound over `𝓜`.
  set Bad : Set (ThinCoins N) :=
    ⋃ M ∈ 𝓜, {ω | ε ≤ |(flagDensity₁ M.2 (graphFlag (thinGraph G ω)) : ℝ)
                - thinExpectDensity lam h0.le h1 G M|} with hBaddef
  have hBadle : μ Bad
      ≤ ∑ _M ∈ 𝓜, ENNReal.ofReal ((m.choose 2 : ℝ) ^ 2 / ((N.choose 2 : ℝ) * ε ^ 2)) := by
    refine le_trans ?_ (Finset.sum_le_sum hCheb)
    rw [hBaddef]
    exact measure_biUnion_finset_le 𝓜 _
  have hthr : Cnum < (N.choose 2 : ℝ) * ε ^ 2 := by
    apply (div_lt_iff₀ hε2).mp
    have hceil : Cnum / ε ^ 2 ≤ (⌈Cnum / ε ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have hsub : (↑N - 1 : ℝ) ≤ (N.choose 2 : ℝ) := by
      have hnat : N - 1 ≤ N.choose 2 := sub_one_le_choose_two N
      have hc2 : ((N - 1 : ℕ) : ℝ) ≤ (N.choose 2 : ℝ) := by exact_mod_cast hnat
      rwa [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hc2
    have hNbig : ((⌈Cnum / ε ^ 2⌉₊ : ℝ) + 2) ≤ (N : ℝ) := by exact_mod_cast hNc
    linarith
  have hsumlt :
      (∑ _M ∈ 𝓜, ENNReal.ofReal ((m.choose 2 : ℝ) ^ 2 / ((N.choose 2 : ℝ) * ε ^ 2))) < 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one,
      ← mul_div_assoc, ← hCnumdef, div_lt_one (mul_pos hN2pos hε2)]
    exact hthr
  have hBadlt : μ Bad < 1 := lt_of_le_of_lt hBadle hsumlt
  have hcompl : (Badᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hBadeq
    rw [hBadeq, measure_univ] at hBadlt
    exact lt_irrefl 1 hBadlt
  obtain ⟨ω₀, hω₀⟩ := hcompl
  rw [Set.mem_compl_iff, hBaddef, Set.mem_iUnion₂] at hω₀
  refine ⟨thinGraph G ω₀, thinGraph_le G ω₀, thinGraph_mem hc hedc hG ω₀, fun M hMm => ?_⟩
  have hM𝓜 : M ∈ 𝓜 := (hmem𝓜 M).mpr hMm
  by_contra hcon
  push_neg at hcon
  exact hω₀ ⟨M, hM𝓜, le_of_lt hcon⟩

end FlagAlgebras.MetaTheory
