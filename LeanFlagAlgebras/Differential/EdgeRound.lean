import LeanFlagAlgebras.Differential.DeleteEdge
import LeanFlagAlgebras.Differential.Ensemble
import LeanFlagAlgebras.Differential.Telescope

/-! # The edge deletion round (Razborov (29)–(33), edge case)

Finite machinery for `bad_edge_negPart_tendsto_zero`, mirroring
`Telescope.lean`:

* `adjPairs`/`pairFlag` — the ordered adjacent pairs of a host and their
  `E`-rooted flags;
* `integral_toMeasure_eq_pair_average` — the empirical integral against the
  `E`-labelling measure is the uniform average over ordered adjacent pairs
  (the label-extension weights `q(F') = |Iso(F')|/(L(L−1))` regroup into
  pair-fibre counts, and the normalisation `∑ q(F')` is the ordered edge
  count over `L(L−1)`, so everything cancels to `1/#pairs`). -/

open MeasureTheory Filter
open scoped Topology

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

/-! ## Ordered adjacent pairs and their rooted flags -/

/-- The ordered adjacent pairs of a host graph. -/
noncomputable def adjPairs {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L)) : Finset (Fin L × Fin L) :=
  Finset.univ.filter (fun p => N.graph.Adj p.1 p.2)

theorem adjPairs_adj {L : ℕ} {N : LabeledGraph ∅ₜ (Fin L)} {p : Fin L × Fin L}
    (hp : p ∈ adjPairs N) : N.graph.Adj p.1 p.2 :=
  (Finset.mem_filter.mp hp).2

theorem mem_adjPairs {L : ℕ} {N : LabeledGraph ∅ₜ (Fin L)} {p : Fin L × Fin L}
    (hp : N.graph.Adj p.1 p.2) : p ∈ adjPairs N := by
  rw [adjPairs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hp⟩

/-- The `E`-rooted flag of an adjacent pair. -/
noncomputable def pairFlag {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (q : {p : Fin L × Fin L // p ∈ adjPairs N}) : FlagWithSize edgeType L :=
  ⟦edgeRootedAt N q.1.1 q.1.2 (adjPairs_adj q.2)⟧

theorem unlabeledGraph_edgeRootedAt {V : Type} (X : LabeledGraph ∅ₜ V) (v₁ v₂ : V)
    (h : X.graph.Adj v₁ v₂)
    : unlabeledGraph (edgeRootedAt X v₁ v₂ h) = X :=
  emptyType_labeledGraph_ext rfl

/-- Every `E`-flag sharing its underlying graph with an untyped host is the
rooting of that host at the pair of labelled vertices. -/
theorem eq_edgeRootedAt_of_graph_eq {L : ℕ} (X : LabeledGraph ∅ₜ (Fin L))
    (H : LabeledGraph edgeType (Fin L)) (hgraph : X.graph = H.graph)
    : H = edgeRootedAt X (H.type_embed 0) (H.type_embed 1)
        (by rw [hgraph]; exact edgeFlag_roots_adj H)
  := by
  have hX : unlabeledGraph H = X := emptyType_labeledGraph_ext hgraph.symm
  subst hX
  exact (edgeRootedAt_unlabeledGraph_self H).symm

/-- The rooted flag of any adjacent pair is a label extension of the host. -/
theorem pairFlag_mem_labelExtensions {L : ℕ} (M : FlagWithSize ∅ₜ L)
    (q : {p : Fin L × Fin L // p ∈ adjPairs M.out})
    : pairFlag M.out q ∈ labelExtensions M edgeType := by
  rw [labelExtensions_eq_filter, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show (⟦unlabeledGraph (edgeRootedAt M.out q.1.1 q.1.2 (adjPairs_adj q.2))⟧
      : FlagWithSize ∅ₜ L) = M
  rw [unlabeledGraph_edgeRootedAt]
  exact Quotient.out_eq M

/-- Every label extension of `M` at the edge type is realised by rooting `M`
at one of its ordered adjacent pairs. -/
theorem exists_realising_pair {L : ℕ} (M : FlagWithSize ∅ₜ L)
    (F' : FlagWithSize edgeType L) (hF' : F' ∈ labelExtensions M edgeType)
    : ∃ q : {p : Fin L × Fin L // p ∈ adjPairs M.out}, pairFlag M.out q = F'
  := by
  rw [labelExtensions_eq_filter, Finset.mem_filter] at hF'
  have h2 : (⟦unlabeledGraph F'.out⟧ : FlagWithSize ∅ₜ L) = M := by
    rw [← unlabel_out' F']
    exact hF'.2
  have hψ : unlabeledGraph F'.out ∼f M.out := Quotient.mk_eq_iff_out.mp h2
  obtain ⟨ψ⟩ := hψ
  have hadj0 : F'.out.graph.Adj (F'.out.type_embed 0) (F'.out.type_embed 1) :=
    edgeFlag_roots_adj F'.out
  have hadj : M.out.graph.Adj (ψ.graph_iso (F'.out.type_embed 0))
      (ψ.graph_iso (F'.out.type_embed 1)) :=
    ψ.graph_iso.map_rel_iff.mpr hadj0
  refine ⟨⟨(ψ.graph_iso (F'.out.type_embed 0), ψ.graph_iso (F'.out.type_embed 1)),
    mem_adjPairs hadj⟩, ?_⟩
  show (⟦edgeRootedAt M.out (ψ.graph_iso (F'.out.type_embed 0))
      (ψ.graph_iso (F'.out.type_embed 1)) _⟧ : FlagWithSize edgeType L) = F'
  have hiso : F'.out ∼f edgeRootedAt M.out (ψ.graph_iso (F'.out.type_embed 0))
      (ψ.graph_iso (F'.out.type_embed 1)) hadj := by
    refine ⟨{ graph_iso := ψ.graph_iso, type_preserve := ?_ }⟩
    funext x
    rcases fin_two_eq_zero_or_one x with rfl | rfl
    · rfl
    · rfl
  calc (⟦edgeRootedAt M.out (ψ.graph_iso (F'.out.type_embed 0))
        (ψ.graph_iso (F'.out.type_embed 1)) hadj⟧ : FlagWithSize edgeType L)
      = ⟦F'.out⟧ := Quotient.sound (flagEqv.symm hiso)
    _ = F' := Quotient.out_eq F'

/-! ## The unlabelling weight at the edge type -/

/-- The unlabelling weight of an `E`-flag on `ℓ + 2` vertices is its number of
realising label placements over the number of ordered pairs. -/
theorem downwardNormalizingFactor_edgeType {ℓ : ℕ} (F : FlagWithSize edgeType (ℓ + 2))
    : downwardNormalizingFactor F
      = (isomorphismCount F.out : ℚ) / (((ℓ : ℚ) + 2) * ((ℓ : ℚ) + 1))
  := by
  conv_lhs => rw [← Quotient.out_eq F]
  show downwardNormalizingFactor_labeledGraph F.out = _
  dsimp only [downwardNormalizingFactor_labeledGraph]
  have hfac : (ℓ + 2).factorial / (ℓ + 2 - 2).factorial = (ℓ + 2) * (ℓ + 1) := by
    have h1 : ℓ + 2 - 2 = ℓ := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, ← mul_assoc]
    exact Nat.mul_div_cancel _ (Nat.factorial_pos ℓ)
  rw [hfac]
  push_cast
  ring

/-- The isomorphism count of a realised label extension is the size of its
pair fibre. -/
theorem isomorphismCount_eq_card_pairs {L : ℕ} (X : LabeledGraph ∅ₜ (Fin L))
    (F : FlagWithSize edgeType L) (q₀ : {p : Fin L × Fin L // p ∈ adjPairs X})
    (hq₀ : pairFlag X q₀ = F)
    : isomorphismCount F.out
      = ((adjPairs X).attach.filter (fun q => pairFlag X q = F)).card
  := by
  rw [isomorphismCount_respect_eqv (flagEqv.symm (Quotient.mk_eq_iff_out.mp hq₀))]
  dsimp only [isomorphismCount]
  symm
  apply Finset.card_bij (fun (q : {p : Fin L × Fin L // p ∈ adjPairs X}) (_ : q ∈ _) =>
    edgeRootedAt X q.1.1 q.1.2 (adjPairs_adj q.2))
  · intro q hq
    rw [Finset.mem_filter] at hq
    simp only [Set.mem_toFinset, isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq]
    refine ⟨rfl, ?_⟩
    exact Quotient.exact (hq₀.trans hq.2.symm)
  · intro q₁ h₁ q₂ h₂ heq
    have h0 := congrArg (fun H : LabeledGraph edgeType (Fin L) => H.type_embed 0) heq
    have h1 := congrArg (fun H : LabeledGraph edgeType (Fin L) => H.type_embed 1) heq
    apply Subtype.ext
    apply Prod.ext
    · exact h0
    · exact h1
  · intro H hH
    simp only [Set.mem_toFinset, isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq] at hH
    obtain ⟨hgraph, hiso⟩ := hH
    have hXH : X.graph = H.graph := hgraph
    have hH' := eq_edgeRootedAt_of_graph_eq X H hXH
    refine ⟨⟨(H.type_embed 0, H.type_embed 1),
      mem_adjPairs (by rw [hXH]; exact edgeFlag_roots_adj H)⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_attach _ _, ?_⟩
      show (⟦edgeRootedAt X (H.type_embed 0) (H.type_embed 1) _⟧
          : FlagWithSize edgeType L) = F
      calc (⟦edgeRootedAt X (H.type_embed 0) (H.type_embed 1) _⟧
            : FlagWithSize edgeType L)
          = ⟦H⟧ := by rw [← hH']
        _ = ⟦edgeRootedAt X q₀.1.1 q₀.1.2 (adjPairs_adj q₀.2)⟧ :=
            Quotient.sound (flagEqv.symm hiso)
        _ = F := hq₀
    · exact hH'.symm

/-! ## The empirical integral as a pair average -/

/-- **The pair-average identity**: the empirical integral of any bounded
measurable function of the rooted evaluation of `g` against the `E`-labelling
measure of an `(ℓ+2)`-vertex model is the uniform average over its ordered
adjacent pairs. -/
theorem integral_toMeasure_eq_pair_average {ℓ : ℕ}
    (M : FlagWithSize ∅ₜ (ℓ + 2))
    (hM : flagDensity₁ edgeType.toEmptyTypeFlag M > 0)
    (g : FlagVector edgeType)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) {c : ℝ}
    (hΨb : ∀ a : FlagDensitySpace edgeType, |Ψ (densityEvalFun g a)| ≤ c)
    : ∫ a, Ψ (densityEvalFun g a)
        ∂(FinFlag.toMeasure (⟨ℓ + 2, M⟩ : FinFlag ∅ₜ) hM)
      = (1 / ((adjPairs M.out).card : ℝ))
          * ∑ q ∈ (adjPairs M.out).attach,
              Ψ (densityEval g ⟨ℓ + 2, pairFlag M.out q⟩)
  := by
  have hmeas : Measurable (fun a : FlagDensitySpace edgeType => Ψ (densityEvalFun g a)) :=
    hΨm.comp (measurable_densityEvalFun g)
  have hint : Integrable (fun a : FlagDensitySpace edgeType => Ψ (densityEvalFun g a))
      (FinFlag.toMeasure (⟨ℓ + 2, M⟩ : FinFlag ∅ₜ) hM) :=
    integrable_of_bounded hmeas c hΨb
  rw [FinFlag.integral_toMeasure_eq_sum (⟨ℓ + 2, M⟩ : FinFlag ∅ₜ) hM _ hint]
  -- the pair fibres partition the ordered adjacent pairs
  have hpart : (adjPairs M.out).attach
      = (labelExtensions M edgeType).biUnion (fun F' =>
          (adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F')) := by
    apply Finset.ext
    intro q
    constructor
    · intro _
      rw [Finset.mem_biUnion]
      refine ⟨pairFlag M.out q, pairFlag_mem_labelExtensions M q, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_attach _ _, rfl⟩
    · intro _
      exact Finset.mem_attach _ _
  have hdisj : ∀ F₁ ∈ labelExtensions M edgeType,
      ∀ F₂ ∈ labelExtensions M edgeType, F₁ ≠ F₂ →
      Disjoint ((adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F₁))
        ((adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F₂)) := by
    intro F₁ _ F₂ _ hne
    rw [Finset.disjoint_left]
    intro q h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact hne (h₁.2 ▸ h₂.2)
  -- the fibre cards sum to the number of ordered adjacent pairs
  have hcards : ∑ F' ∈ labelExtensions M edgeType, (isomorphismCount F'.out : ℝ)
      = ((adjPairs M.out).card : ℝ) := by
    have h1 : ∑ F' ∈ labelExtensions M edgeType, isomorphismCount F'.out
        = (adjPairs M.out).card := by
      calc ∑ F' ∈ labelExtensions M edgeType, isomorphismCount F'.out
          = ∑ F' ∈ labelExtensions M edgeType,
              ((adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F')).card := by
            apply Finset.sum_congr rfl
            intro F' hF'
            obtain ⟨q₀, hq₀⟩ := exists_realising_pair M F' hF'
            exact isomorphismCount_eq_card_pairs M.out F' q₀ hq₀
        _ = ((labelExtensions M edgeType).biUnion (fun F' =>
              (adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F'))).card :=
            (Finset.card_biUnion hdisj).symm
        _ = (adjPairs M.out).attach.card := by rw [← hpart]
        _ = (adjPairs M.out).card := Finset.card_attach
    exact_mod_cast h1
  have hpairs_pos : 0 < (adjPairs M.out).card := by
    obtain ⟨F', hF'⟩ := labelExtensions_nonempty hM
    obtain ⟨q, -⟩ := exists_realising_pair M F' hF'
    exact Finset.card_pos.mpr ⟨q.1, q.2⟩
  have hP : (0 : ℝ) < ((adjPairs M.out).card : ℝ) := by exact_mod_cast hpairs_pos
  have hD : (0 : ℝ) < ((ℓ : ℝ) + 2) * ((ℓ : ℝ) + 1) := by positivity
  -- the total unlabelling weight
  have hsum_dnf : ∑ F'' ∈ labelExtensions M edgeType,
      ((downwardNormalizingFactor F'' : ℚ) : ℝ)
      = ((adjPairs M.out).card : ℝ) / (((ℓ : ℝ) + 2) * ((ℓ : ℝ) + 1)) := by
    rw [← hcards, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro F'' _
    rw [downwardNormalizingFactor_edgeType F'']
    push_cast
    ring
  calc ∑ F' ∈ labelExtensions M edgeType,
        ((downwardNormalizingFactor F' : ℝ)
          / ∑ F'' ∈ labelExtensions M edgeType, (downwardNormalizingFactor F'' : ℝ))
        * Ψ (densityEvalFun g
            (funFromFlagWithSizeToFlagDensitySpace edgeType (ℓ + 2) F'))
      = ∑ F' ∈ labelExtensions M edgeType, (1 / ((adjPairs M.out).card : ℝ))
          * ((((adjPairs M.out).attach.filter
              (fun q => pairFlag M.out q = F')).card : ℝ)
            * Ψ (densityEvalFun g
                (funFromFlagWithSizeToFlagDensitySpace edgeType (ℓ + 2) F'))) := by
        apply Finset.sum_congr rfl
        intro F' hF'
        obtain ⟨q₀, hq₀⟩ := exists_realising_pair M F' hF'
        rw [hsum_dnf, downwardNormalizingFactor_edgeType F',
          isomorphismCount_eq_card_pairs M.out F' q₀ hq₀]
        push_cast
        rw [div_div_div_cancel_right₀]
        · ring
        · exact ne_of_gt hD
    _ = (1 / ((adjPairs M.out).card : ℝ)) * ∑ F' ∈ labelExtensions M edgeType,
          ∑ q ∈ (adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F'),
            Ψ (densityEval g ⟨ℓ + 2, pairFlag M.out q⟩) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro F' _
        congr 1
        have hconst : ∀ q ∈ (adjPairs M.out).attach.filter
            (fun q => pairFlag M.out q = F'),
            Ψ (densityEval g ⟨ℓ + 2, pairFlag M.out q⟩)
              = Ψ (densityEvalFun g
                  (funFromFlagWithSizeToFlagDensitySpace edgeType (ℓ + 2) F')) := by
          intro q hq
          rw [Finset.mem_filter] at hq
          rw [← hq.2, densityEvalFun_emp]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    _ = (1 / ((adjPairs M.out).card : ℝ))
          * ∑ q ∈ (adjPairs M.out).attach,
              Ψ (densityEval g ⟨ℓ + 2, pairFlag M.out q⟩) := by
        congr 1
        have hpd : Set.PairwiseDisjoint
            ((↑(labelExtensions M edgeType) : Set (FlagWithSize edgeType (ℓ + 2))))
            (fun F' => (adjPairs M.out).attach.filter
              (fun q => pairFlag M.out q = F')) := by
          intro F₁ h₁ F₂ h₂ hne
          exact hdisj F₁ h₁ F₂ h₂ hne
        conv_rhs => rw [hpart]
        rw [Finset.sum_biUnion hpd]

/-- Sigma-generic wrapper of the pair-average identity. -/
theorem integral_toMeasure_eq_pair_average' (G : FinFlag ∅ₜ) (h2 : 2 ≤ G.1)
    (hG : flagDensity₁ edgeType.toEmptyTypeFlag G.2 > 0)
    (g : FlagVector edgeType)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) {c : ℝ}
    (hΨb : ∀ a : FlagDensitySpace edgeType, |Ψ (densityEvalFun g a)| ≤ c)
    : ∫ a, Ψ (densityEvalFun g a) ∂(G.toMeasure hG)
      = (1 / ((adjPairs G.2.out).card : ℝ))
          * ∑ q ∈ (adjPairs G.2.out).attach,
              Ψ (densityEval g ⟨G.1, pairFlag G.2.out q⟩)
  := by
  obtain ⟨L, M⟩ := G
  dsimp only at h2 hG ⊢
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, L = ℓ + 2 := ⟨L - 2, by omega⟩
  exact integral_toMeasure_eq_pair_average M hG g Ψ hΨm hΨb

/-! ## Deleting a set of edges -/

/-- The host with the (unordered images of the) pairs in `D` removed. -/
noncomputable def deleteEdgeSet {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (D : Finset (Fin L × Fin L)) : LabeledGraph ∅ₜ (Fin L) where
  graph := N.graph.deleteEdges ↑(D.image (fun p => s(p.1, p.2)))
  type_embed := RelEmbedding.ofIsEmpty _ _

theorem deleteEdgeSet_adj {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (D : Finset (Fin L × Fin L)) (u w : Fin L)
    : (deleteEdgeSet N D).graph.Adj u w
      ↔ N.graph.Adj u w ∧ ∀ p ∈ D, s(p.1, p.2) ≠ s(u, w)
  := by
  dsimp only [deleteEdgeSet]
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro p hp hc
    apply h2
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨p, hp, hc⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [Finset.mem_coe, Finset.mem_image] at hc
    obtain ⟨p, hp, hpc⟩ := hc
    exact h2 p hp hpc

theorem deleteEdgeSet_empty {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    : deleteEdgeSet N ∅ = N := by
  apply emptyType_labeledGraph_ext
  ext u w
  rw [deleteEdgeSet_adj]
  simp only [Finset.notMem_empty, ne_eq, false_implies, implies_true, and_true]

theorem deleteEdgeSet_insert {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (D : Finset (Fin L × Fin L)) (p : Fin L × Fin L)
    : deleteEdgeSet N (insert p D) = deleteEdge (deleteEdgeSet N D) s(p.1, p.2)
  := by
  apply emptyType_labeledGraph_ext
  ext u w
  rw [deleteEdgeSet_adj, deleteEdge_adj, deleteEdgeSet_adj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun q hq => h2 q (Finset.mem_insert_of_mem hq)⟩,
      fun hc => h2 p (Finset.mem_insert_self p D) hc.symm⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact fun hc => h3 hc.symm
    · exact h2 q hq'

theorem deleteEdgeSet_adj_of_adj {L : ℕ} {N : LabeledGraph ∅ₜ (Fin L)}
    {D : Finset (Fin L × Fin L)} {u w : Fin L}
    (h : (deleteEdgeSet N D).graph.Adj u w) : N.graph.Adj u w :=
  ((deleteEdgeSet_adj N D u w).mp h).1

/-! ## Counting supersets -/

/-- The number of `k`-element subsets containing a fixed `T`. -/
theorem card_supersets {L : ℕ} (T : Finset (Fin L)) {k : ℕ} (hT : T.card ≤ k)
    : ({S' : Set (Fin L) | S'.toFinset.card = k ∧ ∀ x ∈ T, x ∈ S'}).toFinset.card
      = (L - T.card).choose (k - T.card)
  := by
  have hcard : ((Finset.univ : Finset (Fin L)) \ T).card = L - T.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ T),
      Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← Finset.card_powersetCard]
  apply Finset.card_bij (fun (S' : Set (Fin L)) (_ : S' ∈ _) => S'.toFinset \ T)
  · intro S' hS'
    rw [Set.mem_toFinset, Set.mem_setOf_eq] at hS'
    obtain ⟨hSc, hTS⟩ := hS'
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ x, hx.2⟩
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr ?_, hSc]
      intro x hx
      rw [Set.mem_toFinset]
      exact hTS x hx
  · intro S₁ h₁ S₂ h₂ heq
    rw [Set.mem_toFinset, Set.mem_setOf_eq] at h₁ h₂
    have hT₁ : T ⊆ S₁.toFinset := fun x hx => Set.mem_toFinset.mpr (h₁.2 x hx)
    have hT₂ : T ⊆ S₂.toFinset := fun x hx => Set.mem_toFinset.mpr (h₂.2 x hx)
    have hfin : S₁.toFinset = S₂.toFinset := by
      calc S₁.toFinset = (S₁.toFinset \ T) ∪ T := by
            rw [Finset.sdiff_union_of_subset hT₁]
        _ = (S₂.toFinset \ T) ∪ T := by rw [heq]
        _ = S₂.toFinset := Finset.sdiff_union_of_subset hT₂
    have h9 := congrArg (fun s : Finset (Fin L) => (↑s : Set (Fin L))) hfin
    simpa using h9
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    obtain ⟨hUsub, hUcard⟩ := hU
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      have h9 := hUsub hx
      rw [Finset.mem_sdiff] at h9
      exact h9.2 hxT
    refine ⟨(↑(U ∪ T) : Set (Fin L)), ?_, ?_⟩
    · rw [Set.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rw [Finset.toFinset_coe, Finset.card_union_of_disjoint hdisj, hUcard]
        omega
      · intro x hx
        rw [Finset.mem_coe]
        exact Finset.mem_union_right U hx
    · rw [Finset.toFinset_coe, Finset.union_sdiff_right,
        Finset.sdiff_eq_self_of_disjoint hdisj]

/-- No `k`-element subset contains a larger `T`. -/
theorem card_supersets_zero {L : ℕ} (T : Finset (Fin L)) {k : ℕ} (hT : k < T.card)
    : ({S' : Set (Fin L) | S'.toFinset.card = k ∧ ∀ x ∈ T, x ∈ S'}).toFinset.card = 0
  := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro S' hS'
  rw [Set.mem_toFinset, Set.mem_setOf_eq] at hS'
  obtain ⟨hSc, hTS⟩ := hS'
  have h1 : T ⊆ S'.toFinset := fun x hx => Set.mem_toFinset.mpr (hTS x hx)
  have h2 := Finset.card_le_card h1
  omega

/-! ## The pair-hitting estimate -/

/-- Every inducing subset of an edge-rooted host contains both roots and has
the right size. -/
theorem inducingSubsets_edgeRooted_mem {L : ℕ} (X : LabeledGraph ∅ₜ (Fin L))
    (v₁ v₂ : Fin L) (h : X.graph.Adj v₁ v₂) {kF : ℕ} (F : FlagWithSize edgeType kF)
    (S' : Set (Fin L)) (hS' : S' ∈ inducingSubsets F.out (edgeRootedAt X v₁ v₂ h))
    : v₁ ∈ S' ∧ v₂ ∈ S' ∧ S'.toFinset.card = kF
  := by
  obtain ⟨hsub, ⟨ψ⟩⟩ := hS'
  refine ⟨hsub ((edgeRootedAt X v₁ v₂ h).type_verts_contain 0),
    hsub ((edgeRootedAt X v₁ v₂ h).type_verts_contain 1), ?_⟩
  have hsz := labeledGraphIso_size_eq _ _ ψ
  simp only [LabeledGraph.size, Fintype.card_fin] at hsz
  rw [Set.toFinset_card]
  exact hsz

/-- The induced rooted subgraphs of the original and edge-deleted hosts agree
on subsets containing no deleted pair. -/
noncomputable def deleteEdgeSet_induce_iso_of_avoiding {L : ℕ}
    (N : LabeledGraph ∅ₜ (Fin L)) (D : Finset (Fin L × Fin L)) (v₁ v₂ : Fin L)
    (h₁ : N.graph.Adj v₁ v₂) (h₂ : (deleteEdgeSet N D).graph.Adj v₁ v₂)
    (S' : Set (Fin L)) (havoid : ∀ p ∈ D, ¬(p.1 ∈ S' ∧ p.2 ∈ S'))
    (hsub₁ : (edgeRootedAt N v₁ v₂ h₁).type_verts ⊆ S')
    (hsub₂ : (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂).type_verts ⊆ S')
    : (LabeledSubgraph.inducedLabeledSubgraph (edgeRootedAt N v₁ v₂ h₁) S' hsub₁).coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph
          (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂) S' hsub₂).coe where
  graph_iso := {
    toEquiv := Equiv.refl _
    map_rel_iff' := by
      intro a b
      constructor
      · rintro ⟨ha, hb, hadj⟩
        exact ⟨a.property, b.property, ((deleteEdgeSet_adj N D _ _).mp hadj).1⟩
      · rintro ⟨ha, hb, hadj⟩
        refine ⟨a.property, b.property, (deleteEdgeSet_adj N D _ _).mpr ⟨hadj, ?_⟩⟩
        intro p hp heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact havoid p hp ⟨h1 ▸ a.property, h2 ▸ b.property⟩
        · exact havoid p hp ⟨h1 ▸ b.property, h2 ▸ a.property⟩
  }
  type_preserve := by
    funext t
    rfl

/-- Membership in the inducing subsets is unchanged by deleting edges the
subset avoids. -/
theorem mem_inducingSubsets_deleteEdgeSet_iff {L : ℕ}
    (N : LabeledGraph ∅ₜ (Fin L)) (D : Finset (Fin L × Fin L)) (v₁ v₂ : Fin L)
    (h₁ : N.graph.Adj v₁ v₂) (h₂ : (deleteEdgeSet N D).graph.Adj v₁ v₂)
    {kF : ℕ} (F : FlagWithSize edgeType kF)
    (S' : Set (Fin L)) (havoid : ∀ p ∈ D, ¬(p.1 ∈ S' ∧ p.2 ∈ S'))
    : S' ∈ inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)
      ↔ S' ∈ inducingSubsets F.out (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)
  := by
  constructor
  · rintro ⟨hsub, ⟨ψ⟩⟩
    have hsub₂ : (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂).type_verts ⊆ S' :=
      edgeRootedAt_type_verts_subset _ h₂
        (hsub ((edgeRootedAt N v₁ v₂ h₁).type_verts_contain 0))
        (hsub ((edgeRootedAt N v₁ v₂ h₁).type_verts_contain 1))
    exact ⟨hsub₂, ⟨((deleteEdgeSet_induce_iso_of_avoiding N D v₁ v₂ h₁ h₂ S'
      havoid hsub hsub₂).symm).trans ψ⟩⟩
  · rintro ⟨hsub, ⟨ψ⟩⟩
    have hsub₁ : (edgeRootedAt N v₁ v₂ h₁).type_verts ⊆ S' :=
      edgeRootedAt_type_verts_subset _ h₁
        (hsub ((edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂).type_verts_contain 0))
        (hsub ((edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂).type_verts_contain 1))
    exact ⟨hsub₁, ⟨(deleteEdgeSet_induce_iso_of_avoiding N D v₁ v₂ h₁ h₂ S'
      havoid hsub₁ hsub).trans ψ⟩⟩

end Differential
end FlagAlgebras
