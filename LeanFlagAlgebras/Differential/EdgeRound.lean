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

/-- **The pair-hitting estimate**: deleting a set `D` of pairs lying inside a
vertex set `S` moves any `E`-rooted `kF`-flag density at a surviving edge by
at most `kF·|S|/(L−2) + kF²·|D|/((L−2)(L−3))`. -/
theorem pair_hitting_density {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (D : Finset (Fin L × Fin L)) (S : Finset (Fin L)) (v₁ v₂ : Fin L)
    (h₁ : N.graph.Adj v₁ v₂) (h₂ : (deleteEdgeSet N D).graph.Adj v₁ v₂)
    {kF : ℕ} (F : FlagWithSize edgeType kF) (hkF : 2 ≤ kF)
    (hL : 4 ≤ L) (hkL : kF ≤ L)
    (hDadj : ∀ p ∈ D, N.graph.Adj p.1 p.2)
    (hDS : ∀ p ∈ D, p.1 ∈ S ∧ p.2 ∈ S)
    : |(flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℝ)
        - (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : Flag edgeType (Fin L)) : ℝ)|
      ≤ (kF : ℝ) * S.card / ((L : ℝ) - 2)
        + (kF : ℝ) * (kF : ℝ) * D.card / (((L : ℝ) - 2) * ((L : ℝ) - 3))
  := by
  have hLr : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hd2 : (0:ℝ) < (L : ℝ) - 2 := by linarith
  have hd3 : (0:ℝ) < (L : ℝ) - 3 := by linarith
  -- the trivial two-vertex case
  rcases Nat.lt_or_ge kF 3 with hk2 | hk3
  · have hkF2 : kF = 2 := by omega
    subst hkF2
    have hF : F = emptyFlag edgeType := Subsingleton.elim _ _
    rw [hF, flagDensity_empty, flagDensity_empty]
    have h9 : (0:ℝ) ≤ (2 : ℕ) * (S.card : ℝ) / ((L : ℝ) - 2)
        + (2 : ℕ) * (2 : ℕ) * (D.card : ℝ) / (((L : ℝ) - 2) * ((L : ℝ) - 3)) := by
      positivity
    simpa using h9
  -- densities as counts over the same denominator
  have hden : (0 : ℚ) < (((L - 2).choose (kF - 2) : ℕ) : ℚ) := by
    have h9 : 0 < (L - 2).choose (kF - 2) := Nat.choose_pos (by omega)
    exact_mod_cast h9
  have hp : (flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℚ)
      = ((inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)).toFinset.card : ℚ)
        / (((L - 2).choose (kF - 2) : ℕ) : ℚ) := by
    conv_lhs => rw [← Quotient.out_eq F]
    rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div]
    simp only [Fintype.card_fin]
  have hp' : (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
        : Flag edgeType (Fin L)) : ℚ)
      = ((inducingSubsets F.out
            (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)).toFinset.card : ℚ)
        / (((L - 2).choose (kF - 2) : ℕ) : ℚ) := by
    conv_lhs => rw [← Quotient.out_eq F]
    rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div]
    simp only [Fintype.card_fin]
  set avoidP : Set (Fin L) → Prop := fun S' => ∀ p ∈ D, ¬(p.1 ∈ S' ∧ p.2 ∈ S')
    with havoidP
  have hAA' : (inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)).toFinset.filter avoidP
      = (inducingSubsets F.out
          (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)).toFinset.filter avoidP := by
    apply Finset.ext
    intro S'
    rw [Finset.mem_filter, Finset.mem_filter, Set.mem_toFinset, Set.mem_toFinset]
    constructor
    · rintro ⟨hmem, hav⟩
      exact ⟨(mem_inducingSubsets_deleteEdgeSet_iff N D v₁ v₂ h₁ h₂ F S' hav).mp hmem, hav⟩
    · rintro ⟨hmem, hav⟩
      exact ⟨(mem_inducingSubsets_deleteEdgeSet_iff N D v₁ v₂ h₁ h₂ F S' hav).mpr hmem, hav⟩
  set HitOne : Finset (Set (Fin L)) := (S \ {v₁, v₂}).biUnion (fun x =>
      ({S' : Set (Fin L) | S'.toFinset.card = kF
        ∧ ∀ y ∈ insert v₁ (insert v₂ ({x} : Finset (Fin L))), y ∈ S'}).toFinset)
    with hHitOne
  set HitTwo : Finset (Set (Fin L)) := (D.filter (fun p =>
      ¬p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∧ ¬p.2 ∈ ({v₁, v₂} : Finset (Fin L)))).biUnion
      (fun p => ({S' : Set (Fin L) | S'.toFinset.card = kF
        ∧ ∀ y ∈ insert v₁ (insert v₂ (insert p.1 ({p.2} : Finset (Fin L)))), y ∈ S'}).toFinset)
    with hHitTwo
  -- every non-avoiding inducing subset of either host is a hitting subset
  have hhit : ∀ {X : LabeledGraph ∅ₜ (Fin L)} (hX : X.graph.Adj v₁ v₂)
      (S' : Set (Fin L)), S' ∈ inducingSubsets F.out (edgeRootedAt X v₁ v₂ hX) →
      ¬avoidP S' → S' ∈ HitOne ∪ HitTwo := by
    intro X hX S' hmem hnav
    obtain ⟨hv₁S, hv₂S, hcard⟩ := inducingSubsets_edgeRooted_mem X v₁ v₂ hX F S' hmem
    rw [havoidP, not_forall] at hnav
    obtain ⟨p, hnp⟩ := hnav
    rw [Classical.not_imp, not_not] at hnp
    obtain ⟨hpD, hp1, hp2⟩ := hnp
    have hpair : s(p.1, p.2) ≠ s(v₁, v₂) := ((deleteEdgeSet_adj N D v₁ v₂).mp h₂).2 p hpD
    have hpne : p.1 ≠ p.2 := (hDadj p hpD).ne
    rw [Finset.mem_union]
    by_cases htouch : p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∨ p.2 ∈ ({v₁, v₂} : Finset (Fin L))
    · left
      rw [hHitOne, Finset.mem_biUnion]
      rcases htouch with ht | ht
      · rw [Finset.mem_insert, Finset.mem_singleton] at ht
        refine ⟨p.2, ?_, ?_⟩
        · rw [Finset.mem_sdiff]
          refine ⟨(hDS p hpD).2, ?_⟩
          intro hc
          rw [Finset.mem_insert, Finset.mem_singleton] at hc
          apply hpair
          rcases ht with ht' | ht' <;> rcases hc with hc' | hc'
          · exact absurd (ht'.trans hc'.symm) hpne
          · rw [ht', hc']
          · rw [ht', hc']
            exact Sym2.eq_swap
          · exact absurd (ht'.trans hc'.symm) hpne
        · rw [Set.mem_toFinset, Set.mem_setOf_eq]
          refine ⟨hcard, ?_⟩
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact hv₁S
          · exact hv₂S
          · exact hp2
      · rw [Finset.mem_insert, Finset.mem_singleton] at ht
        refine ⟨p.1, ?_, ?_⟩
        · rw [Finset.mem_sdiff]
          refine ⟨(hDS p hpD).1, ?_⟩
          intro hc
          rw [Finset.mem_insert, Finset.mem_singleton] at hc
          apply hpair
          rcases hc with hc' | hc' <;> rcases ht with ht' | ht'
          · exact absurd (hc'.trans ht'.symm) hpne
          · rw [hc', ht']
          · rw [hc', ht']
            exact Sym2.eq_swap
          · exact absurd (hc'.trans ht'.symm) hpne
        · rw [Set.mem_toFinset, Set.mem_setOf_eq]
          refine ⟨hcard, ?_⟩
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact hv₁S
          · exact hv₂S
          · exact hp1
    · right
      push_neg at htouch
      rw [hHitTwo, Finset.mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨hpD, htouch.1, htouch.2⟩
      · rw [Set.mem_toFinset, Set.mem_setOf_eq]
        refine ⟨hcard, ?_⟩
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hv₁S
        · exact hv₂S
        · exact hp1
        · exact hp2
  -- the sharing part of the hitting collection
  have hone : HitOne.card ≤ S.card * (L - 3).choose (kF - 3) := by
    rw [hHitOne]
    refine le_trans Finset.card_biUnion_le ?_
    have h9 : ∀ x ∈ S \ ({v₁, v₂} : Finset (Fin L)),
        ({S' : Set (Fin L) | S'.toFinset.card = kF
          ∧ ∀ y ∈ insert v₁ (insert v₂ ({x} : Finset (Fin L))), y ∈ S'}).toFinset.card
        = (L - 3).choose (kF - 3) := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx
      push_neg at hx
      have hc3 : (insert v₁ (insert v₂ ({x} : Finset (Fin L)))).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_singleton]
        · rw [Finset.mem_singleton]
          exact fun hc => hx.2.2 hc.symm
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨h₁.ne, fun hc => hx.2.1 hc.symm⟩
      rw [card_supersets _ (by omega : (insert v₁ (insert v₂
        ({x} : Finset (Fin L)))).card ≤ kF), hc3]
    calc ∑ x ∈ S \ ({v₁, v₂} : Finset (Fin L)),
          ({S' : Set (Fin L) | S'.toFinset.card = kF
            ∧ ∀ y ∈ insert v₁ (insert v₂ ({x} : Finset (Fin L))), y ∈ S'}).toFinset.card
        = ∑ _x ∈ S \ ({v₁, v₂} : Finset (Fin L)), (L - 3).choose (kF - 3) :=
          Finset.sum_congr rfl h9
      _ = (S \ ({v₁, v₂} : Finset (Fin L))).card * (L - 3).choose (kF - 3) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ S.card * (L - 3).choose (kF - 3) := by
          apply Nat.mul_le_mul_right
          exact Finset.card_le_card Finset.sdiff_subset
  -- the four-vertex sets of the disjoint part
  have hc4 : ∀ p ∈ D.filter (fun p =>
      ¬p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∧ ¬p.2 ∈ ({v₁, v₂} : Finset (Fin L))),
      (insert v₁ (insert v₂ (insert p.1 ({p.2} : Finset (Fin L))))).card = 4 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpD, hp1, hp2⟩ := hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
    push_neg at hp1 hp2
    have hpne : p.1 ≠ p.2 := (hDadj p hpD).ne
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · rw [Finset.mem_singleton]
      exact hpne
    · rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun hc => hp1.2 hc.symm, fun hc => hp2.2 hc.symm⟩
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨h₁.ne, fun hc => hp1.1 hc.symm, fun hc => hp2.1 hc.symm⟩
  -- count difference is at most the hitting count
  set A : ℕ := (inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)).toFinset.card with hA
  set A' : ℕ := (inducingSubsets F.out
      (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)).toFinset.card with hA'
  have hdiff : |(A : ℚ) - (A' : ℚ)| ≤ ((HitOne ∪ HitTwo).card : ℚ) := by
    have hsplit₁ := Finset.card_filter_add_card_filter_not
      (s := (inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)).toFinset) avoidP
    have hsplit₂ := Finset.card_filter_add_card_filter_not
      (s := (inducingSubsets F.out
        (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)).toFinset) avoidP
    have hb₁ : ((inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)).toFinset.filter
        (fun S' => ¬avoidP S')).card ≤ (HitOne ∪ HitTwo).card := by
      apply Finset.card_le_card
      intro S' hS'
      rw [Finset.mem_filter, Set.mem_toFinset] at hS'
      exact hhit h₁ S' hS'.1 hS'.2
    have hb₂ : ((inducingSubsets F.out
        (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)).toFinset.filter
        (fun S' => ¬avoidP S')).card ≤ (HitOne ∪ HitTwo).card := by
      apply Finset.card_le_card
      intro S' hS'
      rw [Finset.mem_filter, Set.mem_toFinset] at hS'
      exact hhit h₂ S' hS'.1 hS'.2
    have h9 : ((inducingSubsets F.out (edgeRootedAt N v₁ v₂ h₁)).toFinset.filter
        avoidP).card = ((inducingSubsets F.out
          (edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂)).toFinset.filter avoidP).card := by
      rw [hAA']
    rw [abs_le]
    constructor
    · exact_mod_cast (by omega : -(((HitOne ∪ HitTwo).card : ℕ) : ℤ) ≤ (A : ℤ) - A')
    · exact_mod_cast (by omega : (A : ℤ) - (A' : ℤ) ≤ ((HitOne ∪ HitTwo).card : ℕ))
  -- assemble, splitting on the flag size
  rcases Nat.lt_or_ge kF 4 with hk3' | hk4
  · -- `kF = 3`: no subset contains a root-disjoint deleted pair
    have hkF3 : kF = 3 := by omega
    subst hkF3
    have htwo0 : HitTwo.card = 0 := by
      rw [hHitTwo]
      apply Nat.le_zero.mp
      refine le_trans Finset.card_biUnion_le (le_of_eq ?_)
      apply Finset.sum_eq_zero
      intro p hp
      apply card_supersets_zero
      rw [hc4 p hp]
      omega
    have hone' : ((HitOne ∪ HitTwo).card : ℚ) ≤ (S.card : ℚ) := by
      have h9 := Finset.card_union_le HitOne HitTwo
      have h10 : (L - 3).choose (3 - 3) = 1 := by
        norm_num
      rw [h10, mul_one] at hone
      exact_mod_cast (by omega : (HitOne ∪ HitTwo).card ≤ S.card)
    have hC2 : (((L - 2).choose (3 - 2) : ℕ) : ℚ) = (L : ℚ) - 2 := by
      have h9 : (3:ℕ) - 2 = 1 := by norm_num
      rw [h9, Nat.choose_one_right, Nat.cast_sub (by omega : 2 ≤ L)]
      norm_num
    have hQ : |(flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℚ)
        - (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : Flag edgeType (Fin L)) : ℚ)|
        ≤ (S.card : ℚ) / ((L : ℚ) - 2) := by
      rw [hp, hp', div_sub_div_same, abs_div, abs_of_pos hden]
      rw [← hC2] at *
      apply div_le_div_of_nonneg_right ?_ (le_of_lt hden)
      exact le_trans hdiff hone'
    have hRcast : |(flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℝ)
        - (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : Flag edgeType (Fin L)) : ℝ)|
        ≤ (((S.card : ℚ) / ((L : ℚ) - 2) : ℚ) : ℝ) := by
      rw [← Rat.cast_sub, ← Rat.cast_abs]
      exact_mod_cast hQ
    refine le_trans hRcast ?_
    push_cast
    have h10 : (S.card : ℝ) / ((L : ℝ) - 2) ≤ 3 * (S.card : ℝ) / ((L : ℝ) - 2) := by
      apply div_le_div_of_nonneg_right ?_ hd2.le
      nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
    have h11 : (0:ℝ) ≤ 3 * 3 * (D.card : ℝ) / (((L : ℝ) - 2) * ((L : ℝ) - 3)) := by
      positivity
    linarith
  · -- `kF ≥ 4`: both binomial identities are exact
    have htwo : HitTwo.card ≤ D.card * (L - 4).choose (kF - 4) := by
      rw [hHitTwo]
      refine le_trans Finset.card_biUnion_le ?_
      have h9 : ∀ p ∈ D.filter (fun p =>
          ¬p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∧ ¬p.2 ∈ ({v₁, v₂} : Finset (Fin L))),
          ({S' : Set (Fin L) | S'.toFinset.card = kF
            ∧ ∀ y ∈ insert v₁ (insert v₂ (insert p.1 ({p.2} : Finset (Fin L)))),
              y ∈ S'}).toFinset.card = (L - 4).choose (kF - 4) := by
        intro p hp
        rw [card_supersets _ (by rw [hc4 p hp]; omega), hc4 p hp]
      calc ∑ p ∈ D.filter (fun p =>
            ¬p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∧ ¬p.2 ∈ ({v₁, v₂} : Finset (Fin L))),
            ({S' : Set (Fin L) | S'.toFinset.card = kF
              ∧ ∀ y ∈ insert v₁ (insert v₂ (insert p.1 ({p.2} : Finset (Fin L)))),
                y ∈ S'}).toFinset.card
          = ∑ _p ∈ D.filter (fun p =>
              ¬p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∧ ¬p.2 ∈ ({v₁, v₂} : Finset (Fin L))),
              (L - 4).choose (kF - 4) := Finset.sum_congr rfl h9
        _ = (D.filter (fun p =>
            ¬p.1 ∈ ({v₁, v₂} : Finset (Fin L)) ∧ ¬p.2 ∈ ({v₁, v₂} : Finset (Fin L)))).card
              * (L - 4).choose (kF - 4) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ D.card * (L - 4).choose (kF - 4) := by
            apply Nat.mul_le_mul_right
            exact Finset.card_filter_le _ _
    -- the ℚ-level bound with both terms
    have hQ : |(flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℚ)
        - (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : Flag edgeType (Fin L)) : ℚ)|
        ≤ ((S.card : ℚ) * ((L - 3).choose (kF - 3) : ℕ)
            + (D.card : ℚ) * ((L - 4).choose (kF - 4) : ℕ))
          / (((L - 2).choose (kF - 2) : ℕ) : ℚ) := by
      rw [hp, hp', div_sub_div_same, abs_div, abs_of_pos hden]
      apply div_le_div_of_nonneg_right ?_ (le_of_lt hden)
      refine le_trans hdiff ?_
      have h9 : ((HitOne ∪ HitTwo).card : ℚ)
          ≤ ((S.card * (L - 3).choose (kF - 3)
              + D.card * (L - 4).choose (kF - 4) : ℕ) : ℚ) := by
        have h10 := Finset.card_union_le HitOne HitTwo
        exact_mod_cast (by omega : (HitOne ∪ HitTwo).card
          ≤ S.card * (L - 3).choose (kF - 3) + D.card * (L - 4).choose (kF - 4))
      refine le_trans h9 (le_of_eq ?_)
      push_cast
      ring
    -- binomial identities
    have e2 : kF - 2 = (kF - 3) + 1 := by omega
    have e3 : kF - 3 = (kF - 4) + 1 := by omega
    have hidn₁ : (L - 2) * (L - 3).choose (kF - 3)
        = (L - 2).choose (kF - 2) * (kF - 2) := by
      have h9 : L - 3 + 1 = L - 2 := by omega
      have h10 := Nat.add_one_mul_choose_eq (L - 3) (kF - 3)
      rw [h9] at h10
      rw [e2]
      exact h10
    have hidn₂ : (L - 3) * (L - 4).choose (kF - 4)
        = (L - 3).choose (kF - 3) * (kF - 3) := by
      have h9 : L - 4 + 1 = L - 3 := by omega
      have h10 := Nat.add_one_mul_choose_eq (L - 4) (kF - 4)
      rw [h9] at h10
      rw [e3]
      exact h10
    have hcast2 : ((L - 2 : ℕ) : ℚ) = (L : ℚ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ L)]
      norm_num
    have hcast3 : ((L - 3 : ℕ) : ℚ) = (L : ℚ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ L)]
      norm_num
    have hd2q : (0:ℚ) < (L : ℚ) - 2 := by
      have h9 : (4:ℚ) ≤ (L : ℚ) := by exact_mod_cast hL
      linarith
    have hd3q : (0:ℚ) < (L : ℚ) - 3 := by
      have h9 : (4:ℚ) ≤ (L : ℚ) := by exact_mod_cast hL
      linarith
    have hkF2q : ((kF - 2 : ℕ) : ℚ) ≤ (kF : ℚ) := by
      exact_mod_cast Nat.sub_le kF 2
    have hkF3q : ((kF - 3 : ℕ) : ℚ) ≤ (kF : ℚ) := by
      exact_mod_cast Nat.sub_le kF 3
    have hq₁ : ((L : ℚ) - 2) * ((L - 3).choose (kF - 3) : ℕ)
        = (((L - 2).choose (kF - 2) : ℕ) : ℚ) * ((kF - 2 : ℕ) : ℚ) := by
      rw [← hcast2]
      exact_mod_cast hidn₁
    have hq₂ : ((L : ℚ) - 3) * ((L - 4).choose (kF - 4) : ℕ)
        = (((L - 3).choose (kF - 3) : ℕ) : ℚ) * ((kF - 3 : ℕ) : ℚ) := by
      rw [← hcast3]
      exact_mod_cast hidn₂
    -- the two ratio bounds
    have ht1 : (S.card : ℚ) * ((L - 3).choose (kF - 3) : ℕ)
        / (((L - 2).choose (kF - 2) : ℕ) : ℚ)
        ≤ (kF : ℚ) * S.card / ((L : ℚ) - 2) := by
      rw [div_le_div_iff₀ hden hd2q]
      calc (S.card : ℚ) * ((L - 3).choose (kF - 3) : ℕ) * ((L : ℚ) - 2)
          = (S.card : ℚ) * (((L : ℚ) - 2) * ((L - 3).choose (kF - 3) : ℕ)) := by ring
        _ = (S.card : ℚ) * ((((L - 2).choose (kF - 2) : ℕ) : ℚ) * ((kF - 2 : ℕ) : ℚ)) := by
            rw [hq₁]
        _ ≤ (S.card : ℚ) * ((((L - 2).choose (kF - 2) : ℕ) : ℚ) * (kF : ℚ)) := by
            apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left hkF2q (Nat.cast_nonneg _)
        _ = (kF : ℚ) * S.card * (((L - 2).choose (kF - 2) : ℕ) : ℚ) := by ring
    have ht2 : (D.card : ℚ) * ((L - 4).choose (kF - 4) : ℕ)
        / (((L - 2).choose (kF - 2) : ℕ) : ℚ)
        ≤ (kF : ℚ) * (kF : ℚ) * D.card / (((L : ℚ) - 2) * ((L : ℚ) - 3)) := by
      rw [div_le_div_iff₀ hden (mul_pos hd2q hd3q)]
      calc (D.card : ℚ) * ((L - 4).choose (kF - 4) : ℕ)
            * (((L : ℚ) - 2) * ((L : ℚ) - 3))
          = (D.card : ℚ) * (((L : ℚ) - 2)
              * (((L : ℚ) - 3) * ((L - 4).choose (kF - 4) : ℕ))) := by ring
        _ = (D.card : ℚ) * (((L : ℚ) - 2)
              * ((((L - 3).choose (kF - 3) : ℕ) : ℚ) * ((kF - 3 : ℕ) : ℚ))) := by
            rw [hq₂]
        _ = (D.card : ℚ) * ((kF - 3 : ℕ) : ℚ)
              * (((L : ℚ) - 2) * (((L - 3).choose (kF - 3) : ℕ) : ℚ)) := by ring
        _ = (D.card : ℚ) * ((kF - 3 : ℕ) : ℚ)
              * ((((L - 2).choose (kF - 2) : ℕ) : ℚ) * ((kF - 2 : ℕ) : ℚ)) := by
            rw [hq₁]
        _ ≤ (D.card : ℚ) * (kF : ℚ)
              * ((((L - 2).choose (kF - 2) : ℕ) : ℚ) * (kF : ℚ)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hkF3q (Nat.cast_nonneg _)
            · exact mul_le_mul_of_nonneg_left hkF2q (Nat.cast_nonneg _)
            · positivity
            · positivity
        _ = (kF : ℚ) * (kF : ℚ) * D.card * (((L - 2).choose (kF - 2) : ℕ) : ℚ) := by
            ring
    -- combine and cast
    have hQ2 : |(flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℚ)
        - (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : Flag edgeType (Fin L)) : ℚ)|
        ≤ (kF : ℚ) * S.card / ((L : ℚ) - 2)
          + (kF : ℚ) * (kF : ℚ) * D.card / (((L : ℚ) - 2) * ((L : ℚ) - 3)) := by
      refine le_trans hQ ?_
      rw [add_div]
      exact add_le_add ht1 ht2
    have hRcast : |(flagDensity₁ F (⟦edgeRootedAt N v₁ v₂ h₁⟧ : Flag edgeType (Fin L)) : ℝ)
        - (flagDensity₁ F (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : Flag edgeType (Fin L)) : ℝ)|
        ≤ (((kF : ℚ) * S.card / ((L : ℚ) - 2)
            + (kF : ℚ) * (kF : ℚ) * D.card / (((L : ℚ) - 2) * ((L : ℚ) - 3)) : ℚ) : ℝ) := by
      rw [← Rat.cast_sub, ← Rat.cast_abs]
      exact_mod_cast hQ2
    refine le_trans hRcast (le_of_eq ?_)
    push_cast
    ring

/-- Vector version of the pair-hitting estimate. -/
theorem pair_hitting_eval {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (D : Finset (Fin L × Fin L)) (S : Finset (Fin L)) (v₁ v₂ : Fin L)
    (h₁ : N.graph.Adj v₁ v₂) (h₂ : (deleteEdgeSet N D).graph.Adj v₁ v₂)
    (g : FlagVector edgeType) {K : ℕ}
    (hK : ∀ F ∈ g.support, F.1 ≤ K + 2)
    (hL : 4 ≤ L) (hKL : K + 2 ≤ L)
    (hDadj : ∀ p ∈ D, N.graph.Adj p.1 p.2)
    (hDS : ∀ p ∈ D, p.1 ∈ S ∧ p.2 ∈ S)
    : |densityEval g ⟨L, (⟦edgeRootedAt N v₁ v₂ h₁⟧ : FlagWithSize edgeType L)⟩
        - densityEval g ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : FlagWithSize edgeType L)⟩|
      ≤ (∑ F ∈ g.support, |g F|)
          * (((K : ℝ) + 2) * S.card / ((L : ℝ) - 2)
            + ((K : ℝ) + 2) * ((K : ℝ) + 2) * D.card
                / (((L : ℝ) - 2) * ((L : ℝ) - 3)))
  := by
  have hLr : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hd2 : (0:ℝ) < (L : ℝ) - 2 := by linarith
  have hd3 : (0:ℝ) < (L : ℝ) - 3 := by linarith
  dsimp only [densityEval, linearExtension]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ F ∈ g.support,
      |g F • ((flagDensity₁ F.2 (⟦edgeRootedAt N v₁ v₂ h₁⟧
          : FlagWithSize edgeType L) : ℝ))
        - g F • ((flagDensity₁ F.2 (⟦edgeRootedAt (deleteEdgeSet N D) v₁ v₂ h₂⟧
            : FlagWithSize edgeType L) : ℝ))|
      ≤ |g F| * (((K : ℝ) + 2) * S.card / ((L : ℝ) - 2)
          + ((K : ℝ) + 2) * ((K : ℝ) + 2) * D.card
              / (((L : ℝ) - 2) * ((L : ℝ) - 3))) := by
    intro F hF
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hkF : 2 ≤ F.1 := finFlag_size_ge_n₀ F
    have hkL : F.1 ≤ L := le_trans (hK F hF) hKL
    have h3 := pair_hitting_density N D S v₁ v₂ h₁ h₂ F.2 hkF hL hkL hDadj hDS
    refine le_trans h3 ?_
    have hKr : (F.1 : ℝ) ≤ (K : ℝ) + 2 := by exact_mod_cast hK F hF
    have hKnn : (0:ℝ) ≤ (K : ℝ) + 2 := by positivity
    apply add_le_add
    · apply div_le_div_of_nonneg_right ?_ hd2.le
      apply mul_le_mul_of_nonneg_right hKr (Nat.cast_nonneg _)
    · apply div_le_div_of_nonneg_right ?_ (le_of_lt (mul_pos hd2 hd3))
      apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      apply mul_le_mul hKr hKr ?_ hKnn
      exact_mod_cast Nat.zero_le F.1
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_))
  rw [← Finset.sum_mul]

/-! ## Choosing a dense vertex subset -/

/-- Finset version of the superset count. -/
theorem card_powersetCard_supersets {L : ℕ} (T : Finset (Fin L)) {s : ℕ}
    (hT : T.card ≤ s)
    : (((Finset.univ : Finset (Fin L)).powersetCard s).filter
        (fun S => ∀ x ∈ T, x ∈ S)).card
      = (L - T.card).choose (s - T.card)
  := by
  have hcard : ((Finset.univ : Finset (Fin L)) \ T).card = L - T.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ T),
      Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← Finset.card_powersetCard]
  apply Finset.card_bij (fun (S : Finset (Fin L)) (_ : S ∈ _) => S \ T)
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨-, hSc⟩, hTS⟩ := hS
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ x, hx.2⟩
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (fun x hx => hTS x hx), hSc]
  · intro S₁ h₁ S₂ h₂ heq
    rw [Finset.mem_filter] at h₁ h₂
    calc S₁ = (S₁ \ T) ∪ T := by
          rw [Finset.sdiff_union_of_subset (fun x hx => h₁.2 x hx)]
      _ = (S₂ \ T) ∪ T := by rw [heq]
      _ = S₂ := Finset.sdiff_union_of_subset (fun x hx => h₂.2 x hx)
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    obtain ⟨hUsub, hUcard⟩ := hU
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      have h9 := hUsub hx
      rw [Finset.mem_sdiff] at h9
      exact h9.2 hxT
    refine ⟨U ∪ T, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hUcard]
        omega
      · intro x hx
        exact Finset.mem_union_right U hx
    · rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hdisj]

/-- **The dense-subset selection**: some `s`-element vertex subset contains at
least the average number of bad pairs. -/
theorem exists_dense_subset {L : ℕ} (BadP : Finset (Fin L × Fin L))
    (hne : ∀ p ∈ BadP, p.1 ≠ p.2) (s : ℕ) (h2s : 2 ≤ s) (hsL : s ≤ L)
    : ∃ S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
        BadP.card * (L - 2).choose (s - 2)
          ≤ (BadP.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card * L.choose s
  := by
  -- the double count
  have hdc : ∑ S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
      (BadP.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card
      = BadP.card * (L - 2).choose (s - 2) := by
    have h1 : ∀ S : Finset (Fin L), (BadP.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card
        = ∑ p ∈ BadP, if p.1 ∈ S ∧ p.2 ∈ S then 1 else 0 :=
      fun S => Finset.card_filter _ _
    calc ∑ S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
          (BadP.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card
        = ∑ S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
            ∑ p ∈ BadP, if p.1 ∈ S ∧ p.2 ∈ S then 1 else 0 :=
          Finset.sum_congr rfl (fun S _ => h1 S)
      _ = ∑ p ∈ BadP, ∑ S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
            if p.1 ∈ S ∧ p.2 ∈ S then 1 else 0 := Finset.sum_comm
      _ = ∑ _p ∈ BadP, (L - 2).choose (s - 2) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Finset.card_filter]
          have hpc : ({p.1, p.2} : Finset (Fin L)).card = 2 := by
            rw [Finset.card_insert_of_notMem, Finset.card_singleton]
            rw [Finset.mem_singleton]
            exact hne p hp
          have h3 := card_powersetCard_supersets ({p.1, p.2} : Finset (Fin L))
            (by omega : ({p.1, p.2} : Finset (Fin L)).card ≤ s)
          rw [hpc] at h3
          rw [← h3]
          apply Finset.card_nbij id
          · intro S hS
            rw [Finset.mem_coe, Finset.mem_filter] at hS
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨hS.1, ?_⟩
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hS.2.1
            · exact hS.2.2
          · intro S₁ h₁ S₂ h₂ heq
            exact heq
          · intro S hS
            rw [Finset.mem_coe, Finset.mem_filter] at hS
            refine ⟨S, ?_, rfl⟩
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨hS.1, hS.2 p.1 ?_, hS.2 p.2 ?_⟩
            · rw [Finset.mem_insert]
              exact Or.inl rfl
            · rw [Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr rfl
      _ = BadP.card * (L - 2).choose (s - 2) := by
          rw [Finset.sum_const, smul_eq_mul]
  -- extract an above-average subset
  have hnonempty : ((Finset.univ : Finset (Fin L)).powersetCard s).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    rw [Finset.card_univ, Fintype.card_fin]
    exact hsL
  have hsum_le : ∑ _S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
      BadP.card * (L - 2).choose (s - 2)
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin L)).powersetCard s,
          (BadP.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card * L.choose s := by
    rw [Finset.sum_const, smul_eq_mul, ← Finset.sum_mul, hdc]
    have h9 : ((Finset.univ : Finset (Fin L)).powersetCard s).card = L.choose s := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [h9]
    ring_nf
    exact le_refl _
  obtain ⟨S, hS, hSle⟩ := Finset.exists_le_of_sum_le hnonempty hsum_le
  exact ⟨S, hS, hSle⟩

/-! ## The pair count equals the edge density -/

/-- The isomorphism counts of the label extensions sum to the ordered edge
count (extracted from the fibre partition). -/
theorem sum_isomorphismCount_eq_card_adjPairs {L : ℕ} (M : FlagWithSize ∅ₜ L)
    : ∑ F' ∈ labelExtensions M edgeType, isomorphismCount F'.out
      = (adjPairs M.out).card
  := by
  have hdisj : ∀ F₁ ∈ labelExtensions M edgeType,
      ∀ F₂ ∈ labelExtensions M edgeType, F₁ ≠ F₂ →
      Disjoint ((adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F₁))
        ((adjPairs M.out).attach.filter (fun q => pairFlag M.out q = F₂)) := by
    intro F₁ _ F₂ _ hne
    rw [Finset.disjoint_left]
    intro q h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact hne (h₁.2 ▸ h₂.2)
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

/-- The unlabelling weight of the minimal `E`-flag is `1`. -/
theorem downwardNormalizingFactor_emptyFlag_edgeType
    : downwardNormalizingFactor (emptyFlag edgeType) = 1
  := by
  have h9 := downwardNormalizingFactor_edgeType (ℓ := 0) (emptyFlag edgeType)
  rw [h9]
  -- the isomorphism count of the two-vertex edge flag is `2`
  set X : LabeledGraph ∅ₜ (Fin 2) := unlabeledGraph ((emptyFlag edgeType).out) with hX
  have hadj : X.graph.Adj ((emptyFlag edgeType).out.type_embed 0)
      ((emptyFlag edgeType).out.type_embed 1) := edgeFlag_roots_adj _
  set e0 := (emptyFlag edgeType).out.type_embed 0 with he0
  set e1 := (emptyFlag edgeType).out.type_embed 1 with he1
  have hne : e0 ≠ e1 := hadj.ne
  have hall : ∀ x : Fin 2, x = e0 ∨ x = e1 := by
    intro x
    rcases fin_two_eq_zero_or_one x with rfl | rfl <;>
      rcases fin_two_eq_zero_or_one e0 with h0 | h0 <;>
        rcases fin_two_eq_zero_or_one e1 with h1 | h1 <;>
          rw [h0, h1] <;>
          first
            | exact Or.inl rfl
            | exact Or.inr rfl
            | (exfalso; exact hne (h0.trans h1.symm))
  have hpairs : adjPairs X = {(e0, e1), (e1, e0)} := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hpa := adjPairs_adj hp
      have hpne := hpa.ne
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hall p.1 with h1 | h1 <;> rcases hall p.2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hpne
      · left
        exact Prod.ext h1 h2
      · right
        exact Prod.ext h1 h2
      · exact absurd (h1.trans h2.symm) hpne
    · intro hp
      rw [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact mem_adjPairs hadj
      · exact mem_adjPairs hadj.symm
  have hcard2 : (adjPairs X).card = 2 := by
    rw [hpairs]
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    intro hc
    exact hne (congrArg Prod.fst hc)
  have hq₀ : pairFlag X ⟨(e0, e1), mem_adjPairs hadj⟩ = emptyFlag edgeType :=
    Subsingleton.elim _ _
  have h10 := isomorphismCount_eq_card_pairs X (emptyFlag edgeType)
    ⟨(e0, e1), mem_adjPairs hadj⟩ hq₀
  have h11 : ((adjPairs X).attach.filter
      (fun q => pairFlag X q = emptyFlag edgeType)) = (adjPairs X).attach := by
    apply Finset.filter_true_of_mem
    intro q _
    exact Subsingleton.elim _ _
  rw [h11, Finset.card_attach, hcard2] at h10
  rw [h10]
  norm_num

/-- **The ordered edge count is the edge density times `L(L−1)`.** -/
theorem card_adjPairs_eq {ℓ : ℕ} (M : FlagWithSize ∅ₜ (ℓ + 2))
    : ((adjPairs M.out).card : ℚ)
      = flagDensity₁ edgeType.toEmptyTypeFlag M * (((ℓ : ℚ) + 2) * ((ℓ : ℚ) + 1))
  := by
  have h1 := flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions
    (emptyFlag edgeType) M (by omega : 2 ≤ ℓ + 2)
  rw [downwardNormalizingFactor_emptyFlag_edgeType, mul_one] at h1
  have h2 : ∑ G ∈ labelExtensions M edgeType,
      flagDensity₁ (emptyFlag edgeType) G * downwardNormalizingFactor G
      = ∑ G ∈ labelExtensions M edgeType, downwardNormalizingFactor G := by
    apply Finset.sum_congr rfl
    intro G _
    rw [flagDensity_empty, one_mul]
  rw [h2] at h1
  have h3 : ∑ G ∈ labelExtensions M edgeType, downwardNormalizingFactor G
      = ((adjPairs M.out).card : ℚ) / (((ℓ : ℚ) + 2) * ((ℓ : ℚ) + 1)) := by
    have h4 : ∑ G ∈ labelExtensions M edgeType, downwardNormalizingFactor G
        = ∑ G ∈ labelExtensions M edgeType,
            (isomorphismCount G.out : ℚ) / (((ℓ : ℚ) + 2) * ((ℓ : ℚ) + 1)) := by
      apply Finset.sum_congr rfl
      intro G _
      exact downwardNormalizingFactor_edgeType G
    rw [h4, ← Finset.sum_div]
    congr 1
    exact_mod_cast sum_isomorphismCount_eq_card_adjPairs M
  rw [h3] at h1
  have hD : (0 : ℚ) < ((ℓ : ℚ) + 2) * ((ℓ : ℚ) + 1) := by positivity
  have h5 : flagDensity₁ (unlabel (emptyFlag edgeType)) M
      = flagDensity₁ edgeType.toEmptyTypeFlag M := by
    rw [flagType_asEmptyTypeFlag_eq]
  rw [h5] at h1
  rw [h1]
  field_simp

/-- Sigma-generic wrapper of the pair count. -/
theorem card_adjPairs_eq' (G : FinFlag ∅ₜ) (h2 : 2 ≤ G.1)
    : ((adjPairs G.2.out).card : ℚ)
      = flagDensity₁ edgeType.toEmptyTypeFlag G.2 * ((G.1 : ℚ) * ((G.1 : ℚ) - 1))
  := by
  obtain ⟨L, M⟩ := G
  dsimp only at h2 ⊢
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, L = ℓ + 2 := ⟨L - 2, by omega⟩
  rw [card_adjPairs_eq M]
  push_cast
  ring

/-! ## Markov over an arbitrary index set, and orientation dedup -/

/-- Markov inequality over an arbitrary finite index set. -/
theorem card_bad_ge_of_average_ge_finset {α : Type*} (t : Finset α) (x : α → ℝ)
    {ε B : ℝ} (hB : 0 < B) (hb : ∀ r ∈ t, x r ≤ B) (hnn : ∀ r ∈ t, 0 ≤ x r)
    (havg : ε ≤ (1 / (t.card : ℝ)) * ∑ r ∈ t, x r)
    : ε / (2 * B) * t.card ≤ ((t.filter (fun r => ε / 2 ≤ x r)).card : ℝ)
  := by
  by_cases hε : ε ≤ 0
  · have h1 : ε / (2 * B) * t.card ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact div_nonpos_of_nonpos_of_nonneg hε (by linarith)
      · positivity
    exact le_trans h1 (Nat.cast_nonneg _)
  push_neg at hε
  rcases Finset.eq_empty_or_nonempty t with rfl | hne
  · exfalso
    simp only [Finset.card_empty, Nat.cast_zero, div_zero, Finset.sum_empty,
      zero_mul, mul_zero] at havg
    linarith
  have hn : 0 < t.card := Finset.card_pos.mpr hne
  have hncast : (0 : ℝ) < (t.card : ℝ) := by exact_mod_cast hn
  have hsum_ub : ∑ r ∈ t, x r
      ≤ ((t.filter (fun r => ε / 2 ≤ x r)).card : ℝ) * B + (t.card : ℝ) * (ε / 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not t (fun r => ε / 2 ≤ x r)]
    apply add_le_add
    · calc ∑ r ∈ t.filter (fun r => ε / 2 ≤ x r), x r
          ≤ ∑ r ∈ t.filter (fun r => ε / 2 ≤ x r), B :=
            Finset.sum_le_sum (fun r hr => hb r (Finset.mem_of_mem_filter r hr))
        _ = ((t.filter (fun r => ε / 2 ≤ x r)).card : ℝ) * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
    · calc ∑ r ∈ t.filter (fun r => ¬ε / 2 ≤ x r), x r
          ≤ ∑ r ∈ t.filter (fun r => ¬ε / 2 ≤ x r), (ε / 2) :=
            Finset.sum_le_sum (fun r hr =>
              le_of_lt (not_le.mp (Finset.mem_filter.mp hr).2))
        _ = ((t.filter (fun r => ¬ε / 2 ≤ x r)).card : ℝ) * (ε / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (t.card : ℝ) * (ε / 2) := by
            apply mul_le_mul_of_nonneg_right ?_ (by linarith)
            exact_mod_cast Finset.card_filter_le t _
  have hsum_lb : ε * t.card ≤ ∑ r ∈ t, x r := by
    have h2 := mul_le_mul_of_nonneg_right havg (le_of_lt hncast)
    calc ε * t.card ≤ (1 / (t.card : ℝ)) * (∑ r ∈ t, x r) * t.card := h2
      _ = ∑ r ∈ t, x r := by field_simp
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * B)]
  nlinarith [hsum_ub, hsum_lb]

/-- Every set of non-diagonal pairs has an orientation-unique subset of at
least half its size. -/
theorem exists_orientation_unique_subset {L : ℕ} (P : Finset (Fin L × Fin L))
    (hne : ∀ p ∈ P, p.1 ≠ p.2)
    : ∃ D ⊆ P, (∀ p ∈ D, ∀ q ∈ D, s(p.1, p.2) = s(q.1, q.2) → p = q)
        ∧ P.card ≤ 2 * D.card
  := by
  refine ⟨P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P), Finset.filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq hs
    rw [Finset.mem_filter] at hp hq
    rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    -- q = swap p
    exfalso
    have hqp : q = (p.2, p.1) := by
      apply Prod.ext
      · exact h2.symm
      · exact h1.symm
    have hpne : p.1 ≠ p.2 := hne p hp.1
    rcases hp.2 with hlt | hnot
    · -- p.1 < p.2, so q = (p.2,p.1) has ¬q.1 < q.2 and (q.2,q.1) = p ∈ P
      rcases hq.2 with hlt' | hnot'
      · rw [hqp] at hlt'
        exact absurd hlt' (asymm hlt)
      · rw [hqp] at hnot'
        exact hnot' hp.1
    · -- (p.2,p.1) ∉ P but q = (p.2,p.1) ∈ P
      rw [← hqp] at hnot
      exact hnot hq.1
  · -- P is covered by D and its swap
    have hcov : P ⊆ (P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P))
        ∪ (P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P)).image
            (fun p => (p.2, p.1)) := by
      intro p hp
      rw [Finset.mem_union]
      by_cases hD : p ∈ P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P)
      · exact Or.inl hD
      · right
        rw [Finset.mem_filter] at hD
        push_neg at hD
        obtain ⟨hnlt, hswap⟩ := hD hp
        have hlt : p.2 < p.1 := lt_of_le_of_ne hnlt (hne p hp).symm
        rw [Finset.mem_image]
        refine ⟨(p.2, p.1), ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨hswap, Or.inl hlt⟩
    calc P.card ≤ ((P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P))
          ∪ (P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P)).image
              (fun p => (p.2, p.1))).card := Finset.card_le_card hcov
      _ ≤ (P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P)).card
          + ((P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P)).image
              (fun p => (p.2, p.1))).card := Finset.card_union_le _ _
      _ ≤ 2 * (P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P)).card := by
          have h9 := Finset.card_image_le
            (s := P.filter (fun p => p.1 < p.2 ∨ (p.2, p.1) ∉ P))
            (f := fun p : Fin L × Fin L => (p.2, p.1))
          omega

/-! ## The edge telescopes -/

/-- A deleted pair not covered by the rest of `D` survives in the partially
deleted host. -/
theorem deleteEdgeSet_adj_of_unique {L : ℕ} {N : LabeledGraph ∅ₜ (Fin L)}
    {D : Finset (Fin L × Fin L)} {p : Fin L × Fin L}
    (hadj : N.graph.Adj p.1 p.2)
    (huniq : ∀ q ∈ D, s(q.1, q.2) = s(p.1, p.2) → q = p) (hp : p ∉ D)
    : (deleteEdgeSet N D).graph.Adj p.1 p.2 := by
  rw [deleteEdgeSet_adj]
  refine ⟨hadj, ?_⟩
  intro q hq hc
  exact hp ((huniq q hq hc) ▸ hq)

/-- **(S-edge)** Deleting `|D|` edges moves any model combination's density by
at most `|D| · ‖∂_E g‖₁ · 2/(L(L−1))`. -/
theorem edge_stability {L : ℕ} (g : FlagVector ∅ₜ) (N : LabeledGraph ∅ₜ (Fin L))
    (hsupp : ∀ M ∈ g.support, M.1 ≤ L) (hL2 : 2 ≤ L)
    : ∀ D : Finset (Fin L × Fin L),
      (∀ p ∈ D, N.graph.Adj p.1 p.2) →
      (∀ p ∈ D, ∀ q ∈ D, s(p.1, p.2) = s(q.1, q.2) → p = q) →
      |densityEval g ⟨L, (⟦deleteEdgeSet N D⟧ : FlagWithSize ∅ₜ L)⟩
        - densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩|
      ≤ (D.card : ℝ) * (∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|)
          * 2 / ((L : ℝ) * ((L : ℝ) - 1))
  := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro _ _
    rw [deleteEdgeSet_empty, sub_self, abs_zero]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]
  | insert p D' hp ih =>
    intro hDadj huniq
    have hDadj' : ∀ q ∈ D', N.graph.Adj q.1 q.2 :=
      fun q hq => hDadj q (Finset.mem_insert_of_mem hq)
    have huniq' : ∀ q ∈ D', ∀ r ∈ D', s(q.1, q.2) = s(r.1, r.2) → q = r :=
      fun q hq r hr => huniq q (Finset.mem_insert_of_mem hq) r (Finset.mem_insert_of_mem hr)
    have hih := ih hDadj' huniq'
    have hadj' : (deleteEdgeSet N D').graph.Adj p.1 p.2 := by
      apply deleteEdgeSet_adj_of_unique (hDadj p (Finset.mem_insert_self p D')) ?_ hp
      intro q hq hc
      exact huniq q (Finset.mem_insert_of_mem hq) p (Finset.mem_insert_self p D') hc
    have hstep := edge_deletion_density_vec g hsupp hL2 (deleteEdgeSet N D') p.1 p.2 hadj'
    rw [← deleteEdgeSet_insert] at hstep
    have hLr : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
    have hLpos : (0:ℝ) < (L : ℝ) * ((L : ℝ) - 1) := by nlinarith
    have habs : |densityEval (partialEdgeVec g)
        ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧ : FlagWithSize edgeType L)⟩|
        ≤ ∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F| :=
      abs_densityEval_le _ _
    have hcardins : (insert p D').card = D'.card + 1 := Finset.card_insert_of_notMem hp
    have hBnn : 0 ≤ ∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F| :=
      Finset.sum_nonneg fun F _ => abs_nonneg _
    calc |densityEval g ⟨L, (⟦deleteEdgeSet N (insert p D')⟧ : FlagWithSize ∅ₜ L)⟩
          - densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩|
        = |(densityEval g ⟨L, (⟦deleteEdgeSet N D'⟧ : FlagWithSize ∅ₜ L)⟩
            - densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩)
          + (2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * densityEval (partialEdgeVec g)
              ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
                : FlagWithSize edgeType L)⟩| := by
          rw [hstep]
          ring_nf
      _ ≤ |densityEval g ⟨L, (⟦deleteEdgeSet N D'⟧ : FlagWithSize ∅ₜ L)⟩
            - densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩|
          + |(2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * densityEval (partialEdgeVec g)
              ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
                : FlagWithSize edgeType L)⟩| := abs_add_le _ _
      _ ≤ (D'.card : ℝ) * (∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|)
            * 2 / ((L : ℝ) * ((L : ℝ) - 1))
          + (2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * (∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|) := by
          apply add_le_add hih
          rw [abs_mul]
          have h9 : |2 / ((L : ℝ) * ((L : ℝ) - 1))| = 2 / ((L : ℝ) * ((L : ℝ) - 1)) :=
            abs_of_pos (by positivity)
          rw [h9]
          exact mul_le_mul_of_nonneg_left habs (by positivity)
      _ = ((insert p D').card : ℝ)
            * (∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|)
            * 2 / ((L : ℝ) * ((L : ℝ) - 1)) := by
          rw [hcardins]
          push_cast
          field_simp

/-- **(T-edge)** Deleting `|D|` pairs that are all `ε`-bad *in the original
host* and lie inside `S` drives the density of `g` down by
`|D|·(ε−corr)·2/(L(L−1))`. -/
theorem edge_descent {L : ℕ} (g : FlagVector ∅ₜ) (N : LabeledGraph ∅ₜ (Fin L))
    {ε corr : ℝ} {K : ℕ} (S : Finset (Fin L))
    (hK : ∀ F ∈ (partialEdgeVec g).support, F.1 ≤ K + 2)
    (hsupp : ∀ M ∈ g.support, M.1 ≤ L)
    (hεcorr : 0 ≤ ε - corr) (hL : 4 ≤ L) (hKL : K + 2 ≤ L)
    : ∀ D : Finset (Fin L × Fin L),
      ∀ (hDadj : ∀ p ∈ D, N.graph.Adj p.1 p.2),
      (∀ p ∈ D, p.1 ∈ S ∧ p.2 ∈ S) →
      (∀ p ∈ D, ∀ q ∈ D, s(p.1, p.2) = s(q.1, q.2) → p = q) →
      (∀ p (hp : p ∈ D), densityEval (partialEdgeVec g)
        ⟨L, (⟦edgeRootedAt N p.1 p.2 (hDadj p hp)⟧ : FlagWithSize edgeType L)⟩ ≤ -ε) →
      ((∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|)
        * (((K : ℝ) + 2) * S.card / ((L : ℝ) - 2)
          + ((K : ℝ) + 2) * ((K : ℝ) + 2) * D.card
              / (((L : ℝ) - 2) * ((L : ℝ) - 3))) ≤ corr) →
      densityEval g ⟨L, (⟦deleteEdgeSet N D⟧ : FlagWithSize ∅ₜ L)⟩
        ≤ densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩
          - (D.card : ℝ) * (ε - corr) * 2 / ((L : ℝ) * ((L : ℝ) - 1))
  := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro _ _ _ _ _
    rw [deleteEdgeSet_empty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div, sub_zero, le_refl]
  | insert p D' hp ih =>
    intro hDadj hDS huniq hbad hcorr
    have hLr : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hd2 : (0:ℝ) < (L : ℝ) - 2 := by linarith
    have hd3 : (0:ℝ) < (L : ℝ) - 3 := by linarith
    have hLpos : (0:ℝ) < (L : ℝ) * ((L : ℝ) - 1) := by nlinarith
    have hBnn : 0 ≤ ∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F| :=
      Finset.sum_nonneg fun F _ => abs_nonneg _
    have hcardins : (insert p D').card = D'.card + 1 := Finset.card_insert_of_notMem hp
    have hDadj' : ∀ q ∈ D', N.graph.Adj q.1 q.2 :=
      fun q hq => hDadj q (Finset.mem_insert_of_mem hq)
    have hDS' : ∀ q ∈ D', q.1 ∈ S ∧ q.2 ∈ S :=
      fun q hq => hDS q (Finset.mem_insert_of_mem hq)
    have huniq' : ∀ q ∈ D', ∀ r ∈ D', s(q.1, q.2) = s(r.1, r.2) → q = r :=
      fun q hq r hr => huniq q (Finset.mem_insert_of_mem hq) r (Finset.mem_insert_of_mem hr)
    have hbad' : ∀ q (hq : q ∈ D'), densityEval (partialEdgeVec g)
        ⟨L, (⟦edgeRootedAt N q.1 q.2 (hDadj' q hq)⟧ : FlagWithSize edgeType L)⟩ ≤ -ε :=
      fun q hq => hbad q (Finset.mem_insert_of_mem hq)
    have hcorr' : (∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|)
        * (((K : ℝ) + 2) * S.card / ((L : ℝ) - 2)
          + ((K : ℝ) + 2) * ((K : ℝ) + 2) * D'.card
              / (((L : ℝ) - 2) * ((L : ℝ) - 3))) ≤ corr := by
      refine le_trans ?_ hcorr
      apply mul_le_mul_of_nonneg_left ?_ hBnn
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right ?_ (le_of_lt (mul_pos hd2 hd3))
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hcardins]
      push_cast
      linarith
    have hih := ih hDadj' hDS' huniq' hbad' hcorr'
    -- the inserted pair survives in the partially deleted host
    have hadj' : (deleteEdgeSet N D').graph.Adj p.1 p.2 := by
      apply deleteEdgeSet_adj_of_unique (hDadj p (Finset.mem_insert_self p D')) ?_ hp
      intro q hq hc
      exact huniq q (Finset.mem_insert_of_mem hq) p (Finset.mem_insert_self p D') hc
    -- badness survives up to the hitting correction
    have hpe : densityEval (partialEdgeVec g)
        ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
          : FlagWithSize edgeType L)⟩ ≤ -(ε - corr) := by
      have hhit := pair_hitting_eval N D' S p.1 p.2
        (hDadj p (Finset.mem_insert_self p D')) hadj' (partialEdgeVec g)
        hK hL hKL hDadj' hDS'
      have h1 := hbad p (Finset.mem_insert_self p D')
      have h2 := abs_le.mp hhit
      have h3 : (∑ F ∈ (partialEdgeVec g).support, |partialEdgeVec g F|)
          * (((K : ℝ) + 2) * S.card / ((L : ℝ) - 2)
            + ((K : ℝ) + 2) * ((K : ℝ) + 2) * D'.card
                / (((L : ℝ) - 2) * ((L : ℝ) - 3))) ≤ corr := hcorr'
      linarith [h2.1]
    -- one more deletion step
    have hstep := edge_deletion_density_vec g hsupp (by omega) (deleteEdgeSet N D')
      p.1 p.2 hadj'
    rw [← deleteEdgeSet_insert] at hstep
    have hdrop : (2 / ((L : ℝ) * ((L : ℝ) - 1)))
        * densityEval (partialEdgeVec g)
          ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
            : FlagWithSize edgeType L)⟩
        ≤ -((ε - corr) * 2 / ((L : ℝ) * ((L : ℝ) - 1))) := by
      have h9 : (2 / ((L : ℝ) * ((L : ℝ) - 1)))
          * densityEval (partialEdgeVec g)
            ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
              : FlagWithSize edgeType L)⟩
          ≤ (2 / ((L : ℝ) * ((L : ℝ) - 1))) * (-(ε - corr)) :=
        mul_le_mul_of_nonneg_left hpe (by positivity)
      calc (2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * densityEval (partialEdgeVec g)
              ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
                : FlagWithSize edgeType L)⟩
          ≤ (2 / ((L : ℝ) * ((L : ℝ) - 1))) * (-(ε - corr)) := h9
        _ = -((ε - corr) * 2 / ((L : ℝ) * ((L : ℝ) - 1))) := by
            field_simp
    calc densityEval g ⟨L, (⟦deleteEdgeSet N (insert p D')⟧ : FlagWithSize ∅ₜ L)⟩
        = densityEval g ⟨L, (⟦deleteEdgeSet N D'⟧ : FlagWithSize ∅ₜ L)⟩
          + (2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * densityEval (partialEdgeVec g)
              ⟨L, (⟦edgeRootedAt (deleteEdgeSet N D') p.1 p.2 hadj'⟧
                : FlagWithSize edgeType L)⟩ := hstep
      _ ≤ (densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩
            - (D'.card : ℝ) * (ε - corr) * 2 / ((L : ℝ) * ((L : ℝ) - 1)))
          - (ε - corr) * 2 / ((L : ℝ) * ((L : ℝ) - 1)) := by
          have h9 := hdrop
          linarith
      _ = densityEval g ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩
          - ((insert p D').card : ℝ) * (ε - corr) * 2 / ((L : ℝ) * ((L : ℝ) - 1)) := by
          rw [hcardins]
          push_cast
          field_simp
          ring

/-! ## One full edge-deletion round -/

set_option maxHeartbeats 1600000 in
/-- **One deletion round, edge case**: if the average of
`max(−eval_{∂_E g}, 0)` over the ordered adjacent pairs is at least `ε₀`, and
the ordered edge density is at least `ρ₀`, then deleting the bad edges inside
a well-chosen `⌊σL⌋`-vertex subset drops the density of `g` by
`ε₀²ρ₀σ²/(128B')`, deleting at most `σ²L²` edges, orientation-uniquely. -/
theorem exists_deleted_host_edge {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (gv : FlagVector ∅ₜ) {ε₀ σ B' ρ₀ : ℝ} {K : ℕ}
    (hε₀ : 0 < ε₀) (hσpos : 0 < σ) (hσ1 : σ ≤ 1/2)
    (hB'pos : 0 < B')
    (hBb : ∑ F ∈ (partialEdgeVec gv).support, |partialEdgeVec gv F| ≤ B')
    (hK : ∀ F ∈ (partialEdgeVec gv).support, F.1 ≤ K + 2)
    (hsupp : ∀ M ∈ gv.support, M.1 ≤ L)
    (hσcorr : B' * (2 * ((K:ℝ) + 2) * σ + 4 * ((K:ℝ) + 2)^2 * σ^2) ≤ ε₀ / 4)
    (hKL : K + 2 ≤ L) (hσL : 4 ≤ σ * L)
    (hρ₀nn : 0 ≤ ρ₀)
    (hpairs : ρ₀ * (L:ℝ) * ((L:ℝ) - 1) ≤ ((adjPairs N).card : ℝ))
    (havg : ε₀ ≤ (1 / ((adjPairs N).card : ℝ))
        * ∑ q ∈ (adjPairs N).attach,
            max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0)
    : ∃ D : Finset (Fin L × Fin L),
        (∀ p ∈ D, N.graph.Adj p.1 p.2) ∧
        (∀ p ∈ D, ∀ q ∈ D, s(p.1, p.2) = s(q.1, q.2) → p = q) ∧
        ((D.card : ℝ) ≤ σ^2 * (L:ℝ)^2) ∧
        densityEval gv ⟨L, (⟦deleteEdgeSet N D⟧ : FlagWithSize ∅ₜ L)⟩
          ≤ densityEval gv ⟨L, (⟦N⟧ : FlagWithSize ∅ₜ L)⟩
            - ε₀^2 * ρ₀ * σ^2 / (128 * B')
  := by
  -- basic size facts
  have hL8 : (8:ℝ) ≤ (L:ℝ) := by nlinarith
  have hL8n : 8 ≤ L := by exact_mod_cast hL8
  have hLpos : (0:ℝ) < (L:ℝ) := by linarith
  have hd1 : (0:ℝ) < (L:ℝ) - 1 := by linarith
  have hd2 : (0:ℝ) < (L:ℝ) - 2 := by linarith
  have hd3 : (0:ℝ) < (L:ℝ) - 3 := by linarith
  set B : ℝ := ∑ F ∈ (partialEdgeVec gv).support, |partialEdgeVec gv F| with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun F _ => abs_nonneg _
  -- Markov: many bad ordered pairs
  have hxb : ∀ q ∈ (adjPairs N).attach,
      max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0 ≤ B' := by
    intro q _
    calc max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0
        ≤ |densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩| :=
          max_le (neg_le_abs _) (abs_nonneg _)
      _ ≤ B := abs_densityEval_le _ _
      _ ≤ B' := hBb
  have havg' : ε₀ ≤ (1 / (((adjPairs N).attach.card : ℝ)))
      * ∑ q ∈ (adjPairs N).attach,
          max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0 := by
    rw [Finset.card_attach]
    exact havg
  have hmark := card_bad_ge_of_average_ge_finset (adjPairs N).attach
    (fun q => max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0)
    hB'pos hxb (fun q _ => le_max_right _ _) havg'
  rw [Finset.card_attach] at hmark
  set BadQ := (adjPairs N).attach.filter (fun q =>
      ε₀ / 2 ≤ max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0)
    with hBadQ
  set BadP := BadQ.image (fun q => q.val) with hBadP
  have hBadPcard : BadP.card = BadQ.card := by
    rw [hBadP]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hBadPadj : ∀ p ∈ BadP, N.graph.Adj p.1 p.2 := by
    intro p hp
    rw [hBadP, Finset.mem_image] at hp
    obtain ⟨q, -, rfl⟩ := hp
    exact adjPairs_adj q.2
  have hBadPbad : ∀ p ∈ BadP, ∀ (hadj : N.graph.Adj p.1 p.2),
      densityEval (partialEdgeVec gv)
        ⟨L, (⟦edgeRootedAt N p.1 p.2 hadj⟧ : FlagWithSize edgeType L)⟩ ≤ -(ε₀ / 2) := by
    intro p hp hadj
    rw [hBadP, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hBadQ, Finset.mem_filter] at hq
    have h9 := hq.2
    by_contra hc
    push_neg at hc
    have h10 : max (-(densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩)) 0 < ε₀ / 2 := by
      apply max_lt ?_ (by linarith)
      have h11 : densityEval (partialEdgeVec gv) ⟨L, pairFlag N q⟩
          = densityEval (partialEdgeVec gv)
            ⟨L, (⟦edgeRootedAt N q.val.1 q.val.2 hadj⟧ : FlagWithSize edgeType L)⟩ := rfl
      rw [h11]
      linarith
    linarith
  have hBadPne : ∀ p ∈ BadP, p.1 ≠ p.2 := fun p hp => (hBadPadj p hp).ne
  -- dedup orientations
  obtain ⟨D₀, hD₀sub, hD₀uniq, hD₀card⟩ := exists_orientation_unique_subset BadP hBadPne
  -- the dense vertex subset
  set sz : ℕ := ⌊σ * (L:ℝ)⌋₊ with hsz
  have hsz4 : 4 ≤ sz := by
    have h9 : (4:ℝ) ≤ σ * L := hσL
    have h10 := Nat.le_floor (by exact_mod_cast h9 : ((4:ℕ):ℝ) ≤ σ * (L:ℝ))
    exact_mod_cast h10
  have hszL : sz ≤ L := by
    have h9 : (sz : ℝ) ≤ σ * L := Nat.floor_le (by positivity)
    have h10 : σ * (L:ℝ) ≤ (L:ℝ) := by nlinarith
    exact_mod_cast le_trans h9 h10
  have hszr : (sz : ℝ) ≤ σ * L := Nat.floor_le (by positivity)
  have hszlb : σ * (L:ℝ) / 2 ≤ (sz : ℝ) := by
    have h9 := Nat.lt_floor_add_one (σ * (L:ℝ))
    have h10 : σ * (L:ℝ) - 1 ≤ (sz : ℝ) := by
      push_cast at h9 ⊢
      linarith
    nlinarith
  obtain ⟨S, hSmem, hSdense⟩ := exists_dense_subset D₀
    (fun p hp => hBadPne p (hD₀sub hp)) sz (by omega) hszL
  have hScard : S.card = sz := (Finset.mem_powersetCard.mp hSmem).2
  set D := D₀.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S) with hD
  have hDadj : ∀ p ∈ D, N.graph.Adj p.1 p.2 :=
    fun p hp => hBadPadj p (hD₀sub (Finset.mem_of_mem_filter p hp))
  have hDuniq : ∀ p ∈ D, ∀ q ∈ D, s(p.1, p.2) = s(q.1, q.2) → p = q :=
    fun p hp q hq => hD₀uniq p (Finset.mem_of_mem_filter p hp)
      q (Finset.mem_of_mem_filter q hq)
  have hDS : ∀ p ∈ D, p.1 ∈ S ∧ p.2 ∈ S :=
    fun p hp => (Finset.mem_filter.mp hp).2
  -- |D| is at most σ²L²
  have hDcard_ub : (D.card : ℝ) ≤ σ^2 * (L:ℝ)^2 := by
    have h9 : D ⊆ S ×ˢ S := by
      intro p hp
      rw [Finset.mem_product]
      exact hDS p hp
    have h10 : D.card ≤ sz * sz := by
      calc D.card ≤ (S ×ˢ S).card := Finset.card_le_card h9
        _ = sz * sz := by rw [Finset.card_product, hScard]
    calc (D.card : ℝ) ≤ (sz : ℝ) * sz := by exact_mod_cast h10
      _ ≤ (σ * L) * (σ * L) := by nlinarith [Nat.cast_nonneg (α := ℝ) sz]
      _ = σ^2 * (L:ℝ)^2 := by ring
  -- |D| is at least the average share of the bad pairs (ℕ, cross-multiplied)
  have hDcard_lb : D₀.card * (sz * (sz - 1)) ≤ D.card * (L * (L - 1)) := by
    have hid : sz * (sz - 1) * L.choose sz = L * (L - 1) * (L - 2).choose (sz - 2) := by
      have e1 : sz - 1 = (sz - 2) + 1 := by omega
      have e2 : sz = (sz - 1) + 1 := by omega
      have h10 := Nat.add_one_mul_choose_eq (L - 1) (sz - 1)
      have h11 := Nat.add_one_mul_choose_eq (L - 2) (sz - 2)
      have h12 : L - 1 + 1 = L := by omega
      have h13 : L - 2 + 1 = L - 1 := by omega
      rw [h12] at h10
      rw [h13] at h11
      have h14 : L * (L - 1).choose (sz - 1) = L.choose sz * sz := by
        rw [← e2] at h10
        exact h10
      have h15 : (L - 1) * (L - 2).choose (sz - 2)
          = (L - 1).choose (sz - 1) * (sz - 1) := by
        rw [← e1] at h11
        exact h11
      calc sz * (sz - 1) * L.choose sz
          = (sz - 1) * (L.choose sz * sz) := by ring
        _ = (sz - 1) * (L * (L - 1).choose (sz - 1)) := by rw [← h14]
        _ = L * ((L - 1).choose (sz - 1) * (sz - 1)) := by ring
        _ = L * ((L - 1) * (L - 2).choose (sz - 2)) := by rw [← h15]
        _ = L * (L - 1) * (L - 2).choose (sz - 2) := by ring
    have h16 : D₀.card * (L - 2).choose (sz - 2) ≤ D.card * L.choose sz := hSdense
    have hchoosepos : 0 < (L - 2).choose (sz - 2) := Nat.choose_pos (by omega)
    apply Nat.le_of_mul_le_mul_right ?_ hchoosepos
    calc D₀.card * (sz * (sz - 1)) * (L - 2).choose (sz - 2)
        = (sz * (sz - 1)) * (D₀.card * (L - 2).choose (sz - 2)) := by ring
      _ ≤ (sz * (sz - 1)) * (D.card * L.choose sz) := Nat.mul_le_mul_left _ h16
      _ = D.card * (sz * (sz - 1) * L.choose sz) := by ring
      _ = D.card * (L * (L - 1) * (L - 2).choose (sz - 2)) := by rw [hid]
      _ = D.card * (L * (L - 1)) * (L - 2).choose (sz - 2) := by ring
  -- badness in the dependent form needed by the descent
  have hDbad : ∀ p (hp : p ∈ D), densityEval (partialEdgeVec gv)
      ⟨L, (⟦edgeRootedAt N p.1 p.2 (hDadj p hp)⟧ : FlagWithSize edgeType L)⟩
      ≤ -(ε₀ / 2) :=
    fun p hp => hBadPbad p (hD₀sub (Finset.mem_of_mem_filter p hp)) (hDadj p hp)
  -- discard the definitional bodies to keep the arithmetic light
  clear_value sz BadQ BadP D
  clear hsz hBadQ hBadP hD hxb havg havg' hBadPadj hBadPbad hBadPne hD₀sub
    hD₀uniq hSdense hSmem
  -- the correction budget
  have hcorr : B * (((K:ℝ) + 2) * S.card / ((L:ℝ) - 2)
      + ((K:ℝ) + 2) * ((K:ℝ) + 2) * D.card / (((L:ℝ) - 2) * ((L:ℝ) - 3)))
      ≤ ε₀ / 4 := by
    have h20 : ((K:ℝ) + 2) * S.card / ((L:ℝ) - 2) ≤ 2 * ((K:ℝ) + 2) * σ := by
      rw [hScard, div_le_iff₀ hd2]
      have h21 : (L:ℝ) ≤ 2 * ((L:ℝ) - 2) := by linarith
      calc ((K:ℝ) + 2) * (sz:ℝ)
          ≤ ((K:ℝ) + 2) * (σ * L) :=
            mul_le_mul_of_nonneg_left hszr (by positivity)
        _ ≤ ((K:ℝ) + 2) * (σ * (2 * ((L:ℝ) - 2))) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h21 hσpos.le
        _ = 2 * ((K:ℝ) + 2) * σ * ((L:ℝ) - 2) := by ring
    have h22 : ((K:ℝ) + 2) * ((K:ℝ) + 2) * D.card / (((L:ℝ) - 2) * ((L:ℝ) - 3))
        ≤ 4 * ((K:ℝ) + 2)^2 * σ^2 := by
      rw [div_le_iff₀ (mul_pos hd2 hd3)]
      have h23 : (L:ℝ)^2 ≤ 4 * (((L:ℝ) - 2) * ((L:ℝ) - 3)) := by nlinarith [hL8]
      calc ((K:ℝ) + 2) * ((K:ℝ) + 2) * (D.card:ℝ)
          ≤ ((K:ℝ) + 2) * ((K:ℝ) + 2) * (σ^2 * (L:ℝ)^2) :=
            mul_le_mul_of_nonneg_left hDcard_ub (by positivity)
        _ ≤ ((K:ℝ) + 2) * ((K:ℝ) + 2) * (σ^2 * (4 * (((L:ℝ) - 2) * ((L:ℝ) - 3)))) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h23 (sq_nonneg σ)
        _ = 4 * ((K:ℝ) + 2)^2 * σ^2 * (((L:ℝ) - 2) * ((L:ℝ) - 3)) := by ring
    have h24 : (0:ℝ) ≤ ((K:ℝ) + 2) * S.card / ((L:ℝ) - 2)
        + ((K:ℝ) + 2) * ((K:ℝ) + 2) * D.card / (((L:ℝ) - 2) * ((L:ℝ) - 3)) := by
      positivity
    calc B * (((K:ℝ) + 2) * S.card / ((L:ℝ) - 2)
          + ((K:ℝ) + 2) * ((K:ℝ) + 2) * D.card / (((L:ℝ) - 2) * ((L:ℝ) - 3)))
        ≤ B' * (2 * ((K:ℝ) + 2) * σ + 4 * ((K:ℝ) + 2)^2 * σ^2) := by
          apply mul_le_mul hBb (add_le_add h20 h22) h24 hB'pos.le
      _ ≤ ε₀ / 4 := hσcorr
  -- run the descent
  have hdesc := edge_descent gv N (ε := ε₀/2) (corr := ε₀/4) S hK hsupp
    (by linarith) (by omega) hKL D hDadj hDS hDuniq hDbad hcorr
  refine ⟨D, hDadj, hDuniq, hDcard_ub, ?_⟩
  refine le_trans hdesc ?_
  have hLL1 : (0:ℝ) < (L:ℝ) * ((L:ℝ) - 1) := by nlinarith
  -- the drop dominates ε₀²ρ₀σ²/(128B')
  have hdrop : ε₀^2 * ρ₀ * σ^2 / (128 * B')
      ≤ (D.card : ℝ) * (ε₀/2 - ε₀/4) * 2 / ((L:ℝ) * ((L:ℝ) - 1)) := by
    have c1 : (D₀.card : ℝ) * ((sz:ℝ) * ((sz:ℝ) - 1))
        ≤ (D.card : ℝ) * ((L:ℝ) * ((L:ℝ) - 1)) := by
      have h9 : ((D₀.card * (sz * (sz - 1)) : ℕ) : ℝ)
          ≤ ((D.card * (L * (L - 1)) : ℕ) : ℝ) := by exact_mod_cast hDcard_lb
      push_cast [Nat.cast_sub (by omega : 1 ≤ sz), Nat.cast_sub (by omega : 1 ≤ L)] at h9
      linarith
    have c2 : (BadP.card : ℝ) ≤ 2 * (D₀.card : ℝ) := by exact_mod_cast hD₀card
    have c3 : ε₀ / (2 * B') * ((adjPairs N).card : ℝ) ≤ (BadP.card : ℝ) := by
      rw [hBadPcard]
      exact hmark
    have d0lb : ε₀ / (4 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1)) ≤ (D₀.card : ℝ) := by
      have h9 : ε₀ / (2 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1))
          ≤ ε₀ / (2 * B') * ((adjPairs N).card : ℝ) :=
        mul_le_mul_of_nonneg_left hpairs (by positivity)
      have h10 : ε₀ / (4 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1))
          = (ε₀ / (2 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1))) / 2 := by
        ring
      linarith
    have hsz4r : (4:ℝ) ≤ (sz:ℝ) := by exact_mod_cast hsz4
    have c5 : σ^2 * (L:ℝ)^2 / 8 ≤ (sz:ℝ) * ((sz:ℝ) - 1) := by
      have h9 : σ * (L:ℝ) / 4 ≤ (sz:ℝ) - 1 := by linarith
      calc σ^2 * (L:ℝ)^2 / 8 = (σ * (L:ℝ) / 2) * (σ * (L:ℝ) / 4) := by ring
        _ ≤ (sz:ℝ) * ((sz:ℝ) - 1) :=
            mul_le_mul hszlb h9 (by positivity) (Nat.cast_nonneg _)
    have Dlb : ε₀ / (4 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1)) * (σ^2 * (L:ℝ)^2 / 8)
        ≤ (D.card : ℝ) * ((L:ℝ) * ((L:ℝ) - 1)) := by
      calc ε₀ / (4 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1)) * (σ^2 * (L:ℝ)^2 / 8)
          ≤ (D₀.card : ℝ) * (σ^2 * (L:ℝ)^2 / 8) :=
            mul_le_mul_of_nonneg_right d0lb (by positivity)
        _ ≤ (D₀.card : ℝ) * ((sz:ℝ) * ((sz:ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left c5 (Nat.cast_nonneg _)
        _ ≤ (D.card : ℝ) * ((L:ℝ) * ((L:ℝ) - 1)) := c1
    have DlbX : ε₀ * ρ₀ * σ^2 * (L:ℝ)^2 / (32 * B') ≤ (D.card : ℝ) := by
      have h30 : (ε₀ * ρ₀ * σ^2 * (L:ℝ)^2 / (32 * B')) * ((L:ℝ) * ((L:ℝ) - 1))
          = ε₀ / (4 * B') * (ρ₀ * (L:ℝ) * ((L:ℝ) - 1)) * (σ^2 * (L:ℝ)^2 / 8) := by
        field_simp
        ring
      have h31 : (ε₀ * ρ₀ * σ^2 * (L:ℝ)^2 / (32 * B')) * ((L:ℝ) * ((L:ℝ) - 1))
          ≤ (D.card : ℝ) * ((L:ℝ) * ((L:ℝ) - 1)) := by
        rw [h30]
        exact Dlb
      exact le_of_mul_le_mul_right h31 hLL1
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 128 * B') hLL1]
    have h32 := mul_le_mul_of_nonneg_left DlbX
      (by positivity : (0:ℝ) ≤ 64 * B' * ε₀)
    have hL2L : (L:ℝ) * ((L:ℝ) - 1) ≤ (L:ℝ)^2 := by nlinarith
    have h33 : 64 * B' * ε₀ * (ε₀ * ρ₀ * σ^2 * (L:ℝ)^2 / (32 * B'))
        = 2 * ε₀^2 * ρ₀ * σ^2 * (L:ℝ)^2 := by
      field_simp
      ring
    rw [h33] at h32
    have h34 : ε₀^2 * ρ₀ * σ^2 * ((L:ℝ) * ((L:ℝ) - 1))
        ≤ 2 * ε₀^2 * ρ₀ * σ^2 * (L:ℝ)^2 := by
      have h35 : (0:ℝ) ≤ ε₀^2 * ρ₀ * σ^2 := by positivity
      have h36 : (L:ℝ) * ((L:ℝ) - 1) ≤ 2 * (L:ℝ)^2 := by nlinarith
      calc ε₀^2 * ρ₀ * σ^2 * ((L:ℝ) * ((L:ℝ) - 1))
          ≤ ε₀^2 * ρ₀ * σ^2 * (2 * (L:ℝ)^2) := mul_le_mul_of_nonneg_left h36 h35
        _ = 2 * ε₀^2 * ρ₀ * σ^2 * (L:ℝ)^2 := by ring
    calc ε₀^2 * ρ₀ * σ^2 * ((L:ℝ) * ((L:ℝ) - 1))
        ≤ 2 * ε₀^2 * ρ₀ * σ^2 * (L:ℝ)^2 := h34
      _ ≤ 64 * B' * ε₀ * (D.card : ℝ) := h32
      _ = (D.card : ℝ) * (ε₀/2 - ε₀/4) * 2 * (128 * B') := by ring
  exact sub_le_sub_left hdrop _

end Differential
end FlagAlgebras
