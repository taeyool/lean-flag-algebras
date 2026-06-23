import LeanFlagAlgebras.FlagAlgebra.Compute.FastIso
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists

/-! # Self-contained flag enumeration (Phase 1: empty-typed flags)

This module replaces the Python/JSON flag-enumeration pipeline (for empty-typed
flags) with a computable Lean generator together with a *mathematical* proof of
completeness. The point is to avoid `native_decide` over the entire quotient
type `Sym2EmptyTypedFlag n` (which enumerates and dedups all `2^(n choose 2)`
raw graphs via expensive isomorphism comparisons); instead we prove
`genEmptyTypedFlagSet n = univ` once, computation-free.

The generation pipeline:

* `allRawSym2Graphs n` — every `Sym2Graph n`, built computably as the subsets of
  `allEdges n` (`Finset.toList`/`Multiset.toList` are noncomputable, so we cannot
  go through `Finset.univ`).
* `genSym2GraphsDedup n` — one representative per `∼sf`-class, via a `foldl`
  that keeps a graph only if no kept graph is `isEmptyIsoFast_bool`-equivalent.
* `genSym2Graphs n` — the deduped list re-sorted into the *canonical JSON order*
  (sort by `(edge count, lexicographically-minimal relabeled edge list)`), so
  every downstream index/proof keyed off the old JSON order keeps working.

The completeness/nodup/eq_univ proofs only use that `genSym2Graphs` is a
*permutation* of the deduped list; the sort is for index-compatibility and is
verified empirically (`#eval`) against the JSON files, not proved.
-/

namespace FlagAlgebras.Compute

open List

/-- Structural `DecidableEq` for `Sym2Graph` (compare the underlying edge
finsets). Needed so the generated list can be compared by `native_decide`
against an explicit literal list in the `*_val_eq` bridge lemmas. -/
instance {n : ℕ} : DecidableEq (Sym2Graph n) := fun G G' =>
  decidable_of_iff (G.edges = G'.edges) Sym2Graph.ext_iff.symm

/-! ## Canonical ordering matching the Python/JSON pipeline

`generate_graphs.py` writes, for each graph, the lexicographically smallest
edge list over all `n!` vertex relabelings (each edge stored as `[min, max]`,
the list sorted), then sorts graphs by `(len(edges), edge_list)`. We reproduce
that key here so `genSym2Graphs` matches the JSON file order. -/

/-- An edge as an ordered pair `(min endpoint, max endpoint)` of vertex indices. -/
def edgeToPair {n : ℕ} (e : Sym2 (Fin n)) : ℕ × ℕ :=
  Sym2.lift ⟨fun a b => (min a.val b.val, max a.val b.val),
    fun a b => by
      show (min a.val b.val, max a.val b.val) = (min b.val a.val, max b.val a.val)
      rw [min_comm a.val b.val, max_comm a.val b.val]⟩ e

/-- Strict lexicographic `<` on `(ℕ × ℕ)` pairs. -/
def pairLt (p q : ℕ × ℕ) : Bool :=
  decide (p.1 < q.1) || (p.1 == q.1 && decide (p.2 < q.2))

/-- Non-strict lexicographic `≤` on `(ℕ × ℕ)` pairs. -/
def pairLe (p q : ℕ × ℕ) : Bool :=
  decide (p.1 < q.1) || (p.1 == q.1 && decide (p.2 ≤ q.2))

/-- Strict lexicographic `<` on lists of pairs (Python list comparison). -/
def listPairLt : List (ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: ps, q :: qs => if p == q then listPairLt ps qs else pairLt p q

/-- The sorted edge list of `G` after relabeling vertices by `perm`. We list
`G`'s edges computably as the members of `allEdges n` (any order is fine, the
result is sorted), since `Finset.toList` is noncomputable. -/
def relabeledEdgeList {n : ℕ} (perm : List (Fin n)) (G : Sym2Graph n) : List (ℕ × ℕ) :=
  List.insertionSort (fun p q => pairLe p q = true)
    (((allEdges n).filter (fun e => decide (e ∈ G.edges))).map
      (fun e => edgeToPair (applyPermEdge perm e)))

/-- The canonical (lexicographically smallest over all `n!` relabelings) edge
list of `G`, matching `get_canonical_edges` in `generate_graphs.py`. -/
def canonicalEdgeList {n : ℕ} (G : Sym2Graph n) : List (ℕ × ℕ) :=
  match (List.finRange n).permutations with
  | [] => []
  | p :: ps => ps.foldl (fun best perm =>
      let cand := relabeledEdgeList perm G
      if listPairLt cand best then cand else best) (relabeledEdgeList p G)

/-- The sort key putting graphs into JSON file order: `(edge count, canonical
edge list)`. Precomputed once per graph so the sort does not re-evaluate the
`n!`-cost `canonicalEdgeList` on every comparison. -/
def graphKey {n : ℕ} (G : Sym2Graph n) : ℕ × List (ℕ × ℕ) :=
  (G.edges.card, canonicalEdgeList G)

/-- Total preorder on precomputed `graphKey`s: by edge count, then by canonical
edge list. Yields the same boolean as comparing the graphs directly, but reads
the canonical edge list from the key instead of recomputing it. -/
def graphKeyLe (k k' : ℕ × List (ℕ × ℕ)) : Bool :=
  decide (k.1 < k'.1) ||
    (k.1 == k'.1 && (listPairLt k.2 k'.2 || k.2 == k'.2))

/-! ## Computable enumeration of all graphs -/

/-- Every non-diagonal edge appears in `allEdges n`. -/
theorem mem_allEdges_of_not_isDiag {n : ℕ} {e : Sym2 (Fin n)} (h : ¬ e.IsDiag) :
    e ∈ allEdges n := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Sym2.mk_isDiag_iff] at h
    rw [allEdges, List.mem_flatMap]
    rcases Nat.lt_or_ge u.val v.val with hlt | hge
    · refine ⟨u, List.mem_finRange u, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨v, List.mem_finRange v, by rw [if_pos hlt]⟩
    · have hlt' : v.val < u.val :=
        Nat.lt_of_le_of_ne hge (fun he => h (Fin.ext he.symm))
      refine ⟨v, List.mem_finRange v, ?_⟩
      rw [List.mem_filterMap]
      refine ⟨u, List.mem_finRange u, ?_⟩
      rw [if_pos hlt']
      exact congrArg some Sym2.eq_swap

/-- Build a `Sym2Graph` from a list of edges, dropping any diagonal ones. -/
def mkGraphFromEdges {n : ℕ} (l : List (Sym2 (Fin n))) : Sym2Graph n :=
  ⟨(l.filter (fun e => decide (¬ e.IsDiag))).toFinset, by
    intro e he
    rw [List.mem_toFinset, List.mem_filter] at he
    exact of_decide_eq_true he.2⟩

/-- All `Sym2Graph n`, enumerated computably as the subsets of `allEdges n`. -/
def allRawSym2Graphs (n : ℕ) : List (Sym2Graph n) :=
  (allEdges n).sublists.map mkGraphFromEdges

theorem mem_allRawSym2Graphs {n : ℕ} (G : Sym2Graph n) : G ∈ allRawSym2Graphs n := by
  rw [allRawSym2Graphs, List.mem_map]
  refine ⟨(allEdges n).filter (fun e => decide (e ∈ G.edges)), ?_, ?_⟩
  · rw [List.mem_sublists]; exact List.filter_sublist
  · apply Sym2Graph.ext
    ext e
    simp only [mkGraphFromEdges, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨_, hmem⟩, _⟩; exact hmem
    · intro he
      exact ⟨⟨mem_allEdges_of_not_isDiag (G.edges_valid e he), he⟩, G.edges_valid e he⟩

/-! ## Generation -/

/-- One `foldl` step: append `G` to the accumulator unless some kept graph is
already fast-iso-equivalent to it. -/
def dedupStep {n : ℕ} (acc : List (Sym2Graph n)) (G : Sym2Graph n) : List (Sym2Graph n) :=
  if acc.any (fun H => isEmptyIsoFast_bool H G) = true then acc else acc ++ [G]

/-! ## Canonical-augmentation generator (empty-typed)

Instead of enumerating all `2 ^ C(n,2)` labeled graphs and deduplicating (which
makes `n ≥ 7` intractable), we build the `n`-vertex representatives from the
`(n-1)`-vertex representatives in nauty/McKay "orderly augmentation" style: take
each representative `R` on the first `n-1` vertices, attach a new last vertex
`Fin.last (n-1)` adjacent to every subset `S ⊆ Fin (n-1)`, then deduplicate the
(much smaller) augmented family. Completeness is proved mathematically, so the
elaboration-time `native_decide` bridge evaluates only this small generator.

`augment`/`augmentAll`/`augReps` are the *computational* core (evaluated at
elaboration time); `restrict`/`neighborsOfLast`/`extendEquivLast` are used only
inside the completeness proof and need not be efficient. -/

/-- Extend a vertex permutation `φ` of `Fin n` to `Fin (n+1)`, fixing the last
vertex. Used to transport an isomorphism across the new vertex. -/
def extendEquivLast {n : ℕ} (φ : Fin n ≃ Fin n) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.lastCases (Fin.last n) (fun i => Fin.castSucc (φ i))
  invFun := Fin.lastCases (Fin.last n) (fun i => Fin.castSucc (φ.symm i))
  left_inv := by
    intro x
    cases x using Fin.lastCases with
    | last => simp [Fin.lastCases_last]
    | cast i => simp [Fin.lastCases_castSucc]
  right_inv := by
    intro x
    cases x using Fin.lastCases with
    | last => simp [Fin.lastCases_last]
    | cast i => simp [Fin.lastCases_castSucc]

@[simp] theorem extendEquivLast_castSucc {n : ℕ} (φ : Fin n ≃ Fin n) (i : Fin n) :
    extendEquivLast φ (Fin.castSucc i) = Fin.castSucc (φ i) := by
  simp only [extendEquivLast, Equiv.coe_fn_mk, Fin.lastCases_castSucc]

@[simp] theorem extendEquivLast_last {n : ℕ} (φ : Fin n ≃ Fin n) :
    extendEquivLast φ (Fin.last n) = Fin.last n := by
  simp only [extendEquivLast, Equiv.coe_fn_mk, Fin.lastCases_last]

/-- Add a new last vertex to `G`, adjacent to exactly the vertices in `S`. The
old edges are carried over by `Fin.castSucc`. -/
def augment {n : ℕ} (G : Sym2Graph n) (S : Finset (Fin n)) : Sym2Graph (n + 1) :=
  ⟨G.edges.image (Sym2.map Fin.castSucc) ∪
      S.image (fun v => s(Fin.castSucc v, Fin.last n)), by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · rw [Finset.mem_image] at he
      obtain ⟨e₀, he₀, rfl⟩ := he
      have hnd : ¬ e₀.IsDiag := G.edges_valid e₀ he₀
      clear he₀
      revert hnd
      induction e₀ using Sym2.ind with
      | _ a b =>
        rw [Sym2.map_pair_eq, Sym2.mk_isDiag_iff, Sym2.mk_isDiag_iff]
        exact fun hnd hEq => hnd (Fin.castSucc_injective n hEq)
    · rw [Finset.mem_image] at he
      obtain ⟨v, _, rfl⟩ := he
      rw [Sym2.mk_isDiag_iff]
      exact (Fin.castSucc_lt_last v).ne⟩

/-- Membership in the edge set of `augment G S`: either an old edge carried over
by `Fin.castSucc`, or a new pendant edge `{castSucc v, last}` for `v ∈ S`. -/
theorem mem_augment_edges {n : ℕ} (G : Sym2Graph n) (S : Finset (Fin n))
    (e : Sym2 (Fin (n + 1))) :
    e ∈ (augment G S).edges ↔
      (∃ e₀ ∈ G.edges, Sym2.map Fin.castSucc e₀ = e) ∨
      (∃ v ∈ S, s(Fin.castSucc v, Fin.last n) = e) := by
  simp only [augment, Finset.mem_union, Finset.mem_image]

/-- The induced subgraph of `H` on the first `n` vertices (drop the last). -/
def restrict {n : ℕ} (H : Sym2Graph (n + 1)) : Sym2Graph n :=
  ⟨(Finset.univ : Finset (Sym2 (Fin n))).filter
      (fun e => ¬ e.IsDiag ∧ Sym2.map Fin.castSucc e ∈ H.edges), by
    intro e he
    exact (Finset.mem_filter.mp he).2.1⟩

theorem mem_restrict_edges {n : ℕ} (H : Sym2Graph (n + 1)) (e : Sym2 (Fin n)) :
    e ∈ (restrict H).edges ↔ ¬ e.IsDiag ∧ Sym2.map Fin.castSucc e ∈ H.edges := by
  simp only [restrict, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The neighbors of the last vertex of `H`, as a subset of the first `n`. -/
def neighborsOfLast {n : ℕ} (H : Sym2Graph (n + 1)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => s(Fin.castSucc v, Fin.last n) ∈ H.edges)

theorem mem_neighborsOfLast {n : ℕ} (H : Sym2Graph (n + 1)) (v : Fin n) :
    v ∈ neighborsOfLast H ↔ s(Fin.castSucc v, Fin.last n) ∈ H.edges := by
  simp only [neighborsOfLast, Finset.mem_filter, Finset.mem_univ, true_and]

/-- All subsets of `Fin n`, enumerated computably as the sublists of `finRange n`. -/
def allVertSubsets (n : ℕ) : List (Finset (Fin n)) :=
  (List.finRange n).sublists.map List.toFinset

theorem mem_allVertSubsets {n : ℕ} (S : Finset (Fin n)) : S ∈ allVertSubsets n := by
  rw [allVertSubsets, List.mem_map]
  refine ⟨(List.finRange n).filter (fun v => decide (v ∈ S)), ?_, ?_⟩
  · rw [List.mem_sublists]; exact List.filter_sublist
  · ext v
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- All one-vertex augmentations of `G`: attach the new vertex to each subset. -/
def augmentAll {n : ℕ} (G : Sym2Graph n) : List (Sym2Graph (n + 1)) :=
  (allVertSubsets n).map (augment G)

theorem mem_augmentAll {n : ℕ} (G : Sym2Graph n) (S : Finset (Fin n)) :
    augment G S ∈ augmentAll G :=
  List.mem_map.mpr ⟨S, mem_allVertSubsets S, rfl⟩

/-- The augmentation-generated representatives: build the `(n+1)`-vertex graphs
by augmenting each `n`-vertex representative, then deduplicate. This is the
*specification*: it deduplicates by the `O(n!)`-per-comparison
`isEmptyIsoFast_bool` test directly. The runtime generator `augRepsDeg` computes
the same list, but only runs the `O(n!)` test when a cheap iso-invariant key
collides, so most pairs never reach it. -/
def augReps : (n : ℕ) → List (Sym2Graph n)
  | 0 => [⟨∅, by simp⟩]
  | n + 1 => ((augReps n).flatMap augmentAll).foldl dedupStep []

/-- Attach the cheap key to a graph as a precomputed bucketing key. -/
def withDegKey {n : ℕ} (G : Sym2Graph n) : Sym2Graph n × (ℕ × List ℕ) :=
  (G, degKey G)

/-- Keyed deduplication step with a cheap prefilter: keep `p` unless some survivor
shares its cheap key (`q.2 == p.2`, `O(n)`) *and* is isomorphic to it
(`isEmptyIsoFast_bool`, `O(n!)`). The `&&` short-circuits, so the expensive iso
test runs only on cheap-key collisions. Makes the same keep/drop decisions as
`dedupStep` because the cheap key is an iso invariant (`augRepsDeg_fst_eq`). -/
def dedupStepDeg {n : ℕ} (acc : List (Sym2Graph n × (ℕ × List ℕ)))
    (p : Sym2Graph n × (ℕ × List ℕ)) : List (Sym2Graph n × (ℕ × List ℕ)) :=
  if acc.any (fun q => q.2 == p.2 && isEmptyIsoFast_bool q.1 p.1) = true then acc
  else acc ++ [p]

/-- The fast augmentation generator: identical structure to `augReps`, but each
candidate carries its precomputed cheap key and dedup prefilters by it. The first
component equals `augReps n` (`augRepsDeg_fst_eq`). -/
def augRepsDeg : (n : ℕ) → List (Sym2Graph n × (ℕ × List ℕ))
  | 0 => [withDegKey ⟨∅, by simp⟩]
  | n + 1 =>
      ((((augRepsDeg n).map Prod.fst).flatMap augmentAll).map withDegKey).foldl dedupStepDeg []

/-- The deduplicated list: one representative per `∼sf`-class, produced by the
canonical-augmentation generator (runtime form: cheap-key prefiltered dedup).
The keystone bridge `genSym2GraphsDedup_eq` proves this equals the specification
`augReps n`, so all completeness/`Nodup` reasoning happens on `augReps`. -/
def genSym2GraphsDedup (n : ℕ) : List (Sym2Graph n) :=
  (augRepsDeg n).map Prod.fst

/-- The deduplicated list decorated with each graph's precomputed `graphKey`
`(edge count, canonicalEdgeList)`, sorted into canonical JSON order. We decorate
each graph with its key, sort by the key, and *keep the keys attached*, so the
`n!`-cost `canonicalEdgeList` is evaluated once per graph (inside `graphKey`,
before the sort) rather than on each of the `O(g(n)²)` comparisons the sort
performs. Carrying the keys through also lets downstream consumers
(`genCanonicalEdgeLists`, the `generate_*` commands) reuse the canonical edge
lists instead of recomputing them. -/
def genSym2GraphsKeyed (n : ℕ) : List (Sym2Graph n × ℕ × List (ℕ × ℕ)) :=
  List.insertionSort (fun a b => graphKeyLe a.2 b.2 = true)
    ((genSym2GraphsDedup n).map (fun G => (G, graphKey G)))

/-- The deduplicated list, re-sorted into canonical JSON order (sort keys dropped). -/
def genSym2Graphs (n : ℕ) : List (Sym2Graph n) :=
  (genSym2GraphsKeyed n).map Prod.fst

/-- The canonical edge lists of `genSym2Graphs n`, in the same order, read from
the precomputed `graphKey`s carried by `genSym2GraphsKeyed` (each key's second
component *is* `canonicalEdgeList`). Equal by value to
`(genSym2Graphs n).map canonicalEdgeList`, but without recomputing the `n!`-cost
`canonicalEdgeList` — it was already computed once for the sort key. The
`generate_*` commands and `genFlagData` consume this. -/
def genCanonicalEdgeLists (n : ℕ) : List (List (ℕ × ℕ)) :=
  (genSym2GraphsKeyed n).map (fun p => p.2.2)

/-- The empty-typed flags (quotient classes) of the generated graphs. -/
def genEmptyTypedFlags (n : ℕ) : List (Sym2EmptyTypedFlag n) :=
  (genSym2Graphs n).map (Quotient.mk (Sym2GraphSetoid n))

/-- The finset of generated empty-typed flags. -/
def genEmptyTypedFlagSet (n : ℕ) : Finset (Sym2EmptyTypedFlag n) :=
  (genEmptyTypedFlags n).toFinset

/-! ## `isEmptyIsoFast_bool` completeness

`FastIso` proves soundness (`true → ∼sf`) and the contrapositive completeness
(`false → ¬ ∼sf`). We package the direct completeness statement. -/

theorem isEmptyIsoFast_bool_complete
    {n : ℕ} {G G' : Sym2Graph n} (h : G ∼sf G') :
    isEmptyIsoFast_bool G G' = true := by
  by_contra hne
  exact isEmptyIsoFast_bool_false_correct (eq_false_of_ne_true hne) h

/-! ## Foldl invariants -/

theorem mem_dedupStep_of_mem {n : ℕ} (acc : List (Sym2Graph n)) (x : Sym2Graph n)
    {G : Sym2Graph n} (hG : G ∈ acc) : G ∈ dedupStep acc x := by
  unfold dedupStep
  split
  · exact hG
  · exact List.mem_append.mpr (Or.inl hG)

/-- Elements of the accumulator persist through the rest of the fold. -/
theorem foldl_dedupStep_mono {n : ℕ} (xs : List (Sym2Graph n)) :
    ∀ (acc : List (Sym2Graph n)) (G : Sym2Graph n), G ∈ acc →
      G ∈ xs.foldl dedupStep acc := by
  induction xs with
  | nil => intro acc G hG; simpa using hG
  | cons x rest ih =>
    intro acc G hG
    simp only [List.foldl_cons]
    exact ih (dedupStep acc x) G (mem_dedupStep_of_mem acc x hG)

/-- Every element of the input is `∼sf`-equivalent to some surviving element. -/
theorem foldl_dedupStep_complete {n : ℕ} (xs : List (Sym2Graph n)) :
    ∀ (acc : List (Sym2Graph n)) (G : Sym2Graph n), G ∈ xs →
      ∃ G', G' ∈ xs.foldl dedupStep acc ∧ G ∼sf G' := by
  induction xs with
  | nil => intro acc G hG; exact absurd hG (by simp)
  | cons x rest ih =>
    intro acc G hG
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hG with hGx | hGrest
    · have hx : ∃ G', G' ∈ dedupStep acc x ∧ x ∼sf G' := by
        unfold dedupStep
        by_cases hc : acc.any (fun H => isEmptyIsoFast_bool H x) = true
        · rw [if_pos hc]
          obtain ⟨G', hG'mem, hG'true⟩ := List.any_eq_true.mp hc
          exact ⟨G', hG'mem, Sym2GraphEqv.symm (isEmptyIsoFast_bool_true_correct hG'true)⟩
        · rw [if_neg hc]
          exact ⟨x, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)),
            Sym2GraphEqv.refl x⟩
      obtain ⟨G', hG'mem, hxG'⟩ := hx
      refine ⟨G', foldl_dedupStep_mono rest (dedupStep acc x) G' hG'mem, ?_⟩
      rw [hGx]; exact hxG'
    · exact ih (dedupStep acc x) G hGrest

/-- The deduped flags stay `Nodup` (no two survivors are `∼sf`-equivalent). -/
theorem foldl_dedupStep_flags_nodup {n : ℕ} (xs : List (Sym2Graph n)) :
    ∀ (acc : List (Sym2Graph n)),
      (acc.map (Quotient.mk (Sym2GraphSetoid n))).Nodup →
      ((xs.foldl dedupStep acc).map (Quotient.mk (Sym2GraphSetoid n))).Nodup := by
  induction xs with
  | nil => intro acc hacc; exact hacc
  | cons x rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    unfold dedupStep
    by_cases hc : acc.any (fun H => isEmptyIsoFast_bool H x) = true
    · rw [if_pos hc]; exact hacc
    · rw [if_neg hc, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
      refine ⟨hacc, List.nodup_singleton _, ?_⟩
      intro F hFacc b hb heq
      rw [List.mem_singleton] at hb
      subst hb
      subst heq
      obtain ⟨G', hG'mem, hG'eq⟩ := List.mem_map.mp hFacc
      have hG'x : G' ∼sf x := Quotient.exact hG'eq
      exact hc (List.any_eq_true.mpr ⟨G', hG'mem, isEmptyIsoFast_bool_complete hG'x⟩)

/-! ## Augmentation correctness

The augmentation generator `augReps` is complete (every graph is `∼sf` to some
representative) and produces a `Nodup` flag list. We prove this by induction on
`n`: every `(n+1)`-vertex graph `H` is the augmentation of its own restriction
(`augment_restrict_eq`), the restriction is `∼sf` some `n`-vertex representative
`R₀` (induction hypothesis), and augmentation transports `∼sf` (`augment_transport`),
so `H` is `∼sf` an element of `(augReps n).flatMap augmentAll`, which the dedup fold
preserves up to `∼sf`. -/

/-- The edge set of `augment R (S.image φ)` is the image of `augment G S`'s edge set
under `extendEquivLast φ`, when `φ` is an edge-membership-preserving permutation. -/
theorem augment_edges_image {n : ℕ} {G R : Sym2Graph n} (φ : Fin n ≃ Fin n)
    (hφ : ∀ e₀ : Sym2 (Fin n), e₀ ∈ G.edges ↔ Sym2.map φ e₀ ∈ R.edges) (S : Finset (Fin n)) :
    (augment R (S.image φ)).edges
      = (augment G S).edges.image (Sym2.map (extendEquivLast φ)) := by
  have hRimg : R.edges = G.edges.image (Sym2.map φ) := by
    ext r
    rw [Finset.mem_image]
    constructor
    · intro hr
      refine ⟨Sym2.map φ.symm r, ?_, ?_⟩
      · rw [hφ]; rwa [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id, id_eq]
      · rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id, id_eq]
    · rintro ⟨e₀, he₀, rfl⟩; exact (hφ e₀).mp he₀
  have e1 : (G.edges.image (Sym2.map Fin.castSucc)).image (Sym2.map (extendEquivLast φ))
          = R.edges.image (Sym2.map Fin.castSucc) := by
    rw [Finset.image_image, hRimg, Finset.image_image]
    apply Finset.image_congr
    intro e he
    clear he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.comp_apply, Sym2.map_pair_eq, extendEquivLast_castSucc]
  have e2 : (S.image (fun v => s(Fin.castSucc v, Fin.last n))).image
              (Sym2.map (extendEquivLast φ))
          = (S.image φ).image (fun v => s(Fin.castSucc v, Fin.last n)) := by
    rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro v _
    simp only [Function.comp_apply, Sym2.map_pair_eq, extendEquivLast_castSucc,
      extendEquivLast_last]
  have lhs_eq : (augment R (S.image φ)).edges =
      R.edges.image (Sym2.map Fin.castSucc) ∪
      (S.image φ).image (fun v => s(Fin.castSucc v, Fin.last n)) := rfl
  have rhs_eq : (augment G S).edges =
      G.edges.image (Sym2.map Fin.castSucc) ∪
      S.image (fun v => s(Fin.castSucc v, Fin.last n)) := rfl
  rw [lhs_eq, rhs_eq, Finset.image_union, e1, e2]

/-- Augmentation transports `∼sf`: if `G ∼sf R` then for any `S` there is `S'` with
`augment G S ∼sf augment R S'`. -/
theorem augment_transport {n : ℕ} {G R : Sym2Graph n} (hGR : G ∼sf R) (S : Finset (Fin n)) :
    ∃ S' : Finset (Fin n), augment G S ∼sf augment R S' := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv hGR
  refine ⟨S.image φ, sym2GraphEqv_of_equiv (extendEquivLast φ) ?_⟩
  intro e
  rw [augment_edges_image φ hφ S,
    (sym2_map_injective (extendEquivLast φ).injective).mem_finset_image]

/-- Any `(n+1)`-vertex graph is the augmentation of its restriction by the neighbors
of its last vertex. -/
theorem augment_restrict_eq {n : ℕ} (H : Sym2Graph (n + 1)) :
    H = augment (restrict H) (neighborsOfLast H) := by
  apply Sym2Graph.ext
  ext e
  rw [mem_augment_edges]
  constructor
  · induction e using Sym2.ind with
    | _ a b =>
      intro hmem
      cases a using Fin.lastCases with
      | last =>
        cases b using Fin.lastCases with
        | last => exact absurd (Sym2.mk_isDiag_iff.mpr rfl) (H.edges_valid _ hmem)
        | cast j =>
          right
          refine ⟨j, ?_, Sym2.eq_swap⟩
          rw [mem_neighborsOfLast, Sym2.eq_swap]
          exact hmem
      | cast i =>
        cases b using Fin.lastCases with
        | last =>
          right
          exact ⟨i, (mem_neighborsOfLast H i).mpr hmem, rfl⟩
        | cast j =>
          left
          refine ⟨s(i, j), ?_, by rw [Sym2.map_pair_eq]⟩
          rw [mem_restrict_edges]
          refine ⟨?_, by rw [Sym2.map_pair_eq]; exact hmem⟩
          rw [Sym2.mk_isDiag_iff]
          intro hij
          exact (H.edges_valid _ hmem) (Sym2.mk_isDiag_iff.mpr (by rw [hij]))
  · rintro (⟨e₀, he₀, rfl⟩ | ⟨v, hv, rfl⟩)
    · rw [mem_restrict_edges] at he₀; exact he₀.2
    · exact (mem_neighborsOfLast H v).mp hv

/-- Completeness of the augmentation generator: every graph is `∼sf` to a representative. -/
theorem augReps_complete : ∀ (n : ℕ) (G : Sym2Graph n), ∃ R ∈ augReps n, G ∼sf R
  | 0 => by
    intro G
    haveI : IsEmpty (Sym2 (Fin 0)) :=
      ⟨fun e => by induction e using Sym2.ind with | _ a b => exact a.elim0⟩
    refine ⟨⟨∅, by simp⟩, List.mem_cons_self, ?_⟩
    exact sym2GraphEqv_of_equiv (Equiv.refl (Fin 0)) (fun e => isEmptyElim e)
  | n + 1 => by
    intro H
    obtain ⟨R₀, hR₀mem, hR₀iso⟩ := augReps_complete n (restrict H)
    obtain ⟨S', hS'⟩ := augment_transport hR₀iso (neighborsOfLast H)
    have hHiso : H ∼sf augment R₀ S' := by rw [augment_restrict_eq H]; exact hS'
    have hmemFlat : augment R₀ S' ∈ (augReps n).flatMap augmentAll :=
      List.mem_flatMap.mpr ⟨R₀, hR₀mem, mem_augmentAll R₀ S'⟩
    obtain ⟨R, hRmem, hRiso⟩ :=
      foldl_dedupStep_complete ((augReps n).flatMap augmentAll) [] (augment R₀ S') hmemFlat
    exact ⟨R, hRmem, Sym2GraphEqv.trans hHiso hRiso⟩

/-- The augmentation generator produces a `Nodup` flag list. -/
theorem augReps_flags_nodup (n : ℕ) :
    ((augReps n).map (Quotient.mk (Sym2GraphSetoid n))).Nodup := by
  cases n with
  | zero => simp [augReps]
  | succ m =>
    exact foldl_dedupStep_flags_nodup ((augReps m).flatMap augmentAll) [] (by simp)

/-! ## Degree-prefilter dedup correctness

The runtime generator `augRepsDeg` deduplicates with a cheap-key prefilter. We
show it produces the same list as the specification `augReps` (`augRepsDeg_fst_eq`),
so all completeness/`Nodup` results transfer. The only nontrivial fact is that the
cheap key (`degKey`) is an isomorphism invariant (`degKey_iso_invariant`); the rest
is a fold simulation that reuses `isEmptyIsoFast_bool`'s soundness. -/

/-- `List.any` only sees the list's elements, so a predicate change that agrees on
every member leaves it unchanged. -/
theorem any_eq_of_forall_mem {α : Type*} (l : List α) {P Q : α → Bool}
    (h : ∀ a ∈ l, P a = Q a) : l.any P = l.any Q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- Fold simulation: the prefiltered `dedupStepDeg` fold (on key-tagged graphs)
makes the same keep/drop decisions as the `dedupStep` fold, because the cheap key
is an iso invariant and `isEmptyIsoFast_bool` is sound. We carry two invariants:
the first components match, and every tag equals its graph's `degKey`. -/
theorem foldl_dedupStepDeg_sim {n : ℕ} (xs : List (Sym2Graph n)) :
    ∀ (accK : List (Sym2Graph n × (ℕ × List ℕ))) (accU : List (Sym2Graph n)),
      accK.map Prod.fst = accU → (∀ q ∈ accK, q.2 = degKey q.1) →
      ((xs.map withDegKey).foldl dedupStepDeg accK).map Prod.fst = xs.foldl dedupStep accU
        ∧ (∀ q ∈ (xs.map withDegKey).foldl dedupStepDeg accK, q.2 = degKey q.1) := by
  induction xs with
  | nil => intro accK accU h1 h2; exact ⟨h1, h2⟩
  | cons x rest ih =>
    intro accK accU h1 h2
    simp only [List.map_cons, List.foldl_cons]
    have hany : accK.any (fun q => q.2 == degKey x && isEmptyIsoFast_bool q.1 x)
        = accU.any (fun H => isEmptyIsoFast_bool H x) := by
      rw [← h1, List.any_map]
      apply any_eq_of_forall_mem
      intro q hq
      rw [h2 q hq]
      by_cases hiso : isEmptyIsoFast_bool q.1 x = true
      · have hkey : degKey q.1 = degKey x :=
          degKey_iso_invariant (isEmptyIsoFast_bool_true_correct hiso)
        simp [hiso, hkey]
      · simp only [Bool.not_eq_true] at hiso
        simp [hiso]
    have e1 : dedupStepDeg accK (withDegKey x)
        = if accK.any (fun q => q.2 == degKey x && isEmptyIsoFast_bool q.1 x) = true
          then accK else accK ++ [withDegKey x] := rfl
    have e2 : dedupStep accU x
        = if accU.any (fun H => isEmptyIsoFast_bool H x) = true
          then accU else accU ++ [x] := rfl
    by_cases hb : accK.any (fun q => q.2 == degKey x && isEmptyIsoFast_bool q.1 x) = true
    · rw [e1, if_pos hb, e2, if_pos (by rw [← hany]; exact hb)]
      exact ih accK accU h1 h2
    · rw [e1, if_neg hb, e2, if_neg (by rw [← hany]; exact hb)]
      apply ih
      · simp [List.map_append, withDegKey, h1]
      · intro q hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | hq
        · exact h2 q hq
        · subst hq; rfl

/-- The fast generator's first components agree with the specification `augReps`. -/
theorem augRepsDeg_fst_eq (n : ℕ) : (augRepsDeg n).map Prod.fst = augReps n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show (((((augRepsDeg m).map Prod.fst).flatMap augmentAll).map withDegKey).foldl
      dedupStepDeg []).map Prod.fst = ((augReps m).flatMap augmentAll).foldl dedupStep []
    rw [ih]
    exact (foldl_dedupStepDeg_sim ((augReps m).flatMap augmentAll) [] [] rfl (by simp)).1

theorem genSym2GraphsDedup_eq (n : ℕ) : genSym2GraphsDedup n = augReps n := by
  unfold genSym2GraphsDedup; exact augRepsDeg_fst_eq n

/-! ## Completeness, no-duplication, and `= univ` -/

theorem genSym2GraphsDedup_complete {n : ℕ} (G : Sym2Graph n) :
    ∃ G', G' ∈ genSym2GraphsDedup n ∧ G ∼sf G' := by
  rw [genSym2GraphsDedup_eq]
  obtain ⟨R, hRmem, hiso⟩ := augReps_complete n G
  exact ⟨R, hRmem, hiso⟩

theorem genSym2Graphs_perm (n : ℕ) :
    genSym2Graphs n ~ genSym2GraphsDedup n := by
  unfold genSym2Graphs genSym2GraphsKeyed
  have h := (List.perm_insertionSort (fun a b => graphKeyLe a.2 b.2 = true)
    ((genSym2GraphsDedup n).map (fun G => (G, graphKey G)))).map Prod.fst
  rw [List.map_map] at h
  have hid : (Prod.fst ∘ fun G : Sym2Graph n => (G, graphKey G)) = id := by
    funext G; rfl
  rw [hid, List.map_id] at h
  exact h

theorem genSym2Graphs_complete {n : ℕ} (G : Sym2Graph n) :
    ∃ G', G' ∈ genSym2Graphs n ∧ G ∼sf G' := by
  obtain ⟨G', hmem, hiso⟩ := genSym2GraphsDedup_complete G
  exact ⟨G', (genSym2Graphs_perm n).mem_iff.mpr hmem, hiso⟩

theorem genEmptyTypedFlags_nodup (n : ℕ) : (genEmptyTypedFlags n).Nodup := by
  unfold genEmptyTypedFlags
  have hperm : (genSym2Graphs n).map (Quotient.mk (Sym2GraphSetoid n)) ~
               (genSym2GraphsDedup n).map (Quotient.mk (Sym2GraphSetoid n)) :=
    (genSym2Graphs_perm n).map _
  rw [hperm.nodup_iff, genSym2GraphsDedup_eq]
  exact augReps_flags_nodup n

theorem genEmptyTypedFlagSet_eq_univ (n : ℕ) :
    genEmptyTypedFlagSet n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro F
  obtain ⟨G, rfl⟩ := Quotient.exists_rep F
  obtain ⟨G', hmem, hiso⟩ := genSym2Graphs_complete G
  simp only [genEmptyTypedFlagSet, genEmptyTypedFlags, List.mem_toFinset, List.mem_map]
  exact ⟨G', hmem, Quotient.sound (Sym2GraphEqv.symm hiso)⟩

/-! ## Phase 2: typed-flag enumeration data (matching the JSON flag order)

`generate_flags.py` enumerates, for each underlying graph (in the canonical order
of `genSym2Graphs n`), the valid type embeddings of the type `σ`, groups them into
orbits under the underlying graph's automorphism group, keeps the lexicographically
smallest tuple of each orbit as its representative, and records the downward
coefficient `|orbit| / (n · (n-1) ⋯ (n-k+1))`. Flags are sorted by
`(underlying_graph_num, type_indices)`. The function `genFlagData` reproduces this
data purely in Lean (working on the canonical edge-pair lists produced by
`canonicalEdgeList`), so the `generate_flags` command can synthesize the same named
constants the JSON loader did, in the same order, without reading any JSON file.

This is computed and consumed only at elaboration time; correctness against the
JSON files is checked empirically (`#eval`) and, ultimately, by the per-flag
`native_decide` (downward coefficient) and the `= univ` completeness check. -/

/-- Whether the canonical edge-pair list `edges` contains the edge `{u, v}`. -/
def hasEdgeB (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (min u v, max u v)

/-- All length-`k` tuples over `[0, n)`. -/
def allNatTuples (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap (fun x => (allNatTuples n k).map (x :: ·))

/-- All injective length-`k` tuples over `[0, n)`. -/
def injNatTuples (n k : ℕ) : List (List ℕ) :=
  (allNatTuples n k).filter (fun t => t.dedup.length == t.length)

/-- A tuple `t` (type vertex `a ↦ t[a]`) is a valid embedding of the type with
edge list `sEdges` (on `k` vertices) into the underlying graph with edge list
`eEdges`, i.e. it preserves adjacency and non-adjacency on all type-vertex pairs. -/
def isValidEmbeddingB (sEdges eEdges : List (ℕ × ℕ)) (k : ℕ) (t : List ℕ) : Bool :=
  (List.range k).all (fun a => (List.range k).all (fun b =>
    if a < b then hasEdgeB eEdges (t.getD a 0) (t.getD b 0) == hasEdgeB sEdges a b
    else true))

/-- Sort a list of edge pairs into canonical (lexicographic) order. -/
def sortPairs (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.insertionSort (fun p q => pairLe p q = true) l

/-- Relabel a canonical edge list by a permutation `p` of `[0, n)` (given as a
list), re-canonicalizing each edge. -/
def applyPermToPairs (p : List ℕ) (edges : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  edges.map (fun e =>
    let a := p.getD e.1 0
    let b := p.getD e.2 0
    (min a b, max a b))

/-- The automorphisms of the canonical edge list, as permutations of `[0, n)`. -/
def autPerms (n : ℕ) (edges : List (ℕ × ℕ)) : List (List ℕ) :=
  (List.range n).permutations.filter
    (fun p => sortPairs (applyPermToPairs p edges) == sortPairs edges)

/-- Post-compose an embedding tuple with a permutation (relabel its images). -/
def applyPermToTuple (p t : List ℕ) : List ℕ := t.map (fun v => p.getD v 0)

/-- The orbit of the tuple `t` under the given automorphism permutations. -/
def tupleOrbit (autList : List (List ℕ)) (t : List ℕ) : List (List ℕ) :=
  (autList.map (fun p => applyPermToTuple p t)).dedup

/-- Strict lexicographic `<` on `List ℕ`. -/
def listNatLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then listNatLt as bs else decide (a < b)

/-- Non-strict lexicographic `≤` on `List ℕ`. -/
def listNatLe (s t : List ℕ) : Bool := !(listNatLt t s)

/-- The lexicographically smallest tuple in `ts` (default `[]` when empty). -/
def minTuple (ts : List (List ℕ)) : List ℕ :=
  ts.foldl (fun best t => if listNatLt t best then t else best) (ts.headD [])

/-- Typed-flag data for type `(genSym2Graphs k)[m]` on `n` vertices, in JSON file
order. Each entry is `(underlyingGraphIdx, canonicalUnderlyingEdges, typeIndices,
coeffNum, coeffDen)` with the downward coefficient `coeffNum / coeffDen` reduced. -/
def genFlagData (k m n : ℕ) : List (Nat × List (Nat × Nat) × List Nat × Nat × Nat) :=
  let graphsN := genCanonicalEdgeLists n
  let sEdges := (genCanonicalEdgeLists k).getD m []
  let descF := Nat.descFactorial n k
  (List.range graphsN.length).flatMap (fun j =>
    let eEdges := graphsN.getD j []
    let autE := autPerms n eEdges
    let validEmb := (injNatTuples n k).filter (fun t => isValidEmbeddingB sEdges eEdges k t)
    let reps := List.insertionSort (fun s t => listNatLe s t = true)
                  ((validEmb.map (fun t => minTuple (tupleOrbit autE t))).dedup)
    reps.map (fun rep =>
      let osize := (tupleOrbit autE rep).length
      let g := Nat.gcd osize descF
      (j, eEdges, rep, osize / g, descF / g)))

/-! ## Phase 2 (Step B): mathematical typed-flag completeness (`genFlagSet = univ`)

The empty-typed completeness pipeline above (`allRawSym2Graphs` → dedup →
`genEmptyTypedFlagSet_eq_univ`) is mirrored here for `Sym2LabeledGraph σ n` /
`Sym2Flag σ n`, using the typed fast-iso check `isIsoFast_bool`.

Payoff: the `generate_flags` command discharges `sym2FlagSet_{n}_{k}_{m} = univ`
by a cheap `native_decide` bridge to `genFlagSet σ n` plus the *mathematical*
`genFlagSet_eq_univ`, instead of the prohibitive `native_decide` that materialised
`Finset.univ : Finset (Sym2Flag σ n)` — which forces the entire
`Fintype (Sym2LabeledGraph σ n)` enumeration over *all* `2 ^ (C(n,2)+n)` edge
subsets × graph embeddings. The bridge enumerates only the `2 ^ C(n,2)` genuine
underlying graphs (their type embeddings filtered) and the `= univ` is a symbolic
kernel-checked proof, not a reduction. -/

/-- All functions `Fin k → Fin n`, enumerated computably (length `n ^ k`). Used to
enumerate type embeddings as a genuine `List` (`Finset.univ.toList` is noncomputable,
so cannot be evaluated by `native_decide`). -/
def allFinMaps (n : ℕ) : (k : ℕ) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap (fun x => (allFinMaps n k).map (Fin.cons x))

theorem mem_allFinMaps {n : ℕ} : ∀ {k : ℕ} (f : Fin k → Fin n), f ∈ allFinMaps n k
  | 0, f => by
    simp only [allFinMaps, List.mem_singleton]
    exact funext (fun i => i.elim0)
  | k + 1, f => by
    rw [allFinMaps, List.mem_flatMap]
    refine ⟨f 0, List.mem_finRange _, ?_⟩
    rw [List.mem_map]
    exact ⟨Fin.tail f, mem_allFinMaps _, Fin.cons_self_tail f⟩

/-- Build the `σ`-typed labeled-graph embedding from a candidate vertex map `f`,
returning `none` when `f` is not a graph embedding of `σ` into `G`. Computable
counterpart of picking an element of `Finset.univ : Finset (… ↪g …)`. -/
def mkTypeEmbedding? {k : ℕ} (σ : Sym2FlagType k) {n : ℕ} (G : Sym2Graph n)
    (f : Fin k → Fin n) :
    Option ((SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) ↪g
      (SimpleGraph.fromEdgeSet (SetLike.coe G.edges))) :=
  if h : Function.Injective f ∧
      (∀ a b, (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj (f a) (f b) ↔
        (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)).Adj a b)
  then some ⟨⟨f, h.1⟩, fun {a b} => h.2 a b⟩
  else none

theorem mkTypeEmbedding?_self {k : ℕ} (σ : Sym2FlagType k) {n : ℕ} (G : Sym2Graph n)
    (emb : (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) ↪g
      (SimpleGraph.fromEdgeSet (SetLike.coe G.edges))) :
    mkTypeEmbedding? σ G (fun x => emb x) = some emb := by
  have h : Function.Injective (fun x => emb x) ∧
      (∀ a b, (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj (emb a) (emb b) ↔
        (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)).Adj a b) :=
    ⟨emb.injective, fun a b => emb.map_rel_iff⟩
  rw [mkTypeEmbedding?, dif_pos h]
  congr 1

/-- For a fixed underlying graph `G : Sym2Graph n`, all `σ`-typed labeled graphs
with that underlying edge set: one per graph embedding of the decoded type `σ`. -/
def labeledOfGraph {k : ℕ} (σ : Sym2FlagType k) {n : ℕ} (G : Sym2Graph n) :
    List (Sym2LabeledGraph σ n) :=
  (allFinMaps n k).filterMap (fun f =>
    (mkTypeEmbedding? σ G f).map (fun emb => ⟨G.edges, G.edges_valid, emb⟩))

/-- All `Sym2LabeledGraph σ n`, enumerated computably as: for every raw underlying
graph (subsets of `allEdges n`), every type embedding of `σ` into it. -/
def allRawSym2LabeledGraphs {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n) :=
  (allRawSym2Graphs n).flatMap (labeledOfGraph σ)

theorem mem_allRawSym2LabeledGraphs {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : G ∈ allRawSym2LabeledGraphs σ n := by
  rw [allRawSym2LabeledGraphs, List.mem_flatMap]
  -- Pick the underlying graph `⟨G.edges, G.edges_valid⟩` itself: its `edges`
  -- field is *definitionally* `G.edges`, so `G.type_embed` fits with no transport.
  refine ⟨⟨G.edges, G.edges_valid⟩, mem_allRawSym2Graphs _, ?_⟩
  rw [labeledOfGraph, List.mem_filterMap]
  refine ⟨fun x => G.type_embed x, mem_allFinMaps _, ?_⟩
  rw [mkTypeEmbedding?_self]
  rfl

/-- The fast labeled enumeration: `σ`-typed labeled graphs built over only the
*canonical* underlying graphs `genSym2Graphs n` (the augmentation reps — 156 at
`n = 6`), instead of all `2 ^ C(n,2)` raw edge subsets (491520 at `n = 6`). Not every
labeled graph is *literally* here, but every one is `∼sf` to an element
(`allAugSym2LabeledGraphs_complete`) — all the dedup/`= univ` chain needs — so the
bridge never materialises the brute-force list. -/
def allAugSym2LabeledGraphs {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n) :=
  (genSym2Graphs n).flatMap (labeledOfGraph σ)

/-- Transport a labeled graph along an isomorphism of its underlying graph: if `H`'s
underlying graph is `∼sf` to `R`, then `H` is `∼sf` to the labeled graph over `R`
obtained by post-composing `H`'s type embedding with the underlying iso, which lies in
`labeledOfGraph σ R`. The labeled analogue of the embedding-free transport used for
`genSym2Graphs_complete`. -/
theorem mem_labeledOfGraph_eqv_of_underlying {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (H : Sym2LabeledGraph σ n) {R : Sym2Graph n}
    (hiso : (⟨H.edges, H.edges_valid⟩ : Sym2Graph n) ∼sf R) :
    ∃ H', H' ∈ labeledOfGraph σ R ∧ H ∼sf H' := by
  have ψ : (SimpleGraph.fromEdgeSet (SetLike.coe H.edges)) ≃g
      (SimpleGraph.fromEdgeSet (SetLike.coe R.edges)) := by
    have h := hiso.some.graph_iso
    simpa only [Sym2Graph.toLabeledGraph] using h
  set emb' : (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)) ↪g
      (SimpleGraph.fromEdgeSet (SetLike.coe R.edges)) :=
    ψ.toEmbedding.comp H.type_embed with hemb'
  refine ⟨⟨R.edges, R.edges_valid, emb'⟩, ?_, ?_⟩
  · rw [labeledOfGraph, List.mem_filterMap]
    refine ⟨fun x => emb' x, mem_allFinMaps _, ?_⟩
    rw [mkTypeEmbedding?_self]
    rfl
  · refine Nonempty.intro { graph_iso := ?_, type_preserve := ?_ }
    · exact ψ
    · rfl

/-- Every labeled graph is `∼sf` to an element of the fast augmentation-based
enumeration. The fast replacement for the literal `mem_allRawSym2LabeledGraphs`. -/
theorem allAugSym2LabeledGraphs_complete {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (H : Sym2LabeledGraph σ n) :
    ∃ H', H' ∈ allAugSym2LabeledGraphs σ n ∧ H ∼sf H' := by
  obtain ⟨R, hRmem, hRiso⟩ :=
    genSym2Graphs_complete (⟨H.edges, H.edges_valid⟩ : Sym2Graph n)
  obtain ⟨H', hH'mem, hH'iso⟩ := mem_labeledOfGraph_eqv_of_underlying H hRiso
  exact ⟨H', List.mem_flatMap.mpr ⟨R, hRmem, hH'mem⟩, hH'iso⟩

/-! ### Generation (dedup by `isIsoFast_bool`) -/

/-- One `foldl` step: append `G` unless some survivor is fast-iso to it. -/
def dedupStepL {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (acc : List (Sym2LabeledGraph σ n)) (G : Sym2LabeledGraph σ n) :
    List (Sym2LabeledGraph σ n) :=
  if acc.any (fun H => isIsoFast_bool H G) = true then acc else acc ++ [G]

/-- Attach the cheap key to a labeled graph as a precomputed bucketing key. -/
def withLabeledDegKey {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Sym2LabeledGraph σ n × (ℕ × List ℕ) :=
  (G, labeledDegKey G)

/-- Keyed deduplication step with a cheap prefilter: keep `p` unless some survivor shares
its cheap key (`q.2 == p.2`, `O(n)`) *and* is `isIsoFast_bool` to it. The `&&` short-circuits,
so the expensive iso test runs only on cheap-key collisions. Makes the same keep/drop
decisions as `dedupStepL` because the cheap key is an iso invariant (`foldl_dedupStepDegL_sim`).
The labeled analogue of `dedupStepDeg`. -/
def dedupStepDegL {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (acc : List (Sym2LabeledGraph σ n × (ℕ × List ℕ)))
    (p : Sym2LabeledGraph σ n × (ℕ × List ℕ)) :
    List (Sym2LabeledGraph σ n × (ℕ × List ℕ)) :=
  if acc.any (fun q => q.2 == p.2 && isIsoFast_bool q.1 p.1) = true then acc
  else acc ++ [p]

/-- The deduplicated typed labeled graphs, key-tagged, produced by the cheap-key-prefiltered
fold. `genLabeledGraphsDedup_eq` proves its first components equal the naive `dedupStepL`
fold, so all completeness/`Nodup` reasoning happens on the latter. -/
def genLabeledGraphsDedupKeyed {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n × (ℕ × List ℕ)) :=
  ((allAugSym2LabeledGraphs σ n).map withLabeledDegKey).foldl dedupStepDegL []

/-- The deduplicated typed labeled graphs: one representative per `∼sf`-class, computed by
the cheap-key-prefiltered fold (equal to the naive `dedupStepL` fold by
`genLabeledGraphsDedup_eq`). -/
def genLabeledGraphsDedup {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n) :=
  (genLabeledGraphsDedupKeyed σ n).map Prod.fst

/-- The typed flags (quotient classes) of the generated labeled graphs. -/
def genFlags {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) : List (Sym2Flag σ n) :=
  (genLabeledGraphsDedup σ n).map (Quotient.mk (sym2LabeledGraphSetoid σ n))

/-- The finset of generated typed flags. -/
def genFlagSet {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) : Finset (Sym2Flag σ n) :=
  (genFlags σ n).toFinset

/-- Direct completeness of `isIsoFast_bool` (from the contrapositive). -/
theorem isIsoFast_bool_complete {k n : ℕ} {σ : Sym2FlagType k}
    {G G' : Sym2LabeledGraph σ n} (h : G ∼sf G') :
    isIsoFast_bool G G' = true := by
  by_contra hne
  exact isIsoFast_bool_false_correct (eq_false_of_ne_true hne) h

/-! ### Foldl invariants -/

theorem mem_dedupStepL_of_mem {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (acc : List (Sym2LabeledGraph σ n)) (x : Sym2LabeledGraph σ n)
    {G : Sym2LabeledGraph σ n} (hG : G ∈ acc) : G ∈ dedupStepL acc x := by
  unfold dedupStepL
  split
  · exact hG
  · exact List.mem_append.mpr (Or.inl hG)

/-- Elements of the accumulator persist through the rest of the fold. -/
theorem foldl_dedupStepL_mono {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (xs : List (Sym2LabeledGraph σ n)) :
    ∀ (acc : List (Sym2LabeledGraph σ n)) (G : Sym2LabeledGraph σ n), G ∈ acc →
      G ∈ xs.foldl dedupStepL acc := by
  induction xs with
  | nil => intro acc G hG; simpa using hG
  | cons x rest ih =>
    intro acc G hG
    simp only [List.foldl_cons]
    exact ih (dedupStepL acc x) G (mem_dedupStepL_of_mem acc x hG)

/-- Every input element is `∼sf`-equivalent to some surviving element. -/
theorem foldl_dedupStepL_complete {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (xs : List (Sym2LabeledGraph σ n)) :
    ∀ (acc : List (Sym2LabeledGraph σ n)) (G : Sym2LabeledGraph σ n), G ∈ xs →
      ∃ G', G' ∈ xs.foldl dedupStepL acc ∧ G ∼sf G' := by
  induction xs with
  | nil => intro acc G hG; exact absurd hG (by simp)
  | cons x rest ih =>
    intro acc G hG
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hG with hGx | hGrest
    · have hx : ∃ G', G' ∈ dedupStepL acc x ∧ x ∼sf G' := by
        unfold dedupStepL
        by_cases hc : acc.any (fun H => isIsoFast_bool H x) = true
        · rw [if_pos hc]
          obtain ⟨G', hG'mem, hG'true⟩ := List.any_eq_true.mp hc
          exact ⟨G', hG'mem, sym2LabeledGraphEqv.symm (isIsoFast_bool_true_correct hG'true)⟩
        · rw [if_neg hc]
          exact ⟨x, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)),
            sym2LabeledGraphEqv.refl x⟩
      obtain ⟨G', hG'mem, hxG'⟩ := hx
      refine ⟨G', foldl_dedupStepL_mono rest (dedupStepL acc x) G' hG'mem, ?_⟩
      rw [hGx]; exact hxG'
    · exact ih (dedupStepL acc x) G hGrest

/-! ### Completeness and `= univ` -/

/-- Fold simulation: the prefiltered `dedupStepDegL` fold makes the same keep/drop decisions
as the `dedupStepL` fold, because the cheap key is an iso invariant and `isIsoFast_bool` is
sound. We carry two invariants: the first components match, and every tag is its graph's
`labeledDegKey`. The labeled analogue of `foldl_dedupStepDeg_sim`. -/
theorem foldl_dedupStepDegL_sim {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (xs : List (Sym2LabeledGraph σ n)) :
    ∀ (accK : List (Sym2LabeledGraph σ n × (ℕ × List ℕ)))
      (accU : List (Sym2LabeledGraph σ n)),
      accK.map Prod.fst = accU → (∀ q ∈ accK, q.2 = labeledDegKey q.1) →
      ((xs.map withLabeledDegKey).foldl dedupStepDegL accK).map Prod.fst
          = xs.foldl dedupStepL accU
        ∧ (∀ q ∈ (xs.map withLabeledDegKey).foldl dedupStepDegL accK,
            q.2 = labeledDegKey q.1) := by
  induction xs with
  | nil => intro accK accU h1 h2; exact ⟨h1, h2⟩
  | cons x rest ih =>
    intro accK accU h1 h2
    simp only [List.map_cons, List.foldl_cons]
    have hany : accK.any (fun q => q.2 == labeledDegKey x && isIsoFast_bool q.1 x)
        = accU.any (fun H => isIsoFast_bool H x) := by
      rw [← h1, List.any_map]
      apply any_eq_of_forall_mem
      intro q hq
      rw [h2 q hq]
      by_cases hiso : isIsoFast_bool q.1 x = true
      · have hkey : labeledDegKey q.1 = labeledDegKey x :=
          labeledDegKey_iso_invariant (isIsoFast_bool_true_correct hiso)
        simp [hiso, hkey]
      · simp only [Bool.not_eq_true] at hiso
        simp [hiso]
    have e1 : dedupStepDegL accK (withLabeledDegKey x)
        = if accK.any (fun q => q.2 == labeledDegKey x && isIsoFast_bool q.1 x) = true
          then accK else accK ++ [withLabeledDegKey x] := rfl
    have e2 : dedupStepL accU x
        = if accU.any (fun H => isIsoFast_bool H x) = true
          then accU else accU ++ [x] := rfl
    by_cases hb : accK.any (fun q => q.2 == labeledDegKey x && isIsoFast_bool q.1 x) = true
    · rw [e1, if_pos hb, e2, if_pos (by rw [← hany]; exact hb)]
      exact ih accK accU h1 h2
    · rw [e1, if_neg hb, e2, if_neg (by rw [← hany]; exact hb)]
      apply ih
      · simp [List.map_append, withLabeledDegKey, h1]
      · intro q hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | hq
        · exact h2 q hq
        · subst hq; rfl

/-- The cheap-key-prefiltered dedup equals the naive `dedupStepL` fold (first components),
so all completeness/`Nodup` reasoning transfers. The labeled analogue of `augRepsDeg_fst_eq`. -/
theorem genLabeledGraphsDedup_eq {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    genLabeledGraphsDedup σ n = (allAugSym2LabeledGraphs σ n).foldl dedupStepL [] := by
  unfold genLabeledGraphsDedup genLabeledGraphsDedupKeyed
  exact (foldl_dedupStepDegL_sim (allAugSym2LabeledGraphs σ n) [] [] rfl (by simp)).1

theorem genLabeledGraphsDedup_complete {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    ∃ G', G' ∈ genLabeledGraphsDedup σ n ∧ G ∼sf G' := by
  rw [genLabeledGraphsDedup_eq]
  obtain ⟨H', hH'mem, hGH'⟩ := allAugSym2LabeledGraphs_complete G
  obtain ⟨G', hG'mem, hH'G'⟩ :=
    foldl_dedupStepL_complete (allAugSym2LabeledGraphs σ n) [] H' hH'mem
  exact ⟨G', hG'mem, sym2LabeledGraphEqv.trans hGH' hH'G'⟩

theorem genFlagSet_eq_univ {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    genFlagSet σ n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro F
  obtain ⟨G, rfl⟩ := Quotient.exists_rep F
  obtain ⟨G', hmem, hiso⟩ := genLabeledGraphsDedup_complete G
  simp only [genFlagSet, genFlags, List.mem_toFinset, List.mem_map]
  exact ⟨G', hmem, Quotient.sound (sym2LabeledGraphEqv.symm hiso)⟩

/-! ### O(g) JSON-order bridge for labeled flags

Mirrors the empty-typed `genSym2Graphs` sort layer (`genSym2GraphsKeyed` +
`genSym2Graphs_perm`): re-sort the dedup reps into `genFlagData`'s
`(underlyingGraphIdx, typeIndices)` order so the `generate_flags` macro can bridge
its named flag list to `genFlagsOrdered` with an O(g) positional `native_decide`
(one isomorphism check per position) instead of the O(g²) `Finset`-equality bridge
to `genFlagSet` plus a separate O(g²) `Nodup` `native_decide`. `genFlagsOrdered_perm`
proves it is a permutation of `genFlags`, so `= univ` and `Nodup` transfer through the
existing order-independent `genFlagSet_eq_univ` / `genFlags_nodup`. -/

/-- `G`'s underlying edge-pair list (identity relabeling), in ℕ coordinates and
canonical (`pairLe`) sort order. Equals `relabeledEdgeList` under the identity. -/
def rawPairsNat {n : ℕ} (G : Sym2Graph n) : List (ℕ × ℕ) :=
  sortPairs (((allEdges n).filter (fun e => decide (e ∈ G.edges))).map edgeToPair)

/-- An ℕ-permutation of `[0, n)` relabeling `G`'s edges into `canonicalEdgeList G`.
Any two such perms differ by an automorphism of the canonical graph, so the
orbit-min computed from it (below) is independent of which one `find?` returns. -/
def canonicalizingPerm {n : ℕ} (G : Sym2Graph n) : List ℕ :=
  ((List.range n).permutations.find?
    (fun p => sortPairs (applyPermToPairs p (rawPairsNat G)) == canonicalEdgeList G)).getD
    (List.range n)

/-- The type-embedding tuple `[type_embed 0, …, type_embed (k-1)]` of a labeled
graph, in its own (raw) coordinates. -/
def labeledTypeTuple {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : List ℕ :=
  (List.finRange k).map (fun i => (G.type_embed i).val)

/-- JSON-order sort key of a labeled flag representative: the underlying graph's
`graphKey` (edge count, canonical edge list) and the orbit-minimal type tuple in
canonical coordinates. Class-invariant, matching `genFlagData`'s ordering. -/
def labeledFlagKey {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : (ℕ × List (ℕ × ℕ)) × List ℕ :=
  let Gu : Sym2Graph n := ⟨G.edges, G.edges_valid⟩
  let cel := canonicalEdgeList Gu
  let p := canonicalizingPerm Gu
  let tCanon := applyPermToTuple p (labeledTypeTuple G)
  (graphKey Gu, minTuple (tupleOrbit (autPerms n cel) tCanon))

/-- Lexicographic `≤` on labeled flag keys: edge count, then canonical edge list,
then orbit-min type tuple. -/
def labeledKeyLe (a b : (ℕ × List (ℕ × ℕ)) × List ℕ) : Bool :=
  decide (a.1.1 < b.1.1) ||
    (a.1.1 == b.1.1 &&
      (listPairLt a.1.2 b.1.2 ||
        (a.1.2 == b.1.2 && listNatLe a.2 b.2)))

/-- `genFlags σ n` re-sorted into `genFlagData` (JSON) order via `labeledFlagKey`.
A permutation of `genFlags σ n` (same set, so `= univ` is inherited) but in the
order the `generate_flags` macro emits its named flag list.

Decorate-sort-undecorate (as in `genSym2GraphsKeyed`): each rep's `labeledFlagKey`
— which scans all `n!` permutations (`canonicalEdgeList`, `canonicalizingPerm`,
`autPerms`) — is computed *once* and carried through the sort, so the `O(g²)`
comparisons read the precomputed key instead of recomputing it. -/
def genFlagsOrdered {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) : List (Sym2Flag σ n) :=
  (((genLabeledGraphsDedup σ n).map (fun G => (G, labeledFlagKey G))).insertionSort
    (fun a b => labeledKeyLe a.2 b.2 = true)).map
    (fun a => Quotient.mk (sym2LabeledGraphSetoid σ n) a.1)

/-- `genFlagsOrdered σ n` is a permutation of `genFlags σ n`: the sort only reorders
the dedup reps. Mirrors `genSym2Graphs_perm`. -/
theorem genFlagsOrdered_perm {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    genFlagsOrdered σ n ~ genFlags σ n := by
  unfold genFlagsOrdered genFlags
  have h := (List.perm_insertionSort (fun a b => labeledKeyLe a.2 b.2 = true)
    ((genLabeledGraphsDedup σ n).map (fun G => (G, labeledFlagKey G)))).map
    (fun a => Quotient.mk (sym2LabeledGraphSetoid σ n) a.1)
  rw [List.map_map] at h
  have hid : ((fun a => Quotient.mk (sym2LabeledGraphSetoid σ n) a.1) ∘
        fun G : Sym2LabeledGraph σ n => (G, labeledFlagKey G))
      = Quotient.mk (sym2LabeledGraphSetoid σ n) := by
    funext G; rfl
  rw [hid] at h
  exact h

/-- The deduped labeled flags stay `Nodup` (no two survivors are `∼sf`-equivalent).
The labeled analogue of `foldl_dedupStep_flags_nodup`. -/
theorem foldl_dedupStepL_flags_nodup {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (xs : List (Sym2LabeledGraph σ n)) :
    ∀ (acc : List (Sym2LabeledGraph σ n)),
      (acc.map (Quotient.mk (sym2LabeledGraphSetoid σ n))).Nodup →
      ((xs.foldl dedupStepL acc).map (Quotient.mk (sym2LabeledGraphSetoid σ n))).Nodup := by
  induction xs with
  | nil => intro acc hacc; exact hacc
  | cons x rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    unfold dedupStepL
    by_cases hc : acc.any (fun H => isIsoFast_bool H x) = true
    · rw [if_pos hc]; exact hacc
    · rw [if_neg hc, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
      refine ⟨hacc, List.nodup_singleton _, ?_⟩
      intro F hFacc b hb heq
      rw [List.mem_singleton] at hb
      subst hb
      subst heq
      obtain ⟨G', hG'mem, hG'eq⟩ := List.mem_map.mp hFacc
      have hG'x : G' ∼sf x := Quotient.exact hG'eq
      exact hc (List.any_eq_true.mpr ⟨G', hG'mem, isIsoFast_bool_complete hG'x⟩)

/-- The generated typed flags have no duplicates. Mirrors `genEmptyTypedFlags_nodup`. -/
theorem genFlags_nodup {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    (genFlags σ n).Nodup := by
  unfold genFlags
  rw [genLabeledGraphsDedup_eq]
  exact foldl_dedupStepL_flags_nodup (allAugSym2LabeledGraphs σ n) [] (by simp)

/-- `genFlagsOrdered σ n` has no duplicates (inherited from `genFlags` via the perm). -/
theorem genFlagsOrdered_nodup {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    (genFlagsOrdered σ n).Nodup :=
  (genFlagsOrdered_perm σ n).nodup_iff.mpr (genFlags_nodup σ n)

/-- `genFlagsOrdered σ n` has the same `toFinset` as `genFlags σ n` (i.e. `genFlagSet`),
since they are permutations. Lets the `generate_flags` `= univ` bridge rewrite the
named flag list's `toFinset` to the proven-complete `genFlagSet`. -/
theorem genFlagsOrdered_toFinset {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    (genFlagsOrdered σ n).toFinset = genFlagSet σ n := by
  unfold genFlagSet
  exact Finset.ext fun a => by
    simp only [List.mem_toFinset]; exact (genFlagsOrdered_perm σ n).mem_iff

end FlagAlgebras.Compute
