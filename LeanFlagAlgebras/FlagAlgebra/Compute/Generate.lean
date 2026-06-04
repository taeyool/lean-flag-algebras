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

/-- Total preorder used to order graphs into JSON file order: by edge count,
then by canonical edge list. -/
def graphKeyLe {n : ℕ} (G G' : Sym2Graph n) : Bool :=
  decide (G.edges.card < G'.edges.card) ||
    (G.edges.card == G'.edges.card &&
      (listPairLt (canonicalEdgeList G) (canonicalEdgeList G') ||
       canonicalEdgeList G == canonicalEdgeList G'))

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

/-- The deduplicated list: one representative per `∼sf`-class. -/
def genSym2GraphsDedup (n : ℕ) : List (Sym2Graph n) :=
  (allRawSym2Graphs n).foldl dedupStep []

/-- The deduplicated list, re-sorted into canonical JSON order. -/
def genSym2Graphs (n : ℕ) : List (Sym2Graph n) :=
  List.insertionSort (fun G G' => graphKeyLe G G' = true) (genSym2GraphsDedup n)

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

/-! ## Completeness, no-duplication, and `= univ` -/

theorem genSym2GraphsDedup_complete {n : ℕ} (G : Sym2Graph n) :
    ∃ G', G' ∈ genSym2GraphsDedup n ∧ G ∼sf G' :=
  foldl_dedupStep_complete (allRawSym2Graphs n) [] G (mem_allRawSym2Graphs G)

theorem genSym2Graphs_perm (n : ℕ) :
    genSym2Graphs n ~ genSym2GraphsDedup n :=
  List.perm_insertionSort _ _

theorem genSym2Graphs_complete {n : ℕ} (G : Sym2Graph n) :
    ∃ G', G' ∈ genSym2Graphs n ∧ G ∼sf G' := by
  obtain ⟨G', hmem, hiso⟩ := genSym2GraphsDedup_complete G
  exact ⟨G', (genSym2Graphs_perm n).mem_iff.mpr hmem, hiso⟩

theorem genEmptyTypedFlags_nodup (n : ℕ) : (genEmptyTypedFlags n).Nodup := by
  unfold genEmptyTypedFlags
  have hperm : (genSym2Graphs n).map (Quotient.mk (Sym2GraphSetoid n)) ~
               (genSym2GraphsDedup n).map (Quotient.mk (Sym2GraphSetoid n)) :=
    (genSym2Graphs_perm n).map _
  rw [hperm.nodup_iff]
  exact foldl_dedupStep_flags_nodup (allRawSym2Graphs n) [] List.nodup_nil

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
  let graphsN := (genSym2Graphs n).map canonicalEdgeList
  let sEdges := ((genSym2Graphs k).map canonicalEdgeList).getD m []
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

/-! ### Generation (dedup by `isIsoFast_bool`) -/

/-- One `foldl` step: append `G` unless some survivor is fast-iso to it. -/
def dedupStepL {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (acc : List (Sym2LabeledGraph σ n)) (G : Sym2LabeledGraph σ n) :
    List (Sym2LabeledGraph σ n) :=
  if acc.any (fun H => isIsoFast_bool H G) = true then acc else acc ++ [G]

/-- The deduplicated typed labeled graphs: one representative per `∼sf`-class. -/
def genLabeledGraphsDedup {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n) :=
  (allRawSym2LabeledGraphs σ n).foldl dedupStepL []

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

theorem genLabeledGraphsDedup_complete {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    ∃ G', G' ∈ genLabeledGraphsDedup σ n ∧ G ∼sf G' :=
  foldl_dedupStepL_complete (allRawSym2LabeledGraphs σ n) [] G (mem_allRawSym2LabeledGraphs G)

theorem genFlagSet_eq_univ {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    genFlagSet σ n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro F
  obtain ⟨G, rfl⟩ := Quotient.exists_rep F
  obtain ⟨G', hmem, hiso⟩ := genLabeledGraphsDedup_complete G
  simp only [genFlagSet, genFlags, List.mem_toFinset, List.mem_map]
  exact ⟨G', hmem, Quotient.sound (sym2LabeledGraphEqv.symm hiso)⟩

end FlagAlgebras.Compute
