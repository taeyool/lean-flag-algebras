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

end FlagAlgebras.Compute
