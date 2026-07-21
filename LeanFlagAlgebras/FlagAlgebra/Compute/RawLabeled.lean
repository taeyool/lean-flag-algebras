module

public import LeanFlagAlgebras.FlagAlgebra.Compute.FlagEnumeration

@[expose] public section

/-! # Raw List-based labeled-flag enumeration and its ENCODE bridge

This module provides a raw `List`-based mirror of the labeled-flag enumeration
(`labeledOfGraph` / `allAugSym2LabeledGraphs`) using a representation that carries
**no `Finset` and no bundled `↪g` embedding**:

    RawLab := List (ℕ × ℕ) × List ℕ        -- (canonical nat-pair edge list, type-vertex images)

The kernel can reduce these raw enumerations with far less memory than the real
`Sym2LabeledGraph` enumeration, which materialises one `↪g` per (graph, embedding)
pair and OOMs.  The bridge to the real enumeration goes through an **injective
encoder** `rawEnc : Sym2LabeledGraph σ n → RawLab`, never a decoder: the kernel only
ever reduces raw `List` data, while every `↪g`/`Finset` is built in symbolic proof
elaboration.

The key exported facts are:
* `rawLabeledOfGraph_eq_map` (T1): the raw per-graph labeling matches the encoded real one;
* `rawAllAugLabeledFromSeed_eq_map` (T1, flatMapped): same over a whole seed list;
* `rawIsIsoDeg_rawEnc` (T2a): the raw degree-filtered iso test on encodings equals `isIsoFastDeg_bool`.
-/

namespace FlagAlgebras.Compute

open List

/-- A raw labeled graph: canonical nat-pair edge list + the images of the `k`
type vertices (as a `List ℕ`). No `Finset`, no bundled embedding, no proofs. -/
abbrev RawLab := List (ℕ × ℕ) × List ℕ

/-- Kernel-friendly nodup test (avoids Mathlib's non-exposed `List.dedup`). -/
@[expose] def natListNodup : List ℕ → Bool
  | [] => true
  | x :: xs => !xs.contains x && natListNodup xs

/-- All injective length-`k` tuples over `[0, n)` (raw analogue of `injNatTuples`). -/
@[expose] def rawInjTuples (n k : ℕ) : List (List ℕ) :=
  (allNatTuples n k).filter natListNodup

/-- Raw analogue of `labeledOfGraph σ G`: for a fixed underlying edge list `eEdges`,
one `RawLab` per valid embedding of the type `sEdges`. -/
@[expose] def rawLabeledOfGraph (n k : ℕ) (sEdges : List (ℕ × ℕ)) (eEdges : List (ℕ × ℕ)) :
    List RawLab :=
  ((rawInjTuples n k).filter (fun t => isValidEmbeddingB sEdges eEdges k t)).map
    (fun t => (eEdges, t))

/-- Raw labeling of a whole seed list of underlying edge lists. -/
@[expose] def rawAllAugLabeledFromSeed (n k : ℕ) (sEdges : List (ℕ × ℕ))
    (seedEdges : List (List (ℕ × ℕ))) : List RawLab :=
  seedEdges.flatMap (rawLabeledOfGraph n k sEdges)

/-- All candidate (non-loop) edges on `[0, n)` as ordered nat pairs `(i, j)`, `i < j`. -/
@[expose] def allEdgePairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun i =>
    (List.range n).filterMap (fun j => if i < j then some (i, j) else none))

/-- Raw degree-filtered typed iso check (mirror of `isIsoFastDeg_bool`). -/
@[expose] def rawIsIsoDeg (n k : ℕ) (G1 G2 : RawLab) : Bool :=
  let e1 := G1.1; let e2 := G2.1
  let d1 := (List.range n).map (degAtL e1)
  let d2 := (List.range n).map (degAtL e2)
  let eps := allEdgePairs n
  ((dPerms n d1 d2).filter (fun p =>
      (List.range k).all (fun t => p.getD (G1.2.getD t 0) 0 == G2.2.getD t 0)))
    |>.any (fun p => eps.all (fun ep => e1.contains ep == e2.contains (permPair p ep)))

/-- The ENCODER: the raw encoding of a `σ`-typed labeled graph — its underlying
edge list plus the images of the type vertices.  Injective (T0), and it commutes
with the raw enumeration/iso machinery (T1/T2a). -/
@[expose] def rawEnc {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : Sym2LabeledGraph σ n) : RawLab :=
  (edgesNat ⟨G.edges, G.edges_valid⟩, (List.finRange k).map (fun t => (G.type_embed t).val))

@[simp] theorem rawEnc_fst {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : Sym2LabeledGraph σ n) :
    (rawEnc G).1 = edgesNat ⟨G.edges, G.edges_valid⟩ := rfl

@[simp] theorem rawEnc_snd {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : Sym2LabeledGraph σ n) :
    (rawEnc G).2 = (List.finRange k).map (fun t => (G.type_embed t).val) := rfl

/-! ### `natListNodup` characterization -/

theorem natListNodup_iff : ∀ (l : List ℕ), natListNodup l = true ↔ l.Nodup
  | [] => by simp [natListNodup]
  | x :: xs => by
    rw [natListNodup, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons,
      natListNodup_iff xs, List.contains_eq_mem]
    constructor
    · rintro ⟨hx, hxs⟩
      exact ⟨of_decide_eq_false hx, hxs⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨decide_eq_false hx, hxs⟩

theorem natListNodup_eq_decide (l : List ℕ) : natListNodup l = decide l.Nodup := by
  rw [Bool.eq_iff_iff, natListNodup_iff, decide_eq_true_iff]

/-! ### L-tuples: the encoder tuple transports the map-list of type embeddings -/

/-- The type-vertex-image tuple of `Fin.cons x f` prepends `x.val`. -/
theorem finRange_map_cons {n k : ℕ} (x : Fin n) (f' : Fin k → Fin n) :
    (List.finRange (k + 1)).map (fun i => ((Fin.cons x f' : Fin (k + 1) → Fin n) i).val)
      = x.val :: (List.finRange k).map (fun i => (f' i).val) := by
  rw [List.finRange_succ]
  simp only [List.map_cons, List.map_map, Fin.cons_zero, Function.comp_def, Fin.cons_succ]

/-- **L-tuples.** Mapping each type embedding `f` (as `Fin k → Fin n`) to its raw
type-vertex-image tuple turns the computable embedding enumeration `allFinMaps n k`
into the raw tuple enumeration `allNatTuples n k`, *order-preservingly*. -/
theorem allFinMaps_map_val {n : ℕ} : ∀ (k : ℕ),
    (allFinMaps n k).map (fun f => (List.finRange k).map (fun i => (f i).val)) = allNatTuples n k
  | 0 => by simp [allFinMaps, allNatTuples]
  | k + 1 => by
    rw [allFinMaps, allNatTuples, List.map_flatMap,
      show List.range n = (List.finRange n).map (fun i : Fin n => i.val) from
        (List.map_coe_finRange_eq_range).symm,
      List.flatMap_map]
    congr 1
    funext x
    simp only [List.map_map, Function.comp_def]
    rw [funext (fun f' : Fin k → Fin n => finRange_map_cons x f'),
      ← allFinMaps_map_val (n := n) k]
    simp only [List.map_map, Function.comp_def]

/-! ### L-inj: nodup of the raw tuple ↔ injectivity of the embedding -/

theorem natListNodup_map_val_iff {n k : ℕ} (f : Fin k → Fin n) :
    natListNodup ((List.finRange k).map (fun i => (f i).val)) = decide (Function.Injective f) := by
  rw [natListNodup_eq_decide, decide_eq_decide,
    List.nodup_map_iff_inj_on (List.nodup_finRange k)]
  constructor
  · intro h a b hab
    exact h a (List.mem_finRange a) b (List.mem_finRange b) (congrArg Fin.val hab)
  · intro h a _ b _ hab
    exact h (Fin.val_injective hab)

/-! ### L-adj: `isValidEmbeddingB` on the raw tuple ↔ the adjacency-preservation of `f` -/

/-- Reading off a type-vertex image from the raw tuple. -/
theorem getD_finRange_map_val {n k : ℕ} (f : Fin k → Fin n) {a : ℕ} (ha : a < k) :
    ((List.finRange k).map (fun i => (f i).val)).getD a 0 = (f ⟨a, ha⟩).val := by
  have hlen : a < ((List.finRange k).map (fun i => (f i).val)).length := by
    rw [List.length_map, List.length_finRange]; exact ha
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some,
    List.getElem_map, List.getElem_finRange]
  simp

/-- Per-pair edge bridge: the raw `hasEdgeB` test on `edgesNat` decides adjacency in
the decoded graph.  (Handles the self-loop `u = v` case: neither side holds.) -/
theorem hasEdgeB_edgesNat_eq {n : ℕ} (G : Sym2Graph n) (u v : Fin n) :
    hasEdgeB (edgesNat G) u.val v.val
      = decide ((SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj u v) := by
  have hkey : hasEdgeB (edgesNat G) u.val v.val
      = (edgesNat G).contains (edgeNatPair (Sym2.mk (u, v))) := by
    rw [hasEdgeB, edgeNatPair_mk]
  rw [hkey, List.contains_eq_mem, decide_eq_decide, SimpleGraph.fromEdgeSet_adj]
  by_cases huv : u = v
  · subst huv
    constructor
    · intro hmem
      exfalso
      simp only [edgesNat, List.mem_map, List.mem_filter] at hmem
      obtain ⟨e, ⟨hmem2, _⟩, heq⟩ := hmem
      have hnd := not_isDiag_of_mem_allEdges hmem2
      rw [edgeNatPair_injective heq] at hnd
      exact hnd (Sym2.mk_isDiag_iff.mpr rfl)
    · rintro ⟨_, hne⟩; exact absurd rfl hne
  · have hnd : ¬ (Sym2.mk (u, v) : Sym2 (Fin n)).IsDiag := by
      rw [Sym2.mk_isDiag_iff]; exact huv
    have he : (Sym2.mk (u, v)) ∈ allEdges n := mem_allEdges_of_not_isDiag' hnd
    rw [mem_edgesNat_iff G he, SetLike.mem_coe]
    exact ⟨fun h => ⟨h, huv⟩, fun h => h.1⟩

/-- **L-adj (crux).** For *any* `f : Fin k → Fin n` (no injectivity assumed), the raw
adjacency-preservation test `isValidEmbeddingB` on the encoder tuple is exactly the
`Prop` that `f` preserves adjacency both ways between the decoded type `σ` and `G`. -/
theorem isValidEmbeddingB_map_val_iff {k n : ℕ} (σ : Sym2FlagType k) (G : Sym2Graph n)
    (f : Fin k → Fin n) :
    isValidEmbeddingB (edgesNat σ) (edgesNat G) k ((List.finRange k).map (fun i => (f i).val))
      = decide (∀ a b : Fin k, (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj (f a) (f b)
          ↔ (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)).Adj a b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, isValidEmbeddingB]
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro hAll a b
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · have h := hAll a.val a.isLt b.val b.isLt
      rw [if_pos hlt, getD_finRange_map_val f a.isLt, getD_finRange_map_val f b.isLt,
        hasEdgeB_edgesNat_eq G _ _, hasEdgeB_edgesNat_eq σ ⟨a.val, a.isLt⟩ ⟨b.val, b.isLt⟩,
        beq_iff_eq, decide_eq_decide] at h
      exact h
    · have hab : a = b := Fin.ext heq
      subst hab
      simp
    · have h := hAll b.val b.isLt a.val a.isLt
      rw [if_pos hgt, getD_finRange_map_val f b.isLt, getD_finRange_map_val f a.isLt,
        hasEdgeB_edgesNat_eq G _ _, hasEdgeB_edgesNat_eq σ ⟨b.val, b.isLt⟩ ⟨a.val, a.isLt⟩,
        beq_iff_eq, decide_eq_decide] at h
      rw [SimpleGraph.adj_comm _ (f a) (f b), SimpleGraph.adj_comm _ a b]
      exact h
  · intro hP a ha b hb
    by_cases hab : a < b
    · rw [if_pos hab, getD_finRange_map_val f ha, getD_finRange_map_val f hb,
        hasEdgeB_edgesNat_eq G _ _, hasEdgeB_edgesNat_eq σ ⟨a, ha⟩ ⟨b, hb⟩,
        beq_iff_eq, decide_eq_decide]
      exact hP ⟨a, ha⟩ ⟨b, hb⟩
    · rw [if_neg hab]

/-! ### T1: the raw per-graph labeling equals the encoded real labeling -/

/-- `filterMap` of a proof-independent `dite`-guard collapses to `filter` then `map`. -/
theorem filterMap_dite {α β : Type _} (C : α → Prop) [DecidablePred C] (V : α → β)
    (l : List α) :
    l.filterMap (fun a => if _ : C a then some (V a) else none)
      = (l.filter (fun a => decide (C a))).map V := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h : C a
    · rw [dif_pos h, decide_eq_true h, if_pos rfl, List.map_cons, ih]
    · rw [dif_neg h, decide_eq_false h, if_neg (by simp), ih]

/-- The `rawEnc` of the labeled graph built from `f` (when `f` is a valid embedding),
as a `dite`-guard producing exactly the raw pair `(edgesNat G, tuple f)`. -/
theorem mkTypeEmbedding_map_rawEnc {k n : ℕ} (σ : Sym2FlagType k) (G : Sym2Graph n)
    (f : Fin k → Fin n) :
    (mkTypeEmbedding? σ G f).map
        (fun emb => rawEnc (⟨G.edges, G.edges_valid, emb⟩ : Sym2LabeledGraph σ n))
      = if _ : (Function.Injective f ∧ ∀ a b,
            (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj (f a) (f b)
              ↔ (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)).Adj a b)
        then some ((edgesNat G, (List.finRange k).map (fun i => (f i).val)) : RawLab)
        else none := by
  unfold mkTypeEmbedding?
  by_cases h : (Function.Injective f ∧ ∀ a b,
      (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj (f a) (f b)
        ↔ (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)).Adj a b)
  · rw [dif_pos h, dif_pos h, Option.map_some]; rfl
  · rw [dif_neg h, dif_neg h, Option.map_none]

/-- **T1.**  The raw per-graph labeling of the encoded type/graph edge lists equals
the encodings of the real per-graph labeling. -/
theorem rawLabeledOfGraph_eq_map {k n : ℕ} (σ : Sym2FlagType k) (G : Sym2Graph n) :
    rawLabeledOfGraph n k (edgesNat σ) (edgesNat G) = (labeledOfGraph σ G).map rawEnc := by
  rw [labeledOfGraph, List.map_filterMap]
  have hbody : (fun f : Fin k → Fin n =>
        ((mkTypeEmbedding? σ G f).map
          (fun emb => (⟨G.edges, G.edges_valid, emb⟩ : Sym2LabeledGraph σ n))).map rawEnc)
      = (fun f => if _ : (Function.Injective f ∧ ∀ a b,
            (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).Adj (f a) (f b)
              ↔ (SimpleGraph.fromEdgeSet (SetLike.coe σ.edges)).Adj a b)
          then some ((edgesNat G, (List.finRange k).map (fun i => (f i).val)) : RawLab)
          else none) := by
    funext f
    rw [Option.map_map]
    exact mkTypeEmbedding_map_rawEnc σ G f
  rw [hbody, filterMap_dite, rawLabeledOfGraph, rawInjTuples, ← allFinMaps_map_val (n := n) k,
    List.filter_map, List.filter_map, List.filter_filter, List.map_map]
  congr 1
  congr 1
  funext f
  simp only [Function.comp_apply]
  rw [natListNodup_map_val_iff, isValidEmbeddingB_map_val_iff, Bool.and_comm, ← Bool.decide_and]

/-- **T1, flatMapped.**  Over a whole seed list of underlying graphs, the raw seed
labeling equals the encodings of the real seed labeling. -/
theorem rawAllAugLabeledFromSeed_eq_map {k n : ℕ} (σ : Sym2FlagType k)
    (seedGraphs : List (Sym2Graph n)) :
    rawAllAugLabeledFromSeed n k (edgesNat σ) (seedGraphs.map edgesNat)
      = (seedGraphs.flatMap (labeledOfGraph σ)).map rawEnc := by
  rw [rawAllAugLabeledFromSeed, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro G _
  exact rawLabeledOfGraph_eq_map σ G

/-! ### T2a: the raw degree-filtered iso test on encodings equals `isIsoFastDeg_bool` -/

/-- Generic read-off from a `finRange`-map list. -/
theorem getD_finRange_map {k : ℕ} (h : Fin k → ℕ) {a : ℕ} (ha : a < k) :
    ((List.finRange k).map h).getD a 0 = h ⟨a, ha⟩ := by
  have hlen : a < ((List.finRange k).map h).length := by
    rw [List.length_map, List.length_finRange]; exact ha
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some,
    List.getElem_map, List.getElem_finRange]
  exact congrArg h (Fin.ext rfl)

/-- The candidate-edge lists of the two iso tests agree. -/
theorem allEdgePairs_eq {n : ℕ} : allEdgePairs n = (allEdges n).map edgeNatPair := by
  rw [allEdgePairs, allEdges, List.map_flatMap,
    show List.range n = (List.finRange n).map (fun i : Fin n => i.val) from
      (List.map_coe_finRange_eq_range).symm,
    List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  rw [List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro j _
  by_cases h : i.val < j.val
  · rw [Function.comp_apply, if_pos h, if_pos h, Option.map_some, edgeNatPair_mk,
      min_eq_left h.le, max_eq_right h.le]
  · rw [Function.comp_apply, if_neg h, if_neg h, Option.map_none]

/-- Bridge for the `filter` predicate of the two iso tests. -/
theorem all_typecheck_eq {k : ℕ} (p : List ℕ) (h1 h2 : Fin k → ℕ) :
    (List.range k).all (fun t => p.getD (((List.finRange k).map h1).getD t 0) 0
        == ((List.finRange k).map h2).getD t 0)
      = (List.finRange k).all (fun t => p.getD (h1 t) 0 == h2 t) := by
  rw [show List.range k = (List.finRange k).map (fun i : Fin k => i.val) from
      (List.map_coe_finRange_eq_range).symm, List.all_map]
  apply List.all_congr rfl
  intro t
  rw [Function.comp_apply, getD_finRange_map h1 t.isLt, getD_finRange_map h2 t.isLt]

/-- **T2a.**  The raw degree-filtered typed iso check on encodings is exactly the real
`isIsoFastDeg_bool`.  (Purely symbolic — never reduces an `↪g`.) -/
theorem rawIsIsoDeg_rawEnc {k n : ℕ} {σ : Sym2FlagType k} (G1 G2 : Sym2LabeledGraph σ n) :
    rawIsIsoDeg n k (rawEnc G1) (rawEnc G2) = isIsoFastDeg_bool G1 G2 := by
  rw [isIsoFastDeg_bool_eq]
  unfold rawIsIsoDeg
  simp only [rawEnc_fst, rawEnc_snd]
  rw [allEdgePairs_eq]
  congr 1
  congr 1
  funext p
  exact all_typecheck_eq p (fun i => (G1.type_embed i).val) (fun i => (G2.type_embed i).val)

end FlagAlgebras.Compute
