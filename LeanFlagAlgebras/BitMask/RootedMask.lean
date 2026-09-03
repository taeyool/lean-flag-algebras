import LeanFlagAlgebras.BitMask.Density

/-! # Rooted (σ-typed) masks

The σ-typed layer of the bitmask pipeline (Task 5b groundwork): a
σ-typed labeled graph on `m` vertices **with its roots at positions
`0 … k−1`** is still just a mask — the root positions are fixed by
convention, and the root-root bits must match the type graph `σ`
(`RootsMatch`). `labeledGraphOfMask` decodes such a mask to a
`Sym2LabeledGraph σ m` whose type embedding is `Fin.castLE`, and the
transport theorem turns a **root-fixing** injective vertex map with
corresponding bits into the labeled flag equivalence `∼sf` — the exact
shape a rooted canonicalization sweep certifies. Rooted
canonicalization quotients only by the root-fixing permutations
`S_{m−k}`, so one sweep per `(k, m)` serves every type graph `σ`. -/

namespace FlagAlgebras.Compute.BitMask

/-! ## Rooted decoding -/

/-- The root-root bits of `x` (positions `0 … k−1` among `m` vertices)
are exactly the edges of the type graph `σ`. -/
def RootsMatch {k : ℕ} (σ : Sym2FlagType k) (m x : ℕ) : Prop :=
  ∀ i j : Fin k, i < j →
    (x.testBit (pairIdx m i.val j.val) = true ↔ s(i, j) ∈ σ.edges)

instance {k : ℕ} (σ : Sym2FlagType k) (m x : ℕ) :
    Decidable (RootsMatch σ m x) := by
  unfold RootsMatch; infer_instance

/-- Sorted-pair membership in the decoded edges, for root pairs. -/
private lemma rootsMatch_mem {k m : ℕ} {σ : Sym2FlagType k} {x : ℕ}
    (hx : RootsMatch σ m x) (hkm : k ≤ m) {i j : Fin k} (hij : i < j) :
    s(Fin.castLE hkm i, Fin.castLE hkm j) ∈ (graphOfMask₂ m x).edges
      ↔ s(i, j) ∈ σ.edges := by
  rw [← testBit_iff_mem_edges₂ (show Fin.castLE hkm i < Fin.castLE hkm j from hij)]
  exact hx i j hij

/-- Decode a roots-matching mask as a σ-typed labeled graph, with the
roots at the first `k` positions. -/
def labeledGraphOfMask {k : ℕ} (σ : Sym2FlagType k) (m : ℕ) (hkm : k ≤ m)
    (x : ℕ) (hx : RootsMatch σ m x) : Sym2LabeledGraph σ m where
  edges := (graphOfMask₂ m x).edges
  edges_valid := (graphOfMask₂ m x).edges_valid
  type_embed :=
    { toFun := Fin.castLE hkm
      inj' := Fin.castLE_injective hkm
      map_rel_iff' := by
        intro i j
        simp only [Function.Embedding.coeFn_mk]
        rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
        simp only [Finset.mem_coe]
        constructor
        · rintro ⟨hmem, hne⟩
          have hij : i ≠ j := fun h => hne (congrArg _ h)
          refine ⟨?_, hij⟩
          rcases lt_or_gt_of_ne hij with h | h
          · exact (rootsMatch_mem hx hkm h).mp hmem
          · rw [show (s(i, j) : Sym2 (Fin k)) = s(j, i) from Sym2.eq_swap]
            refine (rootsMatch_mem hx hkm h).mp ?_
            rw [show (s(Fin.castLE hkm j, Fin.castLE hkm i) : Sym2 (Fin m))
                = s(Fin.castLE hkm i, Fin.castLE hkm j) from Sym2.eq_swap]
            exact hmem
        · rintro ⟨hmem, hne⟩
          refine ⟨?_, fun h => hne (Fin.castLE_injective hkm h)⟩
          rcases lt_or_gt_of_ne hne with h | h
          · exact (rootsMatch_mem hx hkm h).mpr hmem
          · rw [show (s(Fin.castLE hkm i, Fin.castLE hkm j) : Sym2 (Fin m))
                = s(Fin.castLE hkm j, Fin.castLE hkm i) from Sym2.eq_swap]
            refine (rootsMatch_mem hx hkm h).mpr ?_
            rw [show (s(j, i) : Sym2 (Fin k)) = s(i, j) from Sym2.eq_swap]
            exact hmem }

@[simp]
lemma labeledGraphOfMask_edges {k : ℕ} (σ : Sym2FlagType k) (m : ℕ)
    (hkm : k ≤ m) (x : ℕ) (hx : RootsMatch σ m x) :
    (labeledGraphOfMask σ m hkm x hx).edges = (graphOfMask₂ m x).edges := rfl

/-! ## Root-fixing transport

The rooted analogue of `graphOfMask₂_eqv_of_bits`: an injective vertex
map that (i) fixes the roots pointwise and (ii) matches the bits decodes
to a **labeled** flag equivalence. The edge-transport core is re-proved
locally (`Mask2` is not touched — a change there would force the
canonicalization sweeps to re-verify). -/

/-- Edge transport along a bit-correspondence (local copy of the core of
`graphOfMask₂_eqv_of_bits`). -/
private lemma edge_iff_of_bits {n : ℕ} {f : Fin n → Fin n}
    (hf : Function.Injective f) {x y : ℕ}
    (hbits : ∀ a b : Fin n, a < b →
      x.testBit (pairIdx n a.val b.val)
        = y.testBit (pairIdx n (sort2 (f a) (f b)).1.val
            (sort2 (f a) (f b)).2.val))
    (a b : Fin n) (hab : a < b) :
    s(a, b) ∈ (graphOfMask₂ n x).edges
      ↔ s(f a, f b) ∈ (graphOfMask₂ n y).edges := by
  have hfab : f a ≠ f b := fun h => hab.ne (hf h)
  have hcd := sort2_lt hfab
  rw [← testBit_iff_mem_edges₂ hab, hbits a b hab,
    show (s(f a, f b) : Sym2 (Fin n))
        = s((sort2 (f a) (f b)).1, (sort2 (f a) (f b)).2) from
      (sort2_sym2 _ _).symm,
    ← testBit_iff_mem_edges₂ hcd]

/-- Adjacency in the decoded labeled flag is edge membership of the
decoded mask. -/
lemma labeledGraphOfMask_adj_iff {k m : ℕ} {σ : Sym2FlagType k}
    (hkm : k ≤ m) (x : ℕ) (hx : RootsMatch σ m x) (u v : Fin m) :
    (labeledGraphOfMask σ m hkm x hx).toLabeledGraph.graph.Adj u v
      ↔ s(u, v) ∈ (graphOfMask₂ m x).edges := by
  show (SimpleGraph.fromEdgeSet _).Adj u v ↔ _
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun huv => ?_⟩
    subst huv
    exact (graphOfMask₂ m x).edges_valid _ h (Sym2.mk_isDiag_iff.mpr rfl)

/-- **Rooted transport.** A root-fixing injective map with matching bits
gives the labeled flag equivalence of the decoded flags. Decidable for
literal data — the shape a rooted sweep's leaves certify. -/
theorem labeledGraphOfMask_eqv_of_bits {k m : ℕ} {σ : Sym2FlagType k}
    (hkm : k ≤ m) {f : Fin m → Fin m} (hf : Function.Injective f)
    (hfix : ∀ i : Fin k, f (Fin.castLE hkm i) = Fin.castLE hkm i)
    {x y : ℕ} (hx : RootsMatch σ m x) (hy : RootsMatch σ m y)
    (hbits : ∀ a b : Fin m, a < b →
      x.testBit (pairIdx m a.val b.val)
        = y.testBit (pairIdx m (sort2 (f a) (f b)).1.val
            (sort2 (f a) (f b)).2.val)) :
    labeledGraphOfMask σ m hkm x hx ∼sf labeledGraphOfMask σ m hkm y hy := by
  have hbij : Function.Bijective f := ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨{ graph_iso := ⟨Equiv.ofBijective f hbij, ?_⟩,
            type_preserve := ?_ }⟩
  · intro a b
    show (labeledGraphOfMask σ m hkm y hy).toLabeledGraph.graph.Adj (f a) (f b)
      ↔ (labeledGraphOfMask σ m hkm x hx).toLabeledGraph.graph.Adj a b
    rw [labeledGraphOfMask_adj_iff, labeledGraphOfMask_adj_iff]
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact (edge_iff_of_bits hf hbits a b hab).symm
    · constructor
      · intro hmem
        exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
          ((graphOfMask₂ m y).edges_valid _ hmem)
      · intro hmem
        exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
          ((graphOfMask₂ m x).edges_valid _ hmem)
    · rw [show (s(f a, f b) : Sym2 (Fin m)) = s(f b, f a) from Sym2.eq_swap,
        show (s(a, b) : Sym2 (Fin m)) = s(b, a) from Sym2.eq_swap]
      exact (edge_iff_of_bits hf hbits b a hba).symm
  · funext t
    show Equiv.ofBijective f hbij (Fin.castLE hkm t) = Fin.castLE hkm t
    exact hfix t

/-! ## Rooted extraction

A σ-typed placement is a vertex set `V` containing all roots. Its
labeling puts the roots first (in `type_embed` order) and the remaining
vertices in ascending order; extraction reads the host mask along that
labeling. As with the unrooted `vtxList`, the non-root enumeration is a
`filter` of `finRange` (kernel-reducible), and the root test is a plain
decidable `∃` over `Fin k` (`type_verts` itself is built through set
machinery the kernel cannot reduce). -/

/-- Rooted vertex list of `V`: the roots (in `type_embed` order), then
the non-root members of `V` ascending. -/
def rootedVtxList {k N : ℕ} {σ : Sym2FlagType k} (G : Sym2LabeledGraph σ N)
    (V : Finset (Fin N)) : List ℕ :=
  ((List.finRange k).map fun t => (G.type_embed t).val)
    ++ (((List.finRange N).filter fun v =>
          decide (v ∈ V) && !decide (∃ t, G.type_embed t = v)).map Fin.val)

/-- Extract the rooted induced-subgraph mask of `V` (pattern size `m`)
from the host mask `h`. Unlike the unrooted `extractMask`, the rooted
vertex list is not ascending (roots come first), so each pair is sorted
by `min`/`max` before ranking. -/
def rootedExtractMask {k N : ℕ} {σ : Sym2FlagType k} (m : ℕ)
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N)) (h : ℕ) : ℕ :=
  (finPairs m).foldl (fun acc p =>
    let u := (rootedVtxList G V).getD p.1.val 0
    let v := (rootedVtxList G V).getD p.2.val 0
    if h.testBit (pairIdx N (min u v) (max u v))
    then acc ||| (1 <<< pairIdx m p.1.val p.2.val)
    else acc) 0

/-- Bit description of the rooted extraction (same argument as
`extractMask_testBit`, over the rooted vertex list). -/
lemma rootedExtractMask_testBit {k N m : ℕ} {σ : Sym2FlagType k}
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N)) (h : ℕ)
    {a b : Fin m} (hab : a < b) :
    (rootedExtractMask m G V h).testBit (pairIdx m a.val b.val)
      = h.testBit (pairIdx N
          (min ((rootedVtxList G V).getD a.val 0)
            ((rootedVtxList G V).getD b.val 0))
          (max ((rootedVtxList G V).getD a.val 0)
            ((rootedVtxList G V).getD b.val 0))) := by
  unfold rootedExtractMask
  rw [testBit_foldl_or, Nat.zero_testBit, Bool.false_or]
  cases hbit : h.testBit (pairIdx N
      (min ((rootedVtxList G V).getD a.val 0)
        ((rootedVtxList G V).getD b.val 0))
      (max ((rootedVtxList G V).getD a.val 0)
        ((rootedVtxList G V).getD b.val 0))) with
  | true =>
    refine List.any_eq_true.mpr ⟨(a, b), mem_finPairs.mpr hab, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hbit, decide_eq_true rfl⟩
  | false =>
    refine List.any_eq_false.mpr ?_
    rintro ⟨x, y⟩ hxy
    rw [Bool.and_eq_true, not_and]
    intro hguard hrank
    have heq : ((x, y) : Fin m × Fin m) = (a, b) :=
      hinjm (x, y) hxy (a, b) (mem_finPairs.mpr hab)
        (of_decide_eq_true hrank)
    rw [heq] at hguard
    rw [of_decide_eq_true hguard] at hbit
    cases hbit

/-- The rooted extraction stays below `2 ^ k`, given the rank bound. -/
lemma rootedExtractMask_lt {k N m c : ℕ} {σ : Sym2FlagType k}
    (hboundm : ∀ p ∈ finPairs m, pairIdx m p.1.val p.2.val < c)
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N)) (h : ℕ) :
    rootedExtractMask m G V h < 2 ^ c :=
  foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos c) hboundm

/-! ### Positions of the rooted vertex list -/

/-- Root positions read the type embedding. -/
lemma rootedVtxList_getD_root {k N : ℕ} {σ : Sym2FlagType k}
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N)) (i : Fin k) :
    (rootedVtxList G V).getD i.val 0 = (G.type_embed i).val := by
  unfold rootedVtxList
  have hlen : i.val < ((List.finRange k).map
      fun t => (G.type_embed t).val).length := by
    rw [List.length_map, List.length_finRange]
    exact i.isLt
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getElem_append_left hlen]
  simp [List.getElem_map, List.getElem_finRange]

/-- The non-root tail of the rooted vertex list is the sorted
enumeration of `V \ type_verts`. -/
lemma rootedVtxList_tail_eq {k N : ℕ} {σ : Sym2FlagType k}
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N)) :
    ((List.finRange N).filter fun v =>
        decide (v ∈ V) && !decide (∃ t, G.type_embed t = v))
      = (V \ G.type_verts).sort (· ≤ ·) := by
  haveI : Std.Antisymm (fun (a b : Fin N) => a ≤ b) := ⟨fun _ _ => le_antisymm⟩
  refine List.Perm.eq_of_pairwise' (r := fun (a b : Fin N) => a ≤ b) ?_ ?_ ?_
  · refine List.Pairwise.sublist List.filter_sublist ?_
    exact ((List.sortedLT_finRange N).pairwise).imp le_of_lt
  · exact (V \ G.type_verts).pairwise_sort (· ≤ ·)
  · refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
    · exact (List.nodup_finRange N).filter _
    · exact (V \ G.type_verts).sort_nodup (· ≤ ·)
    · intro v
      rw [List.mem_filter, Finset.mem_sort, Finset.mem_sdiff]
      simp only [List.mem_finRange, true_and, Bool.and_eq_true,
        decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      rw [Sym2LabeledGraph.type_verts_eq_image]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]

/-- Non-root positions read the order embedding of `V \ type_verts`. -/
lemma rootedVtxList_getD_nonroot {k N m : ℕ} {σ : Sym2FlagType k}
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N))
    (hcard : (V \ G.type_verts).card = m - k) {i : Fin m}
    (hik : k ≤ i.val) :
    (rootedVtxList G V).getD i.val 0
      = (((V \ G.type_verts).orderEmbOfFin hcard)
          ⟨i.val - k, by omega⟩).val := by
  unfold rootedVtxList
  have hlen1 : ((List.finRange k).map
      fun t => (G.type_embed t).val).length = k := by
    rw [List.length_map, List.length_finRange]
  have hlen2 : (((List.finRange N).filter fun v =>
      decide (v ∈ V) && !decide (∃ t, G.type_embed t = v)).map
        Fin.val).length = m - k := by
    rw [List.length_map, rootedVtxList_tail_eq, Finset.length_sort, hcard]
  have hi : i.val < (((List.finRange k).map fun t => (G.type_embed t).val)
      ++ (((List.finRange N).filter fun v =>
          decide (v ∈ V) && !decide (∃ t, G.type_embed t = v)).map
            Fin.val)).length := by
    rw [List.length_append, hlen1, hlen2]
    omega
  rw [List.getD_eq_getElem _ _ hi,
    List.getElem_append_right (by rw [hlen1]; omega)]
  simp only [hlen1, List.getElem_map, rootedVtxList_tail_eq,
    Finset.orderEmbOfFin_apply]
  rfl

/-! ### Extractions are always decodable -/

/-- The underlying unlabeled graph of a σ-typed graph. -/
def underlyingGraph {k N : ℕ} {σ : Sym2FlagType k}
    (G : Sym2LabeledGraph σ N) : Sym2Graph N := ⟨G.edges, G.edges_valid⟩

/-- Host edge membership at two root images is exactly a type-graph
edge (the defining property of the type embedding). -/
private lemma mem_edges_type_embed {k N : ℕ} {σ : Sym2FlagType k}
    (G : Sym2LabeledGraph σ N) {i j : Fin k} (hij : i ≠ j) :
    s(G.type_embed i, G.type_embed j) ∈ G.edges ↔ s(i, j) ∈ σ.edges := by
  have hne : G.type_embed i ≠ G.type_embed j :=
    fun h => hij (G.type_embed.injective h)
  have hrel := G.type_embed.map_rel_iff (a := i) (b := j)
  rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj] at hrel
  simp only [Finset.mem_coe] at hrel
  constructor
  · intro hm
    exact (hrel.mp ⟨hm, hne⟩).1
  · intro hm
    exact (hrel.mpr ⟨hm, hij⟩).1

/-- **Extractions match the type graph on the root bits** — every
placement's extraction decodes as a σ-typed flag. -/
theorem rootedExtractMask_rootsMatch {k N m : ℕ} {σ : Sym2FlagType k}
    (hkm : k ≤ m)
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (G : Sym2LabeledGraph σ N) (V : Finset (Fin N)) :
    RootsMatch σ m
      (rootedExtractMask m G V (maskOfGraph₂ (underlyingGraph G))) := by
  intro i j hij
  have hab : Fin.castLE hkm i < Fin.castLE hkm j := hij
  rw [show pairIdx m i.val j.val
      = pairIdx m (Fin.castLE hkm i).val (Fin.castLE hkm j).val from rfl,
    rootedExtractMask_testBit hinjm G V _ hab]
  simp only [Fin.val_castLE]
  rw [rootedVtxList_getD_root, rootedVtxList_getD_root]
  have hne : G.type_embed i ≠ G.type_embed j :=
    fun h => hij.ne (G.type_embed.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [show min (G.type_embed i).val (G.type_embed j).val
        = (G.type_embed i).val from min_eq_left (le_of_lt h),
      show max (G.type_embed i).val (G.type_embed j).val
        = (G.type_embed j).val from max_eq_right (le_of_lt h),
      testBit_iff_mem_edges₂ h,
      graphOfMask₂_maskOfGraph₂ hinjN (underlyingGraph G)]
    exact mem_edges_type_embed G hij.ne
  · rw [show min (G.type_embed i).val (G.type_embed j).val
        = (G.type_embed j).val from min_eq_right (le_of_lt h),
      show max (G.type_embed i).val (G.type_embed j).val
        = (G.type_embed i).val from max_eq_left (le_of_lt h),
      testBit_iff_mem_edges₂ h,
      graphOfMask₂_maskOfGraph₂ hinjN (underlyingGraph G),
      show (s(G.type_embed j, G.type_embed i) : Sym2 (Fin N))
        = s(G.type_embed i, G.type_embed j) from Sym2.eq_swap]
    exact mem_edges_type_embed G hij.ne

end FlagAlgebras.Compute.BitMask
