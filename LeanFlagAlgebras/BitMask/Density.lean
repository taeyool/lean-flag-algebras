import LeanFlagAlgebras.BitMask.MaskBridge

/-! # Bit-level flag densities (empty-typed, single pattern)

The numerator of the empty-typed flag density
`sym2InducedSubgraphListCount (sym2GraphToList F) G` counts vertex
subsets of `G` whose induced subgraph is isomorphic to `F`. This module
computes that count at the mask level — per subset, the induced
subgraph is *extracted* from the host mask by bit tests along the
sorted vertex enumeration, and membership in the isomorphism class of
`F` is decided by comparing canonical representatives from the sweeps —
so density value lemmas become kernel computations (`decide +kernel`),
with no `native_decide`.

Kernel-engineering notes (they shaped every definition here):
* the vertex enumeration is a `filter` of the already-ascending
  `List.finRange` — `Finset.sort` (merge sort) is well-founded
  recursion, which the kernel cannot reduce;
* the subset enumeration stays at `Finset (Finset (Fin N))` — at
  `N ≤ 7` the powerset has at most 128 elements, so no packed subset
  tables are needed;
* the accept test stays at the mask level (`canonImage` of the
  extracted mask) — decoding to `Finset`-backed graphs inside the count
  would cost seconds per subset in the kernel. -/

namespace FlagAlgebras.Compute.BitMask

/-! ## The extraction machinery -/

/-- The ascending vertex list of a finset, as naturals
(kernel-reducible). -/
def vtxList {N : ℕ} (V : Finset (Fin N)) : List ℕ :=
  ((List.finRange N).filter (fun v => decide (v ∈ V))).map Fin.val

/-- Extract the induced-subgraph mask of `V` (pattern size `m`) from the
host mask `h`: sub-pair `(i, j)` is an edge iff the corresponding pair
of the `i`-th and `j`-th smallest vertices of `V` is set in `h`. -/
def extractMask {N : ℕ} (m : ℕ) (V : Finset (Fin N)) (h : ℕ) : ℕ :=
  (finPairs m).foldl (fun acc p =>
    if h.testBit
        (pairIdx N ((vtxList V).getD p.1.val 0) ((vtxList V).getD p.2.val 0))
    then acc ||| (1 <<< pairIdx m p.1.val p.2.val)
    else acc) 0

/-- Bit-level placement count: the `m`-subsets of the `N` host vertices
whose extracted mask passes `acc`. -/
def maskCount (N m : ℕ) (acc : ℕ → Bool) (h : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin N))).filter
    (fun V => (decide (V.card = m) && acc (extractMask m V h)) = true)).card

/-! ## The vertex list is the sorted enumeration -/

/-- `vtxList` is the (value-mapped) `Finset.sort` — the definition
avoids `sort` only because merge sort does not reduce in the kernel. -/
lemma vtxList_eq_sort_map {N : ℕ} (V : Finset (Fin N)) :
    vtxList V = (V.sort (· ≤ ·)).map Fin.val := by
  unfold vtxList
  congr 1
  haveI : Std.Antisymm (fun (a b : Fin N) => a ≤ b) := ⟨fun _ _ => le_antisymm⟩
  refine List.Perm.eq_of_pairwise' (r := fun (a b : Fin N) => a ≤ b) ?_ ?_ ?_
  · refine List.Pairwise.sublist List.filter_sublist ?_
    exact ((List.sortedLT_finRange N).pairwise).imp le_of_lt
  · exact V.pairwise_sort (· ≤ ·)
  · refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
    · exact (List.nodup_finRange N).filter _
    · exact V.sort_nodup (· ≤ ·)
    · intro v
      simp [List.mem_filter, List.mem_finRange, Finset.mem_sort]

/-- Positions of `vtxList` are the order embedding of the subset. -/
lemma vtxList_getD_eq {N m : ℕ} (V : Finset (Fin N)) (hV : V.card = m)
    (i : Fin m) :
    (vtxList V).getD i.val 0 = (V.orderEmbOfFin hV i).val := by
  have hlen : (vtxList V).length = m := by
    rw [vtxList_eq_sort_map, List.length_map, Finset.length_sort, hV]
  have hi : i.val < (vtxList V).length := by rw [hlen]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  rw [Finset.orderEmbOfFin_apply]
  simp only [vtxList_eq_sort_map, List.getElem_map]
  rfl

/-! ## Bits of the extracted mask -/

/-- Bit description of `extractMask`: the sorted sub-pair `(a, b)` bit
reads the host bit of the corresponding vertex pair. Needs rank
injectivity at the pattern size (kernel-checked per size). -/
lemma extractMask_testBit {N m : ℕ}
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (V : Finset (Fin N)) (h : ℕ) {a b : Fin m} (hab : a < b) :
    (extractMask m V h).testBit (pairIdx m a.val b.val)
      = h.testBit
          (pairIdx N ((vtxList V).getD a.val 0) ((vtxList V).getD b.val 0)) := by
  unfold extractMask
  rw [testBit_foldl_or]
  rw [Nat.zero_testBit, Bool.false_or]
  cases hbit : h.testBit
      (pairIdx N ((vtxList V).getD a.val 0) ((vtxList V).getD b.val 0)) with
  | true =>
    refine List.any_eq_true.mpr ⟨(a, b), mem_finPairs.mpr hab, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hbit, decide_eq_true rfl⟩
  | false =>
    refine List.any_eq_false.mpr ?_
    rintro ⟨x, y⟩ hxy
    rw [Bool.and_eq_true, not_and]
    intro hguard hrank
    have hrank' := of_decide_eq_true hrank
    have heq : ((x, y) : Fin m × Fin m) = (a, b) :=
      hinjm (x, y) hxy (a, b) (mem_finPairs.mpr hab) hrank'
    rw [heq] at hguard
    rw [of_decide_eq_true hguard] at hbit
    cases hbit

/-- The extracted mask stays below `2 ^ k`, given the rank bound at the
pattern size. -/
lemma extractMask_lt {N m k : ℕ}
    (hboundm : ∀ p ∈ finPairs m, pairIdx m p.1.val p.2.val < k)
    (V : Finset (Fin N)) (h : ℕ) : extractMask m V h < 2 ^ k :=
  foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos k) hboundm

/-! ## The extracted mask decodes to the induced subgraph -/

/-- Flag isomorphism of empty-typed labeled graphs from a plain graph
isomorphism (the type-embedding condition is vacuous). -/
def emptyIso_of_graphIso {V W : Type} {G₁ : LabeledGraph ∅ₜ V}
    {G₂ : LabeledGraph ∅ₜ W} (e : G₁.graph ≃g G₂.graph) : G₁ ≃f G₂ where
  graph_iso := e
  type_preserve := by ext z; exact Fin.elim0 z

/-- Sorted-pair membership: the edge of two increasing pattern vertices
is in the decoding of the extract iff the corresponding host pair is an
edge of `G`. -/
lemma extract_mem_iff {N m : ℕ} {G : Sym2Graph N}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (V : Finset (Fin N)) (hV : V.card = m) {a b : Fin m} (hab : a < b) :
    s(a, b) ∈ (graphOfMask₂ m (extractMask m V (maskOfGraph₂ G))).edges
      ↔ s(V.orderEmbOfFin hV a, V.orderEmbOfFin hV b) ∈ G.edges := by
  rw [← testBit_iff_mem_edges₂ hab,
    extractMask_testBit hinjm V (maskOfGraph₂ G) hab,
    vtxList_getD_eq V hV a, vtxList_getD_eq V hV b,
    testBit_iff_mem_edges₂ ((V.orderEmbOfFin hV).strictMono hab),
    graphOfMask₂_maskOfGraph₂ hinjN G]

/-- The decoding of the extracted mask is flag-isomorphic to the induced
subgraph on `V` — extraction is exactly "restrict to `V` and relabel
along the sorted enumeration". -/
theorem nonempty_extractIso {N m : ℕ} {G : Sym2Graph N}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (V : Finset (Fin N)) (hV : V.card = m) :
    Nonempty
      ((graphOfMask₂ m (extractMask m V (maskOfGraph₂ G))).toLabeledGraph
        ≃f (⟨V⟩ : Sym2InducedSubgraph G).toLabeledSubgraph.coe) := by
  refine ⟨emptyIso_of_graphIso ⟨(V.orderIsoOfFin hV).toEquiv, ?_⟩⟩
  intro a b
  rw [← Sym2InducedSubgraph.coe_adj_iff_mem, Sym2Graph.toLabeledGraph_adj_iff]
  show s(((V.orderIsoOfFin hV) a : Fin N), ((V.orderIsoOfFin hV) b : Fin N))
      ∈ G.edges ↔ _
  rw [Finset.coe_orderIsoOfFin_apply, Finset.coe_orderIsoOfFin_apply]
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (extract_mem_iff hinjN hinjm V hV hab).symm
  · constructor
    · intro hmem
      exact absurd (Sym2.mk_isDiag_iff.mpr rfl) (G.edges_valid _ hmem)
    · intro hmem
      exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
        ((graphOfMask₂ m _).edges_valid _ hmem)
  · rw [show (s(a, b) : Sym2 (Fin m)) = s(b, a) from Sym2.eq_swap,
      show (s((V.orderEmbOfFin hV) a, (V.orderEmbOfFin hV) b) : Sym2 (Fin N))
          = s((V.orderEmbOfFin hV) b, (V.orderEmbOfFin hV) a) from
        Sym2.eq_swap]
    exact (extract_mem_iff hinjN hinjm V hV hba).symm

/-! ## Encoding is a two-sided inverse (below the rank bound) -/

/-- Numbers below a power of two agree when their low bits do. -/
lemma eq_of_lt_two_pow {k x y : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ i < k, x.testBit i = y.testBit i) : x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · exact h i hi
  · have hpow : (2 : ℕ) ^ k ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hpow)]

/-- Re-encoding a decoded mask recovers it, below the rank bound. The
cover hypothesis (every bit position below `k` is a pair rank) is
kernel-checkable per vertex count. -/
lemma maskOfGraph₂_graphOfMask₂ {n k : ℕ}
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (hbound : ∀ p ∈ finPairs n, pairIdx n p.1.val p.2.val < k)
    (hcover : ∀ i < k, ∃ p ∈ finPairs n, pairIdx n p.1.val p.2.val = i)
    {x : ℕ} (hx : x < 2 ^ k) :
    maskOfGraph₂ (graphOfMask₂ n x) = x := by
  refine eq_of_lt_two_pow
    (foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos k) hbound) hx
    fun i hi => ?_
  obtain ⟨⟨a, b⟩, hp, hrank⟩ := hcover i hi
  have hab := mem_finPairs.mp hp
  rw [← hrank, Bool.eq_iff_iff, testBit_iff_mem_edges₂ hab,
    graphOfMask₂_maskOfGraph₂ hinj (graphOfMask₂ n x),
    ← testBit_iff_mem_edges₂ hab]

/-! ## Class membership via canonical forms

With a complete representative list whose entries are pairwise
non-equivalent (kernel-checkable per vertex count), the
canonicalization map decides equivalence exactly. -/

/-- Distinct representatives make `canonOf` a complete invariant. -/
theorem eqv_iff_canonOf_eq {n : ℕ} {reps : List ℕ}
    {canonOf : Sym2Graph n → ℕ}
    (hspec : ∀ G : Sym2Graph n,
      canonOf G ∈ reps ∧ G ∼sf graphOfMask₂ n (canonOf G))
    (hdist : ∀ p ∈ reps, ∀ q ∈ reps,
      graphOfMask₂ n p ∼sf graphOfMask₂ n q → p = q)
    (G₁ G₂ : Sym2Graph n) : G₁ ∼sf G₂ ↔ canonOf G₁ = canonOf G₂ := by
  constructor
  · intro h
    refine hdist _ (hspec G₁).1 _ (hspec G₂).1 ?_
    exact ((Sym2GraphEqv.symm (hspec G₁).2).trans h).trans (hspec G₂).2
  · intro h
    refine ((hspec G₁).2.trans ?_).trans (Sym2GraphEqv.symm (hspec G₂).2)
    rw [h]
    exact Sym2GraphEqv.refl _

/-- **Placement criterion, mask form.** A vertex subset carries an
induced copy of `F` iff its extracted mask decodes into the class of
`F`. -/
theorem coe_iso_iff_extract_eqv {N m : ℕ} {G : Sym2Graph N}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2Graph m) (V : Finset (Fin N)) (hV : V.card = m) :
    Nonempty ((⟨V⟩ : Sym2InducedSubgraph G).toLabeledSubgraph.coe
        ≃f F.toLabeledGraph)
      ↔ graphOfMask₂ m (extractMask m V (maskOfGraph₂ G)) ∼sf F := by
  obtain ⟨e₀⟩ := nonempty_extractIso (G := G) hinjN hinjm V hV
  constructor
  · rintro ⟨e⟩
    exact ⟨emptyIso_of_graphIso (e₀.graph_iso.trans e.graph_iso)⟩
  · rintro ⟨d⟩
    exact ⟨emptyIso_of_graphIso (e₀.graph_iso.symm.trans d.graph_iso)⟩

/-! ## The count bridge -/

/-- **The density numerator, bit-level.** The placement count of a
single pattern `F` in `G` equals the mask count, for any accept test
that decides membership in the class of `F` on masks below the rank
bound. All hypotheses are kernel-checkable per vertex count. -/
theorem listCount_eq_maskCount {N m k : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs m, pairIdx m p.1.val p.2.val < k)
    (F : Sym2Graph m) (G : Sym2Graph N) {acc : ℕ → Bool}
    (hacc : ∀ x, x < 2 ^ k → (acc x = true ↔ graphOfMask₂ m x ∼sf F)) :
    sym2InducedSubgraphListCount (sym2GraphToList F) G
      = maskCount N m acc (maskOfGraph₂ G) := by
  have hmem : ∀ Gl : Sym2InducedSubgraphList 1 G,
      predIsoSym2Hl (sym2GraphToList F) Gl ↔
        ((Gl 0).verts.card = m
          ∧ acc (extractMask m (Gl 0).verts (maskOfGraph₂ G)) = true) := by
    intro Gl
    constructor
    · rintro ⟨hiso, -⟩
      obtain ⟨e⟩ := hiso 0
      have hV : (Gl 0).verts.card = m :=
        Finset.card_eq_of_equiv_fin e.graph_iso.toEquiv
      refine ⟨hV, ?_⟩
      refine (hacc _ (extractMask_lt hboundm _ _)).mpr ?_
      exact (coe_iso_iff_extract_eqv hinjN hinjm F (Gl 0).verts hV).mp ⟨e⟩
    · rintro ⟨hV, hacc'⟩
      refine ⟨?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
      intro i
      have hi0 : i = 0 := Subsingleton.elim i 0
      subst hi0
      exact (coe_iso_iff_extract_eqv hinjN hinjm F (Gl 0).verts hV).mpr
        ((hacc _ (extractMask_lt hboundm _ _)).mp hacc')
  unfold sym2InducedSubgraphListCount maskCount
  refine Finset.card_bij (fun Gl _ => (Gl 0).verts) ?_ ?_ ?_
  · intro Gl hGl
    simp only [finsetOfSym2InducedSubgraphListIsoHl, Finset.mem_filter,
      Finset.mem_univ, true_and] at hGl
    obtain ⟨hV, ha⟩ := (hmem Gl).mp hGl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hV, ha⟩
  · intro Gl₁ h₁ Gl₂ h₂ hEq
    have hEq' : (Gl₁ 0).verts = (Gl₂ 0).verts := hEq
    funext i
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    rcases hg₁ : Gl₁ 0 with ⟨v₁⟩
    rcases hg₂ : Gl₂ 0 with ⟨v₂⟩
    rw [hg₁, hg₂] at hEq'
    exact congrArg Sym2InducedSubgraph.mk hEq'
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
    rw [Bool.and_eq_true] at hV
    refine ⟨fun _ => ⟨V⟩, ?_, rfl⟩
    simp only [finsetOfSym2InducedSubgraphListIsoHl, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (hmem _).mpr ⟨of_decide_eq_true hV.1, hV.2⟩

/-- **The density, bit-level.** -/
theorem sym2EmptyTypeFlagDensity₁_eq_maskCount {N m k : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs m, pairIdx m p.1.val p.2.val < k)
    (F : Sym2Graph m) (G : Sym2Graph N) {acc : ℕ → Bool}
    (hacc : ∀ x, x < 2 ^ k → (acc x = true ↔ graphOfMask₂ m x ∼sf F)) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N m acc (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => m) N := by
  show sym2InducedSubgraphListDensity (sym2GraphToList F) G = _
  rw [sym2InducedSubgraphListDensity,
    listCount_eq_maskCount hinjN hinjm hboundm F G hacc]

/-! ## Canonical-form accepts, packaged

Generic in the per-size canon apparatus, so each vertex count
instantiates with one distinctness check and one cover lemma. -/

/-- Reflection of the Bool-level pairwise-distinctness check. -/
theorem distinct_of_bool {n : ℕ} {reps : List ℕ}
    (h : (reps.all fun p => reps.all fun q =>
      p == q || !isEmptyIsoFast_bool (graphOfMask₂ n p) (graphOfMask₂ n q))
        = true) :
    ∀ p ∈ reps, ∀ q ∈ reps,
      graphOfMask₂ n p ∼sf graphOfMask₂ n q → p = q := by
  intro p hp q hq hpq
  have hb := List.all_eq_true.mp (List.all_eq_true.mp h p hp) q hq
  rcases Bool.or_eq_true_iff.mp hb with h' | h'
  · exact beq_iff_eq.mp h'
  · rw [Bool.not_eq_true'] at h'
    exact absurd hpq (isEmptyIsoFast_bool_false_correct h')

/-- Reflection of the degree-key-bucketed distinctness check: pairs are
first separated by the cheap `degKey` invariant, and the permutation
search runs only on key collisions — without this, the exhaustive
searches on non-equivalent same-size pairs dominate at `n ≥ 6`. -/
theorem distinct_of_bool_deg {n : ℕ} {reps : List ℕ}
    (h : (reps.all fun p => reps.all fun q =>
      p == q
        || decide (degKey (graphOfMask₂ n p) ≠ degKey (graphOfMask₂ n q))
        || !isEmptyIsoFast_bool (graphOfMask₂ n p) (graphOfMask₂ n q))
        = true) :
    ∀ p ∈ reps, ∀ q ∈ reps,
      graphOfMask₂ n p ∼sf graphOfMask₂ n q → p = q := by
  intro p hp q hq hpq
  have hb := List.all_eq_true.mp (List.all_eq_true.mp h p hp) q hq
  rcases Bool.or_eq_true_iff.mp hb with h' | h'
  · rcases Bool.or_eq_true_iff.mp h' with h'' | h''
    · exact beq_iff_eq.mp h''
    · exact absurd (degKey_iso_invariant hpq) (of_decide_eq_true h'')
  · rw [Bool.not_eq_true'] at h'
    exact absurd hpq (isEmptyIsoFast_bool_false_correct h')

/-- The canonical-form accept decides membership in the class of `F` on
masks below the rank bound. -/
theorem acc_canon_spec {n k : ℕ} {reps : List ℕ} {canonImage : ℕ → ℕ}
    (canonOf : Sym2Graph n → ℕ)
    (hci : ∀ G : Sym2Graph n, canonOf G = canonImage (maskOfGraph₂ G))
    (hspec : ∀ G : Sym2Graph n,
      canonOf G ∈ reps ∧ G ∼sf graphOfMask₂ n (canonOf G))
    (hdist : ∀ p ∈ reps, ∀ q ∈ reps,
      graphOfMask₂ n p ∼sf graphOfMask₂ n q → p = q)
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (hbound : ∀ p ∈ finPairs n, pairIdx n p.1.val p.2.val < k)
    (hcover : ∀ i < k, ∃ p ∈ finPairs n, pairIdx n p.1.val p.2.val = i)
    (F : Sym2Graph n) :
    ∀ x, x < 2 ^ k →
      ((canonImage x == canonOf F) = true ↔ graphOfMask₂ n x ∼sf F) := by
  intro x hx
  rw [beq_iff_eq]
  have hround : maskOfGraph₂ (graphOfMask₂ n x) = x :=
    maskOfGraph₂_graphOfMask₂ hinj hbound hcover hx
  have hco : canonOf (graphOfMask₂ n x) = canonImage x := by
    rw [hci, hround]
  rw [← hco]
  exact (eqv_iff_canonOf_eq hspec hdist _ F).symm

/-- **Kernel-computable density**, packaged over the canon apparatus of
the pattern size. -/
theorem density₁_eq_maskCount_canon {N n k : ℕ} {reps : List ℕ}
    {canonImage : ℕ → ℕ} (canonOf : Sym2Graph n → ℕ)
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hci : ∀ G : Sym2Graph n, canonOf G = canonImage (maskOfGraph₂ G))
    (hspec : ∀ G : Sym2Graph n,
      canonOf G ∈ reps ∧ G ∼sf graphOfMask₂ n (canonOf G))
    (hdist : ∀ p ∈ reps, ∀ q ∈ reps,
      graphOfMask₂ n p ∼sf graphOfMask₂ n q → p = q)
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (hbound : ∀ p ∈ finPairs n, pairIdx n p.1.val p.2.val < k)
    (hcover : ∀ i < k, ∃ p ∈ finPairs n, pairIdx n p.1.val p.2.val = i)
    (F : Sym2Graph n) (G : Sym2Graph N) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N n (fun x => canonImage x == canonOf F)
            (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => n) N :=
  sym2EmptyTypeFlagDensity₁_eq_maskCount hinjN hinj hbound F G
    (acc_canon_spec canonOf hci hspec hdist hinj hbound hcover F)

/-! ## Five-vertex pattern instance -/

namespace Canon5

set_option maxRecDepth 8192 in
/-- Every bit position below 10 is a five-vertex pair rank. -/
lemma finPairs5_rank_cover : ∀ i < 10, ∃ p ∈ finPairs 5,
    pairIdx 5 p.1.val p.2.val = i := by decide

set_option maxRecDepth 65536 in
/-- The 34 representatives are pairwise non-equivalent
(kernel-checked). -/
lemma reps5_distinct_bool : (reps5.all fun p => reps5.all fun q =>
    p == q || !isEmptyIsoFast_bool (graphOfMask₂ 5 p) (graphOfMask₂ 5 q))
      = true := by
  decide +kernel

/-- The 34 representatives are pairwise non-equivalent. -/
lemma reps5_distinct : ∀ p ∈ reps5, ∀ q ∈ reps5,
    graphOfMask₂ 5 p ∼sf graphOfMask₂ 5 q → p = q :=
  distinct_of_bool reps5_distinct_bool

/-- **Kernel-computable density of any 5-vertex pattern** in any host
whose pair ranks are injective (kernel-checked per host size). -/
theorem density₁_eq_maskCount5 {N : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2Graph 5) (G : Sym2Graph N) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N 5 (fun x => canonImage x == canonOf F)
            (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => 5) N :=
  density₁_eq_maskCount_canon canonOf hinjN (fun _ => rfl) canonOf_spec
    reps5_distinct finPairs5_rank_inj finPairs5_rank_lt
    finPairs5_rank_cover F G

end Canon5

end FlagAlgebras.Compute.BitMask
