import LeanFlagAlgebras.BitMask.RootedDensity
import LeanFlagAlgebras.BitMask.RootedCanon

/-! # The σ-typed count bridge (single pattern)

Bridges the σ-typed placement count
`sym2InducedLabeledSubgraphListCount` (for one pattern) to a bit-level
count over the root-containing vertex subsets, with the accept test on
the rooted extraction — the labeled analogue of `Density.lean`'s
`listCount_eq_maskCount`. The accept correctness comes from the rooted
canonicalization sweeps plus representative distinctness. -/

namespace FlagAlgebras.Compute.BitMask

variable {k N m : ℕ} {σ : Sym2FlagType k} {G : Sym2LabeledGraph σ N}

/-! ## The full placement is the flag itself -/

/-- Adjacency in a σ-typed graph's decoded form is edge membership. -/
lemma sym2LabeledGraph_adj_iff (G : Sym2LabeledGraph σ N) (u v : Fin N) :
    G.toLabeledGraph.graph.Adj u v ↔ s(u, v) ∈ G.edges := by
  show (SimpleGraph.fromEdgeSet _).Adj u v ↔ _
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun huv => ?_⟩
    subst huv
    exact G.edges_valid _ h (Sym2.mk_isDiag_iff.mpr rfl)

/-- The induced labeled subflag on **all** vertices is the flag
itself. -/
lemma nonempty_coe_univ_iso (G : Sym2LabeledGraph σ N) :
    Nonempty ((⟨Finset.univ, Finset.subset_univ _⟩
        : Sym2InducedLabeledSubgraph G).toLabeledSubgraph.coe
      ≃f G.toLabeledGraph) := by
  refine ⟨{ graph_iso := ⟨Equiv.subtypeUnivEquiv fun x => Finset.mem_univ x, ?_⟩,
            type_preserve := ?_ }⟩
  · intro a b
    rw [sym2LabeledGraph_adj_iff]
    rw [labeledCoe_adj_iff_mem]
    show s(a.val, b.val) ∈ G.edges ↔ s(a.val, b.val) ∈ G.edges
    exact Iff.rfl
  · funext t
    have hre := (⟨Finset.univ, Finset.subset_univ _⟩
      : Sym2InducedLabeledSubgraph G).toLabeledSubgraph.embed_eq t
    exact hre

/-! ## Pattern normalization

A σ-typed pattern is normalized by extracting it from itself over its
full vertex set — its own rooted mask. The sweep's reflection then
canonicalizes it, and the placement criterion at `V = univ` identifies
the decoded normalization with the pattern. -/

/-- The rooted mask of a σ-typed flag. -/
def rootedMaskOf {k m : ℕ} {σ : Sym2FlagType k}
    (F : Sym2LabeledGraph σ m) : ℕ :=
  rootedExtractMask m F Finset.univ (maskOfGraph₂ (underlyingGraph F))

/-- The pattern is equivalent to the decoding of its own rooted mask. -/
theorem eqv_decode_rootedMaskOf {k m : ℕ} {σ : Sym2FlagType k}
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2LabeledGraph σ m) (hkm : k ≤ m)
    (hF : RootsMatch σ m (rootedMaskOf F)) :
    F ∼sf labeledGraphOfMask σ m hkm (rootedMaskOf F) hF := by
  have hV : (Finset.univ : Finset (Fin m)).card = m := by
    rw [Finset.card_univ, Fintype.card_fin]
  have h := (labeledCoe_iso_iff_rootedExtract_eqv (G := F) hinjm hinjm F
    Finset.univ (Finset.subset_univ _) hV).mp
    (by
      obtain ⟨e₀⟩ := nonempty_coe_univ_iso F
      obtain ⟨e₁⟩ := sym2LabeledGraphEqv.refl F
      exact ⟨labeledIso_trans e₀ e₁⟩)
  exact sym2LabeledGraphEqv.symm h

/-! ## The rooted mask count and the bridge -/

/-- Bit-level rooted placement count: the root-containing `m`-subsets of
the host whose rooted extraction passes `acc`. The root test uses the
kernel-reducible image form (`type_verts` itself is set machinery). -/
def rmaskCount (G : Sym2LabeledGraph σ N) (m : ℕ) (acc : ℕ → Bool)
    (h : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin N))).filter (fun V =>
    (decide ((Finset.univ.image fun t => G.type_embed t) ⊆ V)
      && decide (V.card = m)
      && acc (rootedExtractMask m G V h)) = true)).card

/-- **The σ-typed density numerator, bit-level** (single pattern). The
accept test decides labeled membership in the class of `F` on
roots-matching masks below the rank bound. -/
theorem labeledListCount_eq_rmaskCount (hkm : k ≤ m)
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    {c : ℕ}
    (hboundm : ∀ p ∈ finPairs m, pairIdx m p.1.val p.2.val < c)
    (F : Sym2LabeledGraph σ m) {acc : ℕ → Bool}
    (hacc : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σ m x,
      (acc x = true ↔ labeledGraphOfMask σ m hkm x hx ∼sf F)) :
    sym2InducedLabeledSubgraphListCount (sym2LabeledGraphToList F) G
      = rmaskCount G m acc (maskOfGraph₂ (underlyingGraph G)) := by
  have hmem : ∀ Gl : Sym2InducedLabeledSubgraphList 1 G,
      predIsoSym2LabeledHl (sym2LabeledGraphToList F) Gl ↔
        ((Gl 0).verts.card = m
          ∧ acc (rootedExtractMask m G (Gl 0).verts
              (maskOfGraph₂ (underlyingGraph G))) = true) := by
    intro Gl
    constructor
    · rintro ⟨hiso, -⟩
      obtain ⟨e⟩ := hiso 0
      have hV : (Gl 0).verts.card = m :=
        Finset.card_eq_of_equiv_fin e.graph_iso.toEquiv
      refine ⟨hV, ?_⟩
      refine (hacc _ (rootedExtractMask_lt hboundm _ _ _)
        (rootedExtractMask_rootsMatch hkm hinjN hinjm G (Gl 0).verts)).mpr ?_
      exact (labeledCoe_iso_iff_rootedExtract_eqv hinjN hinjm F
        (Gl 0).verts (Gl 0).verts_subset hV).mp ⟨e⟩
    · rintro ⟨hV, hacc'⟩
      refine ⟨?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
      intro i
      have hi0 : i = 0 := Subsingleton.elim i 0
      subst hi0
      exact (labeledCoe_iso_iff_rootedExtract_eqv hinjN hinjm F
        (Gl 0).verts (Gl 0).verts_subset hV).mpr
        ((hacc _ (rootedExtractMask_lt hboundm _ _ _)
          (rootedExtractMask_rootsMatch hkm hinjN hinjm G
            (Gl 0).verts)).mp hacc')
  unfold sym2InducedLabeledSubgraphListCount rmaskCount
  refine Finset.card_bij (fun Gl _ => (Gl 0).verts) ?_ ?_ ?_
  · intro Gl hGl
    simp only [finsetOfSym2InducedLabeledSubgraphListIsoHl, Finset.mem_filter,
      Finset.mem_univ, true_and] at hGl
    obtain ⟨hV, ha⟩ := (hmem Gl).mp hGl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨decide_eq_true ?_, decide_eq_true hV⟩, ha⟩
    rw [← Sym2LabeledGraph.type_verts_eq_image]
    exact (Gl 0).verts_subset
  · intro Gl₁ h₁ Gl₂ h₂ hEq
    have hEq' : (Gl₁ 0).verts = (Gl₂ 0).verts := hEq
    funext i
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    exact Sym2InducedLabeledSubgraph.ext hEq'
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
    rw [Bool.and_eq_true, Bool.and_eq_true] at hV
    obtain ⟨⟨hsub, hcard⟩, hac⟩ := hV
    have hTV : G.type_verts ⊆ V := by
      rw [Sym2LabeledGraph.type_verts_eq_image]
      exact of_decide_eq_true hsub
    refine ⟨fun _ => ⟨V, hTV⟩, ?_, rfl⟩
    simp only [finsetOfSym2InducedLabeledSubgraphListIsoHl, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (hmem _).mpr ⟨of_decide_eq_true hcard, hac⟩

/-! ## Class membership via rooted canonical forms -/

/-- With one root there are no root pairs: every mask matches. -/
lemma rootsMatch_one (σ₁ : Sym2FlagType 1) (m x : ℕ) :
    RootsMatch σ₁ m x := by
  intro i j hij
  exact absurd (Subsingleton.elim i j ▸ hij) (lt_irrefl j)

/-- Distinct rooted representatives make the rooted canonical form a
complete invariant of the labeled class (packaged over the reflection
and normalization facts, as in the unrooted `eqv_iff_canonOf_eq`). -/
theorem eqv_iff_rcanonImage_eq {kr mr c : ℕ} {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr) {rreps : List ℕ} {canonImage : ℕ → ℕ}
    (hreflect : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      canonImage x ∈ rreps
        ∧ ∃ hy : RootsMatch σr mr (canonImage x),
            labeledGraphOfMask σr mr hkm x hx
              ∼sf labeledGraphOfMask σr mr hkm (canonImage x) hy)
    (hdist : ∀ p ∈ rreps, ∀ q ∈ rreps,
      ∀ (hp : RootsMatch σr mr p) (hq : RootsMatch σr mr q),
        labeledGraphOfMask σr mr hkm p hp
          ∼sf labeledGraphOfMask σr mr hkm q hq → p = q)
    {x y : ℕ} (hx' : x < 2 ^ c) (hy' : y < 2 ^ c)
    (hx : RootsMatch σr mr x) (hy : RootsMatch σr mr y) :
    labeledGraphOfMask σr mr hkm x hx ∼sf labeledGraphOfMask σr mr hkm y hy
      ↔ canonImage x = canonImage y := by
  obtain ⟨hxm, hxc, hxe⟩ := hreflect x hx' hx
  obtain ⟨hym, hyc, hye⟩ := hreflect y hy' hy
  constructor
  · intro h
    exact hdist _ hxm _ hym hxc hyc
      (((sym2LabeledGraphEqv.symm hxe).trans h).trans hye)
  · intro h
    refine (hxe.trans ?_).trans (sym2LabeledGraphEqv.symm hye)
    have heq : labeledGraphOfMask σr mr hkm (canonImage x) hxc
        = labeledGraphOfMask σr mr hkm (canonImage y) hyc := by
      congr 1
    rw [heq]
    exact sym2LabeledGraphEqv.refl _

/-- **Converse transport.** A labeled equivalence of decoded flags
yields a root-fixing injective vertex map with corresponding bits — so
representative distinctness can be checked at the **mask level, for all
type graphs at once** (the existential over `Fin m → Fin m` is decidable
by finite enumeration). -/
theorem bits_of_labeledEqv {kr mr : ℕ} {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr) {x y : ℕ} {hx : RootsMatch σr mr x}
    {hy : RootsMatch σr mr y}
    (h : labeledGraphOfMask σr mr hkm x hx
      ∼sf labeledGraphOfMask σr mr hkm y hy) :
    ∃ f : Fin mr → Fin mr, Function.Injective f
      ∧ (∀ i : Fin kr, f (Fin.castLE hkm i) = Fin.castLE hkm i)
      ∧ ∀ a b : Fin mr, a < b →
          x.testBit (pairIdx mr a.val b.val)
            = y.testBit (pairIdx mr (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val) := by
  obtain ⟨e⟩ := h
  refine ⟨fun v => e.graph_iso v, fun a b hEq => ?_, ?_, ?_⟩
  · exact e.graph_iso.toEquiv.injective hEq
  · intro i
    exact congrFun e.type_preserve i
  · intro a b hab
    have hrel := e.graph_iso.map_rel_iff (a := a) (b := b)
    rw [labeledGraphOfMask_adj_iff, labeledGraphOfMask_adj_iff] at hrel
    have hfab : e.graph_iso a ≠ e.graph_iso b :=
      fun hEq => hab.ne (e.graph_iso.toEquiv.injective hEq)
    have hcd := sort2_lt hfab
    rw [Bool.eq_iff_iff, testBit_iff_mem_edges₂ hab,
      testBit_iff_mem_edges₂ hcd,
      show (s((sort2 (e.graph_iso a) (e.graph_iso b)).1,
            (sort2 (e.graph_iso a) (e.graph_iso b)).2) : Sym2 (Fin mr))
          = s(e.graph_iso a, e.graph_iso b) from sort2_sym2 _ _]
    exact hrel.symm

/-- Distinctness for every type graph from the mask-level check: if no
listed pair of distinct representatives is related by a root-fixing
bit-correspondence, decoded representatives are distinct in every
labeled class. -/
theorem rdist_of_maskCheck {kr mr : ℕ} (hkm' : kr ≤ mr) {rreps : List ℕ}
    (hcheck : ∀ p ∈ rreps, ∀ q ∈ rreps,
      (∃ f : Fin mr → Fin mr, Function.Injective f
        ∧ (∀ i : Fin kr, f (Fin.castLE hkm' i) = Fin.castLE hkm' i)
        ∧ ∀ a b : Fin mr, a < b →
            p.testBit (pairIdx mr a.val b.val)
              = q.testBit (pairIdx mr (sort2 (f a) (f b)).1.val
                  (sort2 (f a) (f b)).2.val)) → p = q)
    {σr : Sym2FlagType kr} :
    ∀ p ∈ rreps, ∀ q ∈ rreps,
      ∀ (hp : RootsMatch σr mr p) (hq : RootsMatch σr mr q),
        labeledGraphOfMask σr mr hkm' p hp
          ∼sf labeledGraphOfMask σr mr hkm' q hq → p = q := by
  intro p hp' q hq' hp hq h
  obtain ⟨f, hf, hfix, hbits⟩ := bits_of_labeledEqv hkm' h
  exact hcheck p hp' q hq' ⟨f, hf, hfix, hbits⟩

/-- **Packaged accept-spec**: comparing rooted canonical forms against
the pattern's normalized mask decides labeled class membership, given
the sweep reflection and representative distinctness of the
combination. -/
theorem racc_spec_of {kr mr c : ℕ} {σr : Sym2FlagType kr} (hkm : kr ≤ mr)
    {rreps : List ℕ} {canonImage : ℕ → ℕ}
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val < c)
    (hreflect : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      canonImage x ∈ rreps
        ∧ ∃ hy : RootsMatch σr mr (canonImage x),
            labeledGraphOfMask σr mr hkm x hx
              ∼sf labeledGraphOfMask σr mr hkm (canonImage x) hy)
    (hdist : ∀ p ∈ rreps, ∀ q ∈ rreps,
      ∀ (hp : RootsMatch σr mr p) (hq : RootsMatch σr mr q),
        labeledGraphOfMask σr mr hkm p hp
          ∼sf labeledGraphOfMask σr mr hkm q hq → p = q)
    (F : Sym2LabeledGraph σr mr) :
    ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      ((canonImage x == canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask σr mr hkm x hx ∼sf F) := by
  intro x hx' hx
  rw [beq_iff_eq]
  have hFm : rootedMaskOf F < 2 ^ c :=
    rootedExtractMask_lt hboundm _ _ _
  have hFr : RootsMatch σr mr (rootedMaskOf F) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm F Finset.univ
  have hFe := eqv_decode_rootedMaskOf hinjm F hkm hFr
  rw [← eqv_iff_rcanonImage_eq hkm hreflect hdist hx' hFm hx hFr]
  constructor
  · intro h
    exact h.trans (sym2LabeledGraphEqv.symm hFe)
  · intro h
    exact h.trans hFe

/-! ## Typed flag-set completeness (the generation layer)

The σ-typed flag *sets* emitted by `generate_flags` need two facts the
generator previously proved by one `native_decide` against its own
enumeration: the emitted classes are **all** of `Sym2Flag σ n`
(`= univ`), and they are pairwise distinct (`Nodup`). Both follow from
the rooted sweeps: every labeled flag normalizes to the decoding of its
rooted canonical mask, so a kernel-checkable Bool coverage/distinctness
of the canonical masks suffices. -/

/-- Every σ-typed flag is equivalent to the decoding of its rooted
canonical mask (packaged over the sweep reflection). -/
theorem lcanonOf_spec_of {kr mr c : ℕ} {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr) {rreps : List ℕ} {canonImage : ℕ → ℕ}
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val < c)
    (hreflect : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      canonImage x ∈ rreps
        ∧ ∃ hy : RootsMatch σr mr (canonImage x),
            labeledGraphOfMask σr mr hkm x hx
              ∼sf labeledGraphOfMask σr mr hkm (canonImage x) hy)
    (G : Sym2LabeledGraph σr mr) :
    canonImage (rootedMaskOf G) ∈ rreps
      ∧ ∃ hy : RootsMatch σr mr (canonImage (rootedMaskOf G)),
          G ∼sf labeledGraphOfMask σr mr hkm
            (canonImage (rootedMaskOf G)) hy := by
  have hGr : RootsMatch σr mr (rootedMaskOf G) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm G Finset.univ
  obtain ⟨hmem, hyc, hye⟩ := hreflect (rootedMaskOf G)
    (rootedExtractMask_lt hboundm _ _ _) hGr
  exact ⟨hmem, hyc,
    (eqv_decode_rootedMaskOf hinjm G hkm hGr).trans hye⟩

/-- Generic bridge from list completeness to `toFinset = univ`, stated
over an abstract `α` so instance resolution happens at the call site
(where `Sym2Flag`-headed instances apply). -/
theorem toFinset_eq_univ_of_forall_mem {α : Type _} [Fintype α]
    [DecidableEq α] {l : List α} (h : ∀ x : α, x ∈ l) :
    l.toFinset = Finset.univ :=
  Finset.eq_univ_iff_forall.mpr fun x => List.mem_toFinset.mpr (h x)

/-- **Emitted typed flags are complete**: if every roots-matching
representative is hit by the canonicalization of some emitted flag
(kernel-checkable), the emitted classes are all of `Sym2Flag σ n`.
Representative distinctness is **not** needed — only the sweep
reflection. -/
theorem labeledEmitted_complete {kr mr c : ℕ}
    {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr) {rreps : List ℕ}
    {canonImage : ℕ → ℕ}
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val < c)
    (hreflect : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      canonImage x ∈ rreps
        ∧ ∃ hy : RootsMatch σr mr (canonImage x),
            labeledGraphOfMask σr mr hkm x hx
              ∼sf labeledGraphOfMask σr mr hkm (canonImage x) hy)
    (Ls : List (Sym2LabeledGraph σr mr))
    (hcover : ∀ h ∈ rreps, RootsMatch σr mr h →
      h ∈ Ls.map (fun L => canonImage (rootedMaskOf L))) :
    ∀ S : Sym2Flag σr mr,
      S ∈ Ls.map (fun L => (⟦L⟧ : Sym2Flag σr mr)) := by
  intro S
  rw [List.mem_map]
  obtain ⟨G, rfl⟩ := Quotient.exists_rep S
  have hbG : rootedMaskOf G < 2 ^ c := rootedExtractMask_lt hboundm _ _ _
  have hrG : RootsMatch σr mr (rootedMaskOf G) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm G Finset.univ
  obtain ⟨hmem, hyc, hye⟩ := hreflect (rootedMaskOf G) hbG hrG
  obtain ⟨L, hL, hLc⟩ := List.mem_map.mp (hcover _ hmem hyc)
  refine ⟨L, hL, ?_⟩
  have hbL : rootedMaskOf L < 2 ^ c := rootedExtractMask_lt hboundm _ _ _
  have hrL : RootsMatch σr mr (rootedMaskOf L) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm L Finset.univ
  obtain ⟨-, hyL, hyeL⟩ := hreflect (rootedMaskOf L) hbL hrL
  have heq : labeledGraphOfMask σr mr hkm
      (canonImage (rootedMaskOf L)) hyL
        = labeledGraphOfMask σr mr hkm
            (canonImage (rootedMaskOf G)) hyc := by
    congr 1
  have hmid : labeledGraphOfMask σr mr hkm
      (canonImage (rootedMaskOf L)) hyL
        ∼sf labeledGraphOfMask σr mr hkm
            (canonImage (rootedMaskOf G)) hyc := by
    rw [heq]
    exact sym2LabeledGraphEqv.refl _
  exact Quotient.sound
    ((((eqv_decode_rootedMaskOf hinjm L hkm hrL).trans hyeL).trans hmid).trans
      (sym2LabeledGraphEqv.symm
        ((eqv_decode_rootedMaskOf hinjm G hkm hrG).trans hye)))

/-- **Emitted typed flags are distinct**: if the emitted flags' rooted
canonical masks are pairwise distinct naturals (kernel-checkable), the
emitted classes are `Nodup`. -/
theorem labeledEmitted_nodup {kr mr c : ℕ}
    {σr : Sym2FlagType kr} (hkm : kr ≤ mr) {rreps : List ℕ}
    {canonImage : ℕ → ℕ}
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val < c)
    (hreflect : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      canonImage x ∈ rreps
        ∧ ∃ hy : RootsMatch σr mr (canonImage x),
            labeledGraphOfMask σr mr hkm x hx
              ∼sf labeledGraphOfMask σr mr hkm (canonImage x) hy)
    (hdist : ∀ p ∈ rreps, ∀ q ∈ rreps,
      ∀ (hp : RootsMatch σr mr p) (hq : RootsMatch σr mr q),
        labeledGraphOfMask σr mr hkm p hp
          ∼sf labeledGraphOfMask σr mr hkm q hq → p = q)
    (Ls : List (Sym2LabeledGraph σr mr))
    (hnodup : (Ls.map (fun L => canonImage (rootedMaskOf L))).Nodup) :
    (Ls.map (fun L => (⟦L⟧ : Sym2Flag σr mr))).Nodup := by
  have hinj := List.inj_on_of_nodup_map hnodup
  refine (List.Nodup.of_map _ hnodup).map_on ?_
  intro a ha b hb hEq
  refine hinj ha hb ?_
  have hba : rootedMaskOf a < 2 ^ c := rootedExtractMask_lt hboundm _ _ _
  have hbb : rootedMaskOf b < 2 ^ c := rootedExtractMask_lt hboundm _ _ _
  have hra : RootsMatch σr mr (rootedMaskOf a) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm a Finset.univ
  have hrb : RootsMatch σr mr (rootedMaskOf b) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm b Finset.univ
  refine (eqv_iff_rcanonImage_eq hkm hreflect hdist hba hbb hra hrb).mp ?_
  have hab : a ∼sf b := Quotient.exact hEq
  exact ((sym2LabeledGraphEqv.symm
      (eqv_decode_rootedMaskOf hinjm a hkm hra)).trans hab).trans
    (eqv_decode_rootedMaskOf hinjm b hkm hrb)

/-- **Emitted typed flags are distinct, directly**: a kernel Bool check
that no two distinct emitted rooted masks are related by a root-fixing
bit-correspondence (via the converse transport `bits_of_labeledEqv`)
gives `Nodup` of the emitted classes — no representative-distinctness
sweep apparatus needed, so this scales to combinations whose full
`rdist` check is infeasible (e.g. `(2,6)` with 1992 representatives). -/
theorem labeledEmitted_nodup_direct {kr mr : ℕ} {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr)
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (Ls : List (Sym2LabeledGraph σr mr))
    (hcheck : ((Ls.map (fun L => rootedMaskOf L)).all (fun p =>
        (Ls.map (fun L => rootedMaskOf L)).all (fun q =>
          p == q
            || !(decide (∃ f : Fin mr → Fin mr, Function.Injective f
                ∧ (∀ i : Fin kr, f (Fin.castLE hkm i) = Fin.castLE hkm i)
                ∧ ∀ a b : Fin mr, a < b →
                    p.testBit (pairIdx mr a.val b.val)
                      = q.testBit (pairIdx mr (sort2 (f a) (f b)).1.val
                          (sort2 (f a) (f b)).2.val)))))) = true)
    (hnodup : (Ls.map (fun L => rootedMaskOf L)).Nodup) :
    (Ls.map (fun L => (⟦L⟧ : Sym2Flag σr mr))).Nodup := by
  have hinj := List.inj_on_of_nodup_map hnodup
  refine (List.Nodup.of_map _ hnodup).map_on ?_
  intro a ha b hb hEq
  refine hinj ha hb ?_
  have hra : RootsMatch σr mr (rootedMaskOf a) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm a Finset.univ
  have hrb : RootsMatch σr mr (rootedMaskOf b) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm b Finset.univ
  have hab : a ∼sf b := Quotient.exact hEq
  have hchain : labeledGraphOfMask σr mr hkm (rootedMaskOf a) hra
      ∼sf labeledGraphOfMask σr mr hkm (rootedMaskOf b) hrb :=
    ((sym2LabeledGraphEqv.symm
        (eqv_decode_rootedMaskOf hinjm a hkm hra)).trans hab).trans
      (eqv_decode_rootedMaskOf hinjm b hkm hrb)
  obtain ⟨f, hf, hfix, hbits⟩ := bits_of_labeledEqv hkm hchain
  have hpa : rootedMaskOf a ∈ Ls.map (fun L => rootedMaskOf L) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hpb : rootedMaskOf b ∈ Ls.map (fun L => rootedMaskOf L) :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  have h2 := List.all_eq_true.mp
    (List.all_eq_true.mp hcheck _ hpa) _ hpb
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact beq_iff_eq.mp h2
  · have hb : ∀ b : Bool, (!b) = true → b = false := by decide
    exact absurd ⟨f, hf, hfix, hbits⟩
      (of_decide_eq_false (hb _ h2))


/-- Bit-level rooted pair count: ordered pairs of root-containing
subsets, disjoint away from the roots, whose rooted extractions pass
the two accepts. -/
def rmaskCount₂ (G : Sym2LabeledGraph σ N) (m₀ m₁ : ℕ)
    (acc₀ acc₁ : ℕ → Bool) (h : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
    (fun P =>
      (decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.1)
        && decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.2)
        && decide (P.1.card = m₀) && decide (P.2.card = m₁)
        && decide ((P.1 \ (Finset.univ.image fun t => G.type_embed t))
            ∩ (P.2 \ (Finset.univ.image fun t => G.type_embed t)) = ∅)
        && acc₀ (rootedExtractMask m₀ G P.1 h)
        && acc₁ (rootedExtractMask m₁ G P.2 h)) = true)).card

/-- **The σ-typed pair-density numerator, bit-level.** -/
theorem labeledListCount₂_eq_rmaskCount₂ {m₀ m₁ : ℕ}
    (hkm₀ : k ≤ m₀) (hkm₁ : k ≤ m₁)
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm₀ : ∀ p₁ ∈ finPairs m₀, ∀ p₂ ∈ finPairs m₀,
      pairIdx m₀ p₁.1.val p₁.2.val = pairIdx m₀ p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm₁ : ∀ p₁ ∈ finPairs m₁, ∀ p₂ ∈ finPairs m₁,
      pairIdx m₁ p₁.1.val p₁.2.val = pairIdx m₁ p₂.1.val p₂.2.val → p₁ = p₂)
    {c₀ c₁ : ℕ}
    (hboundm₀ : ∀ p ∈ finPairs m₀, pairIdx m₀ p.1.val p.2.val < c₀)
    (hboundm₁ : ∀ p ∈ finPairs m₁, pairIdx m₁ p.1.val p.2.val < c₁)
    (F₀ : Sym2LabeledGraph σ m₀) (F₁ : Sym2LabeledGraph σ m₁)
    {acc₀ acc₁ : ℕ → Bool}
    (hacc₀ : ∀ x, x < 2 ^ c₀ → ∀ hx : RootsMatch σ m₀ x,
      (acc₀ x = true ↔ labeledGraphOfMask σ m₀ hkm₀ x hx ∼sf F₀))
    (hacc₁ : ∀ x, x < 2 ^ c₁ → ∀ hx : RootsMatch σ m₁ x,
      (acc₁ x = true ↔ labeledGraphOfMask σ m₁ hkm₁ x hx ∼sf F₁)) :
    sym2InducedLabeledSubgraphListCount
        (sym2LabeledGraphPairToList F₀ F₁) G
      = rmaskCount₂ G m₀ m₁ acc₀ acc₁
          (maskOfGraph₂ (underlyingGraph G)) := by
  have hone : ∀ (V : Finset (Fin N)) (hTV : G.type_verts ⊆ V)
      {mp cp : ℕ} (hkmp : k ≤ mp)
      (hinjmp : ∀ p₁ ∈ finPairs mp, ∀ p₂ ∈ finPairs mp,
        pairIdx mp p₁.1.val p₁.2.val = pairIdx mp p₂.1.val p₂.2.val
          → p₁ = p₂)
      (hboundmp : ∀ p ∈ finPairs mp, pairIdx mp p.1.val p.2.val < cp)
      (Fp : Sym2LabeledGraph σ mp) {accp : ℕ → Bool}
      (haccp : ∀ x, x < 2 ^ cp → ∀ hx : RootsMatch σ mp x,
        (accp x = true ↔ labeledGraphOfMask σ mp hkmp x hx ∼sf Fp)),
      Nonempty ((⟨V, hTV⟩ : Sym2InducedLabeledSubgraph
          G).toLabeledSubgraph.coe ≃f Fp.toLabeledGraph)
        ↔ (V.card = mp
            ∧ accp (rootedExtractMask mp G V
                (maskOfGraph₂ (underlyingGraph G))) = true) := by
    intro V hTV mp cp hkmp hinjmp hboundmp Fp accp haccp
    constructor
    · rintro ⟨e⟩
      have hV : V.card = mp :=
        Finset.card_eq_of_equiv_fin e.graph_iso.toEquiv
      refine ⟨hV, ?_⟩
      refine (haccp _ (rootedExtractMask_lt hboundmp _ _ _)
        (rootedExtractMask_rootsMatch hkmp hinjN hinjmp G V)).mpr ?_
      exact (labeledCoe_iso_iff_rootedExtract_eqv hinjN hinjmp Fp
        V hTV hV).mp ⟨e⟩
    · rintro ⟨hV, ha⟩
      exact (labeledCoe_iso_iff_rootedExtract_eqv hinjN hinjmp Fp
        V hTV hV).mpr
        ((haccp _ (rootedExtractMask_lt hboundmp _ _ _)
          (rootedExtractMask_rootsMatch hkmp hinjN hinjmp G V)).mp ha)
  have hmem : ∀ Gl : Sym2InducedLabeledSubgraphList 2 G,
      predIsoSym2LabeledHl (sym2LabeledGraphPairToList F₀ F₁) Gl ↔
        (((Gl 0).verts.card = m₀
            ∧ acc₀ (rootedExtractMask m₀ G (Gl 0).verts
                (maskOfGraph₂ (underlyingGraph G))) = true)
          ∧ ((Gl 1).verts.card = m₁
            ∧ acc₁ (rootedExtractMask m₁ G (Gl 1).verts
                (maskOfGraph₂ (underlyingGraph G))) = true)
          ∧ ((Gl 0).verts \ G.type_verts)
              ∩ ((Gl 1).verts \ G.type_verts) = ∅) := by
    intro Gl
    constructor
    · rintro ⟨hiso, hdisj⟩
      refine ⟨(hone (Gl 0).verts (Gl 0).verts_subset hkm₀ hinjm₀
          hboundm₀ F₀ hacc₀).mp (hiso 0),
        (hone (Gl 1).verts (Gl 1).verts_subset hkm₁ hinjm₁
          hboundm₁ F₁ hacc₁).mp (hiso 1),
        hdisj (0 : Fin 2) (1 : Fin 2) (by decide)⟩
    · rintro ⟨h0, h1, hd⟩
      constructor
      · intro i
        match i with
        | 0 => exact (hone (Gl 0).verts (Gl 0).verts_subset hkm₀ hinjm₀
            hboundm₀ F₀ hacc₀).mpr h0
        | 1 => exact (hone (Gl 1).verts (Gl 1).verts_subset hkm₁ hinjm₁
            hboundm₁ F₁ hacc₁).mpr h1
      · intro i j hij
        match i, j with
        | 0, 0 => exact absurd rfl hij
        | 0, 1 => exact hd
        | 1, 0 => rw [Finset.inter_comm]; exact hd
        | 1, 1 => exact absurd rfl hij
  unfold sym2InducedLabeledSubgraphListCount rmaskCount₂
  refine Finset.card_bij (fun Gl _ => ((Gl 0).verts, (Gl 1).verts)) ?_ ?_ ?_
  · intro Gl hGl
    simp only [finsetOfSym2InducedLabeledSubgraphListIsoHl,
      Finset.mem_filter, Finset.mem_univ, true_and] at hGl
    obtain ⟨⟨hV₀, ha₀⟩, ⟨hV₁, ha₁⟩, hd⟩ := (hmem Gl).mp hGl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Bool.and_eq_true]
    rw [← Sym2LabeledGraph.type_verts_eq_image]
    exact ⟨⟨⟨⟨⟨⟨decide_eq_true (Gl 0).verts_subset,
      decide_eq_true (Gl 1).verts_subset⟩,
      decide_eq_true hV₀⟩, decide_eq_true hV₁⟩,
      decide_eq_true hd⟩, ha₀⟩, ha₁⟩
  · intro Gl₁ h₁ Gl₂ h₂ hEq
    have hEq0 : (Gl₁ 0).verts = (Gl₂ 0).verts := congrArg Prod.fst hEq
    have hEq1 : (Gl₁ 1).verts = (Gl₂ 1).verts := congrArg Prod.snd hEq
    funext i
    match i with
    | 0 => exact Sym2InducedLabeledSubgraph.ext hEq0
    | 1 => exact Sym2InducedLabeledSubgraph.ext hEq1
  · intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
    simp only [Bool.and_eq_true] at hP
    obtain ⟨⟨⟨⟨⟨⟨hs₀, hs₁⟩, hc₀⟩, hc₁⟩, hd⟩, ha₀⟩, ha₁⟩ := hP
    have hT₀ : G.type_verts ⊆ P.1 := by
      rw [Sym2LabeledGraph.type_verts_eq_image]
      exact of_decide_eq_true hs₀
    have hT₁ : G.type_verts ⊆ P.2 := by
      rw [Sym2LabeledGraph.type_verts_eq_image]
      exact of_decide_eq_true hs₁
    refine ⟨![⟨P.1, hT₀⟩, ⟨P.2, hT₁⟩], ?_, rfl⟩
    simp only [finsetOfSym2InducedLabeledSubgraphListIsoHl,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine (hmem _).mpr
      ⟨⟨of_decide_eq_true hc₀, ha₀⟩, ⟨of_decide_eq_true hc₁, ha₁⟩, ?_⟩
    have hd' := of_decide_eq_true hd
    rw [Sym2LabeledGraph.type_verts_eq_image]
    exact hd'

/-- **The σ-typed pair density, bit-level.** -/
theorem sym2FlagDensity₂_eq_rmaskCount₂ {m₀ m₁ : ℕ}
    (hkm₀ : k ≤ m₀) (hkm₁ : k ≤ m₁)
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm₀ : ∀ p₁ ∈ finPairs m₀, ∀ p₂ ∈ finPairs m₀,
      pairIdx m₀ p₁.1.val p₁.2.val = pairIdx m₀ p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm₁ : ∀ p₁ ∈ finPairs m₁, ∀ p₂ ∈ finPairs m₁,
      pairIdx m₁ p₁.1.val p₁.2.val = pairIdx m₁ p₂.1.val p₂.2.val → p₁ = p₂)
    {c₀ c₁ : ℕ}
    (hboundm₀ : ∀ p ∈ finPairs m₀, pairIdx m₀ p.1.val p.2.val < c₀)
    (hboundm₁ : ∀ p ∈ finPairs m₁, pairIdx m₁ p.1.val p.2.val < c₁)
    (F₀ : Sym2LabeledGraph σ m₀) (F₁ : Sym2LabeledGraph σ m₁)
    {acc₀ acc₁ : ℕ → Bool}
    (hacc₀ : ∀ x, x < 2 ^ c₀ → ∀ hx : RootsMatch σ m₀ x,
      (acc₀ x = true ↔ labeledGraphOfMask σ m₀ hkm₀ x hx ∼sf F₀))
    (hacc₁ : ∀ x, x < 2 ^ c₁ → ∀ hx : RootsMatch σ m₁ x,
      (acc₁ x = true ↔ labeledGraphOfMask σ m₁ hkm₁ x hx ∼sf F₁)) :
    sym2FlagDensity₂ (⟦F₀⟧ : Sym2Flag σ m₀) (⟦F₁⟧ : Sym2Flag σ m₁)
        (⟦G⟧ : Sym2Flag σ N)
      = (rmaskCount₂ G m₀ m₁ acc₀ acc₁
            (maskOfGraph₂ (underlyingGraph G)) : ℚ)
          / multinomialCoefficient
              (fun i : Fin 2 =>
                (match i with | 0 => m₀ | 1 => m₁) - k) (N - k) := by
  show sym2InducedLabeledSubgraphListDensity
    (sym2LabeledGraphPairToList F₀ F₁) G = _
  rw [sym2InducedLabeledSubgraphListDensity,
    labeledListCount₂_eq_rmaskCount₂ hkm₀ hkm₁ hinjN hinjm₀ hinjm₁
      hboundm₀ hboundm₁ F₀ F₁ hacc₀ hacc₁]
  rfl

/-- **The σ-typed density, bit-level** (single pattern). -/
theorem sym2FlagDensity₁_eq_rmaskCount (hkm : k ≤ m)
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    {c : ℕ}
    (hboundm : ∀ p ∈ finPairs m, pairIdx m p.1.val p.2.val < c)
    (F : Sym2LabeledGraph σ m) {acc : ℕ → Bool}
    (hacc : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σ m x,
      (acc x = true ↔ labeledGraphOfMask σ m hkm x hx ∼sf F)) :
    sym2FlagDensity₁ (⟦F⟧ : Sym2Flag σ m) (⟦G⟧ : Sym2Flag σ N)
      = (rmaskCount G m acc (maskOfGraph₂ (underlyingGraph G)) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => m - k) (N - k) := by
  show sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) G = _
  rw [sym2InducedLabeledSubgraphListDensity,
    labeledListCount_eq_rmaskCount hkm hinjN hinjm hboundm F hacc]

end FlagAlgebras.Compute.BitMask
