import LeanFlagAlgebras.FlagAlgebra.Compute.IsoInvariants
import Mathlib.Data.Nat.Bitwise

/-! # Bitmask literals for simple graphs (2-graphs)

A simple graph on `n` vertices is encoded as a natural number whose bit
`pairIdx n a b` records the edge `{a, b}` (for `a < b`), pairs ranked in
lexicographic order. `graphOfMask₂` decodes a mask back to the
`Finset`-backed `Sym2Graph`, so every mask-level check can be transported
to a statement about the computable flags; hot loops (canonicalization
sweeps, forbidden-subgraph tests) pay a handful of `ℕ`-operations per
incidence test and never touch `Finset`/`Sym2` internals.

This is the 2-graph port of the 3-uniform machinery that carried the
order-7 tetrahedron certificate (its `Mask3`): the lexicographic pair
rank replaces the triple rank, `sort2` replaces the `sort3` comparison
network, and the isomorphism transport lands in this repository's flag
equivalence `∼sf` (via `sym2GraphEqv_of_equiv`) instead of a bespoke
`IsIso`. The mask sweep combinators (`sweepMasks` and its reflection /
gluing lemmas) are reproduced verbatim — they are representation-generic.

Everything here is generic in `n`; per-`n` literal instantiations
(witness tables, representative lists, the leaf checker) live with the
canonicalization examples. -/

namespace FlagAlgebras.Compute.BitMask

/-! ## Lexicographic ranks of pairs

`pairIdx n a b` is the position of `(a, b)` (with `a < b < n`) in the
lexicographic enumeration of all sorted pairs from `{0, …, n − 1}` — a
closed telescoping formula: under the sortedness guards every
subtraction is nonnegative and the division exact, so the `ℕ`-valued
expression computes the true rank. -/

/-- Lexicographic rank of the sorted pair `(a, b)` among the pairs of
`{0, …, n − 1}`. Meaningful for `a < b < n`. -/
def pairIdx (n a b : ℕ) : ℕ :=
  ((n - 1) * n - (n - a) * (n - 1 - a)) / 2 + b - a - 1

/-- The sorted pairs of `Fin n`, in lexicographic order. -/
def finPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).filterMap fun b =>
      if a < b then some (a, b) else none

lemma mem_finPairs {n : ℕ} {a b : Fin n} :
    (a, b) ∈ finPairs n ↔ a < b := by
  constructor
  · intro hp
    obtain ⟨a', -, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b', -, hp⟩ := List.mem_filterMap.mp hp
    by_cases h : a' < b'
    · rw [if_pos h] at hp
      have heq := Option.some.inj hp
      simp only [Prod.ext_iff] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact h
    · rw [if_neg h] at hp
      cases hp
  · intro hab
    refine List.mem_flatMap.mpr ⟨a, List.mem_finRange a, ?_⟩
    exact List.mem_filterMap.mpr ⟨b, List.mem_finRange b, by rw [if_pos hab]⟩

/-! The closed formula agrees with the enumeration order at every vertex
count the pipeline can use (kernel-checked): mapping the rank over the
lexicographic listing yields `0, 1, 2, …` on the nose. This
simultaneously certifies correctness of the rank, its injectivity on
sorted pairs, and surjectivity onto the index range. -/

example : (finPairs 3).map (fun p => pairIdx 3 p.1.val p.2.val)
    = List.range 3 := by decide
example : (finPairs 4).map (fun p => pairIdx 4 p.1.val p.2.val)
    = List.range 6 := by decide
example : (finPairs 5).map (fun p => pairIdx 5 p.1.val p.2.val)
    = List.range 10 := by decide
example : (finPairs 6).map (fun p => pairIdx 6 p.1.val p.2.val)
    = List.range 15 := by decide
example : (finPairs 7).map (fun p => pairIdx 7 p.1.val p.2.val)
    = List.range 21 := by decide
example : (finPairs 8).map (fun p => pairIdx 8 p.1.val p.2.val)
    = List.range 28 := by decide

/-! ## The mask-to-graph bridge

`graphOfMask₂ n m` reads a bitmask back as a `Sym2Graph`: the edges are
`s(a, b)` for the sorted pairs whose bit is set. This is the
specification-side meaning of a mask; the sweeps never evaluate it. -/

/-- The simple graph encoded by a bitmask: edge `{a, b}` (with `a < b`)
present iff bit `pairIdx n a b` is set. -/
def graphOfMask₂ (n m : ℕ) : Sym2Graph n where
  edges :=
    ((finPairs n).filter fun p =>
      m.testBit (pairIdx n p.1.val p.2.val)).toFinset.image
      fun p => s(p.1, p.2)
  edges_valid := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    rw [List.mem_toFinset, List.mem_filter] at hp
    obtain ⟨a, b⟩ := p
    have hab := mem_finPairs.mp hp.1
    rw [Sym2.mk_isDiag_iff]
    exact hab.ne

/-- Membership description of the edges of `graphOfMask₂`. -/
lemma mem_graphOfMask₂_edges {n m : ℕ} {e : Sym2 (Fin n)} :
    e ∈ (graphOfMask₂ n m).edges ↔
      ∃ a b : Fin n, a < b
        ∧ m.testBit (pairIdx n a.val b.val) = true
        ∧ e = s(a, b) := by
  show e ∈ Finset.image _ _ ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_toFinset, List.mem_filter] at hp
    obtain ⟨a, b⟩ := p
    exact ⟨a, b, mem_finPairs.mp hp.1, hp.2, rfl⟩
  · rintro ⟨a, b, hab, hbit, rfl⟩
    refine ⟨(a, b), ?_, rfl⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_finPairs.mpr hab, hbit⟩

/-- A sorted pair's bit is set exactly when its edge is in the
decoding. -/
lemma testBit_iff_mem_edges₂ {n m : ℕ} {a b : Fin n} (hab : a < b) :
    m.testBit (pairIdx n a.val b.val) = true
      ↔ s(a, b) ∈ (graphOfMask₂ n m).edges := by
  constructor
  · intro hm
    exact mem_graphOfMask₂_edges.mpr ⟨a, b, hab, hm, rfl⟩
  · intro hm
    obtain ⟨x, y, hxy, hbit, heq⟩ := mem_graphOfMask₂_edges.mp hm
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hax, hby⟩ | ⟨hay, hbx⟩
    · rw [hax, hby]
      exact hbit
    · subst hay
      subst hbx
      exact absurd (hab.trans hxy) (lt_irrefl _)

/-! ## Sorting a pair -/

/-- Sort two values. -/
def sort2 {α : Type} [LinearOrder α] (a b : α) : α × α :=
  if a ≤ b then (a, b) else (b, a)

/-- On distinct inputs the output is strictly sorted. -/
lemma sort2_lt {α : Type} [LinearOrder α] {a b : α} (hab : a ≠ b) :
    (sort2 a b).1 < (sort2 a b).2 := by
  unfold sort2
  split_ifs with h
  · exact h.lt_of_ne hab
  · exact (not_le.mp h)

/-- The output names the same unordered pair. -/
lemma sort2_sym2 {α : Type} [LinearOrder α] (a b : α) :
    s((sort2 a b).1, (sort2 a b).2) = s(a, b) := by
  unfold sort2
  split_ifs
  · rfl
  · exact Sym2.eq_swap

/-! ## Mask-level isomorphism transport

The canonicalization sweep matches a mask against a listed
representative by exhibiting a vertex bijection under which the pair
bits correspond. The bridge theorem converts the bit-level
correspondence into the flag equivalence `∼sf` of the decoded graphs —
hence equality of their classes in `Sym2EmptyTypedFlag`. The
correspondence hypothesis is decidable, so a sweep discharges it per
(mask, representative, map) by kernel computation alone. -/

/-- The load-bearing transport for canonicalization sweeps: an injective
vertex map under which every pair bit of `m` equals the bit of the
sorted image pair in `h` decodes to a flag equivalence of the graphs.
The hypothesis is decidable for literal `n`, `f`, `m`, `h`. -/
theorem graphOfMask₂_eqv_of_bits {n : ℕ} {f : Fin n → Fin n}
    (hf : Function.Injective f) {m h : ℕ}
    (hbits : ∀ a b : Fin n, a < b →
      m.testBit (pairIdx n a.val b.val)
        = h.testBit (pairIdx n (sort2 (f a) (f b)).1.val
            (sort2 (f a) (f b)).2.val)) :
    graphOfMask₂ n m ∼sf graphOfMask₂ n h := by
  have hbij : Function.Bijective f := ⟨hf, Finite.surjective_of_injective hf⟩
  refine sym2GraphEqv_of_equiv (Equiv.ofBijective f hbij) ?_
  intro e
  induction e using Sym2.ind with | _ x y =>
  rw [show Sym2.map (Equiv.ofBijective f hbij) s(x, y) = s(f x, f y) from
    Sym2.map_pair_eq _ _ _]
  rcases eq_or_ne x y with rfl | hxy
  · constructor
    · intro hmem
      exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
        ((graphOfMask₂ n m).edges_valid _ hmem)
    · intro hmem
      exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
        ((graphOfMask₂ n h).edges_valid _ hmem)
  · have hab : (sort2 x y).1 < (sort2 x y).2 := sort2_lt hxy
    have hfne : f (sort2 x y).1 ≠ f (sort2 x y).2 :=
      fun hEq => hab.ne (hf hEq)
    have hcd : (sort2 (f (sort2 x y).1) (f (sort2 x y).2)).1
        < (sort2 (f (sort2 x y).1) (f (sort2 x y).2)).2 := sort2_lt hfne
    have hsxy : s(x, y) = s((sort2 x y).1, (sort2 x y).2) :=
      (sort2_sym2 x y).symm
    have hsf : s(f x, f y) = s(f (sort2 x y).1, f (sort2 x y).2) := by
      rw [← Sym2.map_pair_eq f x y, ← Sym2.map_pair_eq f, hsxy]
    have hs2 : s(f (sort2 x y).1, f (sort2 x y).2)
        = s((sort2 (f (sort2 x y).1) (f (sort2 x y).2)).1,
            (sort2 (f (sort2 x y).1) (f (sort2 x y).2)).2) :=
      (sort2_sym2 _ _).symm
    rw [hsxy, hsf, hs2, ← testBit_iff_mem_edges₂ hab,
      ← testBit_iff_mem_edges₂ hcd, hbits _ _ hab]

/-! ## Encoding graphs as masks

`maskOfGraph₂` inverts `graphOfMask₂`: fold the sorted pairs, setting
the rank bit of each edge. The generic `testBit` description of such
folds, a bound keeping the result inside the mask range, and the
roundtrip give surjectivity of the decoding — every computational graph
is the decoding of a mask, which is how sweeps over masks reach every
graph. -/

/-- Bits of an or-accumulating fold: bit `i` is set iff it was set in
the seed or some listed element satisfies the guard and maps to `i`. -/
lemma testBit_foldl_or {α : Type} (c : α → Prop) [DecidablePred c]
    (g : α → ℕ) (l : List α) (acc : ℕ) (i : ℕ) :
    (l.foldl (fun a t => if c t then a ||| (1 <<< g t) else a) acc).testBit i
      = (acc.testBit i || l.any fun t => decide (c t) && decide (g t = i)) := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    have hshift : ((1 <<< g t : ℕ)).testBit i = decide (g t = i) := by
      rw [Nat.one_shiftLeft]
      rcases eq_or_ne (g t) i with heq | hne
      · rw [heq, Nat.testBit_two_pow_self, decide_eq_true rfl]
      · rw [Nat.testBit_two_pow_of_ne hne, decide_eq_false hne]
    by_cases hc : c t
    · rw [if_pos hc, decide_eq_true hc, Nat.testBit_lor, hshift]
      cases acc.testBit i <;> cases hgt : (decide (g t = i)) <;> simp
    · rw [if_neg hc, decide_eq_false hc]
      simp

/-- An or-accumulating fold over bit positions below `k` stays below
`2 ^ k`. -/
lemma foldl_or_lt_two_pow {α : Type} (c : α → Prop) [DecidablePred c]
    (g : α → ℕ) (l : List α) (acc k : ℕ) (hacc : acc < 2 ^ k)
    (hg : ∀ t ∈ l, g t < k) :
    l.foldl (fun a t => if c t then a ||| (1 <<< g t) else a) acc < 2 ^ k := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons t ts ih =>
    rw [List.foldl_cons]
    have hg' : ∀ t' ∈ ts, g t' < k := fun t' ht' =>
      hg t' (List.mem_cons_of_mem t ht')
    have hacc' : (if c t then acc ||| (1 <<< g t) else acc) < 2 ^ k := by
      by_cases hc : c t
      · rw [if_pos hc]
        refine Nat.or_lt_two_pow hacc ?_
        rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by omega) (hg t List.mem_cons_self)
      · rwa [if_neg hc]
    exact ih _ hacc' hg'

/-- Encode a computational graph as its bitmask. -/
def maskOfGraph₂ {n : ℕ} (G : Sym2Graph n) : ℕ :=
  (finPairs n).foldl (fun acc p =>
    if s(p.1, p.2) ∈ G.edges then
      acc ||| (1 <<< pairIdx n p.1.val p.2.val)
    else acc) 0

/-- Every non-diagonal `Sym2` element is a strictly sorted pair. -/
lemma exists_sorted_pair {α : Type} [LinearOrder α] {e : Sym2 α}
    (he : ¬e.IsDiag) : ∃ a b : α, a < b ∧ e = s(a, b) := by
  induction e using Sym2.ind with | _ x y =>
  have hxy : x ≠ y := by
    intro hEq
    exact he (Sym2.mk_isDiag_iff.mpr hEq)
  exact ⟨(sort2 x y).1, (sort2 x y).2, sort2_lt hxy, (sort2_sym2 x y).symm⟩

/-- Roundtrip: decoding the encoding recovers the graph, given
injectivity of the rank on the listed pairs (kernel-checkable for each
fixed vertex count). -/
lemma graphOfMask₂_maskOfGraph₂ {n : ℕ}
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (G : Sym2Graph n) : graphOfMask₂ n (maskOfGraph₂ G) = G := by
  refine Sym2Graph.ext ?_
  ext e
  rw [mem_graphOfMask₂_edges]
  constructor
  · rintro ⟨a, b, hab, hbit, rfl⟩
    rw [maskOfGraph₂, testBit_foldl_or] at hbit
    rcases Bool.or_eq_true_iff.mp hbit with hz | hany
    · rw [Nat.zero_testBit] at hz
      cases hz
    · obtain ⟨p, hpmem, hcond⟩ := List.any_eq_true.mp hany
      rw [Bool.and_eq_true] at hcond
      have hedge := of_decide_eq_true hcond.1
      have hrank := of_decide_eq_true hcond.2
      have hpeq : p = (a, b) :=
        hinj p hpmem (a, b) (mem_finPairs.mpr hab) hrank
      rw [hpeq] at hedge
      exact hedge
  · intro he
    have hdiag := G.edges_valid e he
    obtain ⟨a, b, hab, rfl⟩ := exists_sorted_pair hdiag
    refine ⟨a, b, hab, ?_, rfl⟩
    rw [maskOfGraph₂, testBit_foldl_or]
    refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
    refine List.any_eq_true.mpr ⟨(a, b), mem_finPairs.mpr hab, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true he, decide_eq_true rfl⟩

/-- Every computational graph is the decoding of a mask below
`2 ^ C(n,2)`, given rank injectivity and the rank bound on the listed
pairs. -/
lemma exists_mask_graphOfMask₂ {n k : ℕ}
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (hbound : ∀ p ∈ finPairs n, pairIdx n p.1.val p.2.val < k)
    (G : Sym2Graph n) : ∃ m, m < 2 ^ k ∧ graphOfMask₂ n m = G :=
  ⟨maskOfGraph₂ G,
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos k) hbound,
    graphOfMask₂_maskOfGraph₂ hinj G⟩

/-! ## The depth-shallow mask sweep

Exhaustive checks over all masks below a power of two, as a binary tree
on the bits: recursion depth is the bit count while the leaves cover the
whole range. The reflection lemma turns the single `Bool` verdict into
the per-mask statement; the gluing lemma lets subrange pieces build in
parallel (in separate declarations, so the kernel releases its
evaluation cache between them) and assemble into one verdict.
Reproduced verbatim from the 3-graph pipeline — representation-generic. -/

/-- Check `P` on every mask `m₀ * 2^d + r` with `r < 2^d`, at recursion
depth `d`. -/
def sweepMasks (P : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, m => P m
  | d + 1, m => sweepMasks P d (2 * m) && sweepMasks P d (2 * m + 1)

/-- Reflection: a true sweep verdict yields `P` on every mask in the
range. -/
lemma sweepMasks_spec (P : ℕ → Bool) (d : ℕ) :
    ∀ m₀, sweepMasks P d m₀ = true →
      ∀ r, r < 2 ^ d → P (m₀ * 2 ^ d + r) = true := by
  induction d with
  | zero =>
    intro m₀ hs r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simpa [sweepMasks] using hs
  | succ d ih =>
    intro m₀ hs r hr
    rw [sweepMasks, Bool.and_eq_true] at hs
    obtain ⟨h₁, h₂⟩ := hs
    have h2p : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
      rw [pow_succ]
      omega
    by_cases hcase : r < 2 ^ d
    · have hh := ih (2 * m₀) h₁ r hcase
      have heq : m₀ * 2 ^ (d + 1) + r = 2 * m₀ * 2 ^ d + r := by
        rw [h2p]
        ring
      rw [heq]
      exact hh
    · have hh := ih (2 * m₀ + 1) h₂ (r - 2 ^ d) (by omega)
      have hexp : (2 * m₀ + 1) * 2 ^ d = 2 * m₀ * 2 ^ d + 2 ^ d := by ring
      have heq : m₀ * 2 ^ (d + 1) + r
          = (2 * m₀ + 1) * 2 ^ d + (r - 2 ^ d) := by
        rw [hexp, h2p]
        have : 2 ^ d ≤ r := not_lt.mp hcase
        have hdistrib : m₀ * (2 ^ d + 2 ^ d) = 2 * m₀ * 2 ^ d := by ring
        omega
      rw [heq]
      exact hh

/-- Glue: a sweep of depth `d + e` follows from the `2^e` sweeps of
depth `d` over the subranges — the shape that lets the pieces build in
parallel and assemble into one verdict. -/
lemma sweepMasks_of_pieces (P : ℕ → Bool) (d : ℕ) :
    ∀ (e m₀ : ℕ), (∀ j, j < 2 ^ e → sweepMasks P d (m₀ * 2 ^ e + j) = true) →
      sweepMasks P (d + e) m₀ = true := by
  intro e
  induction e with
  | zero =>
    intro m₀ h
    simpa using h 0 (by omega)
  | succ e ih =>
    intro m₀ h
    have h2p : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by
      rw [pow_succ]
      omega
    show sweepMasks P (d + e + 1) m₀ = true
    rw [sweepMasks, Bool.and_eq_true]
    constructor
    · refine ih (2 * m₀) fun j hj => ?_
      have heq : 2 * m₀ * 2 ^ e + j = m₀ * 2 ^ (e + 1) + j := by
        rw [h2p]
        ring
      rw [heq]
      exact h j (by omega)
    · refine ih (2 * m₀ + 1) fun j hj => ?_
      have hexp : (2 * m₀ + 1) * 2 ^ e = 2 * m₀ * 2 ^ e + 2 ^ e := by ring
      have heq : (2 * m₀ + 1) * 2 ^ e + j = m₀ * 2 ^ (e + 1) + (2 ^ e + j) := by
        rw [hexp, h2p]
        have hdistrib : m₀ * (2 ^ e + 2 ^ e) = 2 * m₀ * 2 ^ e := by ring
        omega
      rw [heq]
      exact h (2 ^ e + j) (by omega)

/-! ## The generic canonicalization checker

The per-mask verdict of a canonicalization sweep, engineered for the
kernel: a mask passes if its packed witness permutation index is in
range, the image mask reconstructed through the permutation's
precomputed *rank map* is a listed representative, and the per-pair bit
correspondence holds — `P` bit comparisons, no `Finset`, no `Fin`
arithmetic in the hot path.

Packing conventions (fixed once, adequate for every `n ≤ 8`): a
permutation stores 3 bits per vertex (`pv`); a rank map stores 5 bits
per pair position (positions are `< C(n,2) ≤ 28 < 32`). The vertex-level
meaning of a packed permutation is recovered by the one-time decidable
check `permConsistent`; combining it with the scan verdict,
`leafParts_eqv` turns a true leaf into a flag equivalence with the
listed representative through `graphOfMask₂_eqv_of_bits`. -/

/-- Entry `i` of a packed permutation (three bits per vertex). -/
def pv (w i : ℕ) : ℕ := (w >>> (3 * i)) &&& 7

/-- The packed permutation as a vertex map. -/
def permFn (n : ℕ) [NeZero n] (w : ℕ) : Fin n → Fin n := fun i =>
  ⟨pv w i.val % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- Image-mask reconstruction through a rank map: transport each present
rank bit (`P` pair positions, 5 bits per entry). -/
def rankApply (P r m : ℕ) : ℕ :=
  (List.range P).foldl (fun acc rk =>
    if m.testBit rk then acc ||| (1 <<< ((r >>> (5 * rk)) &&& 31))
    else acc) 0

/-- The per-pair bit correspondence along a rank map. -/
def scanOK (P m r h : ℕ) : Bool :=
  (List.range P).all fun rk =>
    m.testBit rk == h.testBit ((r >>> (5 * rk)) &&& 31)

/-- Consistency of one packed permutation with its rank map: the vertex
map is injective, and each rank-map entry is the rank of the sorted
image pair. -/
def permConsistent (n : ℕ) [NeZero n] (w r : ℕ) : Bool :=
  decide (Function.Injective (permFn n w))
    && decide (∀ a b : Fin n, a < b →
        (r >>> (5 * pairIdx n a.val b.val)) &&& 31
          = pairIdx n (sort2 (permFn n w a) (permFn n w b)).1.val
              (sort2 (permFn n w a) (permFn n w b)).2.val)

/-- Abstract reflection: consistency of a packed permutation with its
rank map plus the scan verdict give the flag equivalence — stated over
plain variables so no table literal is ever unfolded during elaboration.
`hP` bounds the pair ranks by the scanned position count (kernel-checked
per `n`). -/
lemma leafParts_eqv {n : ℕ} [NeZero n] {P m w r h : ℕ}
    (hP : ∀ a b : Fin n, a < b → pairIdx n a.val b.val < P)
    (hcons : permConsistent n w r = true)
    (hscan : scanOK P m r h = true) :
    graphOfMask₂ n m ∼sf graphOfMask₂ n h := by
  unfold permConsistent at hcons
  rw [Bool.and_eq_true] at hcons
  have hinj := of_decide_eq_true hcons.1
  have hcons' := of_decide_eq_true hcons.2
  unfold scanOK at hscan
  have hscan' := List.all_eq_true.mp hscan
  refine graphOfMask₂_eqv_of_bits hinj ?_
  intro a b hab
  have hs := hscan' _ (List.mem_range.mpr (hP a b hab))
  simp only [beq_iff_eq] at hs
  rw [hs, hcons' a b hab]

end FlagAlgebras.Compute.BitMask
