import LeanFlagAlgebras.BitMask.Canon5Data

/-! # The five-vertex canonicalization sweep (pilot)

Kernel-checked completeness for 2-graphs on five vertices: **every**
`Sym2Graph 5` is flag-equivalent (`∼sf`) to the decoding of one of the
34 listed representative masks. The sweep visits all `2^10` masks by
kernel reduction (`decide +kernel`) — no `native_decide`, so the result
adds no axioms beyond the classical trio.

Forbid-agnostic by design: any forbidden-subgraph condition becomes a
filter over the 34 representatives downstream, so this one sweep serves
every 5-vertex problem.

Pipeline shape (mirroring the order-7 tetrahedron pipeline's six-vertex
sweep): a one-time table validation (`perm5Consistent_of_lt`) recovers
the vertex-level meaning of the 120 packed permutations; the per-mask
verdict `leaf5` is pure bit tests; `sweepMasks` covers the range;
`leafParts_eqv` transports each verdict to a `∼sf` statement. -/

namespace FlagAlgebras.Compute.BitMask.Canon5

open FlagAlgebras.Compute.BitMask

/-- The packed vertex map of the permutation with index `i`. -/
def getPerm (i : ℕ) : ℕ := perms5.getD i 0

/-- The packed rank map of the permutation with index `i`. -/
def getRank (i : ℕ) : ℕ := rankMaps5.getD i 0

/-- The witness permutation index of a mask, from the packed chunk
(7 bits per mask). -/
def pidx (m : ℕ) : ℕ := ((wChunks5.getD 0 0) >>> (7 * m)) &&& 127

/-- The canonical image of a mask, reconstructed through its witness
permutation's rank map. -/
def canonImage (m : ℕ) : ℕ := rankApply 10 (getRank (pidx m)) m

/-- Per-mask verdict of the completeness sweep: witness index in range,
canonical image listed, and the per-pair bit correspondence holds. -/
def leaf5 (m : ℕ) : Bool :=
  decide (pidx m < 120)
    && decide (canonImage m ∈ reps5)
    && scanOK 10 m (getRank (pidx m)) (canonImage m)

/-! ## One-time table validation -/

set_option maxRecDepth 65536 in
/-- Each of the 120 packed permutations is consistent with its rank
map (kernel-checked). -/
lemma rows5Consistent : (List.range 120).all
    (fun i => permConsistent 5 (getPerm i) (getRank i)) = true := by
  decide +kernel

/-- Indexed form of the table validation. -/
lemma perm5Consistent_of_lt {i : ℕ} (hi : i < 120) :
    permConsistent 5 (getPerm i) (getRank i) = true :=
  List.all_eq_true.mp rows5Consistent i (List.mem_range.mpr hi)

/-- The rank bound in the quantifier shape the reflection consumes. -/
lemma pairIdx5_lt : ∀ a b : Fin 5, a < b → pairIdx 5 a.val b.val < 10 := by
  decide

/-! ## The sweep -/

set_option maxRecDepth 65536 in
/-- The completeness sweep: `leaf5` holds on all `2^10` masks
(kernel-checked). -/
lemma sweep5 : sweepMasks leaf5 10 0 = true := by decide +kernel

/-- Reflection of one leaf: every mask's canonical image is a listed
representative flag-equivalent to it. -/
theorem leaf5_reflect {m : ℕ} (hm : m < 2 ^ 10) :
    canonImage m ∈ reps5
      ∧ graphOfMask₂ 5 m ∼sf graphOfMask₂ 5 (canonImage m) := by
  have hleaf : leaf5 m = true := by
    have h := sweepMasks_spec leaf5 10 0 sweep5 m hm
    rwa [zero_mul, zero_add] at h
  unfold leaf5 at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  exact ⟨of_decide_eq_true hmem,
    leafParts_eqv pairIdx5_lt
      (perm5Consistent_of_lt (of_decide_eq_true hpidx)) hscan⟩

/-! ## Completeness for arbitrary `Sym2Graph 5` -/

set_option maxRecDepth 8192 in
/-- Rank injectivity on the listed five-vertex pairs. -/
lemma finPairs5_rank_inj : ∀ p₁ ∈ finPairs 5, ∀ p₂ ∈ finPairs 5,
    pairIdx 5 p₁.1.val p₁.2.val = pairIdx 5 p₂.1.val p₂.2.val → p₁ = p₂ := by
  decide

set_option maxRecDepth 8192 in
/-- Rank bound on the listed five-vertex pairs. -/
lemma finPairs5_rank_lt :
    ∀ p ∈ finPairs 5, pairIdx 5 p.1.val p.2.val < 10 := by decide

/-- **Completeness.** Every computable 5-vertex simple graph is
flag-equivalent to the decoding of one of the 34 listed representative
masks. Kernel-checked end to end — no `native_decide`. -/
theorem canon5_complete (G : Sym2Graph 5) :
    ∃ h ∈ reps5, G ∼sf graphOfMask₂ 5 h := by
  obtain ⟨m, hm, hG⟩ :=
    exists_mask_graphOfMask₂ finPairs5_rank_inj finPairs5_rank_lt G
  obtain ⟨hmem, heqv⟩ := leaf5_reflect hm
  exact ⟨canonImage m, hmem, hG ▸ heqv⟩

/-- There are 34 representatives — the number of isomorphism classes of
graphs on five vertices. -/
example : reps5.length = 34 := by decide

end FlagAlgebras.Compute.BitMask.Canon5
