import LeanFlagAlgebras.BitMask.Canon6Data

/-! # The six-vertex canonicalization checker

The per-mask verdict of the 6-vertex completeness sweep and its one-time
table validation. The sweep itself is split into four subrange files
(`Canon6Sweep0`–`Canon6Sweep3`, so they build in parallel) and assembled
in `Canon6`. -/

namespace FlagAlgebras.Compute.BitMask.Canon6

open FlagAlgebras.Compute.BitMask

/-- The packed vertex map of the permutation with index `i`. -/
def getPerm (i : ℕ) : ℕ := perms6.getD i 0

/-- The packed rank map of the permutation with index `i`. -/
def getRank (i : ℕ) : ℕ := rankMaps6.getD i 0

/-- The witness permutation index of a mask, from the packed chunks
(10 bits per mask, 1024 masks per chunk). -/
def pidx (m : ℕ) : ℕ :=
  ((wChunks6.getD (m >>> 10) 0) >>> (10 * (m &&& 1023))) &&& 1023

/-- The canonical image of a mask, reconstructed through its witness
permutation's rank map. -/
def canonImage (m : ℕ) : ℕ := rankApply 15 (getRank (pidx m)) m

/-- Per-mask verdict of the completeness sweep: witness index in range,
canonical image listed, and the per-pair bit correspondence holds. -/
def leaf6 (m : ℕ) : Bool :=
  decide (pidx m < 720)
    && decide (canonImage m ∈ reps6)
    && scanOK 15 m (getRank (pidx m)) (canonImage m)

/-! ## One-time table validation -/

/-- One row (30 permutations) of the table validation. -/
def rowConsistent (r : ℕ) : Bool :=
  (List.range 30).all fun i =>
    permConsistent 6 (getPerm (30 * r + i)) (getRank (30 * r + i))

set_option maxRecDepth 65536 in
lemma rowConsistent_all : (List.range 24).all rowConsistent = true := by
  decide +kernel

/-- Each of the 720 packed permutations is consistent with its rank
map. -/
lemma perm6Consistent_of_lt {i : ℕ} (hi : i < 720) :
    permConsistent 6 (getPerm i) (getRank i) = true := by
  have hrow : rowConsistent (i / 30) = true :=
    List.all_eq_true.mp rowConsistent_all (i / 30)
      (List.mem_range.mpr (by omega))
  have hmem := List.all_eq_true.mp hrow (i % 30)
    (List.mem_range.mpr (by omega))
  rwa [Nat.div_add_mod] at hmem

/-- The rank bound in the quantifier shape the reflection consumes. -/
lemma pairIdx6_lt : ∀ a b : Fin 6, a < b → pairIdx 6 a.val b.val < 15 := by
  decide

set_option maxRecDepth 8192 in
/-- Rank injectivity on the listed six-vertex pairs. -/
lemma finPairs6_rank_inj : ∀ p₁ ∈ finPairs 6, ∀ p₂ ∈ finPairs 6,
    pairIdx 6 p₁.1.val p₁.2.val = pairIdx 6 p₂.1.val p₂.2.val → p₁ = p₂ := by
  decide

set_option maxRecDepth 8192 in
/-- Rank bound on the listed six-vertex pairs. -/
lemma finPairs6_rank_lt :
    ∀ p ∈ finPairs 6, pairIdx 6 p.1.val p.2.val < 15 := by decide

end FlagAlgebras.Compute.BitMask.Canon6
