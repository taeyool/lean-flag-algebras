import LeanFlagAlgebras.BitMask.Canon7Data

/-! # The seven-vertex canonicalization checker

The per-mask verdict of the 7-vertex completeness sweep (`2^21` masks,
5040 permutations, 1044 representatives) and its one-time table
validations. Compared to the six-vertex checker, two lookups are
re-engineered for the 64× larger range: the witness entry carries the
*representative index* alongside the permutation index (so the leaf
compares against a packed representative in O(1) instead of scanning a
1044-element list), and the permutation/rank tables are stored in rows
of 30 (so a lookup costs ≤ 200 list steps instead of ≤ 5040).

The sweep itself is split into 64 subrange files
(`Canon7Sweep00`–`Canon7Sweep63`), glued in `Canon7Glue`/`Canon7`. -/

namespace FlagAlgebras.Compute.BitMask.Canon7

open FlagAlgebras.Compute.BitMask

/-- The packed vertex map of the permutation with index `i`. -/
def getPerm (i : ℕ) : ℕ := (perms7.getD (i / 30) []).getD (i % 30) 0

/-- The packed rank map of the permutation with index `i`. -/
def getRank (i : ℕ) : ℕ := (rankMaps7.getD (i / 30) []).getD (i % 30) 0

/-- The 24-bit witness entry of a mask (permutation index in the low 13
bits, representative index above; 1024 masks per chunk, 32 chunks per
row). -/
def widx (m : ℕ) : ℕ :=
  (((wChunks7.getD (m >>> 15) []).getD ((m >>> 10) &&& 31) 0)
    >>> (24 * (m &&& 1023))) &&& 16777215

/-- The witness permutation index of a mask. -/
def pidx (m : ℕ) : ℕ := widx m &&& 8191

/-- The witness representative index of a mask. -/
def ridx (m : ℕ) : ℕ := widx m >>> 13

/-- The representative with index `i`, read from the packed literal. -/
def repAt (i : ℕ) : ℕ := (repsPacked7 >>> (21 * i)) &&& 2097151

/-- The canonical image of a mask, reconstructed through its witness
permutation's rank map. -/
def canonImage (m : ℕ) : ℕ := rankApply 21 (getRank (pidx m)) m

/-- Per-mask verdict of the completeness sweep: both witness indices in
range, the canonical image is the indexed representative, and the
per-pair bit correspondence holds. -/
def leaf7 (m : ℕ) : Bool :=
  decide (pidx m < 5040) && decide (ridx m < 1044)
    && (repAt (ridx m) == canonImage m)
    && scanOK 21 m (getRank (pidx m)) (canonImage m)

/-! ## One-time table validations -/

set_option maxRecDepth 8192 in
lemma reps7_length : reps7.length = 1044 := by decide

set_option maxRecDepth 65536 in
/-- The packed representatives agree with the list (kernel-checked). -/
lemma repsPacked7_all : (List.range 1044).all
    (fun i => repAt i == reps7.getD i 0) = true := by decide +kernel

/-- Indexed form: `repAt` reads the listed representative. -/
lemma repAt_eq_getD {i : ℕ} (hi : i < 1044) : repAt i = reps7.getD i 0 := by
  have h := List.all_eq_true.mp repsPacked7_all i (List.mem_range.mpr hi)
  simpa [beq_iff_eq] using h

/-- An in-range `repAt` value is a listed representative. -/
lemma repAt_mem {i : ℕ} (hi : i < 1044) : repAt i ∈ reps7 := by
  rw [repAt_eq_getD hi]
  have hlen : i < reps7.length := by rw [reps7_length]; exact hi
  rw [List.getD_eq_getElem reps7 0 hlen]
  exact List.getElem_mem hlen

/-- One row (30 permutations) of the table validation. -/
def rowConsistent (r : ℕ) : Bool :=
  (List.range 30).all fun i =>
    permConsistent 7 (getPerm (30 * r + i)) (getRank (30 * r + i))

set_option maxRecDepth 65536 in
private lemma rows_0 : (List.range 28).all
    (fun q => rowConsistent (28 * 0 + q)) = true := by decide +kernel
set_option maxRecDepth 65536 in
private lemma rows_1 : (List.range 28).all
    (fun q => rowConsistent (28 * 1 + q)) = true := by decide +kernel
set_option maxRecDepth 65536 in
private lemma rows_2 : (List.range 28).all
    (fun q => rowConsistent (28 * 2 + q)) = true := by decide +kernel
set_option maxRecDepth 65536 in
private lemma rows_3 : (List.range 28).all
    (fun q => rowConsistent (28 * 3 + q)) = true := by decide +kernel
set_option maxRecDepth 65536 in
private lemma rows_4 : (List.range 28).all
    (fun q => rowConsistent (28 * 4 + q)) = true := by decide +kernel
set_option maxRecDepth 65536 in
private lemma rows_5 : (List.range 28).all
    (fun q => rowConsistent (28 * 5 + q)) = true := by decide +kernel

/-- Every row of the table validation holds. -/
lemma rowConsistent_of_lt {r : ℕ} (hr : r < 168) : rowConsistent r = true := by
  have hgroup : (List.range 28).all
      (fun q => rowConsistent (28 * (r / 28) + q)) = true := by
    have h6 : r / 28 < 6 := by omega
    match hq : r / 28, h6 with
    | 0, _ => exact rows_0
    | 1, _ => exact rows_1
    | 2, _ => exact rows_2
    | 3, _ => exact rows_3
    | 4, _ => exact rows_4
    | 5, _ => exact rows_5
    | q + 6, h => exact absurd h (by omega)
  have hmem := List.all_eq_true.mp hgroup (r % 28)
    (List.mem_range.mpr (by omega))
  rwa [Nat.div_add_mod] at hmem

/-- Each of the 5040 packed permutations is consistent with its rank
map. -/
lemma perm7Consistent_of_lt {i : ℕ} (hi : i < 5040) :
    permConsistent 7 (getPerm i) (getRank i) = true := by
  have hrow := rowConsistent_of_lt (r := i / 30) (by omega)
  have hmem := List.all_eq_true.mp hrow (i % 30)
    (List.mem_range.mpr (by omega))
  rwa [Nat.div_add_mod] at hmem

/-- The rank bound in the quantifier shape the reflection consumes. -/
lemma pairIdx7_lt : ∀ a b : Fin 7, a < b → pairIdx 7 a.val b.val < 21 := by
  decide

set_option maxRecDepth 8192 in
/-- Rank injectivity on the listed seven-vertex pairs. -/
lemma finPairs7_rank_inj : ∀ p₁ ∈ finPairs 7, ∀ p₂ ∈ finPairs 7,
    pairIdx 7 p₁.1.val p₁.2.val = pairIdx 7 p₂.1.val p₂.2.val → p₁ = p₂ := by
  decide

set_option maxRecDepth 8192 in
/-- Rank bound on the listed seven-vertex pairs. -/
lemma finPairs7_rank_lt :
    ∀ p ∈ finPairs 7, pairIdx 7 p.1.val p.2.val < 21 := by decide

end FlagAlgebras.Compute.BitMask.Canon7
