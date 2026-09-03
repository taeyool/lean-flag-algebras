import LeanFlagAlgebras.BitMask.RCanon2_6Data
import LeanFlagAlgebras.BitMask.RootedCanon

/-! # The `(2, 6)` rooted canonicalization checker

Per-mask verdict of the rooted sweep for six-vertex flags with two
roots (`K3freeC6`'s typed host layer): 2^15 masks, 24 root-fixing
permutations, 1992 representatives. The sweep itself is split into
four subrange files (`RCanon2_6Sweep0`–`RCanon2_6Sweep3`, so they
build in parallel) and assembled in `RCanon2_6`. -/

namespace FlagAlgebras.Compute.BitMask.RCanon2_6

open FlagAlgebras.Compute.BitMask

/-- The packed vertex map of the root-fixing permutation `i`. -/
def getPerm (i : ℕ) : ℕ := rperms2_6.getD i 0

/-- The packed rank map of the root-fixing permutation `i`. -/
def getRank (i : ℕ) : ℕ := rrankMaps2_6.getD i 0

/-- The witness permutation index of a mask (5 bits per mask, 1024
masks per chunk). -/
def pidx (x : ℕ) : ℕ :=
  ((rwChunks2_6.getD (x >>> 10) 0) >>> (5 * (x &&& 1023))) &&& 31

/-- The rooted canonical image of a mask. -/
def canonImage (x : ℕ) : ℕ := rankApply 15 (getRank (pidx x)) x

/-- Per-mask verdict: witness index in range, canonical image listed,
per-pair bit correspondence holds. -/
def leaf (x : ℕ) : Bool :=
  decide (pidx x < 24)
    && decide (canonImage x ∈ rreps2_6)
    && scanOK 15 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 24).all (fun i =>
    permConsistent 6 (getPerm i) (getRank i)
      && permFixesRoots 2 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 24) :
    permConsistent 6 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 2 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 6, a < b → pairIdx 6 a.val b.val < 15 := by
  decide

end FlagAlgebras.Compute.BitMask.RCanon2_6
