import LeanFlagAlgebras.BitMask.RCanon1_2Data
import LeanFlagAlgebras.BitMask.RCanon1_3Data
import LeanFlagAlgebras.BitMask.RCanon2_3Data
import LeanFlagAlgebras.BitMask.RCanon2_4Data
import LeanFlagAlgebras.BitMask.RCanon3_4Data
import LeanFlagAlgebras.BitMask.RCanon1_5Data
import LeanFlagAlgebras.BitMask.RCanon3_5Data
import LeanFlagAlgebras.BitMask.RootedMask

/-! # Rooted canonicalization sweeps

Kernel-checked canonicalization of σ-typed flag masks: for each root
count / vertex count combination `(k, m)`, every mask is matched to a
listed representative by a **root-fixing** witness permutation, so the
decoded flags are equivalent *as labeled flags* (`rleafParts_eqv`). One
sweep per `(k, m)` serves every type graph `σ` — the root-fixing group
preserves the root bits, so `RootsMatch` transfers along the witness.

Instantiated here for the combinations the paper examples use
(`(1,2)`, `(1,3)`, `(2,3)`, `(2,4)`, `(3,4)`, `(1,5)`, `(3,5)`); the
`(2,6)` sweep for `K3freeC6`'s size-6 flags lives in its own split
files (`RCanon2_6Checker` / `RCanon2_6Sweep0`–`3` / `RCanon2_6`). -/

namespace FlagAlgebras.Compute.BitMask

/-! ## Root-fixing checker pieces -/

/-- The packed permutation fixes positions `0 … k−1` pointwise. -/
def permFixesRoots (k w : ℕ) : Bool :=
  (List.range k).all fun i => pv w i == i

/-- Reflection: a checked permutation fixes the root embedding. -/
lemma permFn_fixes_of_permFixesRoots {k m : ℕ} [NeZero m] {w : ℕ}
    (hkm : k ≤ m) (h : permFixesRoots k w = true) (i : Fin k) :
    permFn m w (Fin.castLE hkm i) = Fin.castLE hkm i := by
  have hb := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hv : pv w i.val = i.val := beq_iff_eq.mp hb
  refine Fin.ext ?_
  show pv w (Fin.castLE hkm i).val % m = (Fin.castLE hkm i).val
  rw [show (Fin.castLE hkm i).val = i.val from rfl, hv]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hkm)

/-- Sorting an already-sorted pair is the identity. -/
lemma sort2_of_le {α : Type} [LinearOrder α] {a b : α} (hab : a ≤ b) :
    sort2 a b = (a, b) := by
  unfold sort2
  rw [if_pos hab]

/-- **Rooted leaf reflection.** Consistency of a root-fixing packed
permutation with its rank map plus the scan verdict transfer
`RootsMatch` and give the **labeled** flag equivalence of the decoded
flags — for every type graph `σ` at once. -/
theorem rleafParts_eqv {kr m P w r x y : ℕ} [NeZero m]
    {σ : Sym2FlagType kr} (hkm : kr ≤ m)
    (hP : ∀ a b : Fin m, a < b → pairIdx m a.val b.val < P)
    (hcons : permConsistent m w r = true)
    (hfix : permFixesRoots kr w = true)
    (hscan : scanOK P x r y = true)
    (hx : RootsMatch σ m x) :
    ∃ hy : RootsMatch σ m y,
      labeledGraphOfMask σ m hkm x hx
        ∼sf labeledGraphOfMask σ m hkm y hy := by
  unfold permConsistent at hcons
  rw [Bool.and_eq_true] at hcons
  have hinj := of_decide_eq_true hcons.1
  have hcons' := of_decide_eq_true hcons.2
  unfold scanOK at hscan
  have hscan' := List.all_eq_true.mp hscan
  have hbits : ∀ a b : Fin m, a < b →
      x.testBit (pairIdx m a.val b.val)
        = y.testBit (pairIdx m (sort2 (permFn m w a) (permFn m w b)).1.val
            (sort2 (permFn m w a) (permFn m w b)).2.val) := by
    intro a b hab
    have hs := hscan' _ (List.mem_range.mpr (hP a b hab))
    simp only [beq_iff_eq] at hs
    rw [hs, hcons' a b hab]
  have hfix' := permFn_fixes_of_permFixesRoots (m := m) hkm hfix
  have hy : RootsMatch σ m y := by
    intro i j hij
    have hab : Fin.castLE hkm i < Fin.castLE hkm j := hij
    have hb := hbits _ _ hab
    rw [hfix' i, hfix' j, sort2_of_le (le_of_lt hab)] at hb
    rw [show pairIdx m i.val j.val
        = pairIdx m (Fin.castLE hkm i).val (Fin.castLE hkm j).val from rfl,
      ← hb]
    exact hx i j hij
  exact ⟨hy, labeledGraphOfMask_eqv_of_bits hkm hinj hfix' hx hy hbits⟩

end FlagAlgebras.Compute.BitMask

/-! ## The `(1, 3)` sweep (three-vertex flags with one root) -/

namespace FlagAlgebras.Compute.BitMask.RCanon1_3

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms1_3.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps1_3.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks1_3.getD 0 0) >>> (3 * x)) &&& 7
def canonImage (x : ℕ) : ℕ := rankApply 3 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 2)
    && decide (canonImage x ∈ rreps1_3)
    && scanOK 3 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 2).all (fun i =>
    permConsistent 3 (getPerm i) (getRank i)
      && permFixesRoots 1 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 2) :
    permConsistent 3 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 1 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 3, a < b → pairIdx 3 a.val b.val < 3 := by
  decide

set_option maxRecDepth 8192 in
lemma sweep : sweepMasks leaf 3 0 = true := by decide +kernel

/-- Reflection: every mask's canonical image is listed, and for every
type graph the decoded labeled flags are equivalent. -/
theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 3) {σ : Sym2FlagType 1}
    (hx : RootsMatch σ 3 x) :
    canonImage x ∈ rreps1_3
      ∧ ∃ hy : RootsMatch σ 3 (canonImage x),
          labeledGraphOfMask σ 3 (by omega) x hx
            ∼sf labeledGraphOfMask σ 3 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 3 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon1_3

/-! ## The `(2, 4)` sweep (four-vertex flags with two roots) -/

namespace FlagAlgebras.Compute.BitMask.RCanon2_4

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms2_4.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps2_4.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks2_4.getD 0 0) >>> (3 * x)) &&& 7
def canonImage (x : ℕ) : ℕ := rankApply 6 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 2)
    && decide (canonImage x ∈ rreps2_4)
    && scanOK 6 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 2).all (fun i =>
    permConsistent 4 (getPerm i) (getRank i)
      && permFixesRoots 2 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 2) :
    permConsistent 4 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 2 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 4, a < b → pairIdx 4 a.val b.val < 6 := by
  decide

set_option maxRecDepth 65536 in
lemma sweep : sweepMasks leaf 6 0 = true := by decide +kernel

/-- Reflection: every mask's canonical image is listed, and for every
type graph the decoded labeled flags are equivalent. -/
theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 6) {σ : Sym2FlagType 2}
    (hx : RootsMatch σ 4 x) :
    canonImage x ∈ rreps2_4
      ∧ ∃ hy : RootsMatch σ 4 (canonImage x),
          labeledGraphOfMask σ 4 (by omega) x hx
            ∼sf labeledGraphOfMask σ 4 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 6 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon2_4

/-! ## The `(1, 2)` and `(2, 3)` sweeps (trivial groups)

With only the identity as root-fixing permutation every mask is its own
representative, but the uniform interface keeps downstream code
size-generic. -/

namespace FlagAlgebras.Compute.BitMask.RCanon1_2

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms1_2.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps1_2.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks1_2.getD 0 0) >>> (3 * x)) &&& 7
def canonImage (x : ℕ) : ℕ := rankApply 1 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 1)
    && decide (canonImage x ∈ rreps1_2)
    && scanOK 1 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 1).all (fun i =>
    permConsistent 2 (getPerm i) (getRank i)
      && permFixesRoots 1 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 1) :
    permConsistent 2 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 1 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 2, a < b → pairIdx 2 a.val b.val < 1 := by
  decide

set_option maxRecDepth 8192 in
lemma sweep : sweepMasks leaf 1 0 = true := by decide +kernel

theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 1) {σ : Sym2FlagType 1}
    (hx : RootsMatch σ 2 x) :
    canonImage x ∈ rreps1_2
      ∧ ∃ hy : RootsMatch σ 2 (canonImage x),
          labeledGraphOfMask σ 2 (by omega) x hx
            ∼sf labeledGraphOfMask σ 2 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 1 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon1_2

namespace FlagAlgebras.Compute.BitMask.RCanon2_3

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms2_3.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps2_3.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks2_3.getD 0 0) >>> (3 * x)) &&& 7
def canonImage (x : ℕ) : ℕ := rankApply 3 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 1)
    && decide (canonImage x ∈ rreps2_3)
    && scanOK 3 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 1).all (fun i =>
    permConsistent 3 (getPerm i) (getRank i)
      && permFixesRoots 2 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 1) :
    permConsistent 3 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 2 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 3, a < b → pairIdx 3 a.val b.val < 3 := by
  decide

set_option maxRecDepth 8192 in
lemma sweep : sweepMasks leaf 3 0 = true := by decide +kernel

theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 3) {σ : Sym2FlagType 2}
    (hx : RootsMatch σ 3 x) :
    canonImage x ∈ rreps2_3
      ∧ ∃ hy : RootsMatch σ 3 (canonImage x),
          labeledGraphOfMask σ 3 (by omega) x hx
            ∼sf labeledGraphOfMask σ 3 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 3 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon2_3

namespace FlagAlgebras.Compute.BitMask.RCanon3_4

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms3_4.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps3_4.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks3_4.getD 0 0) >>> (3 * x)) &&& 7
def canonImage (x : ℕ) : ℕ := rankApply 6 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 1)
    && decide (canonImage x ∈ rreps3_4)
    && scanOK 6 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 1).all (fun i =>
    permConsistent 4 (getPerm i) (getRank i)
      && permFixesRoots 3 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 1) :
    permConsistent 4 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 3 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 4, a < b → pairIdx 4 a.val b.val < 6 := by
  decide

set_option maxRecDepth 65536 in
lemma sweep : sweepMasks leaf 6 0 = true := by decide +kernel

theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 6) {σ : Sym2FlagType 3}
    (hx : RootsMatch σ 4 x) :
    canonImage x ∈ rreps3_4
      ∧ ∃ hy : RootsMatch σ 4 (canonImage x),
          labeledGraphOfMask σ 4 (by omega) x hx
            ∼sf labeledGraphOfMask σ 4 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 6 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon3_4

/-! ## The `(1, 5)` sweep (five-vertex flags with one root) -/

namespace FlagAlgebras.Compute.BitMask.RCanon1_5

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms1_5.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps1_5.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks1_5.getD 0 0) >>> (5 * x)) &&& 31
def canonImage (x : ℕ) : ℕ := rankApply 10 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 24)
    && decide (canonImage x ∈ rreps1_5)
    && scanOK 10 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 24).all (fun i =>
    permConsistent 5 (getPerm i) (getRank i)
      && permFixesRoots 1 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 24) :
    permConsistent 5 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 1 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 5, a < b → pairIdx 5 a.val b.val < 10 := by
  decide

set_option maxRecDepth 65536 in
lemma sweep : sweepMasks leaf 10 0 = true := by decide +kernel

/-- Reflection: every mask's canonical image is listed, and for every
type graph the decoded labeled flags are equivalent. -/
theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 10) {σ : Sym2FlagType 1}
    (hx : RootsMatch σ 5 x) :
    canonImage x ∈ rreps1_5
      ∧ ∃ hy : RootsMatch σ 5 (canonImage x),
          labeledGraphOfMask σ 5 (by omega) x hx
            ∼sf labeledGraphOfMask σ 5 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 10 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon1_5

/-! ## The `(3, 5)` sweep (five-vertex flags with three roots) -/

namespace FlagAlgebras.Compute.BitMask.RCanon3_5

open FlagAlgebras.Compute.BitMask

def getPerm (i : ℕ) : ℕ := rperms3_5.getD i 0
def getRank (i : ℕ) : ℕ := rrankMaps3_5.getD i 0
def pidx (x : ℕ) : ℕ := ((rwChunks3_5.getD 0 0) >>> (3 * x)) &&& 7
def canonImage (x : ℕ) : ℕ := rankApply 10 (getRank (pidx x)) x

def leaf (x : ℕ) : Bool :=
  decide (pidx x < 2)
    && decide (canonImage x ∈ rreps3_5)
    && scanOK 10 x (getRank (pidx x)) (canonImage x)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 2).all (fun i =>
    permConsistent 5 (getPerm i) (getRank i)
      && permFixesRoots 3 (getPerm i)) = true := by decide +kernel

lemma consistent_of_lt {i : ℕ} (hi : i < 2) :
    permConsistent 5 (getPerm i) (getRank i) = true
      ∧ permFixesRoots 3 (getPerm i) = true := by
  have h := List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)
  rwa [Bool.and_eq_true] at h

lemma pairIdx_lt : ∀ a b : Fin 5, a < b → pairIdx 5 a.val b.val < 10 := by
  decide

set_option maxRecDepth 65536 in
lemma sweep : sweepMasks leaf 10 0 = true := by decide +kernel

/-- Reflection: every mask's canonical image is listed, and for every
type graph the decoded labeled flags are equivalent. -/
theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 10) {σ : Sym2FlagType 3}
    (hx : RootsMatch σ 5 x) :
    canonImage x ∈ rreps3_5
      ∧ ∃ hy : RootsMatch σ 5 (canonImage x),
          labeledGraphOfMask σ 5 (by omega) x hx
            ∼sf labeledGraphOfMask σ 5 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 10 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon3_5
