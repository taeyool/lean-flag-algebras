import LeanFlagAlgebras.BitMask.Canon7Glue
import LeanFlagAlgebras.BitMask.MaskBridge

/-! # The seven-vertex canonicalization sweep

Kernel-checked completeness for 2-graphs on seven vertices: **every**
`Sym2Graph 7` is flag-equivalent (`∼sf`) to the decoding of one of the
1044 listed representative masks. The sweep visits all `2^21` masks by
kernel reduction (`decide +kernel`, 64 subrange files) — no
`native_decide`.

This is the scale the old enumeration pipeline could not reach in the
kernel (its iso-dedup generation took ~10 minutes *natively* per
problem); here the one-time sweep serves every 7-vertex problem, and
each forbid is a filter over the 1044 representatives. The bridge
section instantiates the generic sweep-to-pipeline lemmas, including
kernel-only K₃-free completeness (107 classes). -/

namespace FlagAlgebras.Compute.BitMask.Canon7

open FlagAlgebras.Compute.BitMask

/-- Reflection of one leaf: every mask's canonical image is a listed
representative flag-equivalent to it. -/
theorem leaf7_reflect {m : ℕ} (hm : m < 2 ^ 21) :
    canonImage m ∈ reps7
      ∧ graphOfMask₂ 7 m ∼sf graphOfMask₂ 7 (canonImage m) := by
  have hleaf : leaf7 m = true := by
    have h := sweepMasks_spec leaf7 21 0 sweep7 m hm
    rwa [zero_mul, zero_add] at h
  unfold leaf7 at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨⟨hp, hr⟩, hrep⟩, hscan⟩ := hleaf
  have hrep' : repAt (ridx m) = canonImage m := by
    simpa [beq_iff_eq] using hrep
  refine ⟨?_, leafParts_eqv pairIdx7_lt
    (perm7Consistent_of_lt (of_decide_eq_true hp)) hscan⟩
  rw [← hrep']
  exact repAt_mem (of_decide_eq_true hr)

/-- **Completeness.** Every computable 7-vertex simple graph is
flag-equivalent to the decoding of one of the 1044 listed
representative masks. Kernel-checked end to end — no
`native_decide`. -/
theorem canon7_complete (G : Sym2Graph 7) :
    ∃ h ∈ reps7, G ∼sf graphOfMask₂ 7 h := by
  obtain ⟨m, hm, hG⟩ :=
    exists_mask_graphOfMask₂ finPairs7_rank_inj finPairs7_rank_lt G
  obtain ⟨hmem, heqv⟩ := leaf7_reflect hm
  exact ⟨canonImage m, hmem, hG ▸ heqv⟩

/-! ## Bridges into the forbid-free pipeline -/

/-- All 7-vertex empty-typed flags, as the 1044 representative
decodings. -/
theorem maskRepFlags7_toFinset_eq_univ :
    (maskRepFlags reps7 7).toFinset = Finset.univ :=
  maskRepFlags_toFinset_eq_univ canon7_complete

/-- The `F`-free 7-vertex flags, for any forbidden `F` — kernel-only
replacement for the pruned generator's completeness at `n = 7`. -/
theorem maskFreeFlags7_toFinset_eq {m : ℕ} (F : Sym2Graph m) :
    (maskFreeFlags F reps7 7).toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) :=
  maskFreeFlags_toFinset_eq F canon7_complete

/-- Canonicalize a 7-vertex graph: encode it and look up its canonical
representative through the witness tables. -/
def canonOf (G : Sym2Graph 7) : ℕ := canonImage (maskOfGraph₂ G)

/-- `canonOf` lands in the representative list and preserves the flag
class — the sweep fact the command-facing wiring consumes. -/
theorem canonOf_spec (G : Sym2Graph 7) :
    canonOf G ∈ reps7 ∧ G ∼sf graphOfMask₂ 7 (canonOf G) := by
  have hm : maskOfGraph₂ G < 2 ^ 21 :=
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 21) finPairs7_rank_lt
  obtain ⟨hmem, heqv⟩ := leaf7_reflect hm
  rw [graphOfMask₂_maskOfGraph₂ finPairs7_rank_inj G] at heqv
  exact ⟨hmem, heqv⟩

set_option maxRecDepth 8192 in
lemma triTable7_cover : ∀ a b c : Fin 7, a < b → b < c →
    (pairIdx 7 a.val b.val, pairIdx 7 a.val c.val, pairIdx 7 b.val c.val)
      ∈ triTable 7 := by decide

set_option maxRecDepth 8192 in
lemma triTable7_sound : ∀ t ∈ triTable 7, ∃ a b c : Fin 7, a < b ∧ b < c
    ∧ t = (pairIdx 7 a.val b.val, pairIdx 7 a.val c.val,
           pairIdx 7 b.val c.val) := by decide

/-- The triangle-free 7-vertex representatives, by the bit-level
test. -/
def k3FreeReps7 : List ℕ := reps7.filter (triFreeMask (triTable 7))

set_option maxRecDepth 8192 in
/-- 107 triangle-free classes on seven vertices (kernel-checked). -/
example : k3FreeReps7.length = 107 := by decide +kernel

/-- The bit-level filter agrees with the generic induced-containment
filter. -/
theorem k3FreeReps7_filter_eq :
    k3FreeReps7 = reps7.filter
      (fun h => !decide (inducedContains triangleGraph (graphOfMask₂ 7 h))) :=
  List.filter_congr fun h _ => by
    rw [Bool.eq_iff_iff, triFreeMask_iff triTable7_cover triTable7_sound,
      Bool.not_eq_true', decide_eq_false_iff_not,
      inducedContains_triangleGraph_iff_hasTri]

/-- The 107 triangle-free 7-vertex flags. -/
def k3FreeFlags7 : List (Sym2EmptyTypedFlag 7) :=
  k3FreeReps7.map (fun h => ⟦graphOfMask₂ 7 h⟧)

/-- **Kernel-only K₃-free completeness at `n = 7`**: the 107 filtered
representative decodings are exactly the flags of zero triangle
density. -/
theorem k3FreeFlags7_toFinset_eq :
    k3FreeFlags7.toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ S = 0) := by
  have heq : k3FreeFlags7 = maskFreeFlags triangleGraph reps7 7 := by
    unfold k3FreeFlags7 maskFreeFlags
    rw [k3FreeReps7_filter_eq]
  rw [heq]
  exact maskFreeFlags7_toFinset_eq triangleGraph

end FlagAlgebras.Compute.BitMask.Canon7
