import LeanFlagAlgebras.BitMask.Canon6Sweep0
import LeanFlagAlgebras.BitMask.Canon6Sweep1
import LeanFlagAlgebras.BitMask.Canon6Sweep2
import LeanFlagAlgebras.BitMask.Canon6Sweep3

/-! # The six-vertex canonicalization sweep

Kernel-checked completeness for 2-graphs on six vertices: **every**
`Sym2Graph 6` is flag-equivalent (`∼sf`) to the decoding of one of the
156 listed representative masks. The sweep visits all `2^15` masks by
kernel reduction (`decide +kernel`) — no `native_decide`.

The sweep is split into four subrange files of eight depth-10 pieces
each (separate declarations, so the kernel releases its evaluation
cache and the files build in parallel), glued here by
`sweepMasks_of_pieces`. Forbid-agnostic: any forbidden-subgraph
condition becomes a filter over the 156 representatives downstream, so
this one sweep serves every 6-vertex problem. -/

namespace FlagAlgebras.Compute.BitMask.Canon6

open FlagAlgebras.Compute.BitMask

/-- The assembled completeness sweep: `leaf6` holds on all `2^15`
masks. -/
lemma sweep6 : sweepMasks leaf6 15 0 = true := by
  refine sweepMasks_of_pieces leaf6 13 2 0 fun k hk => ?_
  rw [zero_mul, zero_add]
  match k, hk with
  | 0, _ => exact sweep6_piece_0
  | 1, _ => exact sweep6_piece_1
  | 2, _ => exact sweep6_piece_2
  | 3, _ => exact sweep6_piece_3
  | n + 4, h => exact absurd h (by omega)

/-- Reflection of one leaf: every mask's canonical image is a listed
representative flag-equivalent to it. -/
theorem leaf6_reflect {m : ℕ} (hm : m < 2 ^ 15) :
    canonImage m ∈ reps6
      ∧ graphOfMask₂ 6 m ∼sf graphOfMask₂ 6 (canonImage m) := by
  have hleaf : leaf6 m = true := by
    have h := sweepMasks_spec leaf6 15 0 sweep6 m hm
    rwa [zero_mul, zero_add] at h
  unfold leaf6 at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  exact ⟨of_decide_eq_true hmem,
    leafParts_eqv pairIdx6_lt
      (perm6Consistent_of_lt (of_decide_eq_true hpidx)) hscan⟩

/-- **Completeness.** Every computable 6-vertex simple graph is
flag-equivalent to the decoding of one of the 156 listed representative
masks. Kernel-checked end to end — no `native_decide`. -/
theorem canon6_complete (G : Sym2Graph 6) :
    ∃ h ∈ reps6, G ∼sf graphOfMask₂ 6 h := by
  obtain ⟨m, hm, hG⟩ :=
    exists_mask_graphOfMask₂ finPairs6_rank_inj finPairs6_rank_lt G
  obtain ⟨hmem, heqv⟩ := leaf6_reflect hm
  exact ⟨canonImage m, hmem, hG ▸ heqv⟩

set_option maxRecDepth 8192 in
/-- There are 156 representatives — the number of isomorphism classes
of graphs on six vertices. -/
example : reps6.length = 156 := by decide

end FlagAlgebras.Compute.BitMask.Canon6
