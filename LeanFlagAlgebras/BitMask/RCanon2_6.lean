import LeanFlagAlgebras.BitMask.RCanon2_6Sweep0
import LeanFlagAlgebras.BitMask.RCanon2_6Sweep1
import LeanFlagAlgebras.BitMask.RCanon2_6Sweep2
import LeanFlagAlgebras.BitMask.RCanon2_6Sweep3

/-! # The `(2, 6)` rooted canonicalization sweep

Kernel-checked rooted canonicalization for six-vertex flags with two
roots: **every** roots-matching mask decodes to a labeled flag
equivalent to the decoding of one of the 1992 listed representatives —
for every 2-root type graph `σ` at once. This is the sweep `K3freeC6`'s
typed size-6 host layer needs. The sweep visits all `2^15` masks by
kernel reduction (`decide +kernel`), split into four subrange files
glued here by `sweepMasks_of_pieces`. -/

namespace FlagAlgebras.Compute.BitMask.RCanon2_6

open FlagAlgebras.Compute.BitMask

/-- The assembled sweep: `leaf` holds on all `2^15` masks. -/
lemma sweep : sweepMasks leaf 15 0 = true := by
  refine sweepMasks_of_pieces leaf 13 2 0 fun k hk => ?_
  rw [zero_mul, zero_add]
  match k, hk with
  | 0, _ => exact sweep_piece_0
  | 1, _ => exact sweep_piece_1
  | 2, _ => exact sweep_piece_2
  | 3, _ => exact sweep_piece_3
  | n + 4, h => exact absurd h (by omega)

/-- Reflection: every mask's canonical image is listed, and for every
type graph the decoded labeled flags are equivalent. -/
theorem rleaf_reflect {x : ℕ} (hx' : x < 2 ^ 15) {σ : Sym2FlagType 2}
    (hx : RootsMatch σ 6 x) :
    canonImage x ∈ rreps2_6
      ∧ ∃ hy : RootsMatch σ 6 (canonImage x),
          labeledGraphOfMask σ 6 (by omega) x hx
            ∼sf labeledGraphOfMask σ 6 (by omega) (canonImage x) hy := by
  have hleaf : leaf x = true := by
    have h := sweepMasks_spec leaf 15 0 sweep x hx'
    rwa [zero_mul, zero_add] at h
  unfold leaf at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  obtain ⟨hcons, hfix⟩ := consistent_of_lt (of_decide_eq_true hpidx)
  exact ⟨of_decide_eq_true hmem,
    rleafParts_eqv (by omega) pairIdx_lt hcons hfix hscan hx⟩

end FlagAlgebras.Compute.BitMask.RCanon2_6
