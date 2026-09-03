import LeanFlagAlgebras.BitMask.RCanon2_6Checker

/-! Rooted (2,6) completeness sweep piece 0 of 4: masks `0`–`8191`.


Machine-generated (see gen_canon.py). The subrange is covered by 8
separate depth-10 kernel evaluations rather than one depth-13
evaluation, so the kernel releases its evaluation cache between
declarations; `sweepMasks_of_pieces` glues them back together. -/

namespace FlagAlgebras.Compute.BitMask.RCanon2_6

open FlagAlgebras.Compute.BitMask

set_option maxRecDepth 65536 in
private lemma s0 : sweepMasks leaf 10 (0 * 8 + 0) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s1 : sweepMasks leaf 10 (0 * 8 + 1) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s2 : sweepMasks leaf 10 (0 * 8 + 2) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s3 : sweepMasks leaf 10 (0 * 8 + 3) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s4 : sweepMasks leaf 10 (0 * 8 + 4) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s5 : sweepMasks leaf 10 (0 * 8 + 5) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s6 : sweepMasks leaf 10 (0 * 8 + 6) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s7 : sweepMasks leaf 10 (0 * 8 + 7) = true := by
  decide +kernel

/-- Subrange 0 of the rooted (2,6) completeness sweep. -/
lemma sweep_piece_0 : sweepMasks leaf 13 0 = true := by
  refine sweepMasks_of_pieces leaf 10 3 0 fun j hj => ?_
  match j, hj with
  | 0, _ => exact s0
  | 1, _ => exact s1
  | 2, _ => exact s2
  | 3, _ => exact s3
  | 4, _ => exact s4
  | 5, _ => exact s5
  | 6, _ => exact s6
  | 7, _ => exact s7
  | n + 8, h => exact absurd h (by omega)

end FlagAlgebras.Compute.BitMask.RCanon2_6
