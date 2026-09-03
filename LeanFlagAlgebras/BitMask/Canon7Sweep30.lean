import LeanFlagAlgebras.BitMask.Canon7Checker

/-! Completeness sweep piece 30 of 64: masks `983040`–`1015807`.

Machine-generated (gen_sweep7.py). The subrange is covered by 32
separate depth-10 kernel evaluations rather than one depth-15
evaluation, so the kernel releases its evaluation cache between
declarations; `sweepMasks_of_pieces` glues them back together. -/

namespace FlagAlgebras.Compute.BitMask.Canon7

open FlagAlgebras.Compute.BitMask

set_option maxRecDepth 65536 in
private lemma s00 : sweepMasks leaf7 10 (30 * 32 + 0) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s01 : sweepMasks leaf7 10 (30 * 32 + 1) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s02 : sweepMasks leaf7 10 (30 * 32 + 2) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s03 : sweepMasks leaf7 10 (30 * 32 + 3) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s04 : sweepMasks leaf7 10 (30 * 32 + 4) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s05 : sweepMasks leaf7 10 (30 * 32 + 5) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s06 : sweepMasks leaf7 10 (30 * 32 + 6) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s07 : sweepMasks leaf7 10 (30 * 32 + 7) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s08 : sweepMasks leaf7 10 (30 * 32 + 8) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s09 : sweepMasks leaf7 10 (30 * 32 + 9) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s10 : sweepMasks leaf7 10 (30 * 32 + 10) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s11 : sweepMasks leaf7 10 (30 * 32 + 11) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s12 : sweepMasks leaf7 10 (30 * 32 + 12) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s13 : sweepMasks leaf7 10 (30 * 32 + 13) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s14 : sweepMasks leaf7 10 (30 * 32 + 14) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s15 : sweepMasks leaf7 10 (30 * 32 + 15) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s16 : sweepMasks leaf7 10 (30 * 32 + 16) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s17 : sweepMasks leaf7 10 (30 * 32 + 17) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s18 : sweepMasks leaf7 10 (30 * 32 + 18) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s19 : sweepMasks leaf7 10 (30 * 32 + 19) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s20 : sweepMasks leaf7 10 (30 * 32 + 20) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s21 : sweepMasks leaf7 10 (30 * 32 + 21) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s22 : sweepMasks leaf7 10 (30 * 32 + 22) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s23 : sweepMasks leaf7 10 (30 * 32 + 23) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s24 : sweepMasks leaf7 10 (30 * 32 + 24) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s25 : sweepMasks leaf7 10 (30 * 32 + 25) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s26 : sweepMasks leaf7 10 (30 * 32 + 26) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s27 : sweepMasks leaf7 10 (30 * 32 + 27) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s28 : sweepMasks leaf7 10 (30 * 32 + 28) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s29 : sweepMasks leaf7 10 (30 * 32 + 29) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s30 : sweepMasks leaf7 10 (30 * 32 + 30) = true := by
  decide +kernel
set_option maxRecDepth 65536 in
private lemma s31 : sweepMasks leaf7 10 (30 * 32 + 31) = true := by
  decide +kernel

/-- Subrange 30 of the completeness sweep. -/
lemma sweep7_piece_30 : sweepMasks leaf7 15 30 = true := by
  refine sweepMasks_of_pieces leaf7 10 5 30 fun j hj => ?_
  match j, hj with
  | 0, _ => exact s00
  | 1, _ => exact s01
  | 2, _ => exact s02
  | 3, _ => exact s03
  | 4, _ => exact s04
  | 5, _ => exact s05
  | 6, _ => exact s06
  | 7, _ => exact s07
  | 8, _ => exact s08
  | 9, _ => exact s09
  | 10, _ => exact s10
  | 11, _ => exact s11
  | 12, _ => exact s12
  | 13, _ => exact s13
  | 14, _ => exact s14
  | 15, _ => exact s15
  | 16, _ => exact s16
  | 17, _ => exact s17
  | 18, _ => exact s18
  | 19, _ => exact s19
  | 20, _ => exact s20
  | 21, _ => exact s21
  | 22, _ => exact s22
  | 23, _ => exact s23
  | 24, _ => exact s24
  | 25, _ => exact s25
  | 26, _ => exact s26
  | 27, _ => exact s27
  | 28, _ => exact s28
  | 29, _ => exact s29
  | 30, _ => exact s30
  | 31, _ => exact s31
  | n + 32, h => exact absurd h (by omega)

end FlagAlgebras.Compute.BitMask.Canon7
