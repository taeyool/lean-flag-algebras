import LeanFlagAlgebras.BitMask.Canon7Sweep00
import LeanFlagAlgebras.BitMask.Canon7Sweep01
import LeanFlagAlgebras.BitMask.Canon7Sweep02
import LeanFlagAlgebras.BitMask.Canon7Sweep03
import LeanFlagAlgebras.BitMask.Canon7Sweep04
import LeanFlagAlgebras.BitMask.Canon7Sweep05
import LeanFlagAlgebras.BitMask.Canon7Sweep06
import LeanFlagAlgebras.BitMask.Canon7Sweep07
import LeanFlagAlgebras.BitMask.Canon7Sweep08
import LeanFlagAlgebras.BitMask.Canon7Sweep09
import LeanFlagAlgebras.BitMask.Canon7Sweep10
import LeanFlagAlgebras.BitMask.Canon7Sweep11
import LeanFlagAlgebras.BitMask.Canon7Sweep12
import LeanFlagAlgebras.BitMask.Canon7Sweep13
import LeanFlagAlgebras.BitMask.Canon7Sweep14
import LeanFlagAlgebras.BitMask.Canon7Sweep15
import LeanFlagAlgebras.BitMask.Canon7Sweep16
import LeanFlagAlgebras.BitMask.Canon7Sweep17
import LeanFlagAlgebras.BitMask.Canon7Sweep18
import LeanFlagAlgebras.BitMask.Canon7Sweep19
import LeanFlagAlgebras.BitMask.Canon7Sweep20
import LeanFlagAlgebras.BitMask.Canon7Sweep21
import LeanFlagAlgebras.BitMask.Canon7Sweep22
import LeanFlagAlgebras.BitMask.Canon7Sweep23
import LeanFlagAlgebras.BitMask.Canon7Sweep24
import LeanFlagAlgebras.BitMask.Canon7Sweep25
import LeanFlagAlgebras.BitMask.Canon7Sweep26
import LeanFlagAlgebras.BitMask.Canon7Sweep27
import LeanFlagAlgebras.BitMask.Canon7Sweep28
import LeanFlagAlgebras.BitMask.Canon7Sweep29
import LeanFlagAlgebras.BitMask.Canon7Sweep30
import LeanFlagAlgebras.BitMask.Canon7Sweep31
import LeanFlagAlgebras.BitMask.Canon7Sweep32
import LeanFlagAlgebras.BitMask.Canon7Sweep33
import LeanFlagAlgebras.BitMask.Canon7Sweep34
import LeanFlagAlgebras.BitMask.Canon7Sweep35
import LeanFlagAlgebras.BitMask.Canon7Sweep36
import LeanFlagAlgebras.BitMask.Canon7Sweep37
import LeanFlagAlgebras.BitMask.Canon7Sweep38
import LeanFlagAlgebras.BitMask.Canon7Sweep39
import LeanFlagAlgebras.BitMask.Canon7Sweep40
import LeanFlagAlgebras.BitMask.Canon7Sweep41
import LeanFlagAlgebras.BitMask.Canon7Sweep42
import LeanFlagAlgebras.BitMask.Canon7Sweep43
import LeanFlagAlgebras.BitMask.Canon7Sweep44
import LeanFlagAlgebras.BitMask.Canon7Sweep45
import LeanFlagAlgebras.BitMask.Canon7Sweep46
import LeanFlagAlgebras.BitMask.Canon7Sweep47
import LeanFlagAlgebras.BitMask.Canon7Sweep48
import LeanFlagAlgebras.BitMask.Canon7Sweep49
import LeanFlagAlgebras.BitMask.Canon7Sweep50
import LeanFlagAlgebras.BitMask.Canon7Sweep51
import LeanFlagAlgebras.BitMask.Canon7Sweep52
import LeanFlagAlgebras.BitMask.Canon7Sweep53
import LeanFlagAlgebras.BitMask.Canon7Sweep54
import LeanFlagAlgebras.BitMask.Canon7Sweep55
import LeanFlagAlgebras.BitMask.Canon7Sweep56
import LeanFlagAlgebras.BitMask.Canon7Sweep57
import LeanFlagAlgebras.BitMask.Canon7Sweep58
import LeanFlagAlgebras.BitMask.Canon7Sweep59
import LeanFlagAlgebras.BitMask.Canon7Sweep60
import LeanFlagAlgebras.BitMask.Canon7Sweep61
import LeanFlagAlgebras.BitMask.Canon7Sweep62
import LeanFlagAlgebras.BitMask.Canon7Sweep63

/-! Machine-generated glue (gen_sweep7.py): assembles the 64 subrange
verdicts into the full `2^21` completeness sweep. -/

namespace FlagAlgebras.Compute.BitMask.Canon7

open FlagAlgebras.Compute.BitMask

/-- The assembled completeness sweep: `leaf7` holds on all `2^21`
masks. -/
lemma sweep7 : sweepMasks leaf7 21 0 = true := by
  refine sweepMasks_of_pieces leaf7 15 6 0 fun k hk => ?_
  rw [zero_mul, zero_add]
  match k, hk with
  | 0, _ => exact sweep7_piece_00
  | 1, _ => exact sweep7_piece_01
  | 2, _ => exact sweep7_piece_02
  | 3, _ => exact sweep7_piece_03
  | 4, _ => exact sweep7_piece_04
  | 5, _ => exact sweep7_piece_05
  | 6, _ => exact sweep7_piece_06
  | 7, _ => exact sweep7_piece_07
  | 8, _ => exact sweep7_piece_08
  | 9, _ => exact sweep7_piece_09
  | 10, _ => exact sweep7_piece_10
  | 11, _ => exact sweep7_piece_11
  | 12, _ => exact sweep7_piece_12
  | 13, _ => exact sweep7_piece_13
  | 14, _ => exact sweep7_piece_14
  | 15, _ => exact sweep7_piece_15
  | 16, _ => exact sweep7_piece_16
  | 17, _ => exact sweep7_piece_17
  | 18, _ => exact sweep7_piece_18
  | 19, _ => exact sweep7_piece_19
  | 20, _ => exact sweep7_piece_20
  | 21, _ => exact sweep7_piece_21
  | 22, _ => exact sweep7_piece_22
  | 23, _ => exact sweep7_piece_23
  | 24, _ => exact sweep7_piece_24
  | 25, _ => exact sweep7_piece_25
  | 26, _ => exact sweep7_piece_26
  | 27, _ => exact sweep7_piece_27
  | 28, _ => exact sweep7_piece_28
  | 29, _ => exact sweep7_piece_29
  | 30, _ => exact sweep7_piece_30
  | 31, _ => exact sweep7_piece_31
  | 32, _ => exact sweep7_piece_32
  | 33, _ => exact sweep7_piece_33
  | 34, _ => exact sweep7_piece_34
  | 35, _ => exact sweep7_piece_35
  | 36, _ => exact sweep7_piece_36
  | 37, _ => exact sweep7_piece_37
  | 38, _ => exact sweep7_piece_38
  | 39, _ => exact sweep7_piece_39
  | 40, _ => exact sweep7_piece_40
  | 41, _ => exact sweep7_piece_41
  | 42, _ => exact sweep7_piece_42
  | 43, _ => exact sweep7_piece_43
  | 44, _ => exact sweep7_piece_44
  | 45, _ => exact sweep7_piece_45
  | 46, _ => exact sweep7_piece_46
  | 47, _ => exact sweep7_piece_47
  | 48, _ => exact sweep7_piece_48
  | 49, _ => exact sweep7_piece_49
  | 50, _ => exact sweep7_piece_50
  | 51, _ => exact sweep7_piece_51
  | 52, _ => exact sweep7_piece_52
  | 53, _ => exact sweep7_piece_53
  | 54, _ => exact sweep7_piece_54
  | 55, _ => exact sweep7_piece_55
  | 56, _ => exact sweep7_piece_56
  | 57, _ => exact sweep7_piece_57
  | 58, _ => exact sweep7_piece_58
  | 59, _ => exact sweep7_piece_59
  | 60, _ => exact sweep7_piece_60
  | 61, _ => exact sweep7_piece_61
  | 62, _ => exact sweep7_piece_62
  | 63, _ => exact sweep7_piece_63
  | n + 64, h => exact absurd h (by omega)

end FlagAlgebras.Compute.BitMask.Canon7
