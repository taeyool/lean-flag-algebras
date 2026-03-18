import LeanFlagAlgebras.ErdosPentagon.FlagDef
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity

open FlagAlgebras
open FlagAlgebras.Compute

namespace ErdosPentagon

-- /- flagDensity₂ O2₁_flag O2₁_flag K3₁_flag = 0 -/
-- @[simp]
-- theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_0_Flag_3_1_0_5
--     : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_0 Flag_3_1_0_5 = 0
--   := by
--   dsimp [Flag_2_1_0_0, Flag_3_1_0_5]
--   rw [flagDensity₂_eq_sym2FlagDensity₂]
--   native_decide


      -- 0,
      -- 1,
      -- 1,
      -- "1/2"
theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_1
    : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_1 = 1/2
  := by
  dsimp [Flag_2_1_0_0, Flag_2_1_0_1, Flag_3_1_0_1]
  rw [flagDensity₂_eq_sym2FlagDensity₂]
  native_decide

end ErdosPentagon
