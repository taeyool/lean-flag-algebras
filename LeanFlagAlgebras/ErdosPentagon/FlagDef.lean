import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.ErdosPentagon.Matrix.PosSemiDef

open FlagAlgebras

namespace ErdosPentagon

def K3 : FinFlag ∅ₜ := ⟨3, Flag_3_0_0_3⟩
noncomputable abbrev C5 := FlagAlgebra_5_0_0_19

#print Sym2Graph_5_0_0_19 -- s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 4)

def σ₂ : FlagType (Fin 3) := FlagType_3_2

noncomputable def Vᵣ : FlagAlgebraVec σ₂ 5 := ![
  FlagAlgebra_4_3_2_0, FlagAlgebra_4_3_2_1, FlagAlgebra_4_3_2_2, FlagAlgebra_4_3_2_3, FlagAlgebra_4_3_2_6
]

end ErdosPentagon
