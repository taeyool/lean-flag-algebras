import «LeanFlagAlgebras».Flags.FlagLoader

set_option linter.unnecessarySimpa false

load_flags "LeanFlagAlgebras/Flags/Flags/flags_2_0_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_3_0_0.json"

load_flags "LeanFlagAlgebras/Flags/Flags/flags_2_1_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_3_1_0.json"

namespace MantelTheorem

-- abbrev O2_Sym2Flag := Sym2Flag_2_0_0_0
-- abbrev K2_Sym2Flag := Sym2Flag_2_0_0_1
-- abbrev O3_Sym2Flag := Sym2Flag_3_0_0_0
-- abbrev E3_Sym2Flag := Sym2Flag_3_0_0_1
-- abbrev P3_Sym2Flag := Sym2Flag_3_0_0_2
-- abbrev K3_Sym2Flag := Sym2Flag_3_0_0_3

-- abbrev O2₁_Sym2Flag := Sym2Flag_2_1_0_0
-- abbrev K2₁_Sym2Flag := Sym2Flag_2_1_0_1
-- abbrev O3₁_Sym2Flag := Sym2Flag_3_1_0_0
-- abbrev E3₁_Sym2Flag := Sym2Flag_3_1_0_1
-- abbrev E3₁'_Sym2Flag := Sym2Flag_3_1_0_2
-- abbrev P3₁_Sym2Flag := Sym2Flag_3_1_0_3
-- abbrev P3₁'_Sym2Flag := Sym2Flag_3_1_0_4
-- abbrev K3₁_Sym2Flag := Sym2Flag_3_1_0_5

noncomputable abbrev O2_flag := Flag_2_0_0_0
noncomputable abbrev K2_flag := Flag_2_0_0_1
noncomputable abbrev O3_flag := Flag_3_0_0_0
noncomputable abbrev E3_flag := Flag_3_0_0_1
noncomputable abbrev P3_flag := Flag_3_0_0_2
noncomputable abbrev K3_flag := Flag_3_0_0_3

noncomputable abbrev O2₁_flag := Flag_2_1_0_0
noncomputable abbrev K2₁_flag := Flag_2_1_0_1
noncomputable abbrev O3₁_flag := Flag_3_1_0_0
noncomputable abbrev E3₁_flag := Flag_3_1_0_1
noncomputable abbrev E3₁'_flag := Flag_3_1_0_2
noncomputable abbrev P3₁_flag := Flag_3_1_0_3
noncomputable abbrev P3₁'_flag := Flag_3_1_0_4
noncomputable abbrev K3₁_flag := Flag_3_1_0_5

noncomputable abbrev O2 := FlagAlgebra_2_0_0_0
noncomputable abbrev K2 := FlagAlgebra_2_0_0_1
noncomputable abbrev O3 := FlagAlgebra_3_0_0_0
noncomputable abbrev E3 := FlagAlgebra_3_0_0_1
noncomputable abbrev P3 := FlagAlgebra_3_0_0_2
noncomputable abbrev K3 := FlagAlgebra_3_0_0_3

noncomputable abbrev O2₁ := FlagAlgebra_2_1_0_0
noncomputable abbrev K2₁ := FlagAlgebra_2_1_0_1
noncomputable abbrev O3₁ := FlagAlgebra_3_1_0_0
noncomputable abbrev E3₁ := FlagAlgebra_3_1_0_1
noncomputable abbrev E3₁' := FlagAlgebra_3_1_0_2
noncomputable abbrev P3₁ := FlagAlgebra_3_1_0_3
noncomputable abbrev P3₁' := FlagAlgebra_3_1_0_4
noncomputable abbrev K3₁ := FlagAlgebra_3_1_0_5

end MantelTheorem
