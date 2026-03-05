import «LeanFlagAlgebras».Flags.FlagLoader

set_option linter.unnecessarySimpa false

load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_1.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_2.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_3.json"

load_flags "LeanFlagAlgebras/Flags/Flags/flags_1_1_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_2_1_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_3_1_0.json"

#print Sym2LabeledGraph_3_1_0_2
#check downward_3_1_0_2
#check flagSet_3_0_0_eq_univ
#check flagSet_3_1_0_val_eq

namespace MantelTheorem

noncomputable abbrev K1_flag := Flag_1_0_0_0
noncomputable abbrev O2_flag := Flag_2_0_0_0
noncomputable abbrev K2_flag := Flag_2_0_0_1
noncomputable abbrev O3_flag := Flag_3_0_0_0
noncomputable abbrev E3_flag := Flag_3_0_0_1
noncomputable abbrev P3_flag := Flag_3_0_0_2
noncomputable abbrev K3_flag := Flag_3_0_0_3

noncomputable abbrev K1₁_flag := Flag_1_1_0_0
noncomputable abbrev O2₁_flag := Flag_2_1_0_0
noncomputable abbrev K2₁_flag := Flag_2_1_0_1
noncomputable abbrev O3₁_flag := Flag_3_1_0_0
noncomputable abbrev E3₁_flag := Flag_3_1_0_1
noncomputable abbrev E3₁'_flag := Flag_3_1_0_2
noncomputable abbrev P3₁_flag := Flag_3_1_0_3
noncomputable abbrev P3₁'_flag := Flag_3_1_0_4
noncomputable abbrev K3₁_flag := Flag_3_1_0_5

noncomputable abbrev K1 := FlagAlgebra_1_0_0_0
noncomputable abbrev O2 := FlagAlgebra_2_0_0_0
noncomputable abbrev K2 := FlagAlgebra_2_0_0_1
noncomputable abbrev O3 := FlagAlgebra_3_0_0_0
noncomputable abbrev E3 := FlagAlgebra_3_0_0_1
noncomputable abbrev P3 := FlagAlgebra_3_0_0_2
noncomputable abbrev K3 := FlagAlgebra_3_0_0_3

noncomputable abbrev K1₁ := FlagAlgebra_1_1_0_0
noncomputable abbrev O2₁ := FlagAlgebra_2_1_0_0
noncomputable abbrev K2₁ := FlagAlgebra_2_1_0_1
noncomputable abbrev O3₁ := FlagAlgebra_3_1_0_0
noncomputable abbrev E3₁ := FlagAlgebra_3_1_0_1
noncomputable abbrev E3₁' := FlagAlgebra_3_1_0_2
noncomputable abbrev P3₁ := FlagAlgebra_3_1_0_3
noncomputable abbrev P3₁' := FlagAlgebra_3_1_0_4
noncomputable abbrev K3₁ := FlagAlgebra_3_1_0_5

end MantelTheorem
