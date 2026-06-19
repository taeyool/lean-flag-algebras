import LeanFlagAlgebras.Flags.FlagGenerator

/-! # Mantel's theorem: flag definitions

This file selects the specific generated flags and flag-algebra basis elements
used in the Mantel's theorem development (Turán density of `K₃`). Each
`Flag_n_k_m_i` / `FlagAlgebra_n_k_m_i` constant comes from the generated flag
library; the commented `abbrev`s document the intended combinatorial name
(`K`-cliques, `O`-independent sets, `E`/`P` two/three-vertex shapes, subscript
`₁` = one labelled vertex). Only the abbreviations actually needed downstream
(`K2`, `O3`, `K3`) are left active. -/

namespace MantelTheorem

-- Locally generate the flags this development uses (formerly imported from the global
-- `Flags/FlagDef.lean`): the empty-typed flags of sizes 0–3 and the σ-typed (1-labelled)
-- flags of sizes 1–3. These produce the `MantelTheorem.Flag_*` / `MantelTheorem.FlagAlgebra_*`
-- constants the abbreviations below and the rest of the development refer to.
generate_empty_typed_flags 0
generate_empty_typed_flags 1
generate_empty_typed_flags 2
generate_empty_typed_flags 3
generate_flags 1 1 0
generate_flags 2 1 0
generate_flags 3 1 0

-- noncomputable abbrev K0_flag := Flag_0_0_0_0
-- noncomputable abbrev K1_flag := Flag_1_0_0_0
-- noncomputable abbrev O2_flag := Flag_2_0_0_0
-- noncomputable abbrev K2_flag := Flag_2_0_0_1
-- noncomputable abbrev O3_flag := Flag_3_0_0_0
-- noncomputable abbrev E3_flag := Flag_3_0_0_1
-- noncomputable abbrev P3_flag := Flag_3_0_0_2
-- noncomputable abbrev K3_flag := Flag_3_0_0_3

-- noncomputable abbrev K1₁_flag := Flag_1_1_0_0
-- noncomputable abbrev O2₁_flag := Flag_2_1_0_0
-- noncomputable abbrev K2₁_flag := Flag_2_1_0_1
-- noncomputable abbrev O3₁_flag := Flag_3_1_0_0
-- noncomputable abbrev E3₁_flag := Flag_3_1_0_1
-- noncomputable abbrev E3₁'_flag := Flag_3_1_0_2
-- noncomputable abbrev P3₁_flag := Flag_3_1_0_3
-- noncomputable abbrev P3₁'_flag := Flag_3_1_0_4
-- noncomputable abbrev K3₁_flag := Flag_3_1_0_5

-- noncomputable abbrev K0 := FlagAlgebra_0_0_0_0
-- noncomputable abbrev K1 := FlagAlgebra_1_0_0_0
-- noncomputable abbrev O2 := FlagAlgebra_2_0_0_0
noncomputable abbrev K2 := FlagAlgebra_2_0_0_1
noncomputable abbrev O3 := FlagAlgebra_3_0_0_0
-- noncomputable abbrev E3 := FlagAlgebra_3_0_0_1
-- noncomputable abbrev P3 := FlagAlgebra_3_0_0_2
noncomputable abbrev K3 := FlagAlgebra_3_0_0_3

-- noncomputable abbrev K1₁ := FlagAlgebra_1_1_0_0
-- noncomputable abbrev O2₁ := FlagAlgebra_2_1_0_0
-- noncomputable abbrev K2₁ := FlagAlgebra_2_1_0_1
-- noncomputable abbrev O3₁ := FlagAlgebra_3_1_0_0
-- noncomputable abbrev E3₁ := FlagAlgebra_3_1_0_1
-- noncomputable abbrev E3₁' := FlagAlgebra_3_1_0_2
-- noncomputable abbrev P3₁ := FlagAlgebra_3_1_0_3
-- noncomputable abbrev P3₁' := FlagAlgebra_3_1_0_4
-- noncomputable abbrev K3₁ := FlagAlgebra_3_1_0_5

end MantelTheorem
