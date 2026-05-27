import LeanFlagAlgebras.Flags.Densities.MulLoader

/-! # Erdős pentagon problem: generated flag products

Bulk-loads the pre-generated flag-pair density theorems, forbidden-density
theorems and flag-product (`flagMul_*`) identities for the 5-vertex,
triangle-free flags over the three 3-vertex types, from the JSON data files.
These supply the product expansions consumed by the certificate reduction in
`Lemmas.lean`. -/

open FlagAlgebras Forbid
open FlagAlgebras.Compute

namespace ErdosPentagonAPI

load_forbid_density_theorems "LeanFlagAlgebras/Flags/Densities/graphs_5_K3_free_indices.json"

load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_5_3_0_from_4_3_0.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_5_3_0_from_4_3_0.json"

load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_5_3_1_from_4_3_1.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_5_3_1_from_4_3_1.json"

load_flag_pair_density_theorems "LeanFlagAlgebras/Flags/Densities/density_5_3_2_from_4_3_2.json"
load_forbid_mul_theorems "LeanFlagAlgebras/Flags/Densities/density_5_3_2_from_4_3_2.json"

#print flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_0

end ErdosPentagonAPI
