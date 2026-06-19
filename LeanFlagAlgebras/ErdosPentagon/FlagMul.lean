import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.ErdosPentagon.FlagDef

/-! # Erdős pentagon problem: generated flag products

Bulk-loads the pre-generated flag-pair density theorems, forbidden-density
theorems and flag-product (`flagMul_*`) identities for the 5-vertex,
triangle-free flags over the three 3-vertex types, from the JSON data files.
These supply the product expansions consumed by the certificate reduction in
`Lemmas.lean`. -/

open FlagAlgebras Forbid
open FlagAlgebras.Compute

namespace ErdosPentagonAPI

generate_forbid_density_theorems 5 K3

generate_flag_pair_density_theorems 4 5 3 0 K3
generate_forbid_mul_theorems 4 5 3 0 K3

generate_flag_pair_density_theorems 4 5 3 1 K3
generate_forbid_mul_theorems 4 5 3 1 K3

generate_flag_pair_density_theorems 4 5 3 2 K3
generate_forbid_mul_theorems 4 5 3 2 K3

#print flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_0

end ErdosPentagonAPI
