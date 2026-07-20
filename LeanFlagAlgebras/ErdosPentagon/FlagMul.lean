module

public import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
public import LeanFlagAlgebras.ErdosPentagon.FlagDef
public meta import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
public meta import LeanFlagAlgebras.ErdosPentagon.FlagDef

@[expose] public section

/-! # Erdős pentagon problem: generated flag products

Bulk-loads the pre-generated flag-pair density theorems, forbidden-density
theorems and flag-product (`flagMul_*`) identities for the 5-vertex,
triangle-free flags over the three 3-vertex types, from the JSON data files.
These supply the product expansions consumed by the certificate reduction in
`Lemmas.lean`. -/

open FlagAlgebras Forbid
open FlagAlgebras.Compute

namespace ErdosPentagonAPI

-- Kernel reduction of the n = 5/6 flag enumeration (via `flag_bridge_decide` =
-- `decide +kernel`) exceeds the default heartbeat budget during elaboration; lift
-- it for this file (matching `native_decide`, which is unbounded).
set_option maxHeartbeats 0
generate_forbid_density_theorems 5 K3

generate_flag_pair_density_theorems 4 5 3 0 K3
generate_forbid_mul_theorems 4 5 3 0 K3

generate_flag_pair_density_theorems 4 5 3 1 K3
generate_forbid_mul_theorems 4 5 3 1 K3

generate_flag_pair_density_theorems 4 5 3 2 K3
generate_forbid_mul_theorems 4 5 3 2 K3

-- #print flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_0

end ErdosPentagonAPI
