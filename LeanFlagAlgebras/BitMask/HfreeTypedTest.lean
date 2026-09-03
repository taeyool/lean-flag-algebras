import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.BitMask.RootedHfree

/-! # Regression test: kernel-only forbid-typed flag sets

Runs the pruned σ-typed generator with `flagGen.maskFlagSets` on
triangle forbids at the Mantel `(1,3)` and `K3freeC6`-pattern `(2,4)`
combinations: the forbid-filtered completeness
(`sym2FlagSetHfree_…_eq`) and the `Nodup` feeding `…_val_eq` are proved
through the rooted canonicalization sweeps by `decide +kernel` — the
pruned generator's `native_decide` bridges are not used. The
`#print axioms` lines pin both layers at
`[propext, Classical.choice, Quot.sound]`.

The `(2,6)` host layer works the same way (validated at 245 flags,
~8 min kernel wall, peak ~16 GB — the distinctness check is chunked
into per-24-row declarations so the kernel evaluation cache is released
between them); it is exercised in the `K3freeC6` example migration
rather than here. -/

namespace HfreeTypedTest

open FlagAlgebras.Compute

set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- The forbidden triangle, as the term the examples use. -/
def K3 : Sym2Graph 3 := completeSym2Graph 3

generate_forbid_free_empty_typed_flags 3 K3
generate_forbid_free_empty_typed_flags 4 K3

set_option flagGen.maskFlagSets true in
generate_forbid_free_flags 3 1 0 K3

set_option flagGen.maskFlagSets true in
generate_forbid_free_flags 4 2 0 K3

#print axioms sym2FlagSetHfree_3_1_0_K3_eq
#print axioms flagSetHfree_3_1_0_K3_val_eq
#print axioms sym2FlagSetHfree_4_2_0_K3_eq
#print axioms flagSetHfree_4_2_0_K3_val_eq

end HfreeTypedTest
