import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.BitMask.RootedAccept

/-! # Regression test: kernel-only typed generation, pair densities, mul

Runs the full σ-typed pipeline with the BitMask kernel options at the
`(k, patN) = (2, 3)`, host-4 combination (the `CompleteGraphFreeP4`
shape):

* `flagGen.maskFlagSets` — `generate_flags` proves the typed flag-set
  completeness (`sym2FlagSet_…_eq_univ`, `flagSet_…_eq_univ`) and
  distinctness (`flagSet_…_val_eq`) through the rooted canonicalization
  sweeps; the `native_decide` list bridge `Sym2FlagList_…_eq` is not
  emitted at all.
* `flagGen.maskPairDensity` — all 200 `flagDensity₂` value theorems are
  proved through the BitMask rooted-density bridges by `decide +kernel`.
  The right-hand values come from the elaboration-time computation, so a
  wrong value would fail its kernel `decide` — the generation itself is
  the cross-check.
* The multiplication theorems (`generate_mul_theorems`) consume only the
  above, so they land at the pure kernel footprint too.

The `#print axioms` lines pin every layer at
`[propext, Classical.choice, Quot.sound]`. -/

namespace MaskPairDensityTest

set_option maxHeartbeats 0
set_option maxRecDepth 65536

generate_empty_typed_flags 3
generate_empty_typed_flags 4

set_option flagGen.maskFlagSets true in
generate_flags 3 2 0

set_option flagGen.maskFlagSets true in
generate_flags 4 2 0

#print axioms sym2FlagSet_3_2_0_eq_univ
#print axioms flagSet_4_2_0_eq_univ
#print axioms flagSet_4_2_0_val_eq

set_option flagGen.maskPairDensity true in
generate_flag_pair_density_theorems_no_forbid 3 4 2 0

#print axioms flagDensity₂_Flag_3_2_0_0_Flag_3_2_0_0_Flag_4_2_0_0

generate_mul_theorems 3 4 2 0

#print axioms flagMul_FlagAlgebra_3_2_0_0_FlagAlgebra_3_2_0_1

end MaskPairDensityTest
