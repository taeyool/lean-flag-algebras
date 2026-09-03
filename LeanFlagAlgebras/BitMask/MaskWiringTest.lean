import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.Forbid.CommonGraphs

/-! # Regression test: kernel-only forbid-free generation via the sweeps

Runs `generate_forbid_free_empty_typed_flags` with
`flagGen.maskCompleteness` (completeness through the bitmask
canonicalization sweeps) and `flagGen.kernelDecide` (remaining bridging
lemmas by `decide +kernel`) at `n = 5` and `n = 6` for a triangle
forbid, and pins the axiom footprint: every generated lemma must depend
only on `propext`, `Classical.choice`, `Quot.sound` — no
`Lean.ofReduceBool` / `Lean.trustCompiler`.

This is the empty-typed generation layer of a `K3freeC6`-style example,
fully kernel-checked. (The σ-typed / pair-density / mul layers still use
`native_decide` — bit-level density is the remaining task.) -/

open FlagAlgebras Forbid FlagAlgebras.Compute
open SimpleGraph

namespace MaskWiringTest

/-- The triangle, as the generation commands consume it. -/
def K3 : Sym2Graph 3 := completeSym2Graph 3

set_option maxHeartbeats 0
set_option maxRecDepth 65536

set_option flagGen.maskCompleteness true in
set_option flagGen.kernelDecide true in
generate_forbid_free_empty_typed_flags 5 K3

set_option flagGen.maskCompleteness true in
set_option flagGen.kernelDecide true in
generate_forbid_free_empty_typed_flags 6 K3

/-- Guard: the completeness lemmas are kernel-only. `#print axioms` on
them shows `[propext, Classical.choice, Quot.sound]`; this `example`
merely keeps them referenced so the build exercises the wiring. -/
example :
    sym2FlagSetHfree_5_0_0_K3
        = Finset.univ.filter (fun S => isHfree_5_0_0_K3 S = true)
      ∧ sym2FlagSetHfree_6_0_0_K3
        = Finset.univ.filter (fun S => isHfree_6_0_0_K3 S = true) :=
  ⟨sym2FlagSetHfree_5_0_0_K3_eq, sym2FlagSetHfree_6_0_0_K3_eq⟩

end MaskWiringTest
