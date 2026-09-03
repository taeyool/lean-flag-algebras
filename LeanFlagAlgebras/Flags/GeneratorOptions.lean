import Lean

/-! # Generator options

Shared switches for the flag-generation macros (the `generate_*` commands in
`Flags/FlagGenerator.lean`, `Flags/Densities/DensityThmGenerator.lean`, and
`Flags/ForbidFreeGenerator.lean`). -/

open Lean

/-- When `true`, the `generate_*` commands prove their bridging/completeness
lemmas by `decide +kernel` instead of `native_decide`, so the generated flag
layer adds no compiled-evaluation axioms
(`Lean.ofReduceBool`/`Lean.trustCompiler`).  Kernel reduction is viable for
small enumerations (e.g. Mantel's `n ≤ 3`); leave `false` for larger ones
(e.g. the pentagon's `n = 5`). -/
register_option flagGen.kernelDecide : Bool := {
  defValue := false
  descr := "flag generators: prove bridging lemmas by `decide +kernel` instead of `native_decide`"
}

/-- When `true`, `generate_forbid_free_empty_typed_flags` proves its
completeness lemma (`sym2FlagSetHfree_…_eq`) through the **bitmask
canonicalization sweeps** (`LeanFlagAlgebras.BitMask.*`) by kernel
computation — no `native_decide`, no extra axioms — instead of the
`native_decide` against the pruned generator. Currently supported for
**triangle forbids** (`completeSym2Graph 3`) at `n ∈ {5, 6, 7}`; the
user's file must import `LeanFlagAlgebras.BitMask.MaskBridge` (and
`….BitMask.Canon7` for `n = 7`). Unsupported combinations fall back to
the pruned route with a warning. -/
register_option flagGen.maskCompleteness : Bool := {
  defValue := false
  descr := "flag generators: prove forbid-free completeness via the kernel bitmask sweeps"
}

/-- When `true`, the pair-density generator proves its `flagDensity₂`
value theorems through the **bitmask rooted-density bridges**
(`LeanFlagAlgebras.BitMask.RootedCount`) by kernel computation — no
`native_decide` — instead of the batched `native_decide`. Currently
supported for combinations `(k, patN) ∈ {(1,2), (1,3), (2,3), (2,4)}`
with host size `≤ 7`; unsupported combinations fall back to the batch
route with a warning. Per-pair kernel evaluation re-enumerates the host
subset pairs, so this is intended for small hosts (Mantel-scale) until
the shared-pass batching lands. -/
register_option flagGen.maskPairDensity : Bool := {
  defValue := false
  descr := "pair-density generator: prove values via the kernel bitmask bridges"
}

/-- When `true` (together with `flagGen.maskPairDensity`), the
pair-density generator **shares the subset-pair pass across pattern
pairs**: one kernel theorem per host identifies the host's key multiset
(`rootedPairKeys`, `LeanFlagAlgebras.BitMask.RootedMatrix`) with a
literal, and each pair-density value is then a cheap `Multiset.count`
over that literal. This is the intended mode for hosts of size ≥ 5,
where per-pair re-enumeration dominates; at host ≤ 4 the plain per-pair
kernel route is already fast. -/
register_option flagGen.maskPairDensityShared : Bool := {
  defValue := false
  descr := "pair-density generator: share the kernel subset-pair pass across pattern pairs"
}

/-- When `true`, the σ-typed flag-set layer is proved through the
**bitmask rooted canonicalization sweeps** by kernel computation:

* `generate_flags` proves completeness (`sym2FlagSet_…_eq_univ`) and
  distinctness (the `Nodup` feeding `flagSet_…_val_eq`), and the
  `native_decide` list bridge `Sym2FlagList_…_eq` is not emitted at
  all (import `LeanFlagAlgebras.BitMask.RootedAccept`);
* `generate_forbid_free_flags` (triangle forbids) proves the
  forbid-filtered completeness `sym2FlagSetHfree_…_eq` and its
  `…_val_eq` `Nodup` the same way (import
  `LeanFlagAlgebras.BitMask.RootedHfree`).

Supported combinations `(k, n) ∈ {(1,2), (1,3), (1,5), (2,3), (2,4),
(2,6), (3,4), (3,5)}`; `(2,6)` additionally needs
`LeanFlagAlgebras.BitMask.RCanon2_6`. Unsupported combinations fall
back to the native routes with a warning. -/
register_option flagGen.maskFlagSets : Bool := {
  defValue := false
  descr := "generate_flags: prove typed flag-set completeness via the kernel bitmask sweeps"
}

/-- Debug knob for the `flagGen.maskFlagSets` forbid-typed route: emit
only the first `N` kernel side-condition lemmas (1 = mapEq, 2 = +sound,
3 = +cover, 4 = +repsLt, 5 = +nodup, 6 = +distinct, 7 = everything).
Used to bisect kernel cost/memory per lemma; leave at the default 7 for
normal operation. -/
register_option flagGen.maskFlagSetsPhase : Nat := {
  defValue := 7
  descr := "debug: emit only the first N maskFlagSets side-condition lemmas"
}

/-- Dispatches to `decide +kernel` when `flagGen.kernelDecide` is set, and to
`native_decide` otherwise.  The `generate_*` commands emit this tactic, so the
choice is made where the generated theorem elaborates — i.e. under the user
file's `set_option flagGen.kernelDecide`. -/
syntax "flag_bridge_decide" : tactic

elab_rules : tactic
  | `(tactic| flag_bridge_decide) => do
    if flagGen.kernelDecide.get (← getOptions) then
      Elab.Tactic.evalTactic (← `(tactic| decide +kernel))
    else
      Elab.Tactic.evalTactic (← `(tactic| native_decide))
