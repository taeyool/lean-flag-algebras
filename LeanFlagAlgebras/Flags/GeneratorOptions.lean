module

public import Lean

@[expose] public section

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
meta register_option flagGen.kernelDecide : Bool := {
  defValue := false
  descr := "flag generators: prove bridging lemmas by `decide +kernel` instead of `native_decide`"
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
