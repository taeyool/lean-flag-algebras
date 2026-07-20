module

public import Lean

@[expose] public section

/-! # Generator options

Shared switches for the flag-generation macros (the `generate_*` commands in
`Flags/FlagGenerator.lean`, `Flags/Densities/DensityThmGenerator.lean`, and
`Flags/ForbidFreeGenerator.lean`). -/

open Lean

/-- Selects the proof backend that every `generate_*` command (and the
hand-written SDP-certificate lines) uses for its bridging/completeness/downward
obligations, via the shared `flag_bridge_decide` tactic below.

* `true` (default) — `decide +kernel`.  Kernel reduction adds **no**
  compiled-evaluation axioms (`Lean.ofReduceBool`/`Lean.trustCompiler`); this is
  what keeps the generated flag layer axiom-clean, and it is the setting used by
  the entire library **except** the three forbid-free files below.
* `false` — `native_decide`.  A deliberate, file-local fallback for enumerations
  whose *kernel* reduction physically exceeds ~16 GB of RAM (the labeled
  construction in `Flagmatic/{K5turan,C5turan,K3forbidC6}.lean`, which OOMs under
  `decide +kernel`).  Compiled evaluation fits in a few GB, at the cost of the
  `Lean.ofReduceBool`/`Lean.trustCompiler` axioms **in those files only**.

Set it per-file with `set_option flagGen.kernelDecide false`.  The default keeps
`#print axioms` clean everywhere it is not overridden. -/
meta register_option flagGen.kernelDecide : Bool := {
  defValue := true
  descr := "flag generators prove bridging lemmas by `decide +kernel` (true) or `native_decide` (false)"
}

/-- The proof tactic emitted by every `generate_*` command for its
bridging/completeness/downward obligations.  Dispatches on `flagGen.kernelDecide`
(see above): `decide +kernel` by default (axiom-clean), or `native_decide` when
the option is set to `false` for a file whose kernel reduction does not fit in
RAM.  Kept as a named tactic (rather than inlining the choice in each generator)
so the proof strategy stays in one place. -/
syntax "flag_bridge_decide" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| flag_bridge_decide) => do
    -- Kernel reduction of the larger (n = 5/6) enumerations exceeds the default
    -- heartbeat budget during the `decide` tactic's elaboration; lift it (matching
    -- `native_decide`, which is not heartbeat-limited). The kernel check itself is
    -- unaffected and still terminates (finite reduction).
    let useKernel := flagGen.kernelDecide.get (← getOptions)
    withOptions (fun o => o.setNat `maxHeartbeats 0) do
      if useKernel then
        evalTactic (← `(tactic| decide +kernel))
      else
        evalTactic (← `(tactic| native_decide))
