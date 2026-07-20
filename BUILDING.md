# Building lean-flag-algebras

Requires the toolchain pinned in `lean-toolchain` (Lean `v4.27.0`) and the Mathlib
build cache (fetched by `lake`). A first build compiles the whole library.

```bash
lake build
```

## Memory / parallelism

This project verifies its flag enumerations by **`decide +kernel`** (kernel
reduction) rather than `native_decide` wherever it fits in RAM. That choice is
deliberate: kernel reduction adds **no compiled-evaluation axioms**
(`Lean.ofReduceBool` / `Lean.trustCompiler`) — run `#print axioms <thm>` on such a
result and you will not see them. The price is RAM: kernel reduction of the larger
enumerations uses far more memory than compiled `native_decide` would.

### The labeled-flag construction and the `native_decide` fallback (three files)

The **labeled-flag construction** driven by the typed `generate_forbid_free_flags`
commands used to peak **above 16 GB under `decide +kernel` and OOM-kill**, because the
kernel materialises the enumeration's bundled graph-embedding (`↪g`) structures — one
per (graph, embedding) pair. That construction cost is now removed: it is rerouted
through a **raw `List (ℕ×ℕ) × List ℕ` enumeration** (`Compute/RawLabeled.lean`, applied
in `runForbidFreeTypedClique`), whose kernel-decided coverage check carries no `Finset`
or `↪g` and fits in a few GB. `Flagmatic/ErdosPentagon.lean` (forbid-K3, n = 5) now
builds under **`decide +kernel`** at ~13.8 GB, axiom-clean (no `ofReduceBool`).

Three files still use the fallback (`set_option flagGen.kernelDecide false`, → `native_decide`,
adding `Lean.ofReduceBool` / `Lean.trustCompiler` **in that file only**):

- `Flagmatic/K5turan.lean` and `Flagmatic/C5turan.lean` (n = 5) — the construction fix
  works, but their *multiplication* stage (backend-independent, ~11 GB; K5-/C5-free is
  barely pruned so it is heavier than the K3 case) tips the file to ~13.9 GB and OOMs
  by a ~1 GB margin on a 15 GB machine. They would build under `decide +kernel` on a
  **≥ ~16–18 GB** machine — flip `flagGen.kernelDecide` back to `true` there. (C5turan
  also uses the subgraph route, whose construction reroute is not yet implemented.)
- `Flagmatic/K3forbidC6.lean` (n = 6) — does **not** build on a 16 GB machine under
  *either* backend: native_decide's n = 6 native-code compilation itself OOMs (~13–15 GB,
  exit 137, ~78 min), kernel-decide is worse. Needs **≥ ~20–24 GB RAM**. A hardware limit
  of the n = 6 example, independent of the decide backend.

The switch lives in `LeanFlagAlgebras/Flags/GeneratorOptions.lean` (`flag_bridge_decide`
dispatches on `flagGen.kernelDecide`, default `true` = kernel). Every file not listed
above stays on `decide +kernel` and is axiom-clean.

### Approximate peak RAM per file (single Lean process)

| Files | backend | peak |
|---|---|---|
| Everything up to n = 4 (Mantel, K4turán, K3-forbid-{P3,C4}, …) | `decide +kernel` | ≲ 3 GB |
| `ErdosPentagon.*` (n = 5 full enumeration, incl. `FlagMul`) | `decide +kernel` | ~11–14 GB |
| `Flagmatic.ErdosPentagon` (forbid-free, n = 5, raw reroute) | `decide +kernel` | ~13.8 GB |
| `Flagmatic.{K5turan,C5turan}` (forbid-free, n = 5) | `native_decide` (fallback) | ~8 GB (kernel: ~13.9 GB, needs ≥ ~16–18 GB) |
| `Flagmatic.K3forbidC6` (forbid-free, **n = 6**) | `native_decide` (fallback) | **> 16 GB — needs ≥ ~20 GB** |

Because a plain `lake build` compiles many files **in parallel**, several heavy
`decide +kernel` files can run at once and exhaust a 16 GB machine. To build
reliably on ~16 GB, build the heavy files **serially** (each fits on its own), then
let the rest parallelize:

```bash
# heavy files one at a time
for m in \
  LeanFlagAlgebras.ErdosPentagon.FlagMul \
  LeanFlagAlgebras.ErdosPentagon.ErdosPentagon \
  LeanFlagAlgebras.Flagmatic.ErdosPentagon \
  LeanFlagAlgebras.Flagmatic.C5turan \
  LeanFlagAlgebras.Flagmatic.K5turan \
  LeanFlagAlgebras.Flagmatic.K3forbidC6 ; do
  lake build "$m"
done
# everything else (light; parallel is fine)
lake build
```

On a machine with more RAM (≳ 32 GB) plain `lake build` works directly.

## What changed vs. `native_decide`

- The `generate_*` flag/density commands emit `flag_bridge_decide` (in
  `Flags/GeneratorOptions.lean`), which is `decide +kernel` by default and
  `native_decide` only where a file opts out via `set_option flagGen.kernelDecide
  false` (the three forbid-free files above). **No other `native_decide` remains in
  the built library.**
- To keep kernel reduction feasible under the module system, the enumeration uses
  an in-repo `@[expose]` insertion sort (`ksort`, in `Compute/IsoInvariants.lean`)
  instead of Mathlib's non-exposed `List.insertionSort`, and a degree-pruned
  isomorphism check (`isEmptyIsoFastDeg_bool`, in `Compute/FastIso.lean`) that
  lowers the empty-graph enumeration's peak RAM by ~37%.
- The density computation routes through a List-based isomorphism checker
  (`isIsoFast_bool` + `extractInduced` bridge in `Compute/FlagDensity.lean`),
  cutting the density sub-step from ~12 GB to ~3 GB while staying axiom-clean.
- The forbid-free labeled-flag *construction* routes through a raw List enumeration
  (`Compute/RawLabeled.lean` + `rawEnc` encode-bridge, applied in the clique route of
  `Flags/ForbidFreeGenerator.lean`), removing the bundled-`↪g` materialisation that
  OOMed `decide +kernel`. This lets `Flagmatic/ErdosPentagon` (n = 5) drop its
  `native_decide` fallback entirely (now axiom-clean under kernel-decide).
- Heavy `generate_*` tactics are unchanged in *usage* — only their proof backend
  moved to `decide +kernel` (with the documented three-file `native_decide`
  fallback).
