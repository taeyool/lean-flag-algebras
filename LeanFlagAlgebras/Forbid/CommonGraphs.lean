import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Forbid.TuranDensity

/-! # Common forbidden graphs

The `generate_complete_graph` command, used by the example developments to define a
forbidden complete graph and its flag identity *locally*, inside the example's own
namespace.

Flags are generated per-development: each example runs `generate_empty_typed_flags` /
`generate_flags` in its own namespace, and there is no global flag library. So a
forbidden graph and its `_toFinFlag_eq` lemma must live in that same namespace, next to
the flags they reference. This file therefore only *provides the macro* — it generates
nothing at the root. A typical example does, inside `namespace Foo`:

```
generate_empty_typed_flags 3          -- the empty-typed 3-vertex flags
generate_complete_graph 3 3           -- K₃ (index 3 among them) + `K3_toFinFlag_eq`
generate_forbid_density_theorems 3 K3 -- … which then resolve `Foo.K3` in scope
```

The forbid theorem generators (`generate_forbid_density_theorems`,
`generate_forbid_mul_theorems`, …) resolve the forbidden graph and its `_toFinFlag_eq`
lemma in the current namespace (falling back to the root), so `K3`/`K4`/`K5` defined
this way are found with no further wiring. -/

open FlagAlgebras SimpleGraph Compute

open Lean Elab Command in
/-- `generate_complete_graph r idx` defines the complete graph
`K{r} : SimpleGraph (Fin r) := completeGraph (Fin r)` and proves
`K{r}_toFinFlag_eq : K{r}.toFinFlag = ⟨r, Flag_r_0_0_idx⟩`, where `idx` is the canonical
index of `K_r` among the empty-typed `r`-vertex flags.

Run it *inside* the example's namespace, after the matching `generate_empty_typed_flags r`
(so `Flag_r_0_0_idx` and `Sym2Graph_r_0_0_idx` are in scope). Canonical indices:
`K₃ → 3`, `K₄ → 10`, `K₅ → 33` (read off a `#print Sym2Graph_r_0_0_i`, or via
`flagmatic_to_lean.py inspect`).

For a non-complete forbid (e.g. `C4`/`C5`) `generate_complete_graph` does not apply: write
`def X : SimpleGraph (Fin n) := …` and `lemma X_toFinFlag_eq : X.toFinFlag = ⟨n, Flag_n_0_0_idx⟩`
by hand in the example's namespace. The simple `congr; fin_cases; simp` proof closes only
when `X` is spelled in the *same* labeling as the canonical flag `Sym2Graph_n_0_0_idx`;
otherwise supply an explicit graph isomorphism via `Quotient.sound` — see
`ErdosPentagon/FlagDef.lean`'s `C5` for a worked example. -/
elab "generate_complete_graph " rStx:num idxStx:num : command => do
  let r := rStx.getNat
  let idx := idxStx.getNat
  let kIdent    := mkIdent (Name.mkSimple s!"K{r}")
  let kEqIdent  := mkIdent (Name.mkSimple s!"K{r}_toFinFlag_eq")
  let flagIdent := mkIdent (Name.mkSimple s!"Flag_{r}_0_0_{idx}")
  let sym2Ident := mkIdent (Name.mkSimple s!"Sym2Graph_{r}_0_0_{idx}")
  let rT : TSyntax `term := Quote.quote r
  elabCommand (← `(command|
    def $kIdent : SimpleGraph (Fin $rT) := completeGraph (Fin $rT)))
  elabCommand (← `(command|
    set_option maxHeartbeats 0 in
    lemma $kEqIdent : ($kIdent).toFinFlag = ⟨$rT, $flagIdent⟩ := by
      simp [toFinFlag, $kIdent:ident]
      congr
      all_goals {
        ext i j
        fin_cases i <;> fin_cases j <;> simp [$sym2Ident:ident, mkEdgeFinset]
      }))
