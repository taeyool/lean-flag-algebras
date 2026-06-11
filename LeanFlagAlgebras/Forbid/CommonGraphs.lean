import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.Forbid.TuranDensity

/-! # Common forbidden graphs

Concrete `SimpleGraph (Fin n)` definitions for graphs frequently used as forbidden or
target subgraphs (e.g. the complete graphs `K3`, `K4`), together with lemmas computing
their `toFinFlag` representations as explicit empty-type flags.
-/

open FlagAlgebras SimpleGraph Compute

open Lean Elab Command in
/-- `generate_complete_graph r idx` defines the complete graph
`K{r} : SimpleGraph (Fin r) := completeGraph (Fin r)` and proves
`K{r}_toFinFlag_eq : K{r}.toFinFlag = ⟨r, Flag_r_0_0_idx⟩`, where `idx` is the canonical
index of `K_r` among the empty-typed `r`-vertex flags from `FlagDef.lean`.

These are exactly the per-clique constants the density/multiplication forbid loaders look
up by the `"K{r}"` tag (`load_forbid_density_theorems`, `load_forbid_mul_theorems`), so
adding a new complete-graph forbid is one line here (plus `--forbid-Kn r` on the Python
side) with no loader edits. -/
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

-- `K₃` (a triangle), `K₄`, `K₅` and their flag identities. The second argument is the
-- canonical index of `K_r` among the empty-typed `r`-vertex flags in `FlagDef.lean`.
generate_complete_graph 3 3
generate_complete_graph 4 10
generate_complete_graph 5 33
