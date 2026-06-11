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

/- ────────────────────────────────────────────────────────────────────────────
   Forbidding a NON-complete graph (worked example: C4, the 4-cycle)
   ────────────────────────────────────────────────────────────────────────────
   `generate_complete_graph` only builds `completeGraph (Fin r)`, so a non-clique
   forbid needs its `def` + `_toFinFlag_eq` written here by hand. The density/mul
   loaders are graph-agnostic: they just need `def <Tag>` and `<Tag>_toFinFlag_eq`
   to exist, with `<Tag>` equal to the JSON `forbid.tag`. Nothing else changes.

   Two things matter (and are exactly what `K_r` gives for free):

   1. The EDGE SET — you must spell out the graph; only complete graphs are
      determined by `r` alone.
   2. The LABELING — the simple proof below closes only if you define the graph
      in the SAME labeling as the canonical flag `Sym2Graph_n_0_0_<idx>`. Read
      that labeling off with `#print Sym2Graph_4_0_0_8` (here: edges
      s(0,1), s(0,2), s(1,3), s(2,3)). If you instead use a different labeling,
      the `congr; fin_cases; simp` proof fails and you need an explicit graph
      isomorphism via `Quotient.sound` — see `C5` in
      `ErdosPentagon/FlagDef.lean` for that fallback.

   Find the index `<idx>` (here 8) by matching your graph against the printed
   `Sym2Graph_4_0_0_i`, or via `flagmatic_to_lean.py inspect`.

   The block below is verified to build green (canonical labeling → simple proof).
   C4 (4-cycle) in the canonical labeling of `Sym2Graph_4_0_0_8`:

   def C4 : SimpleGraph (Fin 4) := {
     Adj i j := match i, j with
       | 0, 1 | 1, 0 | 0, 2 | 2, 0 | 1, 3 | 3, 1 | 2, 3 | 3, 2 => true
       | _, _ => false
   }

   lemma C4_toFinFlag_eq : C4.toFinFlag = ⟨4, Flag_4_0_0_8⟩ := by
     simp [toFinFlag, C4]
     congr
     all_goals {
       ext i j
       fin_cases i <;> fin_cases j <;> simp [Sym2Graph_4_0_0_8, mkEdgeFinset]
     }

   Then on the Python side (tag must equal the Lean identifier "C4"):
     python gen_free_indices.py ../Graphs/graphs_4.json --forbid 4:12233441 --tag C4
     python calculate_densities.py --host ... --pattern ... --forbid 4:12233441 --tag C4
   and in your proof file:
     load_forbid_density_theorems "...graphs_4_C4_free_indices.json"
     load_forbid_mul_theorems     "...density_..._forbid_C4.json"
   ──────────────────────────────────────────────────────────────────────────── -/
