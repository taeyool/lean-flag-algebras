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

/-! ## Edge-based complete graphs (Task 6)

The edge-based, pruning-backed forbid-free commands (`generate_pruned_forbid_free_*`,
`generate_pruned_*_theorems`) forbid a `Sym2Graph m` **term** directly (decision D2), rather
than a `SimpleGraph` tag resolved off a canonical flag. `completeSym2Graph r` is the complete
graph `K_r` in that representation: every non-loop pair of `Fin r` is an edge. Forbidding it
captures *induced* `K_r`-freeness, which for a complete graph coincides with ordinary
`K_r`-freeness (decision D1).

Use it by naming the graph in the example's namespace and passing that identifier to the
edge-based commands and the `flag_expand_hfree` / `expand_one_hfree_at` tactics:

```
def K4 : Sym2Graph 4 := completeSym2Graph 4        -- or `forbid_complete_graph 4`
generate_pruned_forbid_free_empty_typed_flags 4 K4
…
theorem … ≤[(⟨_, Sym2EmptyTypedFlag.toFlag ⟦K4⟧⟩ : FinFlag ∅ₜ)] …
```

**Scope (user, 2026-06-19):** only complete graphs are provided for now; the general edge-list
DSL / `forbid_cycle` / `forbid_path` / forbidding a *list* of graphs are deferred (the family
machinery from Tasks 3/4/5a stays available for when this is revisited). -/

namespace FlagAlgebras.Compute

/-- The complete graph `K_r` as a computable `Sym2Graph r`: every non-loop pair is an edge. -/
def completeSym2Graph (r : ℕ) : Sym2Graph r where
  edges := Finset.univ.filter (fun e => ¬ e.IsDiag)
  edges_valid := fun e he => (Finset.mem_filter.mp he).2

/-- `completeSym2Graph r` is complete: an off-diagonal pair is an edge iff the endpoints differ.
This is the hypothesis the clique-based pruning (`inducedContains_iff_hasClique`, Task 8a) needs. -/
theorem completeSym2Graph_edges_iff (r : ℕ) (i j : Fin r) :
    s(i, j) ∈ (completeSym2Graph r).edges ↔ i ≠ j := by
  simp only [completeSym2Graph, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff,
    ne_eq]

end FlagAlgebras.Compute

/-- `forbid_complete_graph r` elaborates to the complete graph `K_r` as a `Sym2Graph r` term,
for the edge-based forbid-free commands (Task 6). Typical use:
`def K4 : Sym2Graph 4 := forbid_complete_graph 4`. -/
macro "forbid_complete_graph " r:term : term => `(FlagAlgebras.Compute.completeSym2Graph $r)
