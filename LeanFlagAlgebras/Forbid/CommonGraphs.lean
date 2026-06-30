import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Forbid.TuranDensity
import LeanFlagAlgebras.Flags.ForbidFreePruned

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

open FlagAlgebras.Compute in
/-- **Sym2 ↔ SimpleGraph bridge for the complete graph.** The induced forbidden flag of the
edge-based `completeSym2Graph r` equals the empty-type flag of the abstract `completeGraph (Fin r)`
(`= ⊤`). This lets an induced bound `f ≤ᵢ[⟨_, Sym2EmptyTypedFlag.toFlag ⟦completeSym2Graph r⟧⟩] g`
(proved by the Sym2-based pruning/SOS machinery) feed the non-induced graph bridge
`inducedForbidLE_toFinFlag_imp_forbidLE` and hence `forbidLE (completeGraph (Fin r))`. -/
theorem completeSym2Graph_finFlag_eq (r : ℕ) :
    (⟨r, Sym2EmptyTypedFlag.toFlag ⟦completeSym2Graph r⟧⟩ : FinFlag ∅ₜ)
      = (completeGraph (Fin r)).toFinFlag := by
  have hgraph : (completeSym2Graph r).toLabeledGraph.graph = completeGraph (Fin r) := by
    ext u v
    rw [Sym2Graph.toLabeledGraph_adj_iff, completeSym2Graph_edges_iff]
    exact Iff.rfl
  have hflag : Sym2EmptyTypedFlag.toFlag ⟦completeSym2Graph r⟧
      = (⟦{ graph := completeGraph (Fin r), type_embed := RelEmbedding.ofIsEmpty _ _ }⟧
          : Flag ∅ₜ (Fin r)) := by
    simp only [Sym2EmptyTypedFlag.toFlag, Sym2Graph.toFlag, Quotient.lift_mk]
    refine Quotient.sound (Nonempty.intro ?_)
    exact {
      graph_iso := by
        refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
        intro u v
        simp [hgraph]
      type_preserve := List.ofFn_inj.mp rfl }
  show (⟨r, Sym2EmptyTypedFlag.toFlag ⟦completeSym2Graph r⟧⟩ : FinFlag ∅ₜ)
      = ⟨r, (⟦{ graph := completeGraph (Fin r), type_embed := RelEmbedding.ofIsEmpty _ _ }⟧
              : Flag ∅ₜ (Fin r))⟩
  rw [hflag]

open FlagAlgebras.Compute Forbid in
/-- **G2 framework bridge (general, subgraph semantics).** If `G` contains `F` as a (not necessarily
induced) subgraph, then the empty-typed flag of `G` lies in `forbiddenFlags` of `F`'s simple graph.
This is the arbitrary-`F` analogue of `completeSym2Graph_finFlag_mem_forbiddenFlags`: the membership
witness the ordinary `_ofMem` / family expansion lemmas need, with the `IsContained` obligation
discharged by `subgraphContains_iff_isContained`. The representation identity `toFlag ⟦G⟧ = ⟦G.toLabeledGraph⟧`
holds by `rfl` (`Sym2EmptyTypedFlag.toFlag` lifts `Sym2Graph.toFlag = ⟦·.toLabeledGraph⟧`). -/
theorem sym2Graph_finFlag_mem_forbiddenFlags {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n)
    (h : subgraphContains F G) :
    (⟨n, Sym2EmptyTypedFlag.toFlag ⟦G⟧⟩ : FinFlag ∅ₜ)
      ∈ forbiddenFlags F.toLabeledGraph.graph :=
  ⟨G.toLabeledGraph, rfl, (subgraphContains_iff_isContained F G).mp h⟩

open FlagAlgebras.Compute Forbid in
/-- **Supergraph ⇒ `forbiddenFlags` membership.** Any edge-superset `G ⊇ H` (same vertex count)
gives a flag in `forbiddenFlags H`. This is the per-member `hmem` input the finite-family expansion
`basisVector_quot_forbidEq_sum_ofFamilyMem` needs for the supergraph family of `H` (G4). -/
theorem sym2Graph_supergraph_mem_forbiddenFlags {m : ℕ} {H G : Sym2Graph m}
    (hsub : H.edges ⊆ G.edges) :
    (⟨m, Sym2EmptyTypedFlag.toFlag ⟦G⟧⟩ : FinFlag ∅ₜ)
      ∈ forbiddenFlags H.toLabeledGraph.graph :=
  sym2Graph_finFlag_mem_forbiddenFlags H G (subgraphContains_of_edges_subset hsub)

section SupergraphFamily
open FlagAlgebras.Compute Forbid

-- `allEdgesList`, `supergraphSym2List`, `supergraphFamily`, `supergraphFamily_eq_map`, and
-- `supergraphFamily_filter_iff` live in `Flags/ForbidFreePruned.lean` (the `FlagAlgebras.Compute`
-- layer) so the forbid-free generator can reference them; here we add the `forbiddenFlags` membership
-- (which needs the `Forbid` framework) and the subgraph-forbidding capstones on top.

/-- Every member of `supergraphFamily H` is in `forbiddenFlags H` (it is an edge-superset of `H`,
hence subgraph-contains `H`). This is the `hmem` input for `basisVector_quot_forbidEq_sum_ofFamilyMem`. -/
theorem supergraphFamily_mem_forbiddenFlags {m : ℕ} (H : Sym2Graph m) :
    ∀ D ∈ supergraphFamily H, D ∈ forbiddenFlags H.toLabeledGraph.graph := by
  intro D hD
  simp only [supergraphFamily, supergraphSym2List, List.mem_map] at hD
  obtain ⟨s, ⟨S, _, rfl⟩, rfl⟩ := hD
  exact sym2Graph_supergraph_mem_forbiddenFlags Finset.subset_union_left

/-- **Arbitrary-`H` subgraph-forbidding expansion** (capstone of G1–G4). Instantiates the
finite-family expansion `basisVector_quot_forbidEq_sum_ofFamilyMem` at the supergraph family of `H`:
modulo *subgraph*-`H`-freeness, `⟦basisVector F⟧` expands over the flags with zero induced density of
every supergraph of `H` (= the subgraph-`H`-free flags). The membership obligation is discharged by
`supergraphFamily_mem_forbiddenFlags`; the generator cites this directly. -/
theorem basisVector_quot_forbidEq_sum_subgraph {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {m : ℕ} (H : Sym2Graph m) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦basisVector F⟧ =[H.toLabeledGraph.graph]
      ∑ F' : FlagWithSize σ ℓ with (∀ D ∈ supergraphFamily H, flagDensity₁ D.2 (unlabel F') = 0),
        (flagDensity₁ F.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧ :=
  basisVector_quot_forbidEq_sum_ofFamilyMem (supergraphFamily H)
    (supergraphFamily_mem_forbiddenFlags H) F ℓ hℓ

/-- **Arbitrary-`H` subgraph-forbidding product expansion** (capstone). The multiplication analogue of
`basisVector_quot_forbidEq_sum_subgraph`. -/
theorem basisVector_quot_mul_forbidEq_sum_subgraph {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {m : ℕ} (H : Sym2Graph m) (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    : (⟦basisVector F₁⟧ * ⟦basisVector F₂⟧ : FlagAlgebra σ) =[H.toLabeledGraph.graph]
      ∑ F' : FlagWithSize σ ℓ with (∀ D ∈ supergraphFamily H, flagDensity₁ D.2 (unlabel F') = 0),
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • ⟦basisVector ⟨ℓ, F'⟩⟧ :=
  basisVector_quot_mul_forbidEq_sum_ofFamilyMem (supergraphFamily H)
    (supergraphFamily_mem_forbiddenFlags H) F₁ F₂ ℓ hℓ

end SupergraphFamily

open FlagAlgebras.Compute Forbid in
/-- The edge-based complete graph's induced forbidden flag is `H`-forbidden for
`H = completeGraph (Fin r)` (combines `completeSym2Graph_finFlag_eq` with `mem_forbiddenFlags_self`).
Supplies the `hmem` hypothesis that the ordinary `_ofMem` expansion lemmas need; the examples'
`def K_r := completeSym2Graph r` makes `⟦K_r⟧` defeq `⟦completeSym2Graph r⟧`. -/
theorem completeSym2Graph_finFlag_mem_forbiddenFlags (r : ℕ) :
    (⟨r, Sym2EmptyTypedFlag.toFlag ⟦completeSym2Graph r⟧⟩ : FinFlag ∅ₜ)
      ∈ forbiddenFlags (completeGraph (Fin r)) := by
  rw [completeSym2Graph_finFlag_eq r]
  exact mem_forbiddenFlags_self (completeGraph (Fin r))

/-- `forbid_complete_graph r` elaborates to the complete graph `K_r` as a `Sym2Graph r` term,
for the edge-based forbid-free commands (Task 6). Typical use:
`def K4 : Sym2Graph 4 := forbid_complete_graph 4`. -/
macro "forbid_complete_graph " r:term : term => `(FlagAlgebras.Compute.completeSym2Graph $r)
