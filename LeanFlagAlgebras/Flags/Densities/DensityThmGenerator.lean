import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import LeanFlagAlgebras.Flags.ForbidFreePruned
import Mathlib.Tactic

/-! # Density theorem generators

This module provides elaboration-time commands that synthesize `simp` theorems
about flag densities for the flags generated in `FlagDef.lean`. There are two:

* `generate_forbid_density_theorems n Forbid` — for each `n`-vertex (empty-typed)
  flag, records whether it is free of a forbidden subgraph.
* `generate_flag_pair_density_theorems patN hostN k m Forbid` and its
  `…_no_forbid` variant — the pair densities `p(F₁, F₂; G)` used when expanding a
  product of two flags into a sum of larger flags.

See each command's own documentation below for the meaning of its parameters and
example invocations. The densities and the forbidden-free partition are computed
during elaboration, and every generated theorem is independently verified by
`native_decide`.

A forbidden graph `Forbid` is named by any `def Forbid` in `CommonGraphs.lean`
that has a companion `Forbid_toFinFlag_eq` lemma; the complete graphs `K3`, `K4`,
`K5` are provided there, and non-complete graphs (e.g. `C5`) work too.
`MulThmGenerator.lean` adds the matching flag-multiplication generators.
-/

open Lean Elab Command
open FlagAlgebras
open FlagAlgebras.Compute

namespace Flags.Densities

/-- If `tag` has the form `"K<r>"` for some `r ≥ 1`, return that clique size `r`.
This is what lets the forbid loaders handle the complete graph `K_r` for *any* `r`
from a single code path, rather than one hard-coded branch per `r`. -/
def parseCompleteGraphTag (tag : String) : Option Nat :=
  if tag.startsWith "K" then
    match (tag.drop 1).toNat? with
    | some r => if r ≥ 1 then some r else none
    | none   => none
  else
    none

/-- Extract the `Flag_*` representative from a `…_toFinFlag_eq` lemma whose statement is
`G.toFinFlag = ⟨n, Flag_n_0_0_idx⟩`. The forbid loader uses this to `simp` with the
forbidden graph's flag definition, so the canonical index `idx` is read off the lemma
instead of being hard-coded per forbid. -/
def forbidFlagIdentOfToFinFlagEq (thmName : Name) : CommandElabM (TSyntax `ident) := do
  let env ← getEnv
  let some ci := env.find? thmName
    | throwError s!"Missing lemma: {thmName}"
  let some (_, _, rhs) := ci.type.eq?
    | throwError s!"Lemma {thmName} is not an equality `G.toFinFlag = ⟨n, Flag_*⟩`"
  for a in rhs.getAppArgs do
    if let .const nm _ := a.getAppFn then
      -- `nm` may be namespace-qualified (e.g. `Mantel.Flag_3_0_0_3`); test the
      -- final name component so qualified flag constants are recognised too.
      if (match nm with | .str _ s => s.startsWith "Flag_" | _ => false) then
        return mkIdent nm
  throwError s!"Could not locate a `Flag_*` representative in the RHS of {thmName}"

/-- Resolve a forbid `tag` to its Lean graph identifier and `…_toFinFlag_eq` lemma name,
checking both exist. Any `tag` naming a `def <tag>` together with a `<tag>_toFinFlag_eq`
lemma works, so this is not restricted to complete graphs — a `C4`/`P4`/… forbid needs
only those two declarations. Complete-graph tags `"K<r>"` additionally get a
clique-specific hint when the declarations are missing. -/
def resolveForbidGraph (tag : String) : CommandElabM (TSyntax `ident × Name) := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let gSuffix := Name.mkSimple tag
  let eqSuffix := Name.mkSimple s!"{tag}_toFinFlag_eq"
  -- The forbidden graph `def <tag>` and its `<tag>_toFinFlag_eq` lemma are emitted
  -- unqualified, so they land in whatever namespace the example generates them in.
  -- Prefer the current namespace, falling back to the root.
  if env.contains (ns ++ gSuffix) && env.contains (ns ++ eqSuffix) then
    return (mkIdent (ns ++ gSuffix), ns ++ eqSuffix)
  if env.contains gSuffix && env.contains eqSuffix then
    return (mkIdent gSuffix, eqSuffix)
  let hint :=
    match parseCompleteGraphTag tag with
    | some r =>
      s!" Add `generate_complete_graph {r} <canonical index of K{r}>` to CommonGraphs.lean."
    | none =>
      s!" Define `def {tag}` and `lemma {tag}_toFinFlag_eq : {tag}.toFinFlag = \
⟨n, Flag_n_0_0_<idx>⟩` in CommonGraphs.lean, matching the identifier `{tag}` you passed."
  throwError s!"Unknown forbid graph for tag '{tag}': missing `def {tag}` and/or \
`{tag}_toFinFlag_eq`.{hint}"

/-- Build the RHS term of a density theorem from a `(num, den)` value. -/
def densityValueToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `($(Quote.quote num))
  else
    `((($(Quote.quote num) : Rat) / ($(Quote.quote den) : Rat)))

/-! ## Forbidden-subgraph containment and the forbidden-free partition

The helpers below decide, for each flag, whether its underlying graph contains a
given forbidden subgraph. `generate_forbid_density_theorems` uses them to split
the `n`-vertex flags into forbidden-free and not. -/

/-- All injective maps `Fin slots → Fin hostN` whose images avoid `used`,
represented as length-`slots` lists of distinct host-vertex indices (`< hostN`).
The elaboration-time search space for embedding a `forbidN`-vertex graph into an
`n`-vertex host. Structural recursion on `slots`. -/
private def hostInjectionsAux (hostN : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | slots + 1, used =>
      ((List.range hostN).filter (fun v => ¬ used.contains v)).flatMap (fun v =>
        (hostInjectionsAux hostN slots (v :: used)).map (fun rest => v :: rest))

/-- All injective maps `Fin forbidN → Fin hostN` (length-`forbidN` lists of
distinct vertices `< hostN`); empty when `forbidN > hostN`. Entry `i` of each
list is the host vertex assigned to forbidden-graph vertex `i`. -/
private def hostInjections (forbidN hostN : Nat) : List (List Nat) :=
  hostInjectionsAux hostN forbidN []

/-- Undirected edge membership: is `{a, b}` an edge of `edges` (in either
orientation)? -/
private def edgeMem (edges : List (Nat × Nat)) (a b : Nat) : Bool :=
  edges.any (fun e => (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a))

/-- **The single place that fixes the forbidden-subgraph containment notion.**

Returns `true` when the host graph (`hostEdges` on `hostN` vertices) contains the
forbidden graph (`forbidEdges` on `forbidN` vertices) as a **non-induced**
subgraph — i.e. there is an injection `φ` of the forbidden vertices into the host
mapping every forbidden edge to a host edge (extra host edges allowed). This is
exactly Python's `contains_forbidden_subgraph`, and it is the notion we expect to
want for general forbidden graphs in the long run.

Design note (induced vs. non-induced). For a **complete-graph** forbid `K_r` —
the only forbids in current use — non-induced containment coincides exactly with
the *induced* notion (`r` mutually adjacent vertices induce `K_r`), so the
theorems emitted below — which are about the *induced* single-flag density
`flagDensity₁ … = 0` — are provable by `native_decide` precisely on the partition
this function computes. For a future *non-complete, non-induced* forbid the
free/non-free split this function produces is already the intended (non-induced)
one; what would then also need to change is the emitted theorem *statement*
(currently the induced `flagDensity₁ = 0`), to a containment-based statement.
That is the one coupled spot to revisit — see `generate_forbid_density_theorems`. -/
def containsForbiddenSubgraph
    (forbidN : Nat) (forbidEdges : List (Nat × Nat))
    (hostN : Nat) (hostEdges : List (Nat × Nat)) : Bool :=
  if forbidEdges.isEmpty then
    true
  else if hostN < forbidN then
    false
  else
    (hostInjections forbidN hostN).any (fun φ =>
      forbidEdges.all (fun e =>
        edgeMem hostEdges (φ.getD e.1 0) (φ.getD e.2 0)))

/-- Parse a `"Flag_<r>_0_0_<idx>"` constant name into its vertex count `r` and
canonical index `idx`. Used to recover the forbidden graph's canonical edge list
from `genCanonicalEdgeLists r`. -/
def parseFlagRIdx (flagName : String) : CommandElabM (Nat × Nat) := do
  -- `flagName` may be namespace-qualified (e.g. `Mantel.Flag_3_0_0_3`); match on
  -- the final dotted component so qualified names parse too.
  match ((flagName.splitOn ".").getLastD flagName).splitOn "_" with
  | ["Flag", rStr, _, _, idxStr] =>
      let some r := rStr.toNat? | throwError s!"Cannot parse vertex count from {flagName}"
      let some idx := idxStr.toNat? | throwError s!"Cannot parse index from {flagName}"
      pure (r, idx)
  | _ => throwError s!"Unexpected flag-name shape (want Flag_r_0_0_idx): {flagName}"

/-- Evaluate `genCanonicalEdgeLists m` at elaboration time: the canonical edge
lists (0-indexed endpoint pairs) of the `m`-vertex canonical graphs, in the same
order as the generated `Flag_m_0_0_i` constants. Reuses the same compiler-backed
`evalNatPairLists` bridge the flag generator uses. -/
def evalCanonicalEdgeLists (m : Nat) : CommandElabM (List (List (Nat × Nat))) := do
  let edgesStx ← `(FlagAlgebras.Compute.genCanonicalEdgeLists $(Quote.quote m))
  liftTermElabM do
    let valExpr ← Lean.Elab.Term.elabTermAndSynthesize edgesStx none
    let valExpr ← instantiateMVars valExpr
    let typeExpr ← Lean.Meta.inferType valExpr
    evalNatPairLists typeExpr valExpr

/-! ### Edge-based (induced) forbid-free split

For the edge-based forbid commands (forbid is a `Sym2Graph m` *term* `F`, not a tag), the
forbid-free split is computed with the **induced** predicate `inducedContains F`, not the
non-induced `containsForbiddenSubgraph`. The mask is read straight off the Lean enumeration
`genSym2Graphs n`, so it uses exactly the `inducedContains` of the pruning core / Task-4 bridge. -/

/-- Compiler-backed evaluation of a closed `Expr` of type `List Bool`. -/
unsafe def evalBoolListImpl (type value : Lean.Expr) : Lean.Meta.MetaM (List Bool) :=
  Lean.Meta.evalExpr (List Bool) type value

@[implemented_by evalBoolListImpl]
opaque evalBoolList (type value : Lean.Expr) : Lean.Meta.MetaM (List Bool)

/-- The induced forbid-free mask aligned with the flag-index order: entry `i` is `true` iff the
`i`-th canonical `n`-vertex graph (`genSym2Graphs n`) does **not** contain an induced `F`. -/
def evalInducedFreeMask (n : Nat) (fStx : TSyntax `ident) : CommandElabM (List Bool) := do
  let stx ← `((FlagAlgebras.Compute.genSym2Graphs $(Quote.quote n)).map
    (fun G => !decide (FlagAlgebras.Compute.inducedContains $fStx G)))
  liftTermElabM do
    let e ← Lean.Elab.Term.elabTermAndSynthesize stx none
    let e ← instantiateMVars e
    let t ← Lean.Meta.inferType e
    evalBoolList t e

/-- The σ-typed forbid-free indices for an induced forbid mask: flag `i` is free iff its
underlying graph (canonical index `(flags[i]).1`) is induced-`F`-free per `freeMask`. -/
def inducedFreeFlagIndices (freeMask : List Bool)
    (flags : List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) : List Nat :=
  (List.range flags.length).filter (fun i =>
    freeMask.getD ((flags.getD i (0, [], [], 0, 0)).1) false)

/-- Like `evalInducedFreeMask`, but for **subgraph** (non-induced) forbidding: entry `i` is `true`
iff the `i`-th canonical `n`-vertex graph does **not** contain `F` as a (non-induced) subgraph
(`subgraphContains F G`, the G1 predicate). This drives the subgraph-`H`-free flag split (G4). -/
def evalSubgraphFreeMask (n : Nat) (fStx : TSyntax `ident) : CommandElabM (List Bool) := do
  let stx ← `((FlagAlgebras.Compute.genSym2Graphs $(Quote.quote n)).map
    (fun G => !decide (FlagAlgebras.Compute.subgraphContains $fStx G)))
  liftTermElabM do
    let e ← Lean.Elab.Term.elabTermAndSynthesize stx none
    let e ← instantiateMVars e
    let t ← Lean.Meta.inferType e
    evalBoolList t e

/-- Like `evalInducedFreeMask`, but for a **complete-graph** forbid `K_r`: uses the cheap
`hasClique r` (vertex-subset scan) instead of the generic embedding-based `inducedContains`
(Task 8a). Same mask, far cheaper at high `n`. -/
def evalCliqueFreeMask (n r : Nat) : CommandElabM (List Bool) := do
  let stx ← `((FlagAlgebras.Compute.genSym2Graphs $(Quote.quote n)).map
    (fun G => !decide (FlagAlgebras.Compute.hasClique $(Quote.quote r) G)))
  liftTermElabM do
    let e ← Lean.Elab.Term.elabTermAndSynthesize stx none
    let e ← instantiateMVars e
    let t ← Lean.Meta.inferType e
    evalBoolList t e

/-- If the forbid identifier `fStx` is (definitionally) `completeSym2Graph r` for a literal `r`,
return `some r` — so the cheap clique check (Task 8a) can replace the generic `inducedContains`.
Returns `none` for any other forbid (the generic path is then used). -/
def detectCompleteR (fStx : TSyntax `ident) : CommandElabM (Option Nat) := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let nm := fStx.getId
  let some name := ([ns ++ nm, nm].filter (env.contains ·)).head? | return none
  let some ci := env.find? name | return none
  let some val := ci.value? | return none
  match val.getAppFnArgs with
  | (``FlagAlgebras.Compute.completeSym2Graph, #[rArg]) =>
      liftTermElabM do
        match (← Lean.Meta.whnf rArg) with
        | .lit (.natVal r) => return some r
        | _ => return none
  | _ => return none

-- `generate_forbid_density_theorems n Forbid`
--
-- For each `n`-vertex empty-typed flag `Flag_n_0_0_i`, generate a `@[simp]`
-- theorem recording whether it contains the forbidden graph `Forbid`:
--   • forbidden-free  → `flagDensity1_Forbid_Flag_n_0_0_i_eq_zero :`
--                       `   flagDensity₁ Forbid.toFinFlag.2 Flag_n_0_0_i = 0`
--   • contains Forbid → `flagDensity1_Forbid_Flag_n_0_0_i_ne_zero :`
--                       `   ¬ flagDensity₁ Forbid.toFinFlag.2 Flag_n_0_0_i = 0`
-- (one per flag), each proved by `native_decide`.
--
-- Parameters:
--   • `n`      : vertex count of the empty-typed flags to scan (`Flag_n_0_0_*`).
--   • `Forbid` : the forbidden graph — any `def Forbid` in `CommonGraphs.lean`
--                with a `Forbid_toFinFlag_eq` lemma (e.g. `K3`, `K4`, `K5`).
--
-- Prerequisites: run `generate_empty_typed_flags n` first (so `Flag_n_0_0_*`
-- exist), and have `Forbid` / `Forbid_toFinFlag_eq` in scope.
--
-- Example — record which 4-vertex graphs are K₄-free:
--   `generate_forbid_density_theorems 4 K4`
elab "generate_forbid_density_theorems" nStx:num gStx:ident : command => do
  let n := nStx.getNat
  let tag := gStx.getId.toString

  -- Resolve the forbidden graph and read its flag representative — identical to
  -- the JSON loader, so the emitted proof terms match exactly.
  let (gIdent, gEqName) ← resolveForbidGraph tag
  let gEqIdent := mkIdent gEqName
  let forbidFlag ← forbidFlagIdentOfToFinFlagEq gEqName

  -- The forbidden graph's canonical edge list, recovered from the (r, idx) of its
  -- `Flag_r_0_0_idx` representative.
  let (r, idx) ← parseFlagRIdx forbidFlag.getId.toString
  let forbidAll ← evalCanonicalEdgeLists r
  let forbidEdges := forbidAll.getD idx []

  -- The host enumeration, in the same order as the `Flag_n_0_0_i` constants.
  let hostAll ← evalCanonicalEdgeLists n
  let total := hostAll.length

  let mut generatedEqZero : Nat := 0
  let mut generatedNeZero : Nat := 0

  for i in [0:total] do
    let flagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let isFree := ¬ containsForbiddenSubgraph r forbidEdges n (hostAll.getD i [])

    if ¬ (← isDeclaredInScope flagName.getId) then
      throwError s!"Missing definition: {flagName.getId}"

    if isFree then
      let thmName := mkIdent (Name.mkSimple s!"flagDensity1_{tag}_Flag_{n}_0_0_{i}_eq_zero")
      if ¬ (← isDeclaredInScope thmName.getId) then
        elabCommand (← `(
          @[simp]
          theorem $thmName
              : flagDensity₁ ($gIdent).toFinFlag.2 $flagName = 0
            := by
            rw [$gEqIdent:ident]
            unfold $flagName
            simp [$forbidFlag:ident]
            rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
            native_decide
        ))
        generatedEqZero := generatedEqZero + 1
    else
      let thmName := mkIdent (Name.mkSimple s!"flagDensity1_{tag}_Flag_{n}_0_0_{i}_ne_zero")
      if ¬ (← isDeclaredInScope thmName.getId) then
        elabCommand (← `(
          @[simp]
          theorem $thmName
              : ¬ flagDensity₁ ($gIdent).toFinFlag.2 $flagName = 0
            := by
            rw [$gEqIdent:ident]
            unfold $flagName
            simp [$forbidFlag:ident]
            rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
            native_decide
        ))
        generatedNeZero := generatedNeZero + 1

  logInfo s!"Generated {tag} density theorems: eq_zero={generatedEqZero}, ne_zero={generatedNeZero}"

/-! ## Subflag-multiplication density `p(F₁, F₂; G)`

The helpers below compute, by elementary combinatorics over edge lists, the
density `p(F₁, F₂; G)` — the fraction of ways to place two disjoint induced
copies of the pattern flags `F₁`, `F₂` inside a host flag `G` (sharing the type
vertices). `generate_flag_pair_density_theorems` uses it to fill in the
right-hand sides of its `flagDensity₂ … = value` theorems, which `native_decide`
then verifies. The flags' edge lists and type-vertex indices come from
`genFlagData k m n`, in the same order as the generated `Flag_n_k_m_i` constants. -/

/-- Lexicographic `≤` / `<` on endpoint pairs. -/
private def pairLe (x y : Nat × Nat) : Bool := x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2)
private def pairLt (x y : Nat × Nat) : Bool := x.1 < y.1 || (x.1 == y.1 && x.2 < y.2)

/-- Sort an edge list into canonical `(min,max)`-pair lex order. -/
private def sortEdges (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  List.insertionSort (fun x y => pairLe x y = true) edges

/-- Lexicographic `<` on sorted edge lists (shorter prefix is smaller); the order
`canonicalLabeledForm` minimizes over. -/
private def edgeListLt : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if pairLt x y then true
      else if x == y then edgeListLt xs ys
      else false

/-- Apply a relabeling `perm` (`perm[v]` is the new label of `v`) to an edge list,
normalizing each edge to `(min,max)` and sorting. Mirrors Python `relabel_edges`. -/
private def relabelEdges (perm : List Nat) (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  sortEdges (edges.map (fun e =>
    let a := perm.getD e.1 0
    let b := perm.getD e.2 0
    if a ≤ b then (a, b) else (b, a)))

/-- Canonical edge list with the labeled vertices fixed as `0..k-1` (in `labels`
order) and the unlabeled tail permuted to its lexicographically smallest form.
Mirrors Python `canonical_labeled_form`. The density only depends on equality of
these forms, so any consistent type-respecting canonicalization is correct. -/
private def canonicalLabeledForm (edges : List (Nat × Nat)) (n : Nat) (labels : List Nat) :
    List (Nat × Nat) :=
  let k := labels.length
  let unlabeled := (List.range n).filter (fun v => ¬ labels.contains v)
  let baseMap : List Nat := (List.range n).map (fun v =>
    match labels.findIdx? (· == v) with
    | some t => t
    | none => k + (unlabeled.findIdx? (· == v)).getD 0)
  let baseEdges := relabelEdges baseMap edges
  if n == k then baseEdges
  else
    let tail := (List.range (n - k)).map (· + k)
    let cands := tail.permutations.map (fun pt =>
      let fullPerm : List Nat := (List.range n).map (fun v =>
        if v < k then v else pt.getD (v - k) v)
      relabelEdges fullPerm baseEdges)
    cands.foldl (fun best c => if edgeListLt c best then c else best) (cands.headD baseEdges)

/-- All size-`r` sub-lists of `xs` preserving order (Python `itertools.combinations`). -/
private def combinations : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, r + 1 => (combinations xs r).map (fun c => x :: c) ++ combinations xs (r + 1)

/-- The subgraph induced on `vertices` (host vertices), re-indexed to local
positions `0..vertices.length-1`. -/
private def inducedLocalEdges (vertices : List Nat) (hostEdges : List (Nat × Nat)) :
    List (Nat × Nat) :=
  let m := vertices.length
  (List.range m).flatMap (fun i =>
    (List.range m).filterMap (fun j =>
      if i < j then
        if edgeMem hostEdges (vertices.getD i 0) (vertices.getD j 0) then some (i, j) else none
      else none))

/-- Reduce `good / total` to lowest terms, with `total = 0 ↦ 0/1`. -/
private def fracReduce (good total : Nat) : Nat × Nat :=
  if total == 0 then (0, 1)
  else let g := Nat.gcd good total; (good / g, total / g)

/-- Exact subflag-multiplication density `p(F₁, F₂; G)` as a reduced `(num, den)`
pair. Faithful port of Python `density_p_f1_f2_given_g`: counts the fraction of
ways to split the unlabeled host vertices into disjoint groups (sizes `m₁-k`,
`m₂-k`, sharing the `k` type vertices) whose induced labeled subflags equal `F₁`
and `F₂`. -/
def densityPF1F2GivenG
    (hostN : Nat) (hostEdges : List (Nat × Nat)) (hostLabels : List Nat)
    (m1 : Nat) (f1Edges : List (Nat × Nat)) (f1Labels : List Nat)
    (m2 : Nat) (f2Edges : List (Nat × Nat)) (f2Labels : List Nat) : Nat × Nat :=
  let k := hostLabels.length
  if f1Labels.length ≠ k || f2Labels.length ≠ k then (0, 1)
  else if k > m1 || k > m2 then (0, 1)
  else if hostLabels.dedup.length ≠ k then (0, 1)
  else
    let r1 := m1 - k
    let r2 := m2 - k
    if hostN < k + r1 + r2 then (0, 1)
    else
      let f1Canon := canonicalLabeledForm f1Edges m1 f1Labels
      let f2Canon := canonicalLabeledForm f2Edges m2 f2Labels
      let unlabeled := (List.range hostN).filter (fun v => ¬ hostLabels.contains v)
      let res := (combinations unlabeled r1).foldl (fun (acc : Nat × Nat) aExtra =>
        let aVertices := hostLabels ++ aExtra
        let aCanon := canonicalLabeledForm (inducedLocalEdges aVertices hostEdges) m1 (List.range k)
        let remaining := unlabeled.filter (fun v => ¬ aExtra.contains v)
        (combinations remaining r2).foldl (fun (acc2 : Nat × Nat) bExtra =>
          let total := acc2.1 + 1
          if aCanon != f1Canon then (total, acc2.2)
          else
            let bVertices := hostLabels ++ bExtra
            let bCanon := canonicalLabeledForm (inducedLocalEdges bVertices hostEdges) m2 (List.range k)
            if bCanon == f2Canon then (total, acc2.2 + 1) else (total, acc2.2)
        ) acc
      ) (0, 0)
      fracReduce res.2 res.1

/-- Evaluate `genFlagData k m n` at elaboration time: per σ-typed flag, its
`(underlyingGraphIdx, canonicalUnderlyingEdges, typeIndices, coeffNum, coeffDen)`,
in the same order as the generated `Flag_n_k_m_i` constants. -/
def evalFlagDataRows (k m n : Nat) :
    CommandElabM (List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) := do
  let stx ← `(FlagAlgebras.Compute.genFlagData $(Quote.quote k) $(Quote.quote m) $(Quote.quote n))
  liftTermElabM do
    let valExpr ← Lean.Elab.Term.elabTermAndSynthesize stx none
    let valExpr ← instantiateMVars valExpr
    let typeExpr ← Lean.Meta.inferType valExpr
    evalFlagData typeExpr valExpr

/-- The forbidden graph's `(vertexCount, canonicalEdgeList)`, recovered from its
`<tag>_toFinFlag_eq` lemma (`⟨r, Flag_r_0_0_idx⟩`). -/
def forbidEdgesOfTag (tag : String) : CommandElabM (Nat × List (Nat × Nat)) := do
  let (_, gEqName) ← resolveForbidGraph tag
  let forbidFlag ← forbidFlagIdentOfToFinFlagEq gEqName
  let (r, idx) ← parseFlagRIdx forbidFlag.getId.toString
  let forbidAll ← evalCanonicalEdgeLists r
  pure (r, forbidAll.getD idx [])

/-- The forbidden-free indices among a flag list, by **underlying-graph**
containment (`containsForbiddenSubgraph` on each flag's underlying edges). With
`forbid = none`, every index is "free". The σ-typed analogue of the empty-typed
free-index split, matching Python's `forbid_free_only` over flag records. -/
def freeFlagIndices (n : Nat) (forbid : Option (Nat × List (Nat × Nat)))
    (flags : List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) : List Nat :=
  match forbid with
  | none => List.range flags.length
  | some (r, forbidEdges) =>
      (List.range flags.length).filter (fun i =>
        ¬ containsForbiddenSubgraph r forbidEdges n ((flags.getD i (0, [], [], 0, 0)).2.1))

/-- Shared core for the pair-density emitters. For every unordered pair `(i, j)`
of (forbidden-free) pattern flags `Flag_patN_k_m_*` and every (forbidden-free)
host flag `Flag_hostN_k_m_h`, emit the `simp` theorem `flagDensity₂ … = value`,
the `value` computed by `densityPF1F2GivenG`. `forbid = none` includes all flags.

**Task 8b — one batched `native_decide`.** Rather than one `native_decide` per pair (the
dominant typed-example cost: `ErdosPentagon` emits ~2 832), we prove a single batch lemma
`pairDensityBatch_… : [sym2FlagDensity₂ …, …] = [value, …]` by **one** `native_decide`, then
derive each `@[simp] flagDensity₂ … = value` by projecting the batch (`congrArg (·.getD i 0)`),
exactly the `downwardFactorsHfree_…_eq` pattern. This amortizes the per-pair `native_decide`
compilation across all pairs. -/
def genPairDensityCoreOn (k m patN hostN : Nat)
    (patterns hosts : List (Nat × List (Nat × Nat) × List Nat × Nat × Nat))
    (patternFree hostFree : List Nat) : CommandElabM Unit := do
  let patternTag := s!"{patN}_{k}_{m}"
  let hostTag := s!"{hostN}_{k}_{m}"

  -- Collect the batch: the `sym2FlagDensity₂` terms (LHS), the value terms (RHS), and the
  -- per-pair `(thmName, f1, f2, g, value)` metadata (its array index is its batch position).
  let mut sym2Terms : Array (TSyntax `term) := #[]
  let mut valueTerms : Array (TSyntax `term) := #[]
  let mut pairs : Array (Ident × Ident × Ident × Ident × TSyntax `term) := #[]
  for p1 in patternFree do
    for p2 in patternFree do
      if p1 ≤ p2 then
        let f1 := patterns.getD p1 (0, [], [], 0, 0)
        let f2 := patterns.getD p2 (0, [], [], 0, 0)
        for h in hostFree do
          let g := hosts.getD h (0, [], [], 0, 0)
          let nd := densityPF1F2GivenG hostN g.2.1 g.2.2.1 patN f1.2.1 f1.2.2.1 patN f2.2.1 f2.2.2.1
          let rhsTerm ← densityValueToTerm nd.1 nd.2
          let f1Name := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{p1}")
          let f2Name := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{p2}")
          let gName := mkIdent (Name.mkSimple s!"Flag_{hostTag}_{h}")
          let s1Name := mkIdent (Name.mkSimple s!"Sym2Flag_{patternTag}_{p1}")
          let s2Name := mkIdent (Name.mkSimple s!"Sym2Flag_{patternTag}_{p2}")
          let sgName := mkIdent (Name.mkSimple s!"Sym2Flag_{hostTag}_{h}")
          let thmName := mkIdent (Name.mkSimple
            s!"flagDensity₂_Flag_{patternTag}_{p1}_Flag_{patternTag}_{p2}_Flag_{hostTag}_{h}")

          if ¬ (← isDeclaredInScope f1Name.getId) then throwError s!"Missing definition: {f1Name.getId}"
          if ¬ (← isDeclaredInScope f2Name.getId) then throwError s!"Missing definition: {f2Name.getId}"
          if ¬ (← isDeclaredInScope gName.getId) then throwError s!"Missing definition: {gName.getId}"

          sym2Terms := sym2Terms.push
            (← `(FlagAlgebras.Compute.sym2FlagDensity₂ $s1Name $s2Name $sgName))
          valueTerms := valueTerms.push rhsTerm
          pairs := pairs.push (thmName, f1Name, f2Name, gName, rhsTerm)

  -- Batch in chunks (one `native_decide` per chunk), so each per-pair projection's `List.getD`
  -- reduction stays shallow: a single big batch (e.g. 1800 pairs) overflows `maxRecDepth` when the
  -- projection reduces `getD i` for large `i`. Chunk size 200 keeps depth < 512 (the default) while
  -- still collapsing ~1800 per-pair `native_decide`s to ~9.
  let chunk := 200
  let nChunks := (pairs.size + chunk - 1) / chunk
  for c in [0:nChunks] do
    let lo := c * chunk
    let hi := min (lo + chunk) pairs.size
    let batchName := mkIdent (Name.mkSimple s!"pairDensityBatch_{patternTag}_{hostTag}_{c}")
    elabUnlessDefined batchName.getId (← `(
        theorem $batchName
            : ([ $(sym2Terms.extract lo hi),* ] : List ℚ) = [ $(valueTerms.extract lo hi),* ] := by
          native_decide))
    for li in [0:(hi - lo)] do
      let (thmName, f1Name, f2Name, gName, rhsTerm) := pairs[lo + li]!
      if ¬ (← isDeclaredInScope thmName.getId) then
        elabCommand (← `(
          @[simp]
          theorem $thmName : flagDensity₂ $f1Name $f2Name $gName = $rhsTerm := by
            first | delta $f1Name $f2Name $gName | skip
            rw [flagDensity₂_eq_sym2FlagDensity₂]
            exact congrArg (fun l => l.getD $(Quote.quote li) (0 : ℚ)) $batchName))

  logInfo s!"Generated {pairs.size} pair-density theorem(s) via {nChunks} batched native_decide(s): \
pattern {patternTag}, host {hostTag}"

/-- Shared core for the pair-density emitters: compute the (non-induced, tag-based) forbid-free
index split, then delegate to `genPairDensityCoreOn`. -/
def genPairDensityCore (k m patN hostN : Nat)
    (forbid : Option (Nat × List (Nat × Nat))) : CommandElabM Unit := do
  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patternFree := freeFlagIndices patN forbid patterns
  let hostFree := freeFlagIndices hostN forbid hosts
  genPairDensityCoreOn k m patN hostN patterns hosts patternFree hostFree

-- `generate_flag_pair_density_theorems patN hostN k m Forbid`
--
-- Generate the pair-density (`flagDensity₂`) `simp` theorems for a σ-typed flag
-- algebra, restricted to flags free of a forbidden subgraph. Parameters:
--   • `patN`   : size of the two "pattern" flags whose joint density is taken.
--   • `hostN`  : size of the "host" flag the density is measured in.
--   • `k`, `m` : select the flag type σ = `FlagType_k_m` — σ is the `m`-th
--                `k`-vertex graph, `k` the number of labeled (type) vertices.
--   • `Forbid` : a forbidden graph (`def Forbid` + `Forbid_toFinFlag_eq` in
--                `CommonGraphs.lean`, e.g. `K3`/`K4`/`K5`); only `Forbid`-free
--                pattern and host flags take part.
--
-- For each unordered pair `(i ≤ j)` of `Forbid`-free pattern flags and each
-- `Forbid`-free host `h` it emits
--   `flagDensity₂_Flag_patN_k_m_i_Flag_patN_k_m_j_Flag_hostN_k_m_h :`
--   `   flagDensity₂ Flag_patN_k_m_i Flag_patN_k_m_j Flag_hostN_k_m_h = value`,
-- proved by `native_decide`.
--
-- Prerequisites: run `generate_flags patN k m` and `generate_flags hostN k m`.
--
-- Example — K₄-free pair densities of 3-vertex flags of type `FlagType_2_0`
-- inside 4-vertex hosts:
--   `generate_flag_pair_density_theorems 3 4 2 0 K4`
elab "generate_flag_pair_density_theorems" patS:num hostS:num kS:num mS:num
    forbidS:ident : command => do
  let forbid ← forbidEdgesOfTag forbidS.getId.toString
  genPairDensityCore kS.getNat mS.getNat patS.getNat hostS.getNat (some forbid)

-- `generate_flag_pair_density_theorems_no_forbid patN hostN k m`
--
-- The no-forbidden-subgraph version of `generate_flag_pair_density_theorems`:
-- same `patN`, `hostN`, `k`, `m`, but with no `Forbid` every pattern and host
-- flag participates. Emits the same `flagDensity₂ … = value` `@[simp]` theorems.
--
-- Example:
--   `generate_flag_pair_density_theorems_no_forbid 3 4 2 0`
elab "generate_flag_pair_density_theorems_no_forbid" patS:num hostS:num kS:num mS:num : command => do
  genPairDensityCore kS.getNat mS.getNat patS.getNat hostS.getNat none

-- `generate_pruned_flag_pair_density_theorems patN hostN k m F`
--
-- The **edge-based, induced** analogue of `generate_flag_pair_density_theorems`: `F` is a
-- `Sym2Graph mF` *term* (no tag, no canonical flag), and the forbid-free pattern/host split uses
-- the induced predicate `inducedContains F` (via `evalInducedFreeMask`). The emitted
-- `flagDensity₂ … = value` `@[simp]` theorems are identical in form — a density is a density; only
-- *which* pairs are computed differs. Prerequisite: the `F`-free pattern/host flags must exist (run
-- the edge-based generators `generate_forbid_free_flags …` first).
elab "generate_pruned_flag_pair_density_theorems" patS:num hostS:num kS:num mS:num
    fStx:ident : command => do
  let k := kS.getNat
  let m := mS.getNat
  let patN := patS.getNat
  let hostN := hostS.getNat
  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patMask ← evalInducedFreeMask patN fStx
  let hostMask ← evalInducedFreeMask hostN fStx
  let patternFree := inducedFreeFlagIndices patMask patterns
  let hostFree := inducedFreeFlagIndices hostMask hosts
  genPairDensityCoreOn k m patN hostN patterns hosts patternFree hostFree

/-- `generate_subgraph_free_flag_pair_density_theorems patN hostN k m F`: the **subgraph**-forbidding
analogue. A density is a density (forbid-independent); only *which* pattern/host pairs are computed
differs — here via the subgraph mask `evalSubgraphFreeMask` (`subgraphContains F`). Prerequisite: the
subgraph-`F`-free pattern/host flags must exist (`generate_subgraph_free_flags …` first). -/
elab "generate_subgraph_free_flag_pair_density_theorems" patS:num hostS:num kS:num mS:num
    fStx:ident : command => do
  let k := kS.getNat
  let m := mS.getNat
  let patN := patS.getNat
  let hostN := hostS.getNat
  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patMask ← evalSubgraphFreeMask patN fStx
  let hostMask ← evalSubgraphFreeMask hostN fStx
  let patternFree := inducedFreeFlagIndices patMask patterns
  let hostFree := inducedFreeFlagIndices hostMask hosts
  genPairDensityCoreOn k m patN hostN patterns hosts patternFree hostFree

end Flags.Densities
