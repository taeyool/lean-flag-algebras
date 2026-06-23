import «LeanFlagAlgebras».FlagAlgebra.Compute.Downward
import «LeanFlagAlgebras».FlagAlgebra.Compute.FlagEnumeration
import Mathlib.Tactic

/-! # Flag generation macros

This module defines the elaboration-time macros that turn the self-contained
Lean flag enumerations (`FlagAlgebra.Compute.FlagEnumeration`) into named Lean
definitions and theorems, with no external JSON input:

* `generate_empty_typed_flags n` evaluates `genSym2Graphs n` (one canonical
  representative per isomorphism class of `n`-vertex graphs) at elaboration time
  and synthesizes, for each graph `i`, the constants `Sym2Graph_n_0_0_i`,
  `Sym2Flag_n_0_0_i`, `Flag_n_0_0_i`, `FlagAlgebra_n_0_0_i` (empty type ∅ₜ), plus
  the finset/`= univ` lemmas `sym2FlagSet_n_0_0`, `flagSet_n_0_0`,
  `flagSet_n_0_0_val_eq`, `flagSet_n_0_0_eq_univ`.
* `generate_flags n k m` synthesizes the `n`-vertex flags of the type σ given by
  the `k`-vertex graph with index `m`, evaluating the corresponding Lean
  enumeration at elaboration time. It produces the type constants
  `Sym2FlagType_k_m`, `FlagType_k_m`, and for each flag `i` the constants
  `Sym2LabeledGraph_n_k_m_i`, `Sym2Flag_n_k_m_i`, `Flag_n_k_m_i`,
  `FlagAlgebra_n_k_m_i`, the `simp` lemmas `unlabel_n_k_m_i` and `downward_n_k_m_i`
  (relating the labeled flag to its underlying empty-typed flag via the precomputed
  downward-normalizing coefficient), plus the corresponding finset/`= univ` lemmas.

The `… = Finset.univ` completeness lemmas are discharged by the mathematically
proved theorems `genEmptyTypedFlagSet_eq_univ` / `genFlagSet_eq_univ` (bridged to
the named flag lists by a single cheap `native_decide` over the tight Lean
enumeration), rather than by a `native_decide` over the entire quotient
`Fintype`.

The helper `def`s below evaluate the Lean-computed enumerations at elaboration
time and build the syntax for the generated terms.
-/

open Sym2 Lean Elab Command
open FlagAlgebras.Compute

/-- Build a `Finset` of edges from a list of `Sym2 (Fin n)` (used in generated
`Sym2Graph`/`Sym2LabeledGraph` definitions). -/
def mkEdgeFinset (n : ℕ) (l : List (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  l.toFinset

/-- Off-diagonal validity of `mkEdgeFinset n l` reduces to an off-diagonal check
on the underlying *list* `l`, since `mkEdgeFinset n l = l.toFinset` and membership
in `l.toFinset` is membership in `l`.

The generated `Sym2Graph`/`Sym2FlagType`/`Sym2LabeledGraph` definitions use this to
discharge `edges_valid` with a *structural* per-edge proof
(`mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])`):
`fin_cases` splits the finitely-many list entries and `simp` rewrites each via
`isDiag_iff_proj_eq`, yielding a compact proof term the kernel checks cheaply.
This replaces `edges_valid := by decide`, where the kernel must re-run the full
`Decidable` reduction (the `decide` whnf) to verify `of_decide_eq_true (Eq.refl true)`
— paid once in the elaborator and again in kernel type-checking. On the n = 6 worst
case (156 graphs) the switch cut `decide` tactic execution ~9× and roughly halved
kernel type-checking for these definitions. -/
theorem mkEdgeFinset_diag_free {n : ℕ} {l : List (Sym2 (Fin n))}
    (h : ∀ e ∈ l, ¬ e.IsDiag) : ∀ e ∈ mkEdgeFinset n l, ¬ e.IsDiag := by
  intro e he
  simp only [mkEdgeFinset, List.mem_toFinset] at he
  exact h e he

/-- Build the term defining the type embedding `i ↦ typeIndices[i]` as a nested
`if i.1 = j then … else …` chain of `Fin n` *values*, used in the generated
`type_embed` field.

Each branch is `(⟨idx, by decide⟩ : Fin n)` — the bound proof `idx < n` is on a
*concrete literal* (no free `i`), so the kernel checks a tiny `Nat.decLt`
reduction per branch. This is the key to a cheap `type_embed`: the alternative —
a single `ℕ`-valued chain wrapped as `⟨chain, by fin_cases i <;> decide⟩` /
`⟨chain, by split_ifs <;> decide⟩` — forces the kernel to verify the bound for
the *symbolic* `i`, which empirically dominates kernel type-checking (~13s of the
~17s for a 72-flag size-5 line) regardless of the tactic used. Pushing `Fin.mk`
into the branches removes that symbolic obligation entirely. -/
def mkTypeIndexFinExpr (typeIndices : Array Nat) (n : ℕ) : CommandElabM (TSyntax `term) := do
  if _h : typeIndices.size = 0 then
    throwError "type_indices must be nonempty"
  let lastIdx := typeIndices[typeIndices.size - 1]!
  let mut acc : TSyntax `term :=
    ← `((⟨$(Quote.quote lastIdx), by decide⟩ : Fin $(Quote.quote n)))
  for j in (List.range (typeIndices.size - 1)).reverse do
    let idx := typeIndices[j]!
    acc ← `(if i.1 = $(Quote.quote j) then (⟨$(Quote.quote idx), by decide⟩ : Fin $(Quote.quote n)) else $acc)
  pure acc

/-- Build a `Rat` term from a `(numerator, denominator)` coefficient pair. -/
def coeffQTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `((($(Quote.quote num) : Nat) : Rat))
  else
    `((($(Quote.quote num) : Rat) / ($(Quote.quote den) : Rat)))

/-- Compiler-backed evaluation of a closed `Expr` of type `List (List (ℕ × ℕ))`,
used to read the Lean-computed (`genSym2Graphs`) graph enumeration at
elaboration time. -/
unsafe def evalNatPairListsImpl (type : Lean.Expr) (value : Lean.Expr) :
    Lean.Meta.MetaM (List (List (Nat × Nat))) :=
  Lean.Meta.evalExpr (List (List (Nat × Nat))) type value

@[implemented_by evalNatPairListsImpl]
opaque evalNatPairLists (type : Lean.Expr) (value : Lean.Expr) :
    Lean.Meta.MetaM (List (List (Nat × Nat)))

/-- Compiler-backed evaluation of a closed `Expr` of type
`List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)`, used to read the
Lean-computed typed-flag enumeration (`genFlagData`) at elaboration time. Each
tuple is `(underlyingGraphIdx, canonicalUnderlyingEdges, typeIndices, coeffNum,
coeffDen)`. -/
unsafe def evalFlagDataImpl (type : Lean.Expr) (value : Lean.Expr) :
    Lean.Meta.MetaM (List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) :=
  Lean.Meta.evalExpr (List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) type value

@[implemented_by evalFlagDataImpl]
opaque evalFlagData (type : Lean.Expr) (value : Lean.Expr) :
    Lean.Meta.MetaM (List (Nat × List (Nat × Nat) × List Nat × Nat × Nat))

/-- Turn a list of canonical endpoint pairs `[(u,v),…]` into a Lean term
`[Sym2.mk ((u : Fin numVerts), (v : Fin numVerts)), …]`. -/
def natPairsToEdgesTerm (numVerts : ℕ) (edges : List (Nat × Nat)) :
    CommandElabM (TSyntax `term) := do
  let terms ← edges.toArray.mapM fun uv => do
    `(Sym2.mk (($(Quote.quote uv.1) : Fin $(Quote.quote numVerts)),
        ($(Quote.quote uv.2) : Fin $(Quote.quote numVerts))))
  `([ $terms,* ])

/-- True if `name` is declared in the current namespace (as `getCurrNamespace ++ name`)
or at the root. The `generate_*` macros emit *unqualified* names that pick up the
surrounding namespace, so a prerequisite/existence check (e.g. "is the underlying
empty-typed flag present?") must consult both: the locally-generated copy and any
root-level one. -/
def isDeclaredInScope (name : Name) : CommandElabM Bool := do
  let ns ← getCurrNamespace
  let env ← getEnv
  return env.contains (ns ++ name) || env.contains name

/-- Elaborate `cmd` only when `name` is not already declared *in the current
namespace*, so re-running a `generate_*` line is a no-op (the macros stay
idempotent). Generated declarations pick up the surrounding namespace, so this
guard checks the namespace-qualified name `getCurrNamespace ++ name` rather than
the root name: checking the root would (a) wrongly *skip* local generation when a
same-named root constant happens to exist (e.g. while migrating off a global flag
library) and (b) fail to detect the in-namespace re-declaration when two
`generate_*` calls share a type/underlying constant within one namespace. At the
root namespace `getCurrNamespace` is anonymous, so this coincides with the old
root check. -/
def elabUnlessDefined (name : Name) (cmd : Syntax) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  if ¬ (← getEnv).contains (ns ++ name) then
    elabCommand cmd

/-- Emit the three declarations that bridge a finset of `Sym2*Flag`s to the
corresponding finset of `Flag`s, shared verbatim by both generator macros:

* `flagSet …` — the image of the `Sym2*Flag` finset (`setName`) under `toFlag`;
* `flagSet …_val_eq` — its underlying multiset equals the explicit `Flag` list;
* `flagSet …_eq_univ` — completeness, from `setEqUnivName` and surjectivity of
  `toFlag`.

The two macros differ only in the flag element type (`flagElemType`), the flag
type tag (`flagType`), the `toFlag` map and its injectivity proof (`toFlagFn` /
`toFlagInj`), the surjectivity witness (`surjWitness`), and the `Nodup` proof of
the flag list (`nodupProof`); the dedup/`Quot.sound` value-lemma argument and the
`Finset.map_univ_of_surjective` completeness argument are identical. Each
declaration is emitted through `elabUnlessDefined`, so the macros stay idempotent. -/
def emitFlagSetMachinery
    (n : ℕ)
    (flagType flagElemType toFlagFn toFlagInj surjWitness nodupProof : TSyntax `term)
    (flagTerms flagBridgeTerms : Array (TSyntax `term))
    (setName setEqUnivName flagSetName flagSetValEqName flagSetEqUnivName : Ident) :
    CommandElabM Unit := do
  elabUnlessDefined flagSetName.getId (← `(
      def $flagSetName :=
        Finset.map { toFun := $toFlagFn, inj' := $toFlagInj } $setName
    ))

  elabUnlessDefined flagSetValEqName.getId (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize $flagType $(Quote.quote n))).val =
            [ $flagBridgeTerms,* ]) := by
        have hnodup :
            ([ $flagTerms,* ] : List $flagElemType).Nodup := $nodupProof
        have hdedup :
            ([ $flagTerms,* ] : List $flagElemType).dedup
              = ([ $flagTerms,* ] : List $flagElemType) := by
          exact List.Nodup.dedup hnodup
        have hright :
            (List.map $toFlagFn ([ $flagTerms,* ] : List $flagElemType))
              = [ $flagBridgeTerms,* ] := by
          rfl
        refine Quot.sound ?_
        have heq :
            List.map $toFlagFn
              (([ $flagTerms,* ] : List $flagElemType).dedup)
                = [ $flagBridgeTerms,* ] := by
          simpa [hdedup] using hright
        exact heq ▸ List.Perm.refl _
    ))

  elabUnlessDefined flagSetEqUnivName.getId (← `(
      theorem $flagSetEqUnivName : $flagSetName = Finset.univ := by
        change
          Finset.map { toFun := $toFlagFn, inj' := $toFlagInj } $setName
            = Finset.univ
        have hs : $setName = Finset.univ := $setEqUnivName
        rw [hs]
        exact Finset.map_univ_of_surjective (f :=
          { toFun := $toFlagFn, inj' := $toFlagInj })
          $surjWitness
    ))

-- `generate_empty_typed_flags n`: evaluate the self-contained Lean enumeration
-- `genSym2Graphs n` (one canonical representative per isomorphism class) at
-- elaboration time and synthesize the named constants `Sym2Graph_n_0_0_i`,
-- `Sym2Flag_n_0_0_i`, `Flag_n_0_0_i`, `FlagAlgebra_n_0_0_i`, the finset defs and
-- the `… = Finset.univ` lemmas. `sym2FlagSet_n_0_0_eq_univ` is discharged by the
-- mathematically-proved completeness theorem `genEmptyTypedFlagSet_eq_univ`
-- (bridged to the named list by a single cheap `native_decide` over the explicit
-- flag enumeration) rather than a `native_decide` over the entire quotient
-- `Fintype` via `Finset.univ`.
elab "generate_empty_typed_flags" nStx:num : command => do
  let n := nStx.getNat

  let edgesStx ← `(FlagAlgebras.Compute.genCanonicalEdgeLists $(Quote.quote n))
  let graphEdges ← liftTermElabM do
    let valExpr ← Lean.Elab.Term.elabTermAndSynthesize edgesStx none
    let valExpr ← instantiateMVars valExpr
    let typeExpr ← Lean.Meta.inferType valExpr
    evalNatPairLists typeExpr valExpr
  let count := graphEdges.length

  for i in [0:count] do
    let edgePairs := graphEdges[i]!
    let graphName := mkIdent (Name.mkSimple s!"Sym2Graph_{n}_0_0_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{i}")
    let edgesTerm ← natPairsToEdgesTerm n edgePairs

    elabUnlessDefined graphName.getId (← `(
        def $graphName : Sym2Graph $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])
      ))

    elabUnlessDefined flagName.getId (← `(
        def $flagName : Sym2EmptyTypedFlag $(Quote.quote n) :=
          Quotient.mk (Sym2GraphSetoid $(Quote.quote n)) $graphName
      ))

    elabUnlessDefined flagBridgeName.getId (← `(
        def $flagBridgeName := ($flagName : Sym2EmptyTypedFlag $(Quote.quote n)).toFlag
      ))

    elabUnlessDefined flagAlgebraName.getId (← `(
        noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra ∅ₜ :=
          ⟦FlagAlgebras.basisVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
      ))

  let setName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_0_0")
  let setEqUnivName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_0_0_eq_univ")
  let flagTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}") : TSyntax `term))
  let flagListEqName := mkIdent (Name.mkSimple s!"Sym2FlagList_{n}_0_0_eq")

  elabUnlessDefined setName.getId (← `(
      def $setName : Finset (Sym2EmptyTypedFlag $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset
    ))

  -- Positional list bridge: the named flag list equals `genEmptyTypedFlags n`.
  -- Each `Sym2Flag_n_0_0_i` is `⟦Sym2Graph_n_0_0_i⟧`, where `Sym2Graph_n_0_0_i`
  -- is the *canonical relabeling* (`canonicalEdgeList`) of `(genSym2Graphs n)[i]`
  -- — isomorphic to it, but not edge-equal — so the two quotients agree
  -- positionally. Deciding this *list* equality costs `O(g)` isomorphism checks
  -- (one per position), versus the `O(g²)` the `Finset`/`toFinset` route forces;
  -- that removes the quadratic blowup and keeps the bridge tractable at `n = 7`
  -- (g = 1044). Both completeness lemmas below rewrite through it, then close via
  -- the math theorems on `genEmptyTypedFlags`.
  elabUnlessDefined flagListEqName.getId (← `(
      theorem $flagListEqName :
          ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n)))
            = FlagAlgebras.Compute.genEmptyTypedFlags $(Quote.quote n) := by
        native_decide
    ))

  elabUnlessDefined setEqUnivName.getId (← `(
      theorem $setEqUnivName : $setName = Finset.univ := by
        have h : $setName = FlagAlgebras.Compute.genEmptyTypedFlagSet $(Quote.quote n) := by
          have hfl := $flagListEqName
          show (([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset)
              = FlagAlgebras.Compute.genEmptyTypedFlagSet $(Quote.quote n)
          unfold FlagAlgebras.Compute.genEmptyTypedFlagSet
          rw [hfl]
        rw [h]
        exact FlagAlgebras.Compute.genEmptyTypedFlagSet_eq_univ $(Quote.quote n)
    ))

  let flagSetName := mkIdent (Name.mkSimple s!"flagSet_{n}_0_0")
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSet_{n}_0_0_val_eq")
  let flagSetEqUnivName := mkIdent (Name.mkSimple s!"flagSet_{n}_0_0_eq_univ")
  let flagBridgeTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}") : TSyntax `term))

  emitFlagSetMachinery n
    (← `(∅ₜ))
    (← `(Sym2EmptyTypedFlag $(Quote.quote n)))
    (← `(Sym2EmptyTypedFlag.toFlag))
    (← `(Sym2EmptyTypedFlag.toFlag_injective))
    (← `(by
        intro F
        exact ⟨F.toSym2EmptyTypedFlag, FlagAlgebras.Flag.toSym2EmptyTypedFlag_toFlag_eq F⟩))
    (← `(by
        have hfl := $flagListEqName
        rw [hfl]
        exact FlagAlgebras.Compute.genEmptyTypedFlags_nodup $(Quote.quote n)))
    flagTerms flagBridgeTerms
    setName setEqUnivName flagSetName flagSetValEqName flagSetEqUnivName

  logInfo s!"Generated {count} empty-typed flags as `Sym2Flag_{n}_0_0_i` (n = {n})."

-- `generate_flags n k m`: synthesize the `n`-vertex σ-typed flags, where σ is the
-- `k`-vertex graph with index `m`. Evaluates the enumeration `genFlagData k m n`
-- at elaboration time (one orbit representative per flag, in canonical order) and
-- synthesizes the named constants `Sym2FlagType_k_m`,
-- `FlagType_k_m`, and per flag `Sym2LabeledGraph_n_k_m_i`, `Sym2Flag_n_k_m_i`,
-- `Flag_n_k_m_i`, `FlagAlgebra_n_k_m_i`, the `simp` lemmas `unlabel_n_k_m_i` /
-- `downward_n_k_m_i`, and the finset/`= univ` lemmas. The type's edges and each
-- flag's underlying edges are the canonical edge lists `canonicalEdgeList
-- (genSym2Graphs ·)`, so the generated `Sym2LabeledGraph`'s edge Finset matches
-- `Sym2Graph_n_0_0_j`'s exactly (preserving `unlabel`/`downward` defeq); the
-- downward coefficient is the reduced orbit ratio computed by `genFlagData` and
-- independently re-checked by the per-flag `native_decide`.
elab "generate_flags" nStx:num kStx:num mStx:num : command => do
  let n := nStx.getNat
  let k := kStx.getNat
  let m := mStx.getNat

  -- Dependency check: each generated flag's `unlabel`/`downward` bridge is stated against the
  -- underlying empty-typed flag `Flag_n_0_0_i` (produced by `generate_empty_typed_flags n`).
  -- If that prerequisite is missing, the emitted `unlabel` theorem references an undefined
  -- `Flag_n_0_0_i`, which auto-binds as an opaque variable and fails with a cryptic
  -- `Quotient.sound (flagEqv.refl …)` type mismatch only *after* enumerating all flags
  -- (minutes, at large n). Fail fast here with an actionable message instead.
  unless (← isDeclaredInScope (Name.mkSimple s!"Flag_{n}_0_0_0")) do
    throwError s!"`generate_flags {n} {k} {m}` requires the underlying empty-typed flags \
`Flag_{n}_0_0_i`, which are produced by `generate_empty_typed_flags {n}`. \
Add `generate_empty_typed_flags {n}` before this command."

  -- Type edges: the canonical edge list of the `k`-vertex graph with index `m`.
  let typeEdgesStx ← `(FlagAlgebras.Compute.genCanonicalEdgeLists $(Quote.quote k))
  let allTypeEdges ← liftTermElabM do
    let valExpr ← Lean.Elab.Term.elabTermAndSynthesize typeEdgesStx none
    let valExpr ← instantiateMVars valExpr
    let typeExpr ← Lean.Meta.inferType valExpr
    evalNatPairLists typeExpr valExpr
  let typeEdges := allTypeEdges[m]!

  -- Flag data, in JSON order:
  -- `(underlyingGraphIdx, canonicalUnderlyingEdges, typeIndices, coeffNum, coeffDen)`.
  let flagDataStx ← `(FlagAlgebras.Compute.genFlagData
      $(Quote.quote k) $(Quote.quote m) $(Quote.quote n))
  let flagData ← liftTermElabM do
    let valExpr ← Lean.Elab.Term.elabTermAndSynthesize flagDataStx none
    let valExpr ← instantiateMVars valExpr
    let typeExpr ← Lean.Meta.inferType valExpr
    evalFlagData typeExpr valExpr
  let count := flagData.length

  let typeName := mkIdent (Name.mkSimple s!"Sym2FlagType_{k}_{m}")
  let flagTypeName := mkIdent (Name.mkSimple s!"FlagType_{k}_{m}")

  let typeEdgesTerm ← natPairsToEdgesTerm k typeEdges
  elabUnlessDefined typeName.getId (← `(
      def $typeName : Sym2FlagType $(Quote.quote k) where
        edges := mkEdgeFinset $(Quote.quote k) $typeEdgesTerm
        edges_valid := mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])
    ))

  elabUnlessDefined flagTypeName.getId (← `(
      def $flagTypeName := (($typeName : Sym2FlagType $(Quote.quote k))).toFlagType
    ))

  let typeTerm ← `(($typeName : Sym2FlagType $(Quote.quote k)))

  for i in [0:count] do
    let entry := flagData[i]!
    let underlyingIdx := entry.1
    let graphEdges := entry.2.1
    let typeIndices := entry.2.2.1

    let labeledName := mkIdent (Name.mkSimple s!"Sym2LabeledGraph_{n}_{k}_{m}_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{m}_{i}")

    let edgesTerm ← natPairsToEdgesTerm n graphEdges
    let idxFinExpr ← mkTypeIndexFinExpr typeIndices.toArray n

    elabUnlessDefined labeledName.getId (← `(
        def $labeledName : Sym2LabeledGraph $typeTerm $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])
          type_embed := by
            let e : (Fin $(Quote.quote k)) ↪ (Fin $(Quote.quote n)) :=
              ⟨
                (fun i : Fin $(Quote.quote k) => $idxFinExpr),
                by decide
              ⟩
            have hmap : ∀ u v,
                (SimpleGraph.fromEdgeSet ((mkEdgeFinset $(Quote.quote n) $edgesTerm : Finset (Sym2 (Fin $(Quote.quote n)))) : Set (Sym2 (Fin $(Quote.quote n))))).Adj (e u) (e v)
                ↔
                (SimpleGraph.fromEdgeSet ((($typeTerm).edges : Finset (Sym2 (Fin $(Quote.quote k)))) : Set (Sym2 (Fin $(Quote.quote k))))).Adj u v := by
              decide
            refine ⟨e, ?_⟩
            exact hmap _ _
      ))

    elabUnlessDefined flagName.getId (← `(
        def $flagName : Sym2Flag $typeTerm $(Quote.quote n) :=
          Quotient.mk (sym2LabeledGraphSetoid $typeTerm $(Quote.quote n)) $labeledName
      ))

    elabUnlessDefined flagBridgeName.getId (← `(
        def $flagBridgeName := ($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag
      ))

    elabUnlessDefined flagAlgebraName.getId (← `(
        noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra $flagTypeName :=
          ⟦FlagAlgebras.basisVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
      ))

    let unlabelThmName := mkIdent (Name.mkSimple s!"unlabel_{n}_{k}_{m}_{i}")
    let baseFlagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{underlyingIdx}")

    elabUnlessDefined unlabelThmName.getId (← `(
        @[simp]
        theorem $unlabelThmName : FlagAlgebras.unlabel $flagBridgeName = $baseFlagName := by
          exact Quotient.sound (FlagAlgebras.flagEqv.refl _)
      ))

  -- Batch the per-flag downward normalizing factors into ONE `native_decide`
  -- (previously one `native_decide` *per flag*, i.e. `count` compile-to-native
  -- invocations). Each `downward_…_i` below extracts its own factor from this
  -- single list equality by cheap kernel reduction (`List.getD`), so the whole
  -- `generate_flags` call compiles a decision procedure to native code once.
  let downwardFactorsEqName := mkIdent (Name.mkSimple s!"downwardFactors_{n}_{k}_{m}_eq")
  let mut dnfTerms : Array (TSyntax `term) := #[]
  let mut coeffTerms : Array (TSyntax `term) := #[]
  for i in [0:count] do
    let entry := flagData[i]!
    let coeffNum := entry.2.2.2.1
    let coeffDen := entry.2.2.2.2
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    dnfTerms := dnfTerms.push (←
      `(FlagAlgebras.Compute.downwardNormalizingFactor_Sym2Flag
          ($flagName : Sym2Flag $typeTerm $(Quote.quote n))))
    coeffTerms := coeffTerms.push (← coeffQTerm coeffNum coeffDen)

  elabUnlessDefined downwardFactorsEqName.getId (← `(
      theorem $downwardFactorsEqName :
          ([ $dnfTerms,* ] : List ℚ) = [ $coeffTerms,* ] := by
        native_decide
    ))

  for i in [0:count] do
    let entry := flagData[i]!
    let underlyingIdx := entry.1
    let coeffNum := entry.2.2.2.1
    let coeffDen := entry.2.2.2.2

    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{m}_{i}")

    let coeffQ ← coeffQTerm coeffNum coeffDen
    let coeffR ← `(($coeffQ : ℝ))

    let downwardThmName := mkIdent (Name.mkSimple s!"downward_{n}_{k}_{m}_{i}")
    let baseFlagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{underlyingIdx}")
    let baseFlagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{underlyingIdx}")

    elabUnlessDefined downwardThmName.getId (← `(
        @[simp]
        theorem $downwardThmName
            : ⟦$flagAlgebraName⟧₀ = $coeffR • $baseFlagAlgebraName
          := by
          have hdnf : FlagAlgebras.downwardNormalizingFactor $flagBridgeName = $coeffQ := by
            change FlagAlgebras.downwardNormalizingFactor (($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag) = $coeffQ
            rw [FlagAlgebras.Compute.downwardNormalizingFactor_eq]
            exact congrArg (fun l => l.getD $(Quote.quote i) (0 : ℚ)) $downwardFactorsEqName
          change
            FlagAlgebras.downwardFlagVectorQuot (FlagAlgebras.basisVector ⟨$(Quote.quote n), $flagBridgeName⟩)
              =
            $coeffR • (⟦FlagAlgebras.basisVector ⟨$(Quote.quote n), $baseFlagName⟩⟧ : FlagAlgebras.FlagAlgebra ∅ₜ)
          apply Quotient.sound
          simp [FlagAlgebras.downwardFlagVector, FlagAlgebras.downwardFlag, linearExtension, hdnf]
      ))

  let setName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_{k}_{m}")
  let setEqUnivName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_{k}_{m}_eq_univ")
  let flagTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}") : TSyntax `term))

  elabUnlessDefined setName.getId (← `(
      def $setName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset
    ))

  -- Positional list bridge: the named flag list equals `genFlagsOrdered σ n` (the
  -- dedup reps re-sorted into `genFlagData`'s JSON order). Deciding this *list*
  -- equality costs O(g) isomorphism checks (one per position), versus the O(g²) the
  -- `Finset`/`toFinset` route forces. `genFlagsOrdered_perm` then transfers `= univ`
  -- (through `genFlagSet_eq_univ`) and `Nodup` (through `genFlags_nodup`) by proof —
  -- so this single O(g) `native_decide` replaces the previous *two* O(g²) ones (the
  -- `Finset`-equality `= univ` bridge and the separate `Nodup` check). Both lemmas
  -- below rewrite through it, then close via the math theorems on `genFlags`.
  let flagListEqName := mkIdent (Name.mkSimple s!"Sym2FlagList_{n}_{k}_{m}_eq")
  elabUnlessDefined flagListEqName.getId (← `(
      theorem $flagListEqName :
          ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n)))
            = FlagAlgebras.Compute.genFlagsOrdered $typeTerm $(Quote.quote n) := by
        native_decide
    ))

  elabUnlessDefined setEqUnivName.getId (← `(
      theorem $setEqUnivName : $setName = Finset.univ := by
        have h : $setName = FlagAlgebras.Compute.genFlagSet $typeTerm $(Quote.quote n) := by
          have hfl := $flagListEqName
          show (([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset)
              = FlagAlgebras.Compute.genFlagSet $typeTerm $(Quote.quote n)
          rw [hfl]
          exact FlagAlgebras.Compute.genFlagsOrdered_toFinset $typeTerm $(Quote.quote n)
        rw [h]
        exact FlagAlgebras.Compute.genFlagSet_eq_univ $typeTerm $(Quote.quote n)
    ))

  let flagSetName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}")
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}_val_eq")
  let flagSetEqUnivName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}_eq_univ")
  let flagBridgeTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}") : TSyntax `term))

  emitFlagSetMachinery n
    (← `($flagTypeName))
    (← `(Sym2Flag $typeTerm $(Quote.quote n)))
    (← `(Sym2Flag.toFlag))
    (← `(Sym2Flag.toFlag_injective))
    (← `(by
        intro F
        exact ⟨F.toSym2Flag, FlagAlgebras.Flag.toSym2Flag_toFlag_eq F⟩))
    (← `(by
        have hfl := $flagListEqName
        rw [hfl]
        exact FlagAlgebras.Compute.genFlagsOrdered_nodup $typeTerm $(Quote.quote n)))
    flagTerms flagBridgeTerms
    setName setEqUnivName flagSetName flagSetValEqName flagSetEqUnivName

  logInfo s!"Generated `{typeName.getId}` and {count} flags as `Sym2Flag_{n}_{k}_{m}_i` (no JSON)."
