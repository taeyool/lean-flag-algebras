import «LeanFlagAlgebras».FlagAlgebra.Compute.Downward
import «LeanFlagAlgebras».FlagAlgebra.Compute.Generate
import Mathlib.Tactic

/-! # Flag generation macros

This module defines the elaboration-time macros that turn the self-contained
Lean flag enumerations (`FlagAlgebra.Compute.Generate`) into named Lean
definitions and theorems, with no external JSON input:

* `generate_empty_typed_flags n` evaluates `genSym2Graphs n` (one canonical
  representative per isomorphism class of `n`-vertex graphs) at elaboration time
  and synthesizes, for each graph `i`, the constants `Sym2Graph_n_0_0_i`,
  `Sym2Flag_n_0_0_i`, `Flag_n_0_0_i`, `FlagAlgebra_n_0_0_i` (empty type ∅ₜ), plus
  the finset/`= univ` lemmas `Sym2FlagSet_n_0_0`, `flagSet_n_0_0`,
  `flagSet_n_0_0_val_eq`, `flagSet_n_0_0_eq_univ`.
* `generate_flags k m n` evaluates `genFlagData k m n` (the enumerated flags of
  the type σ given by the `k`-vertex graph with index `m`, in canonical order) at
  elaboration time and synthesizes the type constants `Sym2FlagType_k_m`,
  `FlagType_k_m`, and for each flag `i` the constants `Sym2LabeledGraph_n_k_m_i`,
  `Sym2Flag_n_k_m_i`, `Flag_n_k_m_i`, `FlagAlgebra_n_k_m_i`, the `simp` lemmas
  `unlabel_n_k_m_i` and `downward_n_k_m_i` (relating the labeled flag to its
  underlying empty-typed flag via the precomputed downward-normalizing
  coefficient), plus the corresponding finset/`= univ` lemmas.

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

/-- Build the term defining the type embedding `i ↦ typeIndices[i]` as a nested
`if i.1 = j then … else …` chain, used in the generated `type_embed` field. -/
def mkTypeIndexNatExpr (typeIndices : Array Nat) : CommandElabM (TSyntax `term) := do
  if _h : typeIndices.size = 0 then
    throwError "type_indices must be nonempty"
  let lastIdx := typeIndices[typeIndices.size - 1]!
  let mut acc : TSyntax `term := ← `($(Quote.quote lastIdx))
  for j in (List.range (typeIndices.size - 1)).reverse do
    let idx := typeIndices[j]!
    acc ← `(if i.1 = $(Quote.quote j) then $(Quote.quote idx) else $acc)
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

-- `generate_empty_typed_flags n`: evaluate the self-contained Lean enumeration
-- `genSym2Graphs n` (one canonical representative per isomorphism class) at
-- elaboration time and synthesize the named constants `Sym2Graph_n_0_0_i`,
-- `Sym2Flag_n_0_0_i`, `Flag_n_0_0_i`, `FlagAlgebra_n_0_0_i`, the finset defs and
-- the `… = Finset.univ` lemmas. `Sym2FlagSet_n_0_0_eq_univ` is discharged by the
-- mathematically-proved completeness theorem `genEmptyTypedFlagSet_eq_univ`
-- (bridged to the named list by a single cheap `native_decide` over the explicit
-- flag enumeration) rather than a `native_decide` over the entire quotient
-- `Fintype` via `Finset.univ`.
elab "generate_empty_typed_flags" nStx:num : command => do
  let n := nStx.getNat

  let edgesStx ← `((FlagAlgebras.Compute.genSym2Graphs $(Quote.quote n)).map
      FlagAlgebras.Compute.canonicalEdgeList)
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

    let env ← getEnv
    if ¬ env.contains graphName.getId then
      elabCommand (← `(
        def $graphName : Sym2Graph $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := by decide
      ))

    let env ← getEnv
    if ¬ env.contains flagName.getId then
      elabCommand (← `(
        def $flagName : Sym2EmptyTypedFlag $(Quote.quote n) :=
          Quotient.mk (Sym2GraphSetoid $(Quote.quote n)) $graphName
      ))

    let env ← getEnv
    if ¬ env.contains flagBridgeName.getId then
      elabCommand (← `(
        def $flagBridgeName := ($flagName : Sym2EmptyTypedFlag $(Quote.quote n)).toFlag
      ))

    let env ← getEnv
    if ¬ env.contains flagAlgebraName.getId then
      elabCommand (← `(
        noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra ∅ₜ :=
          ⟦FlagAlgebras.unitVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
      ))

  let setName := mkIdent (Name.mkSimple s!"Sym2FlagSet_{n}_0_0")
  let setEqUnivName := mkIdent (Name.mkSimple s!"Sym2FlagSet_{n}_0_0_eq_univ")
  let flagTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}") : TSyntax `term))
  let flagListEqName := mkIdent (Name.mkSimple s!"Sym2FlagList_{n}_0_0_eq")

  let env ← getEnv
  if ¬ env.contains setName.getId then
    elabCommand (← `(
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
  let env ← getEnv
  if ¬ env.contains flagListEqName.getId then
    elabCommand (← `(
      theorem $flagListEqName :
          ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n)))
            = FlagAlgebras.Compute.genEmptyTypedFlags $(Quote.quote n) := by
        native_decide
    ))

  let env ← getEnv
  if ¬ env.contains setEqUnivName.getId then
    elabCommand (← `(
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

  let env ← getEnv
  if ¬ env.contains flagSetName.getId then
    elabCommand (← `(
      def $flagSetName :=
        Finset.map { toFun := Sym2EmptyTypedFlag.toFlag, inj' := Sym2EmptyTypedFlag.toFlag_injective } $setName
    ))

  let env ← getEnv
  if ¬ env.contains flagSetValEqName.getId then
    elabCommand (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n))).val =
            [ $flagBridgeTerms,* ]) := by
        have hnodup :
            ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).Nodup := by
          have hfl := $flagListEqName
          rw [hfl]
          exact FlagAlgebras.Compute.genEmptyTypedFlags_nodup $(Quote.quote n)
        have hdedup :
            ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).dedup
              = ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))) := by
          exact List.Nodup.dedup hnodup
        have hright :
            (List.map Sym2EmptyTypedFlag.toFlag ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))))
              = [ $flagBridgeTerms,* ] := by
          rfl
        refine Quot.sound ?_
        have heq :
            List.map Sym2EmptyTypedFlag.toFlag
              (([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).dedup)
                = [ $flagBridgeTerms,* ] := by
          simpa [hdedup] using hright
        exact heq ▸ List.Perm.refl _
    ))

  let env ← getEnv
  if ¬ env.contains flagSetEqUnivName.getId then
    elabCommand (← `(
      theorem $flagSetEqUnivName : $flagSetName = Finset.univ := by
        change
          Finset.map { toFun := Sym2EmptyTypedFlag.toFlag, inj' := Sym2EmptyTypedFlag.toFlag_injective } $setName
            = Finset.univ
        have hs : $setName = Finset.univ := $setEqUnivName
        rw [hs]
        exact Finset.map_univ_of_surjective (f :=
          { toFun := Sym2EmptyTypedFlag.toFlag, inj' := Sym2EmptyTypedFlag.toFlag_injective })
          (by
            intro F
            exact ⟨F.toSym2EmptyTypedFlag, FlagAlgebras.Flag.toSym2EmptyTypedFlag_toFlag_eq F⟩)
    ))

  logInfo s!"Generated {count} empty-typed flags as `Sym2Flag_{n}_0_0_i` (n = {n})."

-- `generate_flags k m n`: evaluate the self-contained Lean enumeration
-- `genFlagData k m n` at elaboration time (one orbit representative per flag, in
-- canonical order) and synthesize the named constants `Sym2FlagType_k_m`,
-- `FlagType_k_m`, and per flag `Sym2LabeledGraph_n_k_m_i`, `Sym2Flag_n_k_m_i`,
-- `Flag_n_k_m_i`, `FlagAlgebra_n_k_m_i`, the `simp` lemmas `unlabel_n_k_m_i` /
-- `downward_n_k_m_i`, and the finset/`= univ` lemmas. The type's edges and each
-- flag's underlying edges are the canonical edge lists `canonicalEdgeList
-- (genSym2Graphs ·)`, so the generated `Sym2LabeledGraph`'s edge Finset matches
-- `Sym2Graph_n_0_0_j`'s exactly (preserving `unlabel`/`downward` defeq); the
-- downward coefficient is the reduced orbit ratio computed by `genFlagData` and
-- independently re-checked by the per-flag `native_decide`.
elab "generate_flags" kStx:num mStx:num nStx:num : command => do
  let k := kStx.getNat
  let m := mStx.getNat
  let n := nStx.getNat

  -- Type edges: the canonical edge list of the `k`-vertex graph with index `m`.
  let typeEdgesStx ← `((FlagAlgebras.Compute.genSym2Graphs $(Quote.quote k)).map
      FlagAlgebras.Compute.canonicalEdgeList)
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

  let env ← getEnv
  if ¬ env.contains typeName.getId then
    let typeEdgesTerm ← natPairsToEdgesTerm k typeEdges
    elabCommand (← `(
      def $typeName : Sym2FlagType $(Quote.quote k) where
        edges := mkEdgeFinset $(Quote.quote k) $typeEdgesTerm
        edges_valid := by decide
    ))

  let env ← getEnv
  if ¬ env.contains flagTypeName.getId then
    elabCommand (← `(
      def $flagTypeName := (($typeName : Sym2FlagType $(Quote.quote k))).toFlagType
    ))

  let typeTerm ← `(($typeName : Sym2FlagType $(Quote.quote k)))

  for i in [0:count] do
    let entry := flagData[i]!
    let underlyingIdx := entry.1
    let graphEdges := entry.2.1
    let typeIndices := entry.2.2.1
    let coeffNum := entry.2.2.2.1
    let coeffDen := entry.2.2.2.2

    let labeledName := mkIdent (Name.mkSimple s!"Sym2LabeledGraph_{n}_{k}_{m}_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{m}_{i}")

    let edgesTerm ← natPairsToEdgesTerm n graphEdges
    let idxNatExpr ← mkTypeIndexNatExpr typeIndices.toArray

    let env ← getEnv
    if ¬ env.contains labeledName.getId then
      elabCommand (← `(
        def $labeledName : Sym2LabeledGraph $typeTerm $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := by decide
          type_embed := by
            let e : (Fin $(Quote.quote k)) ↪ (Fin $(Quote.quote n)) :=
              ⟨
                (fun i : Fin $(Quote.quote k) =>
                  ⟨$idxNatExpr, by
                    fin_cases i <;> decide⟩),
                by
                  intro a b h
                  fin_cases a <;> fin_cases b <;> simp at h ⊢
              ⟩
            have hmap : ∀ u v,
                (SimpleGraph.fromEdgeSet ((mkEdgeFinset $(Quote.quote n) $edgesTerm : Finset (Sym2 (Fin $(Quote.quote n)))) : Set (Sym2 (Fin $(Quote.quote n))))).Adj (e u) (e v)
                ↔
                (SimpleGraph.fromEdgeSet ((($typeTerm).edges : Finset (Sym2 (Fin $(Quote.quote k)))) : Set (Sym2 (Fin $(Quote.quote k))))).Adj u v := by
              intro u v
              fin_cases u <;> fin_cases v <;> decide
            refine ⟨e, ?_⟩
            exact hmap _ _
      ))

    let env ← getEnv
    if ¬ env.contains flagName.getId then
      elabCommand (← `(
        def $flagName : Sym2Flag $typeTerm $(Quote.quote n) :=
          Quotient.mk (sym2LabeledGraphSetoid $typeTerm $(Quote.quote n)) $labeledName
      ))

    let env ← getEnv
    if ¬ env.contains flagBridgeName.getId then
      elabCommand (← `(
        def $flagBridgeName := ($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag
      ))

    let env ← getEnv
    if ¬ env.contains flagAlgebraName.getId then
      elabCommand (← `(
        noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra $flagTypeName :=
          ⟦FlagAlgebras.unitVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
      ))

    let coeffQ ← coeffQTerm coeffNum coeffDen
    let coeffR ← `(($coeffQ : ℝ))

    let downwardThmName := mkIdent (Name.mkSimple s!"downward_{n}_{k}_{m}_{i}")
    let unlabelThmName := mkIdent (Name.mkSimple s!"unlabel_{n}_{k}_{m}_{i}")

    let baseFlagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{underlyingIdx}")
    let baseFlagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{underlyingIdx}")

    let env ← getEnv
    if ¬ env.contains unlabelThmName.getId then
      elabCommand (← `(
        @[simp]
        theorem $unlabelThmName : FlagAlgebras.unlabel $flagBridgeName = $baseFlagName := by
          exact Quotient.sound (FlagAlgebras.flagEqv.refl _)
      ))

    let env ← getEnv
    if ¬ env.contains downwardThmName.getId then
      elabCommand (← `(
        @[simp]
        theorem $downwardThmName
            : ⟦$flagAlgebraName⟧₀ = $coeffR • $baseFlagAlgebraName
          := by
          have hdnf : FlagAlgebras.downwardNormalizingFactor $flagBridgeName = $coeffQ := by
            change FlagAlgebras.downwardNormalizingFactor (($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag) = $coeffQ
            rw [FlagAlgebras.Compute.downwardNormalizingFactor_eq]
            native_decide
          change
            FlagAlgebras.downwardFlagVectorQuot (FlagAlgebras.unitVector ⟨$(Quote.quote n), $flagBridgeName⟩)
              =
            $coeffR • (⟦FlagAlgebras.unitVector ⟨$(Quote.quote n), $baseFlagName⟩⟧ : FlagAlgebras.FlagAlgebra ∅ₜ)
          apply Quotient.sound
          simp [FlagAlgebras.downwardFlagVector, FlagAlgebras.downwardFlag, linearExtension, hdnf]
      ))

  let setName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_{k}_{m}")
  let setEqUnivName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_{k}_{m}_eq_univ")
  let flagTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}") : TSyntax `term))

  let env ← getEnv
  if ¬ env.contains setName.getId then
    elabCommand (← `(
      def $setName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset
    ))

  -- `sym2FlagSet_{n}_{k}_{m}_eq_univ` is discharged by the mathematically-proved
  -- completeness theorem `genFlagSet_eq_univ` (bridged to the named flag list by
  -- one cheap `native_decide` over the tight `genFlagSet` enumeration) rather than
  -- a `native_decide` that materialises `Finset.univ : Finset (Sym2Flag …)` via the
  -- full `Fintype (Sym2LabeledGraph σ n)` enumeration over all `2 ^ (C(n,2)+n)`
  -- edge subsets × embeddings.
  let env ← getEnv
  if ¬ env.contains setEqUnivName.getId then
    elabCommand (← `(
      theorem $setEqUnivName : $setName = Finset.univ := by
        have h : $setName = FlagAlgebras.Compute.genFlagSet $typeTerm $(Quote.quote n) := by
          native_decide
        rw [h]
        exact FlagAlgebras.Compute.genFlagSet_eq_univ $typeTerm $(Quote.quote n)
    ))

  let flagSetName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}")
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}_val_eq")
  let flagSetEqUnivName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}_eq_univ")
  let flagBridgeTerms : Array (TSyntax `term) :=
    (List.range count).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}") : TSyntax `term))

  let env ← getEnv
  if ¬ env.contains flagSetName.getId then
    elabCommand (← `(
      def $flagSetName :=
        Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } $setName
    ))

  let env ← getEnv
  if ¬ env.contains flagSetValEqName.getId then
    elabCommand (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n))).val =
            [ $flagBridgeTerms,* ]) := by
        have hnodup :
            ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).Nodup := by
          native_decide
        have hdedup :
            ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).dedup
              = ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))) := by
          exact List.Nodup.dedup hnodup
        have hright :
            (List.map Sym2Flag.toFlag ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))))
              = [ $flagBridgeTerms,* ] := by
          rfl
        refine Quot.sound ?_
        have heq :
            List.map Sym2Flag.toFlag
              (([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).dedup)
                = [ $flagBridgeTerms,* ] := by
          simpa [hdedup] using hright
        exact heq ▸ List.Perm.refl _
    ))

  let env ← getEnv
  if ¬ env.contains flagSetEqUnivName.getId then
    elabCommand (← `(
      theorem $flagSetEqUnivName : $flagSetName = Finset.univ := by
        change
          Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } $setName
            = Finset.univ
        have hs : $setName = Finset.univ := $setEqUnivName
        rw [hs]
        exact Finset.map_univ_of_surjective (f :=
          { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective })
          (by
            intro F
            exact ⟨F.toSym2Flag, FlagAlgebras.Flag.toSym2Flag_toFlag_eq F⟩)
    ))

  logInfo s!"Generated `{typeName.getId}` and {count} flags as `Sym2Flag_{n}_{k}_{m}_i` (no JSON)."
