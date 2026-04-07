import «LeanFlagAlgebras».FlagAlgebra.Compute.Downward
import Lean.Data.Json
import Mathlib.Tactic

open Sym2 Lean Elab Command Json
open FlagAlgebras.Compute

structure EmptyTypedJsonData where
  n : ℕ
  graphsJson : Array Json

structure FlagEntry where
  underlyingGraphNum : Nat
  edgesJson : Json
  typeIndices : Array Nat
  downwardCoeffNum : Nat
  downwardCoeffDen : Nat
deriving Inhabited

structure FlagJsonData where
  n : ℕ
  k : ℕ
  m : ℕ
  typeEdgesJson : Json
  flags : Array FlagEntry

def jsonNumberToNat? (x : JsonNumber) : Option Nat :=
  if x.exponent = 0 then
    x.mantissa.toNat?
  else
    none

def mkEdgeFinset (n : ℕ) (l : List (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  l.toFinset

def jsonEdgesToTerm (numVerts : ℕ) (edgesJson : Json) : CommandElabM (TSyntax `term) := do
  let .arr edgeArr := edgesJson | throwError "Edges must be an array"
  let terms ← edgeArr.mapM fun edgeJson => do
    let .arr #[.num u, .num v] := edgeJson | throwError "Edge must be [u, v]"
    let some uNat := jsonNumberToNat? u | throwError "Edge endpoint must be a natural number"
    let some vNat := jsonNumberToNat? v | throwError "Edge endpoint must be a natural number"
    `(Sym2.mk (($(Quote.quote uNat) : Fin $(Quote.quote numVerts)), ($(Quote.quote vNat) : Fin $(Quote.quote numVerts))))
  `([ $terms,* ])

def parseNFromGraphsPath (path : System.FilePath) : CommandElabM Nat := do
  let some fileName := path.fileName
    | throwError s!"Could not extract filename from path: {path}"
  if !(fileName.startsWith "graphs_") || !(fileName.endsWith ".json") then
    throwError s!"Expected filename of the form graphs_n.json, but got: {fileName}"
  let nSlice := (fileName.drop 7).dropEnd 5
  let n ← match nSlice.toNat? with
    | some v => pure v
    | none => throwError s!"Failed to parse n from filename: {fileName}"
  pure n

def parseCoeffString (s : String) : CommandElabM (Nat × Nat) := do
  let parts := (s.trimAscii.toString).splitOn "/"
  match parts with
  | [numStr] =>
      let num ← match numStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid downward_coeff numerator: {numStr}"
      pure (num, 1)
  | [numStr, denStr] =>
      let num ← match numStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid downward_coeff numerator: {numStr}"
      let den ← match denStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid downward_coeff denominator: {denStr}"
      if den = 0 then
        throwError "downward_coeff denominator cannot be zero"
      pure (num, den)
  | _ => throwError s!"Invalid downward_coeff format: {s}"

def parseTypeIndices (j : Json) : CommandElabM (Array Nat) := do
  let arr ← match j with
    | .arr a => pure a
    | _ => throwError "Expected 'type_indices' to be an array"
  arr.mapM fun idxJson => do
    let x ← match idxJson with
      | .num v => pure v
      | _ => throwError "Each type index must be a natural number"
    let n ← match jsonNumberToNat? x with
      | some v => pure v
      | none => throwError "Each type index must be a natural number"
    pure n

def mkTypeIndexNatExpr (typeIndices : Array Nat) : CommandElabM (TSyntax `term) := do
  if _h : typeIndices.size = 0 then
    throwError "type_indices must be nonempty for load_flags"
  let lastIdx := typeIndices[typeIndices.size - 1]!
  let mut acc : TSyntax `term := ← `($(Quote.quote lastIdx))
  for j in (List.range (typeIndices.size - 1)).reverse do
    let idx := typeIndices[j]!
    acc ← `(if i.1 = $(Quote.quote j) then $(Quote.quote idx) else $acc)
  pure acc

def parseEmptyTypedJsonFile (path : System.FilePath) : CommandElabM EmptyTypedJsonData := do
  let fileContent ← liftIO <| IO.FS.readFile path
  let json ← match Json.parse fileContent with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"
  let .arr graphsJson := json | throwError "Expected top-level JSON array in graphs_n.json"
  let n ← parseNFromGraphsPath path
  pure { n := n, graphsJson := graphsJson }

def parseFlagJsonFile (path : System.FilePath) : CommandElabM FlagJsonData := do
  let fileContent ← liftIO <| IO.FS.readFile path
  let json ← match Json.parse fileContent with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let n ← match json.getObjVal? "n" with
    | Except.ok (.num val) =>
        match jsonNumberToNat? val with
        | some n => pure n
        | none => throwError "Failed to parse 'n' as Nat"
    | _ => throwError "Failed to parse 'n'"

  let k ← match json.getObjVal? "k" with
    | Except.ok (.num val) =>
        match jsonNumberToNat? val with
        | some k => pure k
        | none => throwError "Failed to parse 'k' as Nat"
    | _ => throwError "Failed to parse 'k'"

  let m ← match json.getObjVal? "type_num" with
    | Except.ok (.num val) =>
        match jsonNumberToNat? val with
        | some m => pure m
        | none => throwError "Failed to parse 'type_num' as Nat"
    | _ => throwError "Failed to parse 'type_num'"

  let typeEdgesJson ← match json.getObjVal? "type_edges" with
    | Except.ok val => pure val
    | _ => throwError "Failed to parse 'type_edges'"

  let flagsRaw ← match json.getObjVal? "flags" with
    | Except.ok (.arr val) => pure val
    | _ => throwError "Failed to parse 'flags'"

  let flags ← flagsRaw.mapM fun flagJson => do
    let underlyingGraphNum ← match flagJson.getObjVal? "underlying_graph_num" with
      | Except.ok (.num val) =>
          match jsonNumberToNat? val with
          | some idx => pure idx
          | none => throwError "Failed to parse 'underlying_graph_num' as Nat"
      | _ => throwError "Missing or invalid 'underlying_graph_num'"

    let edgesJson ← match flagJson.getObjVal? "edges" with
      | Except.ok val => pure val
      | _ => throwError "Missing or invalid 'edges'"

    let typeIndicesJson ← match flagJson.getObjVal? "type_indices" with
      | Except.ok val => pure val
      | _ => throwError "Missing or invalid 'type_indices'"
    let typeIndices ← parseTypeIndices typeIndicesJson

    let downwardCoeffStr ← match flagJson.getObjVal? "downward_coeff" with
      | Except.ok (.str s) => pure s
      | _ => throwError "Missing or invalid 'downward_coeff'"
    let coeff ← parseCoeffString downwardCoeffStr
    let num := coeff.1
    let den := coeff.2

    if typeIndices.size ≠ k then
      throwError s!"Expected type_indices of length {k}, but got {typeIndices.size}"

    for idx in typeIndices do
      if !(idx < n) then
        throwError s!"type index out of range: {idx} is not < {n}"

    if typeIndices.toList.toFinset.card ≠ typeIndices.size then
      throwError "type_indices must be pairwise distinct"

    pure {
      underlyingGraphNum := underlyingGraphNum
      edgesJson := edgesJson
      typeIndices := typeIndices
      downwardCoeffNum := num
      downwardCoeffDen := den
    }

  if ¬ (k ≤ n) then
    throwError s!"Expected k ≤ n, but got k={k} and n={n}"

  pure {
    n := n
    k := k
    m := m
    typeEdgesJson := typeEdgesJson
    flags := flags
  }

def coeffQTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `((($(Quote.quote num) : Nat) : Rat))
  else
    `((($(Quote.quote num) : Rat) / ($(Quote.quote den) : Rat)))

elab "load_empty_typed_flags" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data ← parseEmptyTypedJsonFile path

  let n := data.n
  let graphsJson := data.graphsJson

  for i in [0:graphsJson.size] do
    let graphEdgesJson := graphsJson[i]!
    let graphName := mkIdent (Name.mkSimple s!"Sym2Graph_{n}_0_0_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{i}")
    let edgesTerm ← jsonEdgesToTerm n graphEdgesJson

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
    (List.range graphsJson.size).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}") : TSyntax `term))

  let env ← getEnv
  if ¬ env.contains setName.getId then
    elabCommand (← `(
      def $setName : Finset (Sym2EmptyTypedFlag $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset
    ))

  let env ← getEnv
  if ¬ env.contains setEqUnivName.getId then
    elabCommand (← `(
      theorem $setEqUnivName : $setName = Finset.univ := by
        native_decide
    ))

  let flagSetName := mkIdent (Name.mkSimple s!"flagSet_{n}_0_0")
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSet_{n}_0_0_val_eq")
  let flagSetEqUnivName := mkIdent (Name.mkSimple s!"flagSet_{n}_0_0_eq_univ")
  let flagBridgeTerms : Array (TSyntax `term) :=
    (List.range graphsJson.size).toArray.map (fun i =>
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
          native_decide
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

  logInfo s!"Loaded {graphsJson.size} empty-typed flags as `Sym2Flag_{n}_0_0_i`."

elab "load_flags" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data ← parseFlagJsonFile path

  let n := data.n
  let k := data.k
  let m := data.m
  let typeEdgesJson := data.typeEdgesJson
  let flags := data.flags

  let typeName := mkIdent (Name.mkSimple s!"Sym2FlagType_{k}_{m}")
  let flagTypeName := mkIdent (Name.mkSimple s!"FlagType_{k}_{m}")

  let env ← getEnv
  if ¬ env.contains typeName.getId then
    let typeEdgesTerm ← jsonEdgesToTerm k typeEdgesJson
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

  for i in [0:flags.size] do
    let entry := flags[i]!
    let graphEdges := entry.edgesJson
    let underlyingIdx := entry.underlyingGraphNum
    let typeIndices := entry.typeIndices
    let coeffNum := entry.downwardCoeffNum
    let coeffDen := entry.downwardCoeffDen

    let labeledName := mkIdent (Name.mkSimple s!"Sym2LabeledGraph_{n}_{k}_{m}_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{m}_{i}")

    let edgesTerm ← jsonEdgesToTerm n graphEdges
    let idxNatExpr ← mkTypeIndexNatExpr typeIndices

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
          have hunlabel : FlagAlgebras.unlabel $flagBridgeName = $baseFlagName := by
            exact $unlabelThmName
          have hdnf : FlagAlgebras.downwardNormalizingFactor $flagBridgeName = $coeffQ := by
            change FlagAlgebras.downwardNormalizingFactor (($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag) = $coeffQ
            rw [FlagAlgebras.Compute.downwardNormalizingFactor_eq]
            native_decide
          change
            FlagAlgebras.downwardFlagVectorQuot (FlagAlgebras.unitVector ⟨$(Quote.quote n), $flagBridgeName⟩)
              =
            $coeffR • (⟦FlagAlgebras.unitVector ⟨$(Quote.quote n), $baseFlagName⟩⟧ : FlagAlgebras.FlagAlgebra ∅ₜ)
          apply Quotient.sound
          simp [FlagAlgebras.downwardFlagVector, FlagAlgebras.downwardFlag, linearExtension, hunlabel, hdnf]
      ))

  let setName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_{k}_{m}")
  let setEqUnivName := mkIdent (Name.mkSimple s!"sym2FlagSet_{n}_{k}_{m}_eq_univ")
  let flagTerms : Array (TSyntax `term) :=
    (List.range flags.size).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}") : TSyntax `term))

  let env ← getEnv
  if ¬ env.contains setName.getId then
    elabCommand (← `(
      def $setName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset
    ))

  let env ← getEnv
  if ¬ env.contains setEqUnivName.getId then
    elabCommand (← `(
      theorem $setEqUnivName : $setName = Finset.univ := by
        native_decide
    ))

  let flagSetName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}")
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}_val_eq")
  let flagSetEqUnivName := mkIdent (Name.mkSimple s!"flagSet_{n}_{k}_{m}_eq_univ")
  let flagBridgeTerms : Array (TSyntax `term) :=
    (List.range flags.size).toArray.map (fun i =>
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

  logInfo s!"Loaded `{typeName.getId}` and {flags.size} flags as `Sym2Flag_{n}_{k}_{m}_i`."
