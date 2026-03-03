import «LeanFlagAlgebras».FlagAlgebra.Compute.Basic
import Lean.Data.Json
import Mathlib.Tactic

open Sym2 Lean Elab Command Json
open FlagAlgebras.Compute

structure FlagJsonData where
  n : ℕ
  k : ℕ
  typeEdgesJson : Json
  typeEdgeCount : Nat
  flagsJson : Array Json

------------------------------------------------------------------
-- 1. Helpers for Type Inference and Graph Creation
------------------------------------------------------------------

-- Helper to convert a List to a Finset for easier type inference
def mkEdgeFinset (n : ℕ) (l : List (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  l.toFinset

------------------------------------------------------------------
-- 2. Metaprogramming (JSON Parsing & Auto-Generation)
------------------------------------------------------------------

/--
  Converts a JSON array of edges into a Lean Syntax Term.
-/
def jsonEdgesToTerm (num_verts : ℕ) (edgesJson : Json) : CommandElabM (TSyntax `term) := do
  let .arr edgeArr := edgesJson | throwError "Edges must be an array"
  let jsonNumberToNat? (x : JsonNumber) : Option Nat :=
    if x.exponent = 0 then
      x.mantissa.toNat?
    else
      none
  let terms ← edgeArr.mapM fun edgeJson => do
    let .arr #[.num u, .num v] := edgeJson | throwError "Edge must be [u, v]"
    let some uNat := jsonNumberToNat? u | throwError "Edge endpoint must be a natural number"
    let some vNat := jsonNumberToNat? v | throwError "Edge endpoint must be a natural number"
    `(Sym2.mk (($(Quote.quote uNat) : Fin $(Quote.quote num_verts)), ($(Quote.quote vNat) : Fin $(Quote.quote num_verts))))
  `([ $terms,* ])

def parseFlagJsonFile (path : System.FilePath) : CommandElabM FlagJsonData := do
  let fileContent ← liftIO $ IO.FS.readFile path
  let json ← match Json.parse fileContent with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let jsonNumberToNat? (x : JsonNumber) : Option Nat :=
    if x.exponent = 0 then
      x.mantissa.toNat?
    else
      none

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

  let typeEdgesJson ← match json.getObjVal? "type_edges" with
    | Except.ok val => pure val
    | _ => throwError "Failed to parse 'type_edges'"

  let .arr typeEdgeArr := typeEdgesJson | throwError "Expected 'type_edges' to be an array"
  let typeEdgeCount := typeEdgeArr.size

  let flagsJson ← match json.getObjVal? "flags" with
    | Except.ok (.arr val) => pure val
    | _ => throwError "Failed to parse 'flags'"

  if ¬ (k ≤ n) then
    throwError s!"Expected k ≤ n, but got k={k} and n={n}"

  pure {
    n := n
    k := k
    typeEdgesJson := typeEdgesJson
    typeEdgeCount := typeEdgeCount
    flagsJson := flagsJson
  }

/--
  Reads a JSON file to generate flags, assuming the corresponding type is already defined.
  Usage: load_flags_with_type "filename.json"
-/
elab "load_flags" filename:str : command => do
  let path := filename.getString
  let data ← parseFlagJsonFile path

  let n := data.n
  let k := data.k
  let typeEdgesJson := data.typeEdgesJson
  let typeEdgeCount := data.typeEdgeCount
  let flagsJson := data.flagsJson

  let typeName := mkIdent (Name.mkSimple s!"Sym2FlagType_{k}_{typeEdgeCount}")
  let typeTerm ← `(($typeName : Sym2FlagType $(Quote.quote k)))

  -- 1. Create the Type definition only if it does not already exist.
  let env ← getEnv
  if ¬ env.contains typeName.getId then
    let typeEdgesTerm ← jsonEdgesToTerm k typeEdgesJson
    elabCommand (← `(
      def $typeName : Sym2FlagType $(Quote.quote k) where
        edges := mkEdgeFinset $(Quote.quote k) $typeEdgesTerm
        edges_valid := by decide
    ))

  let flagTypeName := mkIdent (Name.mkSimple s!"FlagType_{k}_{typeEdgeCount}")
  let env ← getEnv
  if ¬ env.contains flagTypeName.getId then
    elabCommand (← `(
      def $flagTypeName := ($typeTerm).toFlagType
    ))

  -- 2. Create each Flag
  for i in [0:flagsJson.size] do
    let flagEdges := flagsJson[i]!
    let graphName := mkIdent (Name.mkSimple s!"Sym2Graph_{n}_{k}_{typeEdgeCount}_{i}")
    let labeledName := mkIdent (Name.mkSimple s!"Sym2LabeledGraph_{n}_{k}_{typeEdgeCount}_{i}")
    let flagName    := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{typeEdgeCount}_{i}")

    let edgesTerm ← jsonEdgesToTerm n flagEdges

    if k = 0 then
      -- Define Sym2Graph (for empty type)
      elabCommand (← `(
        def $graphName : Sym2Graph $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := by decide
      ))

      -- Define Sym2EmptyTypedFlag (Quotient)
      elabCommand (← `(
        def $flagName : Sym2EmptyTypedFlag $(Quote.quote n) :=
          Quotient.mk (Sym2GraphSetoid $(Quote.quote n)) $graphName
      ))
    else
      -- Define Sym2LabeledGraph
      elabCommand (← `(
        def $labeledName : Sym2LabeledGraph $typeTerm $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := by decide
          type_embed := by
            let e : (Fin $(Quote.quote k)) ↪ (Fin $(Quote.quote n)) :=
              ⟨
                (fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 (by decide)⟩),
                by
                  intro a b h
                  have h' : a.1 = b.1 := by
                    simpa using congrArg (fun x : Fin $(Quote.quote n) => x.1) h
                  exact Fin.ext h'
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

      -- Define Sym2Flag (Quotient)
      elabCommand (← `(
        def $flagName : Sym2Flag $typeTerm $(Quote.quote n) :=
          Quotient.mk (sym2LabeledGraphSetoid $typeTerm $(Quote.quote n)) $labeledName
      ))

    -- Define Flag / FlagAlgebra bridge definitions
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{typeEdgeCount}_{i}")
    let env ← getEnv
    if ¬ env.contains flagBridgeName.getId then
      if k = 0 then
        elabCommand (← `(
          def $flagBridgeName := ($flagName : Sym2EmptyTypedFlag $(Quote.quote n)).toFlag
        ))
      else
        elabCommand (← `(
          def $flagBridgeName := ($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag
        ))

    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{typeEdgeCount}_{i}")
    let env ← getEnv
    if ¬ env.contains flagAlgebraName.getId then
      if k = 0 then
        elabCommand (← `(
          noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra ∅ₜ :=
            ⟦FlagAlgebras.unitVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
        ))
      else
        elabCommand (← `(
          noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra $flagTypeName :=
            ⟦FlagAlgebras.unitVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
        ))

  -- 3. Create Finset of all generated Sym2Flags + univ theorem
  let setName := mkIdent (Name.mkSimple s!"Sym2FlagSet_{n}_{k}_{typeEdgeCount}")
  let setEqUnivName := mkIdent (Name.mkSimple s!"Sym2FlagSet_{n}_{k}_{typeEdgeCount}_eq_univ")
  let flagTerms : Array (TSyntax `term) :=
    (List.range flagsJson.size).toArray.map (fun i =>
      (mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{typeEdgeCount}_{i}") : TSyntax `term))

  if k = 0 then
    elabCommand (← `(
      def $setName : Finset (Sym2EmptyTypedFlag $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset
    ))
  else
    elabCommand (← `(
      def $setName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $flagTerms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset
    ))

  elabCommand (← `(
    theorem $setEqUnivName : $setName = Finset.univ := by
      native_decide
  ))

  logInfo s!"Loaded `{typeName.getId}` and {flagsJson.size} flags as `Sym2Flag_{n}_{k}_{typeEdgeCount}_i`."

------------------------------------------------------------------
-- 3. Execution Example
------------------------------------------------------------------

-- Passing just the JSON file will define everything automatically.
-- load_flags "LeanFlagAlgebras/Flags/Flags/flags_4_2_1.json"

-- Verification
-- #check Sym2FlagType_2_1         -- Sym2FlagType 2
-- #check Sym2LabeledGraph_4_2_1_0 -- Sym2LabeledGraph Sym2FlagType_2_1 4
-- #check Sym2Flag_4_2_1_0         -- Sym2Flag Sym2FlagType_2_1 4
-- #check Sym2FlagSet_4_2_1        -- Finset (Sym2Flag Sym2FlagType_2_1 4)
-- #check Sym2FlagSet_4_2_1_eq_univ

-- load_flags "LeanFlagAlgebras/Flags/Flags/flags_5_3_1.json"

-- #print Sym2FlagSet_5_3_1
-- #check Sym2FlagSet_5_3_1_eq_univ
