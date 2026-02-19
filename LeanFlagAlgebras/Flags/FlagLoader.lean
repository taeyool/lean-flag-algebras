import «LeanFlagAlgebras».Compute.Basic
import Lean.Data.Json
import Mathlib.Tactic

open Sym2 Lean Elab Command Json
open Compute

------------------------------------------------------------------
-- 1. Helpers for Type Inference and Graph Creation
------------------------------------------------------------------

-- Helper to convert a List to a Finset for easier type inference
def mkEdgeFinset (n : ℕ) (l : List (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  l.toFinset

-- Helper to create the type graph (SimpleGraph) from a Finset of edges
def create_type_graph {k : ℕ} (edges : Finset (Sym2 (Fin k))) : SimpleGraph (Fin k) :=
  SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Fin k)))

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

/--
  Reads a JSON file to automatically generate the Type graph and all associated Flags.
  Usage: load_flags_with_type "filename.json" prefix
-/
elab "load_flags_with_type" filename:str prefix_name:ident : command => do
  let path := filename.getString
  let fileContent ← liftIO $ IO.FS.readFile path
  let json ← match Json.parse fileContent with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let jsonNumberToNat? (x : JsonNumber) : Option Nat :=
    if x.exponent = 0 then
      x.mantissa.toNat?
    else
      none

  -- Extract data from the JSON dictionary
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

  let flagsJson ← match json.getObjVal? "flags" with
    | Except.ok (.arr val) => pure val
    | _ => throwError "Failed to parse 'flags'"

  if ¬ (k ≤ n) then
    throwError s!"Expected k ≤ n, but got k={k} and n={n}"

  -- 1. Create the Type graph (Name: prefix_type)
  let typeName := mkIdent (Name.mkSimple s!"{prefix_name.getId}_type")
  let typeEdgesTerm ← jsonEdgesToTerm k typeEdgesJson

  elabCommand (← `(
    def $typeName : FlagAlgebras.FlagType (Fin $(Quote.quote k)) :=
      create_type_graph (mkEdgeFinset $(Quote.quote k) $typeEdgesTerm)
  ))

  -- 2. Create each Flag (Name: prefix_0, prefix_1 ...)
  for i in [0:flagsJson.size] do
    let flagEdges := flagsJson[i]!
    let labeledName := mkIdent (Name.mkSimple s!"{prefix_name.getId}_{i}_labeled")
    let flagName    := mkIdent (Name.mkSimple s!"{prefix_name.getId}_{i}")

    let edgesTerm ← jsonEdgesToTerm n flagEdges

    -- Define LabeledSym2Graph
    -- (The proof for `type_embed` is left as `sorry` to be filled with your custom tactic later)
    elabCommand (← `(
      noncomputable def $labeledName : LabeledSym2Graph $typeName $(Quote.quote n) where
        edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
        edges_valid := by decide
        type_embed := by sorry
    ))

    -- Define Sym2Flag (Quotient)
    elabCommand (← `(
      noncomputable def $flagName : Sym2Flag $typeName $(Quote.quote n) :=
        Quotient.mk (labeledSym2GraphSetoid $typeName $(Quote.quote n)) $labeledName
    ))

  logInfo s!"Loaded type graph `{typeName.getId}` and {flagsJson.size} flags as `{prefix_name.getId}_N`."

------------------------------------------------------------------
-- 3. Execution Example
------------------------------------------------------------------

-- Passing just the JSON file will define everything automatically.
load_flags_with_type "LeanFlagAlgebras/Flags/Flags/flags_4_2_1.json" flag_4_2_1

-- Verification
#check flag_4_2_1_type       -- FlagType (Fin 2)
#check flag_4_2_1_0_labeled  -- LabeledSym2Graph flag_4_2_1_type 4
#check flag_4_2_1_0          -- Sym2Flag flag_4_2_1_type 4
