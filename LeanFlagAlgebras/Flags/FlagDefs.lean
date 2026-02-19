import «LeanFlagAlgebras».Compute.Basic
import Lean.Data.Json -- Required for JSON parsing

-- Open necessary namespaces for metaprogramming and graph theory
open Sym2 Lean Elab Command Json
open Compute

namespace ErdosPentagon

------------------------------------------------------------------
-- 1. Core Structure Definitions
------------------------------------------------------------------

-- Constructor helper to create a LabeledSym2Graph on EmptyType
@[simp]
def create_emptyType_labeledSym2Graph {ℓ : ℕ}
      (edges : Finset (Sym2 (Fin ℓ))) (h : ∀ e ∈ edges, ¬e.IsDiag)
      : LabeledSym2Graph ∅ₜ ℓ where
  edges := edges
  edges_valid := h
  type_embed := RelEmbedding.ofIsEmpty _ _

-- Helper function to convert a List of edges to a Finset
-- This helps Lean infer types correctly when constructing terms
def mkEdgeFinset (n : ℕ) (l : List (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  l.toFinset

------------------------------------------------------------------
-- 2. Metaprogramming: JSON Loader & Definition Generator
------------------------------------------------------------------

/--
  Parses a JSON array of edges (e.g., [[0,1], [2,3]]) into a Lean Syntax Term.
  Returns a syntax representing `[s(0,1), s(2,3)]` with explicit `Fin n` types.
-/
def jsonEdgesToTerm (n : ℕ) (edgesJson : Json) : CommandElabM (TSyntax `term) := do
  let .arr edgeArr := edgesJson | throwError "Edges must be a JSON array"

  let jsonNumberToNat? (x : JsonNumber) : Option Nat :=
    if x.exponent = 0 then
      x.mantissa.toNat?
    else
      none

  -- Map over the JSON array to create a list of syntax terms
  let terms ← edgeArr.mapM fun edgeJson => do
    -- Parse [u, v]
    let .arr #[.num u, .num v] := edgeJson | throwError "Edge must be [u, v]"
    let some uNat := jsonNumberToNat? u | throwError "Edge endpoint must be a natural number"
    let some vNat := jsonNumberToNat? v | throwError "Edge endpoint must be a natural number"

    -- Construct the syntax `Sym2.mk ((u : Fin n), (v : Fin n))`
    -- Explicit type annotation `( ... : Fin n)` is crucial for elaboration.
    `(Sym2.mk (($(Quote.quote uNat) : Fin $(Quote.quote n)), ($(Quote.quote vNat) : Fin $(Quote.quote n))))

  -- Wrap the terms in a list syntax `[ ... ]`
  let listTerm ← `([ $terms,* ])
  return listTerm

/--
  Custom command to load graph data from a JSON file.
  Usage: load_graph_atlas "filename.json"

  Effect:
  Reads the file, parses the JSON, and automatically generates definitions in the current environment.
-/
elab "load_graph_atlas" filename:str : command => do
  let path := filename.getString

  -- Read file content (IO action lifted to CommandElabM)
  let fileContent ← liftIO $ IO.FS.readFile path

  -- Parse JSON content
  let json ← match Json.parse fileContent with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"
  let .arr graphs := json | throwError "JSON root must be an array of graphs"

  -- Hardcoded vertex count for this specific atlas subset
  let n := 5

  -- Iterate through each graph in the JSON array
  for i in [0:graphs.size] do
    let graphEdges := graphs[i]!
    let graphName := mkIdent (Name.mkSimple s!"LabeledSym2Graph_{n}_0_0_{i+1}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i+1}")

    -- Convert JSON edges to Lean syntax
    let edgesTerm ← jsonEdgesToTerm n graphEdges

    -- Generate the `def` command programmatically
    -- Logic: def graph_i : ... := create_... (mkEdgeFinset ...) (by decide)
    elabCommand (← `(
      def $graphName : LabeledSym2Graph ∅ₜ $(Quote.quote n) :=
        create_emptyType_labeledSym2Graph
          (mkEdgeFinset $(Quote.quote n) $edgesTerm)
          (by decide) -- Automatically prove that edges are valid (no loops)
    ))

    elabCommand (← `(
      def $flagName : Sym2Flag ∅ₜ $(Quote.quote n) :=
        ⟦$graphName⟧
    ))

  logInfo s!"Successfully loaded and defined {graphs.size} LabeledSym2Graph and Sym2Flag pairs from {path}."

------------------------------------------------------------------
-- 3. Execution
------------------------------------------------------------------

-- Trigger the loading process.
-- This will generate `LabeledSym2Graph_5_0_0_1` through `LabeledSym2Graph_5_0_0_34`.
-- It also generates `Sym2Flag_5_0_0_1` through `Sym2Flag_5_0_0_34`.
load_graph_atlas "LeanFlagAlgebras/Flags/graphs_5.json"

-- Verification: Check the type of the first and last generated graph
#check LabeledSym2Graph_5_0_0_1
#check LabeledSym2Graph_5_0_0_34

#check Sym2Flag_5_0_0_1
#check Sym2Flag_5_0_0_34

instance : DecidableRel ∅ₜ.Adj := by
  intro a b
  exact .isFalse (by aesop)

def Sym2FlagSet_5_0_0 : Finset (Sym2Flag ∅ₜ 5) where
  val := [Sym2Flag_5_0_0_1, Sym2Flag_5_0_0_2,
          Sym2Flag_5_0_0_3, Sym2Flag_5_0_0_4,
          Sym2Flag_5_0_0_5, Sym2Flag_5_0_0_6, Sym2Flag_5_0_0_7, Sym2Flag_5_0_0_8,
          Sym2Flag_5_0_0_9, Sym2Flag_5_0_0_10, Sym2Flag_5_0_0_11, Sym2Flag_5_0_0_12,
          Sym2Flag_5_0_0_13, Sym2Flag_5_0_0_14, Sym2Flag_5_0_0_15, Sym2Flag_5_0_0_16,
          Sym2Flag_5_0_0_17, Sym2Flag_5_0_0_18, Sym2Flag_5_0_0_19, Sym2Flag_5_0_0_20,
          Sym2Flag_5_0_0_21, Sym2Flag_5_0_0_22, Sym2Flag_5_0_0_23, Sym2Flag_5_0_0_24,
          Sym2Flag_5_0_0_25, Sym2Flag_5_0_0_26, Sym2Flag_5_0_0_27, Sym2Flag_5_0_0_28,
          Sym2Flag_5_0_0_29, Sym2Flag_5_0_0_30, Sym2Flag_5_0_0_31, Sym2Flag_5_0_0_32,
          Sym2Flag_5_0_0_33, Sym2Flag_5_0_0_34]
  nodup := by native_decide

theorem Sym2FlagSet_5_0_0_eq_univ : Sym2FlagSet_5_0_0 = Finset.univ
  := by
  native_decide
