import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import Lean.Data.Json
import Mathlib.Tactic

open Lean Elab Command Json
open FlagAlgebras
open FlagAlgebras.Compute

namespace Flags.Densities

structure DensityJsonData where
  hostTag : String
  patternTag : String
  densities : Array Json

structure TriangleFreeIndexJsonData where
  totalGraphs : Nat
  triangleFreeGraphIndices : Array Nat

structure K4FreeIndexJsonData where
  totalGraphs : Nat
  k4FreeGraphIndices : Array Nat

def jsonNumberToNat? (x : JsonNumber) : Option Nat :=
  if x.exponent = 0 then
    x.mantissa.toNat?
  else
    none

def parseNatFromJson (j : Json) (fieldName : String) : CommandElabM Nat := do
  let .num v := j | throwError s!"Expected Nat for {fieldName}"
  let some n := jsonNumberToNat? v
    | throwError s!"Expected natural number for {fieldName}"
  pure n

def parseNatArrayFromJson (j : Json) (fieldName : String) : CommandElabM (Array Nat) := do
  let arr ← match j with
    | .arr a => pure a
    | _ => throwError s!"Expected array for {fieldName}"
  arr.mapM fun x => parseNatFromJson x fieldName

def natArrayContains (arr : Array Nat) (x : Nat) : Bool :=
  arr.any fun y => y == x

def parseDensityString (s : String) : CommandElabM (Nat × Nat) := do
  let parts := (s.trimAscii.toString).splitOn "/"
  match parts with
  | [numStr] =>
      let num ← match numStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid density numerator: {numStr}"
      pure (num, 1)
  | [numStr, denStr] =>
      let num ← match numStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid density numerator: {numStr}"
      let den ← match denStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid density denominator: {denStr}"
      if den = 0 then
        throwError "Density denominator cannot be zero"
      pure (num, den)
  | _ =>
      throwError s!"Invalid density format: {s}"

def parseDensityJsonFile (path : System.FilePath) : CommandElabM DensityJsonData := do
  let content ← liftIO <| IO.FS.readFile path
  let json ← match Json.parse content with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let hostTag ← match json.getObjVal? "host" with
    | Except.ok (.str s) => pure s
    | _ => throwError "Missing or invalid field 'host'"

  let patternTag ← match json.getObjVal? "pattern" with
    | Except.ok (.str s) => pure s
    | _ => throwError "Missing or invalid field 'pattern'"

  let densities ← match json.getObjVal? "densities" with
    | Except.ok (.arr a) => pure a
    | _ => throwError "Missing or invalid field 'densities'"

  pure {
    hostTag := hostTag
    patternTag := patternTag
    densities := densities
  }

def parseNFromTriangleFreePath (path : System.FilePath) : CommandElabM Nat := do
  let some fileName := path.fileName
    | throwError s!"Could not extract filename from path: {path}"
  let suffix := "_triangle_free_indices.json"

  let nSlice? : Option String :=
    if fileName.startsWith "graphs_" && fileName.endsWith suffix then
      some <| ((fileName.drop 7).dropEnd suffix.length).toString
    else if fileName.startsWith "graph_" && fileName.endsWith suffix then
      some <| ((fileName.drop 6).dropEnd suffix.length).toString
    else
      none

  let some nSlice := nSlice?
    | throwError s!"Expected filename of the form graph_n_triangle_free_indices.json or graphs_n_triangle_free_indices.json, but got: {fileName}"
  let some n := nSlice.toNat?
    | throwError s!"Failed to parse n from filename: {fileName}"
  pure n

def parseTriangleFreeIndexJsonFile (path : System.FilePath) : CommandElabM TriangleFreeIndexJsonData := do
  let content ← liftIO <| IO.FS.readFile path
  let json ← match Json.parse content with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let totalGraphsJson ← match json.getObjVal? "total_graphs" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'total_graphs'"
  let totalGraphs ← parseNatFromJson totalGraphsJson "total_graphs"

  let triangleFreeJson ← match json.getObjVal? "triangle_free_graph_indices" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'triangle_free_graph_indices'"
  let triangleFreeGraphIndices ← parseNatArrayFromJson triangleFreeJson "triangle_free_graph_indices"

  pure {
    totalGraphs := totalGraphs
    triangleFreeGraphIndices := triangleFreeGraphIndices
  }

def parseNFromK4FreePath (path : System.FilePath) : CommandElabM Nat := do
  let some fileName := path.fileName
    | throwError s!"Could not extract filename from path: {path}"
  let suffix := "_k4_free_indices.json"

  let nSlice? : Option String :=
    if fileName.startsWith "graphs_" && fileName.endsWith suffix then
      some <| ((fileName.drop 7).dropEnd suffix.length).toString
    else if fileName.startsWith "graph_" && fileName.endsWith suffix then
      some <| ((fileName.drop 6).dropEnd suffix.length).toString
    else
      none

  let some nSlice := nSlice?
    | throwError s!"Expected filename of the form graph_n_k4_free_indices.json or graphs_n_k4_free_indices.json, but got: {fileName}"
  let some n := nSlice.toNat?
    | throwError s!"Failed to parse n from filename: {fileName}"
  pure n

def parseK4FreeIndexJsonFile (path : System.FilePath) : CommandElabM K4FreeIndexJsonData := do
  let content ← liftIO <| IO.FS.readFile path
  let json ← match Json.parse content with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let totalGraphsJson ← match json.getObjVal? "total_graphs" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'total_graphs'"
  let totalGraphs ← parseNatFromJson totalGraphsJson "total_graphs"

  let k4FreeJson ← match json.getObjVal? "k4_free_graph_indices" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'k4_free_graph_indices'"
  let k4FreeGraphIndices ← parseNatArrayFromJson k4FreeJson "k4_free_graph_indices"

  pure {
    totalGraphs := totalGraphs
    k4FreeGraphIndices := k4FreeGraphIndices
  }

def densityValueToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `($(Quote.quote num))
  else
    `((($(Quote.quote num) : Rat) / ($(Quote.quote den) : Rat)))

elab "load_flag_pair_density_theorems" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data ← parseDensityJsonFile path

  let mut generated : Nat := 0
  for row in data.densities do
    let .arr #[p1Json, p2Json, hJson, valJson] := row
      | throwError "Each density row must be [patternIdx1, patternIdx2, hostIdx, value]"

    let p1 ← parseNatFromJson p1Json "patternIdx1"
    let p2 ← parseNatFromJson p2Json "patternIdx2"
    let h ← parseNatFromJson hJson "hostIdx"

    let valStr ← match valJson with
      | .str s => pure s
      | _ => throwError "Density value must be a string"

    let densityPair ← parseDensityString valStr
    let num := densityPair.1
    let den := densityPair.2
    let rhsTerm ← densityValueToTerm num den

    let f1Name := mkIdent (Name.mkSimple s!"Flag_{data.patternTag}_{p1}")
    let f2Name := mkIdent (Name.mkSimple s!"Flag_{data.patternTag}_{p2}")
    let gName := mkIdent (Name.mkSimple s!"Flag_{data.hostTag}_{h}")
    let thmName := mkIdent (Name.mkSimple s!"flagDensity₂_Flag_{data.patternTag}_{p1}_Flag_{data.patternTag}_{p2}_Flag_{data.hostTag}_{h}")

    let env := (← getEnv)
    if ¬ env.contains f1Name.getId then
      throwError s!"Missing definition: {f1Name.getId}"
    if ¬ env.contains f2Name.getId then
      throwError s!"Missing definition: {f2Name.getId}"
    if ¬ env.contains gName.getId then
      throwError s!"Missing definition: {gName.getId}"

    if ¬ env.contains thmName.getId then
      elabCommand (← `(
        @[simp]
        theorem $thmName
            : flagDensity₂ $f1Name $f2Name $gName = $rhsTerm
          := by
          first | delta $f1Name $f2Name $gName | skip
          rw [flagDensity₂_eq_sym2FlagDensity₂]
          native_decide
      ))
      generated := generated + 1

  logInfo s!"Generated {generated} theorem(s) from density JSON: {filename.getString}"

elab "load_triangle_density_theorems" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let n ← parseNFromTriangleFreePath path
  let data ← parseTriangleFreeIndexJsonFile path

  for i in data.triangleFreeGraphIndices do
    if i >= data.totalGraphs then
      throwError s!"triangle_free_graph_indices contains out-of-range index {i} (total_graphs = {data.totalGraphs})"

  let mut generatedEqZero : Nat := 0
  let mut generatedNeZero : Nat := 0

  for i in [0:data.totalGraphs] do
    let flagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let isTriangleFree := natArrayContains data.triangleFreeGraphIndices i

    let env := (← getEnv)
    if ¬ env.contains flagName.getId then
      throwError s!"Missing definition: {flagName.getId}"

    if isTriangleFree then
      let thmName := mkIdent (Name.mkSimple s!"flagDensity1_K3_Flag_{n}_0_0_{i}_eq_zero")
      if ¬ env.contains thmName.getId then
        elabCommand (← `(
          @[simp]
          theorem $thmName
              : flagDensity₁ K3.toFinFlag.2 $flagName = 0
            := by
            rw [K3_toFinFlag_eq]
            unfold $flagName
            simp [Flag_3_0_0_3]
            rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
            native_decide
        ))
        generatedEqZero := generatedEqZero + 1
    else
      let thmName := mkIdent (Name.mkSimple s!"flagDensity1_K3_Flag_{n}_0_0_{i}_ne_zero")
      if ¬ env.contains thmName.getId then
        elabCommand (← `(
          @[simp]
          theorem $thmName
              : ¬ flagDensity₁ K3.toFinFlag.2 $flagName = 0
            := by
            rw [K3_toFinFlag_eq]
            unfold $flagName
            simp [Flag_3_0_0_3]
            rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
            native_decide
        ))
        generatedNeZero := generatedNeZero + 1

  logInfo s!"Generated triangle density theorems from {filename.getString}: eq_zero={generatedEqZero}, ne_zero={generatedNeZero}"

elab "load_k4_density_theorems" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let n ← parseNFromK4FreePath path
  let data ← parseK4FreeIndexJsonFile path

  for i in data.k4FreeGraphIndices do
    if i >= data.totalGraphs then
      throwError s!"k4_free_graph_indices contains out-of-range index {i} (total_graphs = {data.totalGraphs})"

  let mut generatedEqZero : Nat := 0
  let mut generatedNeZero : Nat := 0

  for i in [0:data.totalGraphs] do
    let flagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let isK4Free := natArrayContains data.k4FreeGraphIndices i

    let env := (← getEnv)
    if ¬ env.contains flagName.getId then
      throwError s!"Missing definition: {flagName.getId}"

    if isK4Free then
      let thmName := mkIdent (Name.mkSimple s!"flagDensity1_K4_Flag_{n}_0_0_{i}_eq_zero")
      if ¬ env.contains thmName.getId then
        elabCommand (← `(
          @[simp]
          theorem $thmName
              : flagDensity₁ K4.toFinFlag.2 $flagName = 0
            := by
            rw [K4_toFinFlag_eq]
            unfold $flagName
            simp [Flag_4_0_0_10]
            rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
            native_decide
        ))
        generatedEqZero := generatedEqZero + 1
    else
      let thmName := mkIdent (Name.mkSimple s!"flagDensity1_K4_Flag_{n}_0_0_{i}_ne_zero")
      if ¬ env.contains thmName.getId then
        elabCommand (← `(
          @[simp]
          theorem $thmName
              : ¬ flagDensity₁ K4.toFinFlag.2 $flagName = 0
            := by
            rw [K4_toFinFlag_eq]
            unfold $flagName
            simp [Flag_4_0_0_10]
            rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
            native_decide
        ))
        generatedNeZero := generatedNeZero + 1

  logInfo s!"Generated K4 density theorems from {filename.getString}: eq_zero={generatedEqZero}, ne_zero={generatedNeZero}"

end Flags.Densities
