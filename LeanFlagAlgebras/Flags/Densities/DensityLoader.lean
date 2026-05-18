import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import Lean.Data.Json
import Mathlib.Tactic

/-! # Density theorem loaders

This module defines elaboration-time macros that consume the JSON produced by
the Python density pipeline and synthesize the corresponding `simp` theorems
about flag densities (which the loaded `Flag_*`/`FlagAlgebra_*` constants from
`FlagDef.lean` must already exist for):

* `load_flag_pair_density_theorems "density_*.json"` reads the
  `calculate_densities.py` output (host/pattern tags and a list of
  `[patternIdx1, patternIdx2, hostIdx, value]` rows) and generates, per row, a
  theorem `flagDensity₂ Flag_… Flag_… Flag_… = value`, proved by reduction to
  `sym2FlagDensity₂` and `native_decide`.
* `load_forbid_density_theorems "*_free_indices.json"` reads the
  `gen_free_indices.py` output (the indices of graphs avoiding a forbidden
  subgraph) and generates, per `n`-vertex empty-typed flag, a theorem stating
  its single-flag density of `K3`/`K4` is zero (forbidden-graph-free) or
  nonzero, again via `native_decide`.

The helper `def`s below parse the two JSON shapes into `DensityJsonData` /
`FreeIndexJsonData`.
-/

open Lean Elab Command Json
open FlagAlgebras
open FlagAlgebras.Compute

namespace Flags.Densities

/-- Parsed `density_*.json`: the host/pattern file tags and the raw array of
density rows `[patternIdx1, patternIdx2, hostIdx, value]`. -/
structure DensityJsonData where
  hostTag : String
  patternTag : String
  densities : Array Json

/-- Parsed `*_free_indices.json`: the graph vertex count, the forbidden-subgraph
tag, the total number of graphs, and the indices of forbidden-free graphs. -/
structure FreeIndexJsonData where
  graphN : Nat
  forbidTag : String
  totalGraphs : Nat
  freeGraphIndices : Array Nat

/-- Convert a JSON number to a `Nat`, succeeding only for non-negative integers. -/
def jsonNumberToNat? (x : JsonNumber) : Option Nat :=
  if x.exponent = 0 then
    x.mantissa.toNat?
  else
    none

/-- Parse a JSON value as a `Nat`, reporting `fieldName` on failure. -/
def parseNatFromJson (j : Json) (fieldName : String) : CommandElabM Nat := do
  let .num v := j | throwError s!"Expected Nat for {fieldName}"
  let some n := jsonNumberToNat? v
    | throwError s!"Expected natural number for {fieldName}"
  pure n

/-- Parse a JSON array of natural numbers. -/
def parseNatArrayFromJson (j : Json) (fieldName : String) : CommandElabM (Array Nat) := do
  let arr ← match j with
    | .arr a => pure a
    | _ => throwError s!"Expected array for {fieldName}"
  arr.mapM fun x => parseNatFromJson x fieldName

/-- Membership test on a `Nat` array. -/
def natArrayContains (arr : Array Nat) (x : Nat) : Bool :=
  arr.any fun y => y == x

/-- Parse a density string (`"num"` or `"num/den"`) into a
`(numerator, denominator)` pair. -/
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

/-- Read and parse a `density_*.json` file into `DensityJsonData`. -/
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

/-- Read and parse a `*_free_indices.json` file into `FreeIndexJsonData`. -/
def parseFreeIndexJsonFile (path : System.FilePath) : CommandElabM FreeIndexJsonData := do
  let content ← liftIO <| IO.FS.readFile path
  let json ← match Json.parse content with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let graphNJson ← match json.getObjVal? "n" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'n'"
  let graphN ← parseNatFromJson graphNJson "n"

  let forbidTag ← match json.getObjVal? "forbid" with
    | Except.ok forbidObj => match forbidObj.getObjVal? "tag" with
      | Except.ok (.str s) => pure s
      | _ => throwError "Missing or invalid field 'forbid.tag'"
    | _ => throwError "Missing or invalid field 'forbid'"

  let totalGraphsJson ← match json.getObjVal? "total_graphs" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'total_graphs'"
  let totalGraphs ← parseNatFromJson totalGraphsJson "total_graphs"

  let freeJson ← match json.getObjVal? "free_graph_indices" with
    | Except.ok v => pure v
    | _ => throwError "Missing or invalid field 'free_graph_indices'"
  let freeGraphIndices ← parseNatArrayFromJson freeJson "free_graph_indices"

  pure {
    graphN := graphN
    forbidTag := forbidTag
    totalGraphs := totalGraphs
    freeGraphIndices := freeGraphIndices
  }

/-- Build the RHS term of a density theorem from a `(num, den)` value. -/
def densityValueToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `($(Quote.quote num))
  else
    `((($(Quote.quote num) : Rat) / ($(Quote.quote den) : Rat)))

-- `load_flag_pair_density_theorems "density_*.json"`: per row
-- `[p1, p2, h, value]`, generate the `simp` theorem
-- `flagDensity₂ Flag_<pattern>_p1 Flag_<pattern>_p2 Flag_<host>_h = value`,
-- proved by `flagDensity₂_eq_sym2FlagDensity₂` + `native_decide`. Errors if any
-- referenced flag constant is missing; skips already-generated theorems.
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

-- `load_forbid_density_theorems "*_free_indices.json"`: for each of the
-- `total_graphs` empty-typed `n`-vertex flags, generate a `simp` theorem
-- stating the single-flag density of the forbidden graph (`K3` or `K4`,
-- selected by `forbid.tag`) is `= 0` when the graph is forbidden-free and
-- `≠ 0` otherwise, proved via `native_decide`.
elab "load_forbid_density_theorems" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data ← parseFreeIndexJsonFile path

  for i in data.freeGraphIndices do
    if i >= data.totalGraphs then
      throwError s!"free_graph_indices contains out-of-range index {i} (total_graphs = {data.totalGraphs})"

  let n := data.graphN
  let mut generatedEqZero : Nat := 0
  let mut generatedNeZero : Nat := 0

  for i in [0:data.totalGraphs] do
    let flagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let isFree := natArrayContains data.freeGraphIndices i

    let env ← getEnv
    if ¬ env.contains flagName.getId then
      throwError s!"Missing definition: {flagName.getId}"

    match data.forbidTag with
    | "K3" =>
      if isFree then
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
    | "K4" =>
      if isFree then
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
    | tag => throwError s!"Unsupported forbid tag: '{tag}'. Supported: K3, K4"

  logInfo s!"Generated {data.forbidTag} density theorems from {filename.getString}: eq_zero={generatedEqZero}, ne_zero={generatedNeZero}"

end Flags.Densities
