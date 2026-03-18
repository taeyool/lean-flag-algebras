import LeanFlagAlgebras.ErdosPentagon.FlagDef
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import Lean.Data.Json
import Mathlib.Tactic

open Lean Elab Command Json
open FlagAlgebras
open FlagAlgebras.Compute

namespace ErdosPentagon

structure DensityJsonData where
  hostTag : String
  patternTag : String
  densities : Array Json

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

def densityValueToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `($(Quote.quote num))
  else
    `((($(Quote.quote num) : Rat) / ($(Quote.quote den) : Rat)))

elab "load_density_relations" filename:str : command => do
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

end ErdosPentagon
