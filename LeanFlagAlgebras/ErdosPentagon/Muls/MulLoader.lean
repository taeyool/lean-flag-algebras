import LeanFlagAlgebras.ErdosPentagon.FlagDef
import Lean.Data.Json

open Lean Elab Command Json
open FlagAlgebras

namespace ErdosPentagon

structure DensityJsonData where
  hostTag : String
  patternTag : String
  hostTriangleFreeIndices : Array Nat
  patternTriangleFreeIndices : Array Nat
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

def parseNatArrayFromField (json : Json) (fieldName : String) : CommandElabM (Array Nat) := do
  let arr <-
    match json.getObjVal? fieldName with
    | Except.ok (.arr a) => pure a
    | _ => throwError s!"Missing or invalid field '{fieldName}'"
  arr.mapM (fun j => parseNatFromJson j fieldName)

def parseDensityString (s : String) : CommandElabM (Nat × Nat) := do
  let parts := (s.trimAscii.toString).splitOn "/"
  match parts with
  | [numStr] =>
      let num <-
        match numStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid density numerator: {numStr}"
      pure (num, 1)
  | [numStr, denStr] =>
      let num <-
        match numStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid density numerator: {numStr}"
      let den <-
        match denStr.trimAscii.toString.toNat? with
        | some v => pure v
        | none => throwError s!"Invalid density denominator: {denStr}"
      if den = 0 then
        throwError "Density denominator cannot be zero"
      pure (num, den)
  | _ =>
      throwError s!"Invalid density format: {s}"

def parseDensityJsonFile (path : System.FilePath) : CommandElabM DensityJsonData := do
  let content <- liftIO <| IO.FS.readFile path
  let json <-
    match Json.parse content with
    | .ok j => pure j
    | .error err => throwError s!"JSON parse error: {err}"

  let hostTag <-
    match json.getObjVal? "host" with
    | Except.ok (.str s) => pure s
    | _ => throwError "Missing or invalid field 'host'"

  let patternTag <-
    match json.getObjVal? "pattern" with
    | Except.ok (.str s) => pure s
    | _ => throwError "Missing or invalid field 'pattern'"

  let hostTriangleFreeIndices <- parseNatArrayFromField json "host_triangle_free_indices"
  let patternTriangleFreeIndices <- parseNatArrayFromField json "pattern_triangle_free_indices"

  let densities <-
    match json.getObjVal? "densities" with
    | Except.ok (.arr a) => pure a
    | _ => throwError "Missing or invalid field 'densities'"

  pure {
    hostTag := hostTag
    patternTag := patternTag
    hostTriangleFreeIndices := hostTriangleFreeIndices
    patternTriangleFreeIndices := patternTriangleFreeIndices
    densities := densities
  }

def parseFlagTypeNameFromTag (tag : String) : CommandElabM Name := do
  let parts := tag.splitOn "_"
  match parts with
  | [_sizeStr, n0Str, typeStr] =>
      if n0Str.toNat?.isNone then
        throwError s!"Invalid tag (cannot parse n0): {tag}"
      if typeStr.toNat?.isNone then
        throwError s!"Invalid tag (cannot parse type index): {tag}"
      pure <| Name.mkSimple s!"FlagType_{n0Str}_{typeStr}"
  | _ =>
      throwError s!"Invalid tag format (expected a_b_c): {tag}"

def natArrayContains (arr : Array Nat) (x : Nat) : Bool :=
  arr.any (fun y => y == x)

def coeffToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `((($(Quote.quote num) : Nat) : ℝ))
  else
    `((($(Quote.quote num) : ℝ) / ($(Quote.quote den) : ℝ)))

def coeffSmulFlagTerm (num den : Nat) (flagName : Name) : CommandElabM (TSyntax `term) := do
  let coeffTerm <- coeffToTerm num den
  let flagIdent := mkIdent flagName
  `($coeffTerm • $flagIdent)

def sumTerms (flagTypeName : Name) (terms : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let flagTypeIdent := mkIdent flagTypeName
  match terms.toList with
  | [] =>
      `((0 : FlagAlgebra $flagTypeIdent))
  | t :: ts =>
      ts.foldlM (fun acc nxt => `($acc + $nxt)) t

def parseDensityRow (row : Json) : CommandElabM (Nat × Nat × Nat × Nat × Nat) := do
  let .arr #[p1Json, p2Json, hJson, valJson] := row
    | throwError "Each density row must be [patternIdx1, patternIdx2, hostIdx, value]"

  let p1 <- parseNatFromJson p1Json "patternIdx1"
  let p2 <- parseNatFromJson p2Json "patternIdx2"
  let h <- parseNatFromJson hJson "hostIdx"

  let valStr <-
    match valJson with
    | .str s => pure s
    | _ => throwError "Density value must be a string"

  let frac <- parseDensityString valStr
  let num := frac.1
  let den := frac.2
  pure (p1, p2, h, num, den)

elab "load_mul_relations" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data <- parseDensityJsonFile path
  let patternFlagTypeName <- parseFlagTypeNameFromTag data.patternTag
  let hostFlagTypeName <- parseFlagTypeNameFromTag data.hostTag
  if patternFlagTypeName != hostFlagTypeName then
    throwError s!"Pattern and host tags use different flag types: {data.patternTag} vs {data.hostTag}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let mut generated : Nat := 0

  for i in data.patternTriangleFreeIndices do
    for j in data.patternTriangleFreeIndices do
      let mut rhsTerms : Array (TSyntax `term) := #[]
      for row in data.densities do
        let parsed <- parseDensityRow row
        let p1 := parsed.1
        let p2 := parsed.2.1
        let h := parsed.2.2.1
        let num := parsed.2.2.2.1
        let den := parsed.2.2.2.2
        if p1 = i && p2 = j && natArrayContains data.hostTriangleFreeIndices h && num != 0 then
          let hostName := Name.mkSimple s!"FlagAlgebra_{data.hostTag}_{h}"
          let env <- getEnv
          if !(env.contains hostName) then
            throwError s!"Missing definition: {hostName}"
          let t <- coeffSmulFlagTerm num den hostName
          rhsTerms := rhsTerms.push t

      let rhs <- sumTerms patternFlagTypeName rhsTerms

      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{j}")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{data.patternTag}_{i}_FlagAlgebra_{data.patternTag}_{j}")

      let env <- getEnv
      if !(env.contains lhs1.getId) then
        throwError s!"Missing definition: {lhs1.getId}"
      if !(env.contains lhs2.getId) then
        throwError s!"Missing definition: {lhs2.getId}"

      if !(env.contains thmName.getId) then
        elabCommand (← `(
          theorem $thmName
              : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K3] $rhs
            := by
            sorry
        ))
        generated := generated + 1

  logInfo s!"Generated {generated} multiplication theorem(s) from density JSON: {filename.getString}"

load_mul_relations "LeanFlagAlgebras/ErdosPentagon/Densities/density_5_3_2_from_4_3_2.json"

#check flagMul_FlagAlgebra_4_3_2_0_FlagAlgebra_4_3_2_1

end ErdosPentagon
