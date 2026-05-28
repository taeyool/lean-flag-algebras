import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.Flags.Densities.DensityLoader
import LeanFlagAlgebras.Forbid.Basic
import Lean.Data.Json
import Mathlib.Tactic

/-! # Forbidden-graph multiplication theorem loader

This module defines the `load_forbid_mul_theorems` macro, which consumes the
`density_*.json` output of `calculate_densities.py` and synthesizes the flag
multiplication theorems used in forbidden-subgraph flag-algebra arguments.

For every unordered pair `(i, j)` of forbidden-free pattern flags, it generates
a theorem `FlagAlgebra_<pattern>_i * FlagAlgebra_<pattern>_j =[Kr.toFinFlag] Σ`,
where the right-hand sum is built from the precomputed density coefficients
times the forbidden-free host flag algebras, proved via
`unitVector_quot_mul_forbidEq_sum` and the `flagSet_*_eq_univ` /
`flagSet_*_val_eq` completeness lemmas. The forbidden graph (`K3` or `K4`) is
selected by `forbid.tag`. It relies on the `Flag_*`/`FlagAlgebra_*`/`flagSet_*`
constants synthesized by `FlagDef.lean` and the JSON helpers in
`DensityLoader.lean`.
-/

open Lean Elab Command Json
open FlagAlgebras Forbid
open FlagAlgebras.Compute

namespace Flags.Densities

/-- Parsed `density_*.json` for the multiplication loader: host/pattern/forbid
tags, the indices of forbidden-free host and pattern flags, and the raw density
rows `[patternIdx1, patternIdx2, hostIdx, value]`. -/
structure MulJsonData where
  hostTag : String
  patternTag : String
  forbidTag : String
  hostFreeIndices : Array Nat
  patternFreeIndices : Array Nat
  densities : Array Json

/-- Parse the named object field as a JSON array of natural numbers. -/
def parseNatArrayFromField (json : Json) (fieldName : String) : CommandElabM (Array Nat) := do
  let arr <-
    match json.getObjVal? fieldName with
    | Except.ok (.arr a) => pure a
    | _ => throwError s!"Missing or invalid field '{fieldName}'"
  arr.mapM (fun j => parseNatFromJson j fieldName)

/-- Read and parse a `density_*.json` file into `MulJsonData`. -/
def parseMulJsonFile (path : System.FilePath) : CommandElabM MulJsonData := do
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

  let forbidTag <-
    match json.getObjVal? "forbid" with
    | Except.ok .null => pure "none"
    | Except.ok forbidObj => match forbidObj.getObjVal? "tag" with
      | Except.ok (.str s) => pure s
      | _ => throwError "Missing or invalid field 'forbid.tag'"
    | _ => throwError "Missing or invalid field 'forbid'"

  let hostFreeIndices <- parseNatArrayFromField json "host_free_indices"
  let patternFreeIndices <- parseNatArrayFromField json "pattern_free_indices"

  let densities <-
    match json.getObjVal? "densities" with
    | Except.ok (.arr a) => pure a
    | _ => throwError "Missing or invalid field 'densities'"

  pure {
    hostTag := hostTag
    patternTag := patternTag
    forbidTag := forbidTag
    hostFreeIndices := hostFreeIndices
    patternFreeIndices := patternFreeIndices
    densities := densities
  }

/-- From a `size_n0_type` tag, build the generated `FlagType_<n0>_<type>` name. -/
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

/-- Parse a `size_n0_type` tag into the numeric triple `(size, n0, typeIdx)`. -/
def parseTagTriple (tag : String) : CommandElabM (Nat × Nat × Nat) := do
  let parts := tag.splitOn "_"
  match parts with
  | [sizeStr, n0Str, typeStr] =>
      let some size := sizeStr.toNat?
        | throwError s!"Invalid tag (cannot parse size): {tag}"
      let some n0 := n0Str.toNat?
        | throwError s!"Invalid tag (cannot parse n0): {tag}"
      let some typeIdx := typeStr.toNat?
        | throwError s!"Invalid tag (cannot parse type index): {tag}"
      pure (size, n0, typeIdx)
  | _ =>
      throwError s!"Invalid tag format (expected a_b_c): {tag}"

/-- Build a real-number coefficient term from a `(num, den)` pair. -/
def coeffToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `((($(Quote.quote num) : Nat) : ℝ))
  else
    `((($(Quote.quote num) : ℝ) / ($(Quote.quote den) : ℝ)))

/-- Build the term `coeff • flagName`, one summand of the multiplication RHS. -/
def coeffSmulFlagTerm (num den : Nat) (flagName : Name) : CommandElabM (TSyntax `term) := do
  let coeffTerm <- coeffToTerm num den
  let flagIdent := mkIdent flagName
  `($coeffTerm • $flagIdent)

/-- Left-fold a list of summands into `t₀ + t₁ + …`, or `0` when empty. -/
def sumTerms (flagTypeName : Name) (terms : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let flagTypeIdent := mkIdent flagTypeName
  match terms.toList with
  | [] =>
      `((0 : FlagAlgebra $flagTypeIdent))
  | t :: ts =>
      ts.foldlM (fun acc nxt => `($acc + $nxt)) t

/-- Parse one density row `[p1, p2, h, "num/den"]` into
`(p1, p2, h, num, den)`. -/
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

/-- Scan the environment for existing `Flag_<hostTag>_h` constants and return
the indices `h` found (up to `searchLimit`). -/
def collectHostFlagIndices (hostTag : String) (searchLimit : Nat := 200) : CommandElabM (Array Nat) := do
  let mut indices : Array Nat := #[]
  let env <- getEnv
  for h in List.range searchLimit do
    let flagName := Name.mkSimple s!"Flag_{hostTag}_{h}"
    if env.contains flagName then
      indices := indices.push h
  pure indices

/-- Strip leading `∀`-binders from an expression, returning its body. -/
private def peelForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ body _ => peelForall body
  | _ => e

/-- Given an equality theorem, return the head constant of its RHS as an
identifier. -/
private def unlabelRhsIdentFromTheorem (thmName : Name) : CommandElabM (TSyntax `ident) := do
  let env <- getEnv
  let some ci := env.find? thmName
    | throwError s!"Missing theorem: {thmName}"
  let ty := peelForall ci.type.consumeMData
  let fn := ty.getAppFn.consumeMData
  let args := ty.getAppArgs
  unless fn.isConstOf ``Eq && args.size = 3 do
    throwError s!"Theorem {thmName} does not have an equality type"
  let rhs := args[2]!.consumeMData.getAppFn.consumeMData
  match rhs with
  | .const rhsName _ =>
      pure (mkIdent rhsName)
  | _ =>
      throwError s!"Could not extract RHS constant name from theorem: {thmName}"

-- `load_forbid_mul_theorems "density_*.json"`: for every unordered pair
-- `(i, j)` of forbidden-free pattern flags, generate the theorem
-- `FlagAlgebra_<pattern>_i * FlagAlgebra_<pattern>_j =[Kr.toFinFlag] Σ`, where
-- the RHS sum collects `coeff • FlagAlgebra_<host>_h` over density rows with
-- forbidden-free host `h` and nonzero coefficient. `Kr` is `K3`/`K4` from
-- `forbid.tag`. Validates the pattern/host tags share a flag type and that all
-- referenced constants exist; skips already-generated theorems.
elab "load_forbid_mul_theorems" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data <- parseMulJsonFile path
  let patternTriple <- parseTagTriple data.patternTag
  let hostTriple <- parseTagTriple data.hostTag
  let patternSize := patternTriple.1
  let patternN0 := patternTriple.2.1
  let hostSize := hostTriple.1
  let hostN0 := hostTriple.2.1
  if patternN0 != hostN0 then
    throwError s!"Pattern and host tags use different n0: {data.patternTag} vs {data.hostTag}"
  let patternFlagTypeName <- parseFlagTypeNameFromTag data.patternTag
  let hostFlagTypeName <- parseFlagTypeNameFromTag data.hostTag
  if patternFlagTypeName != hostFlagTypeName then
    throwError s!"Pattern and host tags use different flag types: {data.patternTag} vs {data.hostTag}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let mut generated : Nat := 0

  for i in data.patternFreeIndices do
    for j in data.patternFreeIndices do
      let iOrd := if i <= j then i else j
      let jOrd := if i <= j then j else i
      let mut rhsTerms : Array (TSyntax `term) := #[]
      for row in data.densities do
        let parsed <- parseDensityRow row
        let p1 := parsed.1
        let p2 := parsed.2.1
        let h := parsed.2.2.1
        let num := parsed.2.2.2.1
        let den := parsed.2.2.2.2
        if p1 = iOrd && p2 = jOrd && natArrayContains data.hostFreeIndices h && num != 0 then
          let hostName := Name.mkSimple s!"FlagAlgebra_{data.hostTag}_{h}"
          let env <- getEnv
          if !(env.contains hostName) then
            throwError s!"Missing definition: {hostName}"
          let t <- coeffSmulFlagTerm num den hostName
          rhsTerms := rhsTerms.push t

      let rhs <- sumTerms patternFlagTypeName rhsTerms

      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{j}")
      let flagOrd1 := mkIdent (Name.mkSimple s!"Flag_{data.patternTag}_{iOrd}")
      let flagOrd2 := mkIdent (Name.mkSimple s!"Flag_{data.patternTag}_{jOrd}")
      let flagSetEqUniv := mkIdent (Name.mkSimple s!"flagSet_{data.hostTag}_eq_univ")
      let flagSetValEq := mkIdent (Name.mkSimple s!"flagSet_{data.hostTag}_val_eq")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{data.patternTag}_{i}_FlagAlgebra_{data.patternTag}_{j}")

      let env <- getEnv
      if !(env.contains lhs1.getId) then
        throwError s!"Missing definition: {lhs1.getId}"
      if !(env.contains lhs2.getId) then
        throwError s!"Missing definition: {lhs2.getId}"
      if !(env.contains flagOrd1.getId) then
        throwError s!"Missing definition: {flagOrd1.getId}"
      if !(env.contains flagOrd2.getId) then
        throwError s!"Missing definition: {flagOrd2.getId}"

      if !(env.contains thmName.getId) then
        match data.forbidTag with
        | "K3" =>
          if i <= j then
            elabCommand (← `(
              theorem $thmName
                  : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K3.toFinFlag] $rhs
                := by
                apply forbidEq_trans
                  (unitVector_quot_mul_forbidEq_sum K3.toFinFlag
                    ⟨$(Quote.quote patternSize), $flagOrd1⟩
                    ⟨$(Quote.quote patternSize), $flagOrd2⟩
                    $(Quote.quote hostSize)
                    (by rfl))
                rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
                have hsetval := $flagSetValEq
                simp [hsetval]
                exact forbidEq_refl K3.toFinFlag _
            ))
          else
            elabCommand (← `(
              theorem $thmName
                  : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K3.toFinFlag] $rhs
                := by
                rw [mul_comm]
                apply forbidEq_trans
                  (unitVector_quot_mul_forbidEq_sum K3.toFinFlag
                    ⟨$(Quote.quote patternSize), $flagOrd1⟩
                    ⟨$(Quote.quote patternSize), $flagOrd2⟩
                    $(Quote.quote hostSize)
                    (by rfl))
                rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
                have hsetval := $flagSetValEq
                simp [hsetval]
                exact forbidEq_refl K3.toFinFlag _
            ))
        | "K4" =>
          if i <= j then
            elabCommand (← `(
              theorem $thmName
                  : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K4.toFinFlag] $rhs
                := by
                apply forbidEq_trans
                  (unitVector_quot_mul_forbidEq_sum K4.toFinFlag
                    ⟨$(Quote.quote patternSize), $flagOrd1⟩
                    ⟨$(Quote.quote patternSize), $flagOrd2⟩
                    $(Quote.quote hostSize)
                    (by rfl))
                rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
                have hsetval := $flagSetValEq
                simp [hsetval]
                exact forbidEq_refl K4.toFinFlag _
            ))
          else
            elabCommand (← `(
              theorem $thmName
                  : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K4.toFinFlag] $rhs
                := by
                rw [mul_comm]
                apply forbidEq_trans
                  (unitVector_quot_mul_forbidEq_sum K4.toFinFlag
                    ⟨$(Quote.quote patternSize), $flagOrd1⟩
                    ⟨$(Quote.quote patternSize), $flagOrd2⟩
                    $(Quote.quote hostSize)
                    (by rfl))
                rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
                have hsetval := $flagSetValEq
                simp [hsetval]
                exact forbidEq_refl K4.toFinFlag _
            ))
        | "K5" =>
          if i <= j then
            elabCommand (← `(
              theorem $thmName
                  : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K5.toFinFlag] $rhs
                := by
                apply forbidEq_trans
                  (unitVector_quot_mul_forbidEq_sum K5.toFinFlag
                    ⟨$(Quote.quote patternSize), $flagOrd1⟩
                    ⟨$(Quote.quote patternSize), $flagOrd2⟩
                    $(Quote.quote hostSize)
                    (by rfl))
                rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
                have hsetval := $flagSetValEq
                simp [hsetval]
                exact forbidEq_refl K5.toFinFlag _
            ))
          else
            elabCommand (← `(
              theorem $thmName
                  : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[K5.toFinFlag] $rhs
                := by
                rw [mul_comm]
                apply forbidEq_trans
                  (unitVector_quot_mul_forbidEq_sum K5.toFinFlag
                    ⟨$(Quote.quote patternSize), $flagOrd1⟩
                    ⟨$(Quote.quote patternSize), $flagOrd2⟩
                    $(Quote.quote hostSize)
                    (by rfl))
                rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
                have hsetval := $flagSetValEq
                simp [hsetval]
                exact forbidEq_refl K5.toFinFlag _
            ))
        | tag => throwError s!"Unsupported forbid tag: '{tag}'. Supported: K3, K4, K5"
        generated := generated + 1

  logInfo s!"Generated {generated} {data.forbidTag}-free multiplication theorem(s) from density JSON: {filename.getString}"

-- `load_mul_theorems "density_*_no_forbid.json"`: for every unordered pair
-- `(i, j)` of pattern flags, generate the plain-equality theorem
-- `@[simp] FlagAlgebra_<pattern>_i * FlagAlgebra_<pattern>_j = Σ`
-- using `unitVector_quot_mul_eq_flagMul_quot` and the `flagSet_*` lemmas.
-- Intended for JSON files without a forbidden subgraph (`"forbid": null`).
elab "load_mul_theorems" filename:str : command => do
  let path := System.FilePath.mk filename.getString
  let data <- parseMulJsonFile path
  let patternTriple <- parseTagTriple data.patternTag
  let hostTriple <- parseTagTriple data.hostTag
  let patternN0 := patternTriple.2.1
  let hostN0 := hostTriple.2.1
  if patternN0 != hostN0 then
    throwError s!"Pattern and host tags use different n0: {data.patternTag} vs {data.hostTag}"
  let patternFlagTypeName <- parseFlagTypeNameFromTag data.patternTag
  let hostFlagTypeName <- parseFlagTypeNameFromTag data.hostTag
  if patternFlagTypeName != hostFlagTypeName then
    throwError s!"Pattern and host tags use different flag types: {data.patternTag} vs {data.hostTag}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let flagSetEqUniv := mkIdent (Name.mkSimple s!"flagSet_{data.hostTag}_eq_univ")
  let flagSetValEq  := mkIdent (Name.mkSimple s!"flagSet_{data.hostTag}_val_eq")

  let mut generated : Nat := 0

  for i in data.patternFreeIndices do
    for j in data.patternFreeIndices do
      let iOrd := if i <= j then i else j
      let jOrd := if i <= j then j else i
      let mut rhsTerms : Array (TSyntax `term) := #[]
      for row in data.densities do
        let parsed <- parseDensityRow row
        let p1 := parsed.1
        let p2 := parsed.2.1
        let h  := parsed.2.2.1
        let num := parsed.2.2.2.1
        let den := parsed.2.2.2.2
        if p1 = iOrd && p2 = jOrd && natArrayContains data.hostFreeIndices h && num != 0 then
          let hostName := Name.mkSimple s!"FlagAlgebra_{data.hostTag}_{h}"
          let env <- getEnv
          if !(env.contains hostName) then
            throwError s!"Missing definition: {hostName}"
          let t <- coeffSmulFlagTerm num den hostName
          rhsTerms := rhsTerms.push t

      let rhs <- sumTerms patternFlagTypeName rhsTerms

      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{j}")
      -- after mul_comm (when i > j), the order becomes iOrd * jOrd
      let flagAlgOrd1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{iOrd}")
      let flagAlgOrd2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{data.patternTag}_{jOrd}")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{data.patternTag}_{i}_FlagAlgebra_{data.patternTag}_{j}")

      let env <- getEnv
      if !(env.contains lhs1.getId) then
        throwError s!"Missing definition: {lhs1.getId}"
      if !(env.contains lhs2.getId) then
        throwError s!"Missing definition: {lhs2.getId}"

      if !(env.contains thmName.getId) then
        let idsArray : Array (TSyntax `ident) := #[flagAlgOrd1, flagAlgOrd2]
        if i <= j then
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) = $rhs
              := by
              dsimp only [$[$idsArray:ident],*]
              rw [unitVector_quot_mul_eq_flagMul_quot]
              simp [flagMul, flagMulWithSize]
              rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
              have hsetval := $flagSetValEq
              rw [hsetval]
              simp [add_quot, smul_quot]
              rfl
          ))
        else
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) = $rhs
              := by
              rw [mul_comm]
              dsimp only [$[$idsArray:ident],*]
              rw [unitVector_quot_mul_eq_flagMul_quot]
              simp [flagMul, flagMulWithSize]
              rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
              have hsetval := $flagSetValEq
              rw [hsetval]
              simp [add_quot, smul_quot]
              rfl
          ))
        elabCommand (← `(attribute [simp] $thmName))
        generated := generated + 1

  logInfo s!"Generated {generated} plain multiplication theorem(s) from density JSON: {filename.getString}"

end Flags.Densities
