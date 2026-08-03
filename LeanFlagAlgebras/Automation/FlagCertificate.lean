import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Flags.ForbidFreeGenerator
import LeanFlagAlgebras.Flags.Densities.MulThmGenerator
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Automation.Basic
import LeanFlagAlgebras.Automation.FlagMulReduce
import LeanFlagAlgebras.Automation.FlagSumSort
import LeanFlagAlgebras.Automation.Matrix.PosSemiDef
import LeanFlagAlgebras.Automation.Matrix.PosSemiDefTerms
import LeanFlagAlgebras.Automation.FlagExpand
import LeanFlagAlgebras.Automation.FinSumUniv
import LeanFlagAlgebras.Forbid.CommonGraphs

/-! # The `flag_certificate` tactic

`flag_certificate "path/to/cert.json" F` proves a flag-algebra bound

  `FlagAlgebra_nObj_0_0_objIdx ≤[H] (bound : ℝ) • (1 : FlagAlgebra ∅ₜ)`

directly from a Flagmatic certificate file, read at elaboration time.  `F` is the
forbidden graph's `Sym2Graph` identifier — the same identifier that was passed to the
`generate_forbid_free_*` commands earlier in the file.  The certificate is *candidate
data only*: the tactic re-derives every fact inside Lean (matrix reconstruction
`M = R·Q'·Rᵀ` and an exact `LDLᵀ` factorization are recomputed here, then re-checked by
`decide +kernel`; densities and product expansions come from the generated theorem
families), so a corrupted certificate can only make the tactic fail, never prove a
wrong bound.

The user still writes the theorem *statement* — this is deliberate: the certificate
then serves purely as a hint, and the fidelity question "is the proved theorem the
intended one?" reduces to reading the statement in the source file.

Prerequisites (checked upfront, with an actionable error message): the
`generate_forbid_free_*` commands this certificate needs must have been run in the
current namespace, together with the file-wide
`set_option maxHeartbeats 0` / `set_option maxRecDepth 1000000` those commands need.

`flag_certificate? "path" F` additionally prints the synthesized tactic script as a
`Try this:` suggestion, so the proof can be materialized in the source file and
audited (the same skeleton `flagmatic_to_lean.py gen-skeleton` would emit, minus the
file-level definitions — matrices and flag vectors appear as inline literals).
-/

open Lean Elab Term Tactic Meta
open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute
open Flags.Densities

namespace FlagAlgebras.Automation.FlagCertificate

/-! ## Rational and flagmatic-string parsing -/

/-- Parse `"a/b"`, `"a"` (possibly negative) into a `Rat`. -/
def parseRatString (s : String) : Except String Rat :=
  match s.splitOn "/" with
  | [a] =>
    match a.toInt? with
    | some i => .ok (i : Rat)
    | none => .error s!"not a rational literal: {s}"
  | [a, b] =>
    match a.toInt?, b.toInt? with
    | some x, some y =>
      if y == 0 then .error s!"zero denominator in {s}" else .ok ((x : Rat) / (y : Rat))
    | _, _ => .error s!"not a rational literal: {s}"
  | _ => .error s!"not a rational literal: {s}"

/-- Parse a Flagmatic JSON rational: an integer JSON number or an `"a/b"` string. -/
def jsonToRat (j : Json) : Except String Rat := do
  match j with
  | .num n =>
    if n.exponent == 0 then
      pure (n.mantissa : Rat)
    else
      .error s!"non-integer JSON number {n}"
  | .str s => parseRatString s
  | _ => .error s!"expected a rational (int or \"a/b\"), got {j.compress}"

/-- A parsed flagmatic graph string `"N:edges"` / `"N:edges(k)"`: vertex count,
0-indexed sorted edge pairs, and the type size when the `(k)` suffix is present. -/
structure FMGraph where
  n : Nat
  edges : List (Nat × Nat)
  typeSize : Option Nat
  deriving Repr, Inhabited

private def sortPair (u v : Nat) : Nat × Nat := if u ≤ v then (u, v) else (v, u)

/-- Parse a flagmatic graph string (`"3:1213"`, `"2:12(1)"`, `"1:"`, …). -/
def parseFlagmatic (s : String) : Except String FMGraph := do
  let parts := s.splitOn ":"
  let (nStr, rest) ← match parts with
    | [a, b] => pure (a, b)
    | _ => .error s!"not a flagmatic graph string: {s}"
  let some n := nStr.toNat? | .error s!"bad vertex count in {s}"
  -- Optional "(k)" suffix.
  let (edgeStr, typeSize) ←
    match rest.splitOn "(" with
    | [e] => pure (e, none)
    | [e, kPart] =>
      match kPart.splitOn ")" with
      | [kStr, ""] =>
        match kStr.toNat? with
        | some kv => pure (e, some kv)
        | none => .error s!"bad type size in {s}"
      | _ => .error s!"bad label suffix in {s}"
    | _ => .error s!"bad label suffix in {s}"
  if edgeStr.length % 2 != 0 then
    .error s!"odd-length edge field in {s}"
  let digits := edgeStr.toList.map (fun c => c.toNat - '0'.toNat)
  let mut edges : List (Nat × Nat) := []
  for i in [0:digits.length / 2] do
    let u := digits[2 * i]! - 1
    let v := digits[2 * i + 1]! - 1
    if u == v || u ≥ n || v ≥ n then
      throw s!"bad edge in {s}"
    let e := sortPair u v
    if edges.contains e then
      throw s!"duplicate edge in {s}"
    edges := edges ++ [e]
  if let some k := typeSize then
    if k > n then throw s!"type size {k} exceeds {n} in {s}"
  pure { n := n, edges := edges, typeSize := typeSize }

/-! ## Isomorphism matching against the canonical enumerations -/

private def relabelEdges (edges : List (Nat × Nat)) (perm : List Nat) : List (Nat × Nat) :=
  edges.map fun (u, v) => sortPair (perm.getD u 0) (perm.getD v 0)

private def edgeSetEq (a b : List (Nat × Nat)) : Bool :=
  a.length == b.length && a.all b.contains && b.all a.contains

/-- Index of the canonical `n`-vertex graph isomorphic to `edges` (port of the
translator's `find_unlabeled_index`; `n ≤ 7`, brute force). -/
def findUnlabeledIndex (n : Nat) (edges : List (Nat × Nat))
    (all : List (List (Nat × Nat))) : Option Nat :=
  (List.range all.length).find? fun i =>
    let g := all.getD i []
    g.length == edges.length &&
      (List.range n).permutations.any fun p => edgeSetEq (relabelEdges edges p) g

/-- Does `host` contain `sub` as a (not necessarily induced) subgraph?  Port of the
translator's `subgraph_contains` — the split the `generate_forbid_free_*` commands use. -/
def subgraphContainsL (subN : Nat) (subEdges : List (Nat × Nat))
    (hostN : Nat) (hostEdges : List (Nat × Nat)) : Bool :=
  if subN > hostN then false
  else
    (List.range hostN).permutations.any fun p =>
      subEdges.all fun (u, v) => hostEdges.contains (sortPair (p.getD u 0) (p.getD v 0))

/-- σ-flag lookup (port of the translator's `find_sigma_flag_index`): the index among
the canonical `(k, typeIdx)`-typed `m`-vertex flags matching `edges` with labels on the
first `k` vertices.  `rows` is `genFlagData k typeIdx m`, `underlyingIdx` the canonical
index of the flag's underlying graph. -/
def findSigmaFlagIndex (m k : Nat) (edges : List (Nat × Nat)) (underlyingIdx : Nat)
    (rows : List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) : Option Nat := Id.run do
  for flagIdx in List.range rows.length do
    let row := rows.getD flagIdx (0, [], [], 0, 0)
    if row.1 != underlyingIdx then
      continue
    let storedEdges := row.2.1
    let typeIndices := row.2.2.1
    -- Forced part: input vertex j (the j-th label) must map to typeIndices[j].
    let forced := (List.range k).map fun j => (j, typeIndices.getD j 0)
    if (forced.map (·.2)).eraseDups.length != forced.length then
      continue
    let freeIns := (List.range m).filter (fun v => ¬ forced.any (·.1 == v))
    let freeOuts := (List.range m).filter (fun v => ¬ forced.any (·.2 == v))
    let found := freeOuts.permutations.any fun assignment =>
      let perm := (List.range m).map fun src =>
        match forced.find? (·.1 == src) with
        | some (_, dst) => dst
        | none =>
          match (freeIns.zip assignment).find? (·.1 == src) with
          | some (_, dst) => dst
          | none => 0
      edgeSetEq (relabelEdges edges perm) storedEdges
    if found then
      return some flagIdx
  return none

/-! ## Exact rational matrix algebra -/

private def matMul (A B : Array (Array Rat)) : Array (Array Rat) :=
  let cols := (B.getD 0 #[]).size
  A.map fun row =>
    .ofFn fun j : Fin cols =>
      (List.range B.size).foldl (fun acc l => acc + row.getD l 0 * (B.getD l #[]).getD j 0) 0

private def matTranspose (A : Array (Array Rat)) : Array (Array Rat) :=
  let rows := A.size
  let cols := (A.getD 0 #[]).size
  .ofFn fun j : Fin cols => .ofFn fun i : Fin rows => (A.getD i #[]).getD j 0

/-- Expand Flagmatic's upper-triangular `Q'` rows into the full symmetric matrix. -/
def parseQdash (qdash : Array (Array Rat)) : Except String (Array (Array Rat)) := do
  let n := qdash.size
  let mut Q : Array (Array Rat) := .replicate n (.replicate n 0)
  for i in [0:n] do
    let row := qdash[i]!
    if row.size != n - i then
      throw s!"qdash row {i}: expected {n - i} upper-triangular entries, got {row.size}"
    for off in [0:row.size] do
      let j := i + off
      let v := row[off]!
      Q := Q.set! i ((Q[i]!).set! j v)
      Q := Q.set! j ((Q[j]!).set! i v)
  pure Q

/-- `M = R · Q' · Rᵀ` in exact rational arithmetic. -/
def assembleBlockMatrix (qdash r : Array (Array Rat)) : Except String (Array (Array Rat)) := do
  let Q ← parseQdash qdash
  pure (matMul (matMul r Q) (matTranspose r))

/-- Exact rational `LDLᵀ` of a symmetric PSD matrix: `(L, d)` with `L` unit lower
triangular.  Fails (with the offending pivot) when the matrix is not PSD — that is,
when the *certificate* is bad; nothing is trusted, since the factorization is
re-checked by `decide +kernel` in the synthesized proof. -/
def ldlDecomposition (M : Array (Array Rat)) :
    Except String (Array (Array Rat) × Array Rat) := do
  let n := M.size
  let mut L : Array (Array Rat) := .replicate n (.replicate n 0)
  let mut D : Array Rat := .replicate n 0
  for i in [0:n] do
    L := L.set! i ((L[i]!).set! i 1)
    let mut di := (M[i]!).getD i 0
    for l in [0:i] do
      di := di - (L[i]!).getD l 0 * (L[i]!).getD l 0 * D.getD l 0
    if di < 0 then
      throw s!"LDLᵀ: pivot D[{i}] = {di} < 0 — certificate matrix is not PSD"
    D := D.set! i di
    for j in [i+1:n] do
      let mut num := (M[j]!).getD i 0
      for l in [0:i] do
        num := num - (L[j]!).getD l 0 * (L[i]!).getD l 0 * D.getD l 0
      if di == 0 then
        if num != 0 then
          throw s!"LDLᵀ: D[{i}] = 0 but residual M[{j},{i}] = {num} ≠ 0 — not PSD"
      else
        L := L.set! j ((L[j]!).set! i (num / di))
  pure (L, D)

/-! ## Certificate model -/

/-- One SDP block of a parsed certificate, with everything resolved against Lean's
canonical enumerations. -/
structure BlockData where
  /-- Type size `k` of `FlagType_k_m`. -/
  typeK : Nat
  /-- Canonical type index `m` of `FlagType_k_m`. -/
  typeIdx : Nat
  /-- Vertex count of this block's σ-flags. -/
  patN : Nat
  /-- Canonical σ-flag indices, in certificate order (the flag vector `v`). -/
  flagIdxs : Array Nat
  /-- `M = R·Q'·Rᵀ`, reconstructed exactly. -/
  M : Array (Array Rat)
  /-- Unit-lower-triangular `L` of the `LDLᵀ` witness. -/
  L : Array (Array Rat)
  /-- Diagonal of the `LDLᵀ` witness. -/
  d : Array Rat
  deriving Inhabited

/-- A parsed and fully resolved certificate. -/
structure CertData where
  desc : String
  bound : Rat
  hostN : Nat
  objN : Nat
  objIdx : Nat
  forbidN : Nat
  forbidEdges : List (Nat × Nat)
  /-- `true` for a complete forbidden graph (Route A: `≤[completeGraph (Fin r)]`),
  `false` for the general subgraph route (Route B: `≤[F.toLabeledGraph.graph]`). -/
  forbidComplete : Bool
  blocks : Array BlockData
  deriving Inhabited

/-! ## Elaboration-time access to the Lean enumerations -/

/-- `genCanonicalEdgeLists n`, evaluated at elaboration time (the same enumeration the
`generate_*` commands use, so indices agree with the generated constants). -/
def evalEdgeLists (n : Nat) : TermElabM (List (List (Nat × Nat))) := do
  let stx ← `(FlagAlgebras.Compute.genCanonicalEdgeLists $(Quote.quote n))
  let valExpr ← Term.elabTermAndSynthesize stx none
  let valExpr ← instantiateMVars valExpr
  let typeExpr ← inferType valExpr
  evalNatPairLists typeExpr valExpr

/-- `genFlagData k m n`, evaluated at elaboration time. -/
def evalFlagRows (k m n : Nat) :
    TermElabM (List (Nat × List (Nat × Nat) × List Nat × Nat × Nat)) := do
  let stx ← `(FlagAlgebras.Compute.genFlagData
      $(Quote.quote k) $(Quote.quote m) $(Quote.quote n))
  let valExpr ← Term.elabTermAndSynthesize stx none
  let valExpr ← instantiateMVars valExpr
  let typeExpr ← inferType valExpr
  evalFlagData typeExpr valExpr

/-! ## Certificate loading -/

private def getStrField (j : Json) (k : String) : Except String String := do
  (← j.getObjVal? k).getStr?

private def getRatArr2 (j : Json) (k : String) : Except String (Array (Array (Array Rat))) := do
  let arr ← (← j.getObjVal? k).getArr?
  arr.mapM fun blk => do
    let rows ← blk.getArr?
    rows.mapM fun row => do
      (← row.getArr?).mapM jsonToRat

/-- Extract `maximize <s> density` / `forbid <s>` from the description line. -/
private def descField (desc : String) (kw : String) : Except String String :=
  match desc.splitOn kw with
  | _ :: rest :: _ =>
    match rest.splitOn " " with
    | tok :: _ => .ok ((tok.splitOn ";").headD tok)
    | _ => .error s!"could not read the token after `{kw}` in: {desc}"
  | _ => .error s!"no `{kw}` clause in certificate description: {desc}"

/-- Parse the JSON and resolve every flagmatic string against the canonical
enumerations.  Everything here is *untrusted* precomputation — each derived fact is
re-established inside the synthesized proof. -/
def loadCert (jsonText : String) : TermElabM CertData := do
  let json ← ofExcept (Json.parse jsonText |>.mapError
    (fun e => s!"certificate is not valid JSON: {e}"))
  let desc ← ofExcept (getStrField json "description")
  let bound ← ofExcept (do jsonToRat (← json.getObjVal? "bound"))
  let hostN ← ofExcept (do (← json.getObjVal? "order_of_admissible_graphs").getNat?)

  -- Objective.
  let objStr ← ofExcept (descField desc "maximize ")
  let obj ← ofExcept (parseFlagmatic objStr)
  let objAll ← evalEdgeLists obj.n
  let some objIdx := findUnlabeledIndex obj.n obj.edges objAll
    | throwError "flag_certificate: objective {objStr} not found in the canonical \
        {obj.n}-vertex enumeration"

  -- Forbidden graph.
  let forbidStr ← ofExcept (descField desc "forbid ")
  let forbid ← ofExcept (parseFlagmatic forbidStr)
  let complete := forbid.edges.length == forbid.n * (forbid.n - 1) / 2

  -- Blocks.
  let typeStrs ← ofExcept (do (← json.getObjVal? "types").getArr?)
  let flagLists ← ofExcept (do (← json.getObjVal? "flags").getArr?)
  let qdashArrs ← ofExcept (getRatArr2 json "qdash_matrices")
  let rArrs ← ofExcept (getRatArr2 json "r_matrices")
  unless typeStrs.size == flagLists.size &&
      typeStrs.size == qdashArrs.size && typeStrs.size == rArrs.size do
    throwError "flag_certificate: types/flags/qdash_matrices/r_matrices have mismatched lengths"

  let mut blocks : Array BlockData := #[]
  for t in [0:typeStrs.size] do
    let typeStr ← ofExcept (typeStrs[t]!.getStr?)
    let ty ← ofExcept (parseFlagmatic typeStr)
    if ty.n == 0 then
      throwError "flag_certificate: empty-type SDP blocks (type \"0:\") are not supported"
    let tyAll ← evalEdgeLists ty.n
    let some typeIdx := findUnlabeledIndex ty.n ty.edges tyAll
      | throwError "flag_certificate: type {typeStr} not found in the canonical enumeration"
    let flagStrs ← ofExcept (flagLists[t]!.getArr?)
    if flagStrs.isEmpty then
      throwError "flag_certificate: block {t + 1} has no flags"
    let mut patN : Nat := 0
    let mut flagIdxs : Array Nat := #[]
    for fs in flagStrs do
      let fStr ← ofExcept (fs.getStr?)
      let fg ← ofExcept (parseFlagmatic fStr)
      unless fg.typeSize == some ty.n do
        throwError "flag_certificate: flag {fStr} does not carry type size ({ty.n})"
      patN := fg.n
      let patAll ← evalEdgeLists fg.n
      let some underlyingIdx := findUnlabeledIndex fg.n fg.edges patAll
        | throwError "flag_certificate: flag {fStr}: underlying graph not found"
      let rows ← evalFlagRows ty.n typeIdx fg.n
      let some flagIdx := findSigmaFlagIndex fg.n ty.n fg.edges underlyingIdx rows
        | throwError "flag_certificate: flag {fStr} not found among the canonical \
            ({fg.n},{ty.n},{typeIdx}) flags"
      flagIdxs := flagIdxs.push flagIdx
    let M ← ofExcept ((assembleBlockMatrix qdashArrs[t]! rArrs[t]!).mapError
      (fun e => s!"flag_certificate: block {t + 1}: {e}"))
    let (L, d) ← ofExcept ((ldlDecomposition M).mapError
      (fun e => s!"flag_certificate: block {t + 1}: {e}"))
    blocks := blocks.push {
      typeK := ty.n, typeIdx := typeIdx, patN := patN,
      flagIdxs := flagIdxs, M := M, L := L, d := d }

  pure {
    desc := desc, bound := bound, hostN := hostN,
    objN := obj.n, objIdx := objIdx,
    forbidN := forbid.n, forbidEdges := forbid.edges,
    forbidComplete := complete, blocks := blocks }

/-! ## Building Lean terms for the certificate data -/

/-- A rational literal `(a / b : ty)` / `(a : ty)` / `(-(a / b) : ty)`. -/
def mkRatLit (q : Rat) (ty : TSyntax `term) : TermElabM (TSyntax `term) := do
  let a := q.num.natAbs
  let core : TSyntax `term ←
    if q.den == 1 then
      `(($(Quote.quote a) : $ty))
    else
      `((($(Quote.quote a) : $ty) / ($(Quote.quote q.den) : $ty)))
  if q.num < 0 then `((-$core)) else pure core

/-- A vector literal `(![x₁, …, xₙ] : Fin n → ty)`. -/
def mkRatVecLit (v : Array Rat) (ty : TSyntax `term) : TermElabM (TSyntax `term) := do
  let entries ← v.mapM (mkRatLit · ty)
  `((![$entries,*] : Fin $(Quote.quote v.size) → $ty))

/-- A matrix literal `(Matrix.of ![![…], …] : Matrix (Fin n) (Fin n) ℚ)` (the
elaboration of the `!![…]` notation, built programmatically). -/
def mkRatMatrixLit (M : Array (Array Rat)) : TermElabM (TSyntax `term) := do
  let qTy ← `(ℚ)
  let rows ← M.mapM fun row => do
    let entries ← row.mapM (mkRatLit · qTy)
    `(![$entries,*])
  let n := Quote.quote M.size
  `((Matrix.of ![$rows,*] : Matrix (Fin $n) (Fin $n) ℚ))

private def finSumUnivWord : Nat → Option String
  | 1 => some "one" | 2 => some "two" | 3 => some "three" | 4 => some "four"
  | 5 => some "five" | 6 => some "six" | 7 => some "seven" | 8 => some "eight"
  | 9 => some "nine" | 10 => some "ten" | 11 => some "eleven" | 12 => some "twelve"
  | 13 => some "thirteen" | 14 => some "fourteen" | 15 => some "fifteen"
  | 16 => some "sixteen"
  | _ => none

/-! ## Human-readable script rendering (for `flag_certificate?`)

The syntax the tactic runs is built by quotations, whose pretty-printed form carries
hygiene markers and so cannot be pasted back into a source file.  The `?` variant
therefore renders the same script a second time as plain text, driven by the same
certificate data, in the style `flagmatic_to_lean.py gen-skeleton` uses. -/

/-- `(3 / 4 : ty)`, `(3 : ty)`, `(-3 / 4 : ty)`, `0`. -/
def ratStr (q : Rat) (ty : String) : String :=
  if q == 0 then "0"
  else if q.den == 1 then s!"({q.num} : {ty})"
  else s!"({q.num} / {q.den} : {ty})"

/-- A `!![…;\n …]` rational matrix literal, rows separated across lines. -/
def matrixStr (M : Array (Array Rat)) (indent : String) : String :=
  let rows := M.toList.map fun row =>
    String.intercalate ", " (row.toList.map (ratStr · "ℚ"))
  "!![" ++ String.intercalate (";\n" ++ indent) rows ++ "]"

/-- A `![…]` rational vector literal. -/
def vecStr (v : Array Rat) : String :=
  "![" ++ String.intercalate ", " (v.toList.map (ratStr · "ℚ")) ++ "]"

/-! ## Prerequisite checking -/

/-- Is `name` declared in the current namespace or at the root (the same lookup the
generator macros use)? -/
def declaredInScope (name : Name) : TermElabM Bool := do
  let ns ← getCurrNamespace
  let env ← getEnv
  return env.contains (ns ++ name) || env.contains name

/-- The generation-command block this certificate requires, in the order
`gen-skeleton` emits it: each entry is `(command line, sentinel declaration)`.
`tag` is the forbidden graph's identifier (its last name component names the
generated `…Hfree_…_{tag}` declarations). -/
def requiredCommands (cert : CertData) (tag : String)
    (patternFree0 : Nat → Nat → Nat → Nat) (hostFree0 : Nat) :
    List (String × Name) := Id.run do
  let mut out : List (String × Name) := []
  -- Empty-typed sizes: objective ∪ host ∪ pattern size per block.
  let mut emptySizes : List Nat := [cert.objN, cert.hostN]
  for b in cert.blocks do
    unless emptySizes.contains b.patN do emptySizes := emptySizes ++ [b.patN]
  for n in emptySizes.mergeSort (· ≤ ·) do
    out := out ++ [(s!"generate_forbid_free_empty_typed_flags {n} {tag}",
      Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}")]
  -- Typed flags: (patN, k, m) and (hostN, k, m) per block.
  let mut triples : List (Nat × Nat × Nat) := []
  for b in cert.blocks do
    for tr in [(b.patN, b.typeK, b.typeIdx), (cert.hostN, b.typeK, b.typeIdx)] do
      unless triples.contains tr do triples := triples ++ [tr]
  let tripleLE : Nat × Nat × Nat → Nat × Nat × Nat → Bool := fun a b =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))
  for (n, k, m) in triples.mergeSort tripleLE do
    out := out ++ [(s!"generate_forbid_free_flags {n} {k} {m} {tag}",
      Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}")]
  -- Pair densities + products, per block in certificate order.
  let mut seen : List (Nat × Nat × Nat) := []
  for b in cert.blocks do
    let key := (b.patN, b.typeK, b.typeIdx)
    unless seen.contains key do
      seen := seen ++ [key]
      let i0 := patternFree0 b.patN b.typeK b.typeIdx
      out := out ++
        [(s!"generate_forbid_free_flag_pair_density_theorems {b.patN} {cert.hostN} {b.typeK} {b.typeIdx} {tag}",
          Name.mkSimple
            s!"pairDensityBatch_{b.patN}_{b.typeK}_{b.typeIdx}_{cert.hostN}_{b.typeK}_{b.typeIdx}_0"),
         (s!"generate_forbid_free_mul_theorems {b.patN} {cert.hostN} {b.typeK} {b.typeIdx} {tag}",
          Name.mkSimple
            s!"flagMul_FlagAlgebra_{b.patN}_{b.typeK}_{b.typeIdx}_{i0}_FlagAlgebra_{b.patN}_{b.typeK}_{b.typeIdx}_{i0}")]
  -- Branch B: the objective density table.
  if cert.objN < cert.hostN then
    out := out ++
      [(s!"generate_forbid_free_flag_density_theorems {cert.objN} {cert.objIdx} {cert.hostN} {tag}",
        Name.mkSimple
          s!"auto_flagDensity1_{cert.objN}_0_0_{cert.objIdx}_{cert.hostN}_0_0_{hostFree0}")]
  return out

/-! ## The tactic -/

/-- Build and (optionally) run the certificate proof script. -/
def runFlagCertificate (pathStx : TSyntax `str) (fStx : TSyntax `ident)
    (suggest : Bool) : TacticM Unit := do
  let path := pathStx.getString

  -- Read and resolve the certificate.
  let jsonText ←
    try
      IO.FS.readFile path
    catch e =>
      throwErrorAt pathStx "flag_certificate: cannot read certificate file '{path}' \
        (paths are relative to the working directory of the build, normally the \
        package root): {e.toMessageData}"
  let cert ← loadCert jsonText

  -- The forbidden-graph identifier must resolve, and its last component names the
  -- generated `…Hfree` declarations.
  let tag := match fStx.getId with
    | .str _ s => s
    | n => n.toString
  discard <| Term.elabTerm fStx none  -- fail early (with the ident's position) if unresolvable

  -- Free-index data (for sentinels, the expansion statement, and Fin.sum lemmas).
  let hostAll ← evalEdgeLists cert.hostN
  let hostFreeIdxs := (List.range hostAll.length).filter fun i =>
    ¬ subgraphContainsL cert.forbidN cert.forbidEdges cert.hostN (hostAll.getD i [])
  let some hostFree0 := hostFreeIdxs.head?
    | throwError "flag_certificate: no forbid-free {cert.hostN}-vertex graphs?"

  let mut patternFree0Map : List ((Nat × Nat × Nat) × Nat) := []
  for b in cert.blocks do
    let key := (b.patN, b.typeK, b.typeIdx)
    unless patternFree0Map.any (·.1 == key) do
      let rows ← evalFlagRows b.typeK b.typeIdx b.patN
      let free := (List.range rows.length).filter fun i =>
        ¬ subgraphContainsL cert.forbidN cert.forbidEdges b.patN
          ((rows.getD i (0, [], [], 0, 0)).2.1)
      patternFree0Map := patternFree0Map ++ [(key, free.headD 0)]
  let patternFree0 : Nat → Nat → Nat → Nat := fun n k m =>
    (patternFree0Map.find? (·.1 == (n, k, m))).map (·.2) |>.getD 0

  -- Prerequisite check.
  let required := requiredCommands cert tag patternFree0 hostFree0
  let mut missing : List String := []
  let mut cmdLines : List String := []
  for (cmd, sentinel) in required do
    let ok ← declaredInScope sentinel
    cmdLines := cmdLines ++ [if ok then s!"  {cmd}" else s!"  {cmd}   -- MISSING"]
    unless ok do missing := missing ++ [cmd]
  if !missing.isEmpty then
    throwError "flag_certificate: the generated theorem families this certificate needs \
are not (all) present in the current namespace.  Add the following before the theorem \
(the `set_option`s are required by the generation commands and by this tactic's \
closing normalization):\n\n  \
set_option flagGen.kernelDecide true  -- optional: kernel-only bridging lemmas\n  \
set_option maxHeartbeats 0\n  set_option maxRecDepth 1000000\n\
{String.intercalate "\n" cmdLines}\n\n\
(`-- MISSING` marks the commands whose generated declarations were not found; \
the forbidden graph `{tag}` must be the same identifier passed to those commands.)"

  -- Term pieces.
  let objIdent : Ident := mkIdent (Name.mkSimple s!"FlagAlgebra_{cert.objN}_0_0_{cert.objIdx}")
  let forbidGraphExpr : TSyntax `term ←
    if cert.forbidComplete then
      `(completeGraph (Fin $(Quote.quote cert.forbidN)))
    else
      `(($fStx).toLabeledGraph.graph)

  -- Per-block matrix/vector literals and PSD `have`s (each also rendered as text for
  -- the `?` variant).
  let forbidGraphStr :=
    if cert.forbidComplete then s!"completeGraph (Fin {cert.forbidN})" else s!"{tag}.toLabeledGraph.graph"
  let mut psdHaves : Array (TSyntax `tactic) := #[]
  let mut qfTerms : Array (TSyntax `term) := #[]      -- ⟦flagQuadraticForm … …⟧₀
  let mut applyQF : Array (TSyntax `tactic) := #[]    -- in reverse block order
  let mut psdHaveStrs : Array String := #[]
  let mut qfTermStrs : Array String := #[]
  let mut applyQFStrs : Array String := #[]
  let mut finSizes : List Nat := []
  for t in [0:cert.blocks.size] do
    let b := cert.blocks[t]!
    let nFlags := b.flagIdxs.size
    unless finSumUnivWord nFlags |>.isSome do
      throwError "flag_certificate: block {t + 1} has {nFlags} flags; only blocks of \
size ≤ 16 are supported (extend Automation/FinSumUniv.lean and finSumUnivWord)"
    unless finSizes.contains nFlags do finSizes := finSizes ++ [nFlags]
    let Mlit ← mkRatMatrixLit b.M
    let Llit ← mkRatMatrixLit b.L
    let dlit ← mkRatVecLit b.d (← `(ℚ))
    let psdName := mkIdent (Name.mkSimple s!"flagCert_psd{t + 1}")
    let sigmaIdent := mkIdent (Name.mkSimple s!"FlagType_{b.typeK}_{b.typeIdx}")
    let flagIdents ← b.flagIdxs.mapM fun i =>
      pure (mkIdent (Name.mkSimple
        s!"FlagAlgebra_{b.patN}_{b.typeK}_{b.typeIdx}_{i}") : TSyntax `term)
    let vlit ← `((![$flagIdents,*] :
      FlagAlgebraVec $sigmaIdent $(Quote.quote nFlags)))
    psdHaves := psdHaves.push (← `(tactic|
      have $psdName : (ratMatrixToReal $Mlit).PosSemidef := by
        psd_real_ldlt_terms $Mlit $Llit $dlit))
    qfTerms := qfTerms.push (← `(⟦flagQuadraticForm (ratMatrixToReal $Mlit) $vlit⟧₀))
    applyQF := applyQF.push (← `(tactic|
      apply forbidLEWith_add_QuadraticForm (ratMatrixToReal $Mlit) $psdName $vlit))
    -- Text renditions.
    let vStr := "(![" ++ String.intercalate ", "
        (b.flagIdxs.toList.map fun i =>
          s!"FlagAlgebra_{b.patN}_{b.typeK}_{b.typeIdx}_{i}") ++
      s!"] : FlagAlgebraVec FlagType_{b.typeK}_{b.typeIdx} {nFlags})"
    psdHaveStrs := psdHaveStrs.push
      (s!"have flagCert_psd{t + 1} : (ratMatrixToReal\n    {matrixStr b.M "      "}).PosSemidef := by\n  " ++
       s!"psd_real_ldlt_terms\n    {matrixStr b.M "      "}\n    {matrixStr b.L "      "}\n    {vecStr b.d}")
    qfTermStrs := qfTermStrs.push
      s!"⟦flagQuadraticForm (ratMatrixToReal {matrixStr b.M "        "}) {vStr}⟧₀"
    applyQFStrs := applyQFStrs.push
      (s!"apply forbidLEWith_add_QuadraticForm (ratMatrixToReal\n      {matrixStr b.M "        "})\n    flagCert_psd{t + 1} {vStr}")

  -- `have flagCert_qf : obj ≤[G] obj + Q₁ + … + Q_T`.
  let objStr := s!"FlagAlgebra_{cert.objN}_0_0_{cert.objIdx}"
  let mut qfRHS : TSyntax `term := objIdent
  for q in qfTerms do
    qfRHS ← `($qfRHS + $q)
  let qfName := mkIdent (Name.mkSimple "flagCert_qf")
  let qfProofTacs : Array (TSyntax `tactic) :=
    applyQF.reverse.push (← `(tactic| exact forbidLEWith_refl _ $objIdent))
  let qfSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$qfProofTacs]*)
  let qfHave ← `(tactic|
    have $qfName : ($objIdent ≤[$forbidGraphExpr] $qfRHS) := by $qfSeq)
  let qfHaveStr :=
    s!"have flagCert_qf : {objStr} ≤[{forbidGraphStr}]\n      " ++
    String.intercalate "\n      + " (objStr :: qfTermStrs.toList) ++ "\n    := by\n" ++
    String.intercalate "\n" ((applyQFStrs.reverse.toList.map ("  " ++ ·)) ++
      [s!"  exact forbidLEWith_refl _ {objStr}"])

  -- Branch B: the objective expansion `have`.
  let branchB := cert.objN < cert.hostN
  let mut expandHave? : Option (TSyntax `tactic) := none
  let mut expandHaveStr := ""
  let expandName := mkIdent (Name.mkSimple "flagCert_expand")
  if branchB then
    let objAll ← evalEdgeLists cert.objN
    let objEdges := objAll.getD cert.objIdx []
    let mut sum? : Option (TSyntax `term) := none
    let mut sumStrs : List String := []
    for i in hostFreeIdxs do
      let nd := inducedDensity1 cert.objN objEdges cert.hostN (hostAll.getD i [])
      if nd.1 != 0 then
        let hostName := s!"FlagAlgebra_{cert.hostN}_0_0_{i}"
        let hostIdent : TSyntax `term := mkIdent (Name.mkSimple hostName)
        let term : TSyntax `term ←
          if nd.1 == nd.2 then
            pure hostIdent
          else do
            let coeff ← mkRatLit ((nd.1 : Rat) / (nd.2 : Rat)) (← `(ℝ))
            `($coeff • $hostIdent)
        sumStrs := sumStrs ++
          [if nd.1 == nd.2 then hostName
           else s!"{ratStr ((nd.1 : Rat) / (nd.2 : Rat)) "ℝ"} • {hostName}"]
        sum? := some (← match sum? with
          | none => pure term
          | some acc => `($acc + $term))
    let some sum := sum?
      | throwError "flag_certificate: the objective has empty forbid-free expansion — \
          the certificate cannot be valid"
    let hostNLit : TSyntax `num := Syntax.mkNumLit (toString cert.hostN)
    expandHave? := some (← `(tactic|
      have $expandName : ($objIdent =[$forbidGraphExpr] $sum) := by
        flag_expand_hfree $hostNLit $fStx))
    expandHaveStr :=
      s!"have flagCert_expand : {objStr} =[{forbidGraphStr}] " ++
      String.intercalate " + " sumStrs ++
      s!" := by\n  flag_expand_hfree {cert.hostN} {tag}"

  -- The `1`-expansion step.
  let oneExpand : TSyntax `tactic ←
    if cert.forbidComplete then
      `(tactic| apply forbidLEWith_trans_forbidEqWith_right ?_
          (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem
            (⟨_, Sym2EmptyTypedFlag.toFlag ⟦$fStx⟧⟩ : FinFlag ∅ₜ)
            (completeSym2Graph_finFlag_mem_forbiddenFlags $(Quote.quote cert.forbidN))
            $(Quote.quote cert.hostN)))))
    else
      `(tactic| apply forbidLEWith_trans_forbidEqWith_right ?_
          (forbidEqWith_smul (forbidEqWith_symm (one_forbidEq_forbidExpand_one_subgraph
            $fStx $(Quote.quote cert.hostN)))))

  -- The quadratic-form expansion simp: one pass with every needed `Fin.sum_univ_*`.
  let mut simpArgs : Array (TSyntax `term) := #[← `(flagQuadraticForm), ← `(ratMatrixToReal)]
  for w in finSizes do
    let some word := finSumUnivWord w | unreachable!
    simpArgs := simpArgs.push (mkIdent (Name.mkStr2 "Fin" s!"sum_univ_{word}"))
  simpArgs := simpArgs.push (← `(add_assoc))

  -- Assemble the whole script, together with its text rendition.
  let oneExpandStr :=
    if cert.forbidComplete then
      s!"apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul \
(forbidEqWith_symm (one_forbidEq_forbidExpand_one_ofMem (⟨_, Sym2EmptyTypedFlag.toFlag \
⟦{tag}⟧⟩ : FinFlag ∅ₜ) (completeSym2Graph_finFlag_mem_forbiddenFlags {cert.forbidN}) \
{cert.hostN})))"
    else
      s!"apply forbidLEWith_trans_forbidEqWith_right ?_  (forbidEqWith_smul \
(forbidEqWith_symm (one_forbidEq_forbidExpand_one_subgraph {tag} {cert.hostN})))"
  let finWords := finSizes.map (fun w => (finSumUnivWord w).getD "two")
  let simpStr := "simp [flagQuadraticForm, ratMatrixToReal, " ++
    String.intercalate ", " (finWords.map (s!"Fin.sum_univ_{·}")) ++ ", add_assoc]"

  let mut tacs : Array (TSyntax `tactic) := #[]
  let mut scriptLines : Array String := #[]
  tacs := tacs ++ psdHaves
  scriptLines := scriptLines ++ psdHaveStrs
  if let some ex := expandHave? then
    tacs := tacs.push ex
    scriptLines := scriptLines.push expandHaveStr
  tacs := tacs.push qfHave
  scriptLines := scriptLines.push qfHaveStr
  tacs := tacs.push (← `(tactic| apply forbidLEWith_trans $qfName))
  scriptLines := scriptLines.push "apply forbidLEWith_trans flagCert_qf"
  tacs := tacs.push oneExpand
  scriptLines := scriptLines.push oneExpandStr
  if branchB then
    if cert.blocks.size ≥ 2 then
      tacs := tacs.push (← `(tactic| simp only [add_assoc]))
      scriptLines := scriptLines.push "simp only [add_assoc]"
    tacs := tacs.push (← `(tactic| rw [forbidLEWith_rw_left_add_right $expandName]))
    scriptLines := scriptLines.push "rw [forbidLEWith_rw_left_add_right flagCert_expand]"
  tacs := tacs.push (← `(tactic| simp [$[$simpArgs:term],*]))
  scriptLines := scriptLines.push simpStr
  tacs := tacs.push (← `(tactic| reduce_downward_flagmul))
  scriptLines := scriptLines.push "reduce_downward_flagmul"
  let hostNLit : TSyntax `num := Syntax.mkNumLit (toString cert.hostN)
  tacs := tacs.push (← `(tactic| expand_one_hfree_at $hostNLit $fStx))
  scriptLines := scriptLines.push s!"expand_one_hfree_at {cert.hostN} {tag}"
  tacs := tacs.push (← `(tactic|
    simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]))
  scriptLines := scriptLines.push
    "simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]"
  tacs := tacs.push (← `(tactic| flagsum_ac_sort_rhs_pipeline))
  scriptLines := scriptLines.push "flagsum_ac_sort_rhs_pipeline"
  tacs := tacs.push (← `(tactic| apply forbidLEWith_of_le))
  scriptLines := scriptLines.push "apply forbidLEWith_of_le"
  tacs := tacs.push (← `(tactic| flag_nonneg))
  scriptLines := scriptLines.push "flag_nonneg"

  -- `flag_certificate?`: offer the explicit script as a `Try this:` suggestion, so
  -- the editor can replace this tactic call with the materialized proof in one click
  -- (the same mechanism `apply?`/`exact?` use).  The script is a plain string, and
  -- string suggestions are inserted verbatim, so continuation lines must be indented
  -- to the call-site column here (tsyntax suggestions get this from `addSuggestion`
  -- itself, but pretty-printing our quotation-built syntax would leak hygiene
  -- markers, which is why the script is rendered as text).
  if suggest then
    let text := String.intercalate "\n" scriptLines.toList
    let ref ← getRef
    let indented ←
      if let some pos := ref.getPos? then
        let col := ((← getFileMap).toPosition pos).column
        pure (text.replace "\n" ("\n" ++ "".pushn ' ' col))
      else
        pure text
    Lean.Meta.Tactic.TryThis.addSuggestion ref { suggestion := .string indented }

  -- Run it.
  for t in tacs do
    evalTactic t

@[inherit_doc FlagAlgebras.Automation.FlagCertificate.runFlagCertificate]
syntax (name := flagCertificateTac) "flag_certificate " str ppSpace ident : tactic

@[inherit_doc FlagAlgebras.Automation.FlagCertificate.runFlagCertificate]
syntax (name := flagCertificateSuggestTac) "flag_certificate? " str ppSpace ident : tactic

elab_rules : tactic
  | `(tactic| flag_certificate $path:str $f:ident) => runFlagCertificate path f false
  | `(tactic| flag_certificate? $path:str $f:ident) => runFlagCertificate path f true

end FlagAlgebras.Automation.FlagCertificate
