import Mathlib.Tactic
import LeanFlagAlgebras.FlagAlgebra.PositiveHom

/-! # Automation.ExprHelpers — shared Expr-traversal utilities

Shared meta-programming utilities used by `FlagExpand` and `FlagMulReduce`.
All definitions live in `FlagAlgebras.Automation` so that both modules can use them
without qualification.

Provides:
* `lastNamePart` — extract the trailing string component of a `Name`.
* `findFlagAlgebraConst?` / `findFlagConst?` — locate the first `FlagAlgebra_*`
  or `Flag_*` constant anywhere in an expression.
* `parseFlagAlgebraIndices?` / `parseFlagIndices?` — parse `(n,k,m,i)` from
  the naming convention `FlagAlgebra_n_k_m_i` / `Flag_n_k_m_i`.
* `collectPrefixConstants` / `collectFlagAlgebraConsts` — collect all constants
  with a given prefix.
* `flagToFlagAlgebraLastPart` / `hasFlagConst` — name-conversion and presence
  helpers.
* `getBinAppArgs?` / `getAddArgs?` / `getSmulArgs?` / `getMulArgs?` /
  `stripDownward?` — structural `Expr` decomposers.
* `mkFlagMulThmName?` — look up the `flagMul_<A>_<B>` theorem name for a given
  product expression.
-/

open Lean Elab Tactic Meta

namespace FlagAlgebras.Automation

/-- The final string component of a `Name`. -/
def lastNamePart (nm : Name) : String :=
  match nm with
  | .anonymous => ""
  | .str _ s   => s
  | .num _ n   => toString n

/-- Find the first `FlagAlgebra_*` constant occurring anywhere in `e`. -/
partial def findFlagAlgebraConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if (lastNamePart nm).startsWith "FlagAlgebra_" then some nm else none
  | .app f x =>
      match findFlagAlgebraConst? f with
      | some nm => some nm
      | none    => findFlagAlgebraConst? x
  | .lam _ _ b _    => findFlagAlgebraConst? b
  | .forallE _ _ b _ => findFlagAlgebraConst? b
  | .letE _ _ v b _ =>
      match findFlagAlgebraConst? v with
      | some nm => some nm
      | none    => findFlagAlgebraConst? b
  | .mdata _ b => findFlagAlgebraConst? b
  | .proj _ _ b => findFlagAlgebraConst? b
  | _ => none

/-- Find the first `Flag_*` constant occurring anywhere in `e`. -/
partial def findFlagConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if (lastNamePart nm).startsWith "Flag_" then some nm else none
  | .app f x =>
      match findFlagConst? f with
      | some nm => some nm
      | none    => findFlagConst? x
  | .lam _ _ b _    => findFlagConst? b
  | .forallE _ _ b _ => findFlagConst? b
  | .letE _ _ v b _ =>
      match findFlagConst? v with
      | some nm => some nm
      | none    => findFlagConst? b
  | .mdata _ b => findFlagConst? b
  | .proj _ _ b => findFlagConst? b
  | _ => none

/-- Parse `(n,k,m,i)` from names of the form `…FlagAlgebra_n_k_m_i`. -/
def parseFlagAlgebraIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
  let s    := nm.toString
  let tail ← match s.splitOn "FlagAlgebra_" with
    | _ :: t :: _ => some t
    | _           => none
  let parts := tail.splitOn "_"
  let (nStr, kStr, mStr, iStr) ← match parts with
    | nStr :: kStr :: mStr :: iStr :: _ => some (nStr, kStr, mStr, iStr)
    | _                                  => none
  let n ← String.toNat? nStr
  let k ← String.toNat? kStr
  let m ← String.toNat? mStr
  let i ← String.toNat? iStr
  pure (n, k, m, i)

/-- Parse `(n,k,m,i)` from names of the form `…Flag_n_k_m_i`. -/
def parseFlagIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
  let s    := nm.toString
  let tail ← match s.splitOn "Flag_" with
    | _ :: t :: _ => some t
    | _           => none
  let parts := tail.splitOn "_"
  let (nStr, kStr, mStr, iStr) ← match parts with
    | nStr :: kStr :: mStr :: iStr :: _ => some (nStr, kStr, mStr, iStr)
    | _                                  => none
  let n ← String.toNat? nStr
  let k ← String.toNat? kStr
  let m ← String.toNat? mStr
  let i ← String.toNat? iStr
  pure (n, k, m, i)

/-- Collect every constant whose name starts with `prefixStr` in `e`. -/
partial def collectPrefixConstants (prefixStr : String) (e : Expr) : Array Name :=
  let rec aux (e : Expr) (acc : Array Name) : Array Name :=
    match e with
    | .const n _ =>
        -- Match the final name component, so namespace-qualified constants
        -- (e.g. `MantelTheorem.FlagAlgebra_…`) are collected too.
        if (lastNamePart n).startsWith prefixStr && !acc.contains n then acc.push n else acc
    | .app f a       => aux a (aux f acc)
    | .lam _ t b _   => aux b (aux t acc)
    | .forallE _ t b _ => aux b (aux t acc)
    | .letE _ t v b _ => aux b (aux v (aux t acc))
    | .mdata _ expr  => aux expr acc
    | .proj _ _ expr => aux expr acc
    | _              => acc
  aux e #[]

/-- Collect all constants containing `FlagAlgebra_` in `e`. -/
partial def collectFlagAlgebraConsts (e : Expr) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .const nm _ =>
      if nm.toString.contains "FlagAlgebra_" then acc.push nm else acc
  | .app f x =>
      collectFlagAlgebraConsts x (collectFlagAlgebraConsts f acc)
  | .lam _ _ b _    => collectFlagAlgebraConsts b acc
  | .forallE _ _ b _ => collectFlagAlgebraConsts b acc
  | .letE _ _ v b _ => collectFlagAlgebraConsts b (collectFlagAlgebraConsts v acc)
  | .mdata _ b      => collectFlagAlgebraConsts b acc
  | .proj _ _ b     => collectFlagAlgebraConsts b acc
  | _               => acc

/-- Convert a `Flag_<suffix>` last-name-part to `FlagAlgebra_<suffix>`. -/
def flagToFlagAlgebraLastPart (s : String) : String :=
  if s.startsWith "Flag_" then "FlagAlgebra_" ++ s.drop 5 else s

/-- `true` when `e` contains a `FlagAlgebra_*` or `Flag_*` constant. -/
def hasFlagConst (e : Expr) : Bool :=
  (findFlagAlgebraConst? e).isSome || (findFlagConst? e).isSome

-- Structural Expr decomposers

/-- Extract `(a, b)` from a binary application `(.app (.app _ a) b)`. -/
def getBinAppArgs? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app (.app _ a) b => some (a, b)
  | _                 => none

/-- If `e` is `x + y`, return `(x, y)`. -/
def getAddArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn   := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``Add.add) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else none

/-- If `e` is `c • x`, return `(c, x)`. -/
def getSmulArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn   := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HSMul.hSMul || fn.isConstOf ``SMul.smul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else none

/-- If `e` is `x * y`, return `(x, y)`. -/
def getMulArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn   := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HMul.hMul || fn.isConstOf ``Mul.mul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else getBinAppArgs? e

/-- Strip an outer `FlagAlgebras.downward` application, returning its argument. -/
def stripDownward? (e : Expr) : Option Expr :=
  if e.isAppOf ``FlagAlgebras.downward then
    let args := e.getAppArgs
    if args.size >= 1 then some args[args.size - 1]! else none
  else none

/-- If `e` is `-x` (`Neg.neg x`), return `x`. Used by `reduce_downward_flagmul` to handle
`downward (-(A * B))` summands (a `(-1) • _` coefficient simplified to a bare negation). -/
def stripNeg? (e : Expr) : Option Expr :=
  if e.getAppFn.isConstOf ``Neg.neg then
    let args := e.getAppArgs
    if args.size >= 1 then some args[args.size - 1]! else none
  else none

/-- Given `mulTerm = A * B`, search the environment for a theorem named
`flagMul_<A>_<B>` (or its reverse).

`curNs` is the current namespace at the call site, used as a fallback when
the flag constants and the `flagMul_*` theorems live in different namespaces. -/
def mkFlagMulThmName? (mulTerm : Expr) (curNs : Name) : MetaM (Option Name) := do
  let some (fExpr, gExpr) := getMulArgs? mulTerm | return none
  let fNm?  := findFlagAlgebraConst? fExpr
  let gNm?  := findFlagAlgebraConst? gExpr
  let fFlag? := findFlagConst? fExpr
  let gFlag? := findFlagConst? gExpr
  let some fNm := fNm?.orElse (fun _ => fFlag?) | return none
  let some gNm := gNm?.orElse (fun _ => gFlag?) | return none
  let env   := ← getEnv
  let fLast := if fNm?.isSome then lastNamePart fNm
               else flagToFlagAlgebraLastPart (lastNamePart fNm)
  let gLast := if gNm?.isSome then lastNamePart gNm
               else flagToFlagAlgebraLastPart (lastNamePart gNm)
  let thmStrFG := s!"flagMul_{fLast}_{gLast}"
  let thmStrGF := s!"flagMul_{gLast}_{fLast}"
  let epNs     := Name.mkSimple "ErdosPentagon"
  let mantelNs := Name.mkSimple "MantelTheorem"
  let cands := [
    Name.str fNm.getPrefix thmStrFG,
    Name.str fNm.getPrefix thmStrGF,
    Name.str curNs thmStrFG,
    Name.str curNs thmStrGF,
    Name.str epNs thmStrFG,
    Name.str epNs thmStrGF,
    Name.str mantelNs thmStrFG,
    Name.str mantelNs thmStrGF,
    Name.mkSimple thmStrFG,
    Name.mkSimple thmStrGF
  ]
  for cand in cands do
    if env.constants.contains cand then
      return some cand
  return none

end FlagAlgebras.Automation
