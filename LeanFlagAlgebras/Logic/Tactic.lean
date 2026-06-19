import Mathlib.Tactic
import LeanFlagAlgebras.Logic.Defs

/-! # Proof tactics for the flag-algebra assertion DSL

Proof automation for the `FlagLogic` DSL. It provides metaprogramming helpers to locate
and parse `Flag_*` / `FlagAlgebra_*` constants, and the two tactics
`prove_flag_expand_with_forbidden_flag` and `prove_flag_mul_with_forbidden_flag`, which
discharge entailments expressing a flag (or product of flags) as a linear combination of
size-`N` flags modulo a forbidden flag.
-/

open Lean Elab Tactic Meta

namespace FlagLogic

/-- Find a constant name containing `FlagAlgebra_...` in an expression. -/
partial def findFlagAlgebraConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if nm.toString.contains "FlagAlgebra_" then some nm else none
  | .app f x =>
      match findFlagAlgebraConst? f with
      | some nm => some nm
      | none => findFlagAlgebraConst? x
  | .lam _ _ b _ => findFlagAlgebraConst? b
  | .forallE _ _ b _ => findFlagAlgebraConst? b
  | .letE _ _ v b _ =>
      match findFlagAlgebraConst? v with
      | some nm => some nm
      | none => findFlagAlgebraConst? b
  | .mdata _ b => findFlagAlgebraConst? b
  | .proj _ _ b => findFlagAlgebraConst? b
  | _ => none

/-- Parse `(n,k,m,i)` from names like `...FlagAlgebra_n_k_m_i`. -/
def parseFlagAlgebraIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
  let s := nm.toString
  let tail ← match s.splitOn "FlagAlgebra_" with
    | _ :: t :: _ => some t
    | _ => none
  let parts := tail.splitOn "_"
  let (nStr, kStr, mStr, iStr) ← match parts with
    | nStr :: kStr :: mStr :: iStr :: _ => some (nStr, kStr, mStr, iStr)
    | _ => none
  let n ← String.toNat? nStr
  let k ← String.toNat? kStr
  let m ← String.toNat? mStr
  let i ← String.toNat? iStr
  pure (n, k, m, i)

/-- Find a constant name containing `Flag_...` in an expression. -/
partial def findFlagConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
    if nm.toString.contains "Flag_" then some nm else none
  | .app f x =>
    match findFlagConst? f with
    | some nm => some nm
    | none => findFlagConst? x
  | .lam _ _ b _ => findFlagConst? b
  | .forallE _ _ b _ => findFlagConst? b
  | .letE _ _ v b _ =>
    match findFlagConst? v with
    | some nm => some nm
    | none => findFlagConst? b
  | .mdata _ b => findFlagConst? b
  | .proj _ _ b => findFlagConst? b
  | _ => none

/-- Parse `(n,k,m,i)` from names like `...Flag_n_k_m_i`. -/
def parseFlagIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
  let s := nm.toString
  let tail ← match s.splitOn "Flag_" with
    | _ :: t :: _ => some t
    | _ => none
  let parts := tail.splitOn "_"
  let (nStr, kStr, mStr, iStr) ← match parts with
    | nStr :: kStr :: mStr :: iStr :: _ => some (nStr, kStr, mStr, iStr)
    | _ => none
  let n ← String.toNat? nStr
  let k ← String.toNat? kStr
  let m ← String.toNat? mStr
  let i ← String.toNat? iStr
  pure (n, k, m, i)

partial def collectPrefixConstants (prefixStr : String) (e : Expr) : Array Name :=
  let rec collectAux (e : Expr) (acc : Array Name) : Array Name :=
    match e with
    | .const n _ =>
      -- Match the final name component, so namespace-qualified constants
      -- (e.g. `MantelTheorem.FlagAlgebra_…`) are collected too.
      if (match n with | .str _ s => s.startsWith prefixStr | _ => false) && !acc.contains n then
        acc.push n
      else
        acc
    | .app f a => collectAux a (collectAux f acc)
    | .lam _ t b _ => collectAux b (collectAux t acc)
    | .forallE _ t b _ => collectAux b (collectAux t acc)
    | .letE _ t v b _ => collectAux b (collectAux v (collectAux t acc))
    | .mdata _ expr => collectAux expr acc
    | .proj _ _ expr => collectAux expr acc
    | _ => acc
  collectAux e #[]

/--
Executes the core logic for `prove_flag_expand_with_forbidden_flag N`.
-/
def runForbiddenFlagExpansion (N : TSyntax `term) : TacticM Unit :=
  withMainContext do
    let nExpr ← elabTerm N (some (mkConst ``Nat))
    let some nVal ← (Meta.evalNat nExpr).run
      | throwError "Could not evaluate N to a natural number in `prove_flag_expand_with_forbidden_flag`."

    let target ← getMainTarget
    let flags := collectPrefixConstants "FlagAlgebra_" target
    if flags.isEmpty then pure ()
    else
      let idents := flags.map mkIdent
      evalTactic (← `(tactic| dsimp [$[$idents:ident],*]))

    evalTactic (← `(tactic| intro φ h))
    evalTactic (← `(tactic| simp only [Assert.eval_eq, FlagAlgebras.PositiveHom.map_zero] at h))
    evalTactic (← `(tactic|
      simp only [Assert.eval_eq, FlagAlgebras.PositiveHom.map_smul, FlagAlgebras.PositiveHom.map_add,
        FlagAlgebras.PositiveHom.map_sub]))

    let goalTy ← (← getMainGoal).getType
    let some (_, lhs, _) := goalTy.eq?
      | throwError "Goal after intro must be an equality."

    let parsed : Option (Nat × Nat × Nat × Nat) :=
      match findFlagConst? lhs with
      | some flagConst => parseFlagIndices? flagConst
      | none =>
          match findFlagAlgebraConst? lhs with
          | some lhsConst => parseFlagAlgebraIndices? lhsConst
          | none => none
    let some (lhsN, kVal, mVal, iVal) := parsed
      | throwError "Could not find/parse `Flag_*` (or `FlagAlgebra_*`) indices in the target equality."

    let flagName : Name := Name.mkSimple s!"Flag_{lhsN}_{kVal}_{mVal}_{iVal}"
    let flagId : TSyntax `term := mkIdent flagName
    let lhsNStx : TSyntax `term := Syntax.mkNumLit (toString lhsN)
    let finFlagTerm ← `(term| ⟨$lhsNStx, $flagId⟩)
    let sigmaTerm : TSyntax `term ←
      if kVal = 0 && mVal = 0 then
        `(term| ∅ₜ)
      else
        pure <| mkIdent (Name.mkSimple s!"FlagType_{kVal}_{mVal}")

    let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
    let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
    let eqUnivId : TSyntax `ident := mkIdent eqUnivName
    let valEqId : TSyntax `ident := mkIdent valEqName

    evalTactic (← `(tactic|
      have hExp := FlagAlgebras.basisVector_quot_eq_sum (σ := $sigmaTerm) $finFlagTerm $N (by simp)))
    evalTactic (← `(tactic| have hφ := congrArg φ hExp))
    evalTactic (← `(tactic| rw [FlagAlgebras.PositiveHom.map_sum] at hφ))
    evalTactic (← `(tactic| rw [Finset.sum_eq_multiset_sum] at hφ))
    evalTactic (← `(tactic| have h_eq_univ := $eqUnivId))
    evalTactic (← `(tactic| have h_val_eq := $valEqId))
    evalTactic (← `(tactic| rw [← h_eq_univ, h_val_eq] at hφ))
    evalTactic (← `(tactic| simp only [Multiset.map_coe, List.map_cons, List.map_nil,
      Multiset.sum_coe, List.sum_cons, List.sum_nil] at hφ))
    evalTactic (← `(tactic| simp only [FlagAlgebras.PositiveHom.map_smul] at hφ))
    evalTactic (← `(tactic| rw [h] at hφ))
    evalTactic (← `(tactic| simp at hφ))
    evalTactic (← `(tactic| rw [hφ]))
    evalTactic (← `(tactic| ring_nf))

/--
Executes the core logic for `prove_flag_mul_with_forbidden_flag N`.
-/
def runForbiddenFlagMul (N : TSyntax `term) : TacticM Unit :=
  withMainContext do
    let nExpr ← elabTerm N (some (mkConst ``Nat))
    let some nVal ← (Meta.evalNat nExpr).run
      | throwError "Could not evaluate N to a natural number in `prove_flag_mul_with_forbidden_flag`."

    let target ← getMainTarget
    let flags := collectPrefixConstants "FlagAlgebra_" target
    if flags.size >= 3 then
      let f1Parsed := parseFlagAlgebraIndices? flags[1]!
      let f2Parsed := parseFlagAlgebraIndices? flags[2]!
      if let (some (_, _, _, i1), some (_, _, _, i2)) := (f1Parsed, f2Parsed) then
        if i1 > i2 then
          evalTactic (← `(tactic| rw [mul_comm]))

    evalTactic (← `(tactic| intro φ h))
    evalTactic (← `(tactic| simp only [Assert.eval_eq, FlagAlgebras.PositiveHom.map_zero] at h))
    evalTactic (← `(tactic|
      simp only [Assert.eval_eq, FlagAlgebras.PositiveHom.map_smul, FlagAlgebras.PositiveHom.map_add,
        FlagAlgebras.PositiveHom.map_sub]))

    if !flags.isEmpty then
      let idents := flags.map mkIdent
      evalTactic (← `(tactic| dsimp [$[$idents:ident],*] at *))

    evalTactic (← `(tactic| rw [FlagAlgebras.basisVector_quot_mul_eq_flagMul_quot]))
    evalTactic (← `(tactic| dsimp [FlagAlgebras.flagMul, FlagAlgebras.flagMulWithSize]))

    -- Figure out the sigma indices from nVal to construct flagSet_N_k_m_eq_univ
    -- Wait, we need kVal and mVal! We can get it from f1Parsed.
    let some (_, kVal, mVal, _) := parseFlagAlgebraIndices? flags[1]!
      | throwError "Could not parse FlagAlgebra indices from {flags[1]!}"

    let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
    let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
    let eqUnivId : TSyntax `ident := mkIdent eqUnivName
    let valEqId : TSyntax `ident := mkIdent valEqName

    evalTactic (← `(tactic| have h_eq_univ := $eqUnivId))
    evalTactic (← `(tactic| have h_val_eq := $valEqId))
    evalTactic (← `(tactic| rw [Finset.sum_eq_multiset_sum, ← h_eq_univ, h_val_eq]))
    evalTactic (← `(tactic| simp [FlagAlgebras.add_quot, FlagAlgebras.smul_quot, FlagAlgebras.PositiveHom.map_add, FlagAlgebras.PositiveHom.map_smul, h]))
    evalTactic (← `(tactic| try ring_nf))

/-
`prove_flag_expand_with_forbidden_flag N` proves goals of the form
`F_forbidden =ₐ 0 ⊢ₐ F =ₐ (size N expansion of F excluding flags that containing F_forbidden)`.
-/
syntax (name := flagExpandWithForbiddenFlagTac)
  "prove_flag_expand_with_forbidden_flag " term : tactic

elab_rules : tactic
  | `(tactic| prove_flag_expand_with_forbidden_flag $N) =>
      runForbiddenFlagExpansion N

/-
`prove_flag_mul_with_forbidden_flag N` proves goals of the form
`F_forbidden =ₐ 0 ⊢ₐ F1 * F2 =ₐ (linear combination of size N flags)`.
-/
syntax (name := flagMulWithForbiddenFlagTac)
  "prove_flag_mul_with_forbidden_flag " term : tactic

elab_rules : tactic
  | `(tactic| prove_flag_mul_with_forbidden_flag $N) =>
      runForbiddenFlagMul N

end FlagLogic
