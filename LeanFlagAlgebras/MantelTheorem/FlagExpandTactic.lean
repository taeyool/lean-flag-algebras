import Mathlib.Tactic
import LeanFlagAlgebras.MantelTheorem.FlagDef

open Lean Elab Tactic Meta

namespace MantelTheorem

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

/--
`flag_unit_expand N` proves goals of the form
`(one loaded flag algebra basis element) = (its size N expansion)`.

It automatically:
1) moves to `FlagVector` via `Quotient.sound`,
2) infers the LHS flag and applies `unitVector_eqv_densityFlagSum`,
3) unfolds `densityFlagSum`,
4) rewrites using generated `flagSet_{N}_{k}_{m}_eq_univ` and `flagSet_{N}_{k}_{m}_val_eq`,
5) closes by normalization (`ring_nf`), so RHS add-order differences are tolerated.
-/
syntax (name := flagUnitExpandTac) "flag_unit_expand " term : tactic

syntax (name := flagLinearUnitStartCompatTac)
  "flag_linear_unit_start " term " at " term : tactic

syntax (name := flagLinearOneStartCompatTac)
  "flag_linear_one_start " term : tactic

elab_rules : tactic
  | `(tactic| flag_unit_expand $N) => do
      withMainContext do
        if (← getGoals).isEmpty then
          pure ()

        let runIfGoals (stx : Syntax) : TacticM Unit := do
          unless (← getGoals).isEmpty do
            evalTactic stx

        let nExpr ← elabTerm N (some (mkConst ``Nat))
        let some nVal ← (Meta.evalNat nExpr).run
          | throwError "Could not evaluate N to a natural number in `flag_unit_expand`."

        let goalTy ← (← getMainGoal).getType
        let some (_, lhs, _) := goalTy.eq?
          | throwError "Goal must be an equality."

        let some lhsConst := findFlagAlgebraConst? lhs
          | throwError "Could not find a `FlagAlgebra_*` constant on the LHS."

        let some (lhsN, kVal, mVal, iVal) := parseFlagAlgebraIndices? lhsConst
          | throwError m!"Could not parse indices from LHS constant `{lhsConst}`."

        let flagName : Name := Name.mkSimple s!"Flag_{lhsN}_{kVal}_{mVal}_{iVal}"
        let flagId : TSyntax `term := mkIdent flagName
        let lhsNStx : TSyntax `term := Syntax.mkNumLit (toString lhsN)
        let finFlagTerm ← `(term| ⟨$lhsNStx, $flagId⟩)

        let eqUnivName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_eq_univ"
        let valEqName : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"

        runIfGoals (← `(tactic| apply Quotient.sound))
        runIfGoals (← `(tactic| dsimp))
        runIfGoals (← `(tactic|
          refine FlagAlgebras.flagVectorEqv.trans
            (FlagAlgebras.unitVector_eqv_densityFlagSum $finFlagTerm $N (by simp)) ?_))
        runIfGoals (← `(tactic| dsimp [FlagAlgebras.densityFlagSum]))

        let eqUnivId : TSyntax `ident := mkIdent eqUnivName
        let valEqId : TSyntax `ident := mkIdent valEqName
        runIfGoals (← `(tactic| have h_eq_univ := $eqUnivId))
        runIfGoals (← `(tactic| have h_val_eq := $valEqId))
        runIfGoals (← `(tactic| rw [Finset.sum_eq_multiset_sum, ← h_eq_univ]))
        runIfGoals (← `(tactic| simp [h_val_eq]))
        try
          runIfGoals (← `(tactic| ring_nf))
        catch _ =>
          pure ()
        try
          runIfGoals (← `(tactic| apply FlagAlgebras.flagVector_eq_eqv; ring_nf))
        catch _ =>
          pure ()
        try
          runIfGoals (← `(tactic| apply FlagAlgebras.flagVector_eq_eqv; simp [add_assoc, add_left_comm, add_comm]))
        catch _ =>
          pure ()

end MantelTheorem
