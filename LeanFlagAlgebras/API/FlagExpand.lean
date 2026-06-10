import LeanFlagAlgebras.API.ExprHelpers

/-! # API.FlagExpand — flag expansion tactics

General-purpose proof automation for flag-algebra computations. Provides two
tactics that expand a flag-algebra element as a finite flag sum:

* `flag_expand_forbid N` — expand a flag at size `N` under a
  forbidden-subgraph (density-zero) restriction hypothesis.
* `flag_expand N` — expand one flag-algebra basis element as its size-`N`
  flag sum.

Both rewrite via the generated `flagSet_*_eq_univ` / `flagSet_*_val_eq`
lemmas and close by algebraic normalization. These tactics are problem-agnostic
and used by the Flagmatic-to-Lean automation in `LeanFlagAlgebras/Flagmatic/`
as well as by individual theorem developments (e.g. `MantelTheorem`).

Shared Expr helpers (`findFlagAlgebraConst?`, `parseFlagAlgebraIndices?`, etc.)
are provided by `API.ExprHelpers`.

For flag-product reduction, see `API.FlagMulReduce`. -/

open Lean Elab Tactic Meta

namespace FlagAlgebras.API

/-
`flag_expand_forbid N` proves goals of the form
`∀ (φ : PositiveHom σ), φ F_forbidden = 0 → φ F = (size N expansion of F without F_forbidden)`.

It introduces `φ` and the restriction hypothesis, expands `F` with
`basisVector_quot_eq_sum`, maps by `φ`, rewrites the
size-`N` flag universe, and then substitutes the forbidden term using the
hypothesis.
-/
syntax (name := flagExpandForbidTac) "flag_expand_forbid " term : tactic

/-- Implementation of the `flag_expand_forbid N` tactic. -/
def runFlagExpandWithRestriction (N : TSyntax `term) : TacticM Unit :=
  withMainContext do
    let nExpr ← elabTerm N (some (mkConst ``Nat))
    let some nVal ← (Meta.evalNat nExpr).run
      | throwError "Could not evaluate N to a natural number in `flag_expand_forbid`."

    let target ← getMainTarget
    let flags := collectPrefixConstants "FlagAlgebra_" target
    if flags.isEmpty then pure ()
    else
      let idents := flags.map mkIdent
      evalTactic (← `(tactic| dsimp [$[$idents:ident],*]))

    evalTactic (← `(tactic| intro φ h))

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
    let valEqName  : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"
    let eqUnivId : TSyntax `ident := mkIdent eqUnivName
    let valEqId  : TSyntax `ident := mkIdent valEqName

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
    evalTactic (← `(tactic| simpa [one_div, add_assoc] using hφ))

elab_rules : tactic
  | `(tactic| flag_expand_forbid $N) =>
      runFlagExpandWithRestriction N

/--
`flag_expand N` proves goals of the form
`(one loaded flag algebra basis element) = (its size N expansion)`.

It automatically:
1) moves to `FlagVector` via `Quotient.sound`,
2) infers the LHS flag and applies `basisVector_eqv_densityFlagSum`,
3) unfolds `densityFlagSum`,
4) rewrites using generated `flagSet_{N}_{k}_{m}_eq_univ` and `flagSet_{N}_{k}_{m}_val_eq`,
5) closes by normalization (`ring_nf`), so RHS add-order differences are tolerated.
-/
syntax (name := flagExpandTac) "flag_expand " term : tactic

elab_rules : tactic
  | `(tactic| flag_expand $N) => do
      withMainContext do
        if (← getGoals).isEmpty then
          pure ()

        let runIfGoals (stx : Syntax) : TacticM Unit := do
          unless (← getGoals).isEmpty do
            evalTactic stx

        let nExpr ← elabTerm N (some (mkConst ``Nat))
        let some nVal ← (Meta.evalNat nExpr).run
          | throwError "Could not evaluate N to a natural number in `flag_expand`."

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
        let valEqName  : Name := Name.mkSimple s!"flagSet_{nVal}_{kVal}_{mVal}_val_eq"

        runIfGoals (← `(tactic| apply Quotient.sound))
        runIfGoals (← `(tactic| dsimp))
        runIfGoals (← `(tactic|
          refine FlagAlgebras.flagVectorEqv.trans
            (FlagAlgebras.basisVector_eqv_densityFlagSum $finFlagTerm $N (by simp)) ?_))
        runIfGoals (← `(tactic| dsimp [FlagAlgebras.densityFlagSum]))

        let eqUnivId : TSyntax `ident := mkIdent eqUnivName
        let valEqId  : TSyntax `ident := mkIdent valEqName
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

end FlagAlgebras.API
