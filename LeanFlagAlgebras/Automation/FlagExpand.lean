import LeanFlagAlgebras.Automation.ExprHelpers
import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.FlagAlgebra.Compute.Basic

/-! # Automation.FlagExpand — flag expansion tactics

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
are provided by `Automation.ExprHelpers`.

For flag-product reduction, see `Automation.FlagMulReduce`. -/

open Lean Elab Tactic Meta

namespace FlagAlgebras.Automation

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
2) infers the LHS flag and applies `basisVector_eqv_flagExpansion`,
3) unfolds `flagExpansion`,
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
            (FlagAlgebras.basisVector_eqv_flagExpansion $finFlagTerm $N (by simp)) ?_))
        runIfGoals (← `(tactic| dsimp [FlagAlgebras.flagExpansion]))

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

/--
`flag_expand_hfree N F` is the forbid-free single-flag analogue of `flag_expand N`.
On a goal `FlagAlgebra_n_k_m_i =ᵢ[⟨_, Sym2EmptyTypedFlag.toFlag ⟦F⟧⟩] (its size-`N` forbid-free
expansion)`, it expands the flag with `basisVector_quot_inducedForbidEq_sum` rewritten directly onto the
explicitly-generated forbid-free set `flagSetHfree_N_k_m_<F>` (via its filtered-completeness lemma
`…_eq` and `…_val_eq`) — never materialising the full `flagSet`, and dropping the forbidden terms
automatically (no manual `basisVector_inducedForbidEq_zero` step).

`F` is the **edge-based** forbidden graph: a `Sym2Graph mF` term (e.g. `K3 : Sym2Graph 3`), the
same identifier passed to `generate_pruned_forbid_free_*`. The forbidden flag is built directly
from it as `⟨_, Sym2EmptyTypedFlag.toFlag ⟦F⟧⟩` (matching the generators and the goal's `=ᵢ[ ]`),
so no canonical forbidden flag / `.toFinFlag` is needed.

Prerequisites: the forbid-free host set must exist (run `generate_forbid_free_flags N k m F`,
or the empty-typed `generate_forbid_free_empty_typed_flags N F` for `k = m = 0`), and the
relevant `flagDensity₁ …` evaluation lemmas must be `@[simp]`.
-/
syntax (name := flagExpandHfreeTac) "flag_expand_hfree " num ident term : tactic

elab_rules : tactic
  | `(tactic| flag_expand_hfree $N:num $forbid:ident $hmem:term) =>
      withMainContext do
        let nVal := N.getNat
        -- Strip any namespace qualifier so the tag matches the generated `flagSetHfree_*` names
        -- (the `generate_pruned_*` commands use the same last-dotted-component convention).
        let tagFull := forbid.getId.toString
        let tag := (tagFull.splitOn ".").getLastD tagFull
        let target ← getMainTarget
        let lhsExpr ←
          match target.getAppFnArgs with
          | (``Forbid.forbidEq, args) =>
              match args[args.size - 2]? with
              | some e => pure e
              | none => throwError "flag_expand_hfree: malformed `=[ ]` goal."
          | _ => throwError "flag_expand_hfree: goal must be `f =[H] g`."
        let some lhsConst := findFlagAlgebraConst? lhsExpr
          | throwError "flag_expand_hfree: no `FlagAlgebra_*` constant on the LHS of `=[ ]`."
        let some (lhsN, kVal, mVal, iVal) := parseFlagAlgebraIndices? lhsConst
          | throwError m!"flag_expand_hfree: could not parse indices from `{lhsConst}`."
        let flagId : TSyntax `term := mkIdent (Name.mkSimple s!"Flag_{lhsN}_{kVal}_{mVal}_{iVal}")
        let lhsNStx : TSyntax `term := Syntax.mkNumLit (toString lhsN)
        let setName : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_{kVal}_{mVal}_{tag}")
        let setEqId : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_{kVal}_{mVal}_{tag}_eq")
        let valEqId : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_{kVal}_{mVal}_{tag}_val_eq")
        -- The forbidden flag is the `FinFlag` of the term `⟦F⟧` (no canonical flag); its `.2` is
        -- `Sym2EmptyTypedFlag.toFlag ⟦F⟧`, matching the generators' `flagSetHfree_…_eq` filter and
        -- the goal's `=ᵢ[ ]`.
        let forbidFlagTm : TSyntax `term ←
          `((⟨_, FlagAlgebras.Compute.Sym2EmptyTypedFlag.toFlag ⟦$forbid⟧⟩ : FlagAlgebras.FinFlag ∅ₜ))
        evalTactic (← `(tactic|
          apply Forbid.forbidEqWith_trans
            (Forbid.basisVector_quot_forbidEq_sum_ofMem $forbidFlagTm
              $hmem ⟨$lhsNStx, $flagId⟩ $N (by decide))))
        evalTactic (← `(tactic|
          rw [Finset.sum_congr (s₂ := $setName) (by rw [$setEqId:term]; try congr 1) (fun _ _ => rfl)]))
        evalTactic (← `(tactic| simp only [Finset.sum_eq_multiset_sum, $valEqId:term]))
        evalTactic (← `(tactic| simp))
        -- Close the residual `produced =ᵢ[F] stated`. For a ≤2-term expansion `produced` is
        -- definitionally the stated RHS (`FlagAlgebra_n_k_m_i` unfolds to its `⟦basisVector⟧`),
        -- so `inducedForbidEq_refl` closes it directly. For ≥3-term expansions the produced sum is
        -- *right*-associated while the stated RHS is *left*-associated, so we first unfold the
        -- `FlagAlgebra_*` constants (making both sides `⟦basisVector⟧`-atoms) and finish with an
        -- additive-commutative normalization that is insensitive to the bracketing.
        evalTactic (← `(tactic| try exact Forbid.forbidEqWith_refl _ _))
        unless (← getGoals).isEmpty do
          withMainContext do
            let faIdents := (collectPrefixConstants "FlagAlgebra_" (← getMainTarget)).map mkIdent
            evalTactic (← `(tactic| refine Forbid.forbidEqWith_of_eq ?_))
            unless faIdents.isEmpty do
              evalTactic (← `(tactic| dsimp only [$[$faIdents:ident],*]))
            evalTactic (← `(tactic|
              first
                | rfl
                | abel
                | simp only [add_assoc, add_comm, add_left_comm]))

/--
`flag_expand_hfree_subgraph N F` is the **subgraph**-forbidding analogue of `flag_expand_hfree`.
On a goal `FlagAlgebra_n_k_m_i =[F.toLabeledGraph.graph] (its size-`N` subgraph-`F`-free expansion)`,
it expands the flag with the subgraph capstone `basisVector_quot_forbidEq_sum_subgraph` rewritten onto
the subgraph-`F`-free set `flagSetHfree_N_k_m_<F>` (via its `…_eq` / `…_val_eq`). Unlike the induced
`flag_expand_hfree`, it needs **no** membership argument — the capstone derives it from
`supergraphFamily`. Prerequisite: run `generate_subgraph_free_flags N k m F` (or the empty-typed
`generate_subgraph_free_empty_typed_flags N F`).
-/
syntax (name := flagExpandHfreeSubgraphTac) "flag_expand_hfree_subgraph " num ident : tactic

elab_rules : tactic
  | `(tactic| flag_expand_hfree_subgraph $N:num $forbid:ident) =>
      withMainContext do
        let nVal := N.getNat
        let tagFull := forbid.getId.toString
        let tag := (tagFull.splitOn ".").getLastD tagFull
        let target ← getMainTarget
        let lhsExpr ←
          match target.getAppFnArgs with
          | (``Forbid.forbidEq, args) =>
              match args[args.size - 2]? with
              | some e => pure e
              | none => throwError "flag_expand_hfree_subgraph: malformed `=[ ]` goal."
          | _ => throwError "flag_expand_hfree_subgraph: goal must be `f =[H] g`."
        let some lhsConst := findFlagAlgebraConst? lhsExpr
          | throwError "flag_expand_hfree_subgraph: no `FlagAlgebra_*` constant on the LHS of `=[ ]`."
        let some (lhsN, kVal, mVal, iVal) := parseFlagAlgebraIndices? lhsConst
          | throwError m!"flag_expand_hfree_subgraph: could not parse indices from `{lhsConst}`."
        let flagId : TSyntax `term := mkIdent (Name.mkSimple s!"Flag_{lhsN}_{kVal}_{mVal}_{iVal}")
        let lhsNStx : TSyntax `term := Syntax.mkNumLit (toString lhsN)
        let setName : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_{kVal}_{mVal}_{tag}")
        let setEqId : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_{kVal}_{mVal}_{tag}_eq")
        let valEqId : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_{kVal}_{mVal}_{tag}_val_eq")
        evalTactic (← `(tactic|
          apply Forbid.forbidEqWith_trans
            (basisVector_quot_forbidEq_sum_subgraph $forbid ⟨$lhsNStx, $flagId⟩ $N (by decide))))
        evalTactic (← `(tactic|
          rw [Finset.sum_congr (s₂ := $setName) (by rw [$setEqId:term]; try congr 1) (fun _ _ => rfl)]))
        evalTactic (← `(tactic| simp only [Finset.sum_eq_multiset_sum, $valEqId:term]))
        evalTactic (← `(tactic| simp))
        evalTactic (← `(tactic| try exact Forbid.forbidEqWith_refl _ _))
        unless (← getGoals).isEmpty do
          withMainContext do
            let faIdents := (collectPrefixConstants "FlagAlgebra_" (← getMainTarget)).map mkIdent
            evalTactic (← `(tactic| refine Forbid.forbidEqWith_of_eq ?_))
            unless faIdents.isEmpty do
              evalTactic (← `(tactic| dsimp only [$[$faIdents:ident],*]))
            evalTactic (← `(tactic|
              first
                | rfl
                | abel
                | simp only [add_assoc, add_comm, add_left_comm]))

end FlagAlgebras.Automation
