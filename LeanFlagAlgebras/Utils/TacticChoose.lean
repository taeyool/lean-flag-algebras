import Lean
import Init.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Nat

/-! # `simp_choose_eq` tactic: clearing binomial coefficients in `ℕ` equalities

Shared custom tactic for goals that equate products of `Nat.choose` terms. It cross-multiplies
by the product of all `k! * (n-k)!` denominators (proving that product nonzero), reduces each
`n.choose k` to a factorial identity, and introduces named hypotheses
`<base>_lhs_i` / `<base>_rhs_i` of the form `n.choose k * k! * (n-k)! = n!` for the caller to
rewrite with. Used to discharge multinomial/binomial algebraic identities in the development.
-/

open Lean Elab Tactic Meta
namespace SimpChooseEqTactic

-- Data structure to hold information about one side of the equality
/-- Per-side accounting for `simp_choose_eq`: the `(n, k)` pairs of each `choose`, the
denominator product `∏ k!·(n-k)!`, the current product, and the target factorial product. -/
structure SideData where
  args : List (Expr × Expr)   -- List of (N, K). To be used to generate and prove K ≤ N later.
  denTerm : Expr              -- Product of (K! * (N-K)!) terms
  curTerm : Expr              -- Product of (N.choose K * K! * (N-K)!) terms
  newTerm : Expr              -- Product of N! terms

-- Recursive helper to gather data from one side of the equality
/-- Recursively walk a product expression on one side of the goal, collecting its `SideData`
(treating `Nat.choose n k` factors specially and recursing through `*`). -/
partial def processSideExpr (e : Expr) : TermElabM SideData := do
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.choose ..) n) k =>
    let n_fact ← mkAppM ``Nat.factorial #[n]
    let k_fact ← mkAppM ``Nat.factorial #[k]
    let nk_sub ← mkAppM ``HSub.hSub #[n, k]
    let nk_fact ← mkAppM ``Nat.factorial #[nk_sub]
    let den_fact ← mkAppM ``HMul.hMul #[k_fact, nk_fact]
    let cur_term_pre ← mkAppM ``HMul.hMul #[e, k_fact]
    let cur_term ← mkAppM ``HMul.hMul #[cur_term_pre, nk_fact]
    let new_term := n_fact
    return {
      args := [(n, k)],
      denTerm := den_fact,
      curTerm := cur_term,
      newTerm := new_term
    }

  | Expr.app (Expr.app e0 e1) e2 =>
    match e0 with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``HMul.hMul _) _) _) _) _ =>
        let data1 ← processSideExpr e1
        let data2 ← processSideExpr e2
        let den_term ← mkAppM ``HMul.hMul #[data1.denTerm, data2.denTerm]
        let cur_term ← mkAppM ``HMul.hMul #[data1.curTerm, data2.curTerm]
        let new_term ← mkAppM ``HMul.hMul #[data1.newTerm, data2.newTerm]
        return {
          args := data1.args ++ data2.args,
          denTerm := den_term,
          curTerm := cur_term,
          newTerm := new_term
        }

    | _ =>
        return {
          args := [],
          denTerm := mkNatLit 1,
          curTerm := e,
          newTerm := e
        }

  | _ =>
    return {
      args := [],
      denTerm := mkNatLit 1,
      curTerm := e,
      newTerm := e
    }

-- Helper to assert an assumption and get the new MVarId and FVarId of the hypothesis.
/-- Add `proof : type` as a named hypothesis to the goal, returning its `FVarId` and the
updated goal. -/
def assertHyp (mvarId : MVarId) (type : Expr) (proof : Expr) (userName : Name) : MetaM (FVarId × MVarId) := do
  let mvarIdNew ← mvarId.assert userName type proof
  let (fvarId, newerMVarId) ← mvarIdNew.intro1P
  return (fvarId, newerMVarId)

/-- `simp_choose_eq `base` reduces a goal that equates products of `Nat.choose` terms to a
factorial identity, introducing rewrite hypotheses `base_lhs_i` / `base_rhs_i` of the form
`n.choose k * k! * (n-k)! = n!`. Requires `k ≤ n` for every `choose` term. -/
elab "simp_choose_eq" baseName:name : tactic =>
  withMainContext do
    let mainGoal ← getMainGoal
    let goalType ← mainGoal.getType

    -- Step 1: Check if the goal is an equality. Gather data from both sides.
    guard goalType.isEq <|> throwError "Goal is not an equality"
    let lhsExpr := goalType.appFn!.appArg!
    let rhsExpr := goalType.appArg!
    let lhsData ← processSideExpr lhsExpr
    let rhsData ← processSideExpr rhsExpr

    -- Step 2: We show that to prove the goal, it is sufficient to show that

    --    lhsExpr * combDen = rhsExpr * combDen
    --
    -- where combDen is the product of all denominators from both sides:
    --
    --     combDen := lhsData.denTerm * rhsData.denTerm
    --
    -- For this purpuse, we prove that combDen != 0, and use it with Nat.pos_iff_ne_zero.mp.

    -- Prove that the combined product of all denominators is positive.
    let combDen ← mkAppM ``HMul.hMul #[lhsData.denTerm, rhsData.denTerm]
    let posCombDenType ← mkAppM ``LT.lt #[mkNatLit 0, combDen]

    let posCombDenMVar ← mkFreshExprMVar posCombDenType
    let posCombDenTactic ← `(tactic| repeat (first | apply mul_pos | simp only [Nat.factorial_pos, Nat.succ_pos]))
    let posCombDenLeftGoals ← Tactic.run posCombDenMVar.mvarId! (evalTactic posCombDenTactic)
    if !posCombDenLeftGoals.isEmpty then
      throwError m!"[choose_eq] Failed to prove the positivity of the product of all denominators:
          {← ppExpr posCombDenType}
      Proof attempt:
          {← ppExpr posCombDenMVar}"
    let posCombDenProof ← instantiateMVars posCombDenMVar

    -- Now, derive combDen ≠ 0 from 0 < combDen.
    -- Then, apply Nat.mul_left_inj to change the goal to:
    --
    --   lhsExpr * combDen = rhsExpr * combDen
    --
    let nonZeroLemma ← mkAppOptM ``Nat.pos_iff_ne_zero #[combDen]
    let h_ne_zero_proof ← mkAppM ``Iff.mp #[nonZeroLemma, posCombDenProof]
    let mulLeftInjLemma ← mkAppOptM ``Nat.mul_left_inj #[combDen, lhsExpr, rhsExpr, h_ne_zero_proof]

    let transCombDen ← mkAppM ``Iff.mp #[mulLeftInjLemma]
    let goalAfterCombDen ← (← getMainGoal).apply transCombDen
    if goalAfterCombDen.isEmpty then
      throwError "[choose_eq] No goals after Step 3."
    replaceMainGoal [goalAfterCombDen[0]!]

    -- Step 3: Reduce the current goal to the one below:
    --
    --     lhsData.curTerm * rhsData.denTerm = rhsData.curTerm * lhsData.denTerm
    --
    -- We do this in three stages. First, we show that
    --
    --     lhsExpr * combDeno = lhsData.curTerm * rhsData.denTerm
    --
    -- and reduce the goal using Eq.trans to:
    --
    --     lhsData.curTerm * rhsData.denTerm = rhsExpr * combDen
    --
    -- Next, we show that
    --
    --     rhsData.curTerm * lhsData.denTerm = rhsExpr * combDen
    --
    -- and reduce the goal again using Eq.trans to:
    --
    --     lhsData.curTerm * rhsData.denTerm = rhsData.curTerm * lhsData.denTerm
    --
    -- as desired.
    let lhsExtended ← mkAppM ``HMul.hMul #[lhsExpr, combDen]
    let rhsExtended ← mkAppM ``HMul.hMul #[rhsExpr, combDen]
    let lhsGrouped ← mkAppM ``HMul.hMul #[lhsData.curTerm, rhsData.denTerm]
    let rhsGrouped ← mkAppM ``HMul.hMul #[rhsData.curTerm, lhsData.denTerm]

    let groupedType1 ← mkAppM ``Eq #[lhsExtended, lhsGrouped]
    let groupedType2 ← mkAppM ``Eq #[rhsGrouped, rhsExtended]
    let groupedType3 ← mkAppM ``Eq #[lhsGrouped, rhsExtended]
    let groupedType4 ← mkAppM ``Eq #[lhsGrouped, rhsGrouped]

    let groupedMVar1 ← mkFreshExprMVar groupedType1
    let groupedMVar2 ← mkFreshExprMVar groupedType2
    let groupedMVar3 ← mkFreshExprMVar groupedType3
    let groupedMVar4 ← mkFreshExprMVar groupedType4

    let groupedTactic ← `(tactic| ring_nf)
    let groupedMVarRest1 ← Tactic.run groupedMVar1.mvarId! (evalTactic groupedTactic)
    let groupedMVarRest2 ← Tactic.run groupedMVar2.mvarId! (evalTactic groupedTactic)

    if !groupedMVarRest1.isEmpty then
      throwError m!"[choose_eq] Failed to prove the equality for the grouping of factors on the LHS:
          {← ppExpr groupedType1}
      Proof attempt:
          {← ppExpr groupedMVar1}"
    if !groupedMVarRest2.isEmpty then
      throwError m!"[choose_eq] Failed to prove the equality for the grouping of factors on the RHS:
          {← ppExpr groupedType2}
      Proof attempt:
          {← ppExpr groupedMVar2}"
    let groupedProof1 ← instantiateMVars groupedMVar1
    let groupedProof2 ← instantiateMVars groupedMVar2

    let transGrouped1 ← mkAppM ``Eq.trans #[groupedProof1, groupedMVar3]
    let transGrouped2 ← mkAppM ``Eq.trans #[groupedMVar4, groupedProof2]

    let goalAfterGrouped1 ← (← getMainGoal).apply transGrouped1
    if goalAfterGrouped1.isEmpty then
      throwError "[choose_eq] No goal after grouping the LHS at Step 4."
    replaceMainGoal [goalAfterGrouped1[0]!]

    let goalAfterGrouped2 ← (← getMainGoal).apply transGrouped2
    if goalAfterGrouped2.isEmpty then
      throwError "[choose_eq] No goal after grouping the RHS at Step 4."
    replaceMainGoal [goalAfterGrouped2[0]!]

    -- Step 4: Generate lemmas that show the equalities between choose product two factorials and one factorial.
    --
    let mut contractedRefinedGoalId1 ← getMainGoal

    for i in [:lhsData.args.length] do
      let (n, k) := lhsData.args[i]!
      let leType ← mkAppM ``LE.le #[k, n]
      let leMVar ← mkFreshExprMVar leType
      let leTactic ← `(tactic| (first | omega))
      let leLeftGoals ← Tactic.run leMVar.mvarId! (evalTactic leTactic)
      if !leLeftGoals.isEmpty then
        throwError "[choose_eq] Failed to prove {← ppExpr leType} for term C({← ppExpr n}, {← ppExpr k}) in LHS. This tactic requires k ≤ n for all choose terms."
      let leProof ← instantiateMVars leMVar
      let contractedProof ← mkAppM ``Nat.choose_mul_factorial_mul_factorial #[leProof]
      let contractedType ← inferType contractedProof
      let (_, newId) ← assertHyp
                        contractedRefinedGoalId1
                        contractedType
                        contractedProof
                        ((baseName.getName.appendAfter "_lhs").appendIndexAfter i)
      contractedRefinedGoalId1 := newId

    replaceMainGoal [contractedRefinedGoalId1]

    let mut contractedRefinedGoalId2 ← getMainGoal

    for i in [:rhsData.args.length] do
      let (n, k) := rhsData.args[i]!
      let leType ← mkAppM ``LE.le #[k, n]
      let leMVar ← mkFreshExprMVar leType .syntheticOpaque
      let leTactic ← `(tactic| first | omega)
      let leLeftGoals ← Tactic.run leMVar.mvarId! (evalTactic leTactic)
      if !leLeftGoals.isEmpty then
        throwError "[choose_eq] Failed to prove {← ppExpr leType} for term C({← ppExpr n}, {← ppExpr k}) in RHS. This tactic requires k ≤ n for all choose terms."
      let leProof ← instantiateMVars leMVar
      let contractedProof ← mkAppM ``Nat.choose_mul_factorial_mul_factorial #[leProof]
      let contractedType ← inferType contractedProof
      let (_, newId) ← assertHyp
                        contractedRefinedGoalId2
                        contractedType
                        contractedProof
                        ((baseName.getName.appendAfter "_rhs").appendIndexAfter i)
      contractedRefinedGoalId2 := newId

    replaceMainGoal [contractedRefinedGoalId2]

    return
end SimpChooseEqTactic

/-
open SimpChooseEqTactic

-- Example usage and tests

example (n k j : Nat) (h1 : j ≤ k) (h2 : k ≤ n) :
    n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) := by
  simp_choose_eq `h
  rw [h_lhs_0, h_lhs_1, h_rhs_0, h_rhs_1]
  have : n - j - (k - j) = n - k := by omega
  rw [this]
  ring

example : Nat.choose 5 2 * Nat.choose 3 1 = Nat.choose 5 1 * Nat.choose 4 2 := by
  simp_choose_eq `h
  rw [h_lhs_0, h_lhs_1, h_rhs_0, h_rhs_1]
  ring

example
  (h_lhs_contr_0 : Nat.choose 5 2 * Nat.factorial 2 * (5 - 2).factorial = Nat.factorial 5)
  (h_lhs_contr_1 : Nat.choose 3 1 * Nat.factorial 1 * (3 - 1).factorial = Nat.factorial 3)
  (h_rhs_contr_0 : Nat.choose 5 1 * Nat.factorial 1 * (5 - 1).factorial = Nat.factorial 5)
  (h_rhs_contr_1 : Nat.choose 4 2 * Nat.factorial 2 * (4 - 2).factorial = Nat.factorial 4)
  : Nat.choose 5 2 * Nat.factorial 2 * (5 - 2).factorial * (Nat.choose 3 1 * Nat.factorial 1 * (3 - 1).factorial) *
    (Nat.factorial 1 * (5 - 1).factorial * (Nat.factorial 2 * (4 - 2).factorial))
    =
    Nat.factorial 5 * Nat.factorial 3 * (Nat.factorial 1 * (5 - 1).factorial * (Nat.factorial 2 * (4 - 2).factorial))
  := by
  rw [h_lhs_contr_0, h_lhs_contr_1]

set_option pp.explicit true in
elab "my_custom_rewrite" : tactic =>
  withMainContext do
    -- let rwRule : TSyntax `Lean.Parser.Tactic.rwRule := TSyntax.mk (mkIdent `h0)
    -- let tacticSyntax ← `(tactic| rw [$rwRule])
    let hs := #[mkIdent `h1, mkIdent `h0]
    let tacticSyntax ← `(tactic| rw [$[$hs:ident],*])
    -- throwError m!"{tacticSyntax}"
    evalTactic tacticSyntax

set_option pp.explicit true in
theorem example_with_hyps (a b c d : Nat)
    (h0 : a = 100)
    (h1 : b = a)
    (h2 : c = d)
    (h_final : d = 100) : b = 100 := by
  my_custom_rewrite

lemma factorial_property
    (ℓ : Nat) (ℓ₁ ℓ₂ ℓ₃ ℓ₁₂ ℓ₂₃ : Nat)
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    : ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
      = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  :=
  let C₁₂ : ℕ := (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  let C₂₃ : ℕ := (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₁₂_C₂₃ :
      ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂
      = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃
    := by
    dsimp [C₁₂, C₂₃]
    simp_choose_eq `h_choose
    rw [h_choose_lhs_0, h_choose_lhs_1, h_choose_lhs_2, h_choose_lhs_3, h_choose_lhs_4]
    rw [h_choose_rhs_0, h_choose_rhs_1, h_choose_rhs_2, h_choose_rhs_3, h_choose_rhs_4]
    ring_nf
    have h₁ : ℓ₁₂ - (ℓ₁ + ℓ₂) = ℓ₁₂ - ℓ₁ - ℓ₂ := by omega
    have h₂ : ℓ₁₂ - ℓ₁ - ℓ₂ - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega
    have h₃ : ℓ - ℓ₂₃ - ℓ₁ = ℓ - (ℓ₁ + ℓ₂₃) := by omega
    have h₄ : ℓ₂₃ - ℓ₂ - ℓ₃ = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega
    have h₅ : ℓ - (ℓ₁ + ℓ₂₃) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ - ℓ₁₂ - ℓ₃ := by omega
    rw [h₁, h₂, h₃, h₄, h₅]
    ring_nf

  h_C₁₂_C₂₃
-/
