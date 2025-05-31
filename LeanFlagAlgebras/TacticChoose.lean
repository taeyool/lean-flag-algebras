import Lean
import Init.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Nat

open Lean Elab Tactic Meta
namespace ChooseEqTactic

-- Data structure to hold information about one side of the equality
structure SideData where
  args : List (Expr × Expr)   -- List of (N, K). To be used to generate and prove K ≤ N later.
  denTerm : Expr              -- Product of (K! * (N-K)!) terms
  curTerm : Expr              -- Product of (N.choose K * K! * (N-K)!) terms
  newTerm : Expr              -- Product of N! terms

-- Recursive helper to gather data from one side of the equality
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
def assertHyp (mvarId : MVarId) (type : Expr) (proof : Expr) (userName : Name) : MetaM (FVarId × MVarId) := do
  let mvarIdNew ← mvarId.assert userName type proof
  let (fvarId, newerMVarId) ← mvarIdNew.intro1P
  return (fvarId, newerMVarId)

elab "choose_eq" : tactic =>
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
    -- For this purpuse, we prove that combTerm != 0, and use it with Nat.post_iff_ne_zero.mp.

    -- Prove that the combined product of all denominators is positive.
    let combDen ← mkAppM ``HMul.hMul #[lhsData.denTerm, rhsData.denTerm]
    let posCombDenType ← mkAppM ``LT.lt #[mkNatLit 0, combDen]

    let posCombDenMVar ← mkFreshExprMVar posCombDenType (userName := `h_den_pos)
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

    -- Step 4: Reduce the current goal to the one below:
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

    let groupedMVar1 ← mkFreshExprMVar groupedType1 .syntheticOpaque
    let groupedMVar2 ← mkFreshExprMVar groupedType2 .syntheticOpaque
    let groupedMVar3 ← mkFreshExprMVar groupedType3 .syntheticOpaque
    let groupedMVar4 ← mkFreshExprMVar groupedType4 .syntheticOpaque

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

    let transGrouped1 ← mkAppM ``Eq.trans #[groupedMVar1, groupedMVar3]
    let transGrouped2 ← mkAppM ``Eq.trans #[groupedMVar4, groupedMVar2]

    let goalAfterGrouped1 ← (← getMainGoal).apply transGrouped1
    if goalAfterGrouped1.isEmpty then
      throwError "[choose_eq] No goal after grouping the LHS at Step 4."
    replaceMainGoal [goalAfterGrouped1[0]!]

    let goalAfterGrouped2 ← (← getMainGoal).apply transGrouped2
    if goalAfterGrouped2.isEmpty then
      throwError "[choose_eq] No goal after grouping the RHS at Step 4."
    replaceMainGoal [goalAfterGrouped2[0]!]

    -- Step 5: Reduce the current goal to the one below:
    --
    --     lhsData.newTerm * rhsData.denTerm = rhsData.newTerm * lhsData.denTerm
    --
    -- We do this in three stages. First, we show that
    --
    --     lhsData.curTerm * rhsData.denTerm = lhsData.newTerm * rhsData.denTerm
    --
    -- and reduce the goal using Eq.trans to:
    --
    --     lhsData.newTerm * rhsData.denTerm = rhsData.curTerm * lhsData.denTerm
    --
    -- Next, we show that
    --
    --     rhsData.newTerm * lhsData.denTerm = rhsData.curTerm * lhsData.denTerm
    --
    -- and reduce the goal again using Eq.trans to:
    --
    --     lhsData.newTerm * rhsData.denTerm = rhsData.newTerm * lhsData.denTerm
    --
    -- as desired.
    let mut contractedRefinedGoalId1 ← getMainGoal

    for i in [:lhsData.args.length] do
      let (n, k) := lhsData.args[i]!
      let leType ← mkAppM ``LE.le #[k, n]
      let leMVar ← mkFreshExprMVar leType .syntheticOpaque
      let leTactic ← `(tactic| (first | omega))
      let leLeftGoals ← Tactic.run leMVar.mvarId! (evalTactic leTactic)
      if !leLeftGoals.isEmpty then
        throwError "[choose_eq] Failed to prove {← ppExpr leType} for term C({← ppExpr n}, {← ppExpr k}) in LHS. This tactic requires k ≤ n for all choose terms."
      let contractedProof ← mkAppM ``Nat.choose_mul_factorial_mul_factorial #[leMVar]
      let contractedType ← inferType contractedProof
      let (_, newId) ← assertHyp contractedRefinedGoalId1 contractedType contractedProof ((`h_lhs_contr).appendIndexAfter i)
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
      let contractedProof ← mkAppM ``Nat.choose_mul_factorial_mul_factorial #[leMVar]
      let contractedType ← inferType contractedProof
      let (_, newId) ← assertHyp contractedRefinedGoalId2 contractedType contractedProof ((`h_rhs_contr).appendIndexAfter i)
      contractedRefinedGoalId2 := newId

    replaceMainGoal [contractedRefinedGoalId2]

    let lhsContracted ← mkAppM ``HMul.hMul #[lhsData.newTerm, rhsData.denTerm]
    let rhsContracted ← mkAppM ``HMul.hMul #[rhsData.newTerm, lhsData.denTerm]

    let contractedType1 ← mkAppM ``Eq #[lhsGrouped, lhsContracted]
    let contractedType2 ← mkAppM ``Eq #[rhsContracted, rhsGrouped]
    let contractedType3 ← mkAppM ``Eq #[lhsContracted, rhsGrouped]
    let contractedType4 ← mkAppM ``Eq #[lhsContracted, rhsContracted]

    let contractedMVar1 ← mkFreshExprMVar contractedType1 .syntheticOpaque
    let contractedMVar2 ← mkFreshExprMVar contractedType2 .syntheticOpaque
    let contractedMVar3 ← mkFreshExprMVar contractedType3 .syntheticOpaque
    let contractedMVar4 ← mkFreshExprMVar contractedType4 .syntheticOpaque

    let contractedTactic ← `(tactic| repeat cc)
    let contractedMVarRest1 ← Tactic.run contractedMVar1.mvarId! (evalTactic contractedTactic)
    let contractedMVarRest2 ← Tactic.run contractedMVar2.mvarId! (evalTactic contractedTactic)

    if !contractedMVarRest1.isEmpty then
      throwError m!"[choose_eq] Failed to prove the equality for the contraction of factors on the LHS:
          {← ppExpr contractedType1}
      Proof attempt:
          {← ppExpr contractedMVar1}
      Goal state:
          {← Meta.ppGoal (← getMainGoal)}"
    if !contractedMVarRest2.isEmpty then
      throwError m!"[choose_eq] Failed to prove the equality for the contraction of factors on the RHS:
          {← ppExpr contractedType2}
      Proof attempt:
          {← ppExpr contractedMVar2}"

    let transContracted1 ← mkAppM ``Eq.trans #[contractedMVar1, contractedMVar3]
    let transContracted2 ← mkAppM ``Eq.trans #[contractedMVar4, contractedMVar2]

    let goalAfterContracted1 ← (← getMainGoal).apply transContracted1
    if goalAfterContracted1.isEmpty then
      throwError "[choose_eq] No goal after grouping the LHS at Step 5."
    replaceMainGoal [goalAfterContracted1[0]!]

    let goalAfterContracted2 ← (← getMainGoal).apply transContracted2
    if goalAfterContracted2.isEmpty then
      throwError "[choose_eq] No goal after grouping the RHS at Step 5."
    replaceMainGoal [goalAfterContracted2[0]!]

    evalTactic (← `(tactic| try simp only [Nat.sub_eq, Nat.add_one_sub_one, Nat.reduceSub]; try ring_nf))
    return
  /-
    --     rhsExpr * combinedDenominator = rhsData.curTerm * lhsData.denFactorialProd
    -- Second, by using the "simp only [Nat.choose_mul_factorial_mul_factorial]", we show that
    --     lhsData.curTerm * rhsData.denFactorialProd = lhsData.newTerm * rhsData.denFactorialProd
    --     rhsData.curTerm * lhsData.denFactorialProd = rhsData.newTerm * rhsData.denoFactorialProd
    -- Finally, using the ring tactic, we show that
    --     lhsData.newTerm * rhsData.denFactorialProd = rhsData.newTerm * lhsData.denFactorialProd


    /-
    throwError m!"[choose_eq] Current goal state:\n{← Meta.ppGoal (← getMainGoal)}"

    throwError m!"[choose_eq] lhsData and rhsData:
        lhsExpr = {← ppExpr lhsExpr},
        rhsExpr = {← ppExpr rhsExpr},
        lhsData.denTerm = {← ppExpr lhsData.denTerm},
        rhsData.denTerm = {← ppExpr rhsData.denTerm}
        lhsData.curTerm = {← ppExpr lhsData.curTerm},
        rhsData.curTerm = {← ppExpr rhsData.curTerm},
        lhsData.newTerm = {← ppExpr lhsData.newTerm},
        rhsData.newTerm = {← ppExpr rhsData.newTerm}"
    -/

/-
    let oneLit := mkNatLit 1
    let h_le_type ← mkAppM ``LE.le #[k, n]
    let h_le_mvar ← mkFreshExprMVar h_le_type .syntheticOpaque (userName := `h_le)
    let tacticStx ← `(tactic| simp_all (config := {decide := true, arith := true, contextual := true}))
    let remainingGoals ← Tactic.run h_le_mvar.mvarId! (evalTactic tacticStx)
    throwError "[choose_eq] Failed to prove {← ppExpr h_le_type} for term C({← ppExpr n}, {← ppExpr k}). This tactic requires k ≤ n for all choose terms."
    if !remainingGoals.isEmpty then
      throwError "[choose_eq] Failed to prove {← ppExpr h_le_type} for term C({← ppExpr n}, {← ppExpr k}). This tactic requires k ≤ n for all choose terms."
-/

    -- We want to change the goal from `lhsExpr = rhsExpr` to `lhsExpr * combinedDenominators = rhsExpr * combinedDenominators`.
    -- The `mulLeftInjLemma` is `(lhsExpr * combinedDen. = rhsExpr * combinedDen.) ↔ (lhsExpr = rhsExpr)`.
    -- `Iff.mp mulLeftInjLemma` gives `(lhsExpr * combinedDen. = rhsExpr * denCombinedDeno.) → (lhsExpr = rhsExpr)`.
    -- Applying this to the current goal `lhsExpr = rhsExpr` changes the goal to `lhsExpr * den = rhsExpr * den`.


    evalTactic (← `(tactic| try simp only [Nat.sub_eq, Nat.add_one_sub_one, Nat.reduceSub]; try ring_nf))
    return

  /-
    -- Step 3: Use `conv` to rewrite products involving `Nat.choose` terms.
    -- `Nat.choose_mul_factorial_mul_factorial` will be applied using the `k <= n` hypotheses now in context.
    -- `mul_assoc`, `mul_comm`, `mul_left_comm` are used to rearrange terms for the rewrite.
    evalTactic (← `(tactic|
      conv =>
        lhs
        (simp (config := {failIfUnchanged := false, arith := true, contextual := true}) only [Nat.choose_mul_factorial_mul_factorial, mul_assoc, mul_comm, mul_left_comm])))
    evalTactic (← `(tactic|
      conv =>
        rhs
        (simp (config := {failIfUnchanged := false, arith := true, contextual := true}) only [Nat.choose_mul_factorial_mul_factorial, mul_assoc, mul_comm, mul_left_comm])))
    evalTactic (← `(tactic| try ring))
    evalTactic (← `(tactic| try rfl))
    evalTactic (← `(tactic| try ring_nf))
  -/
  -/

end ChooseEqTactic

open ChooseEqTactic

-- Example usage and tests

example : Nat.choose 5 2 * Nat.choose 3 1 = Nat.choose 5 1 * Nat.choose 4 2 := by
  choose_eq

example : Nat.choose 5 2 = Nat.choose 5 2 := by
  choose_eq

example : Nat.choose 4 2 = (Nat.factorial 4) / (Nat.factorial 2 * Nat.factorial 2) := by
  choose_eq

example (n k j : Nat) (h1 : j ≤ k) (h2 : k ≤ n) :
    n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) := by
  choose_eq
  sorry

example
  (n k j : ℕ)
  (h1 : j ≤ k)
  (h2 : k ≤ n)
  (h_lhs_contr_0 : n.choose k * k.factorial * (n - k).factorial = n.factorial)
  (h_lhs_contr_1 : k.choose j * j.factorial * (k - j).factorial = k.factorial)
  (h_rhs_contr_0 : n.choose j * j.factorial * (n - j).factorial = n.factorial)
  (h_rhs_contr_1 : (n - j).choose (k - j) * (k - j).factorial * (n - j - (k - j)).factorial = (n - j).factorial)
  :  n.choose k * k.factorial * (n - k).factorial * (k.choose j * j.factorial * (k - j).factorial) *
      (j.factorial * (n - j).factorial * ((k - j).factorial * (n - j - (k - j)).factorial))
      =
    n.choose j * j.factorial * (n.sub j).factorial *
        ((n - j).choose (k - j) * (k - j).factorial * ((n - j).sub (k - j)).factorial) *
      (k.factorial * (n.sub k).factorial * (j.factorial * (k.sub j).factorial))
:= by
repeat cc
