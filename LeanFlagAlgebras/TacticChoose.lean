import Lean
import Init.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Nat -- For ac_refl (CommSemiring for Nat)

open Lean Elab Tactic Meta

namespace ChooseEqTactic

-- Data structure to hold information about one side of the equality
structure SideData where
  chooseArgsProofs : List (Expr × Expr × Expr) -- List of (n_expr, k_expr, h_le_proof)
  denFactorialProd : Expr                      -- Product of (K! * (N-K)!) terms for this side's chooses
  curTerm : Expr                               -- (N.choose K * K! * (N-K)!)
  newTerm : Expr                               -- N!

-- Recursive helper to gather data from one side of the equality
partial def processSideExpr (e : Expr) : TermElabM SideData := do
  let oneLit := mkNatLit 1 -- MetaM operations are lifted to TermElabM
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.choose ..) n) k =>
    let h_le_type ← mkAppM ``LE.le #[k, n]
    -- Create a new metavariable for the proof k <= n
    let h_le_mvar ← mkFreshExprMVar h_le_type .syntheticOpaque (userName := `h_le)
    -- Try to solve k <= n automatically
    let tacticStx ← `(tactic| simp_all (config := {decide := true, arith := true}))
    let remainingGoals ← Tactic.run h_le_mvar.mvarId! (evalTactic tacticStx) -- Tactic.run is TermElabM
    if !remainingGoals.isEmpty then -- If simp_all fails (leaves subgoals), throw an error
      throwError "choose_eq: Failed to prove {← ppExpr h_le_type} for term C({← ppExpr n}, {← ppExpr k}). This tactic requires k ≤ n for all choose terms."

    let n_fact ← mkAppM ``Nat.factorial #[n]
    let k_fact ← mkAppM ``Nat.factorial #[k]
    let nk_sub ← mkAppM ``Nat.sub #[n, k]
    let nk_fact ← mkAppM ``Nat.factorial #[nk_sub]
    let den_fact ← mkAppM ``HMul.hMul #[k_fact, nk_fact]
    let cur_term_pre ← mkAppM ``HMul.hMul #[e, k_fact]
    let cur_term ← mkAppM ``HMul.hMul #[cur_term_pre, nk_fact]
    let new_term := n_fact

    return {
      chooseArgsProofs := [(n, k, h_le_mvar)],
      denFactorialProd := den_fact,
      curTerm := cur_term,
      newTerm := new_term
    }

  | Expr.app (Expr.app e0 e1) e2 =>
    match e0 with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``HMul.hMul _) _) _) _) _ =>
        let data1 ← processSideExpr e1
        let data2 ← processSideExpr e2
        let den_fact ← mkAppM ``HMul.hMul #[data1.denFactorialProd, data2.denFactorialProd]
        let cur_term ← mkAppM ``HMul.hMul #[data1.curTerm, data2.curTerm]
        let new_term ← mkAppM ``HMul.hMul #[data1.newTerm, data2.newTerm]
        return {
          chooseArgsProofs := data1.chooseArgsProofs ++ data2.chooseArgsProofs,
          denFactorialProd := den_fact,
          curTerm := cur_term,
          newTerm := new_term
        }
    | _ =>
        return {
          chooseArgsProofs := [],
          denFactorialProd := oneLit, -- No denominators from this term
          curTerm := e,
          newTerm := e
        }

  | _ => -- Not a choose or a multiplication, treat as an "other factor"
    -- This allows expressions like `A * n.choose k = B * m.choose j`
    -- where A and B are arbitrary expressions.
    return {
      chooseArgsProofs := [],
      denFactorialProd := oneLit, -- No denominators from this term
      curTerm := e,
      newTerm := e
    }

-- Helper to assert an assumption and get the new MVarId and FVarId of the hypothesis.
def assertHyp (mvarId : MVarId) (type : Expr) (proof : Expr) (userName : Name) : MetaM (FVarId × MVarId) := do
  let mvarIdNew ← mvarId.assert userName type proof
  let (fvarId, newerMVarId) ← mvarIdNew.intro1P
  return (fvarId, newerMVarId)

elab "choose_eq" t:term : tactic =>
  withMainContext do
    let mainGoal ← getMainGoal
    let goalType ← mainGoal.getType

    guard goalType.isEq <|> throwError "Goal is not an equality"
    let lhsExpr := goalType.appFn!.appArg!
    let rhsExpr := goalType.appArg!

    -- Step 1: Process both sides to extract choose terms, prove k <= n,
    -- and prepare products of numerators (N!) and denominators (K!(N-K)!).
    let lhsData ← processSideExpr lhsExpr
    let rhsData ← processSideExpr rhsExpr

    -- Assert all k <= n proofs in lhsData and rhsData into the context for `simp` to use later.
    let mut currentGoalId := mainGoal
    for i in [:lhsData.chooseArgsProofs.length] do
      let (_, _, h_le_proof) := lhsData.chooseArgsProofs[i]!
      let proofType ← inferType h_le_proof
      let (_, newId) ← assertHyp currentGoalId proofType h_le_proof ((`h_lhs_le).appendIndexAfter i)
      currentGoalId := newId
    for i in [:rhsData.chooseArgsProofs.length] do
      let (_, _, h_le_proof) := rhsData.chooseArgsProofs[i]!
      let proofType ← inferType h_le_proof
      let (_, newId) ← assertHyp currentGoalId proofType h_le_proof ((`h_rhs_le).appendIndexAfter i)
      currentGoalId := newId
    replaceMainGoal [currentGoalId]

    /-
    throwError m!"[choose_eq] Current goal state:\n{← Meta.ppGoal (← getMainGoal)}"

    throwError m!"[choose_eq] lhsData and rhsData:
        lhsExpr = {← ppExpr lhsExpr},
        rhsExpr = {← ppExpr rhsExpr},
        lhsData.curTerm = {← ppExpr lhsData.curTerm},
        rhsData.curTerm = {← ppExpr rhsData.curTerm},
        lhsData.newTerm = {← ppExpr lhsData.newTerm},
        rhsData.newTerm = {← ppExpr rhsData.newTerm},
        lhsData.denFactorialProd = {← ppExpr lhsData.denFactorialProd},
        rhsData.denFactorialProd = {← ppExpr rhsData.denFactorialProd}"
    -/

    -- Step 2: Justify the transformation to the factorial form.
    --     Goal: lhsExpr = rhsExpr
    --
    -- We prove this in three steps. Let
    --     combinedDenominator := lhsData.denFatorialProd * rhsData.denoFactorialProd
    -- First, using the ring tactic, we show:
    --     lhsExpr * combinedDenominator = lhsData.curTerm * rhsData.denFactorialProd
    --     rhsExpr * combinedDenominator = rhsData.curTerm * lhsData.denFactorialProd
    -- Second, by using the "simp only [Nat.choose_mul_factorial_mul_factorial]", we show that
    --     lhsData.curTerm * rhsData.denFactorialProd = lhsData.newTerm * rhsData.denFactorialProd
    --     rhsData.curTerm * lhsData.denFactorialProd = rhsData.newTerm * rhsData.denoFactorialProd
    -- Finally, using the ring tactic, we show that
    --     lhsData.newTerm * rhsData.denFactorialProd = rhsData.newTerm * lhsData.denFactorialProd

    -- Prove that the combined product of all denominators is positive.
    let combinedDenominators ← mkAppM ``HMul.hMul #[lhsData.denFactorialProd, rhsData.denFactorialProd]
    let combinedDenominatorsPositiveType ← mkAppM ``LT.lt #[mkNatLit 0, combinedDenominators]

    let positiveDenomMVar ← mkFreshExprMVar combinedDenominatorsPositiveType (userName := `h_den_pos)
    let tacticStxDenPos ← `(tactic| repeat (first | apply mul_pos | simp only [Nat.factorial_pos, Nat.succ_pos]))
    let remainingGoalsDenPos ← Tactic.run positiveDenomMVar.mvarId! (evalTactic tacticStxDenPos)
    if !remainingGoalsDenPos.isEmpty then
      throwError m!"[choose_eq] Failed to prove the positivity of the product of all denominators:
          {← ppExpr combinedDenominators}
      Proof attempt:
          {← ppExpr positiveDenomMVar}"
    let positiveDenomProof ← instantiateMVars positiveDenomMVar

    -- Apply Nat.mul_left_inj to change the goal to:
    --   lhsExpr * combinedDenominators = rhsExpr * combinedDenominators
    -- Derive combinedDenominators ≠ 0 from 0 < combinedDenominators
    let posIffNeZeroTheorem ← mkAppOptM ``Nat.pos_iff_ne_zero #[combinedDenominators]
    let h_ne_zero_proof ← mkAppM ``Iff.mp #[posIffNeZeroTheorem, positiveDenomProof]

    -- Get the Nat.mul_left_inj iff lemma: ?b * combinedDenominators = ?c * combinedDenominators ↔ ?b = ?c
    -- Constructing @Nat.mul_left_inj combinedDenominators lhsExpr rhsExpr h_ne_zero_proof
    -- The order of implicit arguments {a b c : Nat} is {combinedDenominators, lhsExpr, rhsExpr}
    let mulLeftInjLemma ← mkAppOptM ``Nat.mul_left_inj #[combinedDenominators, lhsExpr, rhsExpr, h_ne_zero_proof]

    -- We want to change the goal from `lhsExpr = rhsExpr` to `lhsExpr * combinedDenominators = rhsExpr * combinedDenominators`.
    -- The `mulLeftInjLemma` is `(lhsExpr * combinedDen. = rhsExpr * combinedDen.) ↔ (lhsExpr = rhsExpr)`.
    -- `Iff.mp mulLeftInjLemma` gives `(lhsExpr * combinedDen. = rhsExpr * denCombinedDeno.) → (lhsExpr = rhsExpr)`.
    -- Applying this to the current goal `lhsExpr = rhsExpr` changes the goal to `lhsExpr * den = rhsExpr * den`.
    let goalTransformer ← mkAppM ``Iff.mp #[mulLeftInjLemma]

    let goalAfterMultiplyingDeno ← (← getMainGoal).apply goalTransformer
    if goalAfterMultiplyingDeno.isEmpty then
      throwError "[choose_eq] Applying equivalence transformation yielded no goals."
    replaceMainGoal [goalAfterMultiplyingDeno[0]!]

    let lhsExtended ← mkAppM ``HMul.hMul #[lhsExpr, combinedDenominators]
    let rhsExtended ← mkAppM ``HMul.hMul #[rhsExpr, combinedDenominators]
    let lhsGrouped ← mkAppM ``HMul.hMul #[lhsData.curTerm, rhsData.denFactorialProd]
    let rhsGrouped ← mkAppM ``HMul.hMul #[rhsData.curTerm, lhsData.denFactorialProd]
    let lhsContracted ← mkAppM ``HMul.hMul #[lhsData.newTerm, rhsData.denFactorialProd]
    let rhsContracted ← mkAppM ``HMul.hMul #[rhsData.newTerm, lhsData.denFactorialProd]

    let lhsGroupedType ← mkAppM ``Eq #[lhsExtended, lhsGrouped]
    let rhsGroupedType ← mkAppM ``Eq #[rhsExtended, rhsGrouped]
    let lhsContractedType ← mkAppM ``Eq #[lhsGrouped, lhsContracted]
    let rhsContractedType ← mkAppM ``Eq #[rhsGrouped, rhsContracted]

    let lhsGroupedMVar ← mkFreshExprMVar lhsGroupedType .syntheticOpaque (userName := `h_lhs_grouped_eq)
    let tacticStxLhsGrouped ← `(tactic| ring_nf)
    let remainingGoalLhsGroupedMVar ← Tactic.run lhsGroupedMVar.mvarId! (evalTactic tacticStxLhsGrouped)
    if !remainingGoalLhsGroupedMVar.isEmpty then
      throwError m!"[choose_eq] Failed to prove the equality for the grouping of factors on the LHS:
          {← ppExpr lhsGroupedType}
      Proof attempt:
          {← ppExpr lhsGroupedMVar}"

    let (_, goalAfterAddingLhsGrouped) ← assertHyp (← getMainGoal) lhsGroupedType lhsGroupedMVar `h_lhs_grouped_eq
    replaceMainGoal [goalAfterAddingLhsGrouped]
    evalTactic (← `(tactic|
      conv =>
        lhs
        rw [h_lhs_grouped_eq]))
    throwError m!"[choose_eq] Current goal state:\n{← Meta.ppGoal (← getMainGoal)}"

    let rhsGroupedMVar ← mkFreshExprMVar rhsGroupedType (userName := `h_rhs_grouped_eq)
    let tacticStxRhsGrouped ← `(tactic| ring_nf)
    let remainingGoalRhsGroupedMVar ← Tactic.run rhsGroupedMVar.mvarId! (evalTactic tacticStxRhsGrouped)
    if !remainingGoalRhsGroupedMVar.isEmpty then
      throwError m!"choose_eq:
      Failed to prove the equality for the grouping of factors on the RHS:
      {← ppExpr rhsGroupedType}
      Proof attempt:
      {← ppExpr rhsGroupedMVar}"
    let rhsGroupedProof ← instantiateMVars rhsGroupedMVar

    let lemmaListForChoose :=
      (lhsData.chooseArgsProofs ++ rhsData.chooseArgsProofs).map (fun (n, k, h_le_proof) =>
        mkApp3 (mkConst ``Nat.choose_mul_factorial_mul_factorial) n k h_le_proof)

    throwError m!"choose_eq:
      lemmaListForChoose[0](type):
            {← ppExpr (← inferType lemmaListForChoose[0]!)}

      lemmaListForChoose[0](proof):
            {← ppExpr lemmaListForChoose[0]!}

      lhsGroupedType:
          {← ppExpr lhsGroupedType},

      rhsGroupedType:
          {← ppExpr rhsGroupedType},

      lhsContractedType:
          {← ppExpr lhsContractedType},

      rhsContractedType:
          {← ppExpr rhsContractedType}"

    let lhsContractedMVar ← mkFreshExprMVar lhsContractedType (userName := `h_lhs_contracted_eq)
    let tacticStxLhsContracted ← `(tactic| simp only [Nat.choose_mul_factorial_mul_factorial])
    let remainingGoalLhsContractedMVar ← Tactic.run lhsContractedMVar.mvarId! (evalTactic tacticStxLhsContracted)
    if !remainingGoalLhsContractedMVar.isEmpty then
      throwError m!"choose_eq:
      Failed to prove the equality for the contraction of factors on the LHS:
      {← ppExpr lhsContractedType}
      Proof attempt:
      {← ppExpr lhsContractedMVar}"
    let lhsContractedProof ← instantiateMVars lhsContractedMVar

    let rhsContractedMVar ← mkFreshExprMVar rhsContractedType (userName := `h_rhs_contracted_eq)
    let tacticStxRhsContracted ← `(tactic| simp only [Nat.choose_mul_factorial_mul_factorial])
    let remainingGoalRhsContractedMVar ← Tactic.run rhsContractedMVar.mvarId! (evalTactic tacticStxRhsContracted)
    if !remainingGoalRhsContractedMVar.isEmpty then
      throwError m!"choose_eq:
      Failed to prove the equality for the contraction of factors on the RHS:
      {← ppExpr rhsContractedType}
      Proof attempt:
      {← ppExpr rhsContractedMVar}"
    let rhsContractedProof ← instantiateMVars rhsContractedMVar



    let mainGoal ← getMainGoal
    let mainGoalType ← mainGoal.getType
    throwError
    "choose_eq: main goal:
      {← ppExpr mainGoalType}"

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

end ChooseEqTactic

open ChooseEqTactic

-- Example usage and tests

example : Nat.mul 1 1 > 0 := by simp only [Nat.mul_eq, mul_one, gt_iff_lt, zero_lt_one]

example : Nat.choose 5 2 * Nat.choose 3 1 = Nat.choose 5 1 * Nat.choose 4 2 := by
  choose_eq
  sorry

example : Nat.choose 5 2 = Nat.choose 5 2 := by
  choose_eq
  sorry

example : Nat.choose 4 2 = (Nat.factorial 4) / (Nat.factorial 2 * Nat.factorial 2) := by
  choose_eq
  sorry

example (n k j : Nat) (h1 : j ≤ k) (h2 : k ≤ n) :
    n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) := by
  choose_eq
  sorry

example (n k : Nat) : k * n.choose k = n * (n - 1).choose (k - 1) := by
  choose_eq
  sorry

example : 0 <
  Mul.mul
    (Mul.mul (Mul.mul (Nat.factorial 2) (Nat.sub 5 2).factorial) (Mul.mul (Nat.factorial 1) (Nat.sub 3 1).factorial))
    (Mul.mul (Mul.mul (Nat.factorial 3) (Nat.sub 5 3).factorial) (Mul.mul (Nat.factorial 0) (Nat.sub 2 0).factorial))
  := by
    repeat (first | apply mul_pos | simp only [Nat.factorial_pos, Nat.succ_pos])

example (h₁ : 2 ≤ 5) (h₂ : 1 ≤ 3) (h₃ : 3 ≤ 5) (h₄ : 0 ≤ 2) :
    (Nat.choose 5 2)
      * (Nat.choose 3 1)
      * (Nat.factorial 2)
      * (Nat.sub 5 2).factorial
      * (Nat.factorial 1)
      * (Nat.sub 3 1).factorial
      * (Nat.factorial 3)
      * (Nat.sub 5 3).factorial
      * (Nat.factorial 0)
      * (Nat.sub 2 0).factorial
    =
    ((Nat.choose 5 2)
      * (Nat.factorial 2)
      * (Nat.sub 5 2).factorial)
    *
    ((Nat.choose 3 1)
      * (Nat.factorial 1)
      * (Nat.sub 3 1).factorial)
    *
    ((Nat.factorial 3)
      * (Nat.sub 5 3).factorial
      * (Nat.factorial 0)
      * (Nat.sub 2 0).factorial)
  := by
  ring

example (h₁ : 2 ≤ 5) (h₂ : 1 ≤ 3) (h₃ : 3 ≤ 5) (h₄ : 0 ≤ 2) :
    (Nat.choose 5 3)
      * (Nat.choose 2 0)
      * (Nat.factorial 2)
      * (Nat.sub 5 2).factorial
      * (Nat.factorial 1)
      * (Nat.sub 3 1).factorial
      * (Nat.factorial 3)
      * (Nat.sub 5 3).factorial
      * (Nat.factorial 0)
      * (Nat.sub 2 0).factorial
    =
    ((Nat.choose 5 3)
      * (Nat.factorial 3)
      * (Nat.sub 5 3).factorial)
    *
    ((Nat.choose 2 0)
      * (Nat.factorial 0)
      * (Nat.sub 2 0).factorial)
    *
    ((Nat.factorial 2)
      * (Nat.sub 5 2).factorial
      * (Nat.factorial 1)
      * (Nat.sub 3 1).factorial)
  := by
  ring


example (a b c d : ℕ) (h : a ≤ b) :
  (Nat.choose b a) * ((c * d) * ((Nat.factorial a) * (b - a).factorial))
  =
  (Nat.factorial b) * (c * d)
  := by
  ring_nf
  simp only [Nat.mul_comm, Nat.mul_assoc, Nat.choose_mul_factorial_mul_factorial h]
  ring_nf


example :
Nat.choose 5 2 * Nat.choose 3 1 *
    ((Nat.factorial 2 * (Nat.sub 5 2).factorial * (Nat.factorial 1 * (Nat.sub 3 1).factorial))
    * (Nat.factorial 3 * (Nat.sub 5 3).factorial * (Nat.factorial 0 * (Nat.sub 2 0).factorial))) =
  Nat.choose 5 2 * Nat.factorial 2 * (Nat.sub 5 2).factorial *
      (Nat.choose 3 1 * Nat.factorial 1 * (Nat.sub 3 1).factorial) *
    (Nat.factorial 3 * (Nat.sub 5 3).factorial * (Nat.factorial 0 * (Nat.sub 2 0).factorial))
  := by
  ring_nf

example   (h₁ : 2 ≤ 5) (h₂ : 1 ≤ 3) (h₃ : 3 ≤ 5) (h₄ : 0 ≤ 2) :
    Nat.choose 5 2 * Nat.factorial 2 * (Nat.sub 5 2).factorial *
      (Nat.choose 3 1 * Nat.factorial 1 * (Nat.sub 3 1).factorial) *
      (Nat.factorial 3 * (Nat.sub 5 3).factorial * (Nat.factorial 0 * (Nat.sub 2 0).factorial)) =
    Nat.factorial 5 * Nat.factorial 3 *
      (Nat.factorial 3 * (Nat.sub 5 3).factorial * (Nat.factorial 0 * (Nat.sub 2 0).factorial))
  := by
  simp only
    [Nat.choose_mul_factorial_mul_factorial h₁, Nat.choose_mul_factorial_mul_factorial h₂,
    Nat.choose_mul_factorial_mul_factorial h₃, Nat.choose_mul_factorial_mul_factorial h₄]
