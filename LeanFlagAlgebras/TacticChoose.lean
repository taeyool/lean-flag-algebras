import Lean
import Init.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Nat -- For ac_refl (CommSemiring for Nat)

open Lean Elab Tactic Meta

namespace ChooseEqTactic

set_option pp.explicit true

-- Data structure to hold information about one side of the equality
structure SideData where
  chooseArgsProofs : List (Expr × Expr × Expr) -- List of (n_expr, k_expr, h_le_proof)
  termProduct : Expr                           -- Product of all terms (N!, other_factors)
  denFactorialProd : Expr                      -- Product of (K! * (N-K)!) terms for this side's chooses

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
    let den_fact_part ← mkAppM ``Mul.mul #[k_fact, nk_fact]

    return {
      chooseArgsProofs := [(n, k, h_le_mvar)],
      termProduct := n_fact,
      denFactorialProd := den_fact_part
    }

  | Expr.app (Expr.app e0 e1) e2 =>
    match e0 with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``HMul.hMul _) _) _) _) _ =>
        let data1 ← processSideExpr e1
        let data2 ← processSideExpr e2
        let new_term_prod ← mkAppM ``Mul.mul #[data1.termProduct, data2.termProduct]
        let new_den_prod ← mkAppM ``Mul.mul #[data1.denFactorialProd, data2.denFactorialProd]
        return {
          chooseArgsProofs := data1.chooseArgsProofs ++ data2.chooseArgsProofs,
          termProduct := new_term_prod,
          denFactorialProd := new_den_prod
        }
    | _ =>
        return {
          chooseArgsProofs := [],
          termProduct := e, -- This term itself
          denFactorialProd := oneLit -- No denominators from this term
        }

  | _ => -- Not a choose or a multiplication, treat as an "other factor"
    -- This allows expressions like `A * n.choose k = B * m.choose j`
    -- where A and B are arbitrary expressions.
    -- `ac_refl` will succeed if A and B are syntactically identical
    -- and the factorial parts match.
    return {
      chooseArgsProofs := [],
      termProduct := e, -- This term itself
      denFactorialProd := oneLit -- No denominators from this term
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

    guard goalType.isEq <|> throwError "Goal is not an equality"
    let lhsExpr := goalType.appFn!.appArg!
    let rhsExpr := goalType.appArg!

    -- Step 1: Process both sides to extract choose terms, prove k <= n,
    -- and prepare products of numerators (N!) and denominators (K!(N-K)!).
    let lhsData ← processSideExpr lhsExpr
    let rhsData ← processSideExpr rhsExpr

    /-
    throwError m!"choose_eq:
      lhsExpr = {← ppExpr lhsExpr},
      rhsExpr = {← ppExpr rhsExpr},
      lhsData.termProduct = {← ppExpr lhsData.termProduct},
      rhsData.termProduct = {← ppExpr rhsData.termProduct},
      lhsData.denFactorialProd = {← ppExpr lhsData.denFactorialProd},
      rhsData.denFactorialProd = {← ppExpr rhsData.denFactorialProd},"
    -/

    -- Step 2: Justify the transformation to the factorial form.
    -- Goal: LHS = RHS
    -- We want to show this is equivalent to:
    --   lhsData.termProduct * rhsData.denFactorialProd = rhsData.termProduct * lhsData.denFactorialProd
    -- This is done by multiplying the original equality by (lhsData.denFactorialProd * rhsData.denFactorialProd),
    -- then rewriting terms like `C(n,k) * k! * (n-k)!` to `n!`.

    -- Prove that the combined product of all denominators is positive.
    let combinedDenominators ← mkAppM ``Mul.mul #[lhsData.denFactorialProd, rhsData.denFactorialProd]
    let combinedDenominatorsPositiveType ← mkAppM ``LT.lt #[mkNatLit 0, combinedDenominators]
    let positiveDenomMVar ← mkFreshExprMVar combinedDenominatorsPositiveType (userName := `h_den_pos)

    let tacticStxDenPos ← `(tactic| repeat (first | apply mul_pos | simp only [Nat.factorial_pos, Nat.succ_pos]))

    let remainingGoalsDenPos ← Tactic.run positiveDenomMVar.mvarId! (evalTactic tacticStxDenPos)
    let positiveDenomProof ← instantiateMVars positiveDenomMVar

    if !remainingGoalsDenPos.isEmpty then
      throwError m!"choose_eq:
      Failed to prove the positivity of the product of all denominators:
      {← ppExpr combinedDenominators}
      Proof attempt:
      {← ppExpr positiveDenomMVar}"

    -- Apply Nat.mul_left_inj to change the goal to:
    --   lhsExpr * combinedDenominators = rhsExpr * combinedDenominators
    -- Derive combinedDenominators ≠ 0 from 0 < combinedDenominators
    let posIffNeZeroTheorem ← mkAppOptM ``Nat.pos_iff_ne_zero #[combinedDenominators]
    let h_ne_zero_proof ← mkAppM ``Iff.mp #[posIffNeZeroTheorem, positiveDenomProof]

    -- Get the Nat.mul_left_inj iff lemma: ?b * combinedDenominators = ?c * combinedDenominators ↔ ?b = ?c
    -- Implicit arguments ?b (lhsExpr) and ?c (rhsExpr) will be filled by unification when applying to the goal.
    -- Constructing @Nat.mul_left_inj combinedDenominators lhsExpr rhsExpr h_ne_zero_proof
    -- The order of implicit arguments {a b c : Nat} is {combinedDenominators, lhsExpr, rhsExpr}
    let mulLeftInjLemma ← mkAppOptM ``Nat.mul_left_inj #[combinedDenominators, lhsExpr, rhsExpr, h_ne_zero_proof]

    -- We want to change the goal from `lhsExpr = rhsExpr` to `lhsExpr * combinedDenominators = rhsExpr * combinedDenominators`.
    -- The `mulLeftInjLemma` is `(lhs * den = rhs * den) ↔ (lhs = rhs)`.
    -- `Iff.mp mulLeftInjLemma` gives `(lhs * den = rhs * den) → (lhs = rhs)`.
    -- Applying this to the current goal `lhs = rhs` changes the goal to `lhs * den = rhs * den`.
    let goalTransformer ← mkAppM ``Iff.mp #[mulLeftInjLemma]
    let goalAfterMulInj ← mainGoal.apply goalTransformer

    -- Assert all k <= n proofs into the context for `simp` to use.
    if goalAfterMulInj.isEmpty then
      throwError "choose_eq: Applying equivalence transformation yielded no goals."
    let mut currentGoalId := goalAfterMulInj[0]! -- Use the first goal from the list
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

example : Nat.choose 5 2 * Nat.choose 3 1 = Nat.choose 5 3 * Nat.choose 2 0 := by
  choose_eq

example : Nat.choose 5 2 = Nat.choose 5 2 := by
  choose_eq

example : Nat.choose 4 2 = (Nat.factorial 4) / (Nat.factorial 2 * Nat.factorial 2) := by
  choose_eq

example (n k j : Nat) (h1 : j ≤ k) (h2 : k ≤ n) :
    n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) := by
  choose_eq

example (n k : Nat) : k * n.choose k = n * (n - 1).choose (k - 1) := by
  choose_eq

set_option pp.explicit true in
#check (Nat.choose 5 3 * Nat.choose 2 0)

example : 0 <
  Mul.mul
    (Mul.mul (Mul.mul (Nat.factorial 2) (Nat.sub 5 2).factorial) (Mul.mul (Nat.factorial 1) (Nat.sub 3 1).factorial))
    (Mul.mul (Mul.mul (Nat.factorial 3) (Nat.sub 5 3).factorial) (Mul.mul (Nat.factorial 0) (Nat.sub 2 0).factorial))
  := by
    repeat (first | apply mul_pos | simp only [Nat.factorial_pos, Nat.succ_pos])

example (h₁ : 2 ≤ 5) (h₂ : 1 ≤ 3) (h₃ : 3 ≤ 5) (h₄ : 0 ≤ 2):
    Mul.mul
      (Mul.mul (Nat.choose 5 2) (Nat.choose 3 1))
      (Mul.mul
        (Mul.mul (Mul.mul (Nat.factorial 2) (Nat.sub 5 2).factorial) (Mul.mul (Nat.factorial 1) (Nat.sub 3 1).factorial))
        (Mul.mul (Mul.mul (Nat.factorial 3) (Nat.sub 5 3).factorial)
          (Mul.mul (Nat.factorial 0) (Nat.sub 2 0).factorial))) =
    Mul.mul
      (Mul.mul
        (Nat.choose 5 3) (Nat.choose 2 0))
      (Mul.mul
       (Mul.mul (Mul.mul (Nat.factorial 2) (Nat.sub 5 2).factorial) (Mul.mul (Nat.factorial 1) (Nat.sub 3 1).factorial))
        (Mul.mul (Mul.mul (Nat.factorial 3) (Nat.sub 5 3).factorial) (Mul.mul (Nat.factorial 0) (Nat.sub 2 0).factorial)))
  := by
    conv =>
      lhs
      simp [Nat.choose_mul_factorial_mul_factorial, Nat.mul_assoc, Nat.mul_comm]
      simp [Nat.mul_one, Nat.one_mul]
      simp [Nat.choose_mul_factorial_mul_factorial, Nat.mul_assoc, Nat.mul_comm]
    conv =>
      rhs
      simp [Nat.choose_mul_factorial_mul_factorial, Nat.mul_assoc, Nat.mul_comm]
      simp [Nat.mul_one, Nat.one_mul]
      simp [Nat.choose_mul_factorial_mul_factorial, Nat.mul_assoc, Nat.mul_comm]
    sorry
