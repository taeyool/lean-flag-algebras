import LeanFlagAlgebras.ErdosPentagon.FlagMul
import LeanFlagAlgebras.Forbid.Basic
import Mathlib.Tactic

open FlagAlgebras Forbid
open Lean Elab Tactic Meta

namespace ErdosPentagon

private def lastNamePart (nm : Name) : String :=
  match nm with
  | .anonymous => ""
  | .str _ s => s
  | .num _ n => toString n

private partial def findFlagAlgebraConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
  if (lastNamePart nm).startsWith "FlagAlgebra_" then some nm else none
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

private partial def findFlagConst? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
  if (lastNamePart nm).startsWith "Flag_" then some nm else none
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

private def getBinAppArgs? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app (.app _ a) b => some (a, b)
  | _ => none

private def unwrapQuotMk (e : Expr) : Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Quot.mk && args.size = 3 then args[2]! else e

private def getAddArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``Add.add) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    getBinAppArgs? e

private def getSmulArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HSMul.hSMul || fn.isConstOf ``SMul.smul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    match e with
    | .app f x => some (f, x)
    | _ => none

private def getMulArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HMul.hMul || fn.isConstOf ``Mul.mul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    getBinAppArgs? e

private def flagToFlagAlgebraLastPart (s : String) : String :=
  if s.startsWith "Flag_" then
    "FlagAlgebra_" ++ s.drop 5
  else
    s

private def mkFlagMulThmName? (mulTerm : Expr) : MetaM (Option Name) := do
  let some (fExpr, gExpr) := getMulArgs? mulTerm | return none
  let fNm? := findFlagAlgebraConst? fExpr
  let gNm? := findFlagAlgebraConst? gExpr
  let fFlag? := findFlagConst? fExpr
  let gFlag? := findFlagConst? gExpr
  let some fNm := fNm?.orElse (fun _ => fFlag?) | return none
  let some gNm := gNm?.orElse (fun _ => gFlag?) | return none
  let env ← getEnv
  let fLast := if fNm?.isSome then lastNamePart fNm else flagToFlagAlgebraLastPart (lastNamePart fNm)
  let gLast := if gNm?.isSome then lastNamePart gNm else flagToFlagAlgebraLastPart (lastNamePart gNm)
  let thmStrFG := s!"flagMul_{fLast}_{gLast}"
  let thmStrGF := s!"flagMul_{gLast}_{fLast}"
  let epNs := Name.mkSimple "ErdosPentagon"
  let cands := [
    Name.str fNm.getPrefix thmStrFG,
    Name.str fNm.getPrefix thmStrGF,
    Name.str epNs thmStrFG,
    Name.str epNs thmStrGF,
    Name.mkSimple thmStrFG,
    Name.mkSimple thmStrGF
  ]
  for cand in cands do
    if env.constants.contains cand then
      return some cand
  return none

private def stepReduceFlagMul : TacticM Bool :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let args := target.getAppArgs
    if args.size < 2 then
      return false
    let lhsRaw := args[args.size - 2]!
    let lhs := unwrapQuotMk ((← whnf lhsRaw).consumeMData)
    if let some (head, _rest) := getAddArgs? lhs then
      if let some (_c, mulTerm) := getSmulArgs? head then
        let some thmName ← mkFlagMulThmName? mulTerm
          | do
              let fNm? := findFlagAlgebraConst? mulTerm |>.orElse (fun _ => findFlagConst? mulTerm)
              throwError m!"auto_reduce_ep_flagmul: could not find flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
        let thmId : TSyntax `term := mkIdent thmName
        evalTactic (← `(tactic|
          rw [forbidEq_rw_left_add_right (forbidEq_smul (c := _) $thmId),
              forbidEq_move_add_left_iff]))
        return true
      return false
    else if let some (_c, mulTerm) := getSmulArgs? lhs then
      let some thmName ← mkFlagMulThmName? mulTerm
        | do
            let fNm? := findFlagAlgebraConst? mulTerm |>.orElse (fun _ => findFlagConst? mulTerm)
            throwError m!"auto_reduce_ep_flagmul: could not find terminal flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
      let thmId : TSyntax `term := mkIdent thmName
      evalTactic (← `(tactic|
        rw [forbidEq_rw_left (forbidEq_smul (c := _) $thmId),
            forbidEq_move_term_left_iff]))
      return true
    else
      return false

private partial def runReduceFlagMul (fuel : Nat := 256) (steps : Nat := 0) : TacticM Unit := do
  if fuel = 0 then
    throwError "auto_reduce_ep_flagmul: fuel exhausted"
  let progressed ← stepReduceFlagMul
  if progressed then
    runReduceFlagMul (fuel - 1) (steps + 1)
  else
    if steps = 0 then
      withMainContext do
        let goal ← getMainGoal
        let target ← goal.getType
        let args := target.getAppArgs
        if args.size < 2 then
          throwError m!"auto_reduce_ep_flagmul: target has too few args: {target}"
        let lhs0 := (← whnf args[args.size - 2]!).consumeMData
        let lhs := unwrapQuotMk lhs0
        let add? := getAddArgs? lhs
        let smulOnLhs? := getSmulArgs? lhs
        let smulOnHead? := match add? with | some (h, _) => getSmulArgs? h | none => none
        let mulOnHead? := match smulOnHead? with | some (_, m) => getMulArgs? m | none => none
        throwError m!"auto_reduce_ep_flagmul failed. lhs0={lhs0}; lhs={lhs}; addDetected={(add?.isSome)}; smulLhsDetected={(smulOnLhs?.isSome)}; smulHeadDetected={(smulOnHead?.isSome)}; mulHeadDetected={(mulOnHead?.isSome)}"
    else
      pure ()

elab "reduce_flagmul" : tactic =>
  runReduceFlagMul

lemma flagQuadraticForm_R_v₂_forbidEq
    : flagQuadraticForm R_real v₂ =[K3]
        (1512 / 625 : ℝ) • FlagAlgebra_5_3_2_0
        - (380 / 625 : ℝ) • FlagAlgebra_5_3_2_1
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_2
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_3
        + (1512 / 625 : ℝ) • FlagAlgebra_5_3_2_4
        + (192 / 625 : ℝ) • FlagAlgebra_5_3_2_5
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_8
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_9
        - (380 / 625 : ℝ) • FlagAlgebra_5_3_2_10
        + (475 / 625 : ℝ) • FlagAlgebra_5_3_2_11
        + (475 / 625 : ℝ) • FlagAlgebra_5_3_2_12
        - (376 / 625 : ℝ) • FlagAlgebra_5_3_2_13
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_15
        + (568 / 625 : ℝ) • FlagAlgebra_5_3_2_16
        - (2 / 625 : ℝ) • FlagAlgebra_5_3_2_29
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_30
        - (191 / 625 : ℝ) • FlagAlgebra_5_3_2_31
        - (93 / 625 : ℝ) • FlagAlgebra_5_3_2_32
        - (93 / 625 : ℝ) • FlagAlgebra_5_3_2_33
        - (376 / 625 : ℝ) • FlagAlgebra_5_3_2_34
        - (2 / 625 : ℝ) • FlagAlgebra_5_3_2_53
        + (190 / 625 : ℝ) • FlagAlgebra_5_3_2_54
  := by
  simp [flagQuadraticForm, v₂, R_real, ratMatrixToReal, R, Fin.sum_univ_five, add_assoc]
  reduce_flagmul
  apply Forbid.forbidEq_of_eq
  norm_num
  ring_nf
  simp [add_assoc]
  have : (2 : FlagAlgebra FlagType_3_2) = ((2 : ℝ) • (1 : FlagAlgebra FlagType_3_2)) := by
    rw [two_smul]
    norm_num
  repeat rw [this]
  repeat rw [mul_smul_comm]
  simp [smul_smul]
  ring_nf

example
    : flagQuadraticForm R_real v₂ ≥ 0
  :=
  flagQuadraticForm_nonneg R_real R_real_posSemidef v₂

theorem ErdosPentagon
    : C5 ≤[K3] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  sorry

end ErdosPentagon
