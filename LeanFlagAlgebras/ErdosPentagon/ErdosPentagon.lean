import LeanFlagAlgebras.ErdosPentagon.FlagMul
import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.ErdosPentagon.Playground
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

private def getSmulArgsStrict? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HSMul.hSMul || fn.isConstOf ``SMul.smul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]! )
  else
    none
private def getMulArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HMul.hMul || fn.isConstOf ``Mul.mul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    getBinAppArgs? e

private def getSubArgs? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HSub.hSub || fn.isConstOf ``Sub.sub) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

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

/-- Linear term represented as `(base, coeff)` meaning `coeff • base`. -/
abbrev LinTerm := Expr × Expr

private partial def flattenLinearTerms (oneCoeff : Expr) (e : Expr) : MetaM (Array LinTerm) := do
  let e := e.consumeMData
  if let some (a, b) := getAddArgs? e then
    return (← flattenLinearTerms oneCoeff a) ++ (← flattenLinearTerms oneCoeff b)
  if let some (a, b) := getSubArgs? e then
    let left ← flattenLinearTerms oneCoeff a
    let right ← flattenLinearTerms oneCoeff b
    let rightNeg ← right.mapM fun (base, coeff) => do
      let negCoeff ← mkAppM ``Neg.neg #[coeff]
      pure (base, negCoeff)
    return left ++ rightNeg
  if let some (coeff, base) := getSmulArgsStrict? e then
    return #[(base, coeff)]
  -- Fallback: treat bare term as `1 • term`
  return #[(e, oneCoeff)]

private def findBaseIndex (acc : Array LinTerm) (base : Expr) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i < acc.size then
      let (b, _) := acc[i]
      if b == base then some i else go (i + 1)
    else
      none
  go 0

private def groupLinearTerms (terms : Array LinTerm) : MetaM (Array LinTerm) := do
  let mut acc : Array LinTerm := #[]
  for (base, coeff) in terms do
    match findBaseIndex acc base with
    | some i =>
        let (_, oldCoeff) := acc[i]!
        let newCoeff ← mkAppM ``HAdd.hAdd #[oldCoeff, coeff]
        acc := acc.set! i (base, newCoeff)
    | none =>
        acc := acc.push (base, coeff)
  pure acc

private def sortLinearTermsByBase (terms : Array LinTerm) : MetaM (Array LinTerm) := do
  let keyed ← terms.mapM fun (base, coeff) => do
    let kb ← ppExpr base
    pure (kb.pretty, base, coeff)
  let mut sorted : Array (String × Expr × Expr) := #[]
  for item in keyed do
    let mut inserted := false
    let mut next : Array (String × Expr × Expr) := #[]
    for old in sorted do
      if !inserted && item.1 < old.1 then
        next := next.push item
        inserted := true
      next := next.push old
    if !inserted then
      next := next.push item
    sorted := next
  pure <| (sorted.map fun (_, base, coeff) => (base, coeff))

private def rebuildLinearExpr (terms : Array LinTerm) : MetaM Expr := do
  let smulTerms ← terms.mapM fun (base, coeff) => mkAppM ``HSMul.hSMul #[coeff, base]
  match smulTerms.toList with
  | [] => throwError "rebuildLinearExpr: empty term list"
  | t :: ts => ts.foldlM (fun acc nxt => mkAppM ``HAdd.hAdd #[acc, nxt]) t

private def normalizeLinearExpr (oneCoeff : Expr) (e : Expr) : MetaM Expr := do
  let flat ← flattenLinearTerms oneCoeff e
  let grouped ← groupLinearTerms flat
  let sorted ← sortLinearTermsByBase grouped
  rebuildLinearExpr sorted

elab "preview_flagalgebra_linear_normal_form" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let args := target.getAppArgs
    if args.size < 2 then
      throwError "preview_flagalgebra_linear_normal_form: target is not binary relation"
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    let oneCoeff ← Lean.Elab.Term.elabTerm (← `(term| (1 : ℝ))) none
    let lhsNorm ← normalizeLinearExpr oneCoeff lhs
    let rhsNorm ← normalizeLinearExpr oneCoeff rhs
    logInfo m!"[linear-normalize] LHS normalized: {lhsNorm}"
    logInfo m!"[linear-normalize] RHS normalized: {rhsNorm}"

elab "normalize_flagalgebra_linear" : tactic =>
  do
    evalTactic (← `(tactic|
      repeat'
        (first
          | conv_lhs => simp [sub_eq_add_neg, ← neg_smul]
          | conv_rhs => simp [sub_eq_add_neg, ← neg_smul]
          | conv_lhs => rw [← add_assoc]
          | conv_rhs => rw [← add_assoc]
          | conv_lhs => rw [collect_smul_same_deep_right]
          | conv_rhs => rw [collect_smul_same_deep_right]
          | conv_lhs => rw [collect_smul_same_mid_left]
          | conv_rhs => rw [collect_smul_same_mid_left]
          | conv_lhs => rw [collect_smul_same_mid]
          | conv_rhs => rw [collect_smul_same_mid]
          | conv_lhs => rw [collect_smul_same_head]
          | conv_rhs => rw [collect_smul_same_head]
          | conv_lhs => rw [collect_smul_same]
          | conv_rhs => rw [collect_smul_same])))

set_option maxHeartbeats 0

noncomputable def flagQuadraticForm_P_v₀_expand
  :=
  (24 / 625 : ℝ) • FlagAlgebra_5_3_0_0
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_1
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_2
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_3
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_4
  + (277 / 625 : ℝ) • FlagAlgebra_5_3_0_5
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_6
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_7
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_8
  + (277 / 625 : ℝ) • FlagAlgebra_5_3_0_9
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_10
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_11
  + (277 / 625 : ℝ) • FlagAlgebra_5_3_0_12
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_13
  + (97 / 625 : ℝ) • FlagAlgebra_5_3_0_14
  + (97 / 625 : ℝ) • FlagAlgebra_5_3_0_15
  + (97 / 625 : ℝ) • FlagAlgebra_5_3_0_16
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_17
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_18
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_19
  + (24 / 625 : ℝ) • FlagAlgebra_5_3_0_20
  - (79 / 625 : ℝ) • FlagAlgebra_5_3_0_24
  - (79 / 625 : ℝ) • FlagAlgebra_5_3_0_25
  - (79 / 625 : ℝ) • FlagAlgebra_5_3_0_26
  + (97 / 625 : ℝ) • FlagAlgebra_5_3_0_27
  - (79 / 625 : ℝ) • FlagAlgebra_5_3_0_28
  + (97 / 625 : ℝ) • FlagAlgebra_5_3_0_29
  - (79 / 625 : ℝ) • FlagAlgebra_5_3_0_30
  - (79 / 625 : ℝ) • FlagAlgebra_5_3_0_31
  + (97 / 625 : ℝ) • FlagAlgebra_5_3_0_32
  - (259 / 625 : ℝ) • FlagAlgebra_5_3_0_33
  - (259 / 625 : ℝ) • FlagAlgebra_5_3_0_34
  - (259 / 625 : ℝ) • FlagAlgebra_5_3_0_35
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_36
  + (54 / 625 : ℝ) • FlagAlgebra_5_3_0_43
  + (54 / 625 : ℝ) • FlagAlgebra_5_3_0_44
  + (54 / 625 : ℝ) • FlagAlgebra_5_3_0_45
  - (259 / 625 : ℝ) • FlagAlgebra_5_3_0_46
  - (259 / 625 : ℝ) • FlagAlgebra_5_3_0_47
  - (259 / 625 : ℝ) • FlagAlgebra_5_3_0_48
  + (247 / 625 : ℝ) • FlagAlgebra_5_3_0_49
  + (247 / 625 : ℝ) • FlagAlgebra_5_3_0_50
  + (247 / 625 : ℝ) • FlagAlgebra_5_3_0_51
  + (67 / 625 : ℝ) • FlagAlgebra_5_3_0_52
  + (67 / 625 : ℝ) • FlagAlgebra_5_3_0_53
  + (67 / 625 : ℝ) • FlagAlgebra_5_3_0_54
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_64
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_65
  - (36 / 625 : ℝ) • FlagAlgebra_5_3_0_66
  + (54 / 625 : ℝ) • FlagAlgebra_5_3_0_70

lemma flagQuadraticForm_P_v₀_forbidEq
    : flagQuadraticForm P_real v₀ =[K3.toFinFlag] flagQuadraticForm_P_v₀_expand
  := by
  dsimp [flagQuadraticForm_P_v₀_expand]
  simp [flagQuadraticForm, v₀, P_real, ratMatrixToReal, P, Fin.sum_univ_eight, add_assoc]
  reduce_flagmul
  apply Forbid.forbidEq_of_eq
  norm_num
  ring_nf
  simp [add_assoc]
  have : (2 : FlagAlgebra FlagType_3_0) = ((2 : ℝ) • (1 : FlagAlgebra FlagType_3_0)) := by
    rw [two_smul]
    norm_num
  repeat rw [this]
  repeat rw [mul_smul_comm]
  simp [smul_smul]
  ring_nf

noncomputable def flagQuadraticForm_Q_v₁_expand
  :=
  (432 / 625 : ℝ) • FlagAlgebra_5_3_1_0
  - (1551 / 2500 : ℝ) • FlagAlgebra_5_3_1_1
  - (1551 / 2500 : ℝ) • FlagAlgebra_5_3_1_2
  - (327 / 625 : ℝ) • FlagAlgebra_5_3_1_3
  + (432 / 625 : ℝ) • FlagAlgebra_5_3_1_4
  + (584 / 625 : ℝ) • FlagAlgebra_5_3_1_5
  + (584 / 625 : ℝ) • FlagAlgebra_5_3_1_6
  + (371 / 1250 : ℝ) • FlagAlgebra_5_3_1_8
  + (687 / 2500 : ℝ) • FlagAlgebra_5_3_1_9
  - (1551 / 2500 : ℝ) • FlagAlgebra_5_3_1_10
  + (687 / 2500 : ℝ) • FlagAlgebra_5_3_1_11
  - (1551 / 2500 : ℝ) • FlagAlgebra_5_3_1_12
  + (227 / 625 : ℝ) • FlagAlgebra_5_3_1_13
  + (227 / 625 : ℝ) • FlagAlgebra_5_3_1_14
  + (432 / 625 : ℝ) • FlagAlgebra_5_3_1_15
  - (327 / 625 : ℝ) • FlagAlgebra_5_3_1_16
  + (2557 / 2500 : ℝ) • FlagAlgebra_5_3_1_23
  + (687 / 2500 : ℝ) • FlagAlgebra_5_3_1_24
  + (2557 / 2500 : ℝ) • FlagAlgebra_5_3_1_25
  + (687 / 2500 : ℝ) • FlagAlgebra_5_3_1_26
  + (371 / 1250 : ℝ) • FlagAlgebra_5_3_1_29
  - (1021 / 625 : ℝ) • FlagAlgebra_5_3_1_30
  - (1021 / 625 : ℝ) • FlagAlgebra_5_3_1_31
  - (127 / 1250 : ℝ) • FlagAlgebra_5_3_1_32
  + (227 / 625 : ℝ) • FlagAlgebra_5_3_1_33
  - (127 / 1250 : ℝ) • FlagAlgebra_5_3_1_34
  + (227 / 625 : ℝ) • FlagAlgebra_5_3_1_35
  + (3816 / 625 : ℝ) • FlagAlgebra_5_3_1_50
  - (1021 / 625 : ℝ) • FlagAlgebra_5_3_1_51
  + (3816 / 625 : ℝ) • FlagAlgebra_5_3_1_52
  - (1021 / 625 : ℝ) • FlagAlgebra_5_3_1_53
  - (3606 / 625 : ℝ) • FlagAlgebra_5_3_1_54

lemma flagQuadraticForm_Q_v₁_forbidEq
    : flagQuadraticForm Q_real v₁ =[K3.toFinFlag] flagQuadraticForm_Q_v₁_expand
  := by
  dsimp [flagQuadraticForm_Q_v₁_expand]
  simp [flagQuadraticForm, v₁, Q_real, ratMatrixToReal, Q, Fin.sum_univ_six, add_assoc]
  reduce_flagmul
  apply Forbid.forbidEq_of_eq
  norm_num
  ring_nf
  simp [add_assoc]
  have : (2 : FlagAlgebra FlagType_3_1) = ((2 : ℝ) • (1 : FlagAlgebra FlagType_3_1)) := by
    rw [two_smul]
    norm_num
  repeat rw [this]
  repeat rw [mul_smul_comm]
  simp [smul_smul]
  ring_nf

noncomputable def flagQuadraticForm_R_v₂_expand
  :=
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

lemma flagQuadraticForm_R_v₂_forbidEq
    : flagQuadraticForm R_real v₂ =[K3.toFinFlag] flagQuadraticForm_R_v₂_expand
  := by
  dsimp [flagQuadraticForm_R_v₂_expand]
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

lemma flagQuadraticForm_P_v₀_expand_downward_forbidLE_nonneg
    : 0 ≤[K3.toFinFlag] ⟦flagQuadraticForm_P_v₀_expand⟧₀
  := by
  apply downward_forbidLE_nonneg
  apply forbidLE_trans_forbidEq_right _ flagQuadraticForm_P_v₀_forbidEq
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg P_real P_real_posSemidef v₀

lemma flagQuadraticForm_Q_v₁_expand_downward_forbidLE_nonneg
    : 0 ≤[K3.toFinFlag] ⟦flagQuadraticForm_Q_v₁_expand⟧₀
  := by
  apply downward_forbidLE_nonneg
  apply forbidLE_trans_forbidEq_right _ flagQuadraticForm_Q_v₁_forbidEq
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg Q_real Q_real_posSemidef v₁

lemma flagQuadraticForm_R_v₂_expand_downward_forbidLE_nonneg
    : 0 ≤[K3.toFinFlag] ⟦flagQuadraticForm_R_v₂_expand⟧₀
  := by
  apply downward_forbidLE_nonneg
  apply forbidLE_trans_forbidEq_right _ flagQuadraticForm_R_v₂_forbidEq
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg R_real R_real_posSemidef v₂

noncomputable def one_size_five_expand
  :=
  FlagAlgebra_5_0_0_0
  + FlagAlgebra_5_0_0_1
  + FlagAlgebra_5_0_0_2
  + FlagAlgebra_5_0_0_3
  + FlagAlgebra_5_0_0_4
  + FlagAlgebra_5_0_0_6
  + FlagAlgebra_5_0_0_7
  + FlagAlgebra_5_0_0_8
  + FlagAlgebra_5_0_0_10
  + FlagAlgebra_5_0_0_12
  + FlagAlgebra_5_0_0_13
  + FlagAlgebra_5_0_0_18
  + FlagAlgebra_5_0_0_19
  + FlagAlgebra_5_0_0_25

lemma one_forbidEq_one_size_five_expand
    : 1 =[K3.toFinFlag] one_size_five_expand
  := by
  have : (1 : FlagAlgebra ∅ₜ) = ⟦unitVector ⟨0, default⟩⟧ := rfl
  rw [this]
  have h := unitVector_quot_forbidEq_sum K3.toFinFlag (⟨0, default⟩ : FinFlag ∅ₜ) 5 (by simp)
  apply forbidEq_trans h
  simp [default, flagDensity_empty]
  rw [Finset.sum_eq_multiset_sum, ← flagSet_5_0_0_eq_univ]
  simp [flagSet_5_0_0_val_eq, unlabel_emptyType, ← add_assoc]
  apply forbidEq_of_eq
  rfl

theorem ErdosPentagon_flagAlgebra
    : C5.toFlagAlgebra ≤[K3.toFinFlag] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have h₁ : C5.toFlagAlgebra ≤[K3.toFinFlag]
            C5.toFlagAlgebra + ⟦flagQuadraticForm_P_v₀_expand⟧₀
                             + ⟦flagQuadraticForm_Q_v₁_expand⟧₀
                             + ⟦flagQuadraticForm_R_v₂_expand⟧₀
    := by
    have : C5.toFlagAlgebra = C5.toFlagAlgebra + 0 + 0 + 0 := by simp only [add_zero]
    nth_rw 1 [this]
    apply forbidLE_add _ flagQuadraticForm_R_v₂_expand_downward_forbidLE_nonneg
    apply forbidLE_add _ flagQuadraticForm_Q_v₁_expand_downward_forbidLE_nonneg
    apply forbidLE_add _ flagQuadraticForm_P_v₀_expand_downward_forbidLE_nonneg
    exact forbidLE_refl K3.toFinFlag C5.toFlagAlgebra
  have h₂ : (C5.toFlagAlgebra + ⟦flagQuadraticForm_P_v₀_expand⟧₀
                              + ⟦flagQuadraticForm_Q_v₁_expand⟧₀
                              + ⟦flagQuadraticForm_R_v₂_expand⟧₀)
            ≤ (24 / 625 : ℝ) • one_size_five_expand
    := by
    rw [C5_toFlagAlgebra_eq]
    dsimp [flagQuadraticForm_P_v₀_expand, flagQuadraticForm_Q_v₁_expand, flagQuadraticForm_R_v₂_expand, one_size_five_expand]
    simp [downward_add, downward_sub, downward_smul, smul_smul]
    norm_num

    conv =>
      arg 2; arg 2; arg 1; arg 1
      simp only [sub_eq_add_neg, ← neg_smul]
      collect_adjacent_flagsum
    conv =>
      arg 2; arg 2; arg 1; arg 2
      simp only [sub_eq_add_neg, ← neg_smul]
      collect_adjacent_flagsum
    conv =>
      arg 2; arg 2; arg 2
      simp only [sub_eq_add_neg, ← neg_smul]
      collect_adjacent_flagsum
    conv =>
      arg 2; arg 2; arg 1
      simp only [sub_eq_add_neg, ← neg_smul, add_assoc]
      sort_flagsum_by_swaps_at
      collect_adjacent_flagsum
    conv =>
      arg 2; arg 2
      simp only [sub_eq_add_neg, ← neg_smul, add_assoc]
      sort_flagsum_by_swaps_at
      collect_adjacent_flagsum
    conv =>
      arg 2
      ring_nf
      simp only [sub_eq_add_neg, ← neg_smul, add_assoc]
      sort_flagsum_by_swaps_at
      collect_adjacent_flagsum
      rw [← add_assoc, ← add_smul]
      norm_num

    simp only [add_zero]
    intro φ
    simp only [PositiveHom.map_add, ge_iff_le]
    apply add_nonneg <;> try apply add_nonneg
    all_goals
    simp only [PositiveHom.map_smul, Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_nonneg_iff_of_pos_left]
    apply positiveHom_unitVector_ge_zero

  have h₃ : ((24 / 625 : ℝ) • one_size_five_expand) =[K3.toFinFlag]
            (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
    :=
    forbidEq_smul (forbidEq_symm one_forbidEq_one_size_five_expand)
  exact forbidLE_trans h₁ (forbidLE_trans (forbidLE_of_le h₂) (forbidLE_of_forbidEq h₃))

end ErdosPentagon
