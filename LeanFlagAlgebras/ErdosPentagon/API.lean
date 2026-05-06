import LeanFlagAlgebras.ErdosPentagon.FlagMul
import LeanFlagAlgebras.ErdosPentagon.SortTactic
import LeanFlagAlgebras.ErdosPentagon.Lemmas
import LeanFlagAlgebras.Forbid.Basic
import Mathlib.Tactic

open FlagAlgebras Forbid
open Lean Elab Tactic Meta Command

namespace ErdosPentagon

noncomputable def one_expand
    (F_forbid : FinFlag ∅ₜ) (expandSize : ℕ)
    : FlagAlgebra ∅ₜ :=
  ∑ F' : FlagWithSize ∅ₜ expandSize with flagDensity₁ F_forbid.2 (unlabel F') = 0,
    (flagDensity₁ ((⟨0, default⟩ : FinFlag ∅ₜ).2) F' : ℝ) • ⟦unitVector ⟨expandSize, F'⟩⟧

theorem one_forbidEq_expand
    (F_forbid : FinFlag ∅ₜ) (expandSize : ℕ)
    : (1 : FlagAlgebra ∅ₜ) =[F_forbid] one_expand F_forbid expandSize := by
  simpa [one_expand] using
    (unitVector_quot_forbidEq_sum (σ := ∅ₜ) F_forbid (⟨0, default⟩ : FinFlag ∅ₜ) expandSize (by simp))

lemma forbidLE_trans_add_nonneg
    {F_forbid : FinFlag ∅ₜ} {f g c : FlagAlgebra ∅ₜ}
    (hfg : f ≤[F_forbid] g) (hc : 0 ≤[F_forbid] c)
    : f ≤[F_forbid] (g + c) := by
  rw [← add_zero f]
  exact forbidLE_add hfg hc

theorem flagQuadraticForm_downward_forbidLE_nonneg
  (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : 0 ≤[K3.toFinFlag] ⟦flagQuadraticForm M v⟧₀
  := by
  apply downward_forbidLE_nonneg
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg M hM v

theorem forbidLE_add_QuadraticForm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : (f ≤[F_forbid] g) → f ≤[F_forbid] g + ⟦flagQuadraticForm M v⟧₀
  := by
  intro hfg
  rw [← add_zero f]
  apply forbidLE_add hfg
  apply downward_forbidLE_nonneg
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg M hM v

/-
  Given:
  matrix P, Q, R (PSD)
  psdProp : hP, hQ, hR
  vector v₀, v₁, v₂
  forbid graph : K3
  expand_size : 5

  =>

  flagQuadraticForm P_real v0
  flagQuadraticForm Q_real v1
  flagQuadraticForm R_real v2

  task : Need a way to find out the result when expanding.
-/

section ReduceDownwardFlagMul

/-!
`reduce_downward_flagmul` automates the rewriting pattern shown in the example
just below.  Given a goal of the form

```
  downward (c₁ • (A₁ * B₁)) + downward (c₂ • (A₂ * B₂)) + ... + downward (cₙ • (Aₙ * Bₙ))
    ≤[F_forbid] rhs
```

it repeatedly looks at the head term of the left-hand side (after right-
associating the addition with `simp only [add_assoc]`), looks up the
corresponding `flagMul_<A>_<B>` theorem from the constants used in the head
term, and rewrites the head using

```
  Forbid.forbidLE_rw_left_add_right (downward_forbidLE_equal_flags
    (forbidEq_smul flagMul_<A>_<B>))
  forbidLE_move_add_left_iff
```

For the final (right-most) summand it instead uses

```
  forbidLE_rw_left (downward_forbidLE_equal_flags (forbidEq_smul flagMul_<A>_<B>))
  forbidLE_move_term_left_iff
```

The implementation closely mirrors the `reduce_flagmul` tactic in
`Lemmas.lean`, except that it operates on `forbidLE`-goals whose summands are
wrapped in `downward` and uses the corresponding `forbidLE_*` lemmas.  All of
the helper definitions are kept private to this section so they do not leak
out of the file.
-/

private def lastNamePartLE (nm : Name) : String :=
  match nm with
  | .anonymous => ""
  | .str _ s => s
  | .num _ n => toString n

private partial def findFlagAlgebraConstLE? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if (lastNamePartLE nm).startsWith "FlagAlgebra_" then some nm else none
  | .app f x =>
      match findFlagAlgebraConstLE? f with
      | some nm => some nm
      | none => findFlagAlgebraConstLE? x
  | .lam _ _ b _ => findFlagAlgebraConstLE? b
  | .forallE _ _ b _ => findFlagAlgebraConstLE? b
  | .letE _ _ v b _ =>
      match findFlagAlgebraConstLE? v with
      | some nm => some nm
      | none => findFlagAlgebraConstLE? b
  | .mdata _ b => findFlagAlgebraConstLE? b
  | .proj _ _ b => findFlagAlgebraConstLE? b
  | _ => none

private partial def findFlagConstLE? (e : Expr) : Option Name :=
  match e with
  | .const nm _ =>
      if (lastNamePartLE nm).startsWith "Flag_" then some nm else none
  | .app f x =>
      match findFlagConstLE? f with
      | some nm => some nm
      | none => findFlagConstLE? x
  | .lam _ _ b _ => findFlagConstLE? b
  | .forallE _ _ b _ => findFlagConstLE? b
  | .letE _ _ v b _ =>
      match findFlagConstLE? v with
      | some nm => some nm
      | none => findFlagConstLE? b
  | .mdata _ b => findFlagConstLE? b
  | .proj _ _ b => findFlagConstLE? b
  | _ => none

private def getBinAppArgsLE? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app (.app _ a) b => some (a, b)
  | _ => none

private def getAddArgsLE? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``Add.add) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    getBinAppArgsLE? e

private def getSmulArgsLE? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HSMul.hSMul || fn.isConstOf ``SMul.smul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    match e with
    | .app f x => some (f, x)
    | _ => none

private def getMulArgsLE? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HMul.hMul || fn.isConstOf ``Mul.mul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    getBinAppArgsLE? e

/-- Strip an outer `FlagAlgebras.downward` application, returning its argument. -/
private def stripDownwardLE? (e : Expr) : Option Expr :=
  if e.isAppOf ``FlagAlgebras.downward then
    let args := e.getAppArgs
    if args.size >= 1 then some args[args.size - 1]! else none
  else none

private def flagToFlagAlgebraLastPartLE (s : String) : String :=
  if s.startsWith "Flag_" then
    "FlagAlgebra_" ++ s.drop 5
  else
    s

/-- Given `mulTerm = A * B`, search the environment for a theorem named
`flagMul_<A>_<B>` (or its reverse).  The lookup mirrors the strategy used by
`reduce_flagmul` in `Lemmas.lean`. -/
private def mkFlagMulThmNameLE? (mulTerm : Expr) : MetaM (Option Name) := do
  let some (fExpr, gExpr) := getMulArgsLE? mulTerm | return none
  let fNm? := findFlagAlgebraConstLE? fExpr
  let gNm? := findFlagAlgebraConstLE? gExpr
  let fFlag? := findFlagConstLE? fExpr
  let gFlag? := findFlagConstLE? gExpr
  let some fNm := fNm?.orElse (fun _ => fFlag?) | return none
  let some gNm := gNm?.orElse (fun _ => gFlag?) | return none
  let env ← getEnv
  let fLast := if fNm?.isSome then lastNamePartLE fNm
               else flagToFlagAlgebraLastPartLE (lastNamePartLE fNm)
  let gLast := if gNm?.isSome then lastNamePartLE gNm
               else flagToFlagAlgebraLastPartLE (lastNamePartLE gNm)
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

/-- Returns `true` when `e` contains a `FlagAlgebra_*` or `Flag_*` constant
(i.e. it is a plain flag term rather than a `downward` wrapper). -/
private def hasFlagConstLE (e : Expr) : Bool :=
  (findFlagAlgebraConstLE? e).isSome || (findFlagConstLE? e).isSome

/-- Perform a single reduction step.  Returns `true` when progress was made.

Two kinds of head terms are handled:
* `downward (c • (A * B))` — look up the `flagMul_*` theorem, rewrite, then move.
* plain flag term (contains a `FlagAlgebra_*` / `Flag_*` constant but is not
  wrapped in `downward`) — move directly with `forbidLE_move_add_left_iff` /
  `forbidLE_move_term_left_iff` without any rewriting. -/
private def stepReduceDownwardFlagMul : TacticM Bool :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let args := target.getAppArgs
    if args.size < 2 then
      return false
    let lhs := args[args.size - 2]!.consumeMData
    if let some (head, _rest) := getAddArgsLE? lhs then
      -- non-final case: head is the leftmost summand
      let head := head.consumeMData
      if let some downInner := stripDownwardLE? head then
        -- head is `downward (c • (A * B))`
        let downInner := downInner.consumeMData
        let some (_c, mulTerm) := getSmulArgsLE? downInner | return false
        let some thmName ← mkFlagMulThmNameLE? mulTerm
          | do
              let fNm? := findFlagAlgebraConstLE? mulTerm |>.orElse (fun _ => findFlagConstLE? mulTerm)
              throwError m!"reduce_downward_flagmul: could not find flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
        let thmId : TSyntax `term := mkIdent thmName
        evalTactic (← `(tactic|
          rw [Forbid.forbidLE_rw_left_add_right
                (downward_forbidLE_equal_flags (forbidEq_smul (c := _) $thmId)),
              forbidLE_move_add_left_iff]))
        return true
      else if hasFlagConstLE head then
        -- head is a plain flag term: move it directly
        evalTactic (← `(tactic| rw [forbidLE_move_add_left_iff]))
        return true
      else
        return false
    else
      dbg_trace s! "terminal case"
      -- terminal case: lhs itself is a single term
      if let some downInner := stripDownwardLE? lhs then
        dbg_trace s! "alone downward"
        -- lhs is `downward (c • (A * B))`
        let downInner := downInner.consumeMData
        let some (_c, mulTerm) := getSmulArgsLE? downInner | return false
        let some thmName ← mkFlagMulThmNameLE? mulTerm
          | do
              let fNm? := findFlagAlgebraConstLE? mulTerm |>.orElse (fun _ => findFlagConstLE? mulTerm)
              throwError m!"reduce_downward_flagmul: could not find terminal flagMul theorem for mulTerm={mulTerm}; detectedConst={fNm?.getD Name.anonymous}"
        let thmId : TSyntax `term := mkIdent thmName
        evalTactic (← `(tactic|
          rw [forbidLE_rw_left
                (downward_forbidLE_equal_flags (forbidEq_smul (c := _) $thmId)),
              forbidLE_move_term_left_iff]))
        return true
      else if hasFlagConstLE lhs then
        -- lhs is a plain flag term: move it directly
        dbg_trace s! "alone simple"
        evalTactic (← `(tactic| rw [forbidLE_move_term_left_iff]))
        return true
      else
        dbg_trace s! "why...?"
        return false

private partial def runReduceDownwardFlagMul
    (fuel : Nat := 256) (steps : Nat := 0) : TacticM Unit := do
  if fuel = 0 then
    throwError "reduce_downward_flagmul: fuel exhausted"
  let progressed ← stepReduceDownwardFlagMul
  if progressed then
    runReduceDownwardFlagMul (fuel - 1) (steps + 1)
  else
    if steps = 0 then
      withMainContext do
        let goal ← getMainGoal
        let target ← goal.getType
        let args := target.getAppArgs
        if args.size < 2 then
          throwError m!"reduce_downward_flagmul: target has too few args: {target}"
        let lhs := args[args.size - 2]!.consumeMData
        let add? := getAddArgsLE? lhs
        let down? := stripDownwardLE? lhs
        let smulOnHead? := match add? with
          | some (h, _) =>
              match stripDownwardLE? h.consumeMData with
              | some inner => getSmulArgsLE? inner.consumeMData
              | none => none
          | none => none
        throwError m!"reduce_downward_flagmul made no progress. lhs={lhs}; addDetected={add?.isSome}; downwardDetected={down?.isSome}; smulOnHeadDetected={smulOnHead?.isSome}"
    else
      pure ()

/-- Repeatedly rewrite the left-hand side of a `forbidLE` goal whose summands
have the form `downward (c • (A * B))`, replacing each `A * B` with the
expansion supplied by the corresponding `flagMul_*` theorem and moving the
already-rewritten terms onto the right.

Before iterating, this tactic right-associates the sum with
`simp only [add_assoc]`, matching the style of the manual proof in the example
just below. -/
elab "reduce_downward_flagmul" : tactic => do
  evalTactic (← `(tactic| try simp only [downward_add, add_assoc]))
  runReduceDownwardFlagMul

end ReduceDownwardFlagMul



/-
  @[simp]
  lemma unitVector_FlagAlgebra_5_0_0_0
      : ⟦unitVector ⟨5, Flag_5_0_0_0⟩⟧ = FlagAlgebra_5_0_0_0 := Quotient.out_inj.mp rfl
  @[simp]
  lemma unitVector_FlagAlgebra_5_0_0_1
      : ⟦unitVector ⟨5, Flag_5_0_0_1⟩⟧ = FlagAlgebra_5_0_0_1 := Quotient.out_inj.mp rfl
  ...
-/

syntax (name := generateUnitVectorLemmasCmd)
  "generate_unitVector_lemmas" num num : command

private def generateUnitVectorLemmas (n count : Nat) : CommandElabM Unit := do
  for idx in [:count] do
    let lemmaName := mkIdent (Name.mkSimple s!"unitVector_FlagAlgebra_{n}_0_0_{idx}")
    let flagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{idx}")
    let algebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{idx}")
    elabCommand (← `(
      @[simp]
      theorem $lemmaName
          : ⟦unitVector ⟨$(Syntax.mkNumLit (toString n)), $flagName⟩⟧ = $algebraName := Quotient.out_inj.mp rfl
    ))

elab_rules : command
  | `(command| generate_unitVector_lemmas $n:num $count:num) => do
      generateUnitVectorLemmas n.getNat count.getNat

-- Generate all unitVector lemmas for n=5 with 34 flags
generate_unitVector_lemmas 5 34

/-
  task 1. Improve reduce_downward_flagmul to handle more cases.
  task 2. Make tactic to automatically make lemmas like unitVector_FlagAlgebra_5_0_0_0, etc. : Done
  task 3. Organize computational processes and speed up
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1500

theorem ErdosPentagon_flagAlgebra_API
    : C5.toFlagAlgebra ≤[K3.toFinFlag] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  have h₁ : C5.toFlagAlgebra ≤[K3.toFinFlag]
            C5.toFlagAlgebra + ⟦flagQuadraticForm P_real v₀⟧₀
                             + ⟦flagQuadraticForm Q_real v₁⟧₀
                             + ⟦flagQuadraticForm R_real v₂⟧₀ := by
    apply forbidLE_trans_add_nonneg
    · apply forbidLE_trans_add_nonneg
      · apply forbidLE_trans_add_nonneg
        · exact forbidLE_refl K3.toFinFlag C5.toFlagAlgebra
        · exact flagQuadraticForm_downward_forbidLE_nonneg P_real P_real_posSemidef v₀
      · exact flagQuadraticForm_downward_forbidLE_nonneg Q_real Q_real_posSemidef v₁
    · exact flagQuadraticForm_downward_forbidLE_nonneg R_real R_real_posSemidef v₂

  apply forbidLE_trans h₁
  apply forbidLE_trans_forbidEq_right ?_  (forbidEq_smul (forbidEq_symm (one_forbidEq_expand K3.toFinFlag 5)))
  rw [C5_toFlagAlgebra_eq]
  simp [flagQuadraticForm, v₀, P_real, ratMatrixToReal, P, Fin.sum_univ_eight, add_assoc]
  simp [v₁, Q_real, ratMatrixToReal, Q, Fin.sum_univ_six, add_assoc]
  simp [v₂, R_real, ratMatrixToReal, R, Fin.sum_univ_five, add_assoc]

  reduce_downward_flagmul
  rw [forbidLE_rw_left (downward_forbidLE_equal_flags (forbidEq_smul flagMul_FlagAlgebra_4_3_2_6_FlagAlgebra_4_3_2_6))]
  rw [forbidLE_move_term_left_iff]

  dsimp only [one_expand]
  rw [Finset.sum_eq_multiset_sum]
  rw [← flagSet_5_0_0_eq_univ]
  simp [flagSet_5_0_0_val_eq, unlabel_emptyType]
  simp [default, flagDensity_empty]

  simp [smul_smul, downward_add, downward_smul]
  norm_num
  simp only [neg_add, neg_neg, sub_eq_add_neg, ← neg_smul, add_assoc]
  conv =>
    rhs
    ac_sort_at
  simp only [← add_assoc, ← add_smul]
  norm_num

  apply forbidLE_of_le
  intro φ
  simp only [sub_zero, PositiveHom.map_add, ge_iff_le]
  apply add_nonneg <;> try apply add_nonneg
  all_goals {
    simp only [PositiveHom.map_smul, Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_nonneg_iff_of_pos_left]
    apply positiveHom_unitVector_ge_zero
  }

end ErdosPentagon
