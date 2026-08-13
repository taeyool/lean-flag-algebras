import Mathlib.Tactic
import Mathlib.Tactic.Conv
import LeanFlagAlgebras.FlagAlgebra.FlagAlgebra

/-! # `flagsum_sort` / `flagsum_ac_sort` tactics: canonical ordering of additive expressions

Shared custom tactics that reorder the terms of a sum into a canonical order keyed by the
trailing numeric index of each base atom. `flagsum_sort`/`flagsum_sort_lhs`/`flagsum_sort_rhs`
normalize linear combinations (`coeff • base`), while the `flagsum_ac_sort*` family does
add-AC reordering only; `*_pipeline` variants bundle arithmetic-normalization simp passes.
Used to line up flag sums on both sides of (in)equalities so they can be compared term-by-term.
-/

open Lean Elab Tactic Meta

namespace FlagAlgebras.Automation

/-- Linear term represented as `(base, coeff)` meaning `coeff • base`. -/
abbrev LinTerm := Expr × Expr

/-! ## 1) Common Definitions -/

private def parseTrailingNat? (s : String) : Option Nat :=
  let revDigits := s.toList.reverse.takeWhile Char.isDigit
  if revDigits.isEmpty then
    none
  else
    (String.ofList revDigits.reverse).toNat?

/-- Extracts `(index, tie-break key)` from a term's base expression, keyed off the trailing
numeral of the applied head symbol's name (e.g. `FlagAlgebra_5_0_0_7` ↦ `7`). The head-constant
name is checked first since it is free (no `MetaM` work); the full pretty-printer only runs as a
fallback when the head isn't a plain numbered constant, since `ppExpr` is comparatively expensive
and most terms in a flag sum resolve via the cheap path. -/
private def baseIndexKey (e : Expr) : MetaM (Nat × String) := do
  let e := e.consumeMData
  match e.getAppFn.consumeMData with
  | Expr.const nm _ =>
      let nmStr := nm.toString
      match parseTrailingNat? nmStr with
      | some idx => pure (idx, nmStr)
      | none =>
          let keyStr := (← ppExpr e).pretty
          pure ((parseTrailingNat? keyStr).getD 1000000000, keyStr)
  | _ =>
      let keyStr := (← ppExpr e).pretty
      pure ((parseTrailingNat? keyStr).getD 1000000000, keyStr)

private def getBinaryOpArgs? (opName : Name) (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then none else some (args[args.size - 2]!, args[args.size - 1]!)

private def getAddArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HAdd.hAdd e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``Add.add e

private def getSubArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HSub.hSub e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``Sub.sub e

private def getSmulArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HSMul.hSMul e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``SMul.smul e

private def getUnaryOpArg? (opName : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.isEmpty then none else some args[args.size - 1]!

private def getNegArg? (e : Expr) : Option Expr :=
  getUnaryOpArg? ``Neg.neg e

private def insertSortedBy {α}
    (goesBefore : α → α → Bool)
    (item : α)
    (sorted : Array α)
    : Array α :=
  Id.run do
    let mut inserted := false
    let mut next : Array α := #[]
    for old in sorted do
      if !inserted && goesBefore item old then
        next := next.push item
        inserted := true
      next := next.push old
    if !inserted then
      next := next.push item
    return next

private def getEqSides (target : Expr) : TacticM (Expr × Expr) := do
  let t := target.consumeMData
  if !t.getAppFn.isConstOf ``Eq then
    throwError "normalize_flagsum: goal must be an equality"
  let args := t.getAppArgs
  if args.size != 3 then
    throwError "normalize_flagsum: malformed equality target"
  pure (args[1]!, args[2]!)

private def replaceGoalUsingLhsEq
    (goal : MVarId)
    (lhsSorted rhs hLhs : Expr)
    : TacticM Unit := do
  let newGoalType ← mkEq lhsSorted rhs
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType
  let proof ← mkEqTrans hLhs newGoal
  goal.assign proof
  replaceMainGoal [newGoal.mvarId!]

private def replaceGoalUsingRhsEq
    (goal : MVarId)
    (lhs rhsSorted hRhs : Expr)
    : TacticM Unit := do
  let newGoalType ← mkEq lhs rhsSorted
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newGoalType
  let proof ← mkEqTrans newGoal (← mkEqSymm hRhs)
  goal.assign proof
  replaceMainGoal [newGoal.mvarId!]

private def withTimer (label : String) (act : TacticM Unit) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  act
  let t1 ← IO.monoMsNow
  logInfo m!"[timer] {label}: {t1 - t0} ms"

/-! ## 2) Definitions for `sort` and `sort` Implementation -/

private def mkOneCoeff : TacticM Expr := do
  Lean.Elab.Term.elabTerm (← `(term| (1 : ℝ))) none

private partial def flattenLinearTerms (e : Expr) : TacticM (Array LinTerm) := do
  let e0 := e.consumeMData
  let e ←
    match e0 with
    | Expr.const .. =>
        match (← delta? e0) with
        | some e' => pure e'
        | none => pure e0
    | _ => pure e0
  if let some (a, b) := getAddArgs? e then
    return (← flattenLinearTerms a) ++ (← flattenLinearTerms b)
  if let some (a, b) := getSubArgs? e then
    let left ← flattenLinearTerms a
    let right ← flattenLinearTerms b
    let rightNeg ← right.mapM fun (base, coeff) => do
      let negCoeff ← mkAppM ``Neg.neg #[coeff]
      pure (base, negCoeff)
    return left ++ rightNeg
  if let some a := getNegArg? e then
    let terms ← flattenLinearTerms a
    let negTerms ← terms.mapM fun (base, coeff) => do
      let negCoeff ← mkAppM ``Neg.neg #[coeff]
      pure (base, negCoeff)
    return negTerms
  if let some (coeff, base) := getSmulArgs? e then
    return #[(base, coeff)]
  return #[(e, (← mkOneCoeff))]

private structure KeyedTerm where
  idx : Nat
  key : String
  base : Expr
  coeff : Expr

private def insertSortedByKey
    (item : KeyedTerm)
    (sorted : Array KeyedTerm)
    : Array KeyedTerm :=
  insertSortedBy
    (fun a b => a.idx < b.idx || (a.idx = b.idx && a.key < b.key))
    item
    sorted

private def sortLinearTermsByIndex (terms : Array LinTerm) : TacticM (Array LinTerm) := do
  let keyed ← terms.mapM fun (base, coeff) => do
    let (idx, key) ← baseIndexKey base
    pure ({ idx := idx, key := key, base := base, coeff := coeff } : KeyedTerm)
  let mut sorted : Array KeyedTerm := #[]
  for item in keyed do
    sorted := insertSortedByKey item sorted
  pure <| sorted.map fun t => (t.base, t.coeff)

private def rebuildLinearExpr (terms : Array LinTerm) : TacticM Expr := do
  let smulTerms ← terms.mapM fun (base, coeff) => mkAppM ``HSMul.hSMul #[coeff, base]
  match smulTerms.toList with
  | [] => throwError "rebuildLinearExpr: empty term list"
  | t :: ts => ts.foldlM (fun acc nxt => mkAppM ``HAdd.hAdd #[acc, nxt]) t

private def normalizeLinearExpr (e : Expr) : TacticM Expr := do
  let flat ← flattenLinearTerms e
  let sorted ← sortLinearTermsByIndex flat
  rebuildLinearExpr sorted

private def proveEqByAC (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  match lhs.consumeMData with
  | Expr.const nm _ =>
      let id := mkIdent nm
      evalTactic (← `(tactic| try (delta $id)))
  | _ => pure ()
  match rhs.consumeMData with
  | Expr.const nm _ =>
      let id := mkIdent nm
      evalTactic (← `(tactic| try (delta $id)))
  | _ => pure ()
  evalTactic (← `(tactic|
    (try dsimp;
     try (simp [sub_eq_add_neg, smul_eq_mul,
                one_smul, neg_one_smul, neg_smul,
                add_assoc, add_left_comm, add_comm]);
     first
      | ac_rfl
      | try abel_nf
      | try ring_nf)))
  let remaining ← getGoals
  if !remaining.isEmpty then
    throwError m!"proveEqByAC: failed to close normalization side-goal\noriginal lhs: {lhs}\nnormalized: {rhs}"
  setGoals savedGoals
  instantiateMVars mvar

/-- Debug helper: logs the normalized (index-sorted) forms of both sides of an equality
goal without changing the goal. -/
elab "preview_flagsum_nf" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (lhs, rhs) ← getEqSides target
    let lhsNorm ← normalizeLinearExpr lhs
    let rhsNorm ← normalizeLinearExpr rhs
    logInfo m!"[flagsum-nf] LHS: {lhsNorm}"
    logInfo m!"[flagsum-nf] RHS: {rhsNorm}"

/-- Shared implementation: normalizes the current conv focus. -/
private def sortNormalizeConv : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (focus, rhs) ← getEqSides target
    let focusSorted ← normalizeLinearExpr focus
    let h ← proveEqByAC focus focusSorted
    replaceGoalUsingLhsEq goal focusSorted rhs h

/-- Normalize the current conv focus. Use inside `conv_lhs`, `conv_rhs`, or any `conv` block. -/
elab "sort_here" : conv => sortNormalizeConv

/-- Sort only the left side. Works on any relation (=, ≤, <, …). -/
elab "flagsum_sort_lhs" : tactic => do
  evalTactic (← `(tactic| conv_lhs => sort_here))

/-- Sort only the right side. Works on any relation (=, ≤, <, …). -/
elab "flagsum_sort_rhs" : tactic => do
  evalTactic (← `(tactic| conv_rhs => sort_here))

/-- Sort both sides. Works on any relation (=, ≤, <, …). -/
elab "flagsum_sort" : tactic => do
  evalTactic (← `(tactic| flagsum_sort_lhs; flagsum_sort_rhs))

/-- `conv` entry: normalize the current focus (alias for `sort_here`). -/
elab "sort_at" : conv => sortNormalizeConv

/-- Timed `conv` entry for `sort_at` (logs elapsed ms). -/
elab "sort_at_timer" : conv => do
  withTimer "sort_at" sortNormalizeConv

/-! ## 3) Definitions for `ac_sort` and `ac_sort` Implementation -/

/-- Accumulator-passing flatten: pushes onto a single growing array instead of `++`-ing
subresults, so a long left-associated chain of `n` summands costs `O(n)` instead of `O(n²)`. -/
private partial def flattenAddTermsInto (acc : Array Expr) (e : Expr) : Array Expr :=
  let e := e.consumeMData
  match getAddArgs? e with
  | some (a, b) => flattenAddTermsInto (flattenAddTermsInto acc a) b
  | none => acc.push e

private def flattenAddTerms (e : Expr) : Array Expr :=
  flattenAddTermsInto #[] e

private def addTermKey (e : Expr) : MetaM (Nat × String) := do
  let e := e.consumeMData
  match getSmulArgs? e with
  | some (_, base) => baseIndexKey base
  | none => baseIndexKey e

private def sortAddTermsByKey (terms : Array Expr) : MetaM (Array Expr) := do
  let keyed ← terms.mapM fun t => do
    let (idx, key) ← addTermKey t
    pure (idx, key, t)
  let sorted := keyed.qsort (fun a b => a.1 < b.1 || (a.1 = b.1 && a.2.1 < b.2.1))
  pure <| sorted.map fun (_, _, t) => t

private partial def mkRightAssocAdd (terms : List Expr) : MetaM Expr := do
  match terms with
  | [] => throwError "mkRightAssocAdd: empty term list"
  | [t] => pure t
  | t :: ts => do
      let rest ← mkRightAssocAdd ts
      mkAppM ``HAdd.hAdd #[t, rest]

/-- The `+`-application with its type/instance implicit args already filled in but its two
explicit operands left open, extracted from an existing `HAdd`/`Add` application. Reapplying it
via `mkAppN` (pure term construction) avoids repeating typeclass instance search for every pair
that `mkAppM` would otherwise perform. -/
private def getBinaryOpPrefixFn? (opName : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then none else some (mkAppN fn (args.extract 0 (args.size - 2)))

private def getAddPrefixFn? (e : Expr) : Option Expr :=
  match getBinaryOpPrefixFn? ``HAdd.hAdd e with
  | some fn => some fn
  | none => getBinaryOpPrefixFn? ``Add.add e

private partial def mkRightAssocAddFast (prefixFn : Expr) (terms : List Expr) : Expr :=
  match terms with
  | [] => panic! "mkRightAssocAddFast: empty term list"
  | [t] => t
  | t :: ts => mkAppN prefixFn #[t, mkRightAssocAddFast prefixFn ts]

/-- Same as `mkRightAssocAddFast` but left-associated (`(...(t1+t2)+t3...)+tn`). Downstream
consumers of `flagsum_ac_sort_rhs_pipeline`'s output (e.g. `flag_nonneg`'s
`repeat apply add_nonneg`, which — absent `all_goals`/`<;>` — only ever recurses into the first
of the two goals `add_nonneg` produces) rely on this specific shape: for a right-associated sum
`t1 + (t2 + (... + tn))`, splitting peels off only `t1` before getting stuck on the untouched
`t2 + (... + tn)` remainder, whereas a left-associated sum fully decomposes (see
`FLAGSUMSORT_PERF_PROGRESS.md` for how this was diagnosed). -/
private partial def mkLeftAssocAddFast (prefixFn : Expr) (terms : List Expr) : Expr :=
  match terms with
  | [] => panic! "mkLeftAssocAddFast: empty term list"
  | t :: ts => ts.foldl (fun acc t' => mkAppN prefixFn #[acc, t']) t

/-- Rebuild the sorted terms into a right-associated sum. `topE` is the original (pre-sort)
expression, used only to harvest a reusable `+`-instance prefix (see `getAddPrefixFn?`); when
that harvest fails (e.g. `terms` has a single element and `topE` was never an add-application to
begin with) falls back to the slower `mkAppM`-based construction. -/
private def rebuildAddExprRightAssoc (topE : Expr) (terms : Array Expr) : MetaM Expr :=
  match getAddPrefixFn? topE with
  | some prefixFn => pure (mkRightAssocAddFast prefixFn terms.toList)
  | none => mkRightAssocAdd terms.toList

private def normalizeByAddPermutation (e : Expr) : MetaM Expr := do
  let terms := flattenAddTerms e
  let sorted ← sortAddTermsByKey terms
  rebuildAddExprRightAssoc e sorted

private def proveEqByAddAC (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| first | ac_rfl | simp [add_assoc, add_left_comm, add_comm]))
  let remaining ← getGoals
  if !remaining.isEmpty then
    throwError m!"proveEqByAddAC: failed to close side-goal\noriginal lhs: {lhs}\nsorted lhs: {rhs}"
  setGoals savedGoals
  instantiateMVars mvar

/-! ### Merging same-base terms after the sort

`acSortNormalizeConv` only permutes terms; once sorted, terms sharing a base are guaranteed
adjacent, but coefficients aren't combined yet (`c₁ • x + c₂ • x` stays as two summands). The
original pipeline left finding and combining such pairs to a `simp only [← add_assoc, ← add_smul]`
search over the whole (possibly huge) rebuilt tree, which dominated the pipeline's cost even when
there was nothing to merge (see `FLAGSUMSORT_PERF_PROGRESS.md`). Since the sort already tells us
exactly which entries are adjacent-and-equal, we merge them directly instead: each merge step's
proof goal is `O(1)`-sized (the unmerged "rest" of the sum, `R`, is left as one opaque black-box
subterm — `simp` never descends into it), so the cost is independent of how large the surrounding
sum is.

A prior version of this built each merge step's proof via raw `mkAppM ``add_smul`/``add_assoc``
term construction; that caused a real regression in `K5freeEdge.lean` (`flag_nonneg`'s
`repeat apply add_nonneg` got stuck on a merged term, likely an instance-path mismatch — see
`FLAGSUMSORT_PERF_PROGRESS.md`). This version instead proves each merge step via a small
tactic-mode goal (`mkMergeStepProof`, the same "synthetic mvar + evalTactic" pattern
`proveEqByAddAC` already uses), so `add_smul`/`add_assoc` go through the ordinary elaborator
instead of being hand-assembled. -/

/-- `-x = (-1 : ℝ) • x`, restricted to `FlagAlgebra σ`.

`mergeAdjacentAndProve` only merges summands carrying an explicit `c • _` coefficient (see
`termOf`), so a bare `-x` never combines with the `c • x` next to it. That is what used to strand
a `- FlagAlgebra_n_0_0_i` summand in the `objN = hostN` certificates: the objective is moved onto
the right as a plain flag and never cancels against the `bound • FlagAlgebra_n_0_0_i` coming from
the unit expansion, leaving `flag_nonneg` the unprovable goal `0 ≤ φ (-FlagAlgebra_…)`.

`acSortPipeline`'s pre-simp already rewrites `-(a • x)` to `(-a) • x` (`← neg_smul`); it just had
no rule for a negation with no coefficient at all. A general `← neg_one_smul` would be wrong here:
`ℝ` is a module over itself, so it would rewrite scalar literals too. Restricting the statement to
`FlagAlgebra σ` makes it fire on flag summands only. -/
theorem flagNeg_eq_negOne_smul {n₀ : ℕ} {σ : FlagAlgebras.FlagType (Fin n₀)}
    (x : FlagAlgebras.FlagAlgebra σ) : -x = (-1 : ℝ) • x :=
  (neg_one_smul ℝ x).symm

private def mkSmul (coeff base : Expr) : MetaM Expr :=
  mkAppM ``HSMul.hSMul #[coeff, base]

/-- Reconstructs the actual term from a `(coeff, base)` pair: `some c, b ↦ c • b`, but
`none, t ↦ t` *unchanged* — a term that wasn't `smul`-headed to begin with (e.g. a bare negated
flag `-x` left over from something `pre-simp`'s lemma set didn't fully absorb into a coefficient)
must be rebuilt exactly as `t`, not wrapped as `(1 : _) • t`: that wrapper is syntactically
different (even though `one_smul`-defeq) and broke `K3freeP3.lean`'s proof term downstream —
see `FLAGSUMSORT_PERF_PROGRESS.md`. Terms with `none` therefore also never participate in
merging (`mergeableCoeffs` below always rejects them), since merging would require synthesizing
exactly this kind of coefficient wrapper. -/
private def termOf (coeff : Option Expr) (base : Expr) : MetaM Expr :=
  match coeff with
  | some c => mkSmul c base
  | none => pure base

/-- `h : a = b` ↦ proof of `head + a = head + b`. Pure `congrArg` — no typeclass-sensitive lemma
involved, so (unlike `add_smul`/`add_assoc`) there's no suspected reason to route this through
tactic-mode instead of direct term construction. -/
private def congrArgAddLeft (prefixFn head h : Expr) : MetaM Expr := do
  let some (ty, _, _) := (← inferType h).eq? | throwError "congrArgAddLeft: expected an Eq proof"
  withLocalDeclD `x ty fun x => do
    let f ← mkLambdaFVars #[x] (mkAppN prefixFn #[head, x])
    mkAppM ``congrArg #[f, h]

/-- Proves `lhs = rhs` via a small, self-contained tactic-mode goal (mirroring `proveEqByAddAC`'s
"synthetic mvar + evalTactic" pattern) instead of assembling the proof by hand from
`add_assoc`/`add_smul` applied directly. Any opaque subterm shared between `lhs` and `rhs` (e.g.
the unmerged "rest" of the sum) is never descended into by `simp`, so this stays `O(1)` regardless
of how large that shared subterm is. -/
private def mkMergeStepProof (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| simp only [add_assoc, add_smul]))
  let remaining ← getGoals
  if !remaining.isEmpty then
    throwError m!"mkMergeStepProof: failed to close merge step\nlhs: {lhs}\nrhs: {rhs}"
  setGoals savedGoals
  instantiateMVars mvar

/-- Two adjacent entries are mergeable only when *both* have an explicit coefficient (see
`termOf`) and, after a cheap key pre-filter, their bases are confirmed `isDefEq`. Returns the two
coefficients when mergeable. -/
private def mergeableCoeffs (key1 key2 : String) (coeff1 coeff2 : Option Expr) (base1 base2 : Expr) :
    MetaM (Option (Expr × Expr)) := do
  match coeff1, coeff2 with
  | some c1, some c2 =>
      if key1 != key2 then
        pure none
      else if ← isDefEq base1 base2 then
        pure (some (c1, c2))
      else
        pure none
  | _, _ => pure none

/-- Walks a sorted `(key, coeff?, base)` array left to right, merging maximal adjacent runs that
share a base (only among entries with an explicit `coeff`). Returns the merged list together with
a proof that the right-associated sum of the input equals the right-associated sum of the merged
list.

`entries` is the sorted input; `suffix i` must be the right-associated sum of `entries[i:]`, and
`suffix` is built once by the caller. Two things keep a merge step `O(1)` rather than `O(n)`:

* the unmerged remainder is looked up in `suffix` instead of being rebuilt — the previous version
  re-derived it with `rest.mapM termOf`, one `mkAppM` (and so one typeclass search) per remaining
  summand *per step*, which made the whole pass quadratic (~52 000 instance searches for a
  324-term sum, and far worse for the size-6 examples);
* the remainder is abstracted as a local `r` before the step's proof goal is built, so
  `mkMergeStepProof` really does see the `O(1)` goal `c₁ • x + (c₂ • x + r) = (c₁ + c₂) • x + r`
  instead of one containing the whole rest of the sum for `simp only` to walk.

The proof shape is unchanged — each step is still discharged by a small tactic-mode goal, so the
instance paths that this module's history warns about are the same as before. -/
private partial def mergeAdjacentAndProve (prefixFn : Expr)
    (entries : Array (String × Option Expr × Expr)) (suffix : Array Expr) :
    TacticM (List (String × Option Expr × Expr) × Expr) := do
  let n := entries.size
  if n == 0 then throwError "mergeAdjacentAndProve: empty term list"
  let rec go (head : String × Option Expr × Expr) (i : Nat) :
      TacticM (List (String × Option Expr × Expr) × Expr) := do
    let (k1, oc1, b1) := head
    if i ≥ n then
      return ([head], ← mkEqRefl (← termOf oc1 b1))
    let (k2, oc2, b2) := entries[i]!
    match ← mergeableCoeffs k1 k2 oc1 oc2 b1 b2 with
    | some (c1, c2) => do
        let c12 ← mkAppM ``HAdd.hAdd #[c1, c2]
        let t1 ← mkSmul c1 b1
        let t2 ← mkSmul c2 b1
        let t12 ← mkSmul c12 b1
        if i + 1 ≥ n then
          let step ← mkMergeStepProof (← mkAppM ``HAdd.hAdd #[t1, t2]) t12
          return ([(k1, some c12, b1)], step)
        let (mergedRest, eq2) ← go (k1, some c12, b1) (i + 1)
        let restRebuilt := suffix[i + 1]!
        let ty ← inferType t1
        let bridge ← withLocalDeclD `r ty fun r => do
          let lhsR ← mkAppM ``HAdd.hAdd #[t1, ← mkAppM ``HAdd.hAdd #[t2, r]]
          let rhsR ← mkAppM ``HAdd.hAdd #[t12, r]
          pure (mkApp (← mkLambdaFVars #[r] (← mkMergeStepProof lhsR rhsR)) restRebuilt)
        return (mergedRest, ← mkEqTrans bridge eq2)
    | none => do
        let (mergedRest, restEq) ← go (k2, oc2, b2) (i + 1)
        let t1 ← termOf oc1 b1
        return ((k1, oc1, b1) :: mergedRest, ← congrArgAddLeft prefixFn t1 restEq)
  go entries[0]! 1

/-- `conv`-mode step: after `acSortNormalizeConv` has sorted the current focus by base index,
merge adjacent same-base runs (coefficient consolidation), then re-associate the result to
*left*-associated (`(...(t1+t2)+t3...)+tn`) via `proveEqByAddAC`/`ac_rfl` — already-measured-fast
for pure reassociation, no `simp` search. The left-assoc reshape happens unconditionally (even
with nothing to merge) since downstream consumers like `flag_nonneg`'s
`repeat apply add_nonneg` depend on it (see `mkLeftAssocAddFast`'s docstring). `norm_num` (to fold
the resulting literal coefficient sums) only runs when a merge actually happened. -/
private def mergeSameBaseTermsConv : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (focus, rhs) ← getEqSides target
    let terms := flattenAddTerms focus
    let pairs ← terms.mapM fun t => do
      let key := (← addTermKey t).2
      match getSmulArgs? t with
      | some (c, b) => pure (key, some c, b)
      | none => pure (key, none, t)
    match getAddPrefixFn? focus with
    | none => pure ()
    | some prefixFn =>
        -- Build each summand and each right-associated suffix exactly once; the merge walk
        -- indexes into `suffix` instead of re-deriving the remainder at every step.
        let termArr ← pairs.mapM fun (_, oc, b) => termOf oc b
        let mut suffix : Array Expr := Array.replicate termArr.size default
        if termArr.size > 0 then
          suffix := suffix.set! (termArr.size - 1) termArr[termArr.size - 1]!
          for j in [0:termArr.size - 1] do
            let idx := termArr.size - 2 - j
            suffix := suffix.set! idx (mkAppN prefixFn #[termArr[idx]!, suffix[idx + 1]!])
        let (merged, mergeProof) ← mergeAdjacentAndProve prefixFn pairs suffix
        let didMerge := merged.length < pairs.size
        let mergedTerms ← merged.mapM fun (_, oc, b) => termOf oc b
        let mergedExprRight := mkRightAssocAddFast prefixFn mergedTerms
        let mergedExprLeft := mkLeftAssocAddFast prefixFn mergedTerms
        let assocProof ← proveEqByAddAC mergedExprRight mergedExprLeft
        let fullProof ← mkEqTrans mergeProof assocProof
        replaceGoalUsingLhsEq goal mergedExprLeft rhs fullProof
        if didMerge then
          evalTactic (← `(tactic| try norm_num))

/-- Shared implementation: normalizes the current conv focus using add-AC only. -/
private def acSortNormalizeConv : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (focus, rhs) ← getEqSides target
    let focusSorted ← normalizeByAddPermutation focus
    let h ← proveEqByAddAC focus focusSorted
    replaceGoalUsingLhsEq goal focusSorted rhs h

/-- Normalize the current conv focus using add-AC. Use inside `conv_lhs`, `conv_rhs`, etc. -/
elab "ac_sort_here" : conv => acSortNormalizeConv

/-- Swap-based sort on LHS. Works on any relation (=, ≤, <, …). -/
elab "ac_sort_lhs" : tactic => do
  evalTactic (← `(tactic| conv_lhs => ac_sort_here))

/-- Swap-based sort on RHS. Works on any relation (=, ≤, <, …). -/
elab "ac_sort_rhs" : tactic => do
  evalTactic (← `(tactic| conv_rhs => ac_sort_here))

/-- Swap-based sort on both sides. Works on any relation (=, ≤, <, …). -/
elab "ac_sort" : tactic => do
  evalTactic (← `(tactic| ac_sort_lhs; ac_sort_rhs))

/-- `conv` entry: normalize current focus using add-AC (alias for `ac_sort_here`). -/
elab "ac_sort_at" : conv => acSortNormalizeConv

/-- Timed `conv` entry for `ac_sort_at` (logs elapsed ms). -/
elab "ac_sort_at_timer" : conv => do
  withTimer "ac_sort_at" acSortNormalizeConv

/--
Utility `conv` entry around `ac_sort_at`:
`norm_num; simp; ac_sort_at; simp only [← add_assoc, ← add_smul]; norm_num`.

Use this inside `conv` when you want to normalize arithmetic first and then
perform add-AC sorting on the focused expression.
-/
elab "ac_sort_at_pipeline" : conv => do
  -- `maxSteps` is bumped well above the default (100000): the `add_assoc` re-association is
  -- roughly quadratic in the number of summands, so a long RHS sum (large SDP blocks) otherwise
  -- trips `simp`'s "maximum number of steps exceeded" guard. This is a limit, not a loop.
  evalTactic (← `(tactic|
    (try (simp (config := { maxSteps := 10000000 }) only
      [neg_neg, neg_add, sub_eq_add_neg, ← neg_smul, flagNeg_eq_negOne_smul,
       add_assoc, smul_smul]))))
  acSortNormalizeConv
  mergeSameBaseTermsConv

/--
Run the common pipeline on the left side of an equality goal:
`conv_lhs => ac_sort_at_pipeline`.
-/
elab "flagsum_ac_sort_lhs_pipeline" : tactic =>
  do
    evalTactic (← `(tactic|
      (conv_lhs =>
         ac_sort_at_pipeline)))

/--
Run the common pipeline on the right side of an equality goal:
`conv_rhs => ac_sort_at_pipeline`.
-/
elab "flagsum_ac_sort_rhs_pipeline" : tactic =>
  do
    evalTactic (← `(tactic|
      (conv_rhs =>
         ac_sort_at_pipeline)))

/-- Timed variant of `flagsum_ac_sort_rhs_pipeline` (logs elapsed ms). Benchmarking aid. -/
elab "flagsum_ac_sort_rhs_pipeline_timer" : tactic => do
  withTimer "flagsum_ac_sort_rhs_pipeline" do
    evalTactic (← `(tactic|
      (conv_rhs =>
         ac_sort_at_pipeline)))

/--
Run the common pipeline on both sides of an equality goal.
-/
elab "flagsum_ac_sort_pipeline" : tactic =>
  do
    evalTactic (← `(tactic|
      flagsum_ac_sort_lhs_pipeline;
      flagsum_ac_sort_rhs_pipeline))

end FlagAlgebras.Automation
