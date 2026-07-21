module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
-- `Module.Defs` provides the smul/group lemmas named inside this file's tactic quotations
-- (`add_smul`, `neg_smul`, `smul_smul`, `sub_eq_add_neg`, …). Without it those idents resolve
-- to dangling hygienic names (`add_smul✝`) at quotation time and every `simp only [...]`/merge
-- step that references them fails when the tactics run downstream.
public import Mathlib.Algebra.Module.Defs

@[expose] public section

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

private meta def parseTrailingNat? (s : String) : Option Nat :=
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
private meta def baseIndexKey (e : Expr) : MetaM (Nat × String) := do
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

private meta def getBinaryOpArgs? (opName : Name) (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then none else some (args[args.size - 2]!, args[args.size - 1]!)

private meta def getAddArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HAdd.hAdd e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``Add.add e

private meta def getSubArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HSub.hSub e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``Sub.sub e

private meta def getSmulArgs? (e : Expr) : Option (Expr × Expr) :=
  match getBinaryOpArgs? ``HSMul.hSMul e with
  | some ab => some ab
  | none => getBinaryOpArgs? ``SMul.smul e

private meta def getUnaryOpArg? (opName : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.isEmpty then none else some args[args.size - 1]!

private meta def getNegArg? (e : Expr) : Option Expr :=
  getUnaryOpArg? ``Neg.neg e

private meta def insertSortedBy {α}
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

private meta def getEqSides (target : Expr) : TacticM (Expr × Expr) := do
  let t := target.consumeMData
  if !t.getAppFn.isConstOf ``Eq then
    throwError "normalize_flagsum: goal must be an equality"
  let args := t.getAppArgs
  if args.size != 3 then
    throwError "normalize_flagsum: malformed equality target"
  pure (args[1]!, args[2]!)

private meta def replaceGoalUsingLhsEq
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

private meta def withTimer (label : String) (act : TacticM Unit) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  act
  let t1 ← IO.monoMsNow
  logInfo m!"[timer] {label}: {t1 - t0} ms"

/-! ## 2) Definitions for `sort` and `sort` Implementation -/

private meta def mkOneCoeff : TacticM Expr := do
  Lean.Elab.Term.elabTerm (← `(term| (1 : ℝ))) none

private meta partial def flattenLinearTerms (e : Expr) : TacticM (Array LinTerm) := do
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

private meta def insertSortedByKey
    (item : KeyedTerm)
    (sorted : Array KeyedTerm)
    : Array KeyedTerm :=
  insertSortedBy
    (fun a b => a.idx < b.idx || (a.idx = b.idx && a.key < b.key))
    item
    sorted

private meta def sortLinearTermsByIndex (terms : Array LinTerm) : TacticM (Array LinTerm) := do
  let keyed ← terms.mapM fun (base, coeff) => do
    let (idx, key) ← baseIndexKey base
    pure ({ idx := idx, key := key, base := base, coeff := coeff } : KeyedTerm)
  let mut sorted : Array KeyedTerm := #[]
  for item in keyed do
    sorted := insertSortedByKey item sorted
  pure <| sorted.map fun t => (t.base, t.coeff)

private meta def rebuildLinearExpr (terms : Array LinTerm) : TacticM Expr := do
  let smulTerms ← terms.mapM fun (base, coeff) => mkAppM ``HSMul.hSMul #[coeff, base]
  match smulTerms.toList with
  | [] => throwError "rebuildLinearExpr: empty term list"
  | t :: ts => ts.foldlM (fun acc nxt => mkAppM ``HAdd.hAdd #[acc, nxt]) t

private meta def normalizeLinearExpr (e : Expr) : TacticM Expr := do
  let flat ← flattenLinearTerms e
  let sorted ← sortLinearTermsByIndex flat
  rebuildLinearExpr sorted

private meta def proveEqByAC (lhs rhs : Expr) : TacticM Expr := do
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
private meta def sortNormalizeConv : TacticM Unit :=
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
private meta partial def flattenAddTermsInto (acc : Array Expr) (e : Expr) : Array Expr :=
  let e := e.consumeMData
  match getAddArgs? e with
  | some (a, b) => flattenAddTermsInto (flattenAddTermsInto acc a) b
  | none => acc.push e

private meta def flattenAddTerms (e : Expr) : Array Expr :=
  flattenAddTermsInto #[] e

private meta def addTermKey (e : Expr) : MetaM (Nat × String) := do
  let e := e.consumeMData
  match getSmulArgs? e with
  | some (_, base) => baseIndexKey base
  | none => baseIndexKey e

private meta def sortAddTermsByKey (terms : Array Expr) : MetaM (Array Expr) := do
  let keyed ← terms.mapM fun t => do
    let (idx, key) ← addTermKey t
    pure (idx, key, t)
  let sorted := keyed.qsort (fun a b => a.1 < b.1 || (a.1 = b.1 && a.2.1 < b.2.1))
  pure <| sorted.map fun (_, _, t) => t

private meta partial def mkRightAssocAdd (terms : List Expr) : MetaM Expr := do
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
private meta def getBinaryOpPrefixFn? (opName : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if !fn.isConstOf opName then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then none else some (mkAppN fn (args.extract 0 (args.size - 2)))

private meta def getAddPrefixFn? (e : Expr) : Option Expr :=
  match getBinaryOpPrefixFn? ``HAdd.hAdd e with
  | some fn => some fn
  | none => getBinaryOpPrefixFn? ``Add.add e

private meta partial def mkRightAssocAddFast (prefixFn : Expr) (terms : List Expr) : Expr :=
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
private meta partial def mkLeftAssocAddFast (prefixFn : Expr) (terms : List Expr) : Expr :=
  match terms with
  | [] => panic! "mkLeftAssocAddFast: empty term list"
  | t :: ts => ts.foldl (fun acc t' => mkAppN prefixFn #[acc, t']) t

/-- Rebuild the sorted terms into a right-associated sum. `topE` is the original (pre-sort)
expression, used only to harvest a reusable `+`-instance prefix (see `getAddPrefixFn?`); when
that harvest fails (e.g. `terms` has a single element and `topE` was never an add-application to
begin with) falls back to the slower `mkAppM`-based construction. -/
private meta def rebuildAddExprRightAssoc (topE : Expr) (terms : Array Expr) : MetaM Expr :=
  match getAddPrefixFn? topE with
  | some prefixFn => pure (mkRightAssocAddFast prefixFn terms.toList)
  | none => mkRightAssocAdd terms.toList

private meta def normalizeByAddPermutation (e : Expr) : MetaM Expr := do
  let terms := flattenAddTerms e
  let sorted ← sortAddTermsByKey terms
  rebuildAddExprRightAssoc e sorted

private meta def proveEqByAddAC (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| first | ac_rfl | abel | simp [add_assoc, add_left_comm, add_comm]))
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
term construction; that caused a real regression in `K5turan.lean` (`flag_nonneg`'s
`repeat apply add_nonneg` got stuck on a merged term, likely an instance-path mismatch — see
`FLAGSUMSORT_PERF_PROGRESS.md`). This version instead proves each merge step via a small
tactic-mode goal (`mkMergeStepProof`, the same "synthetic mvar + evalTactic" pattern
`proveEqByAddAC` already uses), so `add_smul`/`add_assoc` go through the ordinary elaborator
instead of being hand-assembled. -/

private meta def mkSmul (coeff base : Expr) : MetaM Expr :=
  mkAppM ``HSMul.hSMul #[coeff, base]

/-- Reconstructs the actual term from a `(coeff, base)` pair: `some c, b ↦ c • b`, but
`none, t ↦ t` *unchanged* — a term that wasn't `smul`-headed to begin with (e.g. a bare negated
flag `-x` left over from something `pre-simp`'s lemma set didn't fully absorb into a coefficient)
must be rebuilt exactly as `t`, not wrapped as `(1 : _) • t`: that wrapper is syntactically
different (even though `one_smul`-defeq) and broke `K3forbidP3.lean`'s proof term downstream —
see `FLAGSUMSORT_PERF_PROGRESS.md`. Terms with `none` therefore also never participate in
merging (`mergeableCoeffs` below always rejects them), since merging would require synthesizing
exactly this kind of coefficient wrapper. -/
private meta def termOf (coeff : Option Expr) (base : Expr) : MetaM Expr :=
  match coeff with
  | some c => mkSmul c base
  | none => pure base

/-- `h : a = b` ↦ proof of `head + a = head + b`. Pure `congrArg` — no typeclass-sensitive lemma
involved, so (unlike `add_smul`/`add_assoc`) there's no suspected reason to route this through
tactic-mode instead of direct term construction. -/
private meta def congrArgAddLeft (prefixFn head h : Expr) : MetaM Expr := do
  let some (ty, _, _) := (← inferType h).eq? | throwError "congrArgAddLeft: expected an Eq proof"
  withLocalDeclD `x ty fun x => do
    let f ← mkLambdaFVars #[x] (mkAppN prefixFn #[head, x])
    mkAppM ``congrArg #[f, h]

/-- Proves `lhs = rhs` via a small, self-contained tactic-mode goal (mirroring `proveEqByAddAC`'s
"synthetic mvar + evalTactic" pattern) instead of assembling the proof by hand from
`add_assoc`/`add_smul` applied directly. Any opaque subterm shared between `lhs` and `rhs` (e.g.
the unmerged "rest" of the sum) is never descended into by `simp`, so this stays `O(1)` regardless
of how large that shared subterm is. -/
private meta def mkMergeStepProof (lhs rhs : Expr) : TacticM Expr := do
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
private meta def mergeableCoeffs (key1 key2 : String) (coeff1 coeff2 : Option Expr) (base1 base2 : Expr) :
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

/-- Walks a sorted `(key, coeff?, base)` list left to right, merging maximal adjacent runs that
share a base (only among entries with an explicit `coeff`). Returns the merged list together with
a proof that the right-associated sum of the input equals the right-associated sum of the merged
list. -/
private meta partial def mergeAdjacentAndProve (prefixFn : Expr) :
    List (String × Option Expr × Expr) → TacticM (List (String × Option Expr × Expr) × Expr)
  | [] => throwError "mergeAdjacentAndProve: empty term list"
  | [(k, oc, b)] => do
      pure ([(k, oc, b)], ← mkEqRefl (← termOf oc b))
  | (k1, oc1, b1) :: (k2, oc2, b2) :: rest => do
      match ← mergeableCoeffs k1 k2 oc1 oc2 b1 b2 with
      | some (c1, c2) => do
          let c12 ← mkAppM ``HAdd.hAdd #[c1, c2]
          let t1 ← mkSmul c1 b1
          let t2 ← mkSmul c2 b1
          let t12 ← mkSmul c12 b1
          match rest with
          | [] => do
              let step ← mkMergeStepProof (← mkAppM ``HAdd.hAdd #[t1, t2]) t12
              pure ([(k1, some c12, b1)], step)
          | _ :: _ => do
              let (mergedRest, eq2) ← mergeAdjacentAndProve prefixFn ((k1, some c12, b1) :: rest)
              let restTerms ← rest.mapM fun (_, oc, b) => termOf oc b
              let restRebuilt := mkRightAssocAddFast prefixFn restTerms
              let lhs ← mkAppM ``HAdd.hAdd #[t1, ← mkAppM ``HAdd.hAdd #[t2, restRebuilt]]
              let rhs ← mkAppM ``HAdd.hAdd #[t12, restRebuilt]
              let bridge ← mkMergeStepProof lhs rhs
              pure (mergedRest, ← mkEqTrans bridge eq2)
      | none => do
          let (mergedRest, restEq) ← mergeAdjacentAndProve prefixFn ((k2, oc2, b2) :: rest)
          let t1 ← termOf oc1 b1
          pure ((k1, oc1, b1) :: mergedRest, ← congrArgAddLeft prefixFn t1 restEq)

/-- Cheap left-to-right scan: is there any *adjacent* same-base pair under the exact
`mergeableCoeffs` predicate `mergeAdjacentAndProve` uses? When this is `false` the sorted focus has
all-distinct bases, so nothing merges and `mergeSameBaseTermsConv` can skip the whole merge walk
(and the `O(n)`-deep `congrArg` identity tower it would build proving `focus = focus`), going
straight to the right→left re-association it has to do anyway. Key mismatches short-circuit before
any `isDefEq`, so this is essentially `O(n)` string comparisons. -/
private meta partial def anyAdjacentMergeable :
    List (String × Option Expr × Expr) → MetaM Bool
  | (k1, oc1, b1) :: (k2, oc2, b2) :: rest => do
      match ← mergeableCoeffs k1 k2 oc1 oc2 b1 b2 with
      | some _ => pure true
      | none => anyAdjacentMergeable ((k2, oc2, b2) :: rest)
  | _ => pure false

/-- `conv`-mode step: after `acSortNormalizeConv` has sorted the current focus by base index,
merge adjacent same-base runs (coefficient consolidation), then re-associate the result to
*left*-associated (`(...(t1+t2)+t3...)+tn`) via `proveEqByAddAC`/`ac_rfl` — already-measured-fast
for pure reassociation, no `simp` search. The left-assoc reshape happens unconditionally (even
with nothing to merge) since downstream consumers like `flag_nonneg`'s
`repeat apply add_nonneg` depend on it (see `mkLeftAssocAddFast`'s docstring). `norm_num` (to fold
the resulting literal coefficient sums) only runs when a merge actually happened. -/
private meta def mergeSameBaseTermsConv : TacticM Unit :=
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
        let hasMergeable ← anyAdjacentMergeable pairs.toList
        if hasMergeable then
          -- At least one adjacent same-base pair to combine: run the full merge walk (unchanged).
          let (merged, mergeProof) ← mergeAdjacentAndProve prefixFn pairs.toList
          let didMerge := merged.length < pairs.size
          let mergedTerms ← merged.mapM fun (_, oc, b) => termOf oc b
          let mergedExprRight := mkRightAssocAddFast prefixFn mergedTerms
          let mergedExprLeft := mkLeftAssocAddFast prefixFn mergedTerms
          let assocProof ← proveEqByAddAC mergedExprRight mergedExprLeft
          let fullProof ← mkEqTrans mergeProof assocProof
          replaceGoalUsingLhsEq goal mergedExprLeft rhs fullProof
          if didMerge then
            evalTactic (← `(tactic| try norm_num))
        else
          -- Nothing to merge: skip `mergeAdjacentAndProve`'s O(n)-deep `congrArg` identity tower.
          -- `merged` would equal `pairs`, so `mergedExprLeft` is built identically; only the
          -- right→left re-association remains (`focus` is already the right-assoc sorted sum),
          -- which `proveEqByAddAC` closes directly. No `norm_num` (no coefficients were combined).
          let mergedTerms ← pairs.toList.mapM fun (_, oc, b) => termOf oc b
          let mergedExprLeft := mkLeftAssocAddFast prefixFn mergedTerms
          let assocProof ← proveEqByAddAC focus mergedExprLeft
          replaceGoalUsingLhsEq goal mergedExprLeft rhs assocProof

/-- Shared implementation: normalizes the current conv focus using add-AC only. -/
private meta def acSortNormalizeConv : TacticM Unit :=
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
  -- Stage-A pre-simp folds subtractions/negations into coefficients and collapses nested `smul`s.
  -- It deliberately does NOT re-associate: `flattenAddTerms` (inside `acSortNormalizeConv`) re-
  -- flattens the `+`-tree regardless of association and `proveEqByAddAC`/`ac_rfl` proves the
  -- permutation up to AC, so an `add_assoc` here is redundant O(n²) work feeding a shape that is
  -- discarded immediately. Without it the remaining rewrites are linear; the high `maxSteps` is
  -- now just defensive headroom (the default would already suffice) — a cap, not a loop.
  evalTactic (← `(tactic|
    (try (simp (config := { maxSteps := 10000000 }) only
      [neg_add, neg_neg, sub_eq_add_neg, ← neg_smul, smul_smul]))))
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
