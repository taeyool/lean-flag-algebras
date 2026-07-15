import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.Forbid.CommonGraphs

/-! # Automation.Basic — core flag-algebra proof automation

This module is the foundation of the Automation layer that sits on top of `Forbid`.
It provides the reusable helper lemmas and custom tactics shared by every
per-problem density-bound proof:

* `forbidExpand_one` / `one_inducedForbidEq_forbidExpand_one` — rewrite the constant
  `1` as the forbid-conditioned sum of unlabeled flags of a given size.
* `inducedForbidLE_trans_add_nonneg`, `flagQuadraticForm_downward_inducedForbidLE_nonneg`,
  `inducedForbidLE_add_QuadraticForm` — combine a known `inducedForbidLE` bound with a
  non-negative PSD quadratic-form (SOS) certificate term.
* Custom tactics `fold_basis_vectors`, `expand_one_at n`, and `flag_nonneg`
  (defined via `elab`/`syntax`/`macro`), automating the boilerplate that is
  otherwise identical across all flag-algebra Automation-layer proofs.
-/

open FlagAlgebras Forbid
open SimpleGraph Matrix
open Lean Elab Command Tactic

namespace FlagAlgebras.Automation

/-- The constant `1`, re-expressed under the forbidden subgraph `F_forbid` as
the conditioned sum over unlabeled flags of size `expandSize` whose density
within `F_forbid` is `0`, each weighted by its empty-type density. -/
noncomputable def forbidExpand_one
    (F_forbid : FinFlag ∅ₜ) (expandSize : ℕ)
    : FlagAlgebra ∅ₜ :=
  ∑ F' : FlagWithSize ∅ₜ expandSize with flagDensity₁ F_forbid.2 (unlabel F') = 0,
    (flagDensity₁ ((⟨0, default⟩ : FinFlag ∅ₜ).2) F' : ℝ) • ⟦basisVector ⟨expandSize, F'⟩⟧

/-- Under `F_forbid`, the constant `1` equals its `forbidExpand_one` expansion;
this is the rewrite used to turn the target bound into a sum over explicit
4- or 5-vertex flags. -/
theorem one_inducedForbidEq_forbidExpand_one
    (F_forbid : FinFlag ∅ₜ) (expandSize : ℕ)
    : (1 : FlagAlgebra ∅ₜ) =ᵢ[F_forbid] forbidExpand_one F_forbid expandSize := by
  simpa [forbidExpand_one] using
    (basisVector_quot_inducedForbidEq_sum (σ := ∅ₜ) F_forbid (⟨0, default⟩ : FinFlag ∅ₜ) expandSize (by simp))

/-- Ordinary `H`-free unit expansion (`_ofMem` form): under `forbiddenCondition H`, `1` equals
its `forbidExpand_one` expansion, given the forbid flag is `H`-forbidden (`hmem`). -/
theorem one_forbidEq_forbidExpand_one_ofMem
    {N : ℕ} {H : SimpleGraph (Fin N)} (Fforbid : FinFlag ∅ₜ)
    (hmem : Fforbid ∈ forbiddenFlags H) (expandSize : ℕ)
    : (1 : FlagAlgebra ∅ₜ) =[H] forbidExpand_one Fforbid expandSize := by
  simpa [forbidExpand_one] using
    (basisVector_quot_forbidEq_sum_ofMem (σ := ∅ₜ) Fforbid hmem (⟨0, default⟩ : FinFlag ∅ₜ) expandSize (by simp))

open FlagAlgebras.Compute in
/-- **Subgraph** unit expansion. `1` re-expressed under subgraph-`H`-freeness as the conditioned sum
over the subgraph-`H`-free unlabeled flags (filter `∀ D ∈ supergraphFamily H, …`), matching the
subgraph generator's `flagSetHfree_…_eq`. -/
noncomputable def forbidExpand_one_subgraph {m : ℕ} (H : Sym2Graph m) (expandSize : ℕ)
    : FlagAlgebra ∅ₜ :=
  ∑ F' : FlagWithSize ∅ₜ expandSize with
      (∀ D ∈ supergraphFamily H, flagDensity₁ D.2 (unlabel F') = 0),
    (flagDensity₁ ((⟨0, default⟩ : FinFlag ∅ₜ).2) F' : ℝ) • ⟦basisVector ⟨expandSize, F'⟩⟧

open FlagAlgebras.Compute in
/-- Under subgraph-`H`-freeness, `1` equals its `forbidExpand_one_subgraph` expansion — the subgraph
analogue of `one_forbidEq_forbidExpand_one_ofMem` (membership discharged by the capstone). -/
theorem one_forbidEq_forbidExpand_one_subgraph {m : ℕ} (H : Sym2Graph m) (expandSize : ℕ)
    : (1 : FlagAlgebra ∅ₜ) =[H.toLabeledGraph.graph] forbidExpand_one_subgraph H expandSize := by
  simpa [forbidExpand_one_subgraph] using
    (basisVector_quot_forbidEq_sum_subgraph H (⟨0, default⟩ : FinFlag ∅ₜ) expandSize (by simp))

/-- If `f ≤ᵢ[F] g` and `c` is non-negative under `F`, then `f ≤ᵢ[F] g + c`. -/
lemma inducedForbidLE_trans_add_nonneg
    {F_forbid : FinFlag ∅ₜ} {f g c : FlagAlgebra ∅ₜ}
    (hfg : f ≤ᵢ[F_forbid] g) (hc : 0 ≤ᵢ[F_forbid] c)
    : f ≤ᵢ[F_forbid] (g + c) := by
  rw [← add_zero f]
  exact inducedForbidLE_add hfg hc

/-- The downward projection of a PSD quadratic form in flag vectors is
non-negative under any forbidden subgraph `F_forbid`; this is the basic SOS
(sum-of-squares) certificate term. -/
theorem flagQuadraticForm_downward_inducedForbidLE_nonneg
    {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    (F_forbid : FinFlag ∅ₜ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : 0 ≤ᵢ[F_forbid] ⟦flagQuadraticForm M v⟧₀
  := by
  apply downward_inducedForbidLE_nonneg
  apply inducedForbidLE_of_le
  exact flagQuadraticForm_nonneg M hM v

/-- Adding a PSD quadratic-form (SOS) term to the right-hand side preserves a
`inducedForbidLE` bound: from `f ≤ᵢ[F] g` derive `f ≤ᵢ[F] g + ⟦flagQuadraticForm M v⟧₀`.
This is the workhorse for stacking SDP certificate terms. -/
theorem inducedForbidLE_add_QuadraticForm
    {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : (f ≤ᵢ[F_forbid] g) → f ≤ᵢ[F_forbid] g + ⟦flagQuadraticForm M v⟧₀
  := by
  intro hfg
  rw [← add_zero f]
  apply inducedForbidLE_add hfg
  apply downward_inducedForbidLE_nonneg
  apply inducedForbidLE_of_le
  exact flagQuadraticForm_nonneg M hM v

/-- Condition-generic SOS stacker: adding a PSD quadratic-form term preserves a `forbidLEWith C`
bound. Ordinary examples use `C := forbiddenCondition (completeGraph r)`. -/
theorem forbidLEWith_add_QuadraticForm
    {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {C : ForbidCondition} {f g : FlagAlgebra ∅ₜ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : (forbidLEWith C f g) → forbidLEWith C f (g + ⟦flagQuadraticForm M v⟧₀)
  := by
  intro hfg
  rw [← add_zero f]
  apply forbidLEWith_add hfg
  apply downward_forbidLEWith_nonneg
  apply forbidLEWith_of_le
  exact flagQuadraticForm_nonneg M hM v

/-
`fold_basis_vectors` scans the current goal for subexpressions of the form
`⟦basisVector ⟨n, Flag_n_k_m_i⟩⟧` and folds each occurrence into the
corresponding `FlagAlgebra_n_k_m_i` constant.  No arguments needed.
-/

/-- Recursively collect the names of all `Flag_*` constants occurring in `e`
(helper for `fold_basis_vectors`). -/
private partial def collectFlagConstNamesInExpr (e : Expr) : Array Name :=
  let e := e.consumeMData
  let fromChildren : Array Name := match e with
    | .app f a => collectFlagConstNamesInExpr f ++ collectFlagConstNamesInExpr a
    | .lam _ t b _ => collectFlagConstNamesInExpr t ++ collectFlagConstNamesInExpr b
    | .forallE _ t b _ => collectFlagConstNamesInExpr t ++ collectFlagConstNamesInExpr b
    | .letE _ t v b _ =>
        collectFlagConstNamesInExpr t ++ collectFlagConstNamesInExpr v ++
        collectFlagConstNamesInExpr b
    | _ => #[]
  match e with
  | .const nm _ =>
    if (match nm with | .str _ s => s.startsWith "Flag_" | _ => false) then
      fromChildren.push nm
    else fromChildren
  | _ => fromChildren

/-- Map a `Flag_<suffix>` constant name to the matching `FlagAlgebra_<suffix>`. -/
private def flagConstToAlgebraName (nm : Name) : Option Name :=
  match nm with
  | .str parent s =>
    if s.startsWith "Flag_" then some (.str parent ("FlagAlgebra_" ++ s.drop 5))
    else none
  | _ => none

/-- Inverse of `flagConstToAlgebraName`: map `FlagAlgebra_<suffix>` back to
`Flag_<suffix>`. -/
private def algebraNameToFlagConstName (nm : Name) : Option Name :=
  match nm with
  | .str parent s =>
    if s.startsWith "FlagAlgebra_" then some (.str parent ("Flag_" ++ s.drop 12))
    else none
  | _ => none

elab "fold_basis_vectors" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let flagNames := collectFlagConstNamesInExpr target
    let env ← getEnv
    let algebraNames : Array Name :=
      (flagNames.filterMap flagConstToAlgebraName)
      |>.foldl (fun acc nm => if acc.contains nm then acc else acc.push nm) #[]
      |>.filter (fun nm => env.contains nm)
    if algebraNames.isEmpty then return
    let rw_rules ← algebraNames.mapM fun algNm => do
      let some flagNm := algebraNameToFlagConstName algNm
        | throwError s!"Could not infer flag constant name from {algNm}"
      let algId := mkIdent algNm
      let flagId := mkIdent flagNm
      `(Lean.Parser.Tactic.rwRule| ← (show $algId:term = ⟦basisVector ⟨_, $flagId:term⟩⟧ by rfl))
    evalTactic (← `(tactic| rw [$rw_rules,*]))

/--
`expand_one_at n` unfolds `forbidExpand_one` for a graph of size `n` and reduces
the resulting Finset sum to a sum over the explicit list of unlabeled flags.

This automates the boilerplate step that appears identically in every flag algebra
Automation-layer proof, varying only in `n`:

  dsimp only [forbidExpand_one]
  rw [Finset.sum_eq_multiset_sum]
  rw [← flagSet_n_0_0_eq_univ]
  simp [flagSet_n_0_0_val_eq, unlabel_emptyType]
  simp [default, flagDensity_empty]
-/
syntax "expand_one_at" num : tactic

elab_rules : tactic
  | `(tactic| expand_one_at $n:num) => do
      let nVal := n.getNat
      let eq_univ_id : TSyntax `term := mkIdent (Name.mkSimple s!"flagSet_{nVal}_0_0_eq_univ")
      let val_eq_id  : TSyntax `term := mkIdent (Name.mkSimple s!"flagSet_{nVal}_0_0_val_eq")
      let eq_univ_rw  ← `(Lean.Parser.Tactic.rwRule| ← $eq_univ_id:term)
      let val_eq_simp ← `(Lean.Parser.Tactic.simpLemma| $val_eq_id:term)
      evalTactic (← `(tactic| dsimp only [forbidExpand_one]))
      evalTactic (← `(tactic| rw [Finset.sum_eq_multiset_sum]))
      evalTactic (← `(tactic| rw [$eq_univ_rw]))
      evalTactic (← `(tactic| simp [$val_eq_simp, unlabel_emptyType]))
      evalTactic (← `(tactic| simp [default, flagDensity_empty]))
      evalTactic (← `(tactic| fold_basis_vectors))

/--
`expand_one_hfree_at n F` is the forbid-free analogue of `expand_one_at n`.
It unfolds `forbidExpand_one` for a graph of size `n` and reduces the resulting
`Finset` sum directly onto the explicitly-generated `F`-free flag set
`flagSetHfree_n_0_0_<F>` (via its filtered-completeness lemma `…_eq` and
`…_val_eq`), instead of materializing the full `flagSet` and dropping forbidden
terms. The tactic is forbid-agnostic (the forbidden flag is read from the goal's
`forbidExpand_one`); `F` is only used to name the `flagSetHfree_*` lemmas, so it is
the same identifier (a `Sym2Graph` term, e.g. `K3`) passed to
`generate_forbid_free_empty_typed_flags n F`. Prerequisite: run that command first.
-/
syntax "expand_one_hfree_at" num ident : tactic

elab_rules : tactic
  | `(tactic| expand_one_hfree_at $n:num $forbid:ident) => do
      let nVal := n.getNat
      -- Strip any namespace qualifier so the tag matches the generated `flagSetHfree_*` names.
      let tagFull := forbid.getId.toString
      let tag := (tagFull.splitOn ".").getLastD tagFull
      let setName : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_0_0_{tag}")
      let eq_id   : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_0_0_{tag}_eq")
      let val_eq_id : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_0_0_{tag}_val_eq")
      evalTactic (← `(tactic| dsimp only [forbidExpand_one]))
      evalTactic (← `(tactic|
        rw [Finset.sum_congr (s₂ := $setName) (by rw [$eq_id:term]; try congr 1) (fun _ _ => rfl)]))
      evalTactic (← `(tactic| simp only [Finset.sum_eq_multiset_sum, $val_eq_id:term]))
      evalTactic (← `(tactic| simp [unlabel_emptyType]))
      evalTactic (← `(tactic| simp [default, flagDensity_empty]))
      evalTactic (← `(tactic| fold_basis_vectors))

/--
`expand_one_hfree_at_subgraph n F` is the **subgraph**-forbidding analogue of `expand_one_hfree_at`:
it unfolds `forbidExpand_one_subgraph` (the family-filter unit expansion) and reduces it onto the
subgraph-`F`-free flag set `flagSetHfree_n_0_0_<F>` (via its `…_eq` / `…_val_eq`). Same name reuse as
`expand_one_hfree_at`; only the unfolded definition differs. Prerequisite:
`generate_subgraph_free_empty_typed_flags n F`.
-/
syntax "expand_one_hfree_at_subgraph" num ident : tactic

elab_rules : tactic
  | `(tactic| expand_one_hfree_at_subgraph $n:num $forbid:ident) => do
      let nVal := n.getNat
      let tagFull := forbid.getId.toString
      let tag := (tagFull.splitOn ".").getLastD tagFull
      let setName : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_0_0_{tag}")
      let eq_id   : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_0_0_{tag}_eq")
      let val_eq_id : TSyntax `term := mkIdent (Name.mkSimple s!"flagSetHfree_{nVal}_0_0_{tag}_val_eq")
      evalTactic (← `(tactic| dsimp only [forbidExpand_one_subgraph]))
      evalTactic (← `(tactic|
        rw [Finset.sum_congr (s₂ := $setName) (by rw [$eq_id:term]; try congr 1) (fun _ _ => rfl)]))
      evalTactic (← `(tactic| simp only [Finset.sum_eq_multiset_sum, $val_eq_id:term]))
      evalTactic (← `(tactic| simp [unlabel_emptyType]))
      evalTactic (← `(tactic| simp [default, flagDensity_empty]))
      evalTactic (← `(tactic| fold_basis_vectors))

/--
`flag_nonneg` closes goals of the form `f ≤ᵢ[F_forbid] g` when `g - f` is a
non-negative linear combination of FlagAlgebra unit vectors (of the form `c • ⟦basisVector F⟧`).

It automates the standard closing step in flag algebra Automation-layer proofs:
1. Reduces to a semantic inequality via `inducedForbidLE_of_le`
2. Distributes `φ` over `+` using `PositiveHom.map_add`
3. Decomposes the sum into individual non-negativity goals using `add_nonneg`
4. Closes each leaf with `positiveHom_basisVector_ge_zero`
-/
macro "flag_nonneg" : tactic =>
  `(tactic| (
    intro φ
    try simp only [sub_zero, PositiveHom.map_add, ge_iff_le]
    repeat apply add_nonneg
    all_goals (
      try simp only [PositiveHom.map_smul, Nat.ofNat_pos, div_pos_iff_of_pos_left,
                 mul_nonneg_iff_of_pos_left, one_div, inv_pos]
      apply positiveHom_basisVector_ge_zero
    )
  ))

end FlagAlgebras.Automation
