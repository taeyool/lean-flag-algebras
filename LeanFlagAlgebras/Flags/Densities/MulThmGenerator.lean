import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Forbid.Basic
import Mathlib.Tactic

/-! # Flag multiplication theorem generators

This module provides two elaboration-time commands that synthesize flag-product
("multiplication") theorems for a fixed flag type, expanding the product of two
pattern flags into the basis of larger host flags:

* `generate_forbid_mul_theorems patN hostN k m Forbid` — products modulo a
  forbidden subgraph (right-hand side holds up to `=ᵢ[Forbid.toFinFlag]`).
* `generate_mul_theorems patN hostN k m` — plain products (`=`), no forbid.

See each command's documentation below for the meaning of the parameters and
example invocations. Both obtain their expansion coefficients from the density
computation in `DensityThmGenerator.lean`, and rely on the `FlagAlgebra_*` /
`flagSet_*` constants produced by `generate_flags` (`FlagDef.lean`).
-/

open Lean Elab Command
open FlagAlgebras Forbid
open FlagAlgebras.Compute

namespace Flags.Densities

/-- Build a real-number coefficient term from a `(num, den)` pair. -/
def coeffToTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
  if den = 1 then
    `((($(Quote.quote num) : Nat) : ℝ))
  else
    `((($(Quote.quote num) : ℝ) / ($(Quote.quote den) : ℝ)))

/-- Build the term `coeff • flagName`, one summand of the multiplication RHS. -/
def coeffSmulFlagTerm (num den : Nat) (flagName : Name) : CommandElabM (TSyntax `term) := do
  let coeffTerm <- coeffToTerm num den
  let flagIdent := mkIdent flagName
  `($coeffTerm • $flagIdent)

/-- Left-fold a list of summands into `t₀ + t₁ + …`, or `0` when empty. -/
def sumTerms (flagTypeName : Name) (terms : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let flagTypeIdent := mkIdent flagTypeName
  match terms.toList with
  | [] =>
      `((0 : FlagAlgebra $flagTypeIdent))
  | t :: ts =>
      ts.foldlM (fun acc nxt => `($acc + $nxt)) t

/-- The right-hand side of a multiplication theorem:
`Σ_{h : density ≠ 0} cₕ • FlagAlgebra_hostTag_h`, summed in increasing host-index
order, where `cₕ` is the subflag-multiplication density
`p(pattern iOrd, pattern jOrd; host h)` from `densityPF1F2GivenG`. Shared by both
commands below. -/
def buildMulRhs (patN hostN : Nat) (hostTag : String) (patternFlagTypeName : Name)
    (patterns hosts : List (Nat × List (Nat × Nat) × List Nat × Nat × Nat))
    (hostFree : List Nat) (iOrd jOrd : Nat) : CommandElabM (TSyntax `term) := do
  let f1 := patterns.getD iOrd (0, [], [], 0, 0)
  let f2 := patterns.getD jOrd (0, [], [], 0, 0)
  let mut rhsTerms : Array (TSyntax `term) := #[]
  for h in hostFree do
    let g := hosts.getD h (0, [], [], 0, 0)
    let nd := densityPF1F2GivenG hostN g.2.1 g.2.2.1 patN f1.2.1 f1.2.2.1 patN f2.2.1 f2.2.2.1
    if nd.1 != 0 then
      let hostName := Name.mkSimple s!"FlagAlgebra_{hostTag}_{h}"
      if !(← isDeclaredInScope hostName) then throwError s!"Missing definition: {hostName}"
      rhsTerms := rhsTerms.push (← coeffSmulFlagTerm nd.1 nd.2 hostName)
  sumTerms patternFlagTypeName rhsTerms

-- `generate_forbid_mul_theorems patN hostN k m Forbid`
--
-- Generate the flag-product expansion theorems for a σ-typed flag algebra,
-- modulo a forbidden subgraph. Parameters:
--   • `patN`   : size (number of vertices) of the two factor "pattern" flags.
--   • `hostN`  : size of the "host" flags the product expands into; for a product
--                of two `patN`-vertex flags sharing `k` type vertices this is
--                `hostN = 2 * patN - k`.
--   • `k`, `m` : select the flag type σ = `FlagType_k_m` — σ is the `m`-th
--                `k`-vertex graph, and `k` is the number of labeled (type)
--                vertices shared by every flag.
--   • `Forbid` : a forbidden graph — any `def Forbid` in `CommonGraphs.lean`
--                with a companion `Forbid_toFinFlag_eq` lemma (e.g. `K3`, `K4`,
--                `K5`). Only `Forbid`-free pattern and host flags take part.
--
-- For each ordered pair `(i, j)` of `Forbid`-free pattern flags it emits
--   `flagMul_FlagAlgebra_patN_k_m_i_FlagAlgebra_patN_k_m_j :`
--   `  FlagAlgebra_patN_k_m_i * FlagAlgebra_patN_k_m_j`
--   `    =ᵢ[Forbid.toFinFlag] Σ_h cₕ • FlagAlgebra_hostN_k_m_h`,
-- where `=ᵢ[Forbid.toFinFlag]` is equality in the flag algebra up to the forbidden
-- subgraph, the sum ranges over `Forbid`-free hosts `h`, and `cₕ` is the
-- subflag-multiplication density of the two patterns inside host `h`.
--
-- Prerequisites: run `generate_flags patN k m` and `generate_flags hostN k m`
-- first (so the `FlagAlgebra_*` and `flagSet_…` constants exist), and have
-- `Forbid` / `Forbid_toFinFlag_eq` in scope.
--
-- Example — K₄-free products of 3-vertex flags of type `FlagType_2_0`, expanded
-- over 4-vertex hosts:
--   `generate_forbid_mul_theorems 3 4 2 0 K4`
elab "generate_forbid_mul_theorems" patS:num hostS:num kS:num mS:num forbidS:ident : command => do
  let k := kS.getNat
  let m := mS.getNat
  let patN := patS.getNat
  let hostN := hostS.getNat
  let patternTag := s!"{patN}_{k}_{m}"
  let hostTag := s!"{hostN}_{k}_{m}"
  let patternFlagTypeName := Name.mkSimple s!"FlagType_{k}_{m}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let (gIdent, gEqName) ← resolveForbidGraph forbidS.getId.toString
  let forbidFlag ← forbidFlagIdentOfToFinFlagEq gEqName
  let (r, idx) ← parseFlagRIdx forbidFlag.getId.toString
  let forbidAll ← evalCanonicalEdgeLists r
  let forbid := some (r, forbidAll.getD idx [])

  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patternFree := freeFlagIndices patN forbid patterns
  let hostFree := freeFlagIndices hostN forbid hosts
  let flagSetEqUniv := mkIdent (Name.mkSimple s!"flagSet_{hostTag}_eq_univ")
  let flagSetValEq := mkIdent (Name.mkSimple s!"flagSet_{hostTag}_val_eq")

  let mut generated : Nat := 0
  for i in patternFree do
    for j in patternFree do
      let iOrd := if i ≤ j then i else j
      let jOrd := if i ≤ j then j else i
      let rhs ← buildMulRhs patN hostN hostTag patternFlagTypeName patterns hosts hostFree iOrd jOrd
      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{j}")
      let flagOrd1 := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{iOrd}")
      let flagOrd2 := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{jOrd}")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{patternTag}_{i}_FlagAlgebra_{patternTag}_{j}")

      if !(← isDeclaredInScope lhs1.getId) then throwError s!"Missing definition: {lhs1.getId}"
      if !(← isDeclaredInScope lhs2.getId) then throwError s!"Missing definition: {lhs2.getId}"
      if !(← isDeclaredInScope flagOrd1.getId) then throwError s!"Missing definition: {flagOrd1.getId}"
      if !(← isDeclaredInScope flagOrd2.getId) then throwError s!"Missing definition: {flagOrd2.getId}"

      if !(← isDeclaredInScope thmName.getId) then
        if i ≤ j then
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =ᵢ[($gIdent).toFinFlag] $rhs
              := by
              apply inducedForbidEq_trans
                (basisVector_quot_mul_inducedForbidEq_sum ($gIdent).toFinFlag
                  ⟨$(Quote.quote patN), $flagOrd1⟩
                  ⟨$(Quote.quote patN), $flagOrd2⟩
                  $(Quote.quote hostN)
                  (by rfl))
              rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
              have hsetval := $flagSetValEq
              simp [hsetval]
              exact inducedForbidEq_refl ($gIdent).toFinFlag _
          ))
        else
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =ᵢ[($gIdent).toFinFlag] $rhs
              := by
              rw [mul_comm]
              apply inducedForbidEq_trans
                (basisVector_quot_mul_inducedForbidEq_sum ($gIdent).toFinFlag
                  ⟨$(Quote.quote patN), $flagOrd1⟩
                  ⟨$(Quote.quote patN), $flagOrd2⟩
                  $(Quote.quote hostN)
                  (by rfl))
              rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
              have hsetval := $flagSetValEq
              simp [hsetval]
              exact inducedForbidEq_refl ($gIdent).toFinFlag _
          ))
        generated := generated + 1

  logInfo s!"Generated {generated} {forbidS.getId.toString}-free multiplication theorem(s): pattern {patternTag}"

-- `generate_forbid_free_mul_theorems patN hostN k m F`
--
-- The **edge-based** analogue of `generate_forbid_free_mul_theorems`: `F` is a `Sym2Graph mF`
-- *term* (no tag, no canonical forbidden flag). The forbid flag in the emitted
-- `=ᵢ[Sym2EmptyTypedFlag.toFlag ⟦F⟧]` theorems is `⟦F⟧` directly; the forbid-free pattern/host split
-- is **induced** (`evalInducedFreeMask`); and the proof rewrites the
-- `basisVector_quot_mul_inducedForbidEq_sum (toFlag ⟦F⟧)` expansion onto the edge-based forbid-free host set
-- `flagSetHfree_hostN_k_m_<F>` via its `…_eq` / `…_val_eq` lemmas (emitted by the edge-based
-- generators). Prerequisite: run `generate_forbid_free_empty_typed_flags hostN F`
-- (and, for `k > 0`, `generate_forbid_free_flags hostN k m F`) first.
elab "generate_forbid_free_mul_theorems" patS:num hostS:num kS:num mS:num fStx:ident
    HgStx:term:max hmemStx:term:max : command => do
  let k := kS.getNat
  let m := mS.getNat
  let patN := patS.getNat
  let hostN := hostS.getNat
  let tagFull := toString fStx.getId
  let tag := (tagFull.splitOn ".").getLastD tagFull
  let patternTag := s!"{patN}_{k}_{m}"
  let hostTag := s!"{hostN}_{k}_{m}"
  let patternFlagTypeName := Name.mkSimple s!"FlagType_{k}_{m}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patMask ← evalInducedFreeMask patN fStx
  let hostMask ← evalInducedFreeMask hostN fStx
  let patternFree := inducedFreeFlagIndices patMask patterns
  let hostFree := inducedFreeFlagIndices hostMask hosts

  -- The forbid flag is the `FinFlag` of the term `⟦F⟧` (no canonical flag). Its `.2` is
  -- `Sym2EmptyTypedFlag.toFlag ⟦F⟧`, matching the edge-based generator's `flagSetHfree_…_eq`.
  let forbidFlagTm ← `((⟨_, FlagAlgebras.Compute.Sym2EmptyTypedFlag.toFlag ⟦$fStx⟧⟩
      : FlagAlgebras.FinFlag ∅ₜ))

  let flagSetHfreeName := mkIdent (Name.mkSimple s!"flagSetHfree_{hostTag}_{tag}")
  let flagSetHfreeEq := mkIdent (Name.mkSimple s!"flagSetHfree_{hostTag}_{tag}_eq")
  let flagSetHfreeValEq := mkIdent (Name.mkSimple s!"flagSetHfree_{hostTag}_{tag}_val_eq")
  let ns ← getCurrNamespace
  unless ((← getEnv).contains (ns ++ flagSetHfreeEq.getId) || (← getEnv).contains flagSetHfreeEq.getId) do
    throwError s!"`generate_forbid_free_mul_theorems {patN} {hostN} {k} {m} {tag}` requires the \
edge-based forbid-free host set `flagSetHfree_{hostTag}_{tag}`. Run \
`generate_forbid_free_empty_typed_flags {hostN} {tag}`{if k > 0 then s!" and `generate_forbid_free_flags {hostN} {k} {m} {tag}`" else ""} first."

  -- Host `FlagAlgebra_*` idents, to unfold the folded RHS to `⟦basisVector⟧` form in the
  -- proof finish (so `abel` can reconcile it with the right-associated, unfolded LHS sum).
  let hostIdents : Array (TSyntax `ident) :=
    (hostFree.map (fun h => mkIdent (Name.mkSimple s!"FlagAlgebra_{hostTag}_{h}"))).toArray
  let mut generated : Nat := 0
  for i in patternFree do
    for j in patternFree do
      let iOrd := if i ≤ j then i else j
      let jOrd := if i ≤ j then j else i
      let rhs ← buildMulRhs patN hostN hostTag patternFlagTypeName patterns hosts hostFree iOrd jOrd
      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{j}")
      let flagOrd1 := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{iOrd}")
      let flagOrd2 := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{jOrd}")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{patternTag}_{i}_FlagAlgebra_{patternTag}_{j}")

      if !(← isDeclaredInScope lhs1.getId) then throwError s!"Missing definition: {lhs1.getId}"
      if !(← isDeclaredInScope lhs2.getId) then throwError s!"Missing definition: {lhs2.getId}"
      if !(← isDeclaredInScope flagOrd1.getId) then throwError s!"Missing definition: {flagOrd1.getId}"
      if !(← isDeclaredInScope flagOrd2.getId) then throwError s!"Missing definition: {flagOrd2.getId}"

      if !(← isDeclaredInScope thmName.getId) then
        if i ≤ j then
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[$HgStx] $rhs
              := by
              apply forbidEqWith_trans
                (basisVector_quot_mul_forbidEq_sum_ofMem $forbidFlagTm
                  $hmemStx
                  ⟨$(Quote.quote patN), $flagOrd1⟩
                  ⟨$(Quote.quote patN), $flagOrd2⟩
                  $(Quote.quote hostN)
                  (by rfl))
              rw [Finset.sum_congr (s₂ := $flagSetHfreeName)
                    (by rw [$flagSetHfreeEq:ident]; try congr 1) (fun _ _ => rfl)]
              simp only [Finset.sum_eq_multiset_sum, $flagSetHfreeValEq:ident]
              simp
              all_goals (try (refine forbidEqWith_of_eq ?_))
              all_goals (try dsimp only [$[$hostIdents:ident],*])
              all_goals (try abel)
              all_goals (try rfl)
          ))
        else
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[$HgStx] $rhs
              := by
              rw [mul_comm]
              apply forbidEqWith_trans
                (basisVector_quot_mul_forbidEq_sum_ofMem $forbidFlagTm
                  $hmemStx
                  ⟨$(Quote.quote patN), $flagOrd1⟩
                  ⟨$(Quote.quote patN), $flagOrd2⟩
                  $(Quote.quote hostN)
                  (by rfl))
              rw [Finset.sum_congr (s₂ := $flagSetHfreeName)
                    (by rw [$flagSetHfreeEq:ident]; try congr 1) (fun _ _ => rfl)]
              simp only [Finset.sum_eq_multiset_sum, $flagSetHfreeValEq:ident]
              simp
              refine forbidEqWith_of_eq ?_
              try dsimp only [$[$hostIdents:ident],*]
              abel
          ))
        generated := generated + 1

  logInfo s!"Generated {generated} {tag}-free (edge-based, forbid-free-host) multiplication theorem(s): pattern {patternTag}"

/-- `generate_subgraph_free_mul_theorems patN hostN k m F`: the **subgraph**-forbidding analogue of
`generate_forbid_free_mul_theorems`. The emitted `… =[F.toLabeledGraph.graph] …` theorems use
the subgraph capstone `basisVector_quot_mul_forbidEq_sum_subgraph` (no canonical forbidden flag / `hmem`
needed — the capstone derives the membership from `supergraphFamily`), the subgraph free split
(`evalSubgraphFreeMask`), and rewrite onto the subgraph-`F`-free host set
`flagSetHfree_hostN_k_m_<F>` whose `…_eq` filter matches the capstone's exactly. Prerequisite: run
`generate_subgraph_free_empty_typed_flags hostN F` (and, for `k > 0`,
`generate_subgraph_free_flags hostN k m F`) first. -/
elab "generate_subgraph_free_mul_theorems" patS:num hostS:num kS:num mS:num fStx:ident : command => do
  let k := kS.getNat
  let m := mS.getNat
  let patN := patS.getNat
  let hostN := hostS.getNat
  let tagFull := toString fStx.getId
  let tag := (tagFull.splitOn ".").getLastD tagFull
  let patternTag := s!"{patN}_{k}_{m}"
  let hostTag := s!"{hostN}_{k}_{m}"
  let patternFlagTypeName := Name.mkSimple s!"FlagType_{k}_{m}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patMask ← evalSubgraphFreeMask patN fStx
  let hostMask ← evalSubgraphFreeMask hostN fStx
  let patternFree := inducedFreeFlagIndices patMask patterns
  let hostFree := inducedFreeFlagIndices hostMask hosts

  let flagSetHfreeName := mkIdent (Name.mkSimple s!"flagSetHfree_{hostTag}_{tag}")
  let flagSetHfreeEq := mkIdent (Name.mkSimple s!"flagSetHfree_{hostTag}_{tag}_eq")
  let flagSetHfreeValEq := mkIdent (Name.mkSimple s!"flagSetHfree_{hostTag}_{tag}_val_eq")
  let ns ← getCurrNamespace
  unless ((← getEnv).contains (ns ++ flagSetHfreeEq.getId) || (← getEnv).contains flagSetHfreeEq.getId) do
    throwError s!"`generate_subgraph_free_mul_theorems {patN} {hostN} {k} {m} {tag}` requires the \
subgraph-free host set `flagSetHfree_{hostTag}_{tag}`. Run \
`generate_subgraph_free_empty_typed_flags {hostN} {tag}`{if k > 0 then s!" and `generate_subgraph_free_flags {hostN} {k} {m} {tag}`" else ""} first."

  let hostIdents : Array (TSyntax `ident) :=
    (hostFree.map (fun h => mkIdent (Name.mkSimple s!"FlagAlgebra_{hostTag}_{h}"))).toArray
  let mut generated : Nat := 0
  for i in patternFree do
    for j in patternFree do
      let iOrd := if i ≤ j then i else j
      let jOrd := if i ≤ j then j else i
      let rhs ← buildMulRhs patN hostN hostTag patternFlagTypeName patterns hosts hostFree iOrd jOrd
      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{j}")
      let flagOrd1 := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{iOrd}")
      let flagOrd2 := mkIdent (Name.mkSimple s!"Flag_{patternTag}_{jOrd}")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{patternTag}_{i}_FlagAlgebra_{patternTag}_{j}")

      if !(← isDeclaredInScope lhs1.getId) then throwError s!"Missing definition: {lhs1.getId}"
      if !(← isDeclaredInScope lhs2.getId) then throwError s!"Missing definition: {lhs2.getId}"
      if !(← isDeclaredInScope flagOrd1.getId) then throwError s!"Missing definition: {flagOrd1.getId}"
      if !(← isDeclaredInScope flagOrd2.getId) then throwError s!"Missing definition: {flagOrd2.getId}"

      if !(← isDeclaredInScope thmName.getId) then
        if i ≤ j then
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[($fStx).toLabeledGraph.graph] $rhs
              := by
              apply forbidEqWith_trans
                (basisVector_quot_mul_forbidEq_sum_subgraph $fStx
                  ⟨$(Quote.quote patN), $flagOrd1⟩
                  ⟨$(Quote.quote patN), $flagOrd2⟩
                  $(Quote.quote hostN)
                  (by rfl))
              rw [Finset.sum_congr (s₂ := $flagSetHfreeName)
                    (by rw [$flagSetHfreeEq:ident]; try congr 1) (fun _ _ => rfl)]
              simp only [Finset.sum_eq_multiset_sum, $flagSetHfreeValEq:ident]
              simp
              all_goals (try (refine forbidEqWith_of_eq ?_))
              all_goals (try dsimp only [$[$hostIdents:ident],*])
              all_goals (try abel)
              all_goals (try rfl)
          ))
        else
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) =[($fStx).toLabeledGraph.graph] $rhs
              := by
              rw [mul_comm]
              apply forbidEqWith_trans
                (basisVector_quot_mul_forbidEq_sum_subgraph $fStx
                  ⟨$(Quote.quote patN), $flagOrd1⟩
                  ⟨$(Quote.quote patN), $flagOrd2⟩
                  $(Quote.quote hostN)
                  (by rfl))
              rw [Finset.sum_congr (s₂ := $flagSetHfreeName)
                    (by rw [$flagSetHfreeEq:ident]; try congr 1) (fun _ _ => rfl)]
              simp only [Finset.sum_eq_multiset_sum, $flagSetHfreeValEq:ident]
              simp
              all_goals (try (refine forbidEqWith_of_eq ?_))
              all_goals (try dsimp only [$[$hostIdents:ident],*])
              all_goals (try abel)
              all_goals (try rfl)
          ))
        generated := generated + 1

  logInfo s!"Generated {generated} subgraph-{tag}-free (forbid-free-host) multiplication theorem(s): pattern {patternTag}"

-- `generate_mul_theorems patN hostN k m`
--
-- The no-forbidden-subgraph analogue of `generate_forbid_mul_theorems`: the same
-- `patN`, `hostN`, `k`, `m` parameters but no `Forbid`, so every pattern and host
-- flag participates. For each ordered pair `(i, j)` of pattern flags it emits the
-- plain-equality, `@[simp]`-tagged theorem
--   `flagMul_FlagAlgebra_patN_k_m_i_FlagAlgebra_patN_k_m_j :`
--   `  FlagAlgebra_patN_k_m_i * FlagAlgebra_patN_k_m_j = Σ_h cₕ • FlagAlgebra_hostN_k_m_h`
-- (ordinary `=`, since no subgraph is forbidden). Same prerequisites as above.
--
-- Example — products of 3-vertex flags of type `FlagType_2_0` over 4-vertex hosts:
--   `generate_mul_theorems 3 4 2 0`
elab "generate_mul_theorems" patS:num hostS:num kS:num mS:num : command => do
  let k := kS.getNat
  let m := mS.getNat
  let patN := patS.getNat
  let hostN := hostS.getNat
  let patternTag := s!"{patN}_{k}_{m}"
  let hostTag := s!"{hostN}_{k}_{m}"
  let patternFlagTypeName := Name.mkSimple s!"FlagType_{k}_{m}"
  let flagTypeIdent := mkIdent patternFlagTypeName

  let patterns ← evalFlagDataRows k m patN
  let hosts ← evalFlagDataRows k m hostN
  let patternFree := freeFlagIndices patN none patterns
  let hostFree := freeFlagIndices hostN none hosts
  let flagSetEqUniv := mkIdent (Name.mkSimple s!"flagSet_{hostTag}_eq_univ")
  let flagSetValEq := mkIdent (Name.mkSimple s!"flagSet_{hostTag}_val_eq")

  let mut generated : Nat := 0
  for i in patternFree do
    for j in patternFree do
      let iOrd := if i ≤ j then i else j
      let jOrd := if i ≤ j then j else i
      let rhs ← buildMulRhs patN hostN hostTag patternFlagTypeName patterns hosts hostFree iOrd jOrd
      let lhs1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{i}")
      let lhs2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{j}")
      let flagAlgOrd1 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{iOrd}")
      let flagAlgOrd2 := mkIdent (Name.mkSimple s!"FlagAlgebra_{patternTag}_{jOrd}")
      let thmName := mkIdent (Name.mkSimple s!"flagMul_FlagAlgebra_{patternTag}_{i}_FlagAlgebra_{patternTag}_{j}")

      if !(← isDeclaredInScope lhs1.getId) then throwError s!"Missing definition: {lhs1.getId}"
      if !(← isDeclaredInScope lhs2.getId) then throwError s!"Missing definition: {lhs2.getId}"

      if !(← isDeclaredInScope thmName.getId) then
        let idsArray : Array (TSyntax `ident) := #[flagAlgOrd1, flagAlgOrd2]
        if i ≤ j then
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) = $rhs
              := by
              dsimp only [$[$idsArray:ident],*]
              rw [basisVector_quot_mul_eq_flagMul_quot]
              simp [flagMul, flagMulWithSize]
              rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
              have hsetval := $flagSetValEq
              rw [hsetval]
              simp [add_quot, smul_quot]
              rfl
          ))
        else
          elabCommand (← `(
            theorem $thmName
                : ($lhs1 * $lhs2 : FlagAlgebra $flagTypeIdent) = $rhs
              := by
              rw [mul_comm]
              dsimp only [$[$idsArray:ident],*]
              rw [basisVector_quot_mul_eq_flagMul_quot]
              simp [flagMul, flagMulWithSize]
              rw [Finset.sum_eq_multiset_sum, ← $flagSetEqUniv]
              have hsetval := $flagSetValEq
              rw [hsetval]
              simp [add_quot, smul_quot]
              rfl
          ))
        elabCommand (← `(attribute [simp] $thmName))
        generated := generated + 1

  logInfo s!"Generated {generated} plain multiplication theorem(s): pattern {patternTag}"

end Flags.Densities
