import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator

/-! # Forbid-free flag generation

When working under a forbidden subgraph, only the forbid-free flags are ever
needed (the forbidden ones vanish under the `=[Forbid]` relation). This module
provides generation commands that emit *only* the forbid-free flag constants and
prove the corresponding completeness lemma — the forbid-free analogue of
`generate_empty_typed_flags` / `generate_flags`, whose completeness is `= univ`.

Instead of `flagSet = univ`, the forbid-free completeness is
`flagSetHfree = univ.filter (fun F' => flagDensity₁ Forbid.toFinFlag.2 (unlabel F') = 0)`
— exactly the predicate the `Forbid` expansion lemmas (`basisVector_quot_*_forbidEq_sum`)
produce — so the forbid bridges can rewrite directly onto the named forbid-free list.

The completeness is derived from the existing `… = univ` by filtering: the
forbid-free named list equals the full Lean enumeration filtered by forbid-freeness
(one `native_decide` referencing only the free constants), and filtering commutes
with `toFinset`/`univ`.
-/

open Lean Elab Command
open FlagAlgebras
open FlagAlgebras.Compute
open Flags.Densities

namespace FlagAlgebras.Compute

variable {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}

/-- Forget the type of a computable labeled graph, keeping the underlying graph. -/
def Sym2LabeledGraph.toUnderlying (G : Sym2LabeledGraph σ n) : Sym2EmptyTypedFlag n :=
  ⟦(⟨G.edges, G.edges_valid⟩ : Sym2Graph n)⟧

theorem Sym2LabeledGraph.toUnderlying_respect_eqv
    (G G' : Sym2LabeledGraph σ n) (h : G ∼sf G') :
    G.toUnderlying = G'.toUnderlying :=
  Quotient.sound (underlying_eqv_of_labeled_eqv h)

/-- Forget the type of a computable σ-typed flag, keeping the underlying graph.
A σ-typed flag is `Forbid`-free iff this underlying empty-typed flag is. -/
def Sym2Flag.toUnderlying (S : Sym2Flag σ n) : Sym2EmptyTypedFlag n :=
  Quotient.lift Sym2LabeledGraph.toUnderlying Sym2LabeledGraph.toUnderlying_respect_eqv S

/-- Unlabeling a decoded σ-flag agrees with decoding its underlying graph; the
general form of the per-flag `unlabel_n_k_m_i` lemma. -/
theorem Sym2Flag.unlabel_toFlag_eq (S : Sym2Flag σ n) :
    unlabel (S.toFlag) = (S.toUnderlying).toFlag := by
  induction S using Quotient.inductionOn with
  | _ G => rfl

end FlagAlgebras.Compute

namespace Flags.Densities

-- `generate_forbid_free_empty_typed_flags n Forbid`: emit only the `Forbid`-free
-- `n`-vertex empty-typed flags (`Flag_n_0_0_i` for forbid-free `i`), plus the
-- completeness lemma `flagSetHfree_n_0_0_<Forbid> = univ.filter (forbid-free)`.
-- The forbid-free split (which `i` to emit) uses `containsForbiddenSubgraph`;
-- the emitted completeness is independently verified by `native_decide` against
-- the computable single-flag density of `Forbid`.
elab "generate_forbid_free_empty_typed_flags" nStx:num gStx:ident : command => do
  let n := nStx.getNat
  let tag := gStx.getId.toString

  -- Resolve the forbidden graph; recover its canonical flag `Sym2Flag_r_0_0_idx`.
  let (gIdent, gEqName) ← resolveForbidGraph tag
  let gEqIdent := mkIdent gEqName
  let forbidFlag ← forbidFlagIdentOfToFinFlagEq gEqName
  let (r, idx) ← parseFlagRIdx forbidFlag.getId.toString
  let forbidSym2 := mkIdent (Name.mkSimple s!"Sym2Flag_{r}_0_0_{idx}")

  -- The forbid-free indices among the canonical `n`-vertex graphs.
  let hostEdges ← evalCanonicalEdgeLists n
  let forbidAll ← evalCanonicalEdgeLists r
  let forbidEdges := forbidAll.getD idx []
  let freeIndices := (List.range hostEdges.length).filter (fun i =>
    ¬ containsForbiddenSubgraph r forbidEdges n (hostEdges.getD i []))

  -- Emit the forbid-free flag constants (mirrors `generate_empty_typed_flags`).
  for i in freeIndices do
    let edgePairs := hostEdges[i]!
    let graphName := mkIdent (Name.mkSimple s!"Sym2Graph_{n}_0_0_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{i}")
    let edgesTerm ← natPairsToEdgesTerm n edgePairs
    elabUnlessDefined graphName.getId (← `(
        def $graphName : Sym2Graph $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])
      ))
    elabUnlessDefined flagName.getId (← `(
        def $flagName : Sym2EmptyTypedFlag $(Quote.quote n) :=
          Quotient.mk (Sym2GraphSetoid $(Quote.quote n)) $graphName
      ))
    elabUnlessDefined flagBridgeName.getId (← `(
        def $flagBridgeName := ($flagName : Sym2EmptyTypedFlag $(Quote.quote n)).toFlag
      ))
    elabUnlessDefined flagAlgebraName.getId (← `(
        noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra ∅ₜ :=
          ⟦FlagAlgebras.basisVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧
      ))

  let freeSym2Terms : Array (TSyntax `term) := freeIndices.toArray.map (fun i =>
    mkIdent (Name.mkSimple s!"Sym2Flag_{n}_0_0_{i}"))

  let isHfreeName := mkIdent (Name.mkSimple s!"isHfree_{n}_0_0_{tag}")
  let sym2SetName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_0_0_{tag}")
  let sym2ListEqName := mkIdent (Name.mkSimple s!"sym2FlagListHfree_{n}_0_0_{tag}_eq")
  let sym2SetEqName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_0_0_{tag}_eq")
  let flagSetName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}")
  let flagSetEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}_eq")

  -- Computable forbid-free test via the ℚ-valued `Sym2` density.
  elabUnlessDefined isHfreeName.getId (← `(
      def $isHfreeName (S : FlagAlgebras.Compute.Sym2EmptyTypedFlag $(Quote.quote n)) : Bool :=
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ $forbidSym2 S = 0)
    ))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2EmptyTypedFlag $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset
    ))

  elabUnlessDefined sym2ListEqName.getId (← `(
      theorem $sym2ListEqName :
          ((FlagAlgebras.Compute.genEmptyTypedFlags $(Quote.quote n)).filter (fun S => $isHfreeName S))
            = ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))) := by
        native_decide
    ))

  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := by
        rw [← FlagAlgebras.Compute.genEmptyTypedFlagSet_eq_univ $(Quote.quote n)]
        show _ = ((FlagAlgebras.Compute.genEmptyTypedFlags $(Quote.quote n)).toFinset).filter
            (fun S => $isHfreeName S = true)
        rw [← List.toFinset_filter, $sym2ListEqName:ident]
        rfl
    ))

  elabUnlessDefined flagSetName.getId (← `(
      noncomputable def $flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n)) :=
        ($sym2SetName).map ⟨Sym2EmptyTypedFlag.toFlag,
          fun a b h => Sym2EmptyTypedFlag.toFlag_injective a b h⟩
    ))

  elabUnlessDefined flagSetEqName.getId (← `(
      theorem $flagSetEqName :
          $flagSetName
            = Finset.univ.filter (fun F' => flagDensity₁ ($gIdent).toFinFlag.2 (unlabel F') = 0) := by
        rw [$flagSetName:ident, $sym2SetEqName:ident]
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨S, hS, hSx⟩
          rw [← hSx, unlabel_emptyType, $gEqIdent:ident]
          show flagDensity₁ ($forbidSym2).toFlag S.toFlag = 0
          rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
          exact of_decide_eq_true hS
        · intro hx
          refine ⟨x.toSym2EmptyTypedFlag, ?_, x.toSym2EmptyTypedFlag_toFlag_eq⟩
          rw [unlabel_emptyType, $gEqIdent:ident] at hx
          show $isHfreeName _ = true
          rw [$isHfreeName:ident, decide_eq_true_eq,
            ← flagDensity₁_eq_sym2EmptyTypeFlagDensity₁, x.toSym2EmptyTypedFlag_toFlag_eq]
          exact hx
    ))

  logInfo s!"Generated {freeIndices.length} {tag}-free empty-typed flags (n = {n}); \
flagSetHfree_{n}_0_0_{tag} completeness proved."

-- `generate_forbid_free_flags k m n Forbid`: the σ-typed analogue. Emits only the
-- `Forbid`-free σ-typed `n`-vertex flags `Flag_n_k_m_i` (those whose underlying
-- graph is `Forbid`-free), their `unlabel`/`downward` bridges, and the
-- completeness `flagSetHfree_n_k_m_<Forbid> = univ.filter (forbid-free)`. Requires
-- the underlying `Forbid`-free empty-typed flags (run
-- `generate_forbid_free_empty_typed_flags n Forbid` first).
elab "generate_forbid_free_flags" kStx:num mStx:num nStx:num gStx:ident : command => do
  let k := kStx.getNat
  let m := mStx.getNat
  let n := nStx.getNat
  let tag := gStx.getId.toString

  let (gIdent, gEqName) ← resolveForbidGraph tag
  let gEqIdent := mkIdent gEqName
  let forbidFlag ← forbidFlagIdentOfToFinFlagEq gEqName
  let (r, idx) ← parseFlagRIdx forbidFlag.getId.toString
  let forbidSym2 := mkIdent (Name.mkSimple s!"Sym2Flag_{r}_0_0_{idx}")

  unless (← getEnv).contains (Name.mkSimple s!"Flag_{n}_0_0_0") do
    throwError s!"`generate_forbid_free_flags {k} {m} {n} {tag}` requires the underlying \
{tag}-free empty-typed flags. Add `generate_forbid_free_empty_typed_flags {n} {tag}` first."

  let allTypeEdges ← evalCanonicalEdgeLists k
  let typeEdges := allTypeEdges.getD m []
  let flagData ← evalFlagDataRows k m n
  let count := flagData.length

  let forbidAll ← evalCanonicalEdgeLists r
  let forbidEdges := forbidAll.getD idx []
  -- A σ-typed flag is forbid-free iff its underlying graph (entry.2.1) is.
  let freeArr := ((List.range count).filter (fun i =>
    ¬ containsForbiddenSubgraph r forbidEdges n ((flagData.getD i (0, [], [], 0, 0)).2.1))).toArray

  let typeName := mkIdent (Name.mkSimple s!"Sym2FlagType_{k}_{m}")
  let flagTypeName := mkIdent (Name.mkSimple s!"FlagType_{k}_{m}")
  let typeEdgesTerm ← natPairsToEdgesTerm k typeEdges
  elabUnlessDefined typeName.getId (← `(
      def $typeName : Sym2FlagType $(Quote.quote k) where
        edges := mkEdgeFinset $(Quote.quote k) $typeEdgesTerm
        edges_valid := mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])
    ))
  elabUnlessDefined flagTypeName.getId (← `(
      def $flagTypeName := (($typeName : Sym2FlagType $(Quote.quote k))).toFlagType))
  let typeTerm ← `(($typeName : Sym2FlagType $(Quote.quote k)))

  -- Emit the forbid-free σ-typed flag constants + their `unlabel` bridges.
  for i in freeArr do
    let entry := flagData[i]!
    let underlyingIdx := entry.1
    let graphEdges := entry.2.1
    let typeIndices := entry.2.2.1
    let labeledName := mkIdent (Name.mkSimple s!"Sym2LabeledGraph_{n}_{k}_{m}_{i}")
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{m}_{i}")
    let edgesTerm ← natPairsToEdgesTerm n graphEdges
    let idxFinExpr ← mkTypeIndexFinExpr typeIndices.toArray n
    elabUnlessDefined labeledName.getId (← `(
        def $labeledName : Sym2LabeledGraph $typeTerm $(Quote.quote n) where
          edges := mkEdgeFinset $(Quote.quote n) $edgesTerm
          edges_valid := mkEdgeFinset_diag_free (by intro e he; fin_cases he <;> simp [Sym2.isDiag_iff_proj_eq])
          type_embed := by
            let e : (Fin $(Quote.quote k)) ↪ (Fin $(Quote.quote n)) :=
              ⟨(fun i : Fin $(Quote.quote k) => $idxFinExpr), by decide⟩
            have hmap : ∀ u v,
                (SimpleGraph.fromEdgeSet ((mkEdgeFinset $(Quote.quote n) $edgesTerm : Finset (Sym2 (Fin $(Quote.quote n)))) : Set (Sym2 (Fin $(Quote.quote n))))).Adj (e u) (e v)
                ↔
                (SimpleGraph.fromEdgeSet ((($typeTerm).edges : Finset (Sym2 (Fin $(Quote.quote k)))) : Set (Sym2 (Fin $(Quote.quote k))))).Adj u v := by
              decide
            exact ⟨e, hmap _ _⟩
      ))
    elabUnlessDefined flagName.getId (← `(
        def $flagName : Sym2Flag $typeTerm $(Quote.quote n) :=
          Quotient.mk (sym2LabeledGraphSetoid $typeTerm $(Quote.quote n)) $labeledName))
    elabUnlessDefined flagBridgeName.getId (← `(
        def $flagBridgeName := ($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag))
    elabUnlessDefined flagAlgebraName.getId (← `(
        noncomputable def $flagAlgebraName : FlagAlgebras.FlagAlgebra $flagTypeName :=
          ⟦FlagAlgebras.basisVector ⟨$(Quote.quote n), $flagBridgeName⟩⟧))
    let unlabelThmName := mkIdent (Name.mkSimple s!"unlabel_{n}_{k}_{m}_{i}")
    let baseFlagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{underlyingIdx}")
    elabUnlessDefined unlabelThmName.getId (← `(
        @[simp]
        theorem $unlabelThmName : FlagAlgebras.unlabel $flagBridgeName = $baseFlagName := by
          exact Quotient.sound (FlagAlgebras.flagEqv.refl _)))

  -- Batched downward normalizing factors (one `native_decide` over the free flags).
  let downwardFactorsEqName := mkIdent (Name.mkSimple s!"downwardFactorsHfree_{n}_{k}_{m}_{tag}_eq")
  let mut dnfTerms : Array (TSyntax `term) := #[]
  let mut coeffTerms : Array (TSyntax `term) := #[]
  for i in freeArr do
    let entry := flagData[i]!
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    dnfTerms := dnfTerms.push (←
      `(FlagAlgebras.Compute.downwardNormalizingFactor_Sym2Flag
          ($flagName : Sym2Flag $typeTerm $(Quote.quote n))))
    coeffTerms := coeffTerms.push (← coeffQTerm entry.2.2.2.1 entry.2.2.2.2)
  elabUnlessDefined downwardFactorsEqName.getId (← `(
      theorem $downwardFactorsEqName : ([ $dnfTerms,* ] : List ℚ) = [ $coeffTerms,* ] := by
        native_decide))

  for pos in [0:freeArr.size] do
    let i := freeArr[pos]!
    let entry := flagData[i]!
    let underlyingIdx := entry.1
    let coeffQ ← coeffQTerm entry.2.2.2.1 entry.2.2.2.2
    let coeffR ← `(($coeffQ : ℝ))
    let flagName := mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}")
    let flagBridgeName := mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}")
    let flagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_{k}_{m}_{i}")
    let downwardThmName := mkIdent (Name.mkSimple s!"downward_{n}_{k}_{m}_{i}")
    let baseFlagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{underlyingIdx}")
    let baseFlagAlgebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{underlyingIdx}")
    elabUnlessDefined downwardThmName.getId (← `(
        @[simp]
        theorem $downwardThmName : ⟦$flagAlgebraName⟧₀ = $coeffR • $baseFlagAlgebraName := by
          have hdnf : FlagAlgebras.downwardNormalizingFactor $flagBridgeName = $coeffQ := by
            change FlagAlgebras.downwardNormalizingFactor (($flagName : Sym2Flag $typeTerm $(Quote.quote n)).toFlag) = $coeffQ
            rw [FlagAlgebras.Compute.downwardNormalizingFactor_eq]
            exact congrArg (fun l => l.getD $(Quote.quote pos) (0 : ℚ)) $downwardFactorsEqName
          change
            FlagAlgebras.downwardFlagVectorQuot (FlagAlgebras.basisVector ⟨$(Quote.quote n), $flagBridgeName⟩)
              = $coeffR • (⟦FlagAlgebras.basisVector ⟨$(Quote.quote n), $baseFlagName⟩⟧ : FlagAlgebras.FlagAlgebra ∅ₜ)
          apply Quotient.sound
          simp [FlagAlgebras.downwardFlagVector, FlagAlgebras.downwardFlag, linearExtension, hdnf]))

  -- Completeness, in the bridge's predicate form.
  let freeSym2Terms : Array (TSyntax `term) := freeArr.map (fun i =>
    mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}"))
  let isHfreeName := mkIdent (Name.mkSimple s!"isHfree_{n}_{k}_{m}_{tag}")
  let sym2SetName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_{k}_{m}_{tag}")
  let sym2ListEqName := mkIdent (Name.mkSimple s!"sym2FlagListHfree_{n}_{k}_{m}_{tag}_eq")
  let sym2SetEqName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_{k}_{m}_{tag}_eq")
  let flagSetName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}")
  let flagSetEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}_eq")

  elabUnlessDefined isHfreeName.getId (← `(
      def $isHfreeName (S : Sym2Flag $typeTerm $(Quote.quote n)) : Bool :=
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ $forbidSym2 (S.toUnderlying) = 0)))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset))

  elabUnlessDefined sym2ListEqName.getId (← `(
      theorem $sym2ListEqName :
          ((FlagAlgebras.Compute.genFlagsOrdered $typeTerm $(Quote.quote n)).filter (fun S => $isHfreeName S))
            = ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))) := by
        native_decide))

  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := by
        rw [← FlagAlgebras.Compute.genFlagSet_eq_univ $typeTerm $(Quote.quote n),
          ← FlagAlgebras.Compute.genFlagsOrdered_toFinset $typeTerm $(Quote.quote n)]
        show _ = ((FlagAlgebras.Compute.genFlagsOrdered $typeTerm $(Quote.quote n)).toFinset).filter
            (fun S => $isHfreeName S = true)
        rw [← List.toFinset_filter, $sym2ListEqName:ident]
        rfl))

  elabUnlessDefined flagSetName.getId (← `(
      noncomputable def $flagSetName : Finset (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n)) :=
        ($sym2SetName).map ⟨Sym2Flag.toFlag, fun a b h => Sym2Flag.toFlag_injective a b h⟩))

  elabUnlessDefined flagSetEqName.getId (← `(
      theorem $flagSetEqName :
          $flagSetName
            = Finset.univ.filter (fun F' => flagDensity₁ ($gIdent).toFinFlag.2 (unlabel F') = 0) := by
        rw [$flagSetName:ident, $sym2SetEqName:ident]
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨S, hS, hSx⟩
          rw [← hSx, FlagAlgebras.Compute.Sym2Flag.unlabel_toFlag_eq, $gEqIdent:ident]
          show flagDensity₁ ($forbidSym2).toFlag (S.toUnderlying).toFlag = 0
          rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
          exact of_decide_eq_true hS
        · intro hx
          refine ⟨x.toSym2Flag, ?_, x.toSym2Flag_toFlag_eq⟩
          rw [$gEqIdent:ident] at hx
          show $isHfreeName _ = true
          rw [$isHfreeName:ident, decide_eq_true_eq, ← flagDensity₁_eq_sym2EmptyTypeFlagDensity₁,
            ← FlagAlgebras.Compute.Sym2Flag.unlabel_toFlag_eq, x.toSym2Flag_toFlag_eq]
          exact hx))

  logInfo s!"Generated {freeArr.size} {tag}-free σ-typed flags (n = {n}, type {k}_{m}); \
flagSetHfree_{n}_{k}_{m}_{tag} completeness proved."

end Flags.Densities
