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

/-! ### Pruned generation of forbid-free flags

Generating only the forbid-free flags by filtering at the *underlying-graph* level
(cheap — `genSym2Graphs n` is the small empty-typed enumeration) and building σ-typed
flags only over the surviving graphs, then deduplicating. The completeness lemma
`genFlagsHfree_toFinset_eq` proves the result equals `univ.filter p` (the predicate the
forbid bridges produce) WITHOUT reducing the full typed enumeration `genFlagsOrdered σ n`
— that full reduction is the `native_decide` wall at typed `n ≥ 6`. -/

/-- Survivors of the labeled dedup fold come from the input list. -/
theorem foldl_dedupStepL_subset (xs : List (Sym2LabeledGraph σ n)) :
    ∀ (acc : List (Sym2LabeledGraph σ n)), xs.foldl dedupStepL acc ⊆ acc ++ xs := by
  induction xs with
  | nil => intro acc; simp
  | cons x rest ih =>
    intro acc g hg
    simp only [List.foldl_cons] at hg
    have hg2 := ih (dedupStepL acc x) hg
    rw [List.mem_append] at hg2
    rcases hg2 with hg2 | hg2
    · have hmem : g ∈ acc ++ [x] := by
        unfold dedupStepL at hg2
        split at hg2
        · exact List.mem_append_left _ hg2
        · exact hg2
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact List.mem_append_left _ h
      · exact h ▸ List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hg2)

/-- A member of `labeledOfGraph σ G` has underlying graph `G`. -/
theorem mem_labeledOfGraph_underlying {G : Sym2Graph n} {Glab : Sym2LabeledGraph σ n}
    (h : Glab ∈ labeledOfGraph σ G) : (⟨Glab.edges, Glab.edges_valid⟩ : Sym2Graph n) = G := by
  rw [labeledOfGraph, List.mem_filterMap] at h
  obtain ⟨f, _, hf⟩ := h
  cases hmk : mkTypeEmbedding? σ G f with
  | none => rw [hmk] at hf; simp at hf
  | some emb =>
    rw [hmk] at hf
    obtain rfl := Option.some.inj hf
    rfl

/-- Forbid-free σ-typed labeled graphs: filter the underlying-graph enumeration by `q`,
build labeled graphs over the survivors, dedup (keyed). The graph filter shrinks the input
before the expensive labeled dedup, so the downstream `native_decide` stays tractable. -/
def genLabeledGraphsHfree (σ : Sym2FlagType k) (n : ℕ) (q : Sym2Graph n → Bool) :
    List (Sym2LabeledGraph σ n) :=
  (((((genSym2Graphs n).filter q).flatMap (labeledOfGraph σ)).map withLabeledDegKey).foldl
    dedupStepDegL []).map Prod.fst

/-- The keyed pruned dedup equals the naive `dedupStepL` fold (mirrors
`genLabeledGraphsDedup_eq`). -/
theorem genLabeledGraphsHfree_eq (q : Sym2Graph n → Bool) :
    genLabeledGraphsHfree σ n q
      = (((genSym2Graphs n).filter q).flatMap (labeledOfGraph σ)).foldl dedupStepL [] := by
  unfold genLabeledGraphsHfree
  exact (foldl_dedupStepDegL_sim (((genSym2Graphs n).filter q).flatMap (labeledOfGraph σ))
    [] [] rfl (by simp)).1

/-- The forbid-free σ-typed flags: quotient classes of `genLabeledGraphsHfree`. -/
def genFlagsHfree (σ : Sym2FlagType k) (n : ℕ) (q : Sym2Graph n → Bool) : List (Sym2Flag σ n) :=
  (genLabeledGraphsHfree σ n q).map (Quotient.mk (sym2LabeledGraphSetoid σ n))

/-- **Completeness of the pruned generation, without reducing the full enumeration.** The
flags produced by `genFlagsHfree σ n q` are exactly `univ.filter p`, where the flag
predicate `p` agrees with the graph predicate `q` on underlying graphs (`hcompat`) and `q`
is isomorphism-invariant (`hq`). Mirrors `genFlagSet_eq_univ`, restricting coverage to the
`q`-true classes via `genSym2Graphs_complete`. -/
theorem genFlagsHfree_toFinset_eq (q : Sym2Graph n → Bool) (p : Sym2Flag σ n → Bool)
    (hq : ∀ {G G' : Sym2Graph n}, G ∼sf G' → q G = q G')
    (hcompat : ∀ (Glab : Sym2LabeledGraph σ n),
        p (Quotient.mk (sym2LabeledGraphSetoid σ n) Glab) = q ⟨Glab.edges, Glab.edges_valid⟩) :
    (genFlagsHfree σ n q).toFinset = Finset.univ.filter (fun F => p F = true) := by
  rw [genFlagsHfree, genLabeledGraphsHfree_eq]
  apply Finset.ext
  intro F
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Glab, hGlab, rfl⟩
    have hsub := foldl_dedupStepL_subset
      (((genSym2Graphs n).filter q).flatMap (labeledOfGraph σ)) [] hGlab
    rw [List.nil_append, List.mem_flatMap] at hsub
    obtain ⟨G, hGmem, hGlabmem⟩ := hsub
    rw [List.mem_filter] at hGmem
    rw [hcompat, mem_labeledOfGraph_underlying hGlabmem]
    exact hGmem.2
  · intro hpF
    obtain ⟨Glab0, rfl⟩ := Quotient.exists_rep F
    have hqU : q ⟨Glab0.edges, Glab0.edges_valid⟩ = true := by rw [← hcompat]; exact hpF
    obtain ⟨R, hRmem, hRiso⟩ :=
      genSym2Graphs_complete (⟨Glab0.edges, Glab0.edges_valid⟩ : Sym2Graph n)
    have hqR : q R = true := by rw [← hq hRiso]; exact hqU
    obtain ⟨Glab', hGlab'mem, hGlab'iso⟩ := mem_labeledOfGraph_eqv_of_underlying Glab0 hRiso
    have hInput : Glab' ∈ ((genSym2Graphs n).filter q).flatMap (labeledOfGraph σ) :=
      List.mem_flatMap.mpr ⟨R, List.mem_filter.mpr ⟨hRmem, hqR⟩, hGlab'mem⟩
    obtain ⟨Glab'', hGlab''mem, hGlab''iso⟩ :=
      foldl_dedupStepL_complete (((genSym2Graphs n).filter q).flatMap (labeledOfGraph σ))
        [] Glab' hInput
    exact ⟨Glab'', hGlab''mem,
      Quotient.sound (sym2LabeledGraphEqv.symm (sym2LabeledGraphEqv.trans hGlab'iso hGlab''iso))⟩

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

  -- The underlying multiset of `flagSetHfree` is the explicit free-flag list, so the
  -- forbid bridges can `rw [← …_eq]` onto `flagSetHfree` then unfold to the list.
  -- Mirrors `emitFlagSetMachinery`'s `…_val_eq`; the free list is `Nodup` because it
  -- is a `filter` of the `Nodup` enumeration (`sym2FlagListHfree_eq`).
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}_val_eq")
  let freeBridgeTerms : Array (TSyntax `term) := freeIndices.toArray.map (fun i =>
    mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}"))
  elabUnlessDefined flagSetValEqName.getId (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n))).val
            = [ $freeBridgeTerms,* ]) := by
        have hnodup : ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).Nodup := by
          rw [← $sym2ListEqName:ident]
          exact (FlagAlgebras.Compute.genEmptyTypedFlags_nodup $(Quote.quote n)).filter _
        have hdedup :
            ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).dedup
              = ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))) :=
          List.Nodup.dedup hnodup
        have hright :
            (List.map Sym2EmptyTypedFlag.toFlag
              ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))))
              = [ $freeBridgeTerms,* ] := by rfl
        refine Quot.sound ?_
        have heq :
            List.map Sym2EmptyTypedFlag.toFlag
              (([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).dedup)
                = [ $freeBridgeTerms,* ] := by
          simpa [hdedup] using hright
        exact heq ▸ List.Perm.refl _
    ))

  logInfo s!"Generated {freeIndices.length} {tag}-free empty-typed flags (n = {n}); \
flagSetHfree_{n}_0_0_{tag} completeness + val_eq proved."

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
  let isHfreeGraphName := mkIdent (Name.mkSimple s!"isHfreeGraph_{n}_{k}_{m}_{tag}")
  let sym2SetName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_{k}_{m}_{tag}")
  let sym2SetEqName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_{k}_{m}_{tag}_eq")
  let flagSetName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}")
  let flagSetEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}_eq")

  elabUnlessDefined isHfreeName.getId (← `(
      def $isHfreeName (S : Sym2Flag $typeTerm $(Quote.quote n)) : Bool :=
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ $forbidSym2 (S.toUnderlying) = 0)))

  -- Graph-level forbid-free test (the pruning predicate). Iso-invariant since it factors
  -- through the quotient `⟦·⟧`, and agrees with `isHfree` on a flag's underlying graph.
  elabUnlessDefined isHfreeGraphName.getId (← `(
      def $isHfreeGraphName (G : FlagAlgebras.Compute.Sym2Graph $(Quote.quote n)) : Bool :=
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ $forbidSym2
          (Quotient.mk (FlagAlgebras.Compute.Sym2GraphSetoid $(Quote.quote n)) G) = 0)))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset))

  -- Completeness WITHOUT reducing the full typed enumeration `genFlagsOrdered σ n` (the
  -- `native_decide` wall at typed n ≥ 6). Connect the named free set to the PRUNED generation
  -- (graph-level filter → tractable `native_decide`), then invoke the generic completeness
  -- theorem `genFlagsHfree_toFinset_eq`.
  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := by
        have hpruned : $sym2SetName
            = (FlagAlgebras.Compute.genFlagsHfree $typeTerm $(Quote.quote n) $isHfreeGraphName).toFinset := by
          native_decide
        rw [hpruned]
        refine FlagAlgebras.Compute.genFlagsHfree_toFinset_eq
          $isHfreeGraphName $isHfreeName ?_ (fun Glab => rfl)
        intro G G' hGG'
        simp only [$isHfreeGraphName:ident]
        rw [Quotient.sound hGG']))

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

  -- The underlying multiset of `flagSetHfree` is the explicit free-flag list (mirrors
  -- `emitFlagSetMachinery`'s `…_val_eq`); the free list is `Nodup` by a direct `native_decide`
  -- over the (few) named free flags.
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}_val_eq")
  let freeBridgeTerms : Array (TSyntax `term) := freeArr.map (fun i =>
    mkIdent (Name.mkSimple s!"Flag_{n}_{k}_{m}_{i}"))
  elabUnlessDefined flagSetValEqName.getId (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n))).val
            = ((([ $freeBridgeTerms,* ] : List (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n)))) :
                Multiset (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n)))) := by
        have hnodup : ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).Nodup := by
          native_decide
        have hdedup :
            ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).dedup
              = ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))) :=
          List.Nodup.dedup hnodup
        have hright :
            (List.map Sym2Flag.toFlag
              ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))))
              = ([ $freeBridgeTerms,* ] : List (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n))) := by
          rfl
        refine Quot.sound ?_
        have heq :
            List.map Sym2Flag.toFlag
              (([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).dedup)
                = ([ $freeBridgeTerms,* ] : List (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n))) := by
          simpa [hdedup] using hright
        exact heq ▸ List.Perm.refl _
    ))

  logInfo s!"Generated {freeArr.size} {tag}-free σ-typed flags (n = {n}, type {k}_{m}); \
flagSetHfree_{n}_{k}_{m}_{tag} completeness + val_eq proved."

end Flags.Densities
