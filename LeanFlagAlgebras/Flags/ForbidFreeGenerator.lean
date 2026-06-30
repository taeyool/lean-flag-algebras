import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator
import LeanFlagAlgebras.Flags.ForbidFreePruned

/-! # Forbid-free flag generation

When working under a forbidden subgraph, only the forbid-free flags are ever
needed (the forbidden ones vanish under the `=ᵢ[Forbid]` relation). This module
provides generation commands that emit *only* the forbid-free flag constants and
prove the corresponding completeness lemma — the forbid-free analogue of
`generate_empty_typed_flags` / `generate_flags`, whose completeness is `= univ`.

Instead of `flagSet = univ`, the forbid-free completeness is
`flagSetHfree = univ.filter (fun F' => flagDensity₁ Forbid.toFinFlag.2 (unlabel F') = 0)`
— exactly the predicate the `Forbid` expansion lemmas (`basisVector_quot_*_inducedForbidEq_sum`)
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
  (((((genSym2GraphsDedup n).filter q).flatMap (labeledOfGraph σ)).map withLabeledDegKey).foldl
    dedupStepDegL []).map Prod.fst

/-- The keyed pruned dedup equals the naive `dedupStepL` fold (mirrors
`genLabeledGraphsDedup_eq`). -/
theorem genLabeledGraphsHfree_eq (q : Sym2Graph n → Bool) :
    genLabeledGraphsHfree σ n q
      = (((genSym2GraphsDedup n).filter q).flatMap (labeledOfGraph σ)).foldl dedupStepL [] := by
  unfold genLabeledGraphsHfree
  exact (foldl_dedupStepDegL_sim (((genSym2GraphsDedup n).filter q).flatMap (labeledOfGraph σ))
    [] [] rfl (by simp)).1

/-- The forbid-free σ-typed flags: quotient classes of `genLabeledGraphsHfree`. -/
def genFlagsHfree (σ : Sym2FlagType k) (n : ℕ) (q : Sym2Graph n → Bool) : List (Sym2Flag σ n) :=
  (genLabeledGraphsHfree σ n q).map (Quotient.mk (sym2LabeledGraphSetoid σ n))

/-- **Completeness of the pruned generation, without reducing the full enumeration.** The
flags produced by `genFlagsHfree σ n q` are exactly `univ.filter p`, where the flag
predicate `p` agrees with the graph predicate `q` on underlying graphs (`hcompat`) and `q`
is isomorphism-invariant (`hq`). Mirrors `genFlagSet_eq_univ`, restricting coverage to the
`q`-true classes via `genSym2GraphsDedup_complete`. -/
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
      (((genSym2GraphsDedup n).filter q).flatMap (labeledOfGraph σ)) [] hGlab
    rw [List.nil_append, List.mem_flatMap] at hsub
    obtain ⟨G, hGmem, hGlabmem⟩ := hsub
    rw [List.mem_filter] at hGmem
    rw [hcompat, mem_labeledOfGraph_underlying hGlabmem]
    exact hGmem.2
  · intro hpF
    obtain ⟨Glab0, rfl⟩ := Quotient.exists_rep F
    have hqU : q ⟨Glab0.edges, Glab0.edges_valid⟩ = true := by rw [← hcompat]; exact hpF
    obtain ⟨R, hRmem, hRiso⟩ :=
      genSym2GraphsDedup_complete (⟨Glab0.edges, Glab0.edges_valid⟩ : Sym2Graph n)
    have hqR : q R = true := by rw [← hq hRiso]; exact hqU
    obtain ⟨Glab', hGlab'mem, hGlab'iso⟩ := mem_labeledOfGraph_eqv_of_underlying Glab0 hRiso
    have hInput : Glab' ∈ ((genSym2GraphsDedup n).filter q).flatMap (labeledOfGraph σ) :=
      List.mem_flatMap.mpr ⟨R, List.mem_filter.mpr ⟨hRmem, hqR⟩, hGlab'mem⟩
    obtain ⟨Glab'', hGlab''mem, hGlab''iso⟩ :=
      foldl_dedupStepL_complete (((genSym2GraphsDedup n).filter q).flatMap (labeledOfGraph σ))
        [] Glab' hInput
    exact ⟨Glab'', hGlab''mem,
      Quotient.sound (sym2LabeledGraphEqv.symm (sym2LabeledGraphEqv.trans hGlab'iso hGlab''iso))⟩

/-! ### Genuine-pruning σ-typed generation (Task 8b)

`genFlagsHfree` filters the *full* graph enumeration `genSym2GraphsDedup n` by `q`. The version
below instead builds labeled graphs directly over the **pruned** representatives
`augRepsFreeB qB n` — which never materializes a forbidden graph at the graph level — then labels
and dedups. Its completeness is the same statement as `genFlagsHfree_toFinset_eq`, but routed
through `augRepsFreeB_free` (soundness) and `augRepsFreeB_complete` (completeness) in place of the
filter + `genSym2GraphsDedup_complete`. The predicate `qB` is the recursion-indexed
`(k) → Sym2Graph k → Bool` that `augRepsFreeB` needs (e.g. `qFree F` / `qCliqueFree r`). -/

/-- Forbid-free σ-typed labeled graphs by **genuine pruning**: label the pruned graph reps
`augRepsFreeB qB n`, then keyed-dedup. No forbidden graph is ever built. -/
def genLabeledGraphsHfreePruned (σ : Sym2FlagType k) (n : ℕ)
    (qB : (k : ℕ) → Sym2Graph k → Bool) : List (Sym2LabeledGraph σ n) :=
  (((((augRepsFreeBDeg qB n).map Prod.fst).flatMap (labeledOfGraph σ)).map withLabeledDegKey).foldl
    dedupStepDegL []).map Prod.fst

/-- The keyed pruned dedup equals the naive `dedupStepL` fold (mirrors `genLabeledGraphsHfree_eq`). -/
theorem genLabeledGraphsHfreePruned_eq (qB : (k : ℕ) → Sym2Graph k → Bool) :
    genLabeledGraphsHfreePruned σ n qB
      = ((augRepsFreeB qB n).flatMap (labeledOfGraph σ)).foldl dedupStepL [] := by
  unfold genLabeledGraphsHfreePruned
  rw [augRepsFreeBDeg_fst_eq]
  exact (foldl_dedupStepDegL_sim ((augRepsFreeB qB n).flatMap (labeledOfGraph σ))
    [] [] rfl (by simp)).1

/-- The genuine-pruning forbid-free σ-typed flags. -/
def genFlagsHfreePruned (σ : Sym2FlagType k) (n : ℕ)
    (qB : (k : ℕ) → Sym2Graph k → Bool) : List (Sym2Flag σ n) :=
  (genLabeledGraphsHfreePruned σ n qB).map (Quotient.mk (sym2LabeledGraphSetoid σ n))

/-- **Completeness of the genuine-pruning σ-typed generation.** The flags produced by
`genFlagsHfreePruned σ n qB` are exactly `univ.filter p`, where the flag predicate `p` agrees with
`qB n` on underlying graphs (`hcompat`) and `qB` is iso-invariant (`hq_iso`), preserved by `restrict`
(`hq_restrict`), and holds at the empty base (`hq0`). The arbitrary-`F` σ-typed analogue of
`prunedFreeFlags_toFinset_eq` — no full enumeration, no forbidden graph ever built. -/
theorem genFlagsHfreePruned_toFinset_eq (qB : (k : ℕ) → Sym2Graph k → Bool) (p : Sym2Flag σ n → Bool)
    (hq_iso : ∀ {k : ℕ} {G G' : Sym2Graph k}, G ∼sf G' → qB k G = qB k G')
    (hq_restrict : ∀ {k : ℕ} {H : Sym2Graph (k + 1)}, qB (k + 1) H = true → qB k (restrict H) = true)
    (hq0 : qB 0 (⟨∅, by simp⟩ : Sym2Graph 0) = true)
    (hcompat : ∀ (Glab : Sym2LabeledGraph σ n),
        p (Quotient.mk (sym2LabeledGraphSetoid σ n) Glab) = qB n ⟨Glab.edges, Glab.edges_valid⟩) :
    (genFlagsHfreePruned σ n qB).toFinset = Finset.univ.filter (fun F => p F = true) := by
  rw [genFlagsHfreePruned, genLabeledGraphsHfreePruned_eq]
  apply Finset.ext
  intro F
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Glab, hGlab, rfl⟩
    have hsub := foldl_dedupStepL_subset
      ((augRepsFreeB qB n).flatMap (labeledOfGraph σ)) [] hGlab
    rw [List.nil_append, List.mem_flatMap] at hsub
    obtain ⟨G, hGmem, hGlabmem⟩ := hsub
    rw [hcompat, mem_labeledOfGraph_underlying hGlabmem]
    exact augRepsFreeB_free qB hq0 n G hGmem
  · intro hpF
    obtain ⟨Glab0, rfl⟩ := Quotient.exists_rep F
    have hqU : qB n ⟨Glab0.edges, Glab0.edges_valid⟩ = true := by rw [← hcompat]; exact hpF
    obtain ⟨R, hRmem, hRiso⟩ :=
      augRepsFreeB_complete qB hq_iso hq_restrict n ⟨Glab0.edges, Glab0.edges_valid⟩ hqU
    obtain ⟨Glab', hGlab'mem, hGlab'iso⟩ := mem_labeledOfGraph_eqv_of_underlying Glab0 hRiso
    have hInput : Glab' ∈ (augRepsFreeB qB n).flatMap (labeledOfGraph σ) :=
      List.mem_flatMap.mpr ⟨R, hRmem, hGlab'mem⟩
    obtain ⟨Glab'', hGlab''mem, hGlab''iso⟩ :=
      foldl_dedupStepL_complete ((augRepsFreeB qB n).flatMap (labeledOfGraph σ))
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

/-! ### Edge-based, pruning-backed empty-typed generation (Task 5b)

`generate_pruned_forbid_free_empty_typed_flags n F` is the arbitrary-`F` analogue of
`generate_forbid_free_empty_typed_flags`, with two differences:

* the forbidden graph is a **`Sym2Graph m` term** `F` read directly (D2) — no
  `generate_complete_graph`, no canonical forbidden flag, no tag resolution;
* the forbid-free split uses the **induced** predicate `inducedContains F` (correct for arbitrary
  `F`, not only complete graphs), and the completeness lemma cites
  `prunedFreeFlags_toFinset_eq` (genuine pruning) — **no full enumeration**.

(The `evalBoolList` / `evalInducedFreeMask` helpers live in `Densities.DensityThmGenerator`, shared
with the edge-based pair-density / mul commands.) -/

elab "generate_pruned_forbid_free_empty_typed_flags" nStx:num fStx:ident : command => do
  let n := nStx.getNat
  let tagFull := toString fStx.getId
  let tag := (tagFull.splitOn ".").getLastD tagFull

  let hostEdges ← evalCanonicalEdgeLists n
  -- Task 8a: for a complete-graph forbid `completeSym2Graph r`, prune with the cheap `hasClique r`
  -- (a vertex-subset scan) instead of the generic embedding-based `inducedContains` — same free
  -- set, far cheaper at high `n`. Non-complete forbids keep the generic path.
  let completeR? ← detectCompleteR fStx
  let freeMask ← match completeR? with
    | some r => evalCliqueFreeMask n r
    | none => evalInducedFreeMask n fStx
  let freeIndices := (List.range hostEdges.length).filter (fun i => freeMask.getD i false)

  -- Emit the forbid-free flag constants (identical to `generate_forbid_free_empty_typed_flags`).
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
  let sym2SetEqName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_0_0_{tag}_eq")
  let flagSetName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}")
  let flagSetEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}_eq")

  -- The framework's analytic forbid-free test, stated directly on the `Sym2Graph` term `F`.
  elabUnlessDefined isHfreeName.getId (← `(
      def $isHfreeName (S : FlagAlgebras.Compute.Sym2EmptyTypedFlag $(Quote.quote n)) : Bool :=
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ ⟦$fStx⟧ S = 0)
    ))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2EmptyTypedFlag $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset
    ))

  -- Completeness via genuine pruning (Task 5a): the named free set equals the pruned generation
  -- (one `native_decide` over the *pruned* generator — never builds an `F`-containing graph), closed
  -- by `prunedFreeFlags_toFinset_eq`. No full enumeration, no canonical forbidden flag. For a
  -- complete-graph forbid the `native_decide` runs over the cheap *clique*-pruned generator (8a).
  let sym2SetEqProof : TSyntax `term ← match completeR? with
    | some r => `(by
        have hpruned : $sym2SetName
            = (FlagAlgebras.Compute.prunedCliqueFreeFlags $(Quote.quote r) $(Quote.quote n)).toFinset := by
          native_decide
        rw [hpruned, FlagAlgebras.Compute.prunedCliqueFreeFlags_toFinset_eq $fStx
            (FlagAlgebras.Compute.completeSym2Graph_edges_iff $(Quote.quote r)) (by decide) $(Quote.quote n)]
        ext S
        simp only [$isHfreeName:ident, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq])
    | none => `(by
        have hpruned : $sym2SetName
            = (FlagAlgebras.Compute.prunedFreeFlags $fStx $(Quote.quote n)).toFinset := by
          native_decide
        rw [hpruned, FlagAlgebras.Compute.prunedFreeFlags_toFinset_eq $fStx (by decide) $(Quote.quote n)]
        ext S
        simp only [$isHfreeName:ident, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq])
  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := $sym2SetEqProof
    ))

  elabUnlessDefined flagSetName.getId (← `(
      noncomputable def $flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n)) :=
        ($sym2SetName).map ⟨Sym2EmptyTypedFlag.toFlag,
          fun a b h => Sym2EmptyTypedFlag.toFlag_injective a b h⟩
    ))

  elabUnlessDefined flagSetEqName.getId (← `(
      theorem $flagSetEqName :
          $flagSetName
            = Finset.univ.filter (fun F' =>
                flagDensity₁ (Sym2EmptyTypedFlag.toFlag ⟦$fStx⟧) (unlabel F') = 0) := by
        rw [$flagSetName:ident, $sym2SetEqName:ident]
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨S, hS, hSx⟩
          rw [← hSx, unlabel_emptyType]
          show flagDensity₁ (Sym2EmptyTypedFlag.toFlag ⟦$fStx⟧) S.toFlag = 0
          rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
          exact of_decide_eq_true hS
        · intro hx
          refine ⟨x.toSym2EmptyTypedFlag, ?_, x.toSym2EmptyTypedFlag_toFlag_eq⟩
          rw [unlabel_emptyType] at hx
          show $isHfreeName _ = true
          rw [$isHfreeName:ident, decide_eq_true_eq,
            ← flagDensity₁_eq_sym2EmptyTypeFlagDensity₁, x.toSym2EmptyTypedFlag_toFlag_eq]
          exact hx
    ))

  -- Underlying multiset of `flagSetHfree` = the explicit free-flag list (for the forbid bridges).
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}_val_eq")
  let freeBridgeTerms : Array (TSyntax `term) := freeIndices.toArray.map (fun i =>
    mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}"))
  elabUnlessDefined flagSetValEqName.getId (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n))).val
            = [ $freeBridgeTerms,* ]) := by
        have hnodup : ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).Nodup := by
          native_decide
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

  let pathDesc := match completeR? with
    | some r => s!"cheap clique check (K{r}, hasClique {r})"
    | none => "generic inducedContains"
  logInfo s!"Generated {freeIndices.length} {tag}-free empty-typed flags (n = {n}) by genuine \
pruning (edge-based, induced) via the {pathDesc}; flagSetHfree_{n}_0_0_{tag} completeness + val_eq proved."

/-- `generate_subgraph_free_empty_typed_flags n F`: the **subgraph**-forbidding analogue of
`generate_pruned_forbid_free_empty_typed_flags`. Emits the empty-typed `n`-vertex flags that are
*subgraph*-`F`-free (computed by `subgraphContains`), the analytic test `isHfree` (zero density of
every supergraph of `F`), the completeness `sym2FlagSetHfree…_eq` (direct `native_decide`), and the
`FinFlag`-side bridge `flagSetHfree…_eq` to the filter the subgraph capstone
`basisVector_quot_forbidEq_sum_subgraph` expands over (via `supergraphFamily_filter_iff`). -/
elab "generate_subgraph_free_empty_typed_flags" nStx:num fStx:ident : command => do
  let n := nStx.getNat
  let tagFull := toString fStx.getId
  let tag := (tagFull.splitOn ".").getLastD tagFull
  let hostEdges ← evalCanonicalEdgeLists n
  let freeMask ← evalSubgraphFreeMask n fStx
  let freeIndices := (List.range hostEdges.length).filter (fun i => freeMask.getD i false)

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
  let sym2SetEqName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_0_0_{tag}_eq")
  let flagSetName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}")
  let flagSetEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}_eq")

  -- Subgraph-free analytic test: zero density of *every* supergraph of `F`.
  elabUnlessDefined isHfreeName.getId (← `(
      def $isHfreeName (S : FlagAlgebras.Compute.Sym2EmptyTypedFlag $(Quote.quote n)) : Bool :=
        decide (∀ s ∈ FlagAlgebras.Compute.supergraphSym2List $fStx,
          FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ s S = 0)
    ))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2EmptyTypedFlag $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).toFinset
    ))

  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := by native_decide
    ))

  elabUnlessDefined flagSetName.getId (← `(
      noncomputable def $flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n)) :=
        ($sym2SetName).map ⟨Sym2EmptyTypedFlag.toFlag,
          fun a b h => Sym2EmptyTypedFlag.toFlag_injective a b h⟩
    ))

  elabUnlessDefined flagSetEqName.getId (← `(
      theorem $flagSetEqName :
          $flagSetName
            = Finset.univ.filter (fun F' =>
                ∀ D ∈ FlagAlgebras.Compute.supergraphFamily $fStx,
                  flagDensity₁ D.2 (unlabel F') = 0) := by
        rw [$flagSetName:ident, $sym2SetEqName:ident]
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨S, hS, hSx⟩
          rw [$isHfreeName:ident, decide_eq_true_eq] at hS
          rw [← hSx, unlabel_emptyType]
          exact (FlagAlgebras.Compute.supergraphFamily_filter_iff $fStx S).mpr hS
        · intro hx
          refine ⟨x.toSym2EmptyTypedFlag, ?_, x.toSym2EmptyTypedFlag_toFlag_eq⟩
          rw [$isHfreeName:ident, decide_eq_true_eq]
          rw [unlabel_emptyType, ← x.toSym2EmptyTypedFlag_toFlag_eq] at hx
          exact (FlagAlgebras.Compute.supergraphFamily_filter_iff $fStx x.toSym2EmptyTypedFlag).mp hx
    ))

  -- Underlying multiset of `flagSetHfree` = the explicit free-flag list (for the expand tactics).
  let flagSetValEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_0_0_{tag}_val_eq")
  let freeBridgeTerms : Array (TSyntax `term) := freeIndices.toArray.map (fun i =>
    mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{i}"))
  elabUnlessDefined flagSetValEqName.getId (← `(
      theorem $flagSetValEqName :
          (($flagSetName : Finset (FlagAlgebras.FlagWithSize ∅ₜ $(Quote.quote n))).val
            = [ $freeBridgeTerms,* ]) := by
        have hnodup : ([ $freeSym2Terms,* ] : List (Sym2EmptyTypedFlag $(Quote.quote n))).Nodup := by
          native_decide
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

  logInfo s!"Generated {freeIndices.length} subgraph-{tag}-free empty-typed flags (n = {n}); \
flagSetHfree_{n}_0_0_{tag} completeness + capstone-filter bridge + val_eq proved."

-- `generate_forbid_free_flags n k m Forbid`: the σ-typed analogue (flag size `n`
-- first, matching `generate_flags n k m`). Emits only the `Forbid`-free σ-typed
-- `n`-vertex flags `Flag_n_k_m_i` (those whose underlying graph is `Forbid`-free),
-- their `unlabel`/`downward` bridges, and the completeness
-- `flagSetHfree_n_k_m_<Forbid> = univ.filter (forbid-free)`. Requires the underlying
-- `Forbid`-free empty-typed flags (run `generate_forbid_free_empty_typed_flags n Forbid`
-- first).
elab "generate_forbid_free_flags" nStx:num kStx:num mStx:num gStx:ident : command => do
  let k := kStx.getNat
  let m := mStx.getNat
  let n := nStx.getNat
  let tag := gStx.getId.toString

  let (gIdent, gEqName) ← resolveForbidGraph tag
  let gEqIdent := mkIdent gEqName
  let forbidFlag ← forbidFlagIdentOfToFinFlagEq gEqName
  let (r, idx) ← parseFlagRIdx forbidFlag.getId.toString
  let forbidSym2 := mkIdent (Name.mkSimple s!"Sym2Flag_{r}_0_0_{idx}")

  unless (← isDeclaredInScope (Name.mkSimple s!"Flag_{n}_0_0_0")) do
    throwError s!"`generate_forbid_free_flags {n} {k} {m} {tag}` requires the underlying \
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
        have hq : (Quotient.mk (FlagAlgebras.Compute.Sym2GraphSetoid $(Quote.quote n)) G)
            = Quotient.mk (FlagAlgebras.Compute.Sym2GraphSetoid $(Quote.quote n)) G' :=
          Quotient.sound hGG'
        simp only [$isHfreeGraphName:ident, hq]))

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

/-- `generate_pruned_forbid_free_flags n k m F`: the **edge-based** σ-typed analogue of
`generate_pruned_forbid_free_empty_typed_flags`. `F` is a `Sym2Graph mF` *term* (no canonical
forbidden flag, no tag); the forbid-free split is **induced** (`inducedContains F` on each flag's
underlying graph), and the forbid-free test is the analytic density on `⟦F⟧`. Requires the
underlying `F`-free empty-typed flags (run `generate_pruned_forbid_free_empty_typed_flags n F`
first). Completeness routes through the graph-level `genFlagsHfree` + `genFlagsHfree_toFinset_eq`. -/
elab "generate_pruned_forbid_free_flags" nStx:num kStx:num mStx:num fStx:ident : command => do
  let k := kStx.getNat
  let m := mStx.getNat
  let n := nStx.getNat
  let tagFull := toString fStx.getId
  let tag := (tagFull.splitOn ".").getLastD tagFull

  unless (← isDeclaredInScope (Name.mkSimple s!"Flag_{n}_0_0_0")) do
    throwError s!"`generate_pruned_forbid_free_flags {n} {k} {m} {tag}` requires the underlying \
{tag}-free empty-typed flags. Add `generate_pruned_forbid_free_empty_typed_flags {n} {tag}` first."

  let allTypeEdges ← evalCanonicalEdgeLists k
  let typeEdges := allTypeEdges.getD m []
  let flagData ← evalFlagDataRows k m n
  let count := flagData.length

  -- A σ-typed flag is forbid-free iff its underlying graph (canonical index `entry.1`) is
  -- induced-`F`-free, read off the same induced mask the empty-typed generator uses.
  let freeMask ← evalInducedFreeMask n fStx
  let freeArr := ((List.range count).filter (fun i =>
    freeMask.getD ((flagData.getD i (0, [], [], 0, 0)).1) false)).toArray

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

  -- Emit the forbid-free σ-typed flag constants + their `unlabel` bridges (forbid-independent;
  -- identical to `generate_forbid_free_flags`).
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

  -- Batched downward normalizing factors (forbid-independent).
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

  -- Completeness, in the bridge's predicate form (forbid is the term `⟦F⟧`, no canonical flag).
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
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ ⟦$fStx⟧ (S.toUnderlying) = 0)))

  elabUnlessDefined isHfreeGraphName.getId (← `(
      def $isHfreeGraphName (G : FlagAlgebras.Compute.Sym2Graph $(Quote.quote n)) : Bool :=
        decide (FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ ⟦$fStx⟧
          (Quotient.mk (FlagAlgebras.Compute.Sym2GraphSetoid $(Quote.quote n)) G) = 0)))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset))

  -- Genuine-pruning σ-typed completeness (Task 8b): the named free set equals the labeled flags built
  -- over the *pruned* graph reps `augRepsFreeB (qFree F)` — no forbidden graph is materialized, and the
  -- `native_decide` runs the cheap combinatorial `qFree` over the pruned reps rather than the density
  -- filter over the full `genSym2GraphsDedup`. Closed by `genFlagsHfreePruned_toFinset_eq`; `hcompat`
  -- matches the density-based `isHfree` to `qFree` via the Task-4 bridge (`qFree_eq_density_decide`).
  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := by
        have hpruned : $sym2SetName
            = (FlagAlgebras.Compute.genFlagsHfreePruned $typeTerm $(Quote.quote n)
                (FlagAlgebras.Compute.qFree $fStx)).toFinset := by
          native_decide
        rw [hpruned]
        exact FlagAlgebras.Compute.genFlagsHfreePruned_toFinset_eq (FlagAlgebras.Compute.qFree $fStx)
          $isHfreeName
          (fun {_ _ _} h => FlagAlgebras.Compute.qFree_iso $fStx h)
          (fun {_ _} h => FlagAlgebras.Compute.qFree_restrict $fStx h)
          (FlagAlgebras.Compute.qFree_hq0 $fStx (by decide))
          (fun Glab => by
            rw [FlagAlgebras.Compute.qFree_eq_density_decide]; rfl)))

  elabUnlessDefined flagSetName.getId (← `(
      noncomputable def $flagSetName : Finset (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n)) :=
        ($sym2SetName).map ⟨Sym2Flag.toFlag, fun a b h => Sym2Flag.toFlag_injective a b h⟩))

  elabUnlessDefined flagSetEqName.getId (← `(
      theorem $flagSetEqName :
          $flagSetName
            = Finset.univ.filter (fun F' =>
                flagDensity₁ (Sym2EmptyTypedFlag.toFlag ⟦$fStx⟧) (unlabel F') = 0) := by
        rw [$flagSetName:ident, $sym2SetEqName:ident]
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨S, hS, hSx⟩
          rw [← hSx, FlagAlgebras.Compute.Sym2Flag.unlabel_toFlag_eq]
          show flagDensity₁ (Sym2EmptyTypedFlag.toFlag ⟦$fStx⟧) (S.toUnderlying).toFlag = 0
          rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
          exact of_decide_eq_true hS
        · intro hx
          refine ⟨x.toSym2Flag, ?_, x.toSym2Flag_toFlag_eq⟩
          show $isHfreeName _ = true
          rw [$isHfreeName:ident, decide_eq_true_eq, ← flagDensity₁_eq_sym2EmptyTypeFlagDensity₁,
            ← FlagAlgebras.Compute.Sym2Flag.unlabel_toFlag_eq, x.toSym2Flag_toFlag_eq]
          exact hx))

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

  logInfo s!"Generated {freeArr.size} {tag}-free σ-typed flags (n = {n}, type {k}_{m}) edge-based \
(induced); flagSetHfree_{n}_{k}_{m}_{tag} completeness + val_eq proved."

/-- `generate_subgraph_free_flags n k m F`: the **subgraph**-forbidding σ-typed analogue. Identical
flag/type/downward emission to `generate_pruned_forbid_free_flags`; only the forbid-free split
(`subgraphContains`), the analytic test `isHfree` (zero density of every supergraph of `F`), the
completeness (direct `native_decide`), and the `FinFlag`-bridge `flagSetHfree…_eq` (to the subgraph
capstone's filter, via `supergraphFamily_filter_iff`) differ. Requires the subgraph-`F`-free
empty-typed flags first (`generate_subgraph_free_empty_typed_flags n F`). -/
elab "generate_subgraph_free_flags" nStx:num kStx:num mStx:num fStx:ident : command => do
  let k := kStx.getNat
  let m := mStx.getNat
  let n := nStx.getNat
  let tagFull := toString fStx.getId
  let tag := (tagFull.splitOn ".").getLastD tagFull

  unless (← isDeclaredInScope (Name.mkSimple s!"Flag_{n}_0_0_0")) do
    throwError s!"`generate_subgraph_free_flags {n} {k} {m} {tag}` requires the underlying \
subgraph-{tag}-free empty-typed flags. Add `generate_subgraph_free_empty_typed_flags {n} {tag}` first."

  let allTypeEdges ← evalCanonicalEdgeLists k
  let typeEdges := allTypeEdges.getD m []
  let flagData ← evalFlagDataRows k m n
  let count := flagData.length

  let freeMask ← evalSubgraphFreeMask n fStx
  let freeArr := ((List.range count).filter (fun i =>
    freeMask.getD ((flagData.getD i (0, [], [], 0, 0)).1) false)).toArray

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

  let freeSym2Terms : Array (TSyntax `term) := freeArr.map (fun i =>
    mkIdent (Name.mkSimple s!"Sym2Flag_{n}_{k}_{m}_{i}"))
  let isHfreeName := mkIdent (Name.mkSimple s!"isHfree_{n}_{k}_{m}_{tag}")
  let sym2SetName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_{k}_{m}_{tag}")
  let sym2SetEqName := mkIdent (Name.mkSimple s!"sym2FlagSetHfree_{n}_{k}_{m}_{tag}_eq")
  let flagSetName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}")
  let flagSetEqName := mkIdent (Name.mkSimple s!"flagSetHfree_{n}_{k}_{m}_{tag}_eq")

  elabUnlessDefined isHfreeName.getId (← `(
      def $isHfreeName (S : Sym2Flag $typeTerm $(Quote.quote n)) : Bool :=
        decide (∀ s ∈ FlagAlgebras.Compute.supergraphSym2List $fStx,
          FlagAlgebras.Compute.sym2EmptyTypeFlagDensity₁ s (S.toUnderlying) = 0)))

  elabUnlessDefined sym2SetName.getId (← `(
      def $sym2SetName : Finset (Sym2Flag $typeTerm $(Quote.quote n)) :=
        ([ $freeSym2Terms,* ] : List (Sym2Flag $typeTerm $(Quote.quote n))).toFinset))

  elabUnlessDefined sym2SetEqName.getId (← `(
      theorem $sym2SetEqName :
          $sym2SetName = Finset.univ.filter (fun S => $isHfreeName S = true) := by native_decide))

  elabUnlessDefined flagSetName.getId (← `(
      noncomputable def $flagSetName : Finset (FlagAlgebras.FlagWithSize $flagTypeName $(Quote.quote n)) :=
        ($sym2SetName).map ⟨Sym2Flag.toFlag, fun a b h => Sym2Flag.toFlag_injective a b h⟩))

  elabUnlessDefined flagSetEqName.getId (← `(
      theorem $flagSetEqName :
          $flagSetName
            = Finset.univ.filter (fun F' =>
                ∀ D ∈ FlagAlgebras.Compute.supergraphFamily $fStx,
                  flagDensity₁ D.2 (unlabel F') = 0) := by
        rw [$flagSetName:ident, $sym2SetEqName:ident]
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨S, hS, hSx⟩
          rw [$isHfreeName:ident, decide_eq_true_eq] at hS
          rw [← hSx, FlagAlgebras.Compute.Sym2Flag.unlabel_toFlag_eq]
          exact (FlagAlgebras.Compute.supergraphFamily_filter_iff $fStx (S.toUnderlying)).mpr hS
        · intro hx
          refine ⟨x.toSym2Flag, ?_, x.toSym2Flag_toFlag_eq⟩
          rw [$isHfreeName:ident, decide_eq_true_eq]
          rw [← x.toSym2Flag_toFlag_eq, FlagAlgebras.Compute.Sym2Flag.unlabel_toFlag_eq] at hx
          exact (FlagAlgebras.Compute.supergraphFamily_filter_iff $fStx (x.toSym2Flag.toUnderlying)).mp hx))

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

  logInfo s!"Generated {freeArr.size} subgraph-{tag}-free σ-typed flags (n = {n}, type {k}_{m}); \
flagSetHfree_{n}_{k}_{m}_{tag} completeness + capstone-filter bridge + val_eq proved."

end Flags.Densities
