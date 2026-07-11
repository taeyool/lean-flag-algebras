# Design note: retiring the `hrep` hypothesis (hom→graphon existence)

This is the design for the one remaining *optional* piece of the graphon layer: proving the
Lovász–Szegedy **existence** half of the representation theorem, so that the named hypothesis
`hrep` can be discharged rather than assumed.  Everything else in the hom↔graphon story is
formalised; this note records why that last step is hard and what a proof would take.

## Target

```
theorem exists_graphon_rep (φ : PositiveHom ∅ₜ) :
    ∃ W : Graphon, ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ.coe F
```

Every unlabelled limit functional is represented by some graphon.  This is the sole content of
the named hypothesis

```
hrep : ∀ φ₀ : PositiveHom ∅ₜ, ∃ W : Graphon, ∀ F, graphonProfileFun W F = φ₀.coe F
```

that appears (as an explicit input, in the standing convention of `hES`/`hZykov`) in the
existence forms `k4free_p4_tripartite_of_rep_exists` (`GraphonRepresentation.lean`) and
`parametricP4_top_endpoint_of_rep_exists` (`GraphonParametricTransport.lean`).  The
*representative-quantified* forms of Thm 102 and Cor 106 need no such input and are
unconditional; `hrep` is only what upgrades them to the paper's "every point of the slice is
the tripartite graphon" phrasing.

## Why only existence is needed

The graphon-side rigidity is already complete and unconditional: `Graphon.slice_rigidity` and
the rooted transport (`GraphonKernelTransport`, `GraphonParametricTransport`) turn the slice
identities into the a.e. kernel hypotheses and run the rigidity argument.  Full Lovász–Szegedy
*injectivity* (uniqueness up to weak isomorphism) is never used downstream.  So the only gap is
the plain existence of a representing graphon.

## The gap is graphon-space compactness

The range of `graphonHomPoint` is already proved **dense** in the compact metric space
`PositiveHomSpace ∅ₜ` (`exists_graphonHomPoint_seq_tendsto` in `GraphonCounting`, via the
step-graphon counting lemma and `positiveHom_as_flagSeq_limit`).  Since
`positiveHomSpace_isClosed` gives compactness, `exists_graphon_rep` is *equivalent* to the
single statement

```
IsClosed (Set.range (graphonHomPoint : Graphon → PositiveHomSpace ∅ₜ))
```

(closed + dense ⇒ everything).  So the campaign has one frozen target: closedness of the
graphon-hom range, equivalently sequential compactness of graphon space along a convergent
finite-graph sequence — the classical Lovász–Szegedy compactness theorem.

## Why the naive route fails

The tempting route — realise `φ` as a limit of step graphons `stepGraphon Gₙ` (density is
already in hand), take an a.e. limit kernel by Doob martingale convergence — has a real gap.
Mathlib's martingale theorems (`Submartingale.ae_tendsto_limitProcess`, `tendsto_ae_condExp`)
need the kernels to be conditional expectations of one fixed object along an increasing
filtration on a *single* space.  A sequence of step graphons for combinatorially unrelated
`Gₙ` does **not** satisfy the averaging identity `Wₙ = E[Wₙ₊₁ ∣ ℱₙ]` even when the cell
partitions are nested — nesting partition *geometry* is not nesting partition *values*.  The
obstruction is genuine: hide a bipartite kernel of density `½` inside one coarse cell, and its
coarse average predicts triangle density `⅛` where the truth is `0`.  A fine checkerboard, by
contrast, is quasirandom and harmless — so the fix cannot be any `n`-independent nesting
scheme; the partition must *adapt to each graph's structure*, which is exactly what weak
regularity provides and nothing weaker does.

## The honest route (Frieze–Kannan weak regularity)

The standard proof (Borgs–Chayes–Lovász–Sós–Vesztergombi) uses weak regularity plus a diagonal
martingale on a fixed filtration.  Adapted to this repo:

| Piece | Content | Mathlib support | Est. lines |
|---|---|---|---|
| cut norm | `‖W‖□`, boundedness, monotonicity | absent (no `cutNorm`/`cutDistance`) | 100–200 |
| weak (Frieze–Kannan) regularity for kernels | measurable partition into `≤ 4^{1/ε²}` cells with `‖W − W_P‖□ ≤ ε` | `condExpL2` orthogonal-projection engine exists; the finite `Equitabilise` cost centre vanishes for kernels; Mathlib's packaged `szemeredi_regularity` is a shape template only | 400–700 |
| FK counting lemma | `\|t(F,W) − t(F,W′)\| ≤ e(F)·‖W−W′‖□` for general `F` | Mathlib has only the triangle case | 250–450 |
| nested-diagonal martingale | continue the energy increment across accuracy levels, diagonalise the cell-density data, invoke `Submartingale.ae_tendsto_limitProcess` | martingale convergence present | 350–600 |
| assembly | `exists_graphon_rep` from density + closedness | dominated convergence | 200–400 |

Total ≈ **1300–2350 lines**; treat as its own project with checkpoints after (cut norm + weak
regularity), (counting lemma), and (martingale-diagonal).  Partition convention: measurable
`I → Fin K` maps (the `cellIdx` convention of `GraphonStep`), feeding generated σ-algebras to
Mathlib only at the `condExpL2`/filtration boundary.

## Non-goals

Full Lovász–Szegedy injectivity / weak-isomorphism uniqueness; cut-metric theory beyond what
the counting lemma needs; any use of exchangeability / Aldous–Hoover theory (all absent from
Mathlib and not required).  Until the campaign is run, `hrep` remains an explicit named
hypothesis, consistent with the treatment of the other classical inputs.
