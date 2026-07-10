# Design: the hom→graphon representation (Phase 4)

*Status: design frozen 2026-07-10 (probe verified against the repo and pinned Mathlib); no
implementation started.  Companion of the shipped Phase 2 (`GraphonHom.lean`, the graphon→hom
half).  Read `METATHEORY_WORKLOG.md` § "TO RESUME" for where this sits in the campaign.*

## Goal

For every unlabelled limit functional, produce a representing graphon:

```
theorem exists_graphon_rep (φ : PositiveHom ∅ₜ) :
    ∃ W : Graphon, ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ.coe F
```

together with a **rooted transport** layer turning rooted slice identities into a.e. kernel
hypotheses on `W`.  These are the two inputs that `thm:k4free-p4-tripartite` (Thm 102,
`paper.tex:5035`) and `cor:top-endpoint-recovery` (Cor 106, `paper.tex:5138`) consume; with them,
the `huniq`-style hypotheses of `SliceRecovery.lean` discharge.

## What the consumers actually need (probe finding)

Reading the proofs of Thm 102 / Cor 106 (`paper.tex:5044–5059`, `:5146–5151`):

* **(I) Existence only.**  The proofs start "let `W` represent a point of `Y_{P4}`" and then work
  entirely on the graphon side (`GraphonRigidity`'s `r3_rigidity` / `slice_rigidity` already do
  all uniqueness work combinatorially).  `K₄`-freeness of `W` is explicitly not needed
  (`paper.tex:5051`).  **Full Lovász–Szegedy (injectivity up to weak isomorphism) is NOT
  required** — grep across `MetaTheory/` confirms no downstream use.
* **(II) Rooted transport** (previously unnamed in the worklog).  The slice equations
  (`ParametricP4Slice.lean:263–340`: `parametricP4_eta_equation`, `parametricP4_tau_symm`,
  `parametricP4_tau_equation`) are identities of **rooted** homomorphisms
  `χ ∈ relSσ … FlagType_2_1`, while `Graphon.r3_rigidity` consumes **a.e. kernel** hypotheses
  (`Rτ = 0`, `Rη = 0`).  Bridging them needs a graphon-side rooted-view measure identified with
  the abstract extension measure `ℙ[φ₀]` (`RandomHom.lean:1176–1192`).  This is separate work
  from (I) and can ship first.

## Route comparison for (I) (Mathlib evidence, pinned toolchain)

| Route | Mathlib support | Verdict |
|---|---|---|
| (a) Exchangeability / de Finetti / Aldous–Hoover | **absent entirely** (grep: no `deFinetti`, `Exchangeable`, `Hewitt`, `Aldous`, `Hoover`) | open-ended research risk — NO |
| (b) Szemerédi regularity | full finite regularity lemma exists (`Combinatorics/SimpleGraph/Regularity/*`), but counting lemma is triangle-only, no cut norm, no step-graphon layer | partial — usable as template only |
| (c) Cut-metric compactness | `cutNorm`/`cutDistance` absent; Banach–Alaoglu present but insufficient for multilinear density functionals; **Doob martingale convergence present** (`Probability/Martingale/Convergence.lean`) | the martingale variant is the engine — YES (as part of (d)) |
| (d) Sampling + subsequence | `positiveHom_as_flagSeq_limit` (`FlagAlgebra/FlagSequence.lean:1019`) **already proved, sorry-free**: every `PositiveHom σ` is a flag-sequence limit | **RECOMMENDED entry point** |
| (e) Kolmogorov extension + AH | only kernel-driven projective limits (`IonescuTulcea`), no general Kolmogorov extension; AH absent | NO |

**Recommended route: (d) + martingale limit.**  Use `positiveHom_as_flagSeq_limit` to realise `φ`
as the limit of a density-convergent sequence of finite graphs; build step graphons over refining
partitions; take the a.e./L¹ limit via Doob martingale convergence; prove a from-scratch general
counting/domination lemma (Mathlib's `Triangle/Counting.lean` is the template) to pass every
test-graph density to the limit.

## Prerequisites already in place

* Total mass: `sum_positiveHom_basisVector_flagWithSize_eq_one` (`FlagAlgebra/PositiveHom.lean:97`)
  — the profile restricted to `n`-vertex flags is a probability distribution, for *every*
  `PositiveHom`.
* Marginal consistency = `zeroSpaceProp`; exchangeability is definitional (flags are iso classes).
* Graphon-side density calculus: `GraphonInducedDensity.lean` (extension partition, block product,
  relabelling invariance) — the same identities the limit graphon must satisfy.
* Measure identification without unfolding `Classical.choose`:
  `measure_eq_of_integral_flag_eq` (`MeasureUniqueness.lean:60`), the pattern used by
  `complHomeo_map_eq`.

## Module decomposition and estimates

**Sub-project A — rooted transport (II).  Ship first: 1–2 sessions, low–medium risk.**
1. `GraphonRootedHom.lean` — rooted analogue of `graphonProfileFun`/`graphonHom`: pin the root
   vertices (edge type `τ` / non-edge type `η`), reuse the subset-averaging technique of
   `GraphonHom.lean` verbatim; conditional profile `Graphon → (roots ↦ I) → PositiveHom σ`-style
   values.
2. `GraphonRootedMeasure.lean` — the graphon-side rooted-view measure on `PositiveHomSpace σ`;
   identify with `ℙ[φ₀]` via `measure_eq_of_integral_flag_eq`; pass "holds on `relSσ`" to
   "holds a.e." via `Measure.support_mem_ae` (as in `RelativeSupport.lean:98`).

**Sub-project B — existence (I).  4–8 sessions; treat as its own campaign with a checkpoint.**
3. `GraphonStep.lean` — step graphons from finite graphs / partitions; densities of step graphons
   agree with finite densities (finite Fubini).
4. `GraphonCounting.lean` — the general counting/domination lemma (test-graph densities are
   continuous under the relevant convergence of kernels).  **Checkpoint after this module** —
   reassess before attempting 5.
5. `GraphonMartingaleLimit.lean` — **the single riskiest piece**: sequential compactness of the
   graphon space along refining partitions (Lovász Thm 11.21 analogue) via Doob martingale
   convergence; simultaneous convergence of countably many test densities by diagonalisation;
   a.e.-vs-everywhere bookkeeping.  Est. 1500–3000+ lines, no Mathlib precedent.
6. `GraphonRepresentation.lean` — assembly: `exists_graphon_rep`, then the Thm 102 / Cor 106
   discharges replacing the `huniq` hypotheses in `SliceRecovery.lean`.

## Non-goals

Full Lovász–Szegedy injectivity / weak-isomorphism uniqueness; cut-metric theory for its own
sake; any use of exchangeability theory.  If sub-project B stalls at module 5, sub-project A
alone still upgrades the conditional results (the rooted identities become checkable against any
*hypothesised* representative), and the `hrep : ∃ W, …` named-hypothesis form remains available
as an interim tier, consistent with the repo's classical-input convention.
