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

**Sub-project A — rooted transport (II).  Ship first: 2–3 sessions (module 1 is
GraphonHom-sized; the 1–2 estimate held only for module 2).**

> **STATUS: COMPLETE — shipped 2026-07-11** (sixth/seventh sessions, 2026-07-10/11). The design
> below was carried out as **five** modules rather than the two anticipated here — the "module 1"
> plan below split into `StdRootedBridge` (module 0, the two-root analogue of
> `EmptyTypeGraphBridge`) + `GraphonRootedDensity` (module 1a, the density calculus) +
> `GraphonRootedHom` (module 1b, the conditional homomorphism itself), and "module 2" split into
> `GraphonRootedMeasure` (module 2a, the measure identification) + `GraphonKernelTransport`
> (module 2b, the capstone kernel dictionary + transport). Capstone theorem:
> **`k4freeP4_graphon_tripartite`** (`GraphonKernelTransport.lean`) — any graphon whose `φ_W` lies
> in the `K₄`-free `P₄`-slice (both root types of positive mass) is a.e. the balanced complete
> tripartite graphon, i.e. `Graphon.r3_rigidity` with both a.e. kernel hypotheses discharged —
> the graphon-side content of `thm:k4free-p4-tripartite` (Thm 102). All five modules sorry-free,
> Tier-1 except the last three theorems of `GraphonKernelTransport`
> (`k4freeP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero`/`_tripartite`, Tier-2 — they consume the
> `k4freeP4_*` slice equations). Three adversarial audits, all verdict SHIP (12/12 FAITHFUL for
> modules 0–1, 8/8 FAITHFUL for module 2). Full details, the technical notes, and the audit/build
> record are in `METATHEORY_WORKLOG.md` § **"Sub-project A: the rooted transport — DONE"**. The
> design text below is kept for the record (it correctly anticipated the mathematical content and
> caught the one indexing bug in advance; only the module count differs from what shipped).
> **Sub-project B (existence, below) is now the sole remaining piece of Phase 4.**

*Design detail frozen 2026-07-10 after the rooted-API dossier probe; heed the corrections below —
the probe's own first sketch had a genuine bug.*

1. `GraphonRootedHom.lean` — the rooted conditional homomorphism.  Key decisions:
   * **Index set (bug fix): sum over STANDARD-ROOTED graphs only.**  The rooted profile at
     pinned samples `u v : I` is
     `aᵤᵥ(F) = (∑_{G std-rooted, ⟦mkStdRooted G⟧ = F.2} unnormRootedDensity W G u v) / rootWeight`,
     where the sum ranges over `G : SimpleGraph (Fin F.1)` satisfying
     `RootCompatible σ hn G := ∀ a b : Fin 2, σ.Adj a b ↔ G.Adj (Fin.castLE hn a) (Fin.castLE hn b)`
     and `mkStdRooted` equips `G` with the `Fin.castLE`-embedding as `type_embed`.  Summing over
     the whole quotient class `{H : LabeledGraph σ _ // ⟦H⟧ = F.2}` (as in the probe's sketch) is
     WRONG: pinning coordinates `0,1` only computes the rooted density of graphs whose roots sit
     at `0,1`.
   * **Host convention: general `n` with `hn : 2 ≤ n` and roots at `Fin.castLE hn 0/1`** —
     avoids `Fin (n+2)` offset arithmetic and matches the `castLE` machinery of Phase 2.
   * **Unnormalised density integrates over ALL `n` coordinates** with the root coordinates
     overridden (`Function.update`-style pinning); the two dummy coordinates integrate out on the
     probability space.  This keeps the extension/marginalisation lemmas uniform (no `Fin (n−2)`).
   * `rootWeight W σ u v := adjWeight W (σ.Adj 0 1) u v` (`= W(u,v)` at `τ`, `1−W(u,v)` at `η`);
     `RootAdmissible := 0 < rootWeight`.  The `(0,1)`-pair factor of the unnormalised density of a
     std-rooted graph IS `rootWeight`, so division implements the conditioning exactly:
     `oneProp` = `rootWeight/rootWeight`; in `mulProp` the left side carries `rootWeight⁻²` and the
     glued sum carries `rootWeight·(∏₁)(∏₂)` (the root pair is SHARED at `n₀ = 2`), so the
     normalisation cancels — verified by hand, record in the module docstring.
   * The Props run by the Phase-2 subset-averaging scheme with permutations of `Fin ℓ` **fixing
     the two roots**: need the root-fixing analogues of `exists_perm_comp_emb(_pair)` (same
     complement construction, pinned points) and root-fixing relabelling invariance of the
     unnormalised density.  The counting bridges are ALREADY GENERAL-σ
     (`flagDensity₁_eq_subset_count_div`, `flagDensity₂_eq_subset_count_div`) — no new counting
     infrastructure; what is new is the std-rooted analogue of `EmptyTypeGraphBridge`
     (std-rooted class equality iff root-preserving graph iso; every rooted flag class has a
     std-rooted representative; subsets in the count formulas contain the roots).
   * Generated-type transports `FlagType_2_1 = ⊤` / `FlagType_2_0 = ⊥` exist only as `private`
     lemmas in `TuranSliceIdentities.lean` (:1361/:1366) — re-derive locally (≈5 lines each,
     `ext` + `Sym2FlagType.toFlagType_adj_iff` + `decide`).
2. `GraphonRootedMeasure.lean` — the rooted-view measure
   `Measure.map (fun z : I×I => posHomPoint (graphonRootedHom W σ z.1 z.2 _))` of the
   `rootWeight`-weighted normalised measure on `I × I`; identify with `ℙ[graphonHom W]` via
   `measure_eq_of_integral_flag_eq` (`MeasureUniqueness.lean:60` — needs only integral agreement
   on every `f : FlagAlgebra σ`; the LHS reduces by Fubini to an unrooted density of the downward
   average, so the bridge identity is `∫∫ rootWeight·aᵤᵥ(F) = φ_W-value of ⟦F⟧₀`, a
   `downwardNormalizingFactor` computation).  Then `support_subset_relSσ` +
   `Measure.support_mem_ae` (pattern at `RelativeSupport.lean:95-99`) turns the
   `ParametricP4Slice` equations (`:263-340`, stated on `relSσ … FlagType_2_0/2_1`) into
   `∀ᵐ z : I×I` kernel statements, landing on `Rtau_eq_zero_iff_ae`/`Reta_eq_zero_iff_ae`
   (`GraphonMoments.lean:583-616`) — the exact hypothesis shapes of `Graphon.r3_rigidity`
   (`GraphonRigidity.lean:799`).  Paper's prescribed dictionary (`paper.tex:4861-4875`): at an
   ordered edge root, `a_τ = d(x)−c(x,y)`, `b_τ = d(y)−c(x,y)`, `g_τ = c(x,y)`; at an ordered
   non-edge root, `z_η = 1−d(x)−d(y)+c(x,y)`, `g_η = c(x,y)`.
   Sub-project A takes `hrep : graphonHomPoint W = posHomPoint φ₀` as a NAMED HYPOTHESIS, so it
   ships independently of sub-project B and upgrades the conditional results on its own.
   Admissibility (`RootAdmissible` fails on a `(u,v)`-set) is null under the weighted measure but
   must be threaded through the map (junk-value the hom outside admissibility; the pushforward
   only sees the conull admissible set).  Joint measurability of `(u,v) ↦` the rooted point in
   the product topology follows the `measurable_inducedWeight`/Fubini precedent.

**Sub-project B — existence (I).  4–8 sessions; treat as its own campaign with a checkpoint.**

*Plan revised 2026-07-11 after the module-3/4 design probe.  Two structural findings:*

* ***The density/closedness reframing.***  `positiveHomSpace_isClosed`/compactness
  (`FlagSequence.lean:483-512`) are already in place, so modules 3–4 chained prove **density**
  of `Set.range graphonHomPoint` in `PositiveHomSpace ∅ₜ` (every `φ` is a pointwise limit of
  step-graphon points, via `positiveHom_as_flagSeq_limit` + the counting lemma), and
  `exists_graphon_rep` becomes *equivalent* to the single frozen statement
  `IsClosed (Set.range graphonHomPoint : Set (PositiveHomSpace ∅ₜ))` — adopt THAT as module 5's
  target, not the vaguer "sequential compactness along refining partitions".
* ***The martingale gap (do not ignore).***  The route recommendation "nested partitions +
  Doob" is NOT free as stated: Mathlib's Doob theorems
  (`Probability/Martingale/Convergence.lean`: `tendsto_ae_condExp` :426,
  `Submartingale.ae_tendsto_limitProcess` :208) need the kernels to be conditional expectations
  of one fixed function w.r.t. an increasing filtration on a single space; a sequence
  `stepGraphon Gₙ` for combinatorially unrelated `Gₙ` does not satisfy the averaging identity
  `Wₙ = E[Wₙ₊₁ | ℱₙ]` even with nested cell geometry — nesting the partition geometry is not
  nesting the *values*.  The repo's §5 blow-up machinery solves only the within-one-graph
  refinement problem.  Candidate assets for the fix: Mathlib's finite Szemerédi regularity
  lemma (`Combinatorics/SimpleGraph/Regularity/Lemma.lean:76`, energy-increment partitions)
  adapted to a cross-graph nested/value-compatible construction.  **A design-only spike is
  REQUIRED at the module-4→5 checkpoint** before writing any module-5 Lean: choose between
  (a) regularity-lemma adaptation, (b) another device producing a genuine fixed-space
  martingale, or (c) a direct attack on the `IsClosed` reframing.

3. `GraphonStep.lean` — **SHIPPED 2026-07-11** (sorry-free, Tier-1, audited): step graphons:
   `cellIdx N : I → Fin N` (floor-based, clamped at `x = 1`), `stepGraphon G : Graphon`
   (indicator kernel), measurability + cell volume `1/N`, and the pointwise indicator
   identity `inducedWeight (stepGraphon G) H c = [G.comap (cellIdx N ∘ c) = H]` — note the
   shipped identity uses **literal graph equality** (the weight product detects per-pair
   adjacency on the common vertex set), not the flag-class equality of the earlier sketch.
4. `GraphonCounting.lean` — **SHIPPED 2026-07-11** (sorry-free, Tier-1, audited 7/7): the
   counting lemma with the probe's **explicit constant**:
   `|graphonProfileFun (stepGraphon G) F − flagDensity₁ F.2 (graphFlag G)| ≤ F.1·(F.1−1)/N`
   (exact tuple-count formula `profile = #{realising cell tuples}/Nⁿ`; injective cell-tuples
   ↔ the subset count of `flagDensity₁_graphFlag` times `n!`; non-injective tuples ≤
   `C(n,2)/N` by the union bound; the `descFactorial/N^n ≥ 1 − C(n,2)/N` bound proved from
   scratch), then `tendsto_graphonHomPoint_stepGraphon` and the payoff
   `exists_graphonHomPoint_seq_tendsto (φ) : ∃ V : ℕ → Graphon, Tendsto (graphonHomPoint ∘ V) …`
   — **density of the graphon-hom range: DONE**.  **WE ARE NOW AT THE CHECKPOINT** — run the
   module-5 design spike; do not proceed on the unrepaired martingale route.
5. **CHECKPOINT SPIKE VERDICT (2026-07-11): Route 3 adopted; the regularity campaign is
   deferred as a separately-budgeted project.**  The spike (i) *confirmed* the martingale gap
   — the correct counterexample is the **hidden-bipartite-block** kernel (a fine checkerboard
   is quasirandom and harmless; a bipartite kernel of density `1/2` hidden inside one coarse
   cell predicts triangle density `1/8` but has `0`), and no `n`-independent nesting scheme
   fixes it because the partition must *adapt to each graph's structure* — exactly what
   (weak) regularity buys and nothing weaker does; (ii) costed the honest repair
   (Frieze–Kannan weak regularity for kernels + FK counting lemma + a
   continue-the-energy-increment nested chain + diagonal + genuine Doob martingale):
   cut norm ~100–200 lines (absent from Mathlib), weak regularity ~400–700 (the
   `condExpL2`/orthogonal-projection engine exists; the finite `Equitabilise` cost centre
   disappears for kernels), FK counting ~250–450 (Mathlib has only the triangle case),
   nested-diagonal-martingale ~350–600 (`Submartingale.ae_tendsto_limitProcess` applies;
   Mathlib's packaged `szemeredi_regularity` restarts per call and is not reusable as a
   dependency, only as a shape template), assembly ~200–400 — total ≈ 1300–2350 lines,
   **6–10 sessions**; checkpoints after (cut norm + weak regularity), (counting lemma),
   (martingale-diagonal).  Partition convention if/when built: measurable `I → Fin K` maps
   (the `cellIdx` convention), feeding generated σ-algebras to Mathlib only at the
   `condExpL2`/filtration boundary.  (iii) Observed that `exists_graphonHomPoint_seq_tendsto`
   already reduces the target to literal textbook Lovász–Szegedy for a convergent sequence of
   finite graphs.
6. `GraphonRepresentation.lean` — **the Route-3 closure** (shipped with this revision): the
   bridge `posHomPoint_eq_of_graphonProfileFun_eq`, the **unconditional paper-verbatim
   Thm 102** `k4free_p4_tripartite_of_represents` (*every* graphon representing a point of the
   slice is a.e. balanced tripartite — no `hrep` needed for this direction, which is the
   paper's actual quantifier), and the `hrep`-conditional existence form
   `k4free_p4_tripartite_of_rep_exists` with
   `hrep : ∀ φ₀, ∃ W, ∀ F, graphonProfileFun W F = φ₀.coe F` as the one named classical input
   of Phase 4 (standing convention of `hES`/`hZykov`; retire it by running the deferred
   regularity campaign of item 5).  Cor 106 CANNOT yet get the same treatment even under
   `hrep`: `Graphon.slice_rigidity` has no rooted-transport counterpart — a separate future
   module in the sub-project-A style is required first.

## Non-goals

Full Lovász–Szegedy injectivity / weak-isomorphism uniqueness; cut-metric theory for its own
sake; any use of exchangeability theory.  If sub-project B stalls at module 5, sub-project A
alone still upgrades the conditional results (the rooted identities become checkable against any
*hypothesised* representative), and the `hrep : ∃ W, …` named-hypothesis form remains available
as an interim tier, consistent with the repo's classical-input convention.

**Update (2026-07-11, post-shipping):** the interim tier that actually shipped is *not* the
`hrep : ∃ W, …` existential sketched above — it is the **shipped interface**
`hmem : posHomPoint (graphonHom W) ∈ k4freeP4Slice` together with the root-type admissibility
hypotheses `hστ`/`hση`, all as named hypotheses on `k4freeP4_graphon_tripartite`
(`GraphonKernelTransport.lean`). This is equivalent in spirit (a named hypothesis standing in for
"take a representative graphon") but syntactically different: it is a hypothesis *on the graphon
`W` itself* (any `W`, given as a bare `Graphon`, whose `φ_W` happens to land in the slice — `hmem`
is purely algebraic, `mem_Qσ_iff`, no graph-limit existential), rather than an existential
quantifier over slice points asserting a representative exists. See README Deviation 17 for the
full comparison against the paper's "let `W` represent a point of `Y_{P4}`". Once sub-project B
ships `exists_graphon_rep`, composing it with `k4freeP4_graphon_tripartite` recovers the paper
statement verbatim: apply `exists_graphon_rep` to any `φ₀ ∈ k4freeP4Slice` to get a representing
`W`, for which `hmem` holds by construction.
