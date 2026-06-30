# Density-counting refactor — use the fast same-size checker (plan & roadmap)

> **Working protocol.** Read this file at the start of each task on this refactor; at the
> end, update the status boxes and append a dated entry to the Progress Log. Mirrors the
> spirit of `FORBID_PRUNING_ROADMAP.md`. Status legend: `[ ]` not started · `[~]` in
> progress · `[x]` done · `[!]` blocked.
>
> **Status: PLANNING ONLY — no code changed yet.** This document is the result of a
> read-only investigation (2026-06-30) of `FlagAlgebra/Compute/{FlagDensity,FastIso,Basic}.lean`
> and `Flags/Densities/DensityThmGenerator.lean`.

## 1. Summary of the problem

The computable density counter `sym2FlagDensity₁` / `sym2FlagDensity₂`
(`FlagAlgebra/Compute/FlagDensity.lean`) is what **every generated pair-density and
forbid-density theorem re-derives under `native_decide`**. It evaluates by

1. enumerating **all `2ⁿ` vertex subsets** of the host `G` per pattern slot
   (`Sym2InducedLabeledSubgraph`'s `Fintype`), and
2. filtering each candidate with the **generic abstract labeled-graph isomorphism**
   `Nonempty ((Gl i).toLabeledSubgraph.coe ≃f (Hl i).toLabeledGraph)`, whose decision
   procedure (`Compute/Basic.lean`) enumerates **all `|W|^|V|` functions** between the two
   vertex types before filtering to injective / adjacency-preserving / type-preserving.

The repository already has an optimized, sound-and-complete, **same-size** isomorphism
checker — `isIsoFast_bool` in `Compute/FastIso.lean` (edge-count prefilter + `(n−k)!`
permutation search over non-type vertices) — but it is wired only into flag
**enumeration/dedup** (`FlagEnumeration.dedupStep`, `ForbidFreePruned`), **never into the
density counter**. `FlagDensity.lean` imports `FastIso` only for its type/`Decidable`
instances.

Tellingly, the **generation-time** RHS value is computed by `densityPF1F2GivenG`
(`DensityThmGenerator.lean`) with the *efficient* algorithm — iterate `combinations` of the
**correct size** and compare `canonicalLabeledForm`s — but the **kernel re-verification**
(`native_decide` on `sym2FlagDensity`) re-derives the same number through the slow
`2ⁿ`-subset + generic-`≃f` path. The fast algorithm is known; it is just not the one the
kernel checks.

## 2. Current code path (verbatim chain)

`flagDensity₁/₂ F G` → `sym2FlagDensity₁/₂ F G` (adequacy
`flagDensity₁_eq_sym2FlagDensity₁` / `flagDensity₂_eq_sym2FlagDensity₂`, FlagDensity.lean
~1077 / ~1150)
→ (Quotient.lift) `sym2InducedLabeledSubgraphListDensity Hl G` (≈ L952)
` = sym2InducedLabeledSubgraphListCount Hl G / multinomialCoefficient … `
→ `sym2InducedLabeledSubgraphListCount Hl G = (finsetOfSym2InducedLabeledSubgraphListIsoHl G Hl).card` (L762)
→ `finsetOfSym2InducedLabeledSubgraphListIsoHl = { Gl | predIsoSym2LabeledHl Hl Gl }` (L753),
over the `Fintype (Sym2InducedLabeledSubgraphList t G) = (Fin t → Sym2InducedLabeledSubgraph G)`.

Two cost-bearing pieces:

* **`Sym2InducedLabeledSubgraph G`** (L597) is `{ verts : Finset (Fin n) // G.type_verts ⊆ verts }`;
  its `Fintype` (L602) is `Finset.univ (Finset (Fin n))` `|>.filterMap …` — i.e. it enumerates
  **all `2ⁿ` subsets** and keeps those containing the type vertices. No size restriction.
* **`predIsoSym2LabeledHl`** (L716) = `(∀ i, Nonempty ((Gl i).toLabeledSubgraph.coe ≃f (Hl i).toLabeledGraph)) ∧ predDisjoint…`.
  Its `DecidablePred` (L725) decides each `Nonempty (… ≃f …)` through the **generic** stack in
  `Compute/Basic.lean`: `Fintype (G ≃f G')` filters `Fintype (graph ≃g)` which filters
  `Fintype (V ≃ W)` which filters `Fintype (V → W)` — and `Fintype (V → W)` materializes **all
  `|W|^|V|` functions**.

Generation side (`DensityThmGenerator.lean`): the generated theorem is
`flagDensity₂ Flag₀ Flag₁ Flag_host = value`, proved by
`rw [flagDensity₂_eq_sym2FlagDensity₂]` then projecting a **batch lemma**
`([sym2FlagDensity₂ …, …] : List ℚ) = [value, …] := by native_decide` (chunks of 200).
Forbid-density theorems are `flagDensity₁ … = 0`, one `native_decide` each via
`flagDensity₁_eq_sym2EmptyTypeFlagDensity₁` (the empty-typed analogue, same shape).

## 3. Performance concern (Q3: yes, significant)

**Cost model.** For `sym2FlagDensity₂` (the multiplication / pair density, `t = 2`) on a host
of `n` vertices, pattern sizes `m₀, m₁`, type size `k`:

* candidate space ≈ `(2ⁿ)²` subset-pairs (all subsets, both slots), vs. the *correct* space
  `C(n−k, m₀−k) · C(n−k−(m₀−k), m₁−k)` (only size-correct, disjoint placements);
* per candidate, the generic `≃f` decision enumerates `≈ m^{|verts|}` functions then
  `m!·m²` adjacency checks — vs. `isIsoFast_bool`, which is an `O(1)` edge-count prefilter
  plus `(m−k)!` permutations with edge-set comparison.

Both factors are wasteful: most of the `2ⁿ` subsets are the wrong size (and a wrong-size
candidate still enumerates `m^{|verts|}` functions only to find no bijection), and even the
right-size candidates pay the generic `≃f` instead of the fast checker.

**Evidence it bites in practice** (from `FORBID_PRUNING_ROADMAP.md` §9b profiling, 2026-06-23):
on `ErdosPentagon` the pair-density batches cost **~40 s of kernel time** (~2.8 s × ~15
batches at `n = 5`); `K5turan` (n = 5, weak K₅-free constraint ⇒ near-maximal flag volume)
**exceeded ~6 GB and did not finish** before pair-density batching was introduced. These are
exactly the `native_decide`s that run the slow counter. The cost is `native`-compiled (so
per-op fast) and trusted via the `native_decide`/`ofReduceBool` route, but the candidate
blow-up is intrinsic and **explodes at `n = 6, 7`** (`2ⁿ` = 64, 128 per slot; squared for
pair density) — the regime the forbid-free work wants to reach.

Net: the overhead is real, is a documented cost center at the current `n = 5` examples, and
is the gating factor for higher `n`.

## 4. Q1 — definitions that use generic iso instead of `FastIso`

All in `FlagAlgebra/Compute/FlagDensity.lean`:

* `predIsoSym2LabeledHl` (L716) — the filter predicate; uses `Nonempty (… ≃f …)`.
* its `DecidablePred` instance (L725) — routes to the generic `Compute/Basic.lean` stack.
* `finsetOfSym2InducedLabeledSubgraphListIsoHl` (L753), `sym2InducedLabeledSubgraphListCount`
  (L762), `sym2InducedLabeledSubgraphListDensity` (L952), and the lifts
  `sym2InducedLabeledSubgraphListDensityLifted₁/₂`, `sym2FlagDensity₁` (L1060),
  `sym2FlagDensity₂` (L1132) — all inherit the generic-iso counting.
* The `Sym2InducedLabeledSubgraph` `Fintype` (L602) — the un-restricted `2ⁿ` enumeration.

`isIsoFast_bool` / `isEmptyIsoFast_bool` (`FastIso.lean`) are **not referenced** by any of
these. (Blast radius: `Sym2InducedLabeledSubgraph` occurs only in this file, Archive aside.)

## 5. Q2 — parts of theorem generation affected

The generators whose emitted theorems are verified through this path
(`Flags/Densities/DensityThmGenerator.lean`, and `MulThmGenerator.lean` indirectly):

* `generate_flag_pair_density_theorems` (+ `_no_forbid`, + `generate_pruned_flag_pair_density_theorems`)
  — **the main consumer**: batched `native_decide` on `sym2FlagDensity₂`. Highest volume
  (e.g. ErdosPentagon ~2 832 pairs → ~15 batches).
* `generate_forbid_density_theorems` — per-flag `native_decide` on `flagDensity₁ … = 0`
  (empty-typed `sym2EmptyTypeFlagDensity₁`, same enumeration shape).
* `generate_*_mul_theorems` (`MulThmGenerator.lean`) — **not** themselves `native_decide`d;
  they `rw`/`simp` using the pre-generated pair-density `@[simp]` lemmas, so they are affected
  only transitively (they inherit faster pair densities, no proof-shape change).

The generation-time RHS (`densityPF1F2GivenG`, `canonicalLabeledForm`, `combinations`,
`inducedLocalEdges`) is **independent** of the kernel path and already efficient; it is a
ready-made oracle/spec for what the fast kernel path must reproduce.

## 6. Q4 — proposed refactoring options

**Option A — restrict the enumeration to pattern-size subsets.**
Replace the `2ⁿ` `Sym2InducedLabeledSubgraph` `Fintype` (in the counting path) with an
enumeration of only the subsets of size `mᵢ` that contain the `k` type vertices — i.e.
`C(n−k, mᵢ−k)` candidates per slot (e.g. via `Finset.powersetCard` on the non-type vertices).
*Pro:* removes the dominant exponential factor; per-slot space becomes polynomial in `n` for
fixed `mᵢ`. *Con:* alone, each candidate still pays the generic `≃f`. *Adequacy:* easy —
wrong-size subsets contribute 0 to the count (no bijection `↥verts ≃ Fin mᵢ` exists when
`|verts| ≠ mᵢ`), so the restricted enumeration has the same `card`.

**Option B — reindex each size-`m` candidate to `Sym2LabeledGraph σ m` and use
`isIsoFast_bool`.**
A size-`m` candidate subflag lives on the subtype `↥verts`; reindex it along the
order-isomorphism `verts ≃ Fin m` (`Finset.orderIsoOfFin`) into a `Sym2LabeledGraph σ m`, then
test `isIsoFast_bool reindexed (Hl i)` instead of deciding `Nonempty (… ≃f …)`. *Pro:*
replaces the `|W|^|V|` generic decision with the fast prefiltered `(m−k)!` checker. *Con:*
needs a reindexing function and the adequacy bridge `Nonempty (coe ≃f toLabeledGraph) ↔ isIsoFast_bool …`.

**Option C — bespoke fast checker against a pattern, no abstract `≃f`.**
A single `Bool` function `inducedSubflagMatchesPattern (G) (verts) (Hl i) : Bool` that checks
`verts.card = mᵢ` and the (type-pinned) edge-set match directly — essentially B inlined,
sharing FastIso's permutation/prefilter logic but specialized to "compare an induced subset of
`G` to a fixed pattern." *Pro:* avoids constructing an intermediate `Sym2LabeledGraph` per
candidate; can fuse the size check. *Con:* more new code + its own correctness proof; partly
duplicates `isIsoFast_bool`.

## 7. Recommended plan — **A + B** (size-restricted enumeration + `isIsoFast_bool`)

Introduce a parallel **fast** counter and prove it equal to the existing one, leaving the
abstract `sym2FlagDensity` as the mathematical spec:

1. `sym2InducedLabeledSubgraphListCountFast Hl G` — enumerate only size-`mᵢ` subsets
   (Option A) and filter with `isIsoFast_bool` on the reindexed candidate (Option B) + the
   existing disjointness check.
2. `sym2FlagDensityFast₁/₂` built from it (same `… / multinomialCoefficient` shape).
3. Prove `sym2FlagDensity₁/₂ = sym2FlagDensityFast₁/₂` (the adequacy in §8), hence
   `flagDensity₁/₂ = sym2FlagDensityFast₁/₂` by composition with the existing headline lemmas.
4. Reroute the generator's proof skeleton: `rw [flagDensity₂_eq_sym2FlagDensityFast₂]` and emit
   the batch `native_decide` on `sym2FlagDensityFast₂`. The generated theorem *statements*
   (`flagDensity₂ … = value`) are unchanged, so downstream `@[simp]` consumers (the mul
   generators) are untouched.

Prefer C only if profiling shows the per-candidate `Sym2LabeledGraph` construction in B is
itself a cost. Start with A (cheap, big win, easy adequacy); add B (the iso speedup) second so
each can be measured independently.

## 8. Q5 — required proof / adequacy work

* **Size-support lemma (for A).** `finsetOfSym2InducedLabeledSubgraphListIsoHl G Hl` is
  supported on tuples with `(Gl i).verts.card = Vl i`; equivalently the count is unchanged when
  the per-slot enumeration is restricted to `Finset.powersetCard (Vl i − k)` of the non-type
  vertices (union the type vertices). Follows from: `Nonempty (A ≃f B)` ⇒ the underlying
  `Equiv` forces `Fintype.card` equality of vertex types.
* **Fast-vs-generic iso bridge (for B) — the crux.** For a size-`mᵢ` candidate,
  `Nonempty ((Gl i).toLabeledSubgraph.coe ≃f (Hl i).toLabeledGraph) ↔ isIsoFast_bool (reindex (Gl i)) (Hl i) = true`.
  Factor through:
  (a) the reindexing iso `(Gl i).toLabeledSubgraph.coe ≃f (reindex (Gl i)).toLabeledGraph`
      (the order-iso `verts ≃ Fin m` transports edges + the type embedding);
  (b) `Nonempty (A.toLabeledGraph ≃f B.toLabeledGraph) ↔ A ∼sf B` for `A B : Sym2LabeledGraph σ m`
      (relate `LabeledGraphIso` of `toLabeledGraph` to the `Sym2` equivalence `∼sf` — check
      whether this already exists in `Basic.lean`; if not, it is a small bridge);
  (c) `isIsoFast_bool A B = true ↔ A ∼sf B` — **already proved** (`isIsoFast_bool_true_correct`
      / `isIsoFast_bool_false_correct`, `FastIso.lean`).
* **Count/density equality.** `sym2InducedLabeledSubgraphListCount = …CountFast` (combine the
  two lemmas above + that the disjointness predicate is unchanged), then lift through the two
  `∼sf` quotients exactly as the existing `sym2FlagDensity₁/₂` lifts do, giving
  `sym2FlagDensity = sym2FlagDensityFast`.
* **New headline lemmas** `flagDensity₁/₂_eq_sym2FlagDensityFast₁/₂` (just compose with the
  existing `flagDensity_eq_sym2FlagDensity`).
* **Reindexing well-definedness.** The order-iso `Finset.orderIsoOfFin verts (by …)` needs
  `verts.card = m`; supplied by the size-support lemma. Transporting `type_embed` must land the
  `k` type vertices on the canonical `Fin k ↪ Fin m` so the pattern comparison is type-correct
  (the `isIsoFast_bool` typed variant pins type vertices, so this must agree).

Note: the abstract `sym2FlagDensity` and its iso-invariance lemmas
(`…_respect_eqv`) stay as-is and remain the spec; the fast version inherits iso-invariance
through the proved equality, so the generators' completeness arguments are unaffected.

## 9. Migration steps

* `[ ]` **M1.** Add `sym2InducedLabeledSubgraphListCountFast` + `sym2FlagDensityFast₁/₂` in
  `FlagDensity.lean` (no change yet to existing defs).
* `[ ]` **M2.** Prove the §8 adequacy lemmas (size-support, fast-iso bridge, count equality,
  `flagDensity_eq_…Fast`). Land the `Basic.lean` `≃f ↔ ∼sf` bridge if missing.
* `[ ]` **M3.** Micro-benchmark: `native_decide` one ErdosPentagon pair-density batch on
  `sym2FlagDensityFast₂` vs `sym2FlagDensity₂` (use `lake env lean` on a scratch file). Confirm
  the win before touching the generator.
* `[ ]` **M4.** Reroute the generator proof skeletons in `DensityThmGenerator.lean`
  (`genPairDensityCoreOn` batch lemma + the forbid-density per-flag proof) to the `…Fast`
  lemmas. Keep statements identical.
* `[ ]` **M5.** Full build + per-file profile (`ErdosPentagon`, `K4turan`, `K5turan`);
  record before/after in the Progress Log. Watch for `native_decide` variance (§9b notes ±50 s).
* `[ ]` **M6.** Decide whether to also migrate `MantelTheorem/FlagDensity.lean` (a bespoke
  consumer) and retire the slow path, or keep `sym2FlagDensity` as the spec only.

## 10. Q6 — risks to existing generated theorem code

* **Single-skeleton fragility (highest).** ~thousands of generated theorems across all
  examples flow through one generator proof skeleton. If the `…Fast` adequacy lemma is
  incomplete or the rerouted `rw` doesn't fire, *every* generated density/mul theorem breaks at
  once (cf. `FORBID_PRUNING_ROADMAP.md` §9c's warning about the fragile mul-`simp`). Mitigate by
  keeping statements byte-identical and validating on `MantelHfree` (fast) before the heavy
  files.
* **Soundness is preserved by construction** — the kernel still checks the proved equality
  `flagDensity = sym2FlagDensityFast`; a *wrong* fast counter cannot slip through (it would fail
  the adequacy proof, not produce a false theorem). The `native_decide` trust surface is
  unchanged (same axiom, faster decidable).
* **Reindexing/type-embedding mismatch.** If the reindex doesn't place type vertices where the
  typed `isIsoFast_bool` expects, the bridge lemma won't hold — a proof failure (caught), not a
  silent miscount.
* **`Sym2InducedLabeledSubgraph` is reused inside FlagDensity** for the abstract-equality proofs
  (`labeledGraphListCount_eq_…`). Adding a parallel fast counter avoids editing it; **do not**
  redefine its `Fintype` in place, or those proofs (and any iso-invariance arguments) must be
  re-checked.
* **Performance variance / no-win risk.** At `n = 5` the absolute win may be modest and hard to
  read under `native_decide` compile variance (FORBID_PRUNING §9b); the decisive payoff is at
  `n = 6, 7`. Gate the migration on the M3 micro-benchmark.

## 11. Open questions

* Does a `LabeledGraphIso`-of-`toLabeledGraph` ↔ `∼sf` bridge already exist in `Basic.lean`
  (step (b) of §8), or must it be proved?
* Is the dominant cost the `2ⁿ` candidate space (Option A) or the per-candidate generic `≃f`
  (Option B)? M3 should attribute it; if A alone closes most of the gap, B can be deferred.
* Can the size-restricted enumeration reuse machinery already proven for the generators'
  `combinations` (the meta `densityPF1F2GivenG` enumerates the same `C(n−k, m−k)` sets), to
  share lemmas?
* Should `flagDensity₁ … = 0` forbid-density checks (`t = 1`) get the same treatment, or is a
  cheaper "no size-`m` induced copy exists" Bool check (à la `inducedContains` in
  `ForbidFreePruned.lean`) a better fit there?
* Is the `predDisjoint…` check ever a cost factor, or always dominated by the iso? (Likely
  dominated; confirm in M3.)
* Worth a canonical-form key (hash/sort, as floated for iso-dedup in FORBID_PRUNING §9a) to
  prefilter candidates before `isIsoFast_bool`, or is the edge-count prefilter enough at these
  sizes?

## 12. Design refinements (2026-06-30 — from Q&A)

**Q1 — degree-sequence filter in `FastIso`.** Bucketing (`degKey` in the dedup layer) and an
in-checker degree filter are *complementary*, not substitutes: bucketing cuts the *number* of
`isIsoFast_bool` calls (it is why dedup is sub-quadratic), an in-checker filter cuts the *cost
of one call*. For **dedup** the in-checker filter is redundant — callers already bucket by
`degKey`, so degrees match on entry; the earlier "redundancy is small" verdict stands. For the
**density** use there is *no* bucketing layer, so a degree prefilter is **not** redundant and is
worthwhile. Cheapest form, no re-proof of the search: a wrapper
`isIsoFastDeg A B := (degKey A == degKey B) && isIsoFast_bool A B`, whose correctness
`(= true ↔ A ∼sf B)` follows from the already-proven `degKey_iso_invariant` +
`isIsoFast_bool_true/false_correct`. Pushing degrees *into* the permutation search (only map
same-degree→same-degree) is a further win at large `m` but needs re-proving the search —
deferred (the `(m−k)! ≤ 24` search is already tiny at the example sizes). The degree filter is a
*second-order* refinement of Option B, not the primary lever.

**Q2 — define `Sym2Graph`/`Sym2LabeledGraph` equivalence directly (computably).** Correct
instinct (the slowness is the route through the abstract `≃f`), but the *global* redefinition is
the wrong tool, for two reasons:
- A **fast `∼sf` decision already exists** (`FastIso`'s high-priority `Decidable (G ∼sf G')` via
  `isIsoFast_bool`). The density counter can't reach it only because its candidates are
  `(Gl i).toLabeledSubgraph.coe` — an abstract `LabeledGraph` on a subtype — not
  `Sym2LabeledGraph σ m`. So the culprit is the **count's predicate**, not the definition of `∼sf`.
- Redefining `∼sf` touches the **quotient relation under the entire flag algebra** (generators,
  algebra, dedup) and would force re-discharging adequacy for *all* `∼sf`-based lemmas — *more*
  than once — and still wouldn't fix the density path (which never uses `∼sf`).

So the realization is local: present each candidate in `Sym2LabeledGraph σ m` form (reindex) and
reuse the existing fast equivalence — i.e. Option B. **Decision: do not redefine `∼sf` for this
work** (a possible separate "de-noncomputable" cleanup, with its own justification).

**Chosen realization of Option B (minimal blast radius).** Rather than a new count definition +
adequacy + generator reroute, replace the **`DecidablePred (predIsoSym2LabeledHl)` instance**
(FlagDensity.lean ~L725) — equivalently the `Decidable (Nonempty (… ≃f …))` it uses — with a fast
one backed by `isIsoFastDeg` on the reindexed candidate, justified by the §8 bridge. The `Prop`
`predIsoSym2LabeledHl` is **unchanged**, so the count value, the density defs, the
`flagDensity = sym2FlagDensity` chain, **and every generated theorem are unchanged** —
`native_decide` simply runs the fast decision. This keeps the `2ⁿ` enumeration (Option A) but
makes each candidate check cheap (the fast checker's edge-count/`degKey` prefilter rejects
wrong-size/wrong-degree candidates before any search), capturing the dominant win (generic `≃f` →
fast). Option A (restricting the enumeration to size-`m` subsets) can be layered on later if the
`2ⁿ` outer loop becomes the bottleneck at high `n`.

## Progress log

* **2026-06-30** — Created from a read-only investigation of
  `FlagAlgebra/Compute/{FlagDensity,FastIso,Basic}.lean` + `Flags/Densities/DensityThmGenerator.lean`.
  Confirmed: the density counter enumerates `2ⁿ` subsets per slot and decides placement via the
  generic `≃f` (whose decision enumerates `|W|^|V|` functions); `isIsoFast_bool` is sound+complete
  but used only in enumeration/dedup, never here; the generator computes the RHS efficiently
  (`densityPF1F2GivenG`) but the `native_decide` re-verifies via the slow path. No code changed.
* **2026-06-30 (implementation started).** Reflected the Q1/Q2 discussion (§12). Began the
  Option-B implementation via the §7 chosen realization (fast `DecidablePred` for the iso),
  developing lemmas in a scratch file driven by `lake env lean`. Findings that reshape the effort
  estimate:
  - **Foundational friction.** Even the cheap necessary-condition lemma
    (`Nonempty (H.coe ≃f K.toLabeledGraph) → H.verts.card = m`, the prefilter that rejects every
    wrong-size candidate) needs care: this import closure does **not** include Mathlib's
    `Nat.card` / `Set.ncard`, so cardinalities go through `Fintype.card` with an explicitly supplied
    subtype `Fintype` (`H.verts.fintypeCoeSort`); the `Set`-vs-`Finset` coe-sort and `simp`-unfolding
    `toLabeledSubgraph` (which trips on the `Sym2FlagType.edges` projection) make the
    `Fintype.card ↥(subgraph.verts) = H.verts.card` step fiddly.
  - **The reindex iso is the crux** (§8 (a)/(b)) and is heq-heavy — the existing
    `labeledGraphListCount_eq_…` proof is full of `cast_eq_iff_heq` / `proof_irrel_heq`. The
    `IsoInvariants` `Sym2.map` edge-bijection lemmas (`G ∼sf R ↔ ∀ e, e ∈ G.edges ↔ Sym2.map φ e ∈ R.edges`,
    both directions) are the reusable engine for it.
  - **Iteration + verification cost.** Each scratch proof cycle is ≈60 s (loading `FlagDensity`'s
    import closure). And because `FlagDensity.lean` is a core dependency, **any** change to the
    `DecidablePred` there forces a **full project rebuild** (every example's `native_decide`) to
    verify and measure — there is no cheap-to-verify form of a real speedup.
  Conclusion: full proven-and-verified Option B is a focused multi-step proof effort, not a single
  pass; the hardest part (the reindex iso, M2) is still ahead. The WIP scratch was removed. The
  **card necessary-condition prefilter** (Option A's benefit, realized inside the decision — it
  rejects the `2ⁿ` wrong-size candidates at O(1), the dominant lever at high `n`) is the more
  tractable first increment if a staged landing is preferred.
* **2026-06-30 (card-prefilter increment — LANDED + verified).** Per the user's decision to stage,
  implemented the §7 realization restricted to the tractable card guard. In `FlagDensity.lean`:
  - Added `verts_card_of_coe_iso : Nonempty (H.toLabeledSubgraph.coe ≃f K.toLabeledGraph) →
    H.verts.card = m`, proved by composing `Finset.equivFin` with the iso's vertex equiv
    (`(H.verts.equivFin).symm.trans iso.graph_iso.toEquiv : Fin H.verts.card ≃ Fin m`, then
    `Fintype.card_congr`) — this sidesteps the subtype-`Fintype` / `Set`-coe friction that blocked
    the `Nat.card` (absent from the import closure) and `Fintype.card_coe` routes.
  - Rewrote the per-candidate branch of the `DecidablePred (predIsoSym2LabeledHl)` instance to
    `by_cases hc : (Gl i).verts.card = Vl i` → the existing generic decision when sizes match,
    else `isFalse (fun hiso => hc (verts_card_of_coe_iso (Gl i) (Hl i) hiso))`. Wrong-size
    candidates are rejected at `O(1)` instead of running the generic `|W|^|V|` search.
  - **Correct by construction:** only the `DecidablePred` *instance* changed, not the `Prop`
    `predIsoSym2LabeledHl`; `Finset.filter`/`.card` are independent of the `Decidable` instance, so
    every density value — and thus every generated theorem — is unchanged.
  - **Verified:** `FlagDensity.lean` compiles standalone (14 s); the **full `lake build` is green
    (8005 jobs, no errors)** — every example's density `native_decide` still passes with unchanged
    values. (Uncommitted in the working tree.)
  - **Speedup character + measurement (n = 5).** This realizes Option A's benefit (skip the bulk
    of the `2ⁿ` wrong-size candidates — the dominant lever at high `n`) inside the decision, with
    zero blast radius on the count/density/generators. **Measured** with a controlled before/after
    on `ErdosPentagon` (revert just the prefilter, rebuild only `FlagDensity`'s olean — 12 s — and
    `lake env lean` the example each way): **before 182 s (3 m 2.1 s) vs after 180 s (2 m 59.7 s) —
    a ~2 s (~1%) difference, well inside `native_decide`'s ±50 s variance ⇒ no measurable speedup at
    n = 5.** This matches the prediction: the fixed costs (one-time native compile + kernel-checking
    the batch literals + the mul-command `simp`s, ≈127 s per §9b) dominate and are untouched by the
    prefilter, and the wrong-size work it removes is tiny in absolute native-run terms at n = 5. The
    change is correct and is the right lever; its decisive payoff is at **n = 6, 7**, where the `2ⁿ`
    wrong-size candidates dominate (the regime the forbid-free work targets). The full per-candidate
    `isIsoFast_bool` speedup (the reindex iso) would help the *surviving* size-`m` candidates, but
    that too is mainly a high-`n` lever.
  - **Remaining = full Option B.** The per-candidate `isIsoFast_bool` speedup for the *surviving*
    size-`m` candidates still needs the heq-heavy **reindex iso** (§8 (a)/(b)). The card guard is
    its foundation — it already establishes `card = m`, the precondition the reindex needs
    (`Finset.orderIsoOfFin` requires it). Next step: define `reindex H` via `Sym2.map` of the
    order-iso, prove `H.toLabeledSubgraph.coe ≃f (reindex H).toLabeledGraph` (reusing the
    `IsoInvariants` `Sym2.map` edge-bijection lemmas), and replace the survivor `infer_instance`
    branch with `decidable_of_iff (isIsoFast_bool (reindex (Gl i)) (Hl i)) <bridge>`.
