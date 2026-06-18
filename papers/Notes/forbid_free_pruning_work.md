# Forbid-free generation: sort-drop and genuine pruning

This note summarizes two pieces of work aimed at speeding up the completeness
`native_decide` in the forbid-free flag generation (the `sym2FlagSetHfree_…_eq`
proof, "line 469" of `ForbidFreeGenerator.lean`), plus the measurements that
justify them. For the framework background and design rationale, see
`papers/Notes/forbid_free_framework.tex`.

**Setting.** The typed forbid-free completeness reduces `genFlagsHfree`, which
filters the underlying-graph enumeration by an H-free predicate and builds typed
flags over the survivors. The cost of that `native_decide` is dominated by the
*graph enumeration*, and within it the canonical sort. Two levers reduce it:

1. **Sort-drop** — stop computing the canonical (`canonicalEdgeList`) ordering of
   the graph enumeration.
2. **Genuine pruning** — never build the forbidden graphs at all, rather than
   building all graphs and filtering.

All timings below are the per-`native_decide` "type checking took …" figures from
`set_option profiler true`, at `n = 6`, type `1_0`, forbidding `K3`. Native-decide
timings carry run-to-run variance (~20%); the back-to-back, same-file comparisons
are the reliable ones.

---

## 1. Sort-drop — DONE (committed `e374804`)

**Change.** `genLabeledGraphsHfree` now filters the *unsorted* `genSym2GraphsDedup n`
instead of the *sorted* `genSym2Graphs n`, and `genFlagsHfree_toFinset_eq` cites
`genSym2GraphsDedup_complete` instead of `genSym2Graphs_complete`. This drops the
`canonicalEdgeList` sort (an `O(n!)`-per-graph computation) from the completeness
`native_decide`.

**Why it is sound and needs no new math.** The forbid-free set is a `Finset`
(order-insensitive), and `genSym2GraphsDedup` has the same elements as
`genSym2Graphs` with an existing completeness lemma. So only the cited lemma and
the underlying list change; the proof is otherwise identical.

**Measurement** (genFlagsHfree-equivalent reduction, back-to-back in one file):

| pipeline | graphs | time |
|---|---|---|
| over **sorted** `genSym2Graphs 6` (before) | 156 | **11.3 s** |
| over **unsorted** `genSym2GraphsDedup 6` (after) | 156 | **7.48 s** |

≈ **1.5×** faster (~3.8 s saved), with no new mathematics. `MantelHfree` (which
exercises the changed completeness proof at `n=3`) still builds green.

---

## 2. Genuine pruned augmentation — DONE as far as cleanly possible (committed `00a93e8`)

New file `LeanFlagAlgebras/Flags/ForbidFreePruned.lean`: a *true* pruned augmentation
that builds the triangle-free graphs by augmenting only triangle-free
representatives, so triangle-containing graphs are **never constructed**. (Contrast
the shipped `ForbidFreeGenerator`, which enumerates all graphs and filters.)

It uses a **combinatorial** triangle predicate, for which the two facts the
completeness induction needs are clean to prove (the analytic density predicate would
make the monotonicity step hard — see §3):

- `hasTri G` — `∃` three distinct pairwise-adjacent vertices; `Decidable`.
- `augRepsTriFree` — the pruned generator (augment only triangle-free reps, keep only
  triangle-free augmentations, dedup).
- `hasTri_of_eqv` — **isomorphism invariance** (transport a triangle along the
  edge-preserving permutation from `G ∼sf R`).
- `hasTri_of_restrict` — **vertex-deletion monotonicity**: a triangle in `restrict H`
  is a triangle in `H`; contrapositively, triangle-freeness survives vertex deletion.
  This is the fact that lets the recursion never look at the forbidden graphs.
- `augRepsTriFree_complete` — **every triangle-free graph is `∼sf` a generated
  representative**, by induction mirroring `augReps_complete`. **No `sorry`.**

**Correctness validation.** `native_decide` confirms the generator yields exactly the
known K3-free isomorphism-class counts, each reducing *only* the pruned generation
(never the full enumeration):

| `n` | K3-free classes | total classes |
|---|---|---|
| 4 | 7 | 11 |
| 5 | 14 | 34 |
| 6 | 38 | 156 |

**Measurement** (graph-level build at `n=6`, back-to-back):

| build | graphs produced | time |
|---|---|---|
| pruned `augRepsTriFree 6` | 38 | **3.16 s** |
| full `genSym2GraphsDedup 6` | 156 | **5.74 s** |

≈ **1.8×** faster at the graph level — pruning carries fewer representatives forward
at every augmentation step (and never pays for the forbidden graphs or their dedup).

---

## 3. What is NOT yet done: wiring genuine pruning into the bridges

The pruned generator and its completeness are proved, but they are **not yet plugged
into** `genFlagsHfree_toFinset_eq` (so the command does not yet enjoy the §2 speed-up).
The missing piece is a single bridge lemma between the *combinatorial* predicate used
by the pruned generator and the *analytic* predicate the forbid framework uses:

```
triFree G  ↔  flagDensity₁ K3.toFinFlag.2 (unlabel ⟦G⟧) = 0
```

i.e. "`G` has no triangle" iff "the K3-density in `G` is zero." The forward direction
(no triangle ⇒ density 0) and especially the precise density bookkeeping is the
density↔containment step flagged in the design notes as the genuinely hard lemma; it
requires reasoning inside `sym2EmptyTypeFlagDensity₁`'s definition and was left for
later. With this lemma, `genFlagsHfree_toFinset_eq` could cite
`augRepsTriFree_complete` (suitably lifted to typed flags via `labeledOfGraph`) in
place of `genSym2GraphsDedup_complete`, and the line-469 `native_decide` would reduce
the pruned build instead of the full enumeration.

---

## Cumulative picture (n=6 typed, K3)

The completeness `native_decide` reduces `genFlagsHfree` = *graph enumeration* +
*labeled part* (the labeled part — `labeledOfGraph` over the H-free graphs + dedup —
is only ~1.5–2 s and is the irreducible floor):

| stage | line-469 `native_decide` | note |
|---|---|---|
| original (sorted, full) | ~11.3 s | |
| **+ sort-drop** (shipped) | **~7.5 s** | committed `e374804` |
| **+ genuine pruning** (projected, once wired) | **~5 s** | graph part 5.7 s → 3.2 s; needs the §3 bridge |

So sort-drop is a shipped ~1.5×, and genuine pruning is a proved, measured further
~1.5× that is *not yet realized in the command* pending the combinatorial↔density
bridge. The gains compound and grow with `n`: at `n=7` the canonical sort is
`O(g·n!)` and dedup `O(g²)` with `g = 1044`, while the K3-free fraction is only ~10%
(~107/1044), so both levers matter much more there — that is the regime that
motivates finishing genuine pruning.

---

## Files and commits

- `LeanFlagAlgebras/Flags/ForbidFreeGenerator.lean` — sort-drop (`e374804`).
- `LeanFlagAlgebras/Flags/ForbidFreePruned.lean` — genuine pruned augmentation,
  proved complete, validated, measured (`00a93e8`).
- `papers/Notes/forbid_free_framework.tex` — framework design and rationale.

## Suggested next steps

1. Prove the combinatorial↔density bridge `triFree G ↔ flagDensity₁ K3 (unlabel ⟦G⟧) = 0`
   (the hard, density-internal lemma).
2. Lift `augRepsTriFree` to typed flags (`labeledOfGraph` over its output) and reroute
   `genLabeledGraphsHfree` / `genFlagsHfree_toFinset_eq` through it, realizing the §2
   speed-up in the command.
3. Generalize beyond K3: replace `hasTri` with a general forbidden-subgraph containment
   predicate (the monotonicity and iso-invariance arguments are the same shape).
4. Push to `n=7`, where the pruning + sort-drop gains are largest.
