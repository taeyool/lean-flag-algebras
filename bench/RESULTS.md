# Where `flag_certificate` spends its time, and whether splitting the sort helps

Target: `K5freeEdge_flagAlgebra` (host 5, 4 SDP blocks of 8×8, 3/4 bound).
All numbers are **tactic time** reported by `bench/SplitPipeline.lean`, measured with
`lake env lean bench/run_<chunk>_<mode>.lean`, one Lean process at a time on an otherwise idle
machine.  The generation commands are not re-run — the harness imports the prebuilt
`LeanFlagAlgebras.Flagmatic.K5freeEdge` olean and re-proves only the theorem.

Regenerate a variant with `sh bench/mk.sh <chunk> <mode>`.

## 1. Baseline breakdown

```
[  3.5 s] 4× psd_real_ldlt_terms
[  1.0 s] flag_expand_hfree + have flagCert_qf
[  7.1 s] simp (expand the 4 quadratic forms)
[  0.5 s] reduce_downward_flagmul            -- 162 steps
[  3.0 s] expand_one_hfree_at
[  2.1 s] simp [smul_smul, downward_*]
[ 73.8 s] flagsum_ac_sort_rhs_pipeline       <-- 80 % of the script
[  0.8 s] flag_nonneg
           TOTAL 91.9 s   (wall 125 s incl. olean import)
```

`reduce_downward_flagmul` *moves* every expanded product from the left-hand side onto the
right, so the entire certificate lands in one RHS sum which is then sorted once.

## 2. What inside the pipeline is expensive

`ac_sort_at_pipeline_timed` (a transcription of the real conv tactic with per-phase timers)
on the same goal:

| phase | time | note |
|---|---|---|
| pre-simp `simp only [… add_assoc, smul_smul]` | 16.9 s | re-associates a 324-term sum |
| key extraction + `qsort` | 0.006 s | — |
| `ac_rfl` proving the permutation | 0.33 s | — |
| **`mergeAdjacentAndProve`** | **54.3 s** | 324 terms → 33 |
| left-assoc reshape + `norm_num` | 0.9 s | — |

**The sorting is free; the coefficient merge is the bottleneck.**  Its docstring claims each
step is `O(1)` because the unmerged remainder `R` stays an opaque subterm, but that is not what
happens: every step calls `rest.mapM termOf`, i.e. one `mkAppM` (typeclass search) per remaining
summand, *per step* — ~52 000 instance searches for 324 terms — and then embeds the rebuilt `R`
in the proof goal that `simp only [add_assoc, add_smul]` walks.

## 3. Results

`chunk = k`: run `k` `reduce_downward_flagmul` steps, sort+merge the RHS, repeat (`0` = stock,
one sort at the end).  `mode`: `0` stock merge, `3` merge with the summands and all
right-associated suffixes precomputed once and the remainder abstracted as a local `r` so each
step's proof goal really is `O(1)`.

| chunk | merge | total tactic time | vs. baseline |
|------:|-------|------------------:|-------------:|
| 0 (stock) | stock | 91.9 s | — |
| 32 | stock | 70.6 s | −23 % |
| 200 (single early sort) | stock | 72.2 s | −21 % |
| 0 | linear | 68.3 s | −26 % |
| **32** | **linear** | **61.8 s** | **−33 %** |

Notes:

* Chunking helps, but not because it shrinks the sort — it shrinks the **pre-simp**
  `add_assoc` re-association, which is quadratic in the number of summands.  The number of
  merge steps is the same however you slice it.
* `chunk = 200` (drain everything, then sort once *before* `expand_one_hfree_at`) captures
  nearly the whole chunking win, so most of it is "sort before the unit expansion", not
  "sort per block".
* Chunking adds its own overhead: `norm_num` runs once per round (~1.8 s × 6 here), so very
  small chunks lose.  The optimum on this problem is around `k ≈ 32`.
* After the linear merge, the residual per-step cost is the `evalTactic (simp only …)` call
  itself (~35–100 ms each).  Replacing it with a single pre-proven auxiliary lemma
  `c • x + (d • x + r) = (c + d) • x + r`, instantiated with the instances already present in
  the goal, should remove most of the remaining 31 s — but that is exactly the hand-assembled
  route `FLAGSUMSORT_PERF_PROGRESS.md` records as having broken `flag_nonneg` once, so it needs
  care.

## 4. Files

* `bench/SplitPipeline.lean` — the harness.  Transcribes `runFlagCertificate` and
  `stepReduceDownwardFlagMul` (both have `private` internals upstream), adds
  `flag_certificate_bench "cert" F <chunk> <mode>`, the per-phase-timed `ac_sort_at_pipeline`
  copies, and `mergeLinear`.
* `bench/mk.sh` — emits `bench/run_<chunk>_<mode>.lean`.
* Nothing under `LeanFlagAlgebras/` is modified; `bench/` is outside the lakefile globs, so
  `lake build` ignores it.


---

# host-6: `K3forbidC6` (host 6, blocks 15×15 and 10×10)

`Archive/Flagmatic/K3forbidC6.lean` is a materialized script (no certificate JSON), and it is
excluded from the lakefile globs.  Compiling it end to end takes **98 min**, of which the
generation commands are 41 min.  `bench/HostSixGen.lean` is its first 168 lines (the `K3` def,
the `generate_forbid_free_*` commands, and `M₁/M₂/v₁/v₂`), prebuilt once into
`bench/HostSixGen.olean` (231 MB) so the theorem can be re-measured on its own:

```
lake env sh -c 'LEAN_PATH="$LEAN_PATH;<repo>/bench" lean bench/six_<chunk>_<mode>.lean'
```

`sh bench/mk6.sh <chunk> <mode>` emits the variant; `mode = v` is the archive script verbatim
(`reduce_downward_flagmul` + `flagsum_ac_sort_rhs_pipeline`).

## Measurements

Runs were done two at a time.  Batch 2 was ~2.13× slower than batch 1 overall — the two
*unchanged* leading `simp`s measure 2545/1421 ms in batch 1 and 5387/3036 ms in batch 2 — so the
"norm." column rescales batch 2 into batch-1 conditions.  Cross-batch numbers should only be
read to ~±15 %.

| variant | batch | reduce+sort | final sort | sort total | wall | norm. wall |
|---|:-:|---:|---:|---:|---:|---:|
| archive script verbatim (`mode = v`) | 2 | 1.9 s | 4465.3 s | 4467 s | 5292 s | ~2484 s |
| `chunk = 0, mode = 0` (transcription of the same) | 1 | 1.0 s | 2071.9 s | 2073 s | **3526 s** | 3526 s |
| `chunk = 32, mode = 0` (chunking only) | 2 | 619.2 s | 12.3 s | 631 s | 854 s | **~401 s** |
| `chunk = 32, mode = 3` (chunking + linear merge) | 1 | 197.5 s | 4.7 s | **202 s** | **291 s** | 291 s |

The verbatim script and the transcription agree once rescaled — final sort 4465/2.13 = 2096 s vs
2072 s — so `reduce_and_sort_chunked 0 0` is a faithful stand-in for `reduce_downward_flagmul`.

**Speed-up: ~8.8× from chunking alone, ~12× with the linear merge on top** (3526 s → 291 s,
59 min → 4.9 min).  The sort phase itself goes 2073 s → 202 s.  Downstream steps get cheaper too,
because they now run over an already-collapsed RHS: `expand_one_hfree_at` 6.5 s → 1.3 s,
`simp [downward…]` 10.3 s → 0.4 s.

This is a much bigger win than on K5freeEdge (−33 %), and in the direction the K5 breakdown
predicts: the merge is superlinear in the number of summands, and host-6 rounds carry 200–270
terms where K5 carried 33–120.

## Caveat: this case does not currently close

**All four runs — including the archive script verbatim — fail on the final `flag_nonneg`:**

```
⊢ 0 ≤ φ (-FlagAlgebra_6_0_0_53)
```

So the timings compare four runs that all execute every measured phase and then fail on the last
tactic.  The failure is pre-existing and independent of chunking:

* here `objN = hostN = 6`, so there is no branch-B `flag_expand_hfree` and the objective stays a
  bare `-FlagAlgebra_6_0_0_53`;
* `termOf` deliberately excludes coefficient-less terms from merging, so it is never combined
  with the `c • FlagAlgebra_6_0_0_53` coming from the unit expansion;
* the pre-simp's `← neg_smul` only rewrites `-(a • x)`, not a bare `-x`.

`K5freeEdge` avoids this because `objN = 2 < hostN = 5` expands the objective into `c • H_i`
terms.  Fixing it (e.g. letting the pre-simp turn a bare `-x` into `(-1) • x`) is a separate
change from anything measured here.

---

# Restoring the 6-vertex example as a build target

`K3forbidC6_cert.json` was not lost, only deleted: commit `fe77d05` ("Rename the Flagmatic examples
to match the paper's Section 5.4 case table") renamed every other certificate to the `…free…`
convention and dropped this one along with `C5turan_cert.json`.  `git show fe77d05^:…` recovers it
intact.

Restored as `Certificates/K3freeC6_cert.json` and regenerated in the compact form with

```
python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
  LeanFlagAlgebras/Flagmatic/Certificates/K3freeC6_cert.json \
  LeanFlagAlgebras/Flagmatic/K3freeC6.lean --namespace K3freeC6 --native-decide --force
```

which also yields `K3freeC6_turanDensity` (0.9 s), a statement the materialized `Archive/` version
never had.

| | archive, materialized | `flag_certificate` form |
|---|---:|---:|
| generation (10 commands) | — | 3839 s |
| main theorem | — | **684 s** |
| whole file, `lake env lean` | 5961 s | **4619 s** |
| whole file, `lake build` | not a target | 2882 s |

The materialized script calls `reduce_downward_flagmul` and `flagsum_ac_sort_rhs_pipeline`
directly, so `flagCert.sortChunk` never reaches it; only the `flag_certificate` form gets the
chunking.  Generation time varies a lot between runs on this machine (2458 s – 3839 s for the same
ten commands), so only same-run comparisons are meaningful.

The module lives in `LeanFlagAlgebras/Flagmatic/`, so `lake build` covers it — note that the
lakefile's `.submodules` glob, not the `LeanFlagAlgebras.lean` manifest, is what decides that
(`C5freeEdgeReduced`, `K5freeEdgeClean` and `K5freeEdgeReduced` are likewise built without being
imported by the manifest).  `K3freeC6` is deliberately left out of the manifest.

**It does not compile without `flagNeg_eq_negOne_smul`** — the two must land together.
