# MetaTheory formalisation — worklog & resume notes

*A cross-machine handoff and resume doc for the `MetaTheory/` formalisation. **Tracked by git** and
committed to `main` as `METATHEORY_WORKLOG.md` (renamed from the previously-untracked `WORKLOG.md` and
added to the shared `taeyool` repo on 2026-06-25), so `git pull` keeps it current across machines like
any other doc. (My detailed AI working memory under `~/.claude/` is **machine-local** and will **not**
be on a different machine — this file plus the other committed `MetaTheory/*.md` docs are the portable
context.)*

Last updated: 2026-07-10 (fourth session of 2026-07-09/10: **§11.4–§11.8**). (Stopping point:
§1–**10** of `paper.tex` formalised PLUS the **whole §11.2–§11.8 relative (slice) theory** — the
§11.2–§11.3 foundation (four modules,
`RelativeSupport`/`RelativeClosure`/`RelativeSlackness`/`KernelSlackness`, "§11.2–§11.3 — DONE"
below) AND the §11.4–§11.8 slice method + graphon layer (twelve modules,
`RelativePlanted`/`RelativeCertificateGap`/`RelativePositivstellensatz`/`CertificateSliceVanishing`/
`ParametricP4Slice`/`TuranLimit`/`MantelNotPlantable`/`SliceRecovery` +
`GraphonBasic`/`GraphonMoments`/`GraphonRigidity`/`GraphonQuantStability`, "§11.4–§11.8 — DONE"
below; partial-coverage caveats in README Deviation 14 + the PARTIAL table rows). Prior sessions:
hygiene pass ("Hygiene pass — DONE"), §11.2–§11.3, §10, §9.3–§9.5, §1–9.2 + `lem:complementation`,
§8. `lake build LeanFlagAlgebras.MetaTheory` → **8001 jobs green** (78 modules; "Build completed
successfully" line confirmed — do NOT trust exit-code alone, stale oleans can mask a failure);
`grep -rnwE 'sorry|admit|native_decide'` over `MetaTheory` → empty; headline theorems
`#print axioms` = `[propext, Classical.choice, Quot.sound]` — EXCEPT the sanctioned Tier-2
certificate consumers (`parametricP4_*`/`k4freeP4_*`, `parametric_recovery`,
`parametric_qualitative_stability`), which additionally print
`[Lean.ofReduceBool, Lean.trustCompiler]` inherited from the `Automation` layer's `native_decide`
(README "Axioms assumed", two tiers). Next targets: the §11.5 support identities (Dirac /
second-moment computations at the Turán limit), the Lovász–Szegedy representation bridge (the big
unlock for Thm 102 / Cor 105–106), and the `R_τ⁻` kernel functional + Thm 112(iv); §12 is open
problems — prose, nothing to formalise.)

---

## TL;DR — current status

* **The Lean formalisation of `paper.tex` §1–5 is COMPLETE and `sorry`-free** (committed and pushed
  to `main`, `origin` = `git@github.com:taeyool/lean-flag-algebras.git`).
* **§6 (complete blow-ups / true twins) and §7 (substitution-closed classes) are COMPLETE and
  `sorry`-free** — added 2026-06-16 (`abb2ca1`), cleanup/refactor 2026-06-17 (`2026a18`).
* **§5/§6/§7 are now UNIFIED (2026-06-17):** the single-vertex **blow-up-closure** property
  `BlowupClosed` and the theorem `blowupClosed_root_plantable` (paper §7, rewritten as "A common
  generalisation: blow-up-closed classes") subsume all three; `clone_root_plantable_blowup`,
  `true_clone_root_plantable`, `substitution_root_plantable`, `cluster_root_plantable` are now
  one-line corollaries via the `…toBlowupClosed` implications. The iteration bridge
  `BlowupClosed.toUniform` (single-vertex ⟹ uniform blow-up) is the one new lemma. New module
  `BlowupClosed.lean`; paper §7 fully revised. All theorems depend only on
  `[propext, Classical.choice, Quot.sound]`. (At the §7 milestone: 33 modules, 7939 jobs; with §8:
  39 modules, 7945 jobs; with §9/§9.1/§9.2 + `lem:complementation`: 49 modules, 7955 jobs; **now with
  ALL of §9 (§9.1–§9.5): 55 modules, `lake build LeanFlagAlgebras.MetaTheory` → 7961 jobs green**;
  `grep -rnwE 'sorry|admit|native_decide'` over `MetaTheory` → empty.)
* **Commits:** §5 `3a607f2`/`e795f28`; §6/§7 `abb2ca1`; refactor `2026a18`; unification `d446996`;
  paper §7 correctness review + Notes sync `dcf5285`. All pushed to `main`.
* **Paper:** `LeanFlagAlgebras/MetaTheory/paper.tex` §7 rewritten (blow-up-closure unification) and
  reviewed (added `lem:general-planting-estimate`; fixed intro/§Strengthening claims that wrongly
  called substitution-closure the "broader"/"common" generalisation — it is the *strictest*).
  Compiles clean (`latexmk`). `papers/Notes/root_planting_criterion_and_c4_counterexample.tex` (the
  tracked review copy) is kept byte-identical to `paper.tex`. NB: user's own uncommitted
  `papers/POPL27/paper_draft.tex` is left untouched.
* **Headline result (plantability/positive side):** `blowupClosed_root_plantable` (paper
  `thm:blowup-root-plantable`, in `BlowupClosed.lean`) — the unified theorem;
  `clone_root_plantable` (§5), `true_clone_root_plantable` (§6), `substitution_root_plantable` (§7),
  `cluster_root_plantable`, `clique_free_root_plantable` are all corollaries/instances.
* **Headline results (obstruction/negative side, §8–§9):** `pinning_obstruction` (§9.3 `thm:pinning`,
  the abstract obstruction), `degenerate_not_rootPlantable` / `coDegenerate_not_rootPlantable` (stars /
  co-stars, §9), `c4free_not_rootPlantable` / `coC4free_not_rootPlantable` (sparse / dense hereditary
  classes, §9.1/§9.2), `complementation_invariance` (Lemma 50, §9.2), **`no_interior_pinning`** (§9.4
  `thm:no-interior` — for an edge-deletion-closed class no *interior* density is ever pinned), and
  **`c5free_edge_not_rootPlantable`** (§9.5 `thm:c5-edge-not-root-plantable` — the `C₅`-free class fails
  at the two-root edge type, refuting the all-types conjecture). These are the obstruction capstones —
  a class can FAIL to be root-plantable, on both the sparse and the dense side, and even at one type but
  not another.
* **Headline results (§10, "the gap is invisible to density bounds"):** the §9 obstructions never
  affect an actual empty-type density bound. `emptyType_rootPlantable` /
  `heredClass_emptyType_rootPlantable` (`prop:empty-type`: `Ext_∅ = δ`, `S_∅ = Q₀`, always
  root-plantable; `cor:confined` via `ensemble_implies_quotient_emptyType`),
  `no_closed_certificate_gap` (`thm:no-closed-certificate-gap`: the sums-of-squares and
  nonneg-on-`S_σ` certificate cones have the same `Q₀`-seminorm closure, every type),
  `downward_eval_eq_zero_of_zero_on_Sσ` + `pinned_witness_downward_eq_zero` (`prop:ideal-zero`),
  `Sσ_eq_singleton_of_edgeDegenerate`/`_coEdgeDegenerate` + `edgeDegenerate_cone_collapse`/
  `coEdgeDegenerate_cone_collapse` (`prop:single-point`: `S_vtype` a single point, cones = `ℝ≥0·1₀`),
  `c5free_edge_no_closed_certificate_gap` (`cor:c5-edge-closed-inert`).
* **Headline results (§11.2–§11.3, the relative / slice theory):** the relative support
  `relSσ Y σ` (= `S_σ(Y)`, arbitrary `Y`; `Sσ_eq_relSσ` = `Y = Q₀` recovery, `rfl`),
  `relative_soundness` (`prop:relative-soundness`), `relative_criterion`
  (`prop:relative-criterion`, **unconditional**), `relSσ_closure_eq` (`lem:relative-closure`,
  via `extend_tendsto` weak continuity + `support_subset_closure_iUnion_support`), the
  complementary-slackness family `relative_slackness_*` (+ `_exact_ae_sq`/`_global_sq`,
  `thm:relative-slackness` + `rem:cs-shape`), `downward_cauchy_schwarz`
  (`lem:relative-cauchy-schwarz`), `certificate_first_moment_sq_bound(_one)`
  (`cor:sos-first-moments`), `unique_slice_stability` (`prop:unique-slice-stability`), and the
  matrix form `kernel_slackness_*` (`thm:kernel-slackness`: PSD blocks in, `ker Q` moment
  equations out) — the foundation for the §11.4+ slice results.
* **Headline results (§11.4–§11.8, the slice method + the graphon layer):**
  `relative_planted_criterion` (`prop:relative-plantability`: the relative planted set `relQσ`
  with the planted criterion), `mantel_not_relatively_plantable` (`prop:mantel-not-plantable`:
  the Mantel slice breaks relative root-plantability; pinning input `hpin` = Thm 92(i), explicit
  hypothesis), `no_relative_closed_certificate_gap` (`thm:relative-certificate-gap`),
  `relative_positivstellensatz(_closure)` (`thm:relative-positivstellensatz`: slice-valid ⟹
  class-valid up to `ε` with a finite `M·∑g²` penalty, by compactness), `equality_slice_vanishing`
  (`prop:equality-slice-vanishing`), the `parametricP4_*`/`k4freeP4_*` slice equations
  (`thm:k4free-p4-equality-slice` unconditional at `r = 3` / `thm:parametric-p4-equality-slice`
  under `hZykov` — the verified `CompleteGraphFreeP4.gap_identity` certificate consumed through
  relative slackness; **Tier-2 axioms**), the nonempty Turán/Mantel slices (`exists_turan_limit`,
  existence halves of Thm 91/92), the recovery/stability corollaries (`parametric_recovery`,
  `parametric_qualitative_stability`, `k4free_qualitative_stability`; classical equality cases as
  `hZykEq`/`huniq` hypotheses), and the standalone **graphon layer**: `Graphon.moments_*` +
  `approximate_moments*` (`thm:parametric-moments`/`thm:approximate-moments`),
  `Graphon.slice_rigidity`/`r3_rigidity` (`thm:slice-rigidity`/`cor:r3-rigidity`, in
  measurable-partition form), and the `GraphonQuantStability` chain
  (`thm:k4free-p4-quant-stability`, `thm:parametric-quant-stability` (iii)). Partial coverage +
  hypothesis-ised classical inputs: README Deviation 14.
* **Scale:** 78 Lean modules (33 through §7, +6 for §8, +1 §9 abstract `Pinning`, +5 for §9/§9.1/§9.2,
  +4 for `lem:complementation`, +2 for §9.5 [`C5FewTriangles`/`C5EdgeObstruction`], +4 for §9.4
  [`NoInterior`/`EdgeThinning`/`EdgeThinningLimit`/`NoInteriorThinning`], +7 for §10
  [`DownwardAverage`/`EmptyTypeCollapse`/`CertificateCones`/`VanishingIdeal`/`BooleanPoint`/
  `SinglePoint`/`C5EdgeInert`], +4 for §11.2–§11.3
  [`RelativeSupport`/`RelativeClosure`/`RelativeSlackness`/`KernelSlackness`], +12 for §11.4–§11.8
  [`RelativePlanted`/`RelativeCertificateGap`/`RelativePositivstellensatz`/
  `CertificateSliceVanishing`/`ParametricP4Slice`/`TuranLimit`/`MantelNotPlantable`/`SliceRecovery`/
  `GraphonBasic`/`GraphonMoments`/`GraphonRigidity`/`GraphonQuantStability`]) + 4 committed
  reference docs (`README`/`ARCHITECTURE`/`READING_GUIDE`/`METATHEORY_WORKLOG`, same dir), in
  namespace `FlagAlgebras.MetaTheory`, aggregated by `LeanFlagAlgebras/MetaTheory.lean` and in the
  top build manifest `LeanFlagAlgebras.lean`.

## Read these first (committed reference docs, same directory)

* **`README.md`** — what is formalised (results table), verification status, deviations from the
  paper, scope, and a section *"How the existing flag-algebra formalisation enabled this"*.
* **`ARCHITECTURE.md`** — proof strategy, layered dependency map, module-by-module descriptions, and
  a step-by-step walkthrough of the capstone proof.
* **`READING_GUIDE.md`** — conventions, notation cheat-sheet, suggested reading orders, and a
  paper-result → module → Lean-name map.

---

## Resuming on another machine (office / home)

1. **Get the latest.** The repo is Dropbox-synced, so the files are already there; still, prefer
   `git pull` to be sure you are at the latest `main`. (My formalisation work is committed+pushed
   through `c3c149a` — the latest `MetaTheory.lean` / Lean / doc commit; any newer `update` commits on
   `main` are the user's own edits to `papers/POPL27/paper_draft.tex` and do not touch the MetaTheory
   Lean / docs.) This file (`METATHEORY_WORKLOG.md`) is now **tracked and committed** on `main`, so
   `git pull` fetches it like any other doc (it is no longer an untracked "stray").
2. **TOOLCHAIN IS NOT ON THE NON-INTERACTIVE PATH.** `lake`/`elan`/`lean` live at `~/.elan/bin`,
   which an automated/AI shell does not have on `PATH`. Prefix every command:
   `export PATH="$HOME/.elan/bin:$PATH"`. (An interactive login shell may already have it.) If elan
   is missing entirely, `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none --no-modify-path`.
   Pinned toolchain: `leanprover/lean4:v4.27.0`, Mathlib `v4.27.0` (`lean-toolchain`, `lakefile.lean`)
   — **do not bump** casually.
3. **Always fetch the Mathlib cache before building** (compiling Mathlib from source takes hours):
   ```bash
   export PATH="$HOME/.elan/bin:$PATH"
   lake exe cache get
   ```
4. **Build & verify** (run from the repository ROOT — `cd`-drift breaks `lake`):
   ```bash
   export PATH="$HOME/.elan/bin:$PATH"
   lake build LeanFlagAlgebras.MetaTheory                                   # 8001 jobs, green (§1–10 + §11.2–§11.8)
   grep -rnwE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'   # → empty
   { printf 'import LeanFlagAlgebras.MetaTheory\nopen FlagAlgebras.MetaTheory\n';
     for t in blowupClosed_root_plantable complementation_invariance degenerate_not_rootPlantable \
              coDegenerate_not_rootPlantable c4free_not_rootPlantable coC4free_not_rootPlantable \
              pinning_obstruction no_interior_pinning c5free_edge_not_rootPlantable \
              emptyType_rootPlantable heredClass_emptyType_rootPlantable no_closed_certificate_gap \
              Sσ_eq_singleton_of_edgeDegenerate edgeDegenerate_cone_collapse \
              coEdgeDegenerate_cone_collapse c5free_edge_no_closed_certificate_gap \
              relSσ_closure_eq relative_soundness relative_criterion relative_slackness_global \
              downward_cauchy_schwarz certificate_first_moment_sq_bound unique_slice_stability \
              kernel_slackness_global \
              relative_planted_criterion relative_positivstellensatz \
              mantel_not_relatively_plantable equality_slice_vanishing \
              parametricP4_tau_equation Graphon.slice_rigidity Graphon.approximate_moments; \
       do printf '#print axioms %s\n' "$t"; done; } > /tmp/chk.lean
   lake env lean /tmp/chk.lean      # each → axioms: [propext, Classical.choice, Quot.sound]  (no sorryAx)
   # …EXCEPT `parametricP4_tau_equation` (and every other Tier-2 certificate consumer:
   # the parametricP4_*/k4freeP4_* equations, parametric_recovery,
   # parametric_qualitative_stability), which legitimately also prints
   # `Lean.ofReduceBool, Lean.trustCompiler` — inherited from the Automation layer's
   # native_decide bridges, NOT from MetaTheory (which contains no native_decide).
   # The Automation layer's declared axioms (Zykov_K4_density_bound, Turan_limit_P4_density)
   # must appear in NO MetaTheory output — they enter only as hZykov/hne hypotheses.
   ```
   **Stale-`.olean` gotcha:** `lake build <single module>` can serve a stale `.olean`, so a "green"
   single-module build can hide a real error — `touch` the file (or run the full
   `lake build LeanFlagAlgebras.MetaTheory`) before trusting it.

   **Statement-level audit (separate from the mechanical re-verification above).** The build →
   `grep sorry` → `#print axioms` checks confirm the *proofs* are kernel-accepted and axiom-clean,
   but NOT that each Lean statement says what the paper claims. To audit that correspondence, a human:
   (i) reads each Lean `theorem`/`def` signature; (ii) compares it to the paper result at the line
   given in the `README.md` / `READING_GUIDE.md` paper-result tables; (iii) trusts the kernel for the
   proof itself (guaranteed by the empty `sorry`-grep + the `#print axioms` =
   `[propext, Classical.choice, Quot.sound]` checks above). The row-by-row checklist is `README.md`'s
   **"Auditing the correspondence to `paper.tex`"** section.
5. **Paper:** `LeanFlagAlgebras/MetaTheory/paper.tex` is self-contained; `latexmk -pdf paper.tex`
   builds it (TeX is at `/Library/TeX/texbin`). The Notes copy
   `papers/Notes/root_planting_criterion_and_c4_counterexample.tex` is kept byte-identical to it.

---

## What was done (commit-by-commit, newest first)

*Recent (§6/§7, refactor, unification, paper review): `dcf5285` → `d446996` → `2026a18` → `abb2ca1`
— each described in its own section below. §5 history follows.*

```
3a607f2  README: "how the existing flag-algebra formalisation enabled this"
1a51195  docs: README.md + ARCHITECTURE.md + READING_GUIDE.md
c228651  readability cleanup (docstrings/headers/lint; semantics-preserving)
78d7aa2  top-manifest status comment
e795f28  §5 finale: clone-closed classes are root-plantable  ← CAPSTONE
634d1c1  §5: rooting-measure-as-uniform-pushforward + blow-up limit
4b0855d  §5: planted-ratio limits (BinomialRatio) + rooting-measure weak convergence
bdc40e4  §5: clone-closed graph-class framework (GraphClass, cliqueFreeClass)
d79ce27  §5: constrained representation theorem  ← the hardest new foundational result
6637bbc  §5: planted estimate (equal non-root clones)
b514b96  §3: forbidden ideal = ℝ-span under heredity
5375e46  §5: total clone count
(… earlier commits build §2–§4 and the §5 counting infrastructure …)
```

## Key decisions & deviations (summary — full detail in `README.md`)

1. **Uniform clone sizes** in `planted_estimate` (exact binomial count instead of the paper's
   total-variation bound) → `ProductTV.lean` is correct but **superseded/unused** on the critical
   path.
2. **The constrained representation theorem** (`ConstrainedRep.exists_constrained_flagSeq_limit`) is
   a genuinely **new** strengthening of Razborov 3.3(b) (forbidden-free approximating flags); it was
   the foundational blocker.
3. **Weak convergence** is stated on `FlagDensitySpace σ` (to `(ℙ[φ₀]).map Subtype.val`), not on
   `X_σ` — finite-flag profiles are not honest homomorphisms.
4. Minor packaging/generalisations (`GraphClass` structure; `lem:support-as` for hereditarily-
   Lindelöf spaces; `forbiddenIdeal_eq_span` as a carrier equality; ℚ-valued planted mass).

---

## §6 / §7 — DONE (2026-06-16). How it was reused

The key idea: generalise the independent blow-up to `subBlowup G W` (within-class family `W`), which
covers the complete blow-up of §6 (`W = ⊤`) and the substitution of §7 (`W = H_v`). Off the diagonal
`subBlowup` agrees with the independent blow-up, and the §5 estimate only ever samples "good"
(transversal) sets, so the whole §5 pipeline carries over. New files (all green, sorry-free):
`SubstitutionBlowup`, `SubstitutionEstimate`, `SubstitutionSequence`, `SubstitutionClosed`
(`subst_root_plantable`, the §6/§7 analogue of `clone_root_plantable`), `TrueClone`, `Substitution`,
`ClusterGraph`. The §5 `PlantedEstimate.planted_estimate` was generalised in place to a
host-parametric `planted_estimate_host` (with `planted_estimate` now a one-line instance — §5
unchanged).

**Cleanup/refactor pass (commit `2026a18`):** two structural wins for §8+ and readability.
(A) Heredity was factored out of clone-closure into a shared `HeredClass.lean` base (the constraint
+ the two consumption lemmas + `graphFlag`), with `GraphClass extends HeredClass` (thin wrappers keep
§5 call sites unchanged); the §6/§7 `SubstitutionClass.lean` was folded into `HeredClass`. (B) The
construction-agnostic capstone helpers were extracted from `CloneClosed` into a shared
`CapstoneShared.lean` that both capstones import — so `SubstitutionClosed` no longer depends on the
§5 capstone. Full design rationale + module map: `README.md` (Deviations 5–6) and `ARCHITECTURE.md`.

**Unification pass (commit `d446996`):** §5/§6/§7 unified under the single-vertex `BlowupClosed`
property (`BlowupClosed.lean`) and `blowupClosed_root_plantable`; the three theorems became
corollaries via `…toBlowupClosed`. The one new lemma is the iteration bridge `BlowupClosed.toUniform`
(single-vertex blow-up closure ⟹ uniform full blow-up), built on `oneBlowup_iso` and `Mem_congr`.
Paper §7 rewritten as "A common generalisation: blow-up-closed classes".

**Paper review + Notes sync (commit `dcf5285`):** reviewed §5–§7 of `paper.tex`; added
`lem:general-planting-estimate` ("planting is blind to the interior"); fixed two intro/§Strengthening
claims that wrongly called substitution-closure the "broader"/"common" generalisation (it is the
*strictest* — `rem:strictness`). Synced the Notes copy. Paper compiles clean.

## §8 — DONE (2026-06-22). "Finite planting and the C₅-free class"

Six new modules (all green, `sorry`/`native_decide`-free, axioms `[propext, Classical.choice,
Quot.sound]`), wired into the `MetaTheory.lean` aggregator after `ClusterGraph`:

* **`FinitePlanting`** — `def:finite-local-planting` (`FinitePlanting`) + `thm:finite-local-planting`
  (`finitePlanting_root_plantable`: finite planting at a non-degenerate `σ` ⟹ `S_σ = Q_σ`). The §5/§7
  capstone argument with the blow-up sequence replaced by the abstract planting family `Hₜ`; reuses
  `CapstoneShared`/`WeakConvergence`/`SupportClosure` verbatim. New generic helper `flagSeqLimit_mem_Q0`
  (limit of forbidden-free flags ∈ Q₀) + embedding↔subgraph-count lemmas for the type-positivity.
* **`SparseRootRepair`** — `def:sparse-root-repair` + `thm:sparse-repair-planting`
  (`sparseRootRepair_finitePlanting`). The deviation worth recording: the paper's probabilistic
  coupling is replaced by a **coupling-free finite counting bound** `counting_coupling_bound`
  (the three-term `|p_H − p_G| ≤ 2·P_W[S⊄U] + P_W[S⊆U∧Bad]` split; the `C(N−k,q)` vs `C(n−k,q)`
  denominator mismatch is absorbed algebraically, no PMF/measure needed). Largest module (~1170 lines);
  has `set_option maxHeartbeats 1000000 in` on the capstone (perf only, no semantic shortcut).
* **`C5Free`** — `c5FreeClass : HeredClass` (`Mem G := C5g.Free G`, Mathlib `IsContained`/`Free`/`Copy`;
  `C5g := cycleGraph 5`) and `lem:c5-nbhd` (`c5free_neighborhood_edge_card_le`: `e(G[N(v)]) ≤ |N(v)|`
  via `P₄`-free ⟹ star/triangle components). Public helper `c5_copy_of_pentagon` (5 vtx + 5 edges +
  10 distinctnesses ⟹ `C5g ⊑ G`), reused by the planting-free proofs.
* **`C5OneRoot`** — `def:c5-one-root-planting` (`oneRootPlant`), `lem:c5-planting-free`
  (`oneRootPlant_c5free`), the sparse-repair instance `c5FreeClass_sparseRootRepair_oneVertex`, and
  `c5free_one_root_plantable` (`S₁ = Q₁`). Clause (iii) injects altered pairs into
  `(G.induce N(r)).edgeFinset` then applies `lem:c5-nbhd`.
* **`C5TwoRootNonEdge`** — two-root non-edge analogues: `twoRootPlant`, `twoRootPlant_c5free`,
  `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` (`S_η = Q_η`).
  Two neighbourhoods (`N(r)`, `N(s)`); the non-edge property comes free from the type being `⊥`.
* **`C5Blowup`** — `lem:c5-blowup` (`c5_blowup_free_iff_triangleFree`): an independent blow-up of a
  `C₅`-free graph is `C₅`-free if and only if triangle-free.

**How it was reused (for a future session):** `thm:finite-local-planting` is the §5/§7 capstone over
an abstract `Hₜ`; the construction-agnostic `CapstoneShared` toolkit and `tendsto_rootingMeasure_extend`
(generic over any convergent flag sequence) carried over unchanged — exactly as `CapstoneShared`'s
header anticipated ("reusable for §8+"). The workflow that worked: validate each module's *statement*
in a `/tmp` scratch via `lake env lean` (does NOT take the build lock, so safe to run alongside other
agents' module builds), then delegate each intricate proof to its own agent iterating on
`lake env lean <module>` (NOT `lake build` — that conflicts). Built per-module oleans (`lake build
<module>`) only after each agent finished, then the full aggregator build at the end.

**Correspondence / human audit:** `README.md` now has an **"Auditing the correspondence to
`paper.tex`"** section with a line-numbered `paper.tex`-label ↦ Lean-statement map for all of §8 and
a note on which statements (the `FinitePlanting`/`SparseRootRepair` defs and the planting `def`s)
deserve the closest reading. The §8 deviations (coupling-free counting; sum-type→`Fin N` presentation;
`hrs`; the two `maxHeartbeats` raises) are `README.md` Deviation 8; the reuse of the existing
flag-algebra + §5/§7 layer is `README.md` "How the existing formalisation enabled this" item 9.
`READING_GUIDE.md` (map table + reading order) and `ARCHITECTURE.md` (§8 module map + the
`finitePlanting_root_plantable` six-step walkthrough) are likewise updated.

## §9–§9.2 — DONE (2026-06-24). "Pinning obstructions; sparse degenerate; complementation"

Five new modules (all green, `sorry`/`admit`/`native_decide`-free, axioms `[propext,
Classical.choice, Quot.sound]`), wired into `MetaTheory.lean` after `Pinning`:

* **`EdgeObstruction`** — `def:edge-degenerate`. The one-vertex type `vtype := (⊥ : FlagType (Fin 1))`,
  the one-root edge flag `e : A^vtype` (= `⟦basisVector edgeFF⟧`, `edgeLabeled` = `⊤` on `Fin 2`
  rooted at `0`), the unlabelled edge `ρ := ⟦e⟧₀`, the denominator collapse `one_downward_vtype`
  (`⟦1⟧₀ = 1`, so the random-extension denominator is `1`), the specialised expectation
  `expectation_e` (`∫ χ e = φ₀ ρ`), the two **endpoint a.s.-pinning** facts
  `ae_e_eq_zero_of_pinned`/`ae_e_eq_one_of_pinned` (a `[0,1]`-valued mean-`0`/`1` variable is a.s.
  `0`/`1`), `EdgeDegenerate`/`CoEdgeDegenerate`, and the abstract obstructions
  `edgeDegenerate_not_rootPlantable_of_witness`/`coEdgeDegenerate_not_rootPlantable_of_witness` (over
  `pinning_obstruction`). The key insight (paper's "Endpoints are automatic" remark): both
  obstructions are endpoint cases of `thm:pinning`, so they route through the existing
  `pinning_obstruction` from a mere *expectation* condition.
* **`StarWitness`** — `thm:degenerate-obstruction` + abstract `cor:codegenerate`. The
  flag-sequence→`Q_vtype` assembly `exists_Qσ_point_edge_eq` (Razborov 3.3(a)
  `flagSeq_limit_mem_positiveHom` + compactness `increasing_flagSeq_contain_convergent_subseq`; the
  limit lands in `Q_vtype` via the new σ-typed `flagDensity_forbidden_eq_zero_of_mem`), the star /
  co-star constructions with `star_edge_density = 1` / `coStar_edge_density = 0`, and the concrete
  `degenerate_not_rootPlantable` (stars) / `coDegenerate_not_rootPlantable` (co-stars).
* **`C4Free`** — §9.1 `lem:c4-edge-zero` / `cor:c4-counterexample`. `c4FreeClass`
  (`Mem G := (cycleGraph 4).Free G`), the elementary Kővári–Sós–Turán bound `c4free_card_edges_sq_le`
  (`(2·e(G))² ≤ 2|G|³`, via a **cherry double-count** `∑ deg(deg−1) = ∑_{x≠y}|common nbrs| ≤ N(N−1)`
  and Cauchy–Schwarz), `c4FreeClass_edgeDegenerate` (edge density `e(G_t)/C(N_t,2)` squeezed to `0`),
  and `c4free_not_rootPlantable`. Public helpers `c4_copy_of_square`, `flagDensity_unlabelledEdge_eq`.
* **`DegenerateFamily`** — §9.1 `cor:degenerate-family` general principle:
  `edgeDegenerate_of_subquadratic` (subquadratic edge bound `e(G) ≤ f(|G|)`, `f N/N² → 0`, ⟹
  edge-degenerate). The four listed families (general `K_{s,t}`, even cycles, planar, forests) are
  instances via classical extremal bounds; only `C₄` is proved from scratch (the others' bounds are
  outside current Mathlib), so the criterion is the formalised content.
* **`DenseObstruction`** — §9.2 `cor:codegenerate` made concrete. The *dense*
  complement-of-`C₄`-free class `coC4FreeClass` (`Mem G := (cycleGraph 4).Free Gᶜ`), its
  co-edge-degeneracy `coC4FreeClass_coEdgeDegenerate` (edge density `1 − e(Gᶜ)/C(N,2) → 1`), and
  `coC4free_not_rootPlantable` — a dense hereditary class that *also* fails, so density is not the
  dividing line. The load-bearing `downwardNormalizingFactor_edge_eq_one` (so `φ₀ ρ` is the genuine
  edge density) is proved via `isomorphismCount edgeLabeled = 2` (the edge `K₂` has two type
  placements, both flag-iso via the `0↔1` swap). Complementation is used only at the elementary
  level (`e(G)+e(Gᶜ)=C(|G|,2)`, `coStarᶜ = star`), **not** the full `lem:complementation` iso.

**`lem:complementation` (§9.2) — DONE (2026-06-24, same session).** Root-plantability is invariant
under graph complementation (`complementation_invariance`: `RootPlantable (K.constraintOf σ) ↔
RootPlantable (K̄.constraintOf σᶜ)`; `complementation_invariance_oneVertex` the `σ = vtype` case).
Formalised in a **four-module stack** (1691 lines, all `sorry`-free, axioms `[propext,
Classical.choice, Quot.sound]`): `FlagComplement` (complement on flags `Flag.compl`/`uncompl` + the
density invariance `flagDensity₁_compl`/`flagDensity₂_compl` + `unlabel_compl` +
`downwardNormalizingFactor_compl`), `ComplementHom` (`complHom : PositiveHom σ → PositiveHom σᶜ` built
from the density profile via `positiveHomFromZeroSpaceOneMulProp`, packaged as the homeomorphism
`complHomeo`), `ComplementClass` (`HeredClass.compl` = K̄, `complHomeo_image_Qσ`), `ComplementInvariance`
(the measure pushforward `complHomeo_map_eq` via `measure_eq_of_integral_flag_eq`, the support transfer
`complHomeo_image_Sσ`, the capstone). **Proof-route deviation (worth recording):** the paper builds
the explicit flag-algebra complement *isomorphism* `C_σ : A^σ ≅ A^σ̄`; we build the complement
*homeomorphism* of homomorphism spaces directly (via density profiles), avoiding the algebra-iso
construction entirely — same theorem, leaner route (README Deviation 9b). The key engineering win was
Layer 1's CLEAN `uncompl` involution partner (honest `Eq`, no `σᶜᶜ` transport), so only the base
`∅ₜᶜ = ∅ₜ` transport (in `ComplementInvariance`) needed `Eq.rec`/`HEq` gymnastics. (The §9.2 *concrete*
dense instance `coC4free_not_rootPlantable` remains Lemma-50-independent — it uses only the elementary
edge-count identity, not even the homeomorphism, matching the paper's "identify the witness directly"
route, README Deviation 9a.)

**How it was reused (for a future session):** §9's positive-side machinery carried over wholesale —
`pinning_obstruction` (§9.3 `thm:pinning`, prior session) for the abstract obstruction;
`exists_constrained_flagSeq_limit` (§5 constrained representation) for the C₄ edge-density limit;
`HeredClass`/`constraintOf`/`mem_of_forbiddenFree`/`forbiddenFree_of_mem` (§5/§8 class framework) for
the classes; `flagSeq_limit_mem_positiveHom` + `increasing_flagSeq_contain_convergent_subseq` for the
star witnesses. The workflow: parse-check each module's *statements* (with `sorry`) via `lake env
lean` first, then delegate each module's proofs to its own agent iterating on `lake env lean
<module>` (no build lock), build per-module oleans only after each agent finished, then the full
aggregator build. `C4Free`'s `c4FreeClass_edgeDegenerate` is the template the `DegenerateFamily` and
`DenseObstruction` density-limit proofs mirror.

**Cleanup pass (same session):** deduplicated the two analytic helpers (the squared-density bound and
`2N/(N−1)² → 0`) — now public `edgeDensity_sq_bound` / `edgeDensity_bound_tendsto_zero` in `C4Free`,
reused by `DenseObstruction` (was duplicated); normalised `Filter.*` → bare (`open Filter`, matching
the rest of `MetaTheory/`); removed an unused `open scoped Topology` + a stale docstring bullet in
`EdgeObstruction`. **Correspondence / deviations:** the §9 audit rows are in `README.md` ("What is
formalised" + the §9 results table) and `READING_GUIDE.md`; the §9 deviations — chiefly **(a) Cor 51
`cor:codegenerate` proved *without* Lemma 50 `lem:complementation`** (direct-witness route —
independent of Lemma 50, which is itself separately formalised; see the `lem:complementation` — DONE
section above), plus the `cor:degenerate-family` criterion-only scope, the elementary cherry-count
`C₄` bound, and the edge-flag/`dnf=1` modelling — are `README.md` **Deviation 9**. `ARCHITECTURE.md`
has the §9 module map + the expanded §9 strategy paragraph.

**Row-by-row map pointer (§9–§9.2 + Lemma 50).** This WORKLOG describes the §9 / `lem:complementation`
modules in prose (a worklog, not a checklist), which is fine here. The full `paper.tex`-label ↦
Lean-name ↦ `file:line` map for §9–§9.2 *and* Lemma 50 lives in `README.md` and `READING_GUIDE.md` —
use those for the statement-level correspondence audit.

## §9.3–§9.5 — DONE (2026-06-26). "General obstruction; boundary pinning; the C₅-free edge type"

Six new modules (all green, `sorry`/`admit`/`native_decide`-free, axioms `[propext, Classical.choice,
Quot.sound]`), wired into `MetaTheory.lean` after the complement stack. **The whole of §9 is now
formalised.**

* **§9.3 `thm:pinning`** ("The general obstruction") was already present from the §8/§9 session as
  `Pinning.pinning_obstruction` — confirmed, no new work.
* **§9.5 — the `C₅`-free edge-type obstruction** (the headline that *refutes the all-types
  conjecture*). Two modules:
  * `C5FewTriangles` — `lem:c5-few-triangles` (`c5free_three_mul_triangle_le`: `3·T(G) ≤ 2·e(G)` via
    `3·T(G) = ∑_v e(G[N(v)])` (new combinatorial double-count `three_mul_card_cliqueFinset_three_eq`)
    `≤ ∑_v deg(v)` using `lem:c5-nbhd`), the unlabelled-triangle density `T(G)/C(N,3)`
    (`flagDensity_unlabelledTriangle_eq` + `induced_iso_top3_iff`), and the triangle-degeneracy
    `c5FreeClass_triangleDensity_zero` (mirror of `c4FreeClass_edgeDegenerate`).
  * `C5EdgeObstruction` — the two-root edge type `edgeType`, the triangle flag `F_tri` (`F_△`),
    `ae_Ftri_eq_zero_of_pinned` (`cor:c5-edge-pinned`), the book graph `bookLabeled` (`def:c5-book`)
    with `book_c5free`/`book_Ftri_density`, `exists_book_Qτ_point` (`lem:c5-book`), and the capstone
    `c5free_edge_not_rootPlantable` (`thm:c5-edge-not-root-plantable`). `cor:c5-no-pin` is the two
    no-obstruction-at-vtype facts (`c5free_triOverVtype_zero_on_Qvtype`, `c5free_edge_not_pinned`).
    Also the generalised quotient-point assembly `exists_Qσ_point_flag_eq`.
* **§9.4 — boundary pinning** (`thm:no-interior`). The four-module **edge-thinning stack**:
  `NoInterior` (`EdgeDeletionClosed` predicate), `EdgeThinning` (random Bernoulli edge-thinning over
  `Measure.pi`; `thinExpectDensity` + first-moment bounds + the second-moment realization
  `exists_thinned_realization`), `EdgeThinningLimit` (`exists_thinned_limit`: the thinned constrained
  limit `φ₀^λ ∈ Q₀` by a diagonal realization, mirroring `FinitePlanting`), and `NoInteriorThinning`
  (`exists_boolean_point_in_Sσ`: the `λ→0` weak-limit `{0,1}`-valued point of `S_σ` via L¹/Markov on
  the cylinder criterion) — closing the capstone `no_interior_pinning`.

**Deviations worth recording (for README Deviation list).** (a) §9.4 proof route: the paper uses
random thinning + **McDiarmid**; Mathlib has no bounded-difference inequality, so we used random
thinning + a **second-moment (variance/Chebyshev) concentration** — the variance bound rests on a
block-independence lemma (`1_S ⟂ 1_{S'}` when the two `k`-subsets share `≤ 1` vertex, via `Measure.pi`
coordinate independence). Same theorem, McDiarmid-free route. (b) The first-moment bound is the
**correct induced-density form** `thinExpectDensity ≤ C(C(|M|,2), e(M))·λ^{e(M)}` — the naive `≤ λ^q`
is *false* for induced densities (e.g. induced `P₃` in a thinned `K_n` has density `3λ²(1−λ) > λ²`);
the binomial constant is `λ`-independent so the `λ→0` argument is unaffected. (c) The boolean point
`ψ_σ` is built as the limit of the explicit "edgeless cloud" `σ ⊎ \bar K_m` and shown to be in `S_σ`
by an L¹/Markov cylinder argument (no abstract Dirac-from-moment-convergence machinery). (d) §9.5's
`lem:c5-few-triangles` is the faithful `3T ≤ 2e`; the triangle density `→0` squeeze mirrors §9.1.

**How it was reused.** §9.5 reused the §9.1 `C4Free` degeneracy template wholesale (density-→0
squeeze, `flagDensity₁_eq_subset_count_div` subset-counting, the `StarWitness` quotient-point
assembly). §9.4 reused `pinning`-free: `exists_constrained_flagSeq_limit` (§5), the `FinitePlanting`
diagonal-extraction pattern (§8), `CapstoneShared`'s `mem_closure_of_forall_finset_cylinder`, and the
`RandomHom` extension spec. **Workflow that worked:** scaffold each module's *statements* (with
`sorry`), parse-check via `lake env lean` (no build lock — safe alongside other agents), then delegate
each module's proofs to its own background agent iterating on `lake env lean <module>`; build
per-module oleans only after; full aggregator build + `#print axioms` at the end. The four §9.4
modules were proved by **four agents in parallel** (each owning one file, using the others' stable
*types* as black boxes), then the full clean rebuild connected the chain.

## Hygiene pass — DONE (2026-07-09, third session). "Cleanup / refactor / doc refresh"

A repository-wide cleanup of the 66 `MetaTheory/*.lean` modules and the four docs — **no new
results, no statement changes**, the verified sorry-free axiom-clean state preserved throughout.
End state: `lake build LeanFlagAlgebras.MetaTheory` → 7972 jobs green; `sorry`/`admit`/
`native_decide` grep empty; all headline theorems axiom-clean `[propext, Classical.choice,
Quot.sound]`; compiler warnings cut from ~25 to **6, all intentional** (see below).

**What was cleaned (88 edits across 43 modules, all build-verified):**
* Removed unused `open` namespaces / narrowed multi-namespace opens (~39 sites) — the bulk.
* Removed 11 redundant `import` lines (relying on transitive availability, e.g. `LabeledCount`
  no longer imports `SubflagDensity`, `RelativeSlackness` drops the now-unused
  `Mathlib.Algebra.QuadraticDiscriminant`).
* Lint: dropped unused `set … with h` equation bindings, deleted unused `have`s, underscore-prefixed
  unused private-helper parameters, anonymised unused `obtain`/`rcases` binders, removed redundant
  `simp only [...]` arguments in `BlowupClosed`, `omit`-guarded an unused section variable.
* **Tighter base integration:** `KernelSlackness.eval_flagQuadraticForm_nonneg` now proves its body
  by a pointwise instance of the base library's `flagQuadraticForm_nonneg`
  (`FlagAlgebra/QuadraticForm.lean`) instead of re-deriving it from `Matrix.PosSemidef`.
* Removed two genuinely-dead private lemmas (`SparseRootRepair.ratio_of_nat_le`,
  `DownwardAverage.unlabel_eval_eq_zero_of_degenerate`); added missing docstrings to a few public
  simp/projection lemmas.

**The one real bug the cleanup introduced and how it was caught (record this — it is the key
lesson):** the `BlowupSequence` agent removed `import ConstrainedRep` (correct — `BlowupSequence`
itself does not use it), but `SubstitutionClosed` had been reaching
`exists_constrained_flagSeq_limit` *transitively* through that import, so it broke. The per-file
`lake env lean <module>` checks all passed (they read the stable BASELINE oleans, which still had
everything), and the first full rebuild REPORTED SUCCESS while actually **serving a stale
`SubstitutionClosed.olean`** — the documented stale-olean gotcha. It only surfaced on a genuinely
clean rebuild whose "Build completed successfully (N jobs)" line was checked explicitly. Fix: add an
explicit `import LeanFlagAlgebras.MetaTheory.ConstrainedRep` to `SubstitutionClosed` (the module that
actually uses the identifier) — the correct outcome, not a revert. **Lesson for next time: after
import-removal cleanups, ALWAYS `touch` the whole layer and re-run the full `lake build`, and grep
for the explicit "Build completed successfully" line — never trust the exit code or a downstream
`#print axioms` alone (both can pass against stale oleans).**

**Remaining 6 warnings are all intentional and were deliberately left:** `BinomialRatio.hr` and
`C5TwoRootNonEdge.hrs` (paper-faithful statement hypotheses, unused in the proof but part of the
stated setup — see README Deviation 8d for `hrs`); three unused-section-variable warnings in
`ProductTV` (the superseded, off-critical-path module — kept untouched, one attempted `omit` fix
turned into whack-a-mole and was reverted); and one unused bound-variable `v` inside a public
statement's `∀`-type in `SubstitutionClosed` (alpha-renamable to `_`, but a statement-hypothesis
binder, so left).

**Workflow that worked (repeat it):** (1) capture the ground-truth compiler warnings by
`touch`-ing all modules and rebuilding; `shake` (unused-import detector) is available but was
finicky about olean freshness. (2) A 10-agent read-only analysis workflow surfaced 87 findings
(unused opens/imports, lint, base-reuse, dead code, docstrings) tagged safe/moderate/risky; I
kept the safe + high-confidence-moderate ones and SKIPPED risky base-reuse that edits imported
modules with defeq-load-bearing proofs, cross-module hoists, and dead-code the analysis flagged as
"needs author confirmation" (likely intentional API). (3) An 8-agent apply workflow made the edits
per module group, each `lake env lean`-verified with revert-on-failure. (4) The authoritative full
clean rebuild + `#print axioms` (this is where the stale-olean bug was caught and fixed). (5) Docs.

## §11.4–§11.8 — DONE (2026-07-10, fourth session). "The slice method + the graphon layer"

Twelve new modules (all green, `sorry`/`admit`/`native_decide`-free), wired into `MetaTheory.lean`
after `KernelSlackness`. **The whole applied slice programme §11.4–§11.8 is now formalised** —
§11.4 in full, §11.5–§11.8 with the partial-coverage caveats recorded in **README Deviation 14**
and the **PARTIAL** rows of the README results table / §11.4–§11.8 audit map (classical inputs as
named hypotheses `hpin`/`huniq`/`hZykov`/`hZykEq`/`hmod`/`hne`; kernel `R`-bounds as hypotheses;
Thm 91/92 existence halves only; Thm 102/Cor 106 kernel engines only; Thm 112(iv) open). Axioms:
`[propext, Classical.choice, Quot.sound]` throughout, **except** the certificate consumers
(`parametricP4_*`/`k4freeP4_*`, `parametric_recovery`, `parametric_qualitative_stability`), which
additionally carry `[Lean.ofReduceBool, Lean.trustCompiler]` — inherited from the `Automation`
layer's `native_decide` flag-enumeration bridges, no `native_decide` in `MetaTheory` itself; the
`Automation` layer's declared axioms `Zykov_K4_density_bound`/`Turan_limit_P4_density` are used by
NO MetaTheory theorem (`#print axioms`-verified). Full story: README "Axioms assumed" (two tiers).
Build: `lake build LeanFlagAlgebras.MetaTheory` → **8001 jobs green** (78 modules).

* **`RelativePlanted`** — §11.4 `def:relative-plantability` + `prop:relative-plantability`. The
  relative planted set `relQσ hc Y σ` (= `Q_σ(Y)`: density limits of in-class σ-flags whose
  unlabelled flags converge into `closure Y`) and `RelativelyRootPlantable`; `relQσ_isClosed`
  (diagonal), `relQσ_subset_Qσ`, the weak-convergence/portmanteau inclusion
  `support_subset_relQσ` (⟹ `relSσ_subset_relQσ`), the `Y = Q₀` recovery
  `relQσ_Q0_eq`/`relativelyRootPlantable_Q0_iff`, and part (ii)
  `relQσ_nonneg_implies_relEnsemble` + `relative_planted_criterion`.
* **`RelativeCertificateGap`** — §11.4 `thm:relative-certificate-gap`
  (`no_relative_closed_certificate_gap`): §10's closed-cone equality re-run over `relSσ` and the
  `Y`-seminorm (`YWithin`/`MemYClosure`/`relEnsCone`; the Stone–Weierstrass crux handles the
  `S_σ(Y) = ∅` degenerate branch).
* **`RelativePositivstellensatz`** — §11.4 `thm:relative-positivstellensatz`
  (`relative_positivstellensatz(_closure)`): slice-valid ⟹ class-valid up to `ε·1₀` with a
  finite penalty `M·∑ g_{j_i}²`, by compactness of `Q₀` + finite intersection of the sublevel
  sets `K_n`; the cone form gives the `‖·‖_{Q₀}`-closure of `C_{Q₀} + span{gⱼ²}`.
* **`CertificateSliceVanishing`** — §11.6 `prop:equality-slice-vanishing`
  (`equality_slice_vanishing` + `eqSlice`): the generic mining principle —
  `relative_slackness_global_sq` with `fᵢ := ℓᵢ²`, `n := 0`.
* **`ParametricP4Slice`** — §11.6 `thm:k4free-p4-equality-slice` +
  `thm:parametric-p4-equality-slice` (+ the hom halves of Prop 110 / Thm 112(i)–(ii)). The
  certificate bridge: the verified `CompleteGraphFreeP4.gap_identity` consumed through relative
  slackness on `parametricP4Slice r` (`parametricP4_cert`; the `p₀·f₀ + leftover` remainder
  folded into the slack term `n` — Deviation 14f), yielding
  `parametricP4_eta_equation`/`_tau_symm`/`_tau_equation`, `parametricP4_K4_density` (`hZykov`),
  `parametricP4_sq_bounds` (the 9/8, 1/5, 9/35 pattern), `parametricP4_K4_density_approx`
  (NO Zykov input); at `r = 3` the `κ₄` coefficient vanishes, so the `k4freeP4_*` forms are
  unconditional (`k4freeP4Slice`, `k4freeP4Slice_eq_parametric`). **Tier-2 axioms.**
* **`TuranLimit`** — §11.5 existence halves of `thm:turan-slice`/`thm:relative-mantel`: the
  Turán-graph flag sequence (Mathlib `turanGraph`), edge density `→ (r-1)/r`,
  `exists_turan_limit`, and the nonempty slices `turanSlice(_nonempty)`/`mantelSlice(_nonempty)`.
  The singleton claim (Erdős–Simonovits) and the support identities (i)–(iii) are UNFORMALISED.
* **`MantelNotPlantable`** — §11.4 `prop:mantel-not-plantable`
  (`mantel_not_relatively_plantable`): the parity-bipartite witness `knnPlusW`
  (`K_{n+1,n+1}` + isolated root — Deviation 14g; paper: `K_{n,n}+w`, same limit) gives a
  Mantel-slice planted view with rooted edge density `0`
  (`exists_mantel_planted_view_edge_zero`), so `relSσ ⊂ relQσ`; the pinning input `hpin` is
  Thm 92(i), an explicit hypothesis.
* **`SliceRecovery`** — §11.7 Cor 105 (first half)/Cor 104/Cor 107: `parametric_recovery`
  (`hZykEq` collapses the slice to `{χ★}`; the "consequently" support identities UNFORMALISED),
  `parametric_qualitative_stability` (+ `hne`, via `unique_slice_stability`),
  `k4free_qualitative_stability` (`huniq` = Thm 102's hom avatar). **Tier-2** on the two
  `parametric_*` results.
* **`GraphonBasic`** — §11.7 preliminaries: Mathlib has no graphons, so the `Graphon` structure
  (symmetric measurable `[0,1]`-kernel on `unitInterval`), `deg`/`codeg`,
  `edgeDensity`/`degSq`/`triDensity`, and the Fubini identities are built from scratch
  (Deviation 14b — the layer is standalone kernel measure theory).
* **`GraphonMoments`** — §11.7 `thm:parametric-moments` (`moments_T`/`_D`/`_variance`/
  `_interval`/`_regular_iff`, the `R_η = R_τ = 0` instance) + §11.8 `thm:approximate-moments`
  (`approximate_moments(_interval/_variance)`, certificate-free, every graphon); the a.e.
  hypothesis forms via `Rtau_eq_zero_iff_ae`/`Reta_eq_zero_iff_ae`.
* **`GraphonRigidity`** — §11.7 `thm:slice-rigidity` (`slice_rigidity`) + `cor:r3-rigidity`
  (`r3_rigidity`): the ladder `rigid_deg_ae` → `rigid_codeg_ae` → `rigid_sections_boolean` →
  the measurable partition (`P : I → Fin r`, fibers `1/r`, `W = 0/1` by block a.e. —
  Deviation 14c), colour classes grown by the Markov-selection trick.
* **`GraphonQuantStability`** — §11.8 kernel level: `quadratic_confinement`,
  `moment_deviation_bound`, `interval_localisation(_below)` (both halves of Thm 112(iii)),
  the `r = 3` chain `r3_edge_sq_bound`/`r3_degree_concentration`/`r3_edge_density_stability`/
  `r3_certificate_instance`, and `stability_via_modulus` (`ω_Tur` abstracted over the target
  predicate — Deviation 14d; the `ω_Zyk` route of Thm 112(iv) is NOT formalised, documented in
  the docstring). `R`-bounds enter as hypotheses.

**Deviations:** all recorded as **README Deviation 14 (a)–(g)** — hypothesis-ised classical
inputs, the standalone graphon layer + missing flag↔kernel dictionary, measurable-partition
rigidity, squared/abstracted quantitative forms, Tier-2 axiom inheritance, the folded certificate
remainder, and the `K_{n+1,n+1}` Mantel witness.

**Adversarial statement audit (keep this step):** a **9-agent** statement-vs-paper audit
(§11.4–§11.8, quantifiers/hypotheses/inequality directions/definitional faithfulness) found **NO
fidelity errors in the formalised statements**. It caught one **docstring overclaim** (fixed:
`stability_via_modulus`'s docstring now honestly scoped to the `ω_Tur` route, not all of
Thm 112(iv)) and drove **three same-session additions**: `Graphon.interval_localisation_below`
(the missing `p < α⁻` half of Thm 112(iii)), `parametricP4_sq_bounds`, and
`parametricP4_K4_density_approx`. Also fixed same-session: an open-namespace bug in
`SliceRecovery`.

**Workflow (what worked / what broke):** 12 statement scaffolds (with `sorry`) built once →
proofs delegated to **parallel agents in two rounds** — the first round was killed by rate limits
mid-flight and was relaunched clean (lesson: relaunch, don't resume half-dead agents) — each agent
iterating `lake env lean <module>` only (no build lock). One genuine cross-module fix:
**`GraphonMoments`' section-variable hypotheses had to be explicitly `include`-d**
(`include hη hτ`/`include hr`) so the exact-moment theorems carry their `R = 0` hypotheses in
their public signatures for the downstream `GraphonRigidity`/`GraphonQuantStability` consumers.
Then: aggregator build (8001 jobs) → `#print axioms` on every public declaration (two-tier check,
incl. the *negative* check that `Zykov_K4_density_bound`/`Turan_limit_P4_density` appear nowhere)
→ the 9-agent adversarial audit → docs → commit.

## §11.2–§11.3 — DONE (2026-07-09, second session). "Relative ensembles + complementary slackness"

Four new modules (all green, `sorry`/`admit`/`native_decide`-free, no `maxHeartbeats` raises,
axioms `[propext, Classical.choice, Quot.sound]` on all 33 public declarations), wired into
`MetaTheory.lean` after `C5EdgeInert`. **The foundational §11.2–§11.3 relative theory (Lemma
71–Prop 82) is now formalised**; §11.1 is prose (it cites the already-formalised §5–§8 criteria).

* **`RelativeSupport`** — §11.2. The relative support `relSσ Y σ` (= `S_σ(Y)`) generalises `Sσ`
  by replacing the `Qσ forb0` membership with an arbitrary `Y : Set (PositiveHomSpace ∅ₜ)` in the
  same closure-of-supports definition — so `Sσ_eq_relSσ` (`Y = Q₀` recovery) is `rfl`. Relative
  soundness `relative_soundness` (`prop:relative-soundness`; degenerate `φ₀⟨σ⟩₀ = 0` case via
  `downward_eval_eq_zero_of_degenerate`) and the **unconditional** relative criterion
  `relative_criterion` (`prop:relative-criterion`) — both directions are the "easy" directions of
  `support_criterion`, no Urysohn needed (relative semantics has no external benchmark to miss).
* **`RelativeClosure`** — §11.2 `lem:relative-closure` (`relSσ_closure_eq`:
  `S_σ(closure Y) = S_σ(Y)`). The one genuinely new analysis: weak continuity of the random
  extension on the positive-type-density region (`extend_tendsto` — flag-evaluation integrals are
  the evaluation-continuous ratios `φ ⟦f⟧₀ / φ ⟦1⟧₀` by the extension spec; ε/3 +
  `exists_flag_near` upgrades to all of `C(X_σ)` via
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), plus support lower-semicontinuity
  along weak convergence (`support_subset_closure_iUnion_support`; portmanteau
  `ProbabilityMeasure.le_liminf_measure_open_of_tendsto` on balls +
  `Measure.measure_compl_support`).
* **`RelativeSlackness`** — §11.3 `thm:relative-slackness` as the `relative_slackness_*` family
  (soundness / aggregate / per-term / slack approximate; slack, term, a.s. exact; global
  vanishing on `S_σ(Y)` via ±f `ae_nonneg_iff_nonneg_on_support` + `closure_minimal`), the
  `rem:cs-shape` square instances `_exact_ae_sq`/`_global_sq` (`fᵢ = l·l` ⟹ `ψ(l) = 0` a.s. /
  `l = 0` on the support; added post-audit), `downward_cauchy_schwarz`
  (`lem:relative-cauchy-schwarz` — a thin wrapper over the PRE-EXISTING base-library
  `square_downward_mul_ge_mul_downward_square`, RandomHom), the `√Δ` first-moment bounds in
  squared form (`certificate_first_moment_sq_bound(_one)`, `cor:sos-first-moments`), and
  `unique_slice_stability` (`prop:unique-slice-stability`; arbitrary index family —
  countability unnecessary; `tendsto_of_subseq_tendsto` + `CompactSpace.tendsto_subseq`).
* **`KernelSlackness`** — §11.3 `thm:kernel-slackness` (`kernel_slackness_*`): the matrix form
  over the base library's `flagQuadraticForm` (`⟨Qv,v⟩`); `eval_flagQuadraticForm` (evaluation =
  moment-vector quadratic form), the two real-PSD facts by `discrim_le_zero`
  (`posSemidef_dotProduct_mulVec_sq_le`, `posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero`),
  `kernelCombo` (= `wᵀQv`), and a **measure-free semantic-cone route** for the approximate bound
  (`downward_preserve_semanticCone` on `⟨Qw,w⟩•⟨Qv,v⟩ − (wᵀQv)²` — no degenerate-case split).

**Deviations (README Deviation 13):** (a) `Y` arbitrary ⊆ `X₀` (paper: nonempty ⊆ `Q₀`) — strict
generalisation, nothing needs the dropped hypotheses; (b) `√Δ` bounds in squared form (no
`Real.sqrt`); (c) `prop:unique-slice-stability` over an arbitrary index family; (d)
Cauchy–Schwarz by reuse of the existing RandomHom lemma; (e) kernel form on `flagQuadraticForm`,
`wᵀQv` as `kernelCombo` via symmetry, the rank/row-space closing sentence left as prose; (f)
remarks not formalised except `rem:cs-shape`'s square-instance readings (the `_sq` exports).

**Adversarial statement audit (this session's extra verification step):** a 5-agent workflow
(one auditor per module + a coverage critic) compared every Lean statement against the paper's
§11.2–§11.3 claims (quantifiers, hypotheses, inequality directions, definitional faithfulness).
Result: **no substantive mismatch**; all findings FAITHFUL or sanctioned-deviation, except one
low-severity coverage nit (the `rem:cs-shape` square instances not being exported) — fixed on the
spot by adding `relative_slackness_exact_ae_sq`/`relative_slackness_global_sq`.

**How it was reused.** `RelativeSupport` is `SupportClosure`/`DownwardAverage` re-run over `Y`
(same proofs, one membership swapped); the a.e.-vanishing arguments reuse the `forbidden_ae_zero`
pattern + `integral_eq_zero_iff_of_nonneg_ae`; `RelativeClosure` reuses the extension spec,
`exists_flag_near` (Stone–Weierstrass), `positiveHom_one_downward_pos`, and Mathlib's portmanteau
+ `Measure.support` API; the slackness modules consume `relative_soundness` + the spec only; the
kernel module reuses `FlagAlgebra/QuadraticForm.lean` (`flagQuadraticForm`,
`downward_preserve_semanticCone`, `le_def`) and `Matrix.PosSemidef.dotProduct_mulVec_nonneg`.
**Workflow (same as §9.3–§10, and it worked again):** scaffold all four modules' *statements*
with `sorry`, build the sorry-oleans once → four agents in parallel, one per module, each
iterating `lake env lean <file>` only (no build-lock conflicts), with a shared verified-API cheat
sheet and per-sorry proof-route comments → statement-drift check against a scaffold snapshot
(public declaration lists identical) → aggregator build (7972 jobs) → `#print axioms` on all
public declarations → **adversarial statement-audit workflow** (new step; keep it) → docs → commit.
NB this session ran in a fresh git worktree: the warm `.lake` was CLONED from the main checkout
with `cp -Rc` (APFS copy-on-write, ~30 s) instead of rebuilding — worked perfectly.

## §10 — DONE (2026-07-09). "The gap is invisible to density bounds"

Seven new modules (all green, `sorry`/`admit`/`native_decide`-free, no `maxHeartbeats` raises,
axioms `[propext, Classical.choice, Quot.sound]`), wired into `MetaTheory.lean` after the §9.4/§9.5
stack. **The whole of §10 (`sec:empty-type`, Prop 64–Cor 70) is now formalised.**

* **`DownwardAverage`** — the §10 engine. The two `PositiveHom`/`posHomPoint` roundtrips,
  `downwardNormalizingFactor_le_one` (unlabelling weights are probabilities, by injecting the label
  placements into `Fin n₀ ↪ Fin n`), the degenerate-type collapse
  `downward_eval_eq_zero_of_degenerate` (`φ₀⟨σ⟩₀ = 0` kills every unlabelled average — proved by
  unlabelling the level-`ℓ` expansion of `1`; no separate density-monotonicity lemma needed), the
  **master evaluation bound** `abs_downward_eval_le_of_abs_le_on_Sσ` (`|s| ≤ δ` on `S_σ` ⟹
  `|φ₀ ⟦s⟧₀| ≤ δ` on `Q₀`; drives Thm 66 with `δ = ε` and Prop 67 with `δ = 0`), and the singleton
  collapse `downward_eval_eq_of_Sσ_singleton`.
* **`EmptyTypeCollapse`** — `prop:empty-type` (Prop 64) + `cor:confined` (Cor 65). `⟨∅ₜ⟩₀ = 1`, the
  Dirac identity `extend_emptyType_eq_dirac` (`Ext_∅(φ₀) = δ_{φ₀}` — the paper's variance
  computation is subsumed by the Lemma-50-session moment-uniqueness theorem
  `measure_eq_of_integral_flag_eq`, since `downward` is the identity at `∅ₜ`), `Sσ_emptyType_eq`
  (`S_∅ = Q₀`), `emptyType_rootPlantable` + `heredClass_emptyType_rootPlantable`, and the semantic
  coincidence `emptyType_quotient_iff_ensemble` / `ensemble_implies_quotient_emptyType`.
* **`CertificateCones`** — `thm:no-closed-certificate-gap` (Thm 66). The cones `quotCone`
  (unlabelled averages of ambient sums of squares, Mathlib `IsSumSq`) and `ensCone` (of elements
  non-negative on `S_σ`), the `Q₀`-seminorm ε-closeness `Q0Within`/`MemQ0Closure`, the crux
  Stone–Weierstrass step `ensCone_subset_closure_quotCone` (approximate `√(max(s,0))` by a flag
  evaluation via `exists_flag_near`, square it), and the closure equality
  `no_closed_certificate_gap` — proved for EVERY type (non-degeneracy not needed).
* **`VanishingIdeal`** — `prop:ideal-zero` (Prop 67): four `δ = 0` instances of the master bound —
  vanishing on `S_σ` ⟹ zero unlabelled average, the ideal property, the pinning witness
  `(g − c·1)·h`, and the congruence form.
* **`BooleanPoint`** — the labelled empty-graph limit `edgelessPoint` and complete-graph limit
  `completePoint` in `X_vtype`: `IsEdgelessFlag`/`IsCompleteFlag`, per-size uniqueness of the
  edgeless/complete flag (at `vtype` and at `∅ₜ`), existence via limits of the rooted edgeless/
  complete flag sequences, and the workhorse `val_eq_boolean_of_nonEdgeless_zero` (the vanishing
  pattern forces the whole boolean profile, by size-`n` sum-to-one), giving
  `eq_edgelessPoint_of_nonEdgeless_zero` / `eq_completePoint_of_nonComplete_zero`.
* **`SinglePoint`** — `prop:single-point` (Prop 68). Edge-degeneracy kills every edge-containing
  unlabelled flag (`eval_eq_zero_of_edgeDegenerate`: expand the 2-vertex edge flag,
  `flagDensity_unlabelledEdge_pos`); dually for co-edge-degeneracy (via the size-2 classification
  `flagWithSize_two_edgeless_or_complete` + `nonEdge_eval_eq_zero_of_coEdgeDegenerate`); hence a.s.
  vanishing of all non-boolean flags and `Sσ_eq_singleton_of_edgeDegenerate` / `_coEdgeDegenerate`
  (`S_vtype = {point}`, given a constrained limit exists). Cone collapse:
  `edgeDegenerate_cone_collapse` / `coEdgeDegenerate_cone_collapse` — every ensemble-cone member
  agrees on `Q₀` with some `c•1₀`, `c ≥ 0`, itself in the quotient cone
  (`smul_one_mem_quotCone_vtype`): the §9 degeneracy counterexamples cost nothing for density
  bounds.
* **`C5EdgeInert`** — `cor:c5-edge-closed-inert` (Cor 70): the closed-cone equality at
  `(c5FreeClass, edgeType)` (`c5free_edge_no_closed_certificate_gap`, an instance of Thm 66), plus
  the inertness of the pinned witness: `F_△ = 0` on all of `S_τ` (`c5free_Ftri_zero_on_Sσ`), so
  `F_△` and all its flag-multiples unlabel to zero (`c5free_Ftri_mul_downward_eq_zero`).

**Deviations worth recording (README Deviation 12).** (a) `Q₀`-closures in ε-form
(`Q0Within`/`MemQ0Closure`), not a seminormed-space closure. (b) `quotCone` uses *ambient* sums of
squares — the smallest of the three sandwiched cones, hence the strongest closure equality, which
implies the paper's. (c) "zero in `A⁰[T₁]`" stated in evaluation form (`φ₀ u = 0`/`= c` for all
`φ₀ ∈ Q₀`) — a quotient-algebra equality would need a separation theorem the development doesn't
have; the paper's own proofs establish exactly the evaluation form. (d) Thm 66 proved without the
paper's non-degeneracy hypothesis. (e) the co-degenerate half of Prop 68 by direct mirror instead
of `lem:complementation`. (f) Prop 68's literal `S = {pt}` takes an explicit non-vacuousness
hypothesis (`Q₀ ≠ ∅`); the cone collapse avoids it.

**How it was reused.** §10 rests almost entirely on prior layers: `Sσ`/`support_criterion`/
`support_passes` (§4), the `eq:extension-expectation` spec
(`probMeasure_extend_emptyType_positiveHom_spec`), `measure_eq_of_integral_flag_eq` (the Lemma-50
session — it turns Prop 64's Dirac identity into a 10-liner), `exists_flag_near`
(Stone–Weierstrass), the base-library expansion lemmas `basisVector_quot_eq_sum` /
`sum_flagWithSize_eq_one` / `sum_positiveHom_basisVector_flagWithSize_eq_one` (which replace the
paper's "monotonicity" argument in the degenerate-type collapse), `Sσ_subset_eval_eq_of_ae_pinned`
(§9.3), `EdgeDegenerate`/`CoEdgeDegenerate`/`one_downward_vtype` (§9),
`downwardNormalizingFactor_edge_eq_one` (§9.2), `flagDensity_unlabelledEdge_eq` (§9.1),
`ae_Ftri_eq_zero_of_pinned` (§9.5), and the flag-sequence limit machinery
(`increasing_flagSeq_contain_convergent_subseq` + `flagSeq_limit_mem_positiveHom`).
**Workflow (same as §9.3–§9.5, and it worked again):** scaffold all seven modules' *statements*
with `sorry` and build the sorry-oleans once → six agents in parallel, one per module, each
iterating `lake env lean <file>` only (no `lake build` — no build-lock conflicts), with a shared
verified-API cheat sheet and per-module proof notes → statement-drift check against a scaffold
snapshot (public declaration lists identical) → per-module rebuilds → aggregator build (7968 jobs)
→ `#print axioms` on all 20 public §10 theorems → docs → commit.

## Next work / open follow-ups

**▶ TO RESUME (start here).** Everything through `paper.tex` **§10 is DONE**, plus the
**whole §11.2–§11.8 relative (slice) theory** — most recently the §11.4–§11.8 wave of 2026-07-10
(fourth session): the 12 new modules
`RelativePlanted`/`RelativeCertificateGap`/`RelativePositivstellensatz`/`CertificateSliceVanishing`/
`ParametricP4Slice`/`TuranLimit`/`MantelNotPlantable`/`SliceRecovery` +
`GraphonBasic`/`GraphonMoments`/`GraphonRigidity`/`GraphonQuantStability` + `MetaTheory.lean`
+ the README/ARCHITECTURE/READING_GUIDE/WORKLOG doc sync. All green, `sorry`-free,
statement-audited (9-agent adversarial audit vs the paper), axiom-clean modulo the sanctioned
Tier-2 certificate consumers (README "Axioms assumed"). **§12 is open problems — prose, nothing
to formalise** — so the remaining Lean work is the §11 partial-coverage frontier. Next targets,
in rough order of value (find results by `\label{...}`, **not** line number — they drift):

* **The §11.5 support identities** (the rest of `thm:turan-slice`/`thm:relative-mantel`, Thm
  91/92): the singleton claim is Erdős–Simonovits stability (big; possibly keep hypothesis-ised),
  but the **support identities via the Dirac/second-moment computations at the Turán limit** are
  self-contained and would also discharge `MantelNotPlantable`'s `hpin` hypothesis (Thm 92(i)).
  Inputs: `exists_turan_limit`, the extension-measure spec, `relSσ`.
* **The representation bridge (Lovász–Szegedy)** — the **big unlock**: graphon⟷hom
  correspondence for unlabelled limits. It would convert `Graphon.r3_rigidity`/`slice_rigidity`
  into `thm:k4free-p4-tripartite` (Thm 102) and `cor:top-endpoint-recovery` (Cor 106) as stated,
  discharge `SliceRecovery`'s `huniq`, and yield Cor 105's "consequently" support identities.
  Major project — scope it as its own multi-session effort.
* **The `R_τ⁻` kernel functional + Thm 112(iv)**: define `R_τ⁻ = ∫W(d(x)−d(y))²` at the kernel
  level, connect it to the certificate's τ⁻ square bounds, and formalise the `ω_Zyk` route of
  `thm:parametric-quant-stability` (iv) (currently documented as unformalised in
  `stability_via_modulus`'s docstring).

Reusable scaffolding for the above: the §11.2–§11.8 layer just completed (`relSσ`/`relQσ`, the
slackness families, `eqSlice`/`equality_slice_vanishing`, the `Graphon` kernel calculus,
`unique_slice_stability`), the generalised-blow-up machinery (`subBlowup`,
`planted_estimate_host`, `subst_root_plantable`, `BlowupClosed`), the finite-planting criterion
(`FinitePlanting`/`SparseRootRepair`), and the §9 obstruction + complement stacks.
**Workflow that worked this session (repeat it):** scaffold each statement (with
`sorry`) and build the sorry-oleans once → delegate each module's proofs to its own agent
iterating on `lake env lean <module>` (no build lock; relaunch clean if a round dies mid-flight —
rate limits killed round one this session) → statement-drift check vs the scaffold
snapshot → full aggregator build → `#print axioms` on every public declaration (two-tier check)
→ adversarial statement-audit workflow vs the paper (9 agents this time; again caught real gaps:
a docstring overclaim + three missing statement halves, all fixed same-session)
→ docs → commit. In a fresh worktree, clone the warm `.lake` from the main checkout with
`cp -Rc` (~30 s) instead of rebuilding.

**Already DONE (do NOT re-attempt):** ALL of §1–§10 AND §11.2–§11.8 — most recently the
§11.4–§11.8 slice method + graphon layer (`RelativePlanted`/`RelativeCertificateGap`/
`RelativePositivstellensatz`/`CertificateSliceVanishing`/`ParametricP4Slice`/`TuranLimit`/
`MantelNotPlantable`/`SliceRecovery`/`GraphonBasic`/`GraphonMoments`/`GraphonRigidity`/
`GraphonQuantStability`, session 2026-07-10 #4; PARTIAL-coverage caveats in README Deviation 14 —
the *remaining halves* listed under "▶ TO RESUME" above are fair game, the formalised parts are
not); before that the §11.2–§11.3 relative theory (`RelativeSupport`/`RelativeClosure`/
`RelativeSlackness`/`KernelSlackness`, session 2026-07-09 #2); before that the whole of §10
(`sec:empty-type`, Prop 64–Cor 70; the seven modules `DownwardAverage`/`EmptyTypeCollapse`/
`CertificateCones`/`VanishingIdeal`/`BooleanPoint`/`SinglePoint`/`C5EdgeInert`, session 2026-07-09);
before that §9 / §9.1–§9.5 (the obstruction modules
`EdgeObstruction`/`StarWitness`/`C4Free`/`DegenerateFamily`/`DenseObstruction`, the §9.4 thinning
stack, the §9.5 `C₅`-edge pair), `lem:complementation` (Lemma 50; the four-module stack
`FlagComplement`/`ComplementHom`/`ComplementClass`/`ComplementInvariance`), `cor:codegenerate`
(Cor 51), `thm:pinning` (Thm 53). §9 committed+pushed (`4533cf6`/`e416e0e`/`14ee426`/`c3c149a`/
`4288088`; §8's six modules earlier in `39dc693`, abstract `Pinning` in `25f1bb4`). This file is
tracked+committed on `main` as `METATHEORY_WORKLOG.md` (renamed from `WORKLOG.md`).
* **Non-`C₄` degenerate families (`cor:degenerate-family`).** The three non-`C₄` families (general
  `K_{s,t}`, even cycles `C_{2k}`, planar) are formalised only as *instances* of the abstract
  criterion `edgeDegenerate_of_subquadratic` — their concrete extremal (subquadratic edge-count)
  bounds are outside current Mathlib, so only the criterion is proved from scratch (only `C₄` has its
  bound proved here).
* **(Optional cleanup, NOT done) Collapse §5's capstone fully.** `clone_root_plantable` (§5) keeps
  its original direct proof; the corollary form `clone_root_plantable_blowup` (via the general
  theorem) exists alongside. Rerouting `clone_root_plantable` itself through the general theorem
  would make ~600 lines of the §5-specific independent-blow-up capstone (`BlowupSequence`'s
  `blowupFlagSeq` + limit lemmas, `CloneClosed`'s `planted_cylinder_mass` + iso lemmas) redundant.
  Pruning them is a clean but large/risky followup (needs care: `SubstitutionSequence` reuses some
  `BlowupSequence` helpers like `blowupHostEquiv`/`plantedSet`/`fin_card_le_of_embedding`). Left
  undone deliberately to keep the verified §5 milestone intact. Decide with the user before doing it.

---

## Notes for a future Claude / AI session (on either machine)

* **Portable context = this file + the committed `MetaTheory/*.md` docs** (`README`/`ARCHITECTURE`/
  `READING_GUIDE`). The richer machine-local AI memory under `~/.claude/.../memory/` (e.g.
  `metatheory-sections-6-7-done.md`) exists only on the machine where it was written and is **not**
  Dropbox-synced — do not rely on it cross-machine; this WORKLOG is the source of truth.
* **Workflow that worked well this project:** scaffold a precise statement (with `sorry`) and build it
  to confirm it typechecks → delegate the intricate Lean proof to an agent that iterates on
  `lake build` → independently verify (full rebuild + `grep -rnwE 'sorry|admit|native_decide'` empty +
  `#print axioms` = `[propext, Classical.choice, Quot.sound]` only, no `sorryAx`) + `git status` for
  strays → wire into the `MetaTheory.lean` aggregator → commit. Mirror the §5 file as the template
  when generalising. **When rerouting a clean theorem through a new (`sorry`-stubbed) one, finish the
  proof or revert the reroute** — else you regress a previously-clean result.
* **Gotchas:** lake/elan NOT on PATH (`export PATH="$HOME/.elan/bin:$PATH"`); build from repo ROOT
  (cwd drift breaks `lake`); `lake exe cache get` first; `lake build <single module>` can serve a
  stale `.olean` (`touch` it or full-build before trusting green); `git status` shows `.vscode/`,
  `AGENTS.md`, `CLAUDE.md`, `papers/.DS_Store` as untracked strays — leave them (this
  `METATHEORY_WORKLOG.md` is now tracked, not a stray); the
  user's `papers/POPL27/paper_draft.tex` is their own work — don't commit it. The `MetaTheory.lean`
  aggregator is the source of truth for what is in the build.
