# MetaTheory formalisation — worklog & resume notes

*A cross-machine handoff and resume doc for the `MetaTheory/` formalisation. **Tracked by git** and
committed to `main` as `METATHEORY_WORKLOG.md` (renamed from the previously-untracked `WORKLOG.md` and
added to the shared `taeyool` repo on 2026-06-25), so `git pull` keeps it current across machines like
any other doc. (My detailed AI working memory under `~/.claude/` is **machine-local** and will **not**
be on a different machine — this file plus the other committed `MetaTheory/*.md` docs are the portable
context.)*

Last updated: 2026-06-26. (Stopping point: §1–**9.5** of `paper.tex` formalised — the WHOLE of §9.
This session added **§9.3** (`thm:pinning` general obstruction — already present as `pinning_obstruction`),
**§9.4** (`thm:no-interior`, boundary pinning for edge-deletion-closed classes — the edge-thinning
stack), and **§9.5** (the `C₅`-free edge-type obstruction `thm:c5-edge-not-root-plantable`, refuting
the all-types conjecture). See "§9.3–§9.5 — DONE" below. Prior sessions: §1–9.2 + `lem:complementation`
("§9–§9.2 — DONE"), §8 ("§8 — DONE"). `lake build LeanFlagAlgebras.MetaTheory` → **7961 jobs green**
(55 modules); `grep -rnwE 'sorry|admit|native_decide'` over `MetaTheory` → empty; all headline
theorems (`pinning_obstruction`, `no_interior_pinning`, `c5free_edge_not_rootPlantable`) `#print axioms`
= `[propext, Classical.choice, Quot.sound]`. **NOT yet committed** (6 new untracked modules +
`MetaTheory.lean` modified) as of this update — confirm with the user before committing/pushing to
`main`. Next target: **§10** (`sec:empty-type`, "the gap is invisible to density bounds") and **§11**
(strengthening by a further constraint; the `K₄`-free-`P₄` equality slice).)

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
  39 modules, 7945 jobs; **now with §9 / §9.1 / §9.2 (incl. `lem:complementation`): 49 modules,
  `lake build LeanFlagAlgebras.MetaTheory` → 7955 jobs green**;
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
  classes, §9.1/§9.2), and `complementation_invariance` (Lemma 50, §9.2). These are the obstruction
  capstones — a class can FAIL to be root-plantable, on both the sparse and the dense side.
* **Scale:** 49 Lean modules (33 through §7, +6 for §8, +1 §9 abstract `Pinning`, +5 for §9/§9.1/§9.2, +4 for `lem:complementation`) + 4 committed reference docs (`README`/`ARCHITECTURE`/`READING_GUIDE`/`METATHEORY_WORKLOG`,
  same dir), in namespace `FlagAlgebras.MetaTheory`, aggregated by
  `LeanFlagAlgebras/MetaTheory.lean` and in the top build manifest `LeanFlagAlgebras.lean`.

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
   lake build LeanFlagAlgebras.MetaTheory                                   # 7955 jobs, green (§1–9.2 + Lemma 50)
   grep -rnwE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'   # → empty
   { printf 'import LeanFlagAlgebras.MetaTheory\nopen FlagAlgebras.MetaTheory\n';
     for t in blowupClosed_root_plantable complementation_invariance degenerate_not_rootPlantable \
              coDegenerate_not_rootPlantable c4free_not_rootPlantable coC4free_not_rootPlantable \
              pinning_obstruction; do printf '#print axioms %s\n' "$t"; done; } > /tmp/chk.lean
   lake env lean /tmp/chk.lean      # each → axioms: [propext, Classical.choice, Quot.sound]  (no sorryAx)
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

## Next work / open follow-ups

**▶ TO RESUME (start here).** Everything through `paper.tex` **§9 (all of §9.1–§9.5) +
`lem:complementation` is DONE**, green and `sorry`-free, axiom-clean. §9.3/§9.4/§9.5 are **green and
verified but NOT yet committed** (6 untracked modules `C5FewTriangles`/`C5EdgeObstruction`/`NoInterior`/
`EdgeThinning`/`EdgeThinningLimit`/`NoInteriorThinning` + modified `MetaTheory.lean` + this WORKLOG) —
confirm with the user, then commit/push. The natural next target is **§10** (`sec:empty-type`, "the gap
is invisible to density bounds") and **§11**. In paper order (find sections by
`\section{...}`/`\label{...}`, **not** line number — they drift):

* **§10 "The gap is invisible to density bounds"** — `prop:empty-type` (`sec:empty-type`), with
  `cor:confined`, `thm:no-closed-certificate-gap`, `prop:ideal-zero`, `prop:single-point`,
  `cor:c5-edge-closed-inert`: degenerate-type gaps collapse at the empty type, so they never affect
  closed-cone density bounds — the "payoff" that pinning obstructions are harmless for actual bounds.
* (Further, larger/applied: **§11 "Strengthening by a further constraint"** — relative-ensemble
  enhancements + the `K₄`-free-`P₄` equality-slice / stability results, `thm:relative-mantel`,
  `thm:k4free-p4-equality-slice`/`-tripartite`, …)

Reusable scaffolding for the above: the generalised-blow-up machinery (`subBlowup`,
`planted_estimate_host`, `subst_root_plantable`, `BlowupClosed`), the finite-planting criterion
(`FinitePlanting`/`SparseRootRepair`), and the §9 obstruction + complement stacks. **Workflow that
worked this session:** scaffold each statement (with `sorry`) and parse-check via `lake env lean`
first → delegate each intricate proof to its own agent iterating on `lake env lean <module>` (no
build lock) → build per-module oleans → full aggregator build → `#print axioms` → commit. For a big
multi-piece result (like `lem:complementation`) build it in **verified layers**, one module each.

**Already DONE this session (do NOT re-attempt):** §9 / §9.1 / §9.2 (the five obstruction modules
`EdgeObstruction`/`StarWitness`/`C4Free`/`DegenerateFamily`/`DenseObstruction`), `lem:complementation`
(Lemma 50; the four-module stack `FlagComplement`/`ComplementHom`/`ComplementClass`/`ComplementInvariance`),
`cor:codegenerate` (Cor 51), `thm:pinning` (Thm 53). All committed+pushed (`4533cf6`/`e416e0e`/`14ee426`/
`c3c149a`; §8's six modules earlier in `39dc693`, abstract `Pinning` in `25f1bb4`). This file is now
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
