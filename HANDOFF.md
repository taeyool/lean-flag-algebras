# Session handoff — refreshed 2026-06-10

Notes to resume work on another machine (e.g. the office). This repo is under
Dropbox **and** pushed to `origin`, so both sync paths work. Durable per-fact notes also
live in `~/.claude/.../memory/`, which is **machine-local** (not on the office machine),
so the durable facts are reproduced here.

> The prior version of this file (dated 2026-05-23) was badly stale. The whole prose-pass
> / sorry-survey / "POPL27 §3–§10" narrative it carried has been superseded — the paper was
> moved out of `POPL27/`, renamed in place, and grown a large new arc. That history is in
> git if needed (`git log` around `e0dd9ca`..`2da51b8`). This refresh describes HEAD.

## Shared-agent protocol

This file is shared working memory for Codex and Claude Code. Treat it as a handoff
record, not as an authority that overrides the repository:
- Before relying on any hash, line number, build status, or "clean tree" claim here, verify
  locally with `git status --short --branch`, `git log --oneline -5`, and a quick `rg` in
  the relevant file. `HANDOFF.md` is intentionally untracked and can drift from HEAD.
- Do not overwrite this file from model memory. Read it first, patch it incrementally, and
  preserve useful prior facts unless they are explicitly stale.
- Do not stage or commit `HANDOFF.md` unless the user explicitly asks. It is currently a
  Dropbox-synced local handoff, not part of the tracked repository state.

## CURRENT STOP POINT — 2026-06-10

**Verified git state:** `main` tracks `origin/main` and is currently at `3829417`
("update"), after `4daf508` and `2cd443f`.  Tracked tree has one local prose edit:
`papers/Notes/root_planting_criterion_and_c4_counterexample.tex`.  Usual untracked
local files are present: `.vscode/`, `AGENTS.md`, `CLAUDE.md`, `HANDOFF.md`,
`papers/.DS_Store`.

**Work done 2026-06-10 (local, not yet committed):** continued the root-plantability
clarity pass from the June 9 handoff, focusing on the planted blow-up theorem and the
finite local planting proof.  No mathematics changed.  The edits:
- expanded the planted blow-up estimate's conditional-sampling sentence so it says the
  non-labelled clone-class probabilities are proportional to normalised class sizes and
  equal to $1/(n-k)+O_m(\operatorname{err}_N)$;
- specified in the clone-root-plantability proof that the finite random-labelling
  distribution samples a random induced embedding of $\sigma$ and converges by the
  finite-graph form of the random-extension theorem;
- made explicit that \cref{lem:planted-estimate} plus the choices of
  $t,\lambda,N_j$ put every planted root inside the closed cylinder before applying
  \cref{lem:planted-mass} and Portmanteau;
- mirrored the same clarification in the finite local planting proof, spelling out that
  membership in the closed cylinder comes from the two $\eps/3$ errors and that the weak
  convergence is in the ambient product space.

**Verification:** ran
`latexmk -pdf -interaction=nonstopmode root_planting_criterion_and_c4_counterexample.tex`
from `papers/Notes`.  Build succeeds, PDF is **37 pages**, and a final log scan for
`Warning|undefined|Undefined|multiply|Overfull|Underfull|Rerun` found no LaTeX warnings
(only the package name `rerunfilecheck`).

**Next target:** either commit the current prose-only edit, or continue the same
surgical clarity pass into the later root-plantability examples and the exact finite
certificate gap discussion.  The mathematical open problem noted earlier remains the
exact finite-certificate gap for the $C_5$ edge type.

## PRIOR STOP POINT — 2026-06-09

**Verified git state:** `main` == `origin/main` == `2cd443f`
("FlagAlgebra: rename labeledSubgraph* to labeledGraph* for consistency").  This is newer
than the June 3 stop point below; per the protocol, trust `git log` over older hashes in this
file.  The tracked tree currently has one intentional local edit:
`papers/Notes/root_planting_criterion_and_c4_counterexample.tex`.  Usual untracked local
files are still present: `.vscode/`, `AGENTS.md`, `CLAUDE.md`, `HANDOFF.md`,
`papers/.DS_Store`.

**Newer upstream history since the old stop point:** after the root-planting clarity commits,
the repo received several Lean flag-generation / naming commits and POPL27 experience-paper
commits.  The current HEAD commit `2cd443f` is a Lean naming cleanup; it does not touch the
root-planting paper.  The latest tracked commit touching the root-planting paper is still
`f28acb3`.

**Resumed work done 2026-06-09 (local, not yet committed):** continued the §2→§3 clarity
sweep exactly where the June 3 handoff pointed:
- standardized the intro's lone "nonnegative building blocks" to "non-negative";
- added a short sentence after the extension-expectation formula explaining that
  $\phi_0(\brak\sigma)>0$ is the positive-probability conditioning event;
- added a short post-lemma sentence explaining how `lem:support-as` converts almost-sure
  non-negativity under random extensions into pointwise non-negativity on supports;
- added a parenthetical at `thm:support-criterion` spelling out that non-degenerate means
  $\phi_0(\brak\sigma)>0$ for some $\phi_0\in Q_0$.
- After the user noticed the term was easy to miss at Definition 3, promoted the buried
  sentence defining non-degenerate types into an explicit unnumbered §2 paragraph
  "Non-degenerate types" and repeated the equivalent $Q_0$ condition inside the
  root-planting definition.
- After the user worried that "limit" and "positive homomorphism" were being used
  interchangeably without enough guidance, strengthened §2's "Positive homomorphisms as
  limits" paragraph into an explicit dictionary: a limit means a positive homomorphism
  unless an approximating sequence is named; unlabelled limits are points of
  $\Homp(\A^0[\T],\R)$; $\sigma$-labelled/rooted limits are points of
  $\Homp(\A^\sigma[\T],\R)$.  Also clarified that $Q_\sigma$ is the space of constrained
  $\sigma$-labelled limits and $Q_0$ the space of constrained unlabelled limits.
- After the user noticed that references in the proof of Theorem 4 could render as
  "Theorem 1/2" instead of "Lemma 1/2", fixed the theorem-like environment setup with
  `aliascnt`.  The labels now keep the shared numbering but carry their correct cleveref
  types: `lem:support-as` is Lemma 1, `lem:support-passes-general` is Lemma 2,
  `def:root-planting` is Definition 3, and `thm:support-criterion` is Theorem 4.
- After the user asked what "normal" meant in the last paragraph of the proof of Theorem 4,
  clarified that it is topological normality: in a metrizable space, disjoint closed
  subsets can be separated by a continuous function.  The proof still uses Urysohn and
  Tietze exactly as before.
- After the user noticed that the proof of Theorem 4 silently treats
  $f\in\A^\sigma[\T_0]$ as a function on positive homomorphisms, added the evaluation
  pairing at the start of the proof: $f$ denotes the continuous map
  $\chi\mapsto\chi(f)$ on $X_\sigma$, so "$f\ge0$ on $S_\sigma$" means
  $\chi(f)\ge0$ for every $\chi\in S_\sigma$.
- Audited the final paragraph of the proof of Theorem 4 after the user worried about
  hallucinated use of Urysohn/Tietze/Stone--Weierstrass.  The argument is correct, and the
  paragraph now spells out the hypotheses: $Q_\sigma$ is metrizable/normal, $S_\sigma$ and
  $\{\psi\}$ are disjoint closed subsets of $Q_\sigma$, $Q_\sigma$ is closed in
  $X_\sigma$ (so Tietze applies), and the evaluation functions from
  $\A^\sigma[\T_0]$ form a unital point-separating real subalgebra of $C(X_\sigma)$ (so
  Stone--Weierstrass/Razborov applies).
- Replaced the jargon phrase "uniform density" in that paragraph with the concrete
  statement actually used: every continuous function on $X_\sigma$ can be approximated
  arbitrarily well in sup norm by elements of $\A^\sigma[\T_0]$.

**Verification:** ran
`latexmk -pdf -interaction=nonstopmode root_planting_criterion_and_c4_counterexample.tex`
from `papers/Notes`.  Build succeeds, PDF is **37 pages**, and the final log scan has no
undefined-reference, multiply-defined, overfull, underfull, or LaTeX warning lines.

**Current section map after the local edit:** §1 Introduction 139 · §2 Flag-algebra
background 295 · §3 Constrained classes 444 · §4 Support-closure criterion 551 ·
§5 Clone-closed 658 · planted blow-up estimate 688 · root-plantability theorem 783 ·
§6 Complete blow-ups 867 · §7 Substitution-closed 947 · §8 Finite local planting 1031 ·
sparse repairs 1148 · §9 Degenerate 1255 · examples 1328 · complementation 1398 ·
general obstruction/conjecture 1476 · pinning boundary 1527 · §10 Gap invisible 1577 ·
§11 C5-free split 1767 · one-root 1815 · non-edge type 1911 · edge obstruction 2020 ·
§12 Strengthening 2141 · hereditary 2148 · relative ensembles 2166 · Mantel equality
slice 2219 · certificate equality slices 2296 · §13 Open problems 2787.

**Next target:** the specific June 3 loose ends have now been handled.  Continue the
same surgical clarity pass through the proof of the support-closure criterion and the
root-plantability examples, or switch back to the mathematical open problems below
(especially the exact finite-certificate gap for the C5 edge type).

## PRIOR STOP POINT — 2026-06-03 (historical; keep for context)

**Git state (resume from here):** `main` == `origin/main` == `eb5cbc8` (a **merge**). My
root-planting clarity commits `576fe75…f28acb3` are all in history (`f28acb3` is an ancestor
of HEAD) and the paper holds every one of their edits — verified, builds clean at 36 pages.
HEAD also now contains the collaborator's (`taeyool`) **parallel track**, merged cleanly
because it touches files **disjoint** from the root-planting paper:
- experience-report paper `papers/POPL27/paper_draft_experience_report.tex` (§3 intro + §5–6
  "reflection layer" revisions — commits `a89a486`, `e5f1d01`); and
- Lean flag generation: `Flags/FlagLoader.lean`, `Flags/FlagDef.lean`,
  `FlagAlgebra/Compute/Generate.lean` ("Phase 2: typed flags" `212968a`, JSON-loader removal
  `8a3ceab`).
Tracked tree is clean, nothing unpushed/mid-edit. (An earlier draft of this line said HEAD
`f28acb3` — that was my line's tip *before* the merge. Per the protocol above, trust
`git log`, not this hash.)

**Paper title is now** *Completeness of Forbidden-Subgraph Reasoning in Flag Algebras: A
Root-Planting Criterion* — the "Root Planting, Quotient Semantics, and a Counterexample…"
title quoted further down is **stale**.

**Late-session commits (newest first), all on the one file
`papers/Notes/root_planting_criterion_and_c4_counterexample.tex`, all pure exposition — NO
mathematics changed:**
- `f28acb3` gloss **"non-degenerate type"** at its §2 definition (~line 349): added intuition
  (σ realised = positive density in some limit, so a copy can be sampled/labelled) + a
  degenerate contrast. This is the hypothesis of Theorem 4 (`thm:support-criterion`).
- `9c7c2a9` **name heredity** at the ideal step of the §3 Q_σ argument (~line 454): "a graph
  with a non-T₁ induced subgraph is outside T₁" is heredity (contrapositive) = the
  forbidden-induced-subgraph characterisation, family = whole complement T₀∖T₁.
- `648d4f6` say "**factors through**" not "descends" at the key §3 step (~line 462).
- `8903702` **expand the §3 Q_σ converse** (~lines 438–469) into three explicit steps:
  (i) factor χ through 𝔮_σ (universal property ⇒ need the kernel); (ii) heredity ⇒ forbidden
  flags form an **ideal** ⇒ generated ideal = their span ⇒ ker 𝔮_σ = span(forbidden), nothing
  more; (iii) χ kills the kernel ⇒ unique positive hom ψ ⇒ χ ∈ Q_σ.
- `3d368c5` **anchor the ⟨σ⟩ sampling sentence** (~line 345): a limit has no vertices, so
  "k random vertices form σ" → limiting probability over approximating G_n; "form" → "induce".
- `d9290e2` **K₄-free P₄ slice is nonempty** in `thm:k4free-p4-tripartite` (~line 2314): T_3
  attains π_{P4}=32/9 (achievability direction, `API.CompleteGraphFreeP4` at r=3), so
  Y_{P4} = {T_3} exactly, not merely "every element is tripartite".

**Earlier today (same clarity arc, detail below):** `0e0599f`/`576fe75` polished the intro and
finished British-spelling normalisation; `8858fd6`/`7bf27fa` swept §2's first two paragraphs
(the F^σ "isomorphism classes" fix and the quotient/induced-density compatibility sentence).

**Session summary — 2026-06-03 (§2 "Flag-algebra background" clarity pass begins).** Picked
up the term-by-term clarity pass at §2 (the prior handoff's NEXT TARGET). The user drove it,
pointing at two confusing spots; I applied surgical glosses. **No mathematics changed.** What
was clarified, both in §2's first two paragraphs (~lines 280–301):
- **"Types and flags." paragraph (~line 286):** the sentence "Flags are taken up to
  label-preserving isomorphism, and $\F^\sigma[\T]$ … is the countable set of all of them"
  had an ambiguous **"them"** (the flags, or their isomorphism classes?). Fixed to: "…is the
  countable set of all such **isomorphism classes** (so two flags related by a root-fixing
  isomorphism are the same element of $\F^\sigma$)."
- **"The flag algebra." paragraph (~line 300):** the original "…and are what make ``density''
  a well-defined linear functional on the whole space" was too compressed. The user's
  preferred framing (after rejecting a wordier first attempt of mine): **just state the
  compatibility plainly.** Final text: "This quotient is compatible with the induced-density
  evaluation $p(\,\cdot\,,G)$: for every larger $G$ the identity $p(F,G)=\sum_{|H|=|F|+1}
  p(F,H)\,p(H,G)$ holds, so $p(\,\cdot\,,G)$ respects the defining relations and descends to a
  well-defined linear functional on $\A^\sigma$." (The intended content: the quotienting that
  defines $\A^\sigma$ is *compatible* with subgraph-induced density in the sense of that chain
  equation — that is all "well-defined" means here. The user dislikes scaffolding like
  "descends from the free span / same value on any representative"; prefers the bare
  compatibility statement.)

**Workflow note (learned today):** the user's "point at a confusing word → surgical gloss" loop
holds. Lessons: (1) the user prefers the **shortest** statement that conveys the math
— state the fact, don't unpack what "well-defined"/"quotient" mechanically mean; trim
scaffolding. He likes the **"factor through"** idiom and values **intuition + a concrete
contrast** in a definition (e.g. degenerate vs non-degenerate). (2) **Pushing to `main` may be
blocked** by the auto-mode classifier until the user explicitly says "push" — commit freely,
batch the push until authorized. (This session he said "Commit and push" / "push" each batch,
so pushes were authorized turn-by-turn.) (3) **Dropbox-sync drift bit me today (important):**
the working `.tex` is touched and re-synced mid-session — the other machine's commits were not
visible to my first `git log` (it showed a stale `2da51b8`) until Dropbox landed them. So
**re-read a file right before each Edit** (one Edit failed "string not found" because the
buffer changed under me) and **trust `git log` over this handoff's hash** for HEAD; some
pre-sync edits I made were silently overwritten (harmless — already upstream).

**NEXT TARGET (where to resume):** the §2→§3 clarity sweep is in good shape (this session
covered §2 "Positive homomorphisms as limits", the ⟨σ⟩ and non-degenerate definitions, and the
§3 Q_σ converse). Resume the same point-and-gloss loop wherever the user reads next. Loose
ends noted today:
- §2 still has un-swept later material if wanted: the extension-theorem / `Ext_σ` paragraph
  (~line 356) and the support lemma (`lem:support-as`, ~line 384).
- **Tiny straggler:** the intro (~line 239) has a lone unhyphenated "nonnegative building
  blocks" vs the document's dominant "non-negative" — I offered to fix it, user hasn't said yes.
- **Optional:** a back-reference "non-degenerate (Section 2)" at Theorem 4's statement
  (`thm:support-criterion`, ~line 538) — offered, not yet wanted.

**Active work is entirely Thread B (the paper).** The recent commits after the Lean work
all touch paper files only — see "Recent commits" below. **No Lean files have changed**
since the last handoff; Thread A is stable and sorry-free (status reproduced below).

**Prior-session summary (the work that produced `2da51b8`; kept for context).** That session
shifted from proving individual examples to turning the relative-ensemble idea into a reusable
method:
- We clarified that ensemble semantics can be enhanced by non-hereditary limit
  constraints, unlike quotient semantics.
- We added relative ensemble support, the Mantel equality-slice example, and a general
  "equality slices force certificate terms to vanish" proposition.
- We applied that proposition to the verified `K4freeP4` certificate, extracting the
  three rooted equations on edge/non-edge supports.
- We used those equations to recover the balanced complete tripartite extremizer.
- We generalized the extraction to the parametric `CompleteGraphFreeP4` certificate,
  with Zykov equality clearly marked as the external input for full recovery.
- We upgraded uniqueness to stability: qualitative compactness stability, certificate
  square-term bounds, and a quantitative edge-density estimate
  `|p - 2/3| <= C Delta^(1/4)` followed by graphon Turan stability.
- We then audited the whole main file for mathematical consistency. No correctness
  issue was found; the important subtlety is that the direct certificate route gives a
  fourth-root modulus, not a square-root modulus.

### IMPORTANT — the paper moved and was renamed
- The main paper is now **`papers/Notes/root_planting_criterion_and_c4_counterexample.tex`**
  (it used to be under `papers/POPL27/`; moved 100%-rename in commit `2878b1f`
  "Organized papers folder"). `papers/POPL27/` now holds only build artifacts plus
  `paper_draft_experience_report.tex`.
- **All `.tex` sources now live under `papers/Notes/`** (tracked): the main paper, the two
  C₅ notes below, and the older `eqv_of_forbidden_subgraph_*` / `flagmatic_to_lean` drafts.
- Two **new satellite notes** were added (commit `fb6ac94`), feeding the paper's C₅ section:
  - `papers/Notes/c5_free_one_root_planting.tex` — "One-Root Planting for the C₅-Free Class".
  - `papers/Notes/c5_free_edge_type_obstruction.tex` — "A Two-Root Obstruction for the
    C₅-Free Class" (the book-edge pinning obstruction).

### Paper build — verified clean
- `cd papers/Notes && latexmk -pdf -interaction=nonstopmode root_planting_criterion_and_c4_counterexample.tex`
- **Gotcha:** the agent shell's cwd keeps resetting to `papers/`, so prepend
  `cd papers/Notes &&` to every build or latexmk reports "Could not find file".
- To check warnings, read the *final* LaTeX `.log` for `undefined` / `multiply defined`;
  the first pdflatex pass always prints "undefined on page 1" before the `.aux` is populated
  — that is normal, not an error.
- Builds clean after every commit today: **36 pages**, no errors, no undefined references,
  0 overfull boxes (PDF/aux are build artifacts, not tracked).

## Mathematical status of the paper (root-planting substance unchanged since `2da51b8`)

> The mathematical substance below is unchanged since `2da51b8`; today only clarified the
> introduction's prose/terminology (see the session summaries above).  The latest tracked
> commit touching this paper is `f28acb3`; the repository HEAD is newer because of disjoint
> Lean / POPL27 work.

Title: *Completeness of Forbidden-Subgraph Reasoning in Flag Algebras: A Root-Planting
Criterion.* The abstract/intro were rewritten for accessibility in
`e78e39b` and then lightly polished in `8ec31df`/`2da51b8`. The thesis is unchanged:
**quotient semantics ⟺ ensemble semantics iff root-plantability** (soundness free;
root-plantability = completeness; this is an *incompleteness* result for the quotient
calculus). The main developments now in the paper are:

1. **The C₅-free split is RESOLVED — and the naive all-types conjecture is FALSE**
   (§"The C₅-free split", lines ~1655–2028). It must be analysed type by type:
   - one-vertex type: no elementary pinning obstruction, **root-plantable**
     (`thm:c5-one-root`, backed by `c5_free_one_root_planting.tex`);
   - two-root **non-edge** type: also root-plantable (`thm:c5-nonedge`);
   - two-root **edge** type: a **book edge gives a new pinning obstruction**
     (`thm:c5-edge-pinned` / `thm:c5-edge-not-plantable`), so the all-types C₅-free
     conjecture is **false**. *But* this edge-type gap is **closed-cone inert**
     (`thm:c5-edge-inert`) — see point 3.

2. **Equality-slice / stability mining from verified certificates** (§"Strengthening by
   a further constraint", subsecs ~2047–2660). A verified density certificate can be read
   *backwards* as a system of rooted local equations on its equality slice:
   - Mantel equality slice records the labelled local structure of the balanced complete
     bipartite extremizer (typical vertex degree 1/2) — `thm:relative-mantel`.
   - The **verified K₄-free P₄ certificate** extracts labelled equations forcing edge
     density 2/3 ⇒ recovers the **balanced complete tripartite** extremal graphon
     (`thm:k4free-p4-tripartite`, `thm:k4free-p4-certificate-route`).
   - **Commit `6ae2e2b`: stability.** Qualitative (`cor:...-qualitative-stability`,
     by compactness) + quantitative: if the P₄ defect is Δ then the three rooted square
     terms are O(Δ) (`prop:...-certificate-stability`) and `|p − 2/3| ≤ CΔ^{1/4}`
     (`thm:...-certificate-to-turan-stability`), composing with any graphon Turán-stability
     modulus.
   - Parametric K_{r+1}-free P₄ certificate ⇒ r-partite local equations
     (`thm:parametric-p4-equality-slice`); full identification for r≥4 still leans on the
     **equality case of Zykov's clique-density theorem** (`thm:...-recovery-zykov`).

3. **"The gap is invisible to density bounds" is now a hardened theorem**
   (§, lines ~1465–1654): `thm:no-closed-certificate-gap` — the incompleteness **never
   improves an asymptotic density bound at the closed-cone level**. Supporting props:
   empty-type collapse (`thm:empty-type-collapse`), vanishing ideal unlabels to zero
   (`prop:vanishing-ideal`), degenerate roots collapse to a point (`prop:degenerate-point`).
   The C₅ edge-type gap is the first natural example that is non-root-plantable yet
   closed-cone inert with support that is **not** a single point.

### Historical section map (June 3 line numbers)
> For current line numbers, use the June 9 map near the top of this file.  The numbers below
> are kept only to interpret older notes.

§1 Introduction 116 · §2 Flag-algebra background 241 · §3 Constrained classes & supported
homs 370 · §4 Support-closure criterion 452 · §5 Clone-closed ⇒ root-plantable 539
(planted blow-up estimate 569; theorem 664) · §6 Complete blow-ups & true twins 748 ·
§7 Substitution-closed classes 828 · §8 A finite local planting criterion 912 (sparse
repairs 1029) · §9 Degenerate ⇒ not root-plantable 1136 (examples 1209; complementation
dense obstruction 1279; general obstruction & conjecture 1357; **pinning always boundary**
1408) · §10 The gap is invisible to density bounds 1458 · §11 **The C₅-free split** 1648
(one-root 1696; two-root non-edge 1792; **edge-type obstruction** 1901) · §12 Strengthening
by a further constraint 2022 (hereditary 2029; relative ensemble enhancements 2047; Mantel
equality slice 2100; **certificate equality slices / K₄-free P₄ stability** 2177) ·
§13 Open problems 2661.

## Open problems (current, from §13 — the live to-do list)
1. **Beyond sparse root repairs** — extend planting past pure blow-ups / sparse old-edge
   repairs to denser-but-structured or root-incident repairs, or amalgamation hypotheses.
2. **The characterisation conjecture** (`conj:characterisation`, tentative) — is *absence of
   a pinning obstruction* already sufficient for root-plantability? Decisive next test: a
   type/class with no pinning obstruction but no root-plantability, or a theorem ruling it
   out under checkable hypotheses. (The C₅ split sharpens but does not settle this.)
3. **Exact certificate gaps before closure** — closed-cone gaps are ruled out
   (`thm:no-closed-certificate-gap`); the open question is whether C^ens_σ can strictly
   exceed C^quot_σ *before* closure in a way that changes a finite SDP / rational
   certificate. The **C₅ edge type is the first natural test case**.
4. **Equality-slice mining beyond classical equality theorems** — mine a certificate whose
   equality slice is **not** already controlled by a standard extremal equality theorem
   (Turán/Zykov), and see if the relative equations alone determine new structure.

## Thread A — Lean (unchanged; reproduced for completeness)

`LeanFlagAlgebras/API/CompleteGraphFreeP4.lean` — Murphy–Nir Thm 1.3(i), P₄ density in
K_{r+1}-free graphs. **Builds, `sorry`-free.** Both directions present:
- Upper bound `Kr_plus_1_free_P4_density_upper_bound`: `P4_density ≤[K_{r+1}]
  12·((r-1)/r)³·1` via a corrected SOS certificate; depends on `axiom Zykov_K4_density_bound`.
- Lower bound `Kr_plus_1_free_P4_density_achievable` (collaborator `d78b6f5`): depends on
  `axiom Turan_limit_P4_density`.
- `#print axioms` of the upper bound = `[propext, Classical.choice, Zykov_K4_density_bound,
  Quot.sound]` (no `sorryAx`).

**Durable Lean facts (do not rediscover):**
- Original multipliers `p₁,p₂,p₃` were each wrong by ×6 (`p₀` was right). Corrected,
  `D = 3r²−11r+9`: `p₁ = 6(r-1)(3r-7)/(r²D)`, `p₂ = 3(9r²−32r+25)/(2D)`,
  `p₃ = 3(15r²−24r+7)/(2r²D)`, `p₀ = 18(r-1)²/D`. Reduce **exactly** to `K4freeP4`'s
  `(8/9, 5, 35/9)` at r=3.
- `f₁,f₃` use **real** coeffs `((r:ℝ)-1)`, `((r:ℝ)-2)` (were ℕ-truncated nsmul). r=3
  reference file: `LeanFlagAlgebras/API/K4freeP4.lean`.
- Certificate is an **inequality**: `P4 + Σpᵢfᵢ + leftover = K·1`, `leftover = Σgapⱼ·Fⱼ ≥ 0`.
- Zykov axiom is **provably not** reachable by the local 4-vertex flag-SOS cone (f₀ has a
  negative K₄-atom coefficient; every square's K₄-coefficient is ≥0). Refuted dead-ends:
  telescoping ratio inequality is false in general; k₄ is not a function of (k₂,k₃); the
  bound is asymptotic (finite graphs can exceed it).
- Gotcha: `≤[F]` has **no precedence** — parenthesise any `+`-sum on its LHS.
- `axiom`s ≠ `sorry`: discharging `Zykov_K4_density_bound` / `Turan_limit_P4_density` is a
  separate, harder objective, deliberately not pursued.

### Flagmatic `sorry` survey (background, nothing changed)
Two live `sorry`s exist only in auto-generated Flagmatic skeletons
(`LeanFlagAlgebras/Flagmatic/Mantel.lean:72`, `.../C4Turan.lean:122`); the SDP matrices and
PSD proofs are filled, only the main bound bodies are `sorry`. They are **not in the build
path of any end-to-end theorem**. There is also a separate namespace collision
(`Flagmatic/C4Turan` vs `API/C4TuranAPI` both `namespace C4Turan`) that would break a full
`lake build`. A deliberate decision was made **not** to pursue closing these. (See the
git history of this file around `e0dd9ca` for the full three-options analysis if revisited.)

## How to resume
- **State:** `main` == `origin/main` == `2cd443f`.  There is one intentional local paper
  edit from the 2026-06-09 clarity pass:
  `papers/Notes/root_planting_criterion_and_c4_counterexample.tex`.  Usual untracked local
  files remain (`HANDOFF.md` included).  If committing, stage only the paper file unless the
  user explicitly asks to track this handoff.
- **Paper build:** `cd papers/Notes && latexmk -pdf -interaction=nonstopmode root_planting_criterion_and_c4_counterexample.tex`.
- **Lean build:** `lake exe cache get` (fetch Mathlib cache first — source build takes
  hours), then `lake build LeanFlagAlgebras.API.CompleteGraphFreeP4`. Toolchain pinned
  (Lean v4.27.0 / Mathlib v4.27.0); don't bump. NB: 0 project oleans are cached, so any
  build recompiles the whole project incl. slow flag-loading (~2 s/flag).
- **Scratch checks:** system `python3` has `sympy`. The in-tree `.conda` is wrong CPU arch —
  don't use it.

## Two work threads (one-liners)
- **Thread A — Lean** (`API/CompleteGraphFreeP4.lean`): done, sorry-free, two axioms.
  Next substantive step (open question, hard): formalize the support-closure criterion +
  free soundness direction in Lean (`forbidLE` already *is* ensemble semantics).
- **Thread B — paper** (`papers/Notes/root_planting_criterion_and_c4_counterexample.tex`):
  active. C₅ split resolved (all-types conjecture false), equality-slice/stability mining
  added, closed-cone inertness hardened. Live to-do = the 4 Open problems above.

## Recent root-planting paper commits (not current repo HEAD)
The current repo HEAD is recorded in the June 9 stop point above; this block is the
root-planting paper history that matters for Thread B.
```
7bf27fa state flag-algebra quotient compatible w/ induced density ┐ 2026-06-03
8858fd6 clarify F^sigma is the set of flag isomorphism classes     ┘ §2 clarity pass
53cb61b gloss "sum-of-squares contributions" in the intro   ┐ 2026-06-02
4f532e6 clarify the C4-free counterexample + hereditary def  │ introduction
baa7209 gloss "positive density" in the root-planting intro  │ clarity /
0e0599f clarify introduction terminology + polish abstract   │ terminology
576fe75 finish British-spelling normalization                ┘ pass
2da51b8 update                                      ┐ accessibility/polish
8ec31df update                                      │ on main paper intro
e78e39b Retitle and rewrite abstract/intro for accessibility
a2c548f Merge branch 'main' of https://github.com/taeyool/lean-flag-algebras
074912f POPL27 §5: rewrite introduction             │ old POPL27 experience note
09b7e77 Merge branch 'main' of https://github.com/taeyool/lean-flag-algebras
d31a491 POPL27 §2.4–2.5: rewrite Examples 2.3 and 2.10 for triangle-free setting
6ae2e2b Add K4-free P4 stability analysis          ┐ all touch ONLY
9d9893d Add parametric P4 equality slice analysis   │ papers/Notes/ (paper +
b528329 Add relative ensemble equality slices       │ the two C5 notes)
1879c35 Develop root planting criteria and certificate gaps
fb6ac94 Document C5 root-planting split (adds c5_free_*.tex)
```

## Key files
- Paper: `papers/Notes/root_planting_criterion_and_c4_counterexample.tex` (+ C₅ notes
  `papers/Notes/c5_free_one_root_planting.tex`, `c5_free_edge_type_obstruction.tex`).
- Lean upper bound: `LeanFlagAlgebras/API/CompleteGraphFreeP4.lean`
  (r=3 reference: `LeanFlagAlgebras/API/K4freeP4.lean`).
- This handoff is intentionally untracked but Dropbox-synced. If the user wants this state
  available from a fresh clone without Dropbox, stage and commit `HANDOFF.md` explicitly;
  otherwise leave it untracked.
