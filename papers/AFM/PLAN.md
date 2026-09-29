# AFM resubmission plan: "Formalizing Flag Algebras in Lean"

Drafted 2026-09-29. Working file: `papers/AFM/paper_afm.tex`.

## Status (2026-09-29, end of session)

- Phases 1-3 are done (skeleton, framing, body). See Section 11 for details.
  The paper builds cleanly (48 pages).
- **Next: phase 4, to be run on the desktop machine.** It needs heavy Lean
  builds, which this laptop session did not attempt:
  - `#print axioms` on the seven `*_turanDensity` theorems, `Mantel_Turan`,
    `ErdosPentagon_Turan`, and the Goodman theorems;
  - re-measuring Appendix A.
  The TOPLAS measurements for scale: the pentagon took about 2,700 s and
  42 GB under `decide +kernel`; the K5/C5 kernel builds peak at tens of GB.
- Open decision for phase 4: either first do the axiom check plus a single
  timing run per case (and the five-run protocol later), or run the full
  five-run protocol in the background from the start.
- Still deferred: whether to include the 6-vertex `K3freeC6` case.
- Build the paper with `latexmk -pdf paper_afm.tex` in `papers/AFM/`.

## 1. Background

- **TOPLAS outcome.** The TOPLAS submission (`papers/TOPLAS/paper_toplas.tex`,
  submitted 2026-08-16) was returned as out of scope, presumably because no
  suitable referees were found. There are no referee comments to address, so
  this resubmission is mainly a change of audience. It is not a repair of
  technical objections.
- **Sources.**
  - `papers/TOPLAS/paper_toplas.tex`: the base text. It is concise and it
    describes the current `flag_certificate` implementation.
  - `papers/arxiv/paper_arxiv.tex` (arXiv 2607.23500 v1): source of the
    mathematician-facing material to restore.
  - `papers/MetaTheory/paper.tex`: the companion paper with the full
    meta-theory.
  - `papers/TOPLAS/TOPLAS_SUBMISSION_AUDIT.md`: pre-submission audit. Several
    of its items are still open (Section 8 below).
- **Target venue.** Annals of Formalized Mathematics (AFM), a diamond open
  access overlay journal on Episciences.
  - Papers are written for mathematicians and should "describe the
    mathematical lessons learned during the formalization process". New
    mathematics is not required.
  - The main results must link explicitly to specific code in the artifact.
    The paper should make informal/formal correspondences clear and highlight
    and explain mismatches.
  - The manuscript must first be deposited on arXiv/HAL/Zenodo. For us this
    means arXiv v2 of 2607.23500.
  - The artifact must be open source with a Software Heritage ID (SWHID).
  - Any LaTeX class is allowed, no page limit is stated, and review is
    single-blind.
  - References: <https://afm.episciences.org/page/instructions-for-authors>,
    <https://afm.episciences.org/page/aims-and-scope>

### How the paper addresses AFM's nine reviewer criteria

| # | Criterion | Where the paper answers it |
|---|---|---|
| 1 | Novelty of the formalization | Intro contributions; Related Work leads with prior Lean combinatorics and the concurrent flag-algebra formalizations (Davey et al. local flag algebras, Spiegel) |
| 2 | Novelty/importance of the mathematics | Intro "why flag algebras matter" (restored from arXiv); first formalization of the asymptotic Erdős pentagon density |
| 3 | Insight / lessons on representation | Ensemble semantics and root-plantability (Sec. 8); "Lessons" section (Sec. 7) |
| 4 | Generality | Ambient algebra reused across forbidden graphs; general theory rather than one theorem |
| 5 | Integration with libraries | Built on Mathlib `SimpleGraph`, `Finsupp`, measure theory; say explicitly what is or is not upstreamable |
| 6 | Transferable lessons | Sec. 7, including the restored "Which obstacles are Lean-specific?" paragraph |
| 7 | Size/complexity | New size table (LOC, declaration counts) and the compile-time appendix |
| 8 | Influence of the prover/foundation | Quotients, `HEq`, `Fintype` instance coherence, `decide +kernel` vs `native_decide` |
| 9 | Readability/documentation of code | Artifact appendix with a statement-to-declaration table and build instructions |

## 2. Decisions recorded

- **Base text:** the TOPLAS tex. The arXiv text still describes the older
  `gen-skeleton` script workflow; TOPLAS describes the current elaboration-time
  `flag_certificate` tactic.
- **Title:** "Formalizing Flag Algebras in Lean", matching arXiv v1. The AFM
  version becomes arXiv v2.
- **Cases:** keep the same seven certificates as TOPLAS.
  - The 6-vertex `K3freeC6` case is deferred (Section 10).
  - The `K5freeEdgeClean`, `K5freeEdgeReduced` and `C5freeEdgeReduced` variants
    are excluded.
- **Meta-theory:** keep roughly the TOPLAS summary length, cite the companion
  paper, and align terminology with it.
- **Lean listings:** keep most of them. AFM readers are proof-assistant users.
- **Document class:** `article` with `authblk`, taken from the arXiv preamble.
  Bibliography via BibTeX from a copy of `papers/TOPLAS/refs.bib`.
- **AI disclosure:** keep the TOPLAS paragraph and expand it modestly
  (Section 8, item A5).
- **Style:** no em-dash parentheticals in prose. Keep TOPLAS-level concision.

## 3. Global changes

### 3.1 Reframing vocabulary

Remove the programming-languages framing throughout.

- "certificate-to-proof compiler" -> "certificate verification" / "the
  certificate checker" (keep the tactic name `flag_certificate`).
- "compile(d) bounds", "compilation" -> "verified bounds", "checking".
- "trust model" -> a short "What Lean checks" paragraph.
- "frontends", "statement anchor", "failure semantics", "translation
  fidelity" -> drop, or say plainly in one sentence.
- Keep "specification layer" and "reflection layer". Proof by reflection is
  standard vocabulary for formalizers, but define it plainly on first use.
  "Automation layer" can stay as a section-internal label.
- After editing, grep for: `compil`, `trust`, `frontend`, `translation`,
  `elaboration-time`, `metaprogram`, `PL`, `soundness`. Each remaining hit
  should be deliberate.

### 3.2 Claims to correct everywhere

- Call the results "the asymptotic form of Mantel's theorem" and "the
  asymptotic Erdős pentagon density theorem, pi(C5; K3) = 24/625".
  Relevant locations: abstract, contributions, Sec. 5.4, Sec. 6, conclusion.
- Replace "all known proofs use flag algebras" with a scoped statement, e.g.
  "the published proofs cited here use flag algebras".
- State the novelty claim precisely: "to our knowledge, the first
  proof-assistant formalization of the asymptotic density statement
  pi(C5; K3) = 24/625".
- Remove every statement that the K5-free and C5-free files use
  `native_decide` (see Section 5).
- Reword "Lean recomputes every claimed fact" / "takes none of these numbers
  on trust" to "Lean checks every proof obligation used by the final proof
  term" (audit item 1.3).

## 4. Section-by-section plan

Line numbers refer to `papers/TOPLAS/paper_toplas.tex` (T) and
`papers/arxiv/paper_arxiv.tex` (A) at the time of writing.

### Preamble and front matter (T 1-392)

- Replace the acmart preamble with the arXiv preamble (A 1-240).
- Keep from TOPLAS:
  - the robust `\lean` macro that breaks underscores (T 86);
  - `\emergencystretch`;
  - the TikZ flag macros.
- Remove:
  - acmart workarounds (T 7-19, 327);
  - `\setcopyright`, `\acmJournal`, `\acmYear`;
  - CCSXML and `\ccsdesc`;
  - the `\authorsaddresses` block;
  - `\Description{...}` inside figures;
  - `\boldparagraph` (replace with `\paragraph`);
  - the `acks` environment (replace with `\section*{Acknowledgments}`).
- Authors: use the TOPLAS author data, with ORCIDs and the corrected email
  `sangil@ibs.re.kr`. arXiv v1 has the typo `sagil@`, which v2 fixes.
- Keywords: drop "tactic metaprogramming" and "proof by reflection". Use
  mathematical and formalization keywords instead.

### Abstract (T 331-359)

Rewrite in the arXiv order:
1. what flag algebras do in extremal graph theory;
2. what is formalized (the theory, not just the checker);
3. verified results: the seven Turán-type upper bounds from Flagmatic
   certificates, the asymptotic Mantel theorem and the asymptotic Erdős
   pentagon density theorem with their lower-bound constructions, and
   Goodman's inequalities;
4. the ensemble semantics and root-plantability as the mathematical lesson.

Mention that every headline theorem depends only on Lean's three standard
axioms.

### Sec. 1 Introduction (T 396-594)

- Delete T 399-426: the four-colour/Kepler/hexagon opening and the SAT/SMT/
  translation-validation paragraph. Move at most one sentence about
  formalized computer-assisted proofs (four-colour, Kepler, empty hexagon)
  to Related Work.
- Open with a condensed version of the arXiv "Why flag algebras matter"
  (A 288-353): the Turán density definition, the Mantel example, and the
  list of flag-algebra successes. This list cites razborov2008triangles,
  balogh2016induced5, balogh2017rainbow, razborov2010tetrahedron and
  baber2012turan, which also clears the audit's uncited-entries item.
- Keep the TOPLAS paragraph "Flag algebras and their certificates"
  (T 451-499), which is already math-facing.
- Replace "A certificate-to-proof compiler" (T 501-529) with a neutral
  paragraph on the three layers. Base it on A 355-388.
- Keep "A formalization-driven semantics for forbidden subgraphs"
  (T 531-555). This is the AFM "insight" story; tighten it slightly.
- Contributions (T 557-579), reordered:
  1. formalization of the classical theory;
  2. formally verified theorems (asymptotic Mantel, asymptotic Erdős
     pentagon, seven certificate bounds, Goodman);
  3. ensemble semantics and root-plantability;
  4. lessons on representing quotient-heavy combinatorics.
  Give the SWHID and a pointer to the artifact appendix.
- Update the Organization paragraph accordingly.

### Sec. 2 Background (T 596-1239)

- Keep essentially as is. It is nearly identical to the arXiv text.
- Restore the arXiv worked example "Mantel's theorem via flag algebras"
  (A 1083-1117) at the end of 2.5.
- Adjust T 1230-1239, which currently forward-references the Mantel
  computation in Sec. 5.1. Sec. 5.1 will instead refer back to this example.
- Add one sentence after the Turán density definition (T 1062-1083): the
  limit exists because the normalized sequence is non-increasing and bounded
  below. Cross-reference `tendsto_generalizedTuranDensity` (audit 3.2).

### Sec. 3 Formalizing flag algebras (T 1241-1983)

- Keep the TOPLAS condensed text and listings.
- Add a short subsection or table titled "Where the formal statements differ
  from the informal ones". AFM explicitly asks for this. Items:
  - the ambient algebra vs the H-free algebra, and `forbidLE` (ensemble
    order) vs the built-in order;
  - the Turán density defined via `limUnder`, with a separate convergence
    theorem;
  - `FlagDensitySpace` / `PositiveHomSpace` packaging (the footnote at
    T 1685-1695 can move here);
  - the `n < m` density convention;
  - induced copies vs subgraph copies in `ex(n, F; H)`;
  - "paper-facing" renamed identifiers: list the real names, because AFM
    wants links to specific code.
- Optionally restore two math-facing explanations:
  - the proof idea of Theorem 2.x(b), sampling flags with weights
    phi([G]) at sizes n^2+k (A 1756-1787);
  - the probabilistic reading of the random-extension identity
    (A 1969-1975).

### Sec. 4 The reflection layer (T 1985-2474)

- Keep the structure. Soften the PL framing in the opening (T 1985-2017),
  borrowing A 2204-2210.
- Add one or two paragraphs on the BitMask layer (Section 5 below):
  - a graph on n vertices is encoded as one natural number;
  - canonicalization/completeness sweeps are checked by `decide +kernel`;
  - rooted sweeps and shared subset-pair passes supply the pair densities;
  - the whole certificate pipeline therefore runs without `native_decide`.
  Frame this as a representation lesson.
- Keep the generation-command table (T 2371-2409). It helps readers who want
  to reproduce results.

### Sec. 5 Verifying flag-algebra certificates (T 2476-2974)

- Rename the section. Keep 5.1 "How a certificate proves a bound"
  (T 2508-2671), but replace the duplicated Mantel calculation with a
  back-reference to the Sec. 2 example and keep only the SDP-block
  generalization.
- 5.2 (T 2673-2855):
  - keep the four parts and the `flag_certificate` usage example;
  - cut the CLI details (`gen-skeleton`, `--materialize`,
    `flag_certificate?` "Try this") down to one sentence plus a pointer to
    the artifact README.
- 5.3 Trust model (T 2857-2894): replace with a short "What Lean checks"
  paragraph.
  - Headline: every theorem depends only on `propext`, `Classical.choice`
    and `Quot.sound`, verified by `#print axioms`.
  - Keep one sentence on what is not formally checked (how the certificate's
    Q', R fields are reconstructed) and why this cannot affect validity.
- 5.4 Evaluation (T 2896-2974):
  - update the table text for the new evaluation route;
  - rewrite "Limitations": drop the native_decide point and the build-system
    dependency point (the latter moves to the artifact README); keep
    "coverage, not completeness".

### Sec. 6 Main formalized theorems (T 2976-3141)

- Promote this section: for AFM these are the headline results. Consider
  moving it before Sec. 5, or at least opening the paper's results summary
  with it.
- Mantel: restore the lower-bound details (even/odd n, witness
  `completeBipartiteGraph (Fin k) (Fin k)`) from A 3576-3601.
- Erdős pentagon:
  - restore the remark that C5 copies in a triangle-free graph are
    automatically induced (A 3636-3640);
  - phrase the limit step as "along an unbounded subsequence of sizes,
    followed by convergence of the normalized sequence" (audit 3.4);
  - cite Lidický–Pfender for the exact finite result, contrasting it with
    our asymptotic statement.
- Goodman:
  - state the inequalities as semantic inequalities, i.e. after evaluation
    by every positive homomorphism (audit 3.3);
  - fix the code reference. The paper names `Cauchy_Schwarz_inequality`
    (an alias at `FlagAlgebra/RandomHom.lean:1419` for
    `square_downward_mul_ge_mul_downward_square`), but
    `MantelTheorem/GoodmanBound.lean:69` uses
    `Cauchy_Schwarz_inequality_unit`. Describe what is actually used.

### Sec. 7 Lessons from the formalization (T 3143-3416)

- Rename from "Engineering Obstacles". Keep the four subsections.
- Restore from arXiv:
  - the paragraph "Which engineering obstacles are Lean-specific?"
    (A 4640-4658), for AFM criterion 8;
  - the Finite vs Fintype / noncomputable explanation (A 4004-4031), in
    condensed form.
- Optionally restore "Comparing Flags of Different Sizes" (A 3828-3880) as a
  short paragraph. TOPLAS folded it into the reordering subsection.
- Consider reviving, in condensed form, Lessons 1 and 5 of the commented-out
  arXiv appendix (A 4901-4919, 4983-4997) as closing lessons of this section.
  Lesson 6 is obsolete now that `native_decide` is gone.

### Sec. 8 Meta-theory of ensemble semantics (T 3418-3752)

- Keep the TOPLAS length. Add one sentence of the Stone–Weierstrass
  separation argument from A 4403-4413.
- Re-verify every sentence against the current Lean statements. The
  MetaTheory refactors of 2026-08-24/25 postdate the audit.
  - Constrained algebra: Lean defines it directly as a quotient
    (`MetaTheory/ConstrainedClass.lean`). Either say so or formalize the
    canonical isomorphism (audit 1.4).
  - Forbidden ideal: check whether `forbiddenIdeal_eq_span` still needs the
    closure hypothesis, or whether heredity now implies it.
  - Check the non-degeneracy hypotheses of `support_criterion` and
    `blowupClosed_root_plantable` against the stated theorems.
  - The blow-up sketch must handle multi-root types, not "the labeled
    vertex".
  - `downward_preserve_semanticCone` is ambient, not ensemble-specific;
    reword T 3706-3719.
  - Cite Kővári–Sós–Turán for the o(n^2) edge bound in the C4-free example.
- Align terminology with `papers/MetaTheory/paper.tex`, which uses
  clone-closed, substitution-closed, blow-up-closed and pinning. Cite that
  paper (arXiv ID once posted) in place of "a forthcoming paper".
- Keep the autoformalization paragraph (T 3737-3744) and the declaration map
  (T 3721-3735).

### Sec. 9 Open design questions (T 3754-3826)

- Fold into a shorter "Discussion" section, or into the conclusion.
- Keep "when should the constraint enter" and "separate representations"
  (with the Cohen et al. and Davey et al. comparison).
- Rewrite "Can the computational layer scale beyond five vertices?"
  completely. The native_decide fallback no longer exists, and a 6-vertex
  certificate now checks in the kernel. Even while `K3freeC6` stays out of
  the paper, do not claim that five vertices is a practical ceiling. State
  what the seven reported cases use and what dominates the cost.

### Sec. 10 Related work (T 3828-3960)

New order:
1. formalizations of combinatorics (T 3900-3916);
2. concurrent flag-algebra formalizations (T 3926-3950);
3. computer-assisted flag-algebra arguments (T 3918-3924), plus Lidický–
   Pfender;
4. graph limits (T 3952-3960);
5. one paragraph on proof-assistant verification of numerically found
   certificates: Harrison SOS, Morrison `sos`, the empty hexagon, and
   refinements (Cohen et al.) for the reflection pattern.

Remove the paragraphs "Certificate checking and proof reconstruction"
(T 3831-3866), "Proof by reflection and trusted evaluation" (T 3868-3886) and
"Proof engineering at scale" (T 3888-3898). Keep only the sentences needed for
item 5.

### Sec. 11 Conclusion (T 3962-4006)

- Remove "the two largest certificates still rely on `native_decide`"
  (T 3993-3995) and state the standard-axioms result instead.
- Keep the future work: the differential structure (Razborov Sec. 4.3),
  hypergraphs and digraphs, and the graphon bridge.

### Back matter

- AI disclosure (T 4008-4019): see Section 8, item A5.
- Acknowledgments: keep. The thanks to Ross Kang and Sidharth Hariharan for
  pushing to remove `native_decide` can now say that this was done.
- Appendix A, compile times: see Section 5.
- New Appendix B, Artifact: see Section 6.

## 5. Updates required by code changes since TOPLAS

Commits `2b90913`, `3ae201f` and `a3c30c2` (2026-09-03) added the BitMask
kernel pipeline and regenerated the remaining examples. As a result, every
`*_turanDensity` theorem depends only on the three standard axioms.

Current state of the seven reported files (`LeanFlagAlgebras/Flagmatic/`):

| File | `kernelDecide` | BitMask options | `native_decide` |
|---|---|---|---|
| Mantel, K3freeP3, K3freeC4, K4freeEdge, ErdosPentagon | yes | no | none |
| K5freeEdge | yes | yes | none |
| C5freeEdge | yes | yes | none |

To do:
- [ ] Run `#print axioms` on all seven `*_turanDensity` theorems plus
      `Mantel_Turan`, `ErdosPentagon_Turan`, the Goodman theorems and the
      MetaTheory headline theorems. Record the output for Appendix B.
- [ ] Re-measure Appendix A: all seven cases under the committed
      configuration, five runs each, same machine description.
  - Drop the `native_decide` columns, or keep them as a comparison for the
    five cases that previously had both.
  - Recount the "Lemmas" column: the mask pair-density route generates
    different declarations.
  - Report median and range, and state the exclusion rule in advance
    (audit 3.6).
- [ ] Rewrite every passage that mentions `native_decide`, trusting the
      native compiler, or kernel checking not scaling. Locations include
      the abstract, T 2885-2894, T 2963-2967, T 3799-3826, T 3993-3995 and
      the Appendix A text.
- [ ] Add the BitMask description to Sec. 4, as in Section 4 above.

## 6. AFM-specific additions

### 6.1 Statement-to-declaration table

The main results must link to specific code. The locations below are verified
against the current tree. Pin them to the release commit and use SWHID
context links in the final version.

| Informal statement | Lean declaration | File |
|---|---|---|
| Chain rule (Lemma 2.x) | `flagDensity_eq_sum_density_prods` | `FlagAlgebra/SubflagListDensity.lean:2999` |
| Product independent of auxiliary size | `flagMulWithSize_indep_on_size` | `FlagAlgebra/FlagAlgebra.lean:542` |
| Razborov convergence theorem (a) | `flagSeq_limit_mem_positiveHom` | `FlagAlgebra/FlagSequence.lean:656` |
| Razborov convergence theorem (b) | `positiveHom_as_flagSeq_limit` | `FlagAlgebra/FlagSequence.lean:1019` |
| Random-extension identity | `exists_probMeasure_extend_emptyType_positiveHom` | `FlagAlgebra/RandomHom.lean:1096` |
| Downward operator preserves non-negativity | `downward_preserve_semanticCone` | `FlagAlgebra/RandomHom.lean:1229` |
| Cauchy–Schwarz for the downward operator | `Cauchy_Schwarz_inequality` (alias) | `FlagAlgebra/RandomHom.lean:1419` |
| Turán density limit exists | `tendsto_generalizedTuranDensity` | `Turan/GeneralizedTuran.lean:253` |
| Ensemble inequality implies Turán bound | `generalizedTuranDensity_le_of_forbidLE` | `Forbid/TuranDensity.lean:250` |
| Density adequacy | `flagDensity₁_eq_sym2FlagDensity₁` (and ₂) | `FlagAlgebra/Compute/FlagDensity.lean:1140` |
| Downward-factor adequacy | `downwardNormalizingFactor_eq` | `FlagAlgebra/Compute/Downward.lean:170` |
| PSD from rational LDLᵀ | `posSemidef_real_of_LDLt` | `Automation/Matrix/PosSemiDef.lean:73` |
| Adding a downward quadratic form | `forbidLEWith_add_QuadraticForm` | `Automation/Basic.lean:128` |
| Density permutation invariance | `flagDensity_permute` | `FlagAlgebra/SubflagListDensity.lean:649` |
| Asymptotic Mantel | `Mantel_Turan` | `MantelTheorem/MantelTheorem.lean:191` |
| Asymptotic Erdős pentagon | `ErdosPentagon_Turan` | `ErdosPentagon/ErdosPentagon.lean:286` |
| Pentagon lower bound | `ErdosPentagon_Turan_lowerBound` | `ErdosPentagon/ErdosPentagon.lean:264` |
| Goodman triangle bound | `Goodman_bound_on_triangle_density` | `MantelTheorem/GoodmanBound.lean:15` |
| Goodman Ramsey multiplicity | `Goodman_theorem_on_Ramsey_multiplicity` | `MantelTheorem/GoodmanRamsey.lean:16` |
| Seven certificate bounds | `<Case>_turanDensity` | `Flagmatic/<Case>.lean` |
| Quotient implies ensemble | `quotient_implies_ensemble` | `MetaTheory/SupportClosure.lean:130` |
| Support-closure criterion | `support_criterion` | `MetaTheory/SupportClosure.lean:139` |
| Blow-up closure implies root-plantability | `blowupClosed_root_plantable` | `MetaTheory/BlowupClosed.lean:530` |
| Empty type is root-plantable | `heredClass_emptyType_rootPlantable` | `MetaTheory/EmptyTypeCollapse.lean:180` |
| C4-free counterexample | `c4free_not_rootPlantable` | `MetaTheory/C4Free.lean:455` |

(Paths are relative to `LeanFlagAlgebras/`.)

Put this table in Appendix B. Also add inline references at each theorem
environment in the text, e.g. a footnote or a margin tag with the
declaration name.

### 6.2 Artifact appendix (Appendix B)

- Release repository `taeyool/lean-flag-algebras-release`:
  - sync it with the BitMask commits;
  - keep the axiom-free `CompleteGraphFreeP4.lean` noted in audit 2.2;
  - create a tag and cite the commit SHA and SWHID.
- Lean and Mathlib versions, and build commands:
  - per-case `lake build LeanFlagAlgebras.Flagmatic.<Case>`;
  - the Mantel and Erdős modules;
  - `LeanFlagAlgebras.MetaTheory`;
  - a full clean build, with expected time and memory.
- Certificate files: path and SHA-256 for each of the seven.
- Instruct users to run `lake clean` after editing a certificate (the
  build-tracking caveat moved out of the main text).
- Separate what this paper claims from additional results in the repository
  (audit 7.2).

### 6.3 Size and complexity table

- Lines of code and the number of `def`/`theorem`/`lemma` declarations per
  component: Flags/FlagAlgebra (specification), Compute and BitMask
  (reflection), Automation and Flagmatic (certificates), Forbid/Turan,
  MantelTheorem/ErdosPentagon, and MetaTheory.
- Also give the number of generated declarations for the pentagon case.
- Compute these with a small script; do not estimate.

## 7. Material to restore from the arXiv version (summary)

| arXiv lines | Content | Destination |
|---|---|---|
| A 288-353 | Why flag algebras matter; Turán density; successes | Sec. 1 |
| A 1083-1117 | Mantel via flag algebras (worked example) | end of Sec. 2 |
| A 1756-1787 | Proof idea of convergence theorem (b) | Sec. 3 (optional) |
| A 1969-1975 | Probabilistic reading of the random extension | Sec. 3 (optional) |
| A 2204-2210 | Why flag algebras suit reflection | Sec. 4 opening |
| A 3576-3601 | Mantel lower bound details | Sec. 6 |
| A 3636-3640 | Induced vs non-induced C5 remark | Sec. 6 |
| A 3828-3880 | Comparing flags of different sizes | Sec. 7 (optional, condensed) |
| A 4004-4031 | Finite vs Fintype, noncomputable instances | Sec. 7 (condensed) |
| A 4403-4413 | Stone–Weierstrass separation step | Sec. 8 |
| A 4640-4658 | Which obstacles are Lean-specific? | Sec. 7 |
| A 4901-4919, 4983-4997 | Lessons 1 and 5 | end of Sec. 7 (condensed) |

## 8. Open items carried over from the TOPLAS audit

- [x] A1. Asymptotic naming and novelty phrasing (audit 1.1, 1.2, 4.1;
      Section 3.2 above). Done in phases 2-3; re-check in the final pass.
- [x] A2. Trust wording matches what is actually checked (audit 1.3).
      Done in the Sec. 5 rewrite.
- [x] A3. Meta-theory text vs Lean statements (audit 1.4; Sec. 8 above).
      Done in phase 3 from a fresh audit of the current Lean code.
- [x] A4. Add Lidický–Pfender and Kővári–Sós–Turán with verified metadata
      (audit 5.1). Lidický–Pfender's DOI was checked on arXiv; the KST entry
      has no DOI.
- [ ] A5. AI disclosure. Keep the TOPLAS paragraph and add two or three
      sentences on:
  - which tools were used for which task (tool names, and versions where
    known);
  - how the authors reviewed statements, proofs, citations and the
    correspondence between the paper and the Lean code;
  - that Lean type-checking does not by itself certify that statements are
    faithful to the informal ones.
  AFM's scope excludes AI-derived insight only in the absence of formal
  artifacts, which does not apply here (audit 1.5).
- [ ] A6. Artifact immutability and reproducibility (audit 1.6; Sec. 6.2).
- [ ] A7. Spiegel citation: verify the talk title against the slides, and
      soften the description if it cannot be confirmed (audit 4.3).
- [x] A8. State that the certificate pipeline supports a single forbidden
      graph H, while the background allows finite families (audit 3.1).
      Done in the "Scope" paragraph of Sec. 5.4.

## 9. Bibliography

- Start from a copy of `papers/TOPLAS/refs.bib`.
- Candidates for removal after the Related Work condensation, if no longer
  cited: pnueli1998translation, lammich2020unsat, tan2023cakelpr,
  bohme2010z3, armand2011modular, besson2006fast, mcconnell2011certifying,
  alkassar2014framework, roux2018validating, gregoire2002compiled,
  boespflug2011full, boutin1997reflection, ringer2019qed, ahman2026everest,
  sozeau2020metacoq. Keep gonthier2008fourcolour, hales2017kepler and
  heule2024hexagon only if the Related Work sentence uses them.
- Now cited again via the restored intro: razborov2008triangles,
  balogh2017rainbow, razborov2010tetrahedron, baber2012turan.
- Add: Lidický–Pfender; Kővári–Sós–Turán; the MetaTheory companion paper.
- Software references (Flagmatic, Lean `sos`, Freer's graphon library): add
  a tag or commit and an access date.
- Use a plain numeric style with DOIs/URLs (e.g. `plainurl`).
- Check with `bibtex` that there are no uncited or undefined entries.

## 10. Deferred

- **`K3freeC6` (6-vertex host, bound 92129/5242880).** Not included for now.
  Revisit after the rewrite; including it would mainly strengthen the scaling
  discussion. Until then, avoid wording that it would contradict.
- Whether the MetaTheory companion also goes to AFM. This affects how much of
  Sec. 8 to keep, but the current plan keeps the summary either way.

## 11. Work phases

1. [x] **Skeleton.** Create `paper_afm.tex` from the TOPLAS tex. Swap the
   preamble, copy `refs.bib`, and check that it builds with `latexmk -pdf`.
   Done 2026-09-29:
   - `article` + `authblk` preamble with colored links (no link boxes);
   - title set, ORCID line added, email fixed to `sangil@`;
   - CCS removed; math-facing keywords added;
   - `\boldparagraph` -> `\paragraph`; `\Description` and `acks` removed;
   - bibliography style `plainurl`; `latexmkrc` copied.
   Build result: 48 pages, no undefined references or citations, no BibTeX
   warnings. Two overfull boxes (long Lean identifiers, around the
   convergence-theorem paragraph and the `sym2LabeledGraphDensity` paragraph)
   are left for phase 7, since both paragraphs will be edited. Body text is
   still the TOPLAS text verbatim.
2. [x] **Framing.** Title, abstract, introduction, contributions,
   organization. Done 2026-09-29:
   - abstract rewritten in the arXiv order (method, formalization, verified
     theorems, ensemble semantics); the standard-axioms sentence carries a
     phase-4 TODO;
   - introduction now opens with Mantel and the flag-algebra successes; the
     four-colour/Kepler/SAT/SMT/translation-validation paragraphs are gone;
   - "compiler" framing replaced by the three-part description;
   - contributions reordered to the four AFM-facing items;
   - `refs.bib` gained razborov2008triangles, razborov2010tetrahedron,
     baber2012turan, balogh2017rainbow and mathlib2020;
   - `xurl` added for URL line breaks.
   The Organization paragraph still lists `sec:unsure`; update it if
   Sec. 9 is folded away or Sec. 6 moves in phase 3.
3. [x] **Body.** Sections 2 to 11 per Section 4, with the restored material
   from Section 7. Done 2026-09-29 (48 pages, no warnings).
   - Sec. 2: Mantel worked example `ex:mantel-fa` moved here (from TOPLAS
     5.1); sentence on existence of the Turán-density limit; Lidický–Pfender
     note in `ex:pentagon`.
   - Sec. 3: proof idea of convergence theorem (b) restored; the sentence
     claiming the certificate proofs go through
     `downward_preserve_semanticCone` corrected to
     `downward_forbidLEWith_nonneg`; new subsection `sec:informal-formal`.
   - Sec. 4: subsection 4.3 renamed; new subsection `sec:reflection-bitmask`
     on the BitMask encoding.
   - Sec. 5: rewritten as "Verifying Flag-Algebra Certificates"; the Mantel
     calculation is replaced by a back-reference; "What Lean Checks" replaces
     the trust model; "Scope" paragraph (single forbidden graph).
   - Sec. 6: "The Main Density Theorems".
     - Mantel is stated with Mathlib's `extremalNumber`/`turanDensity`.
     - Goodman: fixed to the unit Cauchy–Schwarz form actually used, and
       the inequalities are stated in the ambient semantic order.
   - Sec. 7: renamed "Lessons from the Formalization"; restored the canonical
     representative trade-off and the noncomputable `Fintype` remark; new
     subsection `sec:lean-specific` (including the kernel-evaluation lessons
     from the BitMask work).
   - Sec. 8: rewritten per the MetaTheory audit.
     - Constrained algebra defined as a quotient by the generated ideal.
     - No non-degeneracy hypothesis; the blow-up theorem is stated at every
       nonempty type.
     - Stone–Weierstrass step added.
     - Kővári–Sós–Turán cited for the (2e)^2 <= 2n^3 bound proved in Lean.
     - Multi-root blow-up sketch.
     - Downward-lemma sentence fixed.
     - Terminology is now "standard"/"quotient order" instead of
       "built-in".
     - The companion paper is cited as `metatheory2026`.
   - Sec. 9 is now "Discussion", with the scaling paragraph rewritten.
     There is no five-vertex ceiling claim, and K3freeC6 is not mentioned.
   - Sec. 10: reordered, and the three PL paragraphs are condensed into
     "Formal verification of computer-found evidence".
     - New disclosure: Mathlib's Turán theorem already gives finite Mantel
       and the K4/K5-free edge bounds.
     - Sec. 5.4 says the same.
   - Sec. 11 and the acknowledgments are updated. The AI paragraph is
     reworded only (the A5 expansion is still open).
   - Preamble: `\theoremstyle{definition}` for definition, example and remark.
   - Not restored (optional items): the probabilistic reading of the random
     extension (A 1969-1975) and "Comparing Flags of Different Sizes".
   - Findings to carry into later phases:
     - MetaTheory headline theorems print only the three standard axioms
       (checked on existing oleans, which are newer than the sources). None
       of them imports `CompleteGraphFreeP4.lean`.
     - The seven Flagmatic files have not yet been checked with
       `#print axioms`; the evidence so far is the a3c30c2 commit message.
     - Stale code comments to fix before the artifact release (criterion 9):
       - `GeneratorOptions.lean:15-16` (says to keep kernelDecide off for
         the pentagon);
       - the `maskPairDensity` doc at `:40` omits (3,4);
       - the `maskCompleteness` doc at `:27` says triangle-only;
       - `Flagmatic/C5freeEdge.lean:36-37` says "triangle forbids" but the
         file uses the subgraph route.
     - Pair-density counts are route-independent (15, 15, 210, 390, 2832,
       10332, 8172). K5 and C5 additionally have 287 and 227 `pairKeys_*`
       theorems.
4. [ ] **Code-state updates.** Section 5: axioms audit, re-measurement,
   BitMask paragraph.
5. [ ] **AFM additions.** Section 6: correspondence table, artifact
   appendix, size table.
6. [ ] **Audit items and bibliography.** Sections 8 and 9.
7. [ ] **Final pass.**
   - Terminology grep (Section 3.1).
   - No em-dashes.
   - No undefined references or citations, and no overfull boxes.
   - Consistency with `papers/MetaTheory/paper.tex`.
   - Every declaration name in the text exists at the release commit.
   - Page breaking. `article` uses `\raggedbottom`, and a break before a
     `\paragraph` heading gets the `\@secpenalty` bonus, so pages can end
     early with large gaps. Seen first on page 3 before "Organization". Try
     `\@secpenalty=0` (or `\flushbottom`) and re-check the `\Needspace` calls
     inherited from the acmsmall layout.
8. [ ] **Submission.**
   - Release tag and SWHID.
   - arXiv v2 of 2607.23500.
   - Episciences submission (PDF not inside a zip).
