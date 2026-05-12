# Writer Task

Project: Formalizing Flag Algebras in Lean 4 via Computational Reflection
Target Section: Conclusion

Depth Target:
- 2-3 substantial paragraphs with summary, limitations, and concrete next steps.

Section Blueprint (Hard Constraints):
- (no section blueprint configured)

Equation Source PDFs (for mathematical formulas):
- papers/References/Razborov07.pdf
- papers/References/GrzesikThesis14.pdf

Exemplar Formalization Papers (quality bar):
- (no exemplar files found)

Quality Requirements:
- Use papers/paper_claude.tex as the quality benchmark — match or exceed its depth and precision.
- Improve the reference draft rather than rewrite: identify gaps, strengthen weak arguments, add missing technical detail.
- Use explicit motivation → method → formalization detail → implication flow.
- Explain design choices and trade-offs, not only what was implemented.
- Keep claims tightly grounded in Lean evidence and avoid generic hype language.
- Ensure each section can stand alone for a PL researcher unfamiliar with the codebase.

Mandatory Considerations:
# Paper Writing Considerations

## PRIORITY 0: Reference Draft

**The file `papers/paper_claude.tex` is the high-quality reference draft for this paper.**
All agents must:
1. **Read the reference draft section first** (it is provided in the prompt as "Reference Section Draft").
2. **Improve and refine it** — do not discard it and write from scratch.
3. **Preserve all accurate technical content** already present in the reference draft.
4. **Identify gaps and strengthen weak arguments** rather than adding entirely new content.

The reference draft already has a good structure and solid mathematical content. The agent's job is to improve depth, fix imprecision, add missing details, and ensure all Section Blueprint constraints are satisfied.

## PRIORITY 1: English-Only Output

All section bodies must be written in English. The considerations and author notes may contain Korean text for historical reasons, but all agent outputs (planner JSON, writer LaTeX, verifier LaTeX) must be in English.

## PRIORITY 2: POPL Fitness

The paper targets POPL 2027. Key POPL-specific requirements:
- Separate the mathematical content (what was formalized) from the engineering choices (how it was implemented in Lean 4) in every section.
- PL researchers care about the type-theoretic encoding choices. Explain WHY quotient types, WHY reflection, WHY custom tactics — not just THAT they were used.
- Proof assistant papers at POPL are evaluated on: correctness of claims, depth of formalization novelty, generalizability of techniques, and trustworthiness of the proof pipeline.

---

이 파일은 에이전트가 논문 문장을 생성할 때 반드시 참고하는 제약과 체크리스트입니다.
항목을 자유롭게 추가/수정하면 다음 실행부터 자동 반영됩니다.

## 0) Journal Fit Profile (Paraphrased, Agent-Ready)
아래는 저널 aims/scope의 핵심을 요약한 실행 규칙이다. 원문 복붙 대신 이 요약을 우선 사용한다.

### 0.1 핵심 방향
- 수학 독자를 대상으로 쓰되, Introduction은 비전공자도 따라올 수 있게 접근 가능해야 한다.
- 논문 주장은 반드시 형식화 산출물(Lean 코드/증명 아티팩트)과 함께 제시되어야 한다.
- 본문에 긴 코드 블록을 과도하게 넣지 말고, 코드 저장소를 주 근거로 참조한다.
- 논문 평가는 "수학적 관련성 + 형식화의 품질 + 재현 가능성" 중심으로 맞춘다.

### 0.2 평가 축(섹션별로 반영)
- Formalization novelty: 기존 형식화 대비 무엇이 새로운가?
- Mathematical significance: 다루는 결과의 수학적 의미가 무엇인가?
- Insight: 형식화 과정에서 얻은 새로운 통찰이 있는가?
- Generality: 결과와 기법이 어디까지 일반화되는가?
- Integration: 기존 라이브러리와 어떻게 연결/통합되는가?
- Reproducibility: 타 생태계/타 프로젝트에 이전 가능한 교훈이 있는가?
- Engineering quality: 코드 가독성/문서화/유지보수성은 충분한가?

### 0.3 Agent Execution Rules (Hard Constraints)
- MUST: 모든 핵심 주장에 Lean 아티팩트 근거를 붙인다.
- MUST: "AI가 제안"한 내용이라도 증명 아티팩트가 없으면 기여로 주장하지 않는다.
- MUST: 코드 블록은 설명에 꼭 필요한 최소량만 사용한다.
- SHOULD: 각 섹션 말미에 novelty/insight/reproducibility 관점 요약 2~4문장을 둔다.
- SHOULD: proof assistant 선택(Lean 4)이 결과에 준 영향을 명시한다.

### 0.4 운영 팁
- 저널 원문은 별도 메모(예: author_notes.md)에 링크와 함께 보관하고, 이 파일에는 요약 규칙만 둔다.
- 저널 정책이 갱신되면 0.1~0.3만 업데이트하고 나머지 체크리스트는 유지한다.

## 1) Claim-Evidence Alignment
- 각 핵심 주장마다 Lean 코드 근거(정의/정리/파일 경로)를 붙인다.
- 코드에서 확인되지 않은 내용은 추측으로 쓰지 않는다.
- 정리 이름, 모듈 이름은 저장소의 실제 이름과 정확히 일치시킨다.

## 2) Mathematical Precision
- 기호, 정의역, 크기 조건(예: v(G)-k 관련 조건)을 누락하지 않는다.
- "isomorphic", "embedding", "induced subgraph" 같은 용어는 일관되게 사용한다.
- 비형식 설명과 형식 정의가 어긋나지 않도록 문단 끝에 교차 확인 메모를 둔다.

## 3) Formalization-Specific Narrative
- "수학 결과"와 "Lean 구현상의 설계 선택"을 분리해서 설명한다.
- 계산 가능 정의(computable definitions) 채택 이유를 분명히 밝힌다.
- 자동화 한계와 우회 전략(전술, 보조정리, 계산 스크립트)을 숨기지 않는다.

## 4) Reproducibility
- 실험/계산 파이프라인은 입력 파일, 스크립트, 산출물 위치를 함께 기술한다.
- 가능하면 섹션별로 "재현 절차"를 3~5 단계로 정리한다.
- 대규모 계산 의존 구간은 신뢰 경계(trust boundary)를 명시한다.

## 5) Scope and Honesty
- 이번 작업에서 "증명 완료"된 범위와 "향후 과제"를 명확히 분리한다.
- 기존 문헌 대비 기여를 과장하지 않는다.
- 성능/자동화 수준은 정량 근거가 있을 때만 주장한다.

## 6) Writing Style
- 한 문단에 하나의 메시지 원칙을 지킨다.
- 섹션 시작 문단에 "이 섹션의 목적"을 먼저 명시한다.
- 너무 긴 문장은 둘로 분해하고, 불필요한 수식 반복은 줄인다.

## 7) Final Consistency Checks
- Abstract, Introduction, Conclusion의 기여 항목이 서로 일치하는지 확인한다.
- 본문의 용어 표기(Flag, type, forbidden graph)가 전역 일관적인지 점검한다.
- 참고문헌/인용 텍스트의 철자 및 연도 오기를 점검한다.


Author Notes:
# Author Notes for the Agents

This file contains project-specific notes that agents should follow when writing or improving sections.
Hard constraints belong in `considerations.md`; this file is for tone, emphasis, and venue-specific guidance.

---

## Target Venue and Tone

- **Target venue**: POPL 2027 (Principles of Programming Languages)
- **Audience**: PL researchers with some background in type theory, proof assistants, and functional programming. Mathematical background in graph theory and combinatorics should not be assumed; motivate it.
- **Tone**: Precise, technical, argument-driven. Avoid marketing language ("seamlessly", "powerful", "elegant"). Prefer concrete claims with code/theorem evidence.
- **Length guidance**: Conference paper, roughly 25–30 pages in ACM two-column format.

---

## The Reference Draft

**`papers/paper_claude.tex` is the high-quality reference draft for this paper.**
Agents must treat it as the primary starting point and *improve* it — not replace it.
Key properties of the reference draft that must be preserved:

1. **Two-layer architecture framing** (abstract + reflection layers): this is the paper's organizing principle. Do not flatten it.
2. **Three categories of proof obligation** (abstract structure / data-heavy computation / algebraic bookkeeping): the introduction uses these to motivate the two layers. Keep this framing sharp.
3. **Section structure**: Introduction → Background: Flag Algebras → Abstract Formalization → The Reflection Layer → The Tactic Layer → Results → Related Work → Conclusion. These exact section names must be used in the output draft.
4. **Key claimed contributions** (all four must appear in abstract, introduction, and conclusion):
   - Abstract formalization of flag algebra in Lean 4 (flags as quotient types, flag algebra as quotient module, positive homomorphisms, forbidden-subgraph framework)
   - Reflection architecture: `Sym2Graph` + adequacy theorems + `native_decide`/`decide+kernel` for density and SDP certificate verification
   - Tactic automation: `ac_sort_pipeline` for linear normalization, `prove_flag_expand_with_forbidden_flag` and `prove_flag_mul_with_forbidden_flag` for expansion/multiplication identities
   - Verified results: Mantel's theorem and Erdős pentagon theorem ($\pi(K_3; C_5) = 24/625$, both bounds)

---

## Terminology Decisions

Use these consistently throughout the paper:

| Concept | Preferred term |
|---|---|
| Flagmatic-style certificates | "SDP certificates" |
| The concrete graph type | `Sym2Graph` |
| Lean's kernel evaluator tactic | `decide +kernel` |
| Lean's native-code evaluator tactic | `native_decide` |
| The abstract/semantic ordering | "semantic cone" |
| The bridge theorem to Turán density | `generalizedTuranDensity_le_of_forbidLE` |
| The LDL^T decomposition check | "LDL^⊤ decomposition" |
| The flag naming scheme | "canonical naming convention" |

---

## Must-Highlight Contributions

These are the key technical novelties that reviewers will evaluate. Each must get explicit treatment:

1. **Forbidden-subgraph framework generality**: In Razborov's original formulation, forbidding a subgraph requires axiomatizing a new theory per problem. Our `forbidLE` predicate works inside a single theory and is applied at proof time rather than theory construction time. This is a genuine formalization insight.

2. **Trust hierarchy**: The deliberate use of `native_decide` (faster, trusts native compiler) for density tables vs. `decide +kernel` (slower, only trusts kernel) for SDP matrix equalities is an important architectural decision. Explain the trade-off explicitly.

3. **Performance of `ac_sort_pipeline`**: The comment in `ErdosPentagon.Lemmas` — "sort_at -- takes more than 10 minutes" — is concrete evidence that the custom tactic is not cosmetic. Cite it.

4. **Elaboration-time theorem generation**: The `load_flag_pair_density_theorems` macro generates and immediately proves hundreds of density theorems at compile time. This is unusual in the Lean ecosystem and should be explained carefully.

5. **Lower bound via blow-up**: The lower bound of the Erdős pentagon theorem is proved via an explicit blow-up construction with a formal `Filter.Tendsto` limit argument. This is mathematically non-trivial and should not be summarized in one sentence.

---

## Claims to Avoid Unless Quantified

- Do not say "our formalization is complete" without specifying what is and is not formalized.
- Do not claim a specific line count or proof size unless you have verified it from the repository.
- Do not say the framework "handles all flag algebra arguments" — say it "provides reusable infrastructure for the three categories of proof obligation that arise in all known flag algebra arguments."
- Do not claim `native_decide` is "safe" — clarify its trust boundary (relies on native compiler, not just kernel).

---

## Open Technical Caveats to Acknowledge

- `native_decide` for density tables introduces a dependency on the Lean-to-native compiler (outside the kernel). The paper should acknowledge this is a trust assumption.
- The SDP certificates are found externally by a numerical solver and then formally verified. The numerical solver itself is not verified.
- The framework currently handles graphs only; extension to hypergraphs or directed graphs would require generalizing the type-parameter conventions.

---

## Section-Specific Emphasis

### Introduction
- Open with the extremal combinatorics motivation before introducing the proof assistant.
- The three-category decomposition of proof obligations is the key insight that motivates the architecture. Spend at least one paragraph on it.

### Background: Flag Algebras
- For a POPL audience, motivate WHY flag algebras matter before defining them.
- Give the flag product formula explicitly (not just "there is a product").
- End with the Erdős pentagon problem as the running example.

### Abstract Formalization
- The `forbidLE` predicate and `generalizedTuranDensity_le_of_forbidLE` theorem are the most novel part of this section. Give them a full subsection.
- Explain why quotient types in Lean 4 are the right representation for flags (not just an implementation choice — they encode the mathematical semantics faithfully).

### The Reflection Layer
- Lead with the general proof-by-reflection pattern before the specifics.
- Be explicit about what "adequacy" means: the computable function gives the same value as the abstract definition on all inputs.
- The LDL^⊤ approach for SDP verification is non-standard — explain why it works (no floating point, exact rational arithmetic).

### The Tactic Layer
- The naming convention is the load-bearing design decision for the whole tactic layer. Explain it before the specific tactics.
- Include the concrete example of `prove_flag_expand_with_forbidden_flag 3` replacing 15–20 tactic steps.

### Results
- State the two main theorems prominently at the start.
- The "no sorry" claim needs the full trust chain: what axioms does `ErdosPentagon_Turan` actually depend on?

### Conclusion
- The generalizability claim should be precise: "the ~100 known flag algebra results in extremal combinatorics all involve the same three categories of proof obligation."
- Identify concrete future work (replace `native_decide` with `decide+kernel`; extend to hypergraphs; automate SDP certificate discovery from within Lean).


Global Instructions:
- papers/paper_claude.tex is the high-quality reference draft. Use its content as your primary starting point and IMPROVE it rather than write from scratch.
- The section structure in papers/paper_claude.tex is the correct target. Section names are: Introduction, Background: Flag Algebras, Abstract Formalization, The Reflection Layer, The Tactic Layer, Results, Related Work, Conclusion.
- The target venue is POPL 2027. Write with PL-community sensibilities: precision, explicitness about proof assistants and formal systems, clear separation of mathematical content from engineering choices.
- When the reference draft section is provided, treat it as a first draft to improve — identify gaps, strengthen weak arguments, add missing technical detail, and fix any imprecision.

Section-Specific Instructions:
- (none)

=== REVISION MODE: Feedback to Address ===
Each point below MUST be addressed. Do not silently skip any.
Produce a concrete fix for each point, not just an acknowledgement.

## Global Feedback
1. The title "Formalizing Flag Algebras in Lean 4 via Computational Reflection" is misleading: computational reflection is used only for verifying SDP certificates and density tables, not for formalizing flag algebra theory itself. Consider removing "via Computational Reflection" from the title, or replacing it with a phrase that more accurately reflects the overall scope of the work.
=== END FEEDBACK ===

Read planner_output.json and retriever_output.json first.

Selected evidence:
1. [text] line @ papers/paper_claude.tex:12 :: %   Theory of computation~Proof theory        [500]
2. [text] line @ papers/paper_claude.tex:16 :: % Keywords: flag algebras, Lean 4, proof by reflection, semidefinite
3. [text] line @ papers/paper_claude.tex:17 :: %   programming, Turan density, interactive theorem proving,
4. [text] line @ papers/paper_claude.tex:18 :: %   tactic metaprogramming, extremal combinatorics
5. [text] line @ papers/paper_claude.tex:37 :: % ---- Theorem environments -----------------------------------------------
6. [text] line @ papers/paper_claude.tex:38 :: \newtheorem{theorem}{Theorem}[section]
7. [text] line @ papers/paper_claude.tex:39 :: \newtheorem{lemma}[theorem]{Lemma}
8. [text] line @ papers/paper_claude.tex:40 :: \newtheorem{definition}[theorem]{Definition}
9. [text] line @ papers/paper_claude.tex:41 :: \newtheorem{example}[theorem]{Example}
10. [text] line @ papers/paper_claude.tex:42 :: \newtheorem{remark}[theorem]{Remark}
11. [text] line @ papers/paper_claude.tex:49 :: \newcommand{\Flag}[1]{\mathcal{F}^{#1}}
12. [text] line @ papers/paper_claude.tex:50 :: \newcommand{\FlagAlg}[1]{\mathcal{A}^{#1}}
13. [text] line @ papers/paper_claude.tex:53 :: \newcommand{\tdensity}[2]{\pi(#1;\,#2)}
14. [text] line @ papers/paper_claude.tex:54 :: \newcommand{\lean}[1]{\texttt{#1}}
15. [text] line @ papers/paper_claude.tex:56 :: % Lean code style
16. [text] line @ papers/paper_claude.tex:57 :: \lstdefinelanguage{Lean4}{
17. [text] line @ papers/paper_claude.tex:58 :: keywords={def,theorem,lemma,instance,structure,class,import,open,namespace,
18. [text] line @ papers/paper_claude.tex:60 :: return,do,for,in,noncomputable,abbrev,variable,section,
19. [text] line @ papers/paper_claude.tex:61 :: native_decide,decide,norm_num,simp,ring,linarith,omega,
20. [text] line @ papers/paper_claude.tex:67 :: stringstyle=\color{orange!80!black},
21. [text] line @ papers/paper_claude.tex:68 :: morestring=[b]",
22. [text] line @ papers/paper_claude.tex:86 :: \lstset{language=Lean4, frame=single, framesep=4pt,
23. [text] line @ papers/paper_claude.tex:90 :: \title{Formalizing Flag Algebras in Lean~4 via Computational Reflection}
24. [text] line @ papers/paper_claude.tex:106 :: \begin{abstract}


Reference Section Draft (your primary starting point):
---BEGIN REFERENCE DRAFT---
\label{sec:conclusion}

We have presented a Lean~4 formalization of Razborov's flag algebra method for
simple graphs.  The main point of the development is the quotient-level
formalization of the mathematical theory: flags modulo isomorphism, the
quotient algebra of density-expansion relations, positive homomorphisms and the
semantic cone, and a proof-time framework for reasoning under a forbidden
subgraph.  Reflection is used as a checked implementation boundary for the
finite computations demanded by concrete proofs.  The concrete graph
representation and density procedures are connected to the abstract
definitions by adequacy theorems; SDP certificates are verified over
$\mathbb{Q}$ by exact LDL$^\top$ decompositions.  The tactic layer is separate
again: it automates normalization, expansion, and multiplication steps but does
not change the mathematical specification or the certificate trust story.

The case studies prove the flag-algebra form of Mantel's theorem and the
Erd\H{o}s pentagon theorem ($\tdensity{C_5}{K_3} = 24/625$), with additional
Goodman-style inequalities in the active library.  We expect the architecture
to transfer to further graph flag algebra arguments because the same concerns
recur: quotient-level semantics, exact finite counting, externally generated
but internally checked certificates, and large-scale algebraic bookkeeping.

\paragraph{Lessons for proof engineering.}
Five design choices proved unexpectedly decisive.  First, reflection had to be
treated as a verified optimization problem, not merely as a way to run the
definition.  The naive executable version of flag density still exposed
Lean's evaluator to quotient equality, proof-valued fields, generic finite
enumeration, and repeated graph-isomorphism search.  The usable version
separates specification from implementation: abstract flag densities remain the
specification, while \lean{Sym2Graph}, the fast Boolean isomorphism checkers,
and the concrete induced-subgraph counters are optimized implementations
connected back to the specification by adequacy theorems.  Second, numerical
equalities had to be proved extensionally: when two densities are equal because
they count the same choices, the Lean proof names the two finite sets,
constructs an equivalence between them, and derives equality through
\lean{Fintype.card\_congr}.  This made counting lemmas robust in the presence
of quotient representatives and overlapping finite-type instances.  Third, the
\emph{trust hierarchy} (using \lean{decide +kernel} for SDP certificates and
\lean{native\_decide} for density tables) emerged not from abstract principle
but from practical necessity: \lean{native\_decide} over rational matrix
products exceeds the kernel's stack depth, while \lean{decide +kernel} over
the same matrix terminates in finite (if slow) time.  The hierarchy is thus a
response to concrete computational constraints, not a prior design commitment.
Fourth, \emph{encoding structure in names} rather than type-class attributes
was motivated by a performance observation: attribute lookup during elaboration
triggers unification, which compounds with the size of flag algebra expressions
to cause timeouts; name inspection does not.  Fifth, the \emph{general
forbidden-subgraph rule} (\lean{forbidLE}) was harder to build than anticipated
because it required a measure-theoretic construction (the random extension
measure $\mathbb{P}^{\phi_0}$) that is implicit in the mathematical literature
but must be made entirely explicit for a formal proof.

\paragraph{Future work.}
Replacing \lean{native\_decide} with \lean{decide +kernel} throughout (or
with a formally verified external checker) would eliminate the remaining
dependency on the native compiler.  Extending the framework beyond graphs---to
hypergraphs, directed graphs, or other combinatorial structures---would require
more than changing type parameters: the concrete reflection layer, density
generation scripts, and tactic naming conventions are all graph-specific.
Nevertheless, the same conceptual split between abstract semantics,
reflective computation, and tactic automation appears promising for those
settings.  Automating the discovery of SDP certificates from within Lean
(rather than importing them from external solvers) remains a longer-term goal.
A full formalization of graphon theory, connecting flag algebra limits to the
Lov\'asz theory~\cite{lovasz2012large}, would provide a richer mathematical
foundation for future extensions.

% =========================================================================
\bibliographystyle{ACM-Reference-Format}
\begin{thebibliography}{99}

\bibitem{razborov2007flag}
A.~A.~Razborov.
\newblock Flag algebras.
\newblock \textit{Journal of Symbolic Logic}, 72(4):1239--1282, 2007.

\bibitem{razborov2008}
A.~A.~Razborov.
\newblock On the minimal density of triangles in graphs.
\newblock \textit{Combinatorics, Probability and Computing},
  17(4):603--618, 2008.

\bibitem{razborov2013flag}
A.~A.~Razborov.
\newblock Flag algebras: An interim report.
\newblock In \textit{The Mathematics of Paul Erd\H{o}s II}, pages 207--232.
  Springer, 2013.

\bibitem{grzesik2012}
A.~Grzesik.
\newblock On the maximum number of five-cycles in a triangle-free graph.
\newblock \textit{Journal of Combinatorial Theory, Series B},
  102(5):1061--1066, 2012.

\bibitem{hatami2012}
H.~Hatami, J.~Hladk\'{y}, D.~Kr\'{a}l, S.~Norine, and A.~Razborov.
\newblock On the number of pentagons in triangle-free graphs.
\newblock \textit{Journal of Combinatorial Theory, Series A},
  120(3):722--732, 2013.

\bibitem{dillies2022szemeredi}
Y.~Dillies and B.~Mehta.
\newblock Formalising Szemer\'{e}di's regularity lemma in Lean.
\newblock In \textit{Proc.\ ITP 2022}, LIPIcs~237, 2022.

\bibitem{mehta2022kruskal}
B.~Mehta.
\newblock Formalising the Kruskal-Katona theorem in Lean.
\newblock In \textit{Proc.\ ITP 2022}, 2022.

\bibitem{subercaseaux2024hexagon}
B.~Subercaseaux, M.~J.~H.~Heule, J.~Mackey, J.~Meadows, R.~Tao, and
  C.~Wu.
\newblock Formal verification of the empty hexagon number.
\newblock In \textit{Proc.\ ITP 2024}, LIPIcs~309, 2024.

\bibitem{gowers2024formalizing}
W.~T.~Gowers, D.~Green, F.~Manners, and T.~Tao.
\newblock On a conjecture of Marton.
\newblock \textit{arXiv:2311.05762}, 2023.
\newblock (Lean formalization by T.~Bloom et al., 2024.)

\bibitem{vaughan2013flagmatic}
E.~R.~Vaughan.
\newblock Flagmatic 2.0: A user-friendly implementation of flag algebra
  arguments.
\newblock Preprint, 2013. Available at \texttt{https://github.com/jsloan/flagmatic}.

\bibitem{chlipala2013cpdt}
A.~Chlipala.
\newblock \textit{Certified Programming with Dependent Types}.
\newblock MIT Press, 2013.

\bibitem{cohen2013refinements}
C.~Cohen, M.~Denes, and A.~M\"{o}rtberg.
\newblock Refinements for free!
\newblock In \textit{Proc.\ CPP 2013}, LNCS~8307, pages 147--162, 2013.

\bibitem{amin2017collapsing}
N.~Amin and T.~Rompf.
\newblock Type soundness proofs with definitional interpreters.
\newblock In \textit{Proc.\ POPL 2017}, pages 666--679, 2017.

\bibitem{harrison2007verifying}
J.~Harrison.
\newblock Verifying nonlinear real formulas via sums of squares.
\newblock In \textit{Proc.\ TPHOLs 2007}, LNCS~4732, pages 102--118, 2007.

\bibitem{parrilo2003minimizing}
P.~A.~Parrilo and B.~Sturmfels.
\newblock Minimizing polynomial functions.
\newblock In \textit{Algorithmic and Quantitative Real Algebraic Geometry},
  DIMACS Series in Discrete Math., pages 83--99, 2003.

\bibitem{ebner2017structured}
G.~Ebner, S.~Ullrich, J.~Roesch, J.~Avigad, and L.~de~Moura.
\newblock A metaprogramming framework for formal verification.
\newblock \textit{Proc.\ ACM Program.\ Lang.}, 1(ICFP):34:1--34:29, 2017.

\bibitem{sozeau2008coq}
M.~Sozeau and N.~Oury.
\newblock First-class type classes.
\newblock In \textit{Proc.\ TPHOLs 2008}, LNCS~5170, 2008.

\bibitem{malecha2014towards}
G.~Malecha and G.~Morrisett.
\newblock Towards foundational verification of cyber-physical systems.
\newblock In \textit{Proc.\ SoSyM 2014}, 2014.

\bibitem{billingsley1999convergence}
P.~Billingsley.
\newblock \textit{Convergence of Probability Measures}, 2nd ed.
\newblock Wiley, 1999.

\bibitem{lovasz2012large}
L.~Lov\'{a}sz.
\newblock \textit{Large Networks and Graph Limits}.
\newblock American Mathematical Society, 2012.

\end{thebibliography}
---END REFERENCE DRAFT---

Revise the Reference Draft for section 'Conclusion' to address the feedback above.
Make targeted changes: edit, cut, or expand only what the feedback requires.
Preserve structure and content not targeted by any feedback point.
Hard gate: satisfy all Section Blueprint constraints (subsections, equations, code references where required).
For mathematical formulas, derive and align notation from the listed Equation Source PDFs.
Do not include \section{...}.
Save output as writer_output.md.
