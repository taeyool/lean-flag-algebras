# Retriever Task

Project: Formalizing Flag Algebras in Lean 4 via Computational Reflection
Target Section: Abstract Formalization

Depth Target:
- 3-5 substantial paragraphs with clear logical flow, not a short overview.

Section Blueprint (Hard Constraints):
- min_subsections: 4
- min_paragraphs: 8
- min_code_references: 10
- required_repo_files:
  - LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean
  - LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean
  - LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean
  - LeanFlagAlgebras/FlagAlgebra/QuadraticForm.lean
  - LeanFlagAlgebras/Logic/Defs.lean
  - LeanFlagAlgebras/Logic/Tactic.lean

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
- papers/paper_claude.tex already has a detailed formalization section covering: Flags as Quotient Types, Flag Algebra as Quotient Module, Semantic Ordering via Positive Homomorphisms, and the Forbidden-Subgraph Framework.
- Improve by: (1) expanding the explanation of FlagWithSize and FinFlag type hierarchy, (2) clarifying how ZeroSpace encodes the density-expansion relations, (3) giving more detail on the forbidLE predicate and why it is more general than Razborov's original axiom approach.
- The forbidden-subgraph framework (forbidLE, generalizedTuranDensity_le_of_forbidLE) is a key novel contribution — ensure it gets at least one full subsection with the theorem statement shown.

Read planner_output.json first, then select evidence IDs.

Candidate evidence list:
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
25. [text] line @ papers/paper_claude.tex:107 :: Razborov's flag algebra method is one of the most powerful tools in extremal
26. [text] line @ papers/paper_claude.tex:108 :: combinatorics, having resolved many open problems about asymptotic subgraph
27. [text] line @ papers/paper_claude.tex:109 :: densities.  Applying it in practice, however, requires combining abstract algebraic
28. [text] line @ papers/paper_claude.tex:110 :: and measure-theoretic reasoning with large external computations: subgraph
29. [text] line @ papers/paper_claude.tex:111 :: density tables computed by enumeration, and semidefinite programming (SDP)
30. [text] line @ papers/paper_claude.tex:112 :: certificates found by numerical solvers.  Formalizing such proofs in a proof
31. [text] line @ papers/paper_claude.tex:113 :: assistant is therefore a challenge on two fronts: the abstract mathematical
32. [text] line @ papers/paper_claude.tex:116 :: compromise the overall proof's trustworthiness.
33. [text] line @ papers/paper_claude.tex:118 :: We present a Lean~4 formalization of Razborov's flag algebra method for
34. [text] line @ papers/paper_claude.tex:119 :: graphs, organized around a \emph{reflection-based} architecture.  At the
35. [text] line @ papers/paper_claude.tex:120 :: abstract level, we define flags as quotient types under graph isomorphism,
36. [text] line @ papers/paper_claude.tex:121 :: construct the flag algebra as a quotient module, equip it with a semantic
37. [text] line @ papers/paper_claude.tex:122 :: ordering via positive homomorphisms, and connect flag algebra inequalities to
38. [text] line @ papers/paper_claude.tex:123 :: combinatorial Turán densities through a measure-theoretic framework.  At the
39. [text] line @ papers/paper_claude.tex:124 :: computational level, we introduce a concrete, decidably-equal graph
40. [text] line @ papers/paper_claude.tex:125 :: representation (\lean{Sym2Graph}) and prove adequacy theorems connecting it to
41. [text] line @ papers/paper_claude.tex:126 :: the abstract definitions; this allows \lean{native\_decide} and \lean{decide
42. [text] line @ papers/paper_claude.tex:127 :: +kernel} to discharge over 2{,}800 density and matrix-equality obligations
43. [text] line @ papers/paper_claude.tex:128 :: automatically.  Structural proof obligations---normalizing linear combinations
44. [text] line @ papers/paper_claude.tex:129 :: of flag terms and applying expansion and multiplication identities---are handled
45. [text] line @ papers/paper_claude.tex:130 :: by a suite of custom Lean~4 elaboration tactics that inspect the AST and exploit
46. [text] line @ papers/paper_claude.tex:131 :: a canonical naming convention for flags as a machine-readable encoding of
47. [text] line @ papers/paper_claude.tex:134 :: As results, we give complete formal proofs of Mantel's theorem and of the
48. [text] line @ papers/paper_claude.tex:135 :: Erd\H{o}s pentagon theorem ($\tdensity{C_5}{K_3} = 24/625$), the latter including
49. [text] line @ papers/paper_claude.tex:136 :: both the upper bound via a formally verified SDP certificate and the lower bound
50. [text] line @ papers/paper_claude.tex:137 :: via an explicit blow-up construction.  To our knowledge, this is the first
51. [text] line @ papers/paper_claude.tex:138 :: formalization of the flag algebra method in any proof assistant.  The
52. [text] line @ papers/paper_claude.tex:139 :: formalization comprises approximately 25{,}000 lines of Lean~4 code.
53. [text] line @ papers/paper_claude.tex:140 :: \end{abstract}
54. [text] line @ papers/paper_claude.tex:143 :: \section{Introduction}
55. [text] line @ papers/paper_claude.tex:146 :: \paragraph{Flag algebras in extremal combinatorics.}
56. [text] line @ papers/paper_claude.tex:147 :: A central question in extremal graph theory is: among all large graphs on $n$
57. [text] line @ papers/paper_claude.tex:148 :: vertices that avoid some fixed graph $H$ as a subgraph, what is the
58. [text] line @ papers/paper_claude.tex:149 :: maximum possible density of copies of another graph $F$?
59. [text] line @ papers/paper_claude.tex:150 :: The \emph{generalized Turán density} $\tdensity{F}{H}$
60. [text] line @ papers/paper_claude.tex:151 :: formalizes this question as a limit:
61. [text] line @ papers/paper_claude.tex:153 :: \tdensity{F}{H}
62. [text] line @ papers/paper_claude.tex:162 :: Razborov's flag algebra method~\cite{razborov2007flag} provides a
63. [text] line @ papers/paper_claude.tex:164 :: It works by constructing a graded, commutative $\mathbb{R}$-algebra---the
64. [text] line @ papers/paper_claude.tex:165 :: \emph{flag algebra}---whose elements represent linear combinations of
65. [text] line @ papers/paper_claude.tex:166 :: induced subgraph patterns.  The algebra is equipped with a product encoding
66. [text] line @ papers/paper_claude.tex:167 :: simultaneous occurrence and a semantic ordering: an element $f$ is
67. [text] line @ papers/paper_claude.tex:169 :: positive $\mathbb{R}$-algebra homomorphism is $\geq 0$.
68. [text] line @ papers/paper_claude.tex:170 :: Non-negativity certificates for carefully chosen elements yield upper bounds
69. [text] line @ papers/paper_claude.tex:171 :: on Turán densities directly.
70. [text] line @ papers/paper_claude.tex:173 :: In practice, these certificates are produced by semidefinite programming:
71. [text] line @ papers/paper_claude.tex:174 :: one seeks a positive semidefinite matrix $Q$ such that
72. [text] line @ papers/paper_claude.tex:175 :: $f - c\cdot\mathbf{1} = \sum_{i,j} Q_{ij}\cdot e_i e_j$ holds in the algebra
73. [text] line @ papers/paper_claude.tex:176 :: (where the $e_i$ are typed flag basis elements and $c$ is the claimed bound).
74. [text] line @ papers/paper_claude.tex:177 :: An SDP solver finds $Q$ numerically; one must then \emph{verify} that $Q$ is
75. [text] line @ papers/paper_claude.tex:178 :: genuinely positive semidefinite and that the algebraic identity holds exactly.
76. [text] line @ papers/paper_claude.tex:180 :: \paragraph{The formalization challenge.}
77. [text] line @ papers/paper_claude.tex:181 :: Formalizing a flag algebra proof in a proof assistant requires confronting three
78. [text] line @ papers/paper_claude.tex:182 :: distinct, non-reducible categories of proof obligation:
79. [text] line @ papers/paper_claude.tex:185 :: \item \textbf{Abstract structure.}  Flags (quotients of labeled graphs under
80. [text] line @ papers/paper_claude.tex:186 :: isomorphism), the flag algebra (a quotient module equipped with a commutative
81. [text] line @ papers/paper_claude.tex:187 :: ring structure), positive homomorphisms (the semantic ordering),
82. [text] line @ papers/paper_claude.tex:188 :: the Turán density (a measure-theoretic limit), and the transfer theorem
83. [text] line @ papers/paper_claude.tex:189 :: connecting flag algebra inequalities to density bounds.  These are
84. [text] line @ papers/paper_claude.tex:193 :: \item \textbf{Data-heavy computation.}  For each pair of flags $(F,G)$
85. [text] line @ papers/paper_claude.tex:194 :: appearing in the proof, one must certify the exact rational density
86. [text] line @ papers/paper_claude.tex:195 :: $\den{F}{G}$.  For the Erd\H{o}s pentagon theorem,
87. [text] line @ papers/paper_claude.tex:196 :: this means thousands of density values over graphs with up to five vertices
88. [text] line @ papers/paper_claude.tex:197 :: and flag multiplication tables of similar size.  These values are computed
89. [text] line @ papers/paper_claude.tex:198 :: externally and must be imported into the proof and verified against the
90. [text] line @ papers/paper_claude.tex:199 :: formal definitions.
91. [text] line @ papers/paper_claude.tex:201 :: \item \textbf{Algebraic bookkeeping.}  Flag algebra arguments involve
92. [text] line @ papers/paper_claude.tex:202 :: manipulating linear combinations of hundreds of flag terms: expanding a
93. [text] line @ papers/paper_claude.tex:203 :: flag at a larger vertex count, computing products of typed flags, and
94. [text] line @ papers/paper_claude.tex:204 :: normalizing sums into a canonical form.  Each individual step is routine
95. [text] line @ papers/paper_claude.tex:209 :: \emph{qualitatively different} proof techniques.  The abstract structure
96. [text] line @ papers/paper_claude.tex:211 :: The data-heavy computation requires a \emph{reflection} architecture:
97. [text] line @ papers/paper_claude.tex:212 :: a decidably-computable concrete representation whose connection to the abstract
98. [text] line @ papers/paper_claude.tex:213 :: definitions is certified by adequacy theorems, allowing Lean's kernel (or native
99. [text] line @ papers/paper_claude.tex:214 :: evaluator) to check each density value automatically.
100. [text] line @ papers/paper_claude.tex:215 :: The algebraic bookkeeping requires \emph{proof-by-reflection via custom
101. [text] line @ papers/paper_claude.tex:216 :: elaboration tactics} that inspect the syntactic structure of the proof state
102. [text] line @ papers/paper_claude.tex:217 :: and dispatch the right sequence of domain-specific lemmas without manual
103. [text] line @ papers/paper_claude.tex:220 :: \paragraph{This paper.}
104. [text] line @ papers/paper_claude.tex:221 :: We present a Lean~4 formalization of Razborov's flag algebra method for
105. [text] line @ papers/paper_claude.tex:222 :: graphs, organized around the two-layer architecture that the challenge analysis
106. [text] line @ papers/paper_claude.tex:223 :: dictates.  The \emph{abstract layer} encodes the mathematical semantics
107. [text] line @ papers/paper_claude.tex:224 :: faithfully in Lean~4's dependent type system, including a novel
108. [text] line @ papers/paper_claude.tex:225 :: \emph{general forbidden-subgraph reasoning rule} that does not require
109. [text] line @ papers/paper_claude.tex:226 :: problem-specific axiomatization.  The \emph{reflection layer} bridges the
110. [text] line @ papers/paper_claude.tex:227 :: abstract definitions to a finitely-computable concrete representation, enabling
111. [text] line @ papers/paper_claude.tex:228 :: automated discharge of density and SDP certificate obligations.
112. [text] line @ papers/paper_claude.tex:230 :: \paragraph{Contributions.}
113. [text] line @ papers/paper_claude.tex:232 :: \item \textbf{Abstract formalization (\S\ref{sec:abstract}).}
114. [text] line @ papers/paper_claude.tex:233 :: We formalize the full abstract structure of Razborov's flag algebra in
115. [text] line @ papers/paper_claude.tex:234 :: Lean~4: flags as quotient types of labeled graphs under isomorphism,
116. [text] line @ papers/paper_claude.tex:235 :: the flag algebra as a quotient $\mathbb{R}$-module with a commutative ring
117. [text] line @ papers/paper_claude.tex:236 :: structure, the semantic ordering via positive homomorphisms, and a
118. [text] line @ papers/paper_claude.tex:237 :: measure-theoretic forbidden-subgraph reasoning framework
119. [text] line @ papers/paper_claude.tex:238 :: (\lean{forbidLE}, \lean{generalizedTuranDensity\_le\_of\_forbidLE}).
120. [text] line @ papers/paper_claude.tex:239 :: The forbidden-subgraph rule is formulated inside a \emph{single} ambient

Output format (JSON only):
{
  "selected_ids": [1,2,3],
  "selection_rationale": ["..."],
  "missing_evidence": ["..."]
}
