# Verifier Task

Project: Formalizing Flag Algebras in Lean 4 via Computational Reflection
Target Section: Background: Flag Algebras

Depth Target:
- 3-5 substantial paragraphs with clear logical flow, not a short overview.

Section Blueprint (Hard Constraints):
- min_subsections: 4
- min_paragraphs: 8
- min_equations: 6
- must_define_symbols:
  - type sigma
  - sigma-flag
  - flag isomorphism
  - induced density p(F,G)
  - flag product
  - positive homomorphism
  - semantic cone
  - Turán density pi(F;H)
- must_use_equation_sources:
  - papers/References/Razborov07.pdf
  - papers/References/GrzesikThesis14.pdf

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
- papers/paper_claude.tex already has a concise background section. Improve mathematical depth: expand the flag density definition, make the flag product formula explicit, and add the downward operator definition.
- When drafting this section, also draw on papers/References/Razborov07.pdf and papers/References/GrzesikThesis14.pdf for mathematical precision.
- The section must define: type σ, σ-flag, flag isomorphism, flag density p(F,G), flag product, flag algebra as quotient module, positive homomorphism, semantic cone, and Turán density. End with the Erdős pentagon problem statement.
- Do not claim details from external papers unless they are actually checked from those sources.

Read writer_output.md first.

Selected evidence:
1. [text] line @ papers/paper_claude.tex:18 :: % ---- Theorem environments -----------------------------------------------
2. [text] line @ papers/paper_claude.tex:19 :: \newtheorem{theorem}{Theorem}[section]
3. [text] line @ papers/paper_claude.tex:20 :: \newtheorem{lemma}[theorem]{Lemma}
4. [text] line @ papers/paper_claude.tex:21 :: \newtheorem{definition}[theorem]{Definition}
5. [text] line @ papers/paper_claude.tex:22 :: \newtheorem{example}[theorem]{Example}
6. [text] line @ papers/paper_claude.tex:23 :: \newtheorem{remark}[theorem]{Remark}
7. [text] line @ papers/paper_claude.tex:30 :: \newcommand{\Flag}[1]{\mathcal{F}^{#1}}
8. [text] line @ papers/paper_claude.tex:31 :: \newcommand{\FlagAlg}[1]{\mathcal{A}^{#1}}
9. [text] line @ papers/paper_claude.tex:34 :: \newcommand{\tdensity}[2]{\pi(#1;\,#2)}
10. [text] line @ papers/paper_claude.tex:35 :: \newcommand{\lean}[1]{\texttt{#1}}
11. [text] line @ papers/paper_claude.tex:36 :: \newcommand{\leanfmt}[1]{\texttt{\small #1}}
12. [text] line @ papers/paper_claude.tex:38 :: % Lean code style
13. [text] line @ papers/paper_claude.tex:39 :: \lstdefinelanguage{Lean4}{
14. [text] line @ papers/paper_claude.tex:40 :: keywords={def,theorem,lemma,instance,structure,class,import,open,namespace,
15. [text] line @ papers/paper_claude.tex:42 :: return,do,for,in,noncomputable,abbrev,variable,section,
16. [text] line @ papers/paper_claude.tex:43 :: native_decide,decide,norm_num,simp,ring,linarith,omega,
17. [text] line @ papers/paper_claude.tex:49 :: stringstyle=\color{orange!80!black},
18. [text] line @ papers/paper_claude.tex:50 :: morestring=[b]",
19. [text] line @ papers/paper_claude.tex:68 :: \lstset{language=Lean4, frame=single, framesep=4pt,
20. [text] line @ papers/paper_claude.tex:72 :: \title{Formalizing Flag Algebras in Lean~4 via Computational Reflection}
21. [text] line @ papers/paper_claude.tex:95 :: \begin{abstract}
22. [text] line @ papers/paper_claude.tex:96 :: Razborov's flag algebra method is one of the most powerful tools in extremal
23. [text] line @ papers/paper_claude.tex:97 :: combinatorics, having resolved many open problems about asymptotic subgraph
24. [text] line @ papers/paper_claude.tex:98 :: densities.  Applying it in practice, however, requires combining abstract algebraic


Reference Section Draft (your primary starting point — improve and refine this):
---BEGIN REFERENCE DRAFT---
\label{sec:background}

\paragraph{Types and flags.}
Fix a finite simple graph $\sigma$ on vertex set $[k] = \{1,\ldots,k\}$,
called a \emph{type} of size $k$.  A \emph{$\sigma$-flag} is a pair
$(G, \theta)$ where $G$ is a finite simple graph and
$\theta : [k] \hookrightarrow V(G)$ is an injective graph homomorphism from
$\sigma$ to $G$ (i.e., an embedding of the type).  Two $\sigma$-flags
$(G,\theta)$ and $(G',\theta')$ are \emph{isomorphic} if there is a graph
isomorphism $\phi : G \to G'$ with $\phi \circ \theta = \theta'$.  We write
$\Flag{\sigma}_n$ for the set of isomorphism classes of $\sigma$-flags of size
$n$ (necessarily finite), and $\Flag{\sigma} = \bigcup_n \Flag{\sigma}_n$.

The \emph{empty type} $\emptyset$ (size $k=0$) gives ordinary graphs up to
isomorphism.  For this type, flags are just isomorphism classes of graphs.

\paragraph{Flag densities.}
For $\sigma$-flags $F$ of size $m$ and $G$ of size $n \geq m$, the
\emph{induced density} $\den{F}{G}$ is the probability that a uniformly random
$(m - k)$-subset of $V(G) \setminus \operatorname{Im}(\theta_G)$ induces a
copy of $F$ compatible with the type embedding.  More precisely:
\[
  \den{F}{G} \;=\;
  \frac{\bigl|\{\text{injections } \iota : V(F) \to V(G) \mid \iota \text{ preserves type and induces } F\}\bigr|}
       {\binom{n-k}{m-k} \cdot (m-k)!}.
\]
This quantity is always in $[0,1]$ and is a rational number whenever $G$ is
finite.

\paragraph{The flag algebra.}
Fix a type $\sigma$.  The \emph{flag algebra} $\FlagAlg{\sigma}$ is
constructed as follows.  Let $\mathbb{R}[\Flag{\sigma}]$ be the free
$\R$-module with basis $\Flag{\sigma}$.  Define the \emph{zero space}
$\mathcal{Z}^\sigma$ as the subspace generated by elements of the form
\[
  F - \sum_{G \in \Flag{\sigma}_n} \den{F}{G} \cdot G,
\]
for each $F \in \Flag{\sigma}_m$ and each $n \geq m$.  Then
$\FlagAlg{\sigma} = \mathbb{R}[\Flag{\sigma}] / \mathcal{Z}^\sigma$.

The product of $F \in \Flag{\sigma}_m$ and $F' \in \Flag{\sigma}_{m'}$ at size
$\ell \geq m + m' - k$ is
\[
  F \cdot F' = \sum_{G \in \Flag{\sigma}_\ell} \den{F,F'}{G} \cdot G,
\]
where $\den{F,F'}{G}$ is the probability that two independently chosen
(compatible) subsets of $V(G)$ induce copies of $F$ and $F'$ respectively.
This product is well-defined on the quotient and makes $\FlagAlg{\sigma}$ into
a commutative $\R$-algebra.

\paragraph{The semantic cone and positivity.}
A \emph{positive homomorphism} is an $\R$-algebra homomorphism
$\phi : \FlagAlg{\emptyset} \to \R$ satisfying $\phi(F) \geq 0$ for all
flags $F$.  It can be shown that positive homomorphisms are in bijection with
convergent sequences of graphs: every infinite graph sequence that
``converges'' (in the sense that all flag densities have limits) determines a
unique positive homomorphism.

The \emph{semantic cone} is $\{f \in \FlagAlg{\sigma} \mid \forall \phi, \phi(f) \geq 0\}$.
Razborov's key theorem is:
\begin{theorem}[Razborov~\cite{razborov2007flag}]
  If $A$ is a positive semidefinite matrix and $e_1,\ldots,e_r$ are typed flags
  in $\FlagAlg{\sigma}$, then $\sum_{i,j} A_{ij} \cdot e_i e_j$ lies in the
  semantic cone after averaging over the type embedding (the ``downward'' operator
  $\llbracket \cdot \rrbracket_\sigma$).
\end{theorem}
This is the main mechanism by which SDP certificates produce valid
non-negativity proofs.

\paragraph{Turán density and the pentagon problem.}
For unlabeled graphs $F$ and $H$, the \emph{generalized Turán density}
$\tdensity{F}{H}$ is:
\[
  \tdensity{F}{H} = \lim_{n\to\infty} \frac{1}{\binom{n}{|V(F)|}}
  \max\bigl\{|\text{copies of } F \text{ in } G \mid G \text{ is } H\text{-free},\; |V(G)|=n\bigr\}.
\]
The \emph{Erd\H{o}s pentagon problem} asks for $\tdensity{K_3}{C_5}$: the
maximum density of triangles in triangle-free-with-respect-to-$C_5$-free
graphs.  The answer, $24/625$, was proved by Grzesik~\cite{grzesik2012} and
independently by Hatami, Hladk\'y, Kr\'al, Norine, and
Razborov~\cite{hatami2012}; it is achieved by the blow-up of $C_5$.

% =========================================================================
---END REFERENCE DRAFT---

Revise to remove unsupported claims and strengthen evidence alignment.
If the prose is shallow, expand it to match exemplar-paper depth while staying evidence-grounded.
Hard gate: reject output if Section Blueprint constraints are not satisfied.
For equation-heavy sections, verify formulas and notation are consistent with the listed Equation Source PDFs.
Return only final LaTeX section body without markdown fences and without \section{...}.
Save output as verifier_output.md.
