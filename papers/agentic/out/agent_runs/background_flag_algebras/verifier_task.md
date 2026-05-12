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

=== REVISION MODE: Feedback to Address ===
Each point below MUST be addressed. Do not silently skip any.
Produce a concrete fix for each point, not just an acknowledgement.

## Global Feedback
1. The title "Formalizing Flag Algebras in Lean 4 via Computational Reflection" is misleading: computational reflection is used only for verifying SDP certificates and density tables, not for formalizing flag algebra theory itself. Consider removing "via Computational Reflection" from the title, or replacing it with a phrase that more accurately reflects the overall scope of the work.
=== END FEEDBACK ===

Read writer_output.md first.

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
\label{sec:background}

This section recalls the mathematical definitions underlying flag algebras,
following Razborov~\cite{razborov2007flag}, and sets up the notation used
throughout the paper.
For $n \in \mathbb{N}$ we write $[n] = \{1,\ldots,n\}$.
All graphs are undirected, finite and simple.

\subsection{Types and Flags}

\paragraph{Types.}
A \emph{type} of size $k$ is a graph $\sigma$ with vertex set $[k]$.
The \emph{empty type} $\emptyset$ (size $k=0$) is the unique graph on the
empty vertex set; flags over $\emptyset$ are just ordinary finite graphs
up to isomorphism.

\paragraph{Flags.}
Fix a type $\sigma$ of size $k$.
A \emph{$\sigma$-flag} is a pair $G^\sigma = (G, \theta)$ where $G$ is a
finite graph and $\theta : [k] \hookrightarrow V(G)$ is an injective map such
that $\sigma$ is isomorphic to $G[\operatorname{Im}(\theta)]$ via $\theta$ 
(i.e., $\theta$ is a graph embedding of $\sigma$ into $G$).
The integer $|V(G)|$ is the \emph{size} of $G^\sigma$.

Two $\sigma$-flags $(G_1,\theta_1)$ and $(G_2,\theta_2)$ are
\emph{isomorphic} if there is a graph isomorphism $\phi: V(G_1)\to V(G_2)$
with $\phi \circ \theta_1 = \theta_2$.  The set of isomorphism classes of
$\sigma$-flags of size $n$ is written $\mathcal{F}^\sigma_n$, and
$\mathcal{F}^\sigma = \bigcup_{n \geq k} \mathcal{F}^\sigma_n$.
Each $\mathcal{F}^\sigma_n$ is finite.

\subsection{Subflag Densities}

\paragraph{Single-flag density.}
For $\sigma$-flags $F$ of size $m$ and $G$ of size $n \geq m$, the
\emph{induced density} $\den{F}{G}$ is the probability that a uniformly
random injective map from $V(F) \setminus \operatorname{Im}(\theta_F)$ to
$V(G) \setminus \operatorname{Im}(\theta_G)$ (extending the type embedding)
induces a copy of $F$ in $G$ compatible with the type.  Explicitly:
\[
  \den{F}{G}
  \;=\;
  \frac{\bigl|\{\iota : V(F) \hookrightarrow V(G)
                  \mid \iota \text{ preserves type embedding and induces }F\}\bigr|}
       {\binom{n-k}{m-k}\,(m-k)!}.
\]
This value lies in $[0,1] \cap \mathbb{Q}$ and is invariant under
isomorphism of both $F$ and $G$.

\begin{example}[A rooted pentagon density]
  Let $\sigma$ be the one-vertex type, and let $E^\bullet$ be the
  $\sigma$-flag on two vertices in which the unlabeled vertex is adjacent to
  the labeled one.  Let $\overline{E}^{\bullet}$ be the corresponding
  non-edge flag.  Now root a copy of $C_5$ at one of its vertices.  Among the
  four non-root vertices, exactly two are neighbors of the root.  Hence
  \[
    \den{E^\bullet}{C_5^\bullet} = \frac{2}{4} = \frac12,
    \qquad
    \den{\overline{E}^{\bullet}}{C_5^\bullet} = \frac{2}{4} = \frac12.
  \]
  This tiny example captures the reason flags are useful: a flag remembers
  the local view from a labeled configuration.  The same unrooted pentagon can
  be queried from the perspective of a distinguished vertex, and the algebra
  records those conditional densities as first-class objects.
\end{example}

\paragraph{Joint density.}
For $\sigma$-flags $F_1$ of size $m_1$ and $F_2$ of size $m_2$ and a host
flag $G$ of size $n \geq m_1 + m_2 - k$, the \emph{joint density}
$\den{F_1,F_2}{G}$ is the probability that two independently and uniformly
chosen injections from $V(F_i)\setminus [k]$ into $V(G)\setminus [k]$
(sampled without replacement from the same pool) each induce their
respective flag, compatible with the shared type embedding.

\subsection{The Flag Algebra}

Fix a type $\sigma$.  Let $\mathbb{R}[\mathcal{F}^\sigma]$ be the free
$\mathbb{R}$-module with basis $\mathcal{F}^\sigma$.
Define the \emph{zero space} $\mathcal{Z}^\sigma$ as the subspace generated
by all elements of the form
\[
  F - \sum_{G \in \mathcal{F}^\sigma_n} \den{F}{G} \cdot G,
  \qquad F \in \mathcal{F}^\sigma_m,\; n \geq m.
\]
The \emph{flag algebra} is the quotient module
\[
  \mathcal{A}^\sigma \;=\; \mathbb{R}[\mathcal{F}^\sigma] \,/\, \mathcal{Z}^\sigma.
\]
The zero-space relations express the combinatorial identity that, in a
sufficiently large graph, the average density of $F$ over all extensions of
the type embedding equals $\den{F}{G}$.

\paragraph{Multiplication.}
For $[F_1] \in \mathcal{A}^\sigma_{m_1}$ and $[F_2] \in \mathcal{A}^\sigma_{m_2}$,
their product at size $\ell \geq m_1 + m_2 - k$ is
\[
  [F_1] \cdot [F_2]
  \;=\;
  \sum_{G \in \mathcal{F}^\sigma_\ell} \den{F_1,F_2}{G} \cdot [G]
  \;\in\; \mathcal{A}^\sigma_\ell.
\]
This is well-defined on the quotient (independent of $\ell$) and makes
$\mathcal{A}^\sigma$ into a commutative, associative $\mathbb{R}$-algebra
with unit $[\text{type graph } \sigma]$.

\begin{example}[The edge expansion behind Mantel's theorem]
  The simplest useful zero-space relation expands the untyped edge $K_2$ at
  size $3$.  There are four unlabeled graphs on three vertices: the empty
  graph, the one-edge graph, the two-edge path, and the triangle.  If an
  edge is sampled uniformly from the three possible vertex pairs, its density
  in these graphs is respectively
  \[
    0,\qquad \frac13,\qquad \frac23,\qquad 1.
  \]
  Thus the quotient identifies
  \[
    K_2
    \;=\;
    \frac13\,G_{\text{one-edge}}
    + \frac23\,G_{\text{path}}
    + G_{\triangle}
    \qquad\text{in } \mathcal{A}^{\emptyset}.
  \]
  In the Mantel proof, the triangle term is then eliminated under the
  $K_3$-free hypothesis.  This is exactly the kind of elementary
  combinatorial bookkeeping that becomes unbearable in the pentagon proof:
  the coefficients are simple, but there are hundreds of such coefficients
  and they must all line up syntactically inside Lean.
\end{example}

\subsection{The Downward Operator and Semantic Non-Negativity}

\paragraph{Downward (unlabeling) operator.}
For a $\sigma$-flag $F$ of size $m$ (type of size $k$), the \emph{downward
operator} $\llbracket F \rrbracket_\sigma$ averages over all ways to embed
the type $\sigma$ into $F$, producing an element of the untyped algebra:
\[
  \llbracket F \rrbracket_\sigma
  \;=\;
  \frac{k!\,(m-k)!}{m!}
  \sum_{\theta: [k]\hookrightarrow V(F)}
  \bigl[(F, \theta)\bigr]_\emptyset,
\]
extended linearly to all of $\mathcal{A}^\sigma$.
The downward operator is an $\mathbb{R}$-module map
$\llbracket\cdot\rrbracket_\sigma : \mathcal{A}^\sigma \to \mathcal{A}^\emptyset$.

\paragraph{Positive homomorphisms.}
A \emph{positive homomorphism} is an $\mathbb{R}$-algebra homomorphism
$\phi: \mathcal{A}^\emptyset \to \mathbb{R}$ satisfying $\phi([G]) \geq 0$
for every graph $G$.
Positive homomorphisms correspond bijectively to convergent graph sequences:
every sequence $(G_n)$ with $|V(G_n)|\to\infty$ such that all flag densities
have limits determines a unique positive homomorphism~\cite{razborov2007flag}.

The \emph{semantic cone} is
$\mathcal{C} = \{f \in \mathcal{A}^\emptyset \mid \phi(f) \geq 0\ \forall \phi\}$.

\begin{theorem}[Razborov~{\cite{razborov2007flag}}]
  \label{thm:sdp-nonneg}
  For any type $\sigma$, flags $e_1,\ldots,e_r \in \mathcal{A}^\sigma$,
  and positive semidefinite matrix $A \in \mathbb{R}^{r\times r}$,
  \[
    \Bigl\llbracket \sum_{i,j=1}^r A_{ij}\, e_i\, e_j \Bigr\rrbracket_\sigma
    \;\in\; \mathcal{C}.
  \]
\end{theorem}

This theorem is the engine behind all SDP-based flag algebra bounds.
Given a target element $f_0 \in \mathcal{A}^\emptyset$ and a claimed bound
$c \in \mathbb{R}$, if one exhibits a PSD matrix $A$ and typed flags $e_i$ such
that
\[
  c \cdot \mathbf{1} - f_0
  \;=\;
  \Bigl\llbracket \sum_{i,j} A_{ij}\, e_i\, e_j \Bigr\rrbracket_\sigma,
\]
then $\phi(f_0) \leq c$ for all positive homomorphisms $\phi$, yielding an
upper bound on the Turán density of the corresponding graph pattern.

\subsection{Turán Densities and the Pentagon Problem}

\paragraph{Generalized Turán density.}
For unlabeled graphs $F$ and $H$, the \emph{generalized Turán density} is
\[
  \tdensity{F}{H}
  \;=\;
  \lim_{n\to\infty}
  \frac{\max\bigl\{|\text{copies of }F\text{ in }G|
                   \mid |V(G)|=n,\; G \text{ is }H\text{-free}\bigr\}}
       {\binom{n}{|V(F)|}}.
\]

\paragraph{The Erd\H{o}s pentagon problem.}
The problem asks for $\tdensity{C_5}{K_3}$: the maximum density of
pentagons in triangle-free graphs.  The answer $24/625$ was proved
independently by Grzesik~\cite{grzesik2012} and by Hatami, Hladk\'y, Kr\'al,
Norine, and Razborov~\cite{hatami2012}.  It is achieved by the blow-up of
$C_5$ (partition $n$ vertices into five nearly-equal groups and add all edges
between consecutive groups in the cycle).  We use this theorem as the main
case study throughout the paper, as it involves the full proof-engineering
stack: abstract structure, extensional finite counting, data-heavy density
computation (thousands of rational values over 5-vertex graphs), and heavy
algebraic bookkeeping.
---END REFERENCE DRAFT---

Feedback Checklist (verify BEFORE returning output):
For each feedback point in 'Feedback to Address' above, confirm the revised text addresses it.
If any point is unaddressed, fix it now before returning.

Revise to remove unsupported claims and strengthen evidence alignment.
If the prose is shallow, expand it to match exemplar-paper depth while staying evidence-grounded.
Hard gate: reject output if Section Blueprint constraints are not satisfied.
For equation-heavy sections, verify formulas and notation are consistent with the listed Equation Source PDFs.
Return only final LaTeX section body without markdown fences and without \section{...}.
Save output as verifier_output.md.
