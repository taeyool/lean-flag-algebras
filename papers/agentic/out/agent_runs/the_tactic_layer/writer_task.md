# Writer Task

Project: Formalizing Flag Algebras in Lean 4 via Computational Reflection
Target Section: The Tactic Layer

Depth Target:
- 3-5 substantial paragraphs with clear logical flow, not a short overview.

Section Blueprint (Hard Constraints):
- min_subsections: 3
- min_paragraphs: 6
- min_code_references: 6
- required_repo_files:
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
- papers/paper_claude.tex has a tactic layer section covering naming conventions, ac_sort_pipeline, and prove_flag_expand/mul_with_forbidden_flag. Improve by: (1) giving a concrete before/after example showing how many tactic steps are replaced, (2) explaining the AST traversal approach in more detail, (3) making the performance argument (>10 min timeout vs <1 sec) more prominent.
- The naming convention as machine-readable encoding is a design insight that distinguishes this work — explain it clearly and connect it to certified compilation ideas.
- Include the concrete example of prove_flag_expand_with_forbidden_flag usage.

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
\label{sec:tactics}

The reflection layer handles data-heavy computation.  A complementary layer of
custom elaboration tactics handles the structurally repetitive proof steps that
arise in every flag algebra argument.

\subsection{Naming Convention as Machine-Readable Encoding}

A key enabling design decision is that every flag and flag algebra constant is
named according to the scheme \lean{Flag\_n\_k\_m\_i} and
\lean{FlagAlgebra\_n\_k\_m\_i}, where $n$ is the vertex count, $k$ and $m$
identify the type graph, and $i$ is the canonical index within that
isomorphism class.  This convention is not merely organizational: it serves as
a machine-readable encoding of mathematical structure that all custom tactics
exploit.  By parsing the trailing integers from a constant's name, a tactic can
determine:
\begin{itemize}
  \item the \emph{canonical order} of a flag term in a linear combination,
  \item the \emph{precomputed lemma name} for its density or multiplication
    identity, and
  \item the \emph{flag type parameters} needed to instantiate the appropriate
    adequacy theorem.
\end{itemize}

\paragraph{Why names rather than type-class annotations.}
An alternative design would encode this information via Lean~4 type-class
instances or user-defined attributes.  We chose the naming convention instead
for a performance reason: Lean~4's elaboration monad can inspect a constant's
\lean{Name} (a syntactic object) without triggering type-checking or
attribute resolution, which can time out on large expressions.  By encoding
the flag index in the name, \lean{ac\_sort\_pipeline} computes sort keys
entirely in the fast elaboration path, without reducing any term in the kernel.
The approach is similar to the use of canonical normal forms in certified
compilers: the name is a ``normal form'' that tactics can manipulate directly.

\begin{example}[A name as a tiny certificate]
  The name \lean{FlagAlgebra\_3\_0\_0\_2} is not just a human mnemonic.  It says
  that the term is an untyped flag-algebra basis element (\lean{k = 0}), living
  at size $3$, with canonical index $2$ among the generated representatives.
  A tactic that sees this constant already knows where it belongs in the
  normal order of a sum, which generated expansion lemma to try, and which
  multiplication-table entry can mention it.  In other words, the name carries
  the same kind of lightweight metadata that a compiler might attach to an
  intermediate-language node.  The difference is that here the metadata is
  available to the Lean elaborator without any type-class search.
\end{example}

\subsection{Linear Normalization: \lean{ac\_sort\_pipeline}}

\paragraph{The problem.}
After expanding a flag algebra element at a larger size, the proof obligation
is typically an equality between two linear combinations of flag terms that are
provably equal but syntactically in different orders.  Generic tactics such as
\lean{ring} or \lean{ac\_rfl} handle this in principle but become prohibitively
slow on large expressions ($\geq 20$ terms) because they must search over all
permutations of summands.

\paragraph{The solution.}
The \lean{sort} family of tactics, implemented in
\lean{LeanFlagAlgebras.ErdosPentagon.SortTactic}, normalizes a linear
combination by:
\begin{enumerate}
  \item \emph{Flattening.}  The tactic traverses the expression's AST,
    pattern-matching on \lean{HAdd.hAdd}, \lean{HSub.hSub},
    \lean{HSMul.hSMul}, and \lean{Neg.neg}, to produce a flat list of
    \lean{(base, coefficient)} pairs.
  \item \emph{Sorting.}  Each base term is assigned a sort key: the trailing
    integer in its constant name (e.g., \lean{FlagAlgebra\_5\_1\_0\_3} gets
    key $3$), with the pretty-printed string as a tiebreaker.  The list is
    sorted by this key using insertion sort.
  \item \emph{Rebuilding.}  The sorted list is reassembled into a Lean
    expression (left-associative sum of scalar multiples).
  \item \emph{Equality proof.}  The tactic proves that the original and sorted
    expressions are equal by \lean{ac\_rfl} or \lean{abel\_nf}, then replaces
    the goal with the sorted form.
\end{enumerate}
The full pipeline \lean{ac\_sort\_pipeline} additionally runs \lean{norm\_num}
before and after sorting, and collects like terms with
\lean{add\_smul} rewriting after sorting, so that the resulting expression is
fully simplified.

\paragraph{Why this is necessary, not cosmetic.}
The comment in \lean{ErdosPentagon.Lemmas} is revealing:
``\texttt{-- sort\_at -- takes more than 10 minutes}''.
The generic \lean{sort\_at} (which uses \lean{simp} without index guidance)
times out on expressions with $\sim 25$ flag terms.  The index-guided
\lean{ac\_sort} completes the same step in under a second, by exploiting domain
knowledge to bypass combinatorial search.  The tactic is not a convenience
wrapper; it is a correctness-enabling optimization.

\subsection{Flag Expansion and Multiplication Tactics}

\paragraph{The problem.}
A central step in every flag algebra proof is the \emph{expansion} identity: a
small flag $F \in \Flag{\sigma}_m$, viewed in the algebra at size $n > m$,
equals a weighted sum of all $n$-vertex flags.  Similarly, the product of two
typed flags equals a linear combination at the product size.  These identities
must be verified for each specific flag and expansion size that appears in the
proof---dozens of instances per theorem.

\paragraph{\lean{prove\_flag\_expand\_with\_forbidden\_flag} N.}
This tactic, implemented in \lean{LeanFlagAlgebras.Logic.Tactic}, proves goals
of the form:
\[
  \bigl(\lean{FlagAlgebra\_3\_0\_0\_3} =_{a} 0\bigr)
  \;\vdash_a\;
  \lean{FlagAlgebra\_2\_0\_0\_1} =_{a} \tfrac{1}{3} \cdot \lean{FlagAlgebra\_3\_0\_0\_1}
    + \tfrac{2}{3} \cdot \lean{FlagAlgebra\_3\_0\_0\_2}
\]
where $=_{a}$ is the assertion operator in the logical framework.  The tactic:
\begin{enumerate}
  \item Scans the goal's AST for all \lean{FlagAlgebra\_*} and \lean{Flag\_*}
    constants using \lean{collectPrefixConstants}, and parses their indices
    $(n, k, m, i)$ using \lean{parseFlagAlgebraIndices?}.
  \item Unfolds the flag definitions by name, introduces the positive
    homomorphism $\phi$ and the forbidden-flag hypothesis $h$.
  \item Applies \lean{unitVector\_quot\_eq\_sum} to expand the flag at size
    $N$, then rewrites with the preloaded lemmas \lean{flagSet\_N\_k\_m\_eq\_univ}
    and \lean{flagSet\_N\_k\_m\_val\_eq} (themselves generated by the loaders).
  \item Simplifies the expansion using $h$ (the forbidden flag has value~0)
    and closes with \lean{ring\_nf}.
\end{enumerate}

\paragraph{\lean{prove\_flag\_mul\_with\_forbidden\_flag} N.}
This tactic handles product identities under a forbidden-flag assumption.  It
follows the same structure but applies \lean{unitVector\_quot\_mul\_eq\_flagMul\_quot}
and unfolds the flag multiplication at size $N$.  It also normalizes the
multiplication order: if the two operands' indices are in non-canonical order,
it first applies \lean{mul\_comm} before the rest of the proof, ensuring that
precomputed lemmas (which assume a fixed canonical ordering) can be applied
directly.

The result of these two tactics is that expansion and multiplication identities
that would individually require 15--20 tactic steps are each proved by a single
tactic invocation:
\begin{lstlisting}
example : FlagAlgebra_3_0_0_3 =a 0
    |-a FlagAlgebra_2_0_0_1 =a (1/3 : R) * FlagAlgebra_3_0_0_1
                             + (2/3 : R) * FlagAlgebra_3_0_0_2
  := by prove_flag_expand_with_forbidden_flag 3
\end{lstlisting}

This example is the Mantel expansion above in executable clothing.  The goal
says: assuming the triangle flag \lean{FlagAlgebra\_3\_0\_0\_3} has value zero,
prove that the edge flag expands as a weighted sum of the one-edge and
two-edge three-vertex graphs.  The human proof is a one-line counting argument:
among the three vertex pairs, the one-edge graph contains one edge and the
two-edge path contains two.  The Lean proof has to find the right generated
expansion lemma, instantiate it at size $3$, remove the forbidden triangle
term, and normalize scalar arithmetic.  The point of the tactic is to make the
formal proof resemble the human explanation again.

\paragraph{Key challenge.}
The tactic must be robust to the syntactic variation that Lean's elaborator
introduces: after unification and implicit argument resolution, the same flag
term can appear in different syntactic forms (with universe levels, implicit
arguments, or coercions inserted differently).  We addressed this by defining
the \lean{collectPrefixConstants} traversal to normalize the expression tree
before inspecting constant names, and by using \lean{Expr.eqv} rather than
structural equality when comparing flag terms.  This required significant
experimentation with Lean~4's metaprogramming API.
---END REFERENCE DRAFT---

Revise the Reference Draft for section 'The Tactic Layer' to address the feedback above.
Make targeted changes: edit, cut, or expand only what the feedback requires.
Preserve structure and content not targeted by any feedback point.
Hard gate: satisfy all Section Blueprint constraints (subsections, equations, code references where required).
For mathematical formulas, derive and align notation from the listed Equation Source PDFs.
Do not include \section{...}.
Save output as writer_output.md.
