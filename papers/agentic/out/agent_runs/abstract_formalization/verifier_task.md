# Verifier Task

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


Reference Section Draft (your primary starting point — improve and refine this):
---BEGIN REFERENCE DRAFT---
\label{sec:abstract}

The abstract formalization layer encodes the mathematical content of
Section~\ref{sec:background} faithfully in Lean~4's dependent type system.
The design principle is that every mathematical definition has a direct
Lean~4 counterpart that preserves the mathematical semantics exactly,
with no hidden invariants or definitional shortcuts.  This section describes
the four main components: flags as quotient types, the flag algebra as a
quotient module, the semantic ordering via positive homomorphisms, and a
general forbidden-subgraph reasoning framework.

\subsection{Flags as Quotient Types}

A \emph{type graph} of size $k$ is a \lean{SimpleGraph (Fin k)}, the standard
Lean~4/Mathlib type for simple graphs on a finite vertex set.  A
\emph{labeled graph} over type $\sigma$ with vertex set $V$ is a pair
\begin{lstlisting}
structure LabeledGraph (sigma : FlagType (Fin n0)) (V : Type) where
  graph     : SimpleGraph V
  typeEmbed : sigma ->gg graph  -- injective graph homomorphism
\end{lstlisting}
where \lean{->gg} denotes a \lean{SimpleGraph} homomorphism that is also
injective on vertices.  Two labeled graphs over the same type are
\emph{flag-isomorphic} if they are related by a graph isomorphism that
commutes with the type embeddings.  The type of flags is then the quotient:
\begin{lstlisting}
def Flag (sigma : FlagType (Fin n0)) (V : Type) : Type :=
  Quotient (labeledGraphSetoid sigma V)
\end{lstlisting}
The setoid \lean{labeledGraphSetoid} is defined from flag-isomorphism,
which is an equivalence relation on labeled graphs.

\paragraph{Size-indexed families.}
We write \lean{FlagWithSize sigma n} for \lean{Flag sigma (Fin n)} (flags of size
$n$) and \lean{FinFlag sigma} for the dependent sum
$\Sigma\, (n : \mathbb{N}),\, \lean{FlagWithSize}\ \sigma\ n$, which collects
all flags across all sizes.
Each \lean{FlagWithSize sigma n} is a \lean{Fintype} (inheriting finiteness from
the finiteness of \lean{Fin n} and the decidability of flag isomorphism,
established in Section~\ref{sec:reflection}), while \lean{FinFlag sigma} is
\lean{Countable} and \lean{Infinite} when the type $\sigma$ is non-trivial.

\subsection{The Flag Algebra as a Quotient Module}

The flag algebra is built in
\lean{LeanFlagAlgebras.FlagAlgebra.FlagAlgebra}.
Following the mathematical definition, we first form the free
$\mathbb{R}$-module of finitely-supported functions on flags:
\begin{lstlisting}
abbrev FlagVector sigma := FinFlag sigma ->0 R  -- Finsupp free module
\end{lstlisting}
(Here \lean{->0} is Mathlib's \lean{Finsupp} type: functions with finite
support, forming a free module over $\mathbb{R}$.)
The \emph{zero space} \lean{ZeroSpace sigma} is defined as the submodule of
\lean{FlagVector sigma} generated by all elements of the form
$[\lean{F}] - \sum_{G \in \lean{FlagWithSize}\ \sigma\ n} \den{F}{G} \cdot [G]$,
for each flag $F$ of size $m$ and each $n \geq m$.
The flag algebra is the quotient:
\begin{lstlisting}
def FlagAlgebra sigma := FlagVector sigma / ZeroSpace sigma
\end{lstlisting}
We prove that \lean{FlagAlgebra sigma} carries a commutative $\mathbb{R}$-algebra
structure, with product defined by
\begin{lstlisting}
def flagMulWithSize (F1 : FlagWithSize sigma m1) (F2 : FlagWithSize sigma m2)
    (l : N) (h : m1 + m2 - typeSize sigma <= l) : FlagVector sigma :=
  sum G : FlagWithSize sigma l, flagDensity2 F1 F2 G * unitVector G
\end{lstlisting}
and shown to be well-defined on the quotient via the zero-space relations.
The unit element is the class of the type graph $\sigma$ itself.

\subsection{Semantic Ordering via Positive Homomorphisms}

The ordering on \lean{FlagAlgebra sigma} is semantic rather than syntactic.
We define:
\begin{lstlisting}
structure PositiveHom (sigma : FlagType (Fin n0)) where
  toFun  : FlagAlgebra sigma ->a[R] R  -- R-algebra homomorphism
  nonneg : forall F : FinFlag sigma, 0 <= toFun [[unitVector F]]
\end{lstlisting}
The \emph{semantic cone} and its induced ordering are:
\begin{lstlisting}
def semanticCone sigma : Set (FlagAlgebra sigma) :=
  {f | forall phi : PositiveHom sigma, 0 <= phi.toFun f}

instance : Preorder (FlagAlgebra sigma) :=
  { le := fun f g => g - f is in semanticCone sigma, ... }
\end{lstlisting}

The main non-negativity theorem, proved in
\lean{LeanFlagAlgebras.FlagAlgebra.QuadraticForm}, is the Lean~4 counterpart
of Theorem~\ref{thm:sdp-nonneg}:
\begin{lstlisting}
theorem flagQuadraticForm_nonneg
    (M : Matrix (Fin r) (Fin r) R) (hM : M.PosSemidef)
    (v : Fin r -> FlagAlgebra sigma) :
    0 <= [[ sum i j, M i j * (downward (v i * v j)) ]]
\end{lstlisting}
This is the key lemma converting a PSD matrix into an element of the semantic
cone.  Its proof follows from the definition of positive homomorphisms and
the linearity of the downward operator: for any $\phi$,
$\phi\bigl(\llbracket \sum_{ij} M_{ij} v_i v_j \rrbracket\bigr)
= \mathbb{E}_\theta\bigl[\sum_{ij} M_{ij} \phi(v_i^{(\theta)}) \phi(v_j^{(\theta)})\bigr] \geq 0$
since $M$ is PSD and $\phi$ maps each basis vector to a non-negative real.

\subsection{The Forbidden-Subgraph Framework}
\label{sec:forbidden}

\paragraph{Motivation.}
In Razborov's original presentation~\cite{razborov2007flag}, applying the
flag algebra method to $H$-free graphs requires working in a modified theory
that axiomatizes the $H$-freeness condition from the outset.  This
per-problem axiomatization is pragmatically reasonable for a pen-and-paper
proof but is an obstacle to formalization: it would require a separate
verified theory for each forbidden subgraph.

\paragraph{Our approach.}
We instead develop a \emph{general forbidden-subgraph reasoning rule} that
works inside the ambient theory of simple graphs.  The key definition
(in \lean{LeanFlagAlgebras.Forbid.Basic}) is:
\begin{lstlisting}
def forbidLE (H : FinFlag emptyType) (f g : FlagAlgebra sigma) : Prop :=
  forall (phi0 : PositiveHom emptyType), phi0.toFun [[unitVector H]] = 0 ->
    P[phi0] {phi | phi.toFun f <= phi.toFun g} = 1
\end{lstlisting}
The notation $f \leq_{[H]} g$ means: almost surely under the measure
$\mathbb{P}^{\phi_0}$ (the ``random flag extension'' measure induced by any
positive homomorphism $\phi_0$ that assigns zero density to $H$), the typed
homomorphism satisfies $\phi(f) \leq \phi(g)$.

The measure $\mathbb{P}^{\phi_0}$ on typed positive homomorphisms is
constructed in \lean{LeanFlagAlgebras.FlagAlgebra.RandomHom}: the space of
positive homomorphisms for type $\sigma$ is given a compact topology (as a
closed subset of $[0,1]^{|\lean{FinFlag}\ \sigma|}$, which is compact by
Tychonoff's theorem), and $\phi_0$ induces a Borel probability measure on it
via Prokhorov's theorem~\cite{billingsley1999convergence}
(Mathlib: \lean{MeasureTheory.Measure.Prokhorov}).

The transfer theorem is:
\begin{lstlisting}
theorem generalizedTuranDensity_le_of_forbidLE
    (H : FinFlag emptyType) (F : FinFlag emptyType) (c : R) (hc : 0 < c)
    (hineq : forbidLE H (unitVector F) (c * 1)) :
    generalizedTuranDensity H F <= c
\end{lstlisting}
\emph{Argument-order note.}  The Lean constant takes arguments in the order
\emph{forbidden graph first, target graph second}: \lean{generalizedTuranDensity H F}
means the maximum density of $F$ in $H$-free graphs, which the paper
writes as $\tdensity{F}{H}$ in mathematical notation.

This theorem, grounded in the measure-theoretic framework, is sufficiently
general for the present applications: any flag algebra inequality of the
form $f \leq_{[H]} c \cdot \mathbf{1}$ proved in the Lean theory immediately
yields a Turán density upper bound $\tdensity{F}{H} \leq c$, for any
forbidden subgraph $H$ and target pattern $F$.  No additional per-problem
axiomatization is needed.  The framework captures the intended general
pattern, but some auxiliary generalization lemmas in \lean{Forbid/Basic}
relating the quotient-level \lean{forbidLE} predicate to individual flag
representatives remain unfinished; these gaps are described in
\S\ref{sec:intensional} and do not affect the main results.

\paragraph{What Mathlib provides.}
This layer builds on substantial Mathlib infrastructure.  For the algebraic
structure, we use \lean{Mathlib.LinearAlgebra.Finsupp} for free modules and
\lean{Mathlib.LinearAlgebra.Matrix.PosDef} for positive semidefiniteness.
For the measure-theoretic layer, we use
\lean{Mathlib.MeasureTheory.Measure.ProbabilityMeasure},
\lean{Mathlib.Probability.ProductMeasure}, and critically
\lean{Mathlib.MeasureTheory.Measure.Prokhorov} for the compactness argument.
\lean{Mathlib.Combinatorics.SimpleGraph.Subgraph} provides the ambient graph
infrastructure.  What is \emph{not} in Mathlib and was built from scratch:
the \lean{LabeledGraph} structure and flag-isomorphism quotient, the
\lean{FlagAlgebra} quotient module with its ring structure, the \lean{PositiveHom}
type and semantic cone, the \lean{forbidLE} predicate and
\lean{generalizedTuranDensity\_le\_of\_forbidLE} (including the random
extension measure construction in \lean{RandomHom.lean}, $\sim$1\,300 lines).

\paragraph{Key challenge.}
The hardest single component in the abstract layer was \lean{RandomHom.lean}.
Constructing $\mathbb{P}^{\phi_0}$ requires showing that the space of positive
homomorphisms is a compact metric space (so that it admits a Borel probability
measure structure), and that $\phi_0$ determines a tight family of measures
on it (so that Prokhorov's theorem applies).  Compactness follows from the
observation that positive homomorphisms are algebra homomorphisms with
values in $[0,1]$, hence a closed bounded subset of $\mathbb{R}^{|\lean{FinFlag}\ \sigma|}$;
Tychonoff gives compactness.  The measure itself is then the pushforward of the
counting measure on sequences of graphs through the map that sends a graph
sequence to its induced positive homomorphism (when it exists).  Each of these
steps has a precise Mathlib counterpart, but threading them together required
significant care about which topological and measurability assumptions each
lemma required.


\subsection{Type-Theoretic Obstacles from Intensionality}
\label{sec:intensional}

Lean~4 is based on an \emph{intensional} type theory: definitional equality is
decidable but strictly weaker than propositional equality.  Two types that are
provably equal may not be definitionally equal, and the kernel does not
automatically identify them.  This creates three concrete classes of obstacle
in a flag algebra formalization, each requiring its own systematic workaround.

\paragraph{Obstacle 1: Quotient types require explicit eliminators.}
Both \lean{Flag} and \lean{FlagAlgebra} are quotients, so any function
\emph{from} them or equality \emph{in} them must go through
\lean{Quotient.lift} or \lean{Quotient.sound}.  \lean{Quotient.lift} requires
a proof that the function respects the equivalence relation; \lean{Quotient.sound}
requires producing a witness of the relation for each equality goal.

The adequacy theorems in \S\ref{sec:reflection} illustrate the cost.  To state
that \lean{Sym2Graph.toFlag} is inverse to \lean{Flag.toSym2EmptyTypedFlag}, one
cannot write a direct equality between concrete and abstract objects; every step
must go through the quotient eliminators:
\begin{lstlisting}
def Sym2EmptyTypedFlag.toFlag (F : Sym2EmptyTypedFlag n) : Flag emptyType (Fin n) :=
  Quotient.lift Sym2Graph.toFlag Sym2Graph.toFlag_respect_eqv F
\end{lstlisting}
The \lean{toFlag\_respect\_eqv} proof --- showing that isomorphic \lean{Sym2Graph}
values map to the same \lean{Flag} --- is not automatic; it required
\lean{Quotient.sound} applied to a graph isomorphism witness assembled from the
concrete data.  In an extensional type theory, both directions of this round-trip
would hold definitionally.

\paragraph{Obstacle 2: Size-changing operations produce dependent-type mismatches.}
Flag algebra operations change the vertex count of flags: the product of a
size-$m_1$ and a size-$m_2$ flag lives at size $\ell \geq m_1 + m_2 - k$.
In the formalization, the product is computed as a sum over all size-$\ell$ flags:
\begin{lstlisting}
def flagMulWithSize (F1 : FlagWithSize sigma m1) (F2 : FlagWithSize sigma m2)
    (l : N) (h : m1 + m2 - typeSize sigma <= l) : FlagVector sigma :=
  sum G : FlagWithSize sigma l, flagDensity2 F1 F2 G * unitVector G
\end{lstlisting}
To show this is well-defined on the quotient (i.e., independent of $\ell$),
one must relate terms at different sizes --- but \lean{FlagWithSize sigma l}
and \lean{FlagWithSize sigma l'} are definitionally distinct types.

The same issue arises internally when collecting the flags for the multiplication
sum.  A \lean{FlagList sigma t Vl} (a $t$-tuple of flags with type family $Vl$)
changes type when a new flag is inserted: the result has type
\lean{FlagList sigma (t+1) (listTypeInsert Vl W)}.  Because
\lean{listTypeInsert Vl W} is not definitionally equal to any pre-existing type
family, relating the old and new lists requires \emph{heterogeneous equality}
(\lean{HEq}):
\begin{lstlisting}
theorem flagList_HEq
    (h_Vl_eq : Vl' = Vl)
    (h_Fl_eq : forall i, Fl i = cast (Flag.type_eq h_Vl_eq i) (Fl' i))
    : HEq Fl Fl'
\end{lstlisting}
The \lean{cast} calls are explicit coercions through propositional equality proofs;
they are the formalization's acknowledgment that two types are equal only up to a
proof, not up to definition.  In an extensional type theory, type equality would
be reflected into definitional equality, making these casts unnecessary.

Similarly, even if two indices $i$ and $i'$ into a flag list are propositionally
equal ($i = i'$), the types \lean{Flag sigma (Vl i)} and \lean{Flag sigma (Vl i')}
are not definitionally equal, forcing the use of heterogeneous equality:
\begin{lstlisting}
theorem flaglist_heq_of_idx_eq {i i' : Fin t} (h : i = i')
    : HEq (Fl i) (Fl i') := by subst h; rfl
\end{lstlisting}
This pervasive use of \lean{HEq} and \lean{cast} propagates through the entire
density computation infrastructure: every operation that crosses a size boundary
must carry explicit propositional equality evidence.

\paragraph{Obstacle 3: Function extensionality and proof-valued fields.}
In Lean~4's intensional type theory, function extensionality
($(\forall x,\, f\,x = g\,x) \Rightarrow f = g$) is not definitional but is
available as an axiom (\lean{funext}).  This creates friction wherever the
formalization must relate a function-level equality (such as a type embedding)
to a pointwise equality (the embedding's behavior on individual vertices).
For example, constructing a labeled-graph isomorphism from a vertex map $\zeta$
requires reassembling pointwise information back into a function:
\begin{lstlisting}
have h_emb : forall t : T, zeta (G0'.type_embed t) = G1'.type_embed t := ...
let iso : G0'.coe =~f G1'.coe := { ..., type_preserve := funext h_emb }
\end{lstlisting}
Without \lean{funext} as an axiom, the \lean{type\_preserve} field could not
be filled.  Lean~4 accepts \lean{funext} as a consequence of \lean{propext},
so this is not an unsound assumption, but it does mean that every such step is a
propositional proof obligation rather than a definitional reduction.

Proof-valued structure fields create a related difficulty.  The \lean{Sym2Graph}
type carries a field \lean{edges\_valid : forall e in edges, not e.IsDiag}; two
\lean{Sym2Graph} values with the same edge set but different proof terms for
\lean{edges\_valid} are propositionally equal (by proof irrelevance) but not
definitionally equal.  Comparing \lean{Sym2Graph} values in the adequacy
theorems therefore requires the \lean{proof\_irrel\_heq} tactic at every
such field:
\begin{lstlisting}
theorem Sym2Graph.toLabeledGraph.toSym2Graph_eq (G : Sym2Graph n) :
    G.toLabeledGraph.toSym2Graph = G := by
  congr  -- reduces to field equalities
  ...
  · exact proof_irrel_heq _ _  -- edge validity field
\end{lstlisting}

\paragraph{What remains open.}
Not all intensionality obstacles were resolved.  The most significant gap is in
\lean{LeanFlagAlgebras.Forbid.Basic}: two lemmas relating the quotient-level
\lean{forbidLE} predicate to the density of individual flag representatives
were left as comments with \lean{sorry} markers.  Concretely, showing that
$f \leq_{[H]} 0$ implies the density of $H$ in any flag in the support of $f$
is positive requires reasoning about which representatives of a quotient class
can appear under a homomorphism --- a question that reduces to asking how the
zero-space relations interact with the flag representatives pointwise.  This
interaction is nontrivial in an intensional setting because the zero-space
relations hold only propositionally (they are proved as theorems, not built into
the type definition).  These gaps do not affect the soundness of the main
results --- \lean{Mantel\_theorem} and \lean{ErdosPentagon\_Turan} are proved
without them --- but they limit the generality of the \lean{forbidLE} framework
for future applications.

\subsection{Fintype Instance Conflicts}
\label{sec:fintype}

A second class of proof failures --- distinct from propositional-vs-definitional
equality issues but equally pervasive --- arose from Lean~4's treatment of
\lean{Fintype} instances.

\paragraph{Background.}
In Lean~4's typeclass system, a type may satisfy \lean{Fintype} (the type has a
computable enumeration) or the weaker \lean{Finite} (the type is merely
finitely inhabited, non-constructively).  Many Mathlib lemmas about cardinality
(\lean{Fintype.card}, \lean{Finset.card\_univ}, \lean{Fintype.card\_congr})
require \lean{Fintype}, not merely \lean{Finite}.  The elaborator infers
\lean{Fintype} instances automatically, but in a development with multiple
overlapping constructions (quotient types, embedded subgraphs, partial-function
spaces), the same type can receive different \lean{Fintype} instances from
different elaboration paths.  When two instances do not reduce to the same term
definitionally, the kernel rejects the goal even if the instances are provably
equal.

\paragraph{The Finite-vs-Fintype gap.}
Sets defined by set-builder notation $\{x \mid P\ x\}$ have type
\lean{Set T}, which is \lean{Finite} whenever \lean{T} is a \lean{Fintype},
but does not automatically carry a \lean{Fintype} instance.  This was a
recurring obstacle in \lean{SubflagListDensity.lean}: whenever a cardinality
argument compared two finite sets defined by structural conditions on flag lists,
the proof required an explicit conversion:
\begin{lstlisting}
let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
have card_eq : Fintype.card S₀ = Fintype.card S₁ :=
  Fintype.card_congr h_iso_S₀_S₁
\end{lstlisting}
This pattern appears at three independent sites in \lean{SubflagListDensity.lean}
(functions \lean{flagDensity\_eq}, \lean{flagDensity\_permute}, and
\lean{flagDensity\_insert\_empty}).  Without the explicit \lean{let} bindings,
Lean synthesizes a \lean{Fintype} for each set via a different path on each
use, and \lean{Fintype.card\_congr} cannot unify the instances.  The same
\lean{Fintype.ofFinite} fix was needed in \lean{FlagOperators.lean} (for
\lean{isoLabeledGraphSetWithSameGraph}) and in \lean{FlagDef.lean} (for
\lean{LabeledGraph} and \lean{LabeledSubgraph}).

\paragraph{Instance disambiguation for function and embedding types.}
For parameterized types such as injections \lean{V ↪ W} and equivalences
\lean{V ≃ W}, Lean can synthesize \lean{Fintype} instances in multiple ways
depending on which prior instances are in scope.  In
\lean{Compute/Basic.lean}, where \lean{Fintype} instances for these types are
defined, the elaborator had to be given explicit guidance via
\lean{@Finset.univ} with the intended instance passed as a named argument:
\begin{lstlisting}
instance : Fintype (V ↪ W) :=
  { elems := @Finset.univ (V ↪ W) (inferInstance), ... }
\end{lstlisting}
Without the explicit \lean{@}, Lean would sometimes apply a different,
incompatible \lean{Fintype} instance for \lean{V ↪ W} further down the proof,
causing goals of the form \lean{x ∈ Finset.univ} to fail to close by
\lean{Finset.mem\_univ}.

A related issue arose for dependent function types indexed by a small finite
type.  The \lean{FintypeList} typeclass (used internally to manage lists of
typed flags indexed by \lean{Fin t}) must be instantiated by threading through
\lean{Fintype} instances for each component type separately.  For the cases
\lean{Fin 2 → Type} and \lean{Fin 3 → Type} that arise in the density
computation, the instances had to be written with explicit per-case
\lean{inferInstance} calls rather than a uniform typeclass search:
\begin{lstlisting}
instance {V W : Type} [Fintype V] [Fintype W]
    : FintypeList (fun (i : Fin 2) => match i with
        | 0 => V | 1 => W) where
  fintype_all := fun i => match i with
    | 0 => inferInstance | 1 => inferInstance
\end{lstlisting}
Lean's typeclass search does not look through \lean{match} expressions inside
type-valued functions, so the uniform instance \lean{fun i => inferInstance}
fails to elaborate.

\paragraph{Cardinality comparison across paired sets.}
In \lean{FlagDensity.lean}, computing induced subgraph densities requires
converting a set of vertices (of type \lean{Set (Fin n)}) to a \lean{Finset}
for cardinality comparisons.  The standard conversion
\lean{Set.toFinset} requires a \lean{Fintype} instance for the set, which is
not automatically synthesized when the set is defined as the vertex set of a
subgraph:
\begin{lstlisting}
verts := @Set.toFinset _ (Hl i).subgraph.verts (Fintype.ofFinite _)
\end{lstlisting}
The explicit \lean{Fintype.ofFinite \_} argument prevents the elaborator from
picking up an incompatible instance from a \lean{DecidablePred} path.
Similarly, when two goals differ only in which \lean{Fintype} instance was
used to compute a \lean{Finset}, the \lean{convert} tactic was used to accept
the goal up to a \lean{Fintype} proof obligation that \lean{Subsingleton}
then closed:
\begin{lstlisting}
convert h_adj   -- goal matches up to Fintype instance
\end{lstlisting}

\paragraph{Lesson.}
The root cause in all three cases is the same: Lean~4's typeclass system is
\emph{globally coherent by convention}, not by enforcement.  When a type has
a unique \lean{Fintype} instance (e.g., \lean{Fin n}), there is no conflict.
When a type's \lean{Fintype} instance is assembled from multiple subinstances
(e.g., a function type, a quotient, or a set defined by a predicate), the
elaborator can take different paths, and the resulting terms are not
definitionally equal even if they enumerate the same elements.  The fix in
every case was the same: make the intended instance explicit at the point of
synthesis, either by a \lean{let} binding with a type annotation, by passing
the instance as an explicit argument to \lean{@Finset.univ} or
\lean{@Set.toFinset}, or by writing the instance by hand when the uniform
typeclass search fails.  These are low-level engineering burdens that do not
appear in pen-and-paper mathematics, but are unavoidable in a large-scale
Lean~4 development that crosses quotient and reflection boundaries.
---END REFERENCE DRAFT---

Revise to remove unsupported claims and strengthen evidence alignment.
If the prose is shallow, expand it to match exemplar-paper depth while staying evidence-grounded.
Hard gate: reject output if Section Blueprint constraints are not satisfied.
For equation-heavy sections, verify formulas and notation are consistent with the listed Equation Source PDFs.
Return only final LaTeX section body without markdown fences and without \section{...}.
Save output as verifier_output.md.
