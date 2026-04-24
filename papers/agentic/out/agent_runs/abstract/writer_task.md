# Writer Task

Project: Formalizing Flag Algebra in Lean
Target Section: Abstract

Depth Target:
- 1 compact paragraph (5-8 sentences) with problem, method, contributions, and application outcome.

Section Blueprint (Hard Constraints):
- (no section blueprint configured)

Equation Source PDFs (for mathematical formulas):
- papers/References/Razborov07.pdf
- papers/References/GrzesikThesis14.pdf

Exemplar Formalization Papers (quality bar):
- papers/References/Formalization/A complete formalization of Fermat's Last Theorem for regular primes in Lean.pdf
- papers/References/Formalization/A formalization of Borel determinacy in Lean.pdf
- papers/References/Formalization/Derandomization with Pseudorandomness.pdf
- papers/References/Formalization/Duality theory in linear optimization and its extensions -- formally verified.pdf
- papers/References/Formalization/Formalising the Bruhat-Tits Tree.pdf
- papers/References/Formalization/Formalising the local compactness of the adele ring.pdf
- papers/References/Formalization/Formalization of derived categories in Lean&mathlib.pdf
- papers/References/Formalization/Formalizing zeta and L-functions in Lean.pdf

Quality Requirements:
- Write section bodies with publication-grade depth, not short summaries.
- Use explicit motivation -> method -> formalization detail -> implication flow.
- Explain design choices and trade-offs, not only what was implemented.
- Keep claims tightly grounded in evidence and avoid generic hype language.
- Ensure each section can stand alone for a mathematical reader unfamiliar with the codebase.

Mandatory Considerations:
# Paper Writing Considerations

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

이 파일에는 에이전트가 참고해야 하는 프로젝트별 메모를 적습니다.
예: 타깃 저널 톤, 강조할 기여, 피하고 싶은 표현, 꼭 넣어야 할 그림/표.

## Example Template
- Target venue:
- Preferred tone:
- Must-highlight contributions:
- Claims to avoid unless quantified:
- Terminology decisions:
- Open technical caveats:

주의: 이 파일은 자유 메모입니다. 강제 제약은 considerations.md에 작성하세요.

## Project-Specific Notes
- 논문 본문에 Section "Formalization of Flag Algebra"를 추가했다. 관련 설명은 이 섹션을 기준으로 우선 배치한다.
- 현재 목차 구조는 초안이며 고정 규칙이 아니다. 필요하면 섹션/소절을 분할, 통합, 재정렬, 리네이밍해도 된다.
- 단, 구조를 조정할 때는 변경 이유를 1~3문장으로 설명하고, Abstract/Introduction/Conclusion의 핵심 기여 서술과 충돌하지 않게 유지한다.
- Background 작성 시 우선 참고 소스:
	- papers/References/Razborov07.pdf
	- papers/References/GrzesikThesis14.pdf
	- papers/BEATCS_Collumn26/paper.tex
- Background 문단은 위 3개 문헌의 문제 맥락, 핵심 정의 관점, 기존 접근의 한계/차이를 먼저 정리한 뒤, 현재 Lean 형식화와 연결한다.
- Background에서는 코드 세부 구현보다 개념적 흐름과 문헌 대비 기여를 우선한다.


Global Instructions:
- The current paper structure is a helpful draft, not a hard constraint.
- If clarity improves, you may split, merge, reorder, or rename sections/subsections while preserving technical correctness.
- When proposing structural changes, include a brief rationale and maintain consistency with abstract/introduction/conclusion claims.

Section-Specific Instructions:
- (none)

Read planner_output.json and retriever_output.json first.

Selected evidence:
1. [text] line @ papers/paper.tex:23 :: \title{Formalizing Flag Algebra in Lean}
2. [text] line @ papers/paper.tex:49 :: \item We formalize Alexander Razborov’s flag algebra for graphs in Lean 4.
3. [text] line @ papers/paper.tex:50 :: \item We define a computable version of flags so that computations of flag algebra operations can be verified within Lean.
4. [text] line @ papers/paper.tex:52 :: \item We formally verify the flag algebra proof of the Erdős pentagon problem using our framework.
5. [text] line @ papers/paper.tex:55 :: \section{Background on Flag Algebra}
6. [text] line @ papers/paper.tex:60 :: A \emph{type} of size $k$ is a graph $\sigma$ with $V(\sigma)=[k]$. For a graph $G$, an \emph{embedding} of $\sigma$ into $G$ is an injective map $\theta : [k] \to V(G)$ such that $\sigma$ is isomorphic to the induced subgraph $G[\operatorname{Im}\theta]$. A \emph{$\sigma$-flag} is a pair $G^{\sigma}=(G,\theta)$ consisting of a graph $G$ and an embedding $\theta$ of $\sigma$ into $G$. For $G^{\sigma}=(G,\theta)$, we define $V(G^{\sigma}) \coloneqq V(G)$, $E(G^{\sigma}) \coloneqq E(G)$, $v(G^{\sigma}) \coloneqq v(G)$, and $e(G^{\sigma}) \coloneqq e(G)$. We call $v(G^{\sigma})$ the \emph{size} of $G^{\sigma}$.
7. [text] line @ papers/paper.tex:62 :: We say that two $\sigma$-flags $G^{\sigma}_1=(G_1,\theta_1)$ and $G^{\sigma}_2=(G_2,\theta_2)$ are \emph{isomorphic}, denoted $G^{\sigma}_1 \simeq G^{\sigma}_2$, if there exists a graph isomorphism $f : V(G_1) \to V(G_2)$ such that $f \circ \theta_1 = \theta_2$. For $n \ge v(\sigma)$, let $\mathcal{F}_n^{\sigma}$ denote the set of all $\sigma$-flags of size $n$ up to isomorphism, and let $\mathcal{F}^{\sigma}$ denote the set of all $\sigma$-flags up to isomorphism.
8. [text] line @ papers/paper.tex:64 :: \subsection{Subflag Density}
9. [text] line @ papers/paper.tex:66 :: Fix a type $\sigma$ of size $k$. Let $G^{\sigma}$, $F^{\sigma}_1$, ..., $F^{\sigma}_t$ be $\sigma$-flags such that
10. [text] line @ papers/paper.tex:71 :: \subsection{Flag Algebra}
11. [text] line @ papers/paper.tex:75 :: \section{Formalization of Flag Algebra}
12. [text] line @ papers/paper.tex:77 :: \section{Computable Definition of Flags}
13. [text] line @ papers/paper.tex:81 :: \subsection{Mantel's Theorem}
14. [text] line @ papers/paper.tex:83 :: \subsection{Erdős Pentagon Problem}
15. [text] line @ papers/paper.tex:102 :: \item \textbf{Section 1 \& 2 (Background \& Math):} Introduces the mathematical context and provides pen-and-paper proof sketches before introducing code.
16. [text] line @ papers/paper.tex:110 :: \item \textbf{Structure by Abstraction:} Presenting mathematical proof sketches before technical code significantly reduces reader fatigue.
17. [text] line @ papers/paper.tex:128 :: \item \textbf{Section 3 (Mathematical Background):} Provides informal, pen-and-paper proof sketches for the LYM inequalities, Kruskal-Katona, and Erd\H{o}s-Ko-Rado theorems to ground the reader.
18. [text] line @ papers/paper.tex:129 :: \item \textbf{Section 4 (Formalizing the Shadow):} Details the Lean definitions for set families and shadows, followed by the formal proofs of the local and general LYM inequalities.
19. [text] line @ papers/paper.tex:139 :: \item \textbf{Adapt Mathematical Proofs:} Demonstrate how traditional textbook proofs (like double-counting on pairs) are translated into structures better suited for the prover, such as forming two exact sets and demonstrating subset relations.
20. [text] line @ papers/paper.tex:153 :: \item \textbf{Sections 1 \& 2 (Background \& Overview):} Introduces the history of the Erd\H{o}s-Szekeres problem and the overall pipeline of the SAT-based proof.
21. [text] line @ papers/paper.tex:155 :: \item \textbf{Sections 5 \& 6 (Symmetry Breaking \& SAT Encoding):} Explains the search space reduction techniques via canonical position transformations, the construction of the CNF formula, and the actual execution results of the SAT solver and proof checker (\texttt{cake\_lpr}).
22. [text] line @ papers/paper.tex:164 :: \item \textbf{Modular Trust Story:} For proofs requiring massive computation, it is crucial to clearly explain the "trust structure"—detailing how the theorem prover (Lean), high-performance solver (CaDiCaL), and external checker (\texttt{cake\_lpr}) are separated and integrated so that the entire pipeline operates without logical flaws.

Write only LaTeX body for section: Abstract.
Write publication-grade prose with explicit transitions, motivation, and technical substance.
Hard gate: satisfy all Section Blueprint constraints (subsections, equations, code references where required).
For mathematical formulas, derive and align notation from the listed Equation Source PDFs.
Do not include \section{...}.
Save output as writer_output.md.
