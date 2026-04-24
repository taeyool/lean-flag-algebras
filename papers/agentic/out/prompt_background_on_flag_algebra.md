# Agent Task: Draft Section

Project: Formalizing Flag Algebra in Lean
Target Section: Background on Flag Algebra
Target TeX: papers/agentic/out/paper_draft_from_contributions.tex

## Mandatory Considerations
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


## Author Notes
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


## Global Instructions
- The current paper structure is a helpful draft, not a hard constraint.
- If clarity improves, you may split, merge, reorder, or rename sections/subsections while preserving technical correctness.
- When proposing structural changes, include a brief rationale and maintain consistency with abstract/introduction/conclusion claims.

## Section-Specific Instructions
- When drafting this section, prioritize conceptual grounding from papers/References/Razborov07.pdf, papers/References/GrzesikThesis14.pdf, and papers/BEATCS_Collumn26/paper.tex.
- Explain definitions and motivation in a way suitable for a broad mathematical audience, then connect to this repository's Lean formalization.
- Do not claim details from external papers unless they are actually checked from those sources.

## Retrieved Evidence
- [def] Fin.coe @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:5 :: def Fin.coe {t : ℕ} (i : Fin (t + 1)) (hi : i.val ≠ t) : Fin t
- [structure] LabeledGraph @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:20 :: structure LabeledGraph (σ : FlagType T) (V : Type) where
- [def] LabeledGraph.type_verts @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:24 :: def LabeledGraph.type_verts (G : LabeledGraph σ V) : Set V :=
- [lemma] LabeledGraph.mem_type_verts @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:28 :: lemma LabeledGraph.mem_type_verts {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} {v : V} :
- [lemma] LabeledGraph.type_verts_card_eq @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:36 :: lemma LabeledGraph.type_verts_card_eq {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
- [lemma] LabeledGraph.type_verts_contain @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:43 :: lemma LabeledGraph.type_verts_contain {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (t : T)
- [lemma] iso_type_G_eq_type_embed @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:69 :: lemma iso_type_G_eq_type_embed
- [lemma] LabeledGraph.type_size_le_size @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:92 :: lemma LabeledGraph.type_size_le_size {σ : FlagType T} {V : Type} [Fintype V] (G : LabeledGraph σ V)
- [theorem] type_embed_Adj_iff @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:99 :: theorem type_embed_Adj_iff
- [theorem] iso_type_Adj_iff @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:106 :: theorem iso_type_Adj_iff
- [def] emptyLabeledGraph @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:117 :: def emptyLabeledGraph (σ : FlagType T) : LabeledGraph σ T
- [structure] LabeledSubgraph @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:122 :: structure LabeledSubgraph (σ : FlagType T) {V : Type} (G : LabeledGraph σ V) where
- [def] LabeledGraph.top @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:127 :: def LabeledGraph.top (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
- [lemma] LabeledGraph.top_isInduced @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:146 :: lemma LabeledGraph.top_isInduced (G : LabeledGraph σ V)
- [def] LabeledGraph.bottom @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:149 :: def LabeledGraph.bottom (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
- [lemma] LabeledGraph.bottom_isInduced @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:172 :: lemma LabeledGraph.bottom_isInduced (G : LabeledGraph σ V)
- [def] IsInduced @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:177 :: def IsInduced {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : Prop
- [def] coe @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:188 :: def coe {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G)
- [theorem] coe_adj_iff @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:194 :: theorem coe_adj_iff
- [lemma] coe_type_verts_eq @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:201 :: lemma coe_type_verts_eq
- [theorem] labeledSubgraph_contain_type_verts @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:222 :: theorem labeledSubgraph_contain_type_verts
- [def] inducedLabeledSubgraph @ LeanFlagAlgebras/FlagAlgebra/FlagDef.lean:230 :: def inducedLabeledSubgraph
- [def] relOfLabeledSubgraph @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:30 :: def relOfLabeledSubgraph
- [lemma] relOfLabeledSubgraph_symm @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:37 :: lemma relOfLabeledSubgraph_symm
- [def] relOfPredOnLabeledSubgraph @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:57 :: def relOfPredOnLabeledSubgraph
- [def] predIsoLabeledH @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:64 :: def predIsoLabeledH
- [lemma] predIsoLabeledH_related_support @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:70 :: lemma predIsoLabeledH_related_support
- [lemma] predIsoLabeledH_related @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:110 :: lemma predIsoLabeledH_related
- [lemma] predIsoLabeledH_related_ind @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:121 :: lemma predIsoLabeledH_related_ind
- [def] inducedLabeledSubgraphByIso @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:136 :: def inducedLabeledSubgraphByIso
- [lemma] inducedLabeledSubgraphByIso_isInduced @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:145 :: lemma inducedLabeledSubgraphByIso_isInduced
- [lemma] inducedLabeledSubgraph_related @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:156 :: lemma inducedLabeledSubgraph_related
- [theorem] embed_heq_of_subgraph_eq @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:164 :: theorem embed_heq_of_subgraph_eq
- [theorem] type_embed_heq_of_subgraph_eq @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:176 :: theorem type_embed_heq_of_subgraph_eq
- [lemma] labeledSubgraph_eq_from_subgraph_eq @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:187 :: lemma labeledSubgraph_eq_from_subgraph_eq
- [lemma] H_eq_reverseinduced_induced_H @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:194 :: lemma H_eq_reverseinduced_induced_H
- [def] isoSetOfInducedLabeledSubgraph @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:210 :: def isoSetOfInducedLabeledSubgraph
- [def] isoSetOfInducedLabeledSubgraphFromIsoGH @ LeanFlagAlgebras/FlagAlgebra/SubflagDensity.lean:240 :: def isoSetOfInducedLabeledSubgraphFromIsoGH
- [def] LabeledSubgraphList.IsInduced @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:38 :: def LabeledSubgraphList.IsInduced
- [def] predDisjointLabeledSubgraphList @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:42 :: def predDisjointLabeledSubgraphList
- [def] predIsoLabeledHl @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:47 :: def predIsoLabeledHl
- [def] setOfLabeledSubgraphListIsoHl @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:54 :: def setOfLabeledSubgraphListIsoHl (G : LabeledGraph σ U) (Hl : LabeledGraphList σ t Vl)
- [def] relOfLabeledSubgraphList @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:72 :: def relOfLabeledSubgraphList
- [lemma] relOfLabeledSubgraphList_symm @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:80 :: lemma relOfLabeledSubgraphList_symm
- [lemma] relOfLabeledSubgraphList_indep @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:90 :: lemma relOfLabeledSubgraphList_indep
- [def] relOfPredOnLabeledSubgraphList @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:112 :: def relOfPredOnLabeledSubgraphList
- [lemma] predIsoLabeledHl_related @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:124 :: lemma predIsoLabeledHl_related
- [def] inducedLabeledSubgraphList @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:149 :: def inducedLabeledSubgraphList
- [lemma] inducedLabeledSubgraphList_isInduced @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:155 :: lemma inducedLabeledSubgraphList_isInduced
- [def] inducedLabeledSubgraphListByIso @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:160 :: def inducedLabeledSubgraphListByIso
- [lemma] inducedLabeledSubgraphListByIso_isInduced @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:170 :: lemma inducedLabeledSubgraphListByIso_isInduced
- [lemma] inducedLabeledSubgraphList_related @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:180 :: lemma inducedLabeledSubgraphList_related
- [lemma] Hl_eq_reverseinduced_induced_Hl @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:192 :: lemma Hl_eq_reverseinduced_induced_Hl
- [def] isoSetOfInducedLabeledSubgraphList @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:200 :: def isoSetOfInducedLabeledSubgraphList
- [lemma] labeledSubgraphListDensity_respect_eqv @ LeanFlagAlgebras/FlagAlgebra/SubflagListDensity.lean:249 :: lemma labeledSubgraphListDensity_respect_eqv
- [text] line @ papers/BEATCS_Collumn26/paper.tex:224 :: \title{An Introduction to Razborov's Flag Algebra as a Proof System for Extremal Graph Theory}
- [text] line @ papers/BEATCS_Collumn26/paper.tex:243 :: Razborov's flag algebra forms a powerful framework for deriving asymptotic inequalities between induced subgraph densities, underpinning many advances in extremal graph theory. This survey introduces flag algebra to computer scientists working in logic, programming languages, automated verification, and formal methods. We take a logical perspective on flag algebra and present it in terms of syntax, semantics, and proof strategies, in a style closer to formal logic. One popular proof strategy derives valid inequalities by first proving inequalities in a labelled variant of flag algebra and then transferring them to the original unlabelled setting using the so-called downward operator. We explain this strategy in detail and highlight that its transfer mechanism relies on the notion of what we call an adjoint pair, reminiscent of Galois connections and categorical adjunctions, which appear frequently in work on automated verification and programming languages. Along the way, we work through representative examples, including Mantel's theorem and Goodman's bound on Ramsey multiplicity, to illustrate how mathematical arguments can be carried out symbolically in the flag algebra framework.
- [text] line @ papers/BEATCS_Collumn26/paper.tex:248 :: Razborov's flag algebra~\cite{Razborov2007} is a framework for reasoning about
- [text] line @ papers/BEATCS_Collumn26/paper.tex:250 :: In extremal graph theory, many problems ask for the maximum or minimum possible density

## Instructions
1. Write one coherent section draft in academic style.
2. Do not invent theorem names or file paths.
3. Ensure each nontrivial claim is grounded in Retrieved Evidence.
4. Respect Mandatory Considerations first, then adapt wording to Author Notes.
5. You may adjust section structure if it improves clarity, but explain the change briefly.
6. End with a short 'Evidence Coverage' list mapping key claims to evidence lines.
