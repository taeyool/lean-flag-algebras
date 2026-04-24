# Agent Task: Draft Section

Project: Formalizing Flag Algebra in Lean
Target Section: Computable Definition of Flags
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
- (No section-specific instructions configured.)

## Retrieved Evidence
- [structure] EmptyTypedJsonData @ LeanFlagAlgebras/Flags/FlagLoader.lean:8 :: structure EmptyTypedJsonData where
- [structure] FlagEntry @ LeanFlagAlgebras/Flags/FlagLoader.lean:12 :: structure FlagEntry where
- [structure] FlagJsonData @ LeanFlagAlgebras/Flags/FlagLoader.lean:20 :: structure FlagJsonData where
- [def] jsonNumberToNat @ LeanFlagAlgebras/Flags/FlagLoader.lean:27 :: def jsonNumberToNat? (x : JsonNumber) : Option Nat :=
- [def] mkEdgeFinset @ LeanFlagAlgebras/Flags/FlagLoader.lean:33 :: def mkEdgeFinset (n : ℕ) (l : List (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
- [def] jsonEdgesToTerm @ LeanFlagAlgebras/Flags/FlagLoader.lean:36 :: def jsonEdgesToTerm (numVerts : ℕ) (edgesJson : Json) : CommandElabM (TSyntax `term) := do
- [def] parseNFromGraphsPath @ LeanFlagAlgebras/Flags/FlagLoader.lean:45 :: def parseNFromGraphsPath (path : System.FilePath) : CommandElabM Nat := do
- [def] parseCoeffString @ LeanFlagAlgebras/Flags/FlagLoader.lean:56 :: def parseCoeffString (s : String) : CommandElabM (Nat × Nat) := do
- [def] parseTypeIndices @ LeanFlagAlgebras/Flags/FlagLoader.lean:76 :: def parseTypeIndices (j : Json) : CommandElabM (Array Nat) := do
- [def] mkTypeIndexNatExpr @ LeanFlagAlgebras/Flags/FlagLoader.lean:89 :: def mkTypeIndexNatExpr (typeIndices : Array Nat) : CommandElabM (TSyntax `term) := do
- [def] parseEmptyTypedJsonFile @ LeanFlagAlgebras/Flags/FlagLoader.lean:99 :: def parseEmptyTypedJsonFile (path : System.FilePath) : CommandElabM EmptyTypedJsonData := do
- [def] parseFlagJsonFile @ LeanFlagAlgebras/Flags/FlagLoader.lean:108 :: def parseFlagJsonFile (path : System.FilePath) : CommandElabM FlagJsonData := do
- [def] coeffQTerm @ LeanFlagAlgebras/Flags/FlagLoader.lean:196 :: def coeffQTerm (num den : Nat) : CommandElabM (TSyntax `term) := do
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:89 :: def generate_flag_json(n: int, k: int, type_num: int) -> Dict:
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:95 :: flags_dir = base_dir / "Flags"
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:96 :: flags_dir.mkdir(parents=True, exist_ok=True)
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:121 :: flags: List[Dict] = []
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:140 :: flags.append(
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:151 :: flags.sort(key=lambda x: (x["underlying_graph_num"], x["type_indices"]))
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:158 :: "flags": flags,
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:164 :: description="Generate enriched flag JSON from Graphs/graphs_k.json and Graphs/graphs_n.json"
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:171 :: output = generate_flag_json(args.n, args.k, args.type_num)
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:173 :: out_path = Path(__file__).resolve().parent / "Flags" / f"flags_{args.n}_{args.k}_{args.type_num}.json"
- [text] line @ LeanFlagAlgebras/Flags/generate_flags.py:177 :: print(f"Saved {len(output['flags'])} flags to {out_path}")
- [text] line @ LeanFlagAlgebras/Flags/generate_graphs.py:71 :: filename=f"LeanFlagAlgebras/Flags/Graphs/graphs_{n}.json"
- [structure] Sym2Graph @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:82 :: structure Sym2Graph (n : ℕ) where
- [def] Sym2Graph.toLabeledGraph @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:86 :: def Sym2Graph.toLabeledGraph
- [theorem] Sym2Graph.toLabeledGraph_injective @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:91 :: theorem Sym2Graph.toLabeledGraph_injective
- [theorem] Sym2Graph.toLabeledGraph_adj_iff @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:115 :: theorem Sym2Graph.toLabeledGraph_adj_iff
- [theorem] _root_.FlagAlgebras.LabeledGraph.toSym2Graph_toLabeledGraph_eq @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:153 :: theorem _root_.FlagAlgebras.LabeledGraph.toSym2Graph_toLabeledGraph_eq
- [theorem] Sym2Graph.toLabeledGraph_toSym2Graph_eq @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:165 :: theorem Sym2Graph.toLabeledGraph_toSym2Graph_eq
- [def] Sym2GraphEqv @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:177 :: def Sym2GraphEqv {n : ℕ} (G G' : Sym2Graph n) : Prop :=
- [theorem] sym2Graph_card_edges_eq_of_eqv @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:189 :: theorem sym2Graph_card_edges_eq_of_eqv
- [theorem] Sym2GraphEqv.refl @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:221 :: theorem Sym2GraphEqv.refl (G : Sym2Graph n) : G ∼sf G :=
- [theorem] Sym2GraphEqv.symm @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:224 :: theorem Sym2GraphEqv.symm {G G' : Sym2Graph n} (h : G ∼sf G') : G' ∼sf G :=
- [theorem] Sym2GraphEqv.trans @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:227 :: theorem Sym2GraphEqv.trans {G G' G'' : Sym2Graph n} (h₁ : G ∼sf G') (h₂ : G' ∼sf G'') : G ∼sf G'' :=
- [def] Sym2EmptyTypedFlag @ LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean:238 :: def Sym2EmptyTypedFlag (n : ℕ) : Type :=
- [def] sym2GraphToList @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:13 :: def sym2GraphToList
- [def] sym2GraphPairToList @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:18 :: def sym2GraphPairToList
- [def] Sym2GraphList.toLabeledGraphList @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:24 :: def Sym2GraphList.toLabeledGraphList
- [structure] Sym2InducedSubgraph @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:31 :: structure Sym2InducedSubgraph
- [def] Sym2InducedSubgraph.edges @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:49 :: def Sym2InducedSubgraph.edges
- [theorem] Sym2InducedSubgraph.edges_valid @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:54 :: theorem Sym2InducedSubgraph.edges_valid
- [theorem] Sym2InducedSubgraph.edges_subset @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:62 :: theorem Sym2InducedSubgraph.edges_subset
- [def] Sym2InducedSubgraph.toLabeledSubraph @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:70 :: def Sym2InducedSubgraph.toLabeledSubraph
- [theorem] Sym2InducedSubgraph.toLabeledSubraph_isInduced @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:93 :: theorem Sym2InducedSubgraph.toLabeledSubraph_isInduced
- [def] predDisjointSym2InducedSubgraphList @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:105 :: def predDisjointSym2InducedSubgraphList
- [def] predIsoSym2Hl @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:110 :: def predIsoSym2Hl
- [def] finsetOfSym2InducedSubgraphListIsoHl @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:145 :: def finsetOfSym2InducedSubgraphListIsoHl
- [def] sym2InducedSubgraphListCount @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:151 :: def sym2InducedSubgraphListCount
- [lemma] induced_subgraph_adj_iff @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:157 :: lemma induced_subgraph_adj_iff
- [lemma] subgraph_not_adj @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:166 :: lemma subgraph_not_adj
- [theorem] labeledSubgraphListCount_eq_sym2InducedSubgraphListCount @ LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean:175 :: theorem labeledSubgraphListCount_eq_sym2InducedSubgraphListCount

## Instructions
1. Write one coherent section draft in academic style.
2. Do not invent theorem names or file paths.
3. Ensure each nontrivial claim is grounded in Retrieved Evidence.
4. Respect Mandatory Considerations first, then adapt wording to Author Notes.
5. You may adjust section structure if it improves clarity, but explain the change briefly.
6. End with a short 'Evidence Coverage' list mapping key claims to evidence lines.
