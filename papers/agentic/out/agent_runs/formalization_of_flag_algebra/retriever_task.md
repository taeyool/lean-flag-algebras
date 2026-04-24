# Retriever Task

Project: Formalizing Flag Algebra in Lean
Target Section: Formalization of Flag Algebra

Depth Target:
- 3-5 substantial paragraphs with clear logical flow, not a short overview.

Section Blueprint (Hard Constraints):
- min_subsections: 3
- min_paragraphs: 7
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
- Describe the formal architecture of the Lean development (core definitions, algebraic operators, logic layer, and tactics) before implementation details.
- Clarify which components encode mathematical semantics and which components exist for computability/automation.
- Use concrete file-level evidence when stating what was formalized.

Read planner_output.json first, then select evidence IDs.

Candidate evidence list:
1. [def] FinFlag @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:63 :: def FinFlag (σ : FlagType (Fin n₀)) : Type
2. [theorem] finFlag_one_fst @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:73 :: theorem finFlag_one_fst
3. [theorem] finFlag_one_snd @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:77 :: theorem finFlag_one_snd
4. [theorem] flagDensity_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:81 :: theorem flagDensity_one
5. [theorem] flagPairDensity_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:88 :: theorem flagPairDensity_one
6. [theorem] finFlag_size_ge_n @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:94 :: theorem finFlag_size_ge_n₀
7. [lemma] rat_smul_eq_real_smul @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:109 :: lemma rat_smul_eq_real_smul
8. [theorem] unitVector_apply_self @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:132 :: theorem unitVector_apply_self
9. [theorem] unitVector_support @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:139 :: theorem unitVector_support
10. [theorem] unitVector_apply_other @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:146 :: theorem unitVector_apply_other
11. [theorem] unitVector_apply_other_size @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:152 :: theorem unitVector_apply_other_size
12. [theorem] flagVector_eq_sum_unitVector @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:159 :: theorem flagVector_eq_sum_unitVector
13. [theorem] flagVector_one_support @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:173 :: theorem flagVector_one_support
14. [theorem] flagVector_one_apply_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:180 :: theorem flagVector_one_apply_one
15. [theorem] flagMulWithSize_comm @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:192 :: theorem flagMulWithSize_comm
16. [theorem] flagMulWithSize_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:200 :: theorem flagMulWithSize_one
17. [theorem] flagMul_comm @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:224 :: theorem flagMul_comm
18. [theorem] flagMul_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:229 :: theorem flagMul_one
19. [theorem] flagVector_mul_eq_nested_sum @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:239 :: theorem flagVector_mul_eq_nested_sum
20. [theorem] flagVector_mul_comm @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:244 :: theorem flagVector_mul_comm
21. [def] emptyType @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:14 :: def emptyType : FlagType (Fin 0) := SimpleGraph.emptyGraph (Fin 0)
22. [theorem] emptyType_size @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:19 :: theorem emptyType_size : ∅ₜ.size = 0 := by
23. [def] isoLabeledGraphSetWithSameGraph @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:23 :: def isoLabeledGraphSetWithSameGraph
24. [def] funBetweenIsoLabeledGraphSetWithSameGraph @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:43 :: def funBetweenIsoLabeledGraphSetWithSameGraph
25. [lemma] comp_funBetweenIsoLabeledGraphSetWithSameGraph @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:98 :: lemma comp_funBetweenIsoLabeledGraphSetWithSameGraph
26. [def] isoSetOfIsoLabeledGraphWithSameGraph @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:115 :: def isoSetOfIsoLabeledGraphWithSameGraph
27. [lemma] isomorphismCount_respect_eqv @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:123 :: lemma isomorphismCount_respect_eqv
28. [lemma] downwardNormalizingFactor_labeledGraph_respect_eqv @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:130 :: lemma downwardNormalizingFactor_labeledGraph_respect_eqv
29. [theorem] downwardNormalizingFactor_pos @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:144 :: theorem downwardNormalizingFactor_pos
30. [theorem] downwardNormalizingFactor_nonneg @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:163 :: theorem downwardNormalizingFactor_nonneg
31. [theorem] downwardNormalizingFactor_emptyFlag_pos @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:169 :: theorem downwardNormalizingFactor_emptyFlag_pos
32. [def] unlabeledGraph @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:182 :: def unlabeledGraph {V : Type} (G : LabeledGraph σ V) : LabeledGraph ∅ₜ V where
33. [theorem] unlabeledGraph_iso @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:186 :: theorem unlabeledGraph_iso
34. [def] unlabeledGraphQuot @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:197 :: def unlabeledGraphQuot {V : Type} (G : LabeledGraph σ V) : Flag ∅ₜ V :=
35. [theorem] unlabeledGraphQuot_respect_eqv @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:200 :: theorem unlabeledGraphQuot_respect_eqv
36. [theorem] unlabel_eq_iff_unlabeledGraph_eqv @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:213 :: theorem unlabel_eq_iff_unlabeledGraph_eqv
37. [lemma] downwardFlagVector_zero @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:231 :: lemma downwardFlagVector_zero
38. [lemma] downwardFlagVector_unitVector @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:236 :: lemma downwardFlagVector_unitVector
39. [lemma] downwardFlagVector_add @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:242 :: lemma downwardFlagVector_add
40. [lemma] downwardFlagVector_sum @ LeanFlagAlgebras/FlagAlgebra/FlagOperators.lean:248 :: lemma downwardFlagVector_sum
41. [def] PositiveHom @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:14 :: def PositiveHom (σ : FlagType (Fin n₀)) : Type
42. [theorem] ext @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:27 :: theorem ext {φ₁ φ₂ : PositiveHom σ} (h : ∀ f : FlagAlgebra σ, φ₁ f = φ₂ f) : φ₁ = φ₂
43. [theorem] map_zero @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:35 :: theorem map_zero (φ : PositiveHom σ) : φ 0 = 0
44. [theorem] map_one @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:40 :: theorem map_one (φ : PositiveHom σ) : φ 1 = 1
45. [theorem] map_add @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:44 :: theorem map_add (φ : PositiveHom σ) (f g : FlagAlgebra σ) : φ (f + g) = φ f + φ g
46. [theorem] map_sub @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:48 :: theorem map_sub (φ : PositiveHom σ) (f g : FlagAlgebra σ) : φ (f - g) = φ f - φ g
47. [theorem] map_smul @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:52 :: theorem map_smul (φ : PositiveHom σ) (r : ℝ) (f : FlagAlgebra σ) : φ (r • f) = r * φ f
48. [theorem] map_mul @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:59 :: theorem map_mul (φ : PositiveHom σ) (f g : FlagAlgebra σ) : φ (f * g) = φ f * φ g
49. [theorem] map_sum @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:63 :: theorem map_sum (φ : PositiveHom σ) {ι : Type} (s : Finset ι) (f : ι → FlagAlgebra σ)
50. [theorem] positiveHom_unitVector_ge_zero @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:70 :: theorem positiveHom_unitVector_ge_zero
51. [theorem] sum_positiveHom_unitVector_flagWithSize_eq_one @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:76 :: theorem sum_positiveHom_unitVector_flagWithSize_eq_one
52. [theorem] positiveHom_unitVector_le_one @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:82 :: theorem positiveHom_unitVector_le_one
53. [theorem] positiveHom_unitVector_eq_zero @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:97 :: theorem positiveHom_unitVector_eq_zero
54. [def] semanticCone @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:119 :: def semanticCone (σ : FlagType (Fin n₀)) : Set (FlagAlgebra σ) :=
55. [theorem] le_def @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:126 :: theorem le_def (f g : FlagAlgebra σ) : f ≤ g ↔ g - f ∈ semanticCone σ :=
56. [theorem] flag_sub_nonneg @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:129 :: theorem flag_sub_nonneg
57. [theorem] flag_geq_zero @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:149 :: theorem flag_geq_zero
58. [theorem] flag_add_le_add @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:157 :: theorem flag_add_le_add
59. [theorem] flag_add_le_add_left @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:168 :: theorem flag_add_le_add_left
60. [theorem] flag_add_le_add_right @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:174 :: theorem flag_add_le_add_right
61. [theorem] nonneg_smul_nonneg_geq_zero @ LeanFlagAlgebras/FlagAlgebra/PositiveHom.lean:186 :: theorem nonneg_smul_nonneg_geq_zero
62. [theorem] flagQuadraticForm_nonneg @ LeanFlagAlgebras/FlagAlgebra/QuadraticForm.lean:16 :: theorem flagQuadraticForm_nonneg
63. [theorem] flagQuadraticForm_downward_nonneg @ LeanFlagAlgebras/FlagAlgebra/QuadraticForm.lean:60 :: theorem flagQuadraticForm_downward_nonneg
64. [def] eval @ LeanFlagAlgebras/Logic/Defs.lean:28 :: def eval (A : Assert σ) (φ : PositiveHom σ) : Prop
65. [def] isValid @ LeanFlagAlgebras/Logic/Defs.lean:43 :: def isValid (A : Assert σ) : Prop :=
66. [def] Entails @ LeanFlagAlgebras/Logic/Defs.lean:46 :: def Entails (A B : Assert σ) : Prop :=
67. [theorem] eval_eq @ LeanFlagAlgebras/Logic/Defs.lean:52 :: theorem eval_eq (f g : FlagAlgebra σ) (φ : PositiveHom σ)
68. [theorem] isValid_eq @ LeanFlagAlgebras/Logic/Defs.lean:57 :: theorem isValid_eq (f g : FlagAlgebra σ)
69. [theorem] entails_def @ LeanFlagAlgebras/Logic/Defs.lean:62 :: theorem entails_def (A B : Assert σ)
70. [theorem] eq_refl @ LeanFlagAlgebras/Logic/Defs.lean:66 :: theorem eq_refl (f : FlagAlgebra σ) : isValid (f =ₐ f) := by
71. [theorem] eq_symm @ LeanFlagAlgebras/Logic/Defs.lean:70 :: theorem eq_symm (f g : FlagAlgebra σ)
72. [theorem] eq_trans @ LeanFlagAlgebras/Logic/Defs.lean:75 :: theorem eq_trans (f g h : FlagAlgebra σ)
73. [def] Eqv @ LeanFlagAlgebras/Logic/Defs.lean:80 :: def Eqv (f g : FlagAlgebra σ) : Prop :=
74. [theorem] eqv_iff @ LeanFlagAlgebras/Logic/Defs.lean:86 :: theorem eqv_iff (f g : FlagAlgebra σ)
75. [theorem] eqv_refl @ LeanFlagAlgebras/Logic/Defs.lean:90 :: theorem eqv_refl (f : FlagAlgebra σ) : f ≡ₐ f :=
76. [theorem] eqv_symm @ LeanFlagAlgebras/Logic/Defs.lean:93 :: theorem eqv_symm {f g : FlagAlgebra σ} (h : f ≡ₐ g) : g ≡ₐ f := by
77. [theorem] eqv_trans @ LeanFlagAlgebras/Logic/Defs.lean:97 :: theorem eqv_trans {f g h : FlagAlgebra σ} (hfg : f ≡ₐ g) (hgh : g ≡ₐ h) : f ≡ₐ h := by
78. [theorem] eqv_add @ LeanFlagAlgebras/Logic/Defs.lean:105 :: theorem eqv_add {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
79. [theorem] eqv_sub @ LeanFlagAlgebras/Logic/Defs.lean:115 :: theorem eqv_sub {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
80. [theorem] eqv_mul @ LeanFlagAlgebras/Logic/Defs.lean:125 :: theorem eqv_mul {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
81. [theorem] eqv_smul @ LeanFlagAlgebras/Logic/Defs.lean:135 :: theorem eqv_smul (r : ℝ) {f g : FlagAlgebra σ} (hfg : f ≡ₐ g)
82. [theorem] eval_le @ LeanFlagAlgebras/Logic/Defs.lean:145 :: theorem eval_le (f g : FlagAlgebra σ) (φ : PositiveHom σ)
83. [theorem] isValid_le @ LeanFlagAlgebras/Logic/Defs.lean:150 :: theorem isValid_le (f g : FlagAlgebra σ)
84. [theorem] eval_implies @ LeanFlagAlgebras/Logic/Defs.lean:155 :: theorem eval_implies (A B : Assert σ) (φ : PositiveHom σ)
85. [theorem] isValid_implies @ LeanFlagAlgebras/Logic/Defs.lean:160 :: theorem isValid_implies (A B : Assert σ)
86. [theorem] le_refl @ LeanFlagAlgebras/Logic/Defs.lean:164 :: theorem le_refl (f : FlagAlgebra σ) : isValid (f ≤ₐ f) := by
87. [theorem] le_trans @ LeanFlagAlgebras/Logic/Defs.lean:168 :: theorem le_trans (f g h : FlagAlgebra σ)
88. [theorem] le_antisymm_eq @ LeanFlagAlgebras/Logic/Defs.lean:173 :: theorem le_antisymm_eq (f g : FlagAlgebra σ)
89. [theorem] eq_implies_le @ LeanFlagAlgebras/Logic/Defs.lean:178 :: theorem eq_implies_le (f g : FlagAlgebra σ)
90. [theorem] eq_implies_le' @ LeanFlagAlgebras/Logic/Defs.lean:183 :: theorem eq_implies_le' (f g : FlagAlgebra σ)
91. [theorem] le_add_right @ LeanFlagAlgebras/Logic/Defs.lean:188 :: theorem le_add_right (f g a : FlagAlgebra σ)
92. [theorem] le_add_left @ LeanFlagAlgebras/Logic/Defs.lean:198 :: theorem le_add_left (f g a : FlagAlgebra σ)
93. [theorem] le_smul_nonneg @ LeanFlagAlgebras/Logic/Defs.lean:208 :: theorem le_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (f g : FlagAlgebra σ)
94. [theorem] implies_refl @ LeanFlagAlgebras/Logic/Defs.lean:216 :: theorem implies_refl (A : Assert σ) : isValid (A →ₐ A) := by
95. [theorem] implies_trans @ LeanFlagAlgebras/Logic/Defs.lean:220 :: theorem implies_trans (A B C : Assert σ)
96. [theorem] modus_ponens @ LeanFlagAlgebras/Logic/Defs.lean:225 :: theorem modus_ponens {A B : Assert σ}
97. [theorem] entails_refl @ LeanFlagAlgebras/Logic/Defs.lean:231 :: theorem entails_refl (A : Assert σ) : A ⊢ₐ A :=
98. [theorem] entails_trans @ LeanFlagAlgebras/Logic/Defs.lean:234 :: theorem entails_trans {A B C : Assert σ} (hAB : A ⊢ₐ B) (hBC : B ⊢ₐ C) : A ⊢ₐ C := by
99. [theorem] eqv_iff_isValid_eq @ LeanFlagAlgebras/Logic/Defs.lean:245 :: theorem eqv_iff_isValid_eq (f g : FlagAlgebra σ) : (f ≡ₐ g) ↔ isValid (f =ₐ g) :=
100. [theorem] entails_iff_isValid_implies @ LeanFlagAlgebras/Logic/Defs.lean:249 :: theorem entails_iff_isValid_implies (A B : Assert σ) : (A ⊢ₐ B) ↔ isValid (A →ₐ B) :=
101. [def] parseFlagAlgebraIndices @ LeanFlagAlgebras/Logic/Tactic.lean:28 :: def parseFlagAlgebraIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
102. [def] parseFlagIndices @ LeanFlagAlgebras/Logic/Tactic.lean:63 :: def parseFlagIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
103. [def] runForbiddenFlagExpansion @ LeanFlagAlgebras/Logic/Tactic.lean:98 :: def runForbiddenFlagExpansion (N : TSyntax `term) : TacticM Unit :=
104. [def] runForbiddenFlagMul @ LeanFlagAlgebras/Logic/Tactic.lean:162 :: def runForbiddenFlagMul (N : TSyntax `term) : TacticM Unit :=

Output format (JSON only):
{
  "selected_ids": [1,2,3],
  "selection_rationale": ["..."],
  "missing_evidence": ["..."]
}
