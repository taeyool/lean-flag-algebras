# Agent Task: Draft Section

Project: Formalizing Flag Algebra in Lean
Target Section: Introduction
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
- [text] line @ README.md:1 :: # lean-flag-algebras
- [text] line @ README.md:2 :: The goal of this project is to formalize the results of the paper [Flag Algebras](https://people.cs.uchicago.edu/~razborov/files/flag.pdf) by Alexander A. Razborov.
- [text] line @ README.md:19 :: MATHLIB_NO_CACHE_ON_UPDATE=1 lake build LeanFlagAlgebras:docs
- [text] line @ README.md:26 :: MATHLIB_NO_CACHE_ON_UPDATE=1 lake update LeanFlagAlgebras
- [text] line @ README.md:27 :: MATHLIB_NO_CACHE_ON_UPDATE=1 lake build LeanFlagAlgebras:docs
- [def] FinFlag @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:63 :: def FinFlag (σ : FlagType (Fin n₀)) : Type
- [theorem] finFlag_one_fst @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:73 :: theorem finFlag_one_fst
- [theorem] finFlag_one_snd @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:77 :: theorem finFlag_one_snd
- [theorem] flagDensity_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:81 :: theorem flagDensity_one
- [theorem] flagPairDensity_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:88 :: theorem flagPairDensity_one
- [theorem] finFlag_size_ge_n @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:94 :: theorem finFlag_size_ge_n₀
- [lemma] rat_smul_eq_real_smul @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:109 :: lemma rat_smul_eq_real_smul
- [theorem] unitVector_apply_self @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:132 :: theorem unitVector_apply_self
- [theorem] unitVector_support @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:139 :: theorem unitVector_support
- [theorem] unitVector_apply_other @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:146 :: theorem unitVector_apply_other
- [theorem] unitVector_apply_other_size @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:152 :: theorem unitVector_apply_other_size
- [theorem] flagVector_eq_sum_unitVector @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:159 :: theorem flagVector_eq_sum_unitVector
- [theorem] flagVector_one_support @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:173 :: theorem flagVector_one_support
- [theorem] flagVector_one_apply_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:180 :: theorem flagVector_one_apply_one
- [theorem] flagMulWithSize_comm @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:192 :: theorem flagMulWithSize_comm
- [theorem] flagMulWithSize_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:200 :: theorem flagMulWithSize_one
- [theorem] flagMul_comm @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:224 :: theorem flagMul_comm
- [theorem] flagMul_one @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:229 :: theorem flagMul_one
- [theorem] flagVector_mul_eq_nested_sum @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:239 :: theorem flagVector_mul_eq_nested_sum
- [theorem] flagVector_mul_comm @ LeanFlagAlgebras/FlagAlgebra/FlagAlgebra.lean:244 :: theorem flagVector_mul_comm
- [def] eval @ LeanFlagAlgebras/Logic/Defs.lean:28 :: def eval (A : Assert σ) (φ : PositiveHom σ) : Prop
- [def] isValid @ LeanFlagAlgebras/Logic/Defs.lean:43 :: def isValid (A : Assert σ) : Prop :=
- [def] Entails @ LeanFlagAlgebras/Logic/Defs.lean:46 :: def Entails (A B : Assert σ) : Prop :=
- [theorem] eval_eq @ LeanFlagAlgebras/Logic/Defs.lean:52 :: theorem eval_eq (f g : FlagAlgebra σ) (φ : PositiveHom σ)
- [theorem] isValid_eq @ LeanFlagAlgebras/Logic/Defs.lean:57 :: theorem isValid_eq (f g : FlagAlgebra σ)
- [theorem] entails_def @ LeanFlagAlgebras/Logic/Defs.lean:62 :: theorem entails_def (A B : Assert σ)
- [theorem] eq_refl @ LeanFlagAlgebras/Logic/Defs.lean:66 :: theorem eq_refl (f : FlagAlgebra σ) : isValid (f =ₐ f) := by
- [theorem] eq_symm @ LeanFlagAlgebras/Logic/Defs.lean:70 :: theorem eq_symm (f g : FlagAlgebra σ)
- [theorem] eq_trans @ LeanFlagAlgebras/Logic/Defs.lean:75 :: theorem eq_trans (f g h : FlagAlgebra σ)
- [def] Eqv @ LeanFlagAlgebras/Logic/Defs.lean:80 :: def Eqv (f g : FlagAlgebra σ) : Prop :=
- [theorem] eqv_iff @ LeanFlagAlgebras/Logic/Defs.lean:86 :: theorem eqv_iff (f g : FlagAlgebra σ)
- [theorem] eqv_refl @ LeanFlagAlgebras/Logic/Defs.lean:90 :: theorem eqv_refl (f : FlagAlgebra σ) : f ≡ₐ f :=
- [theorem] eqv_symm @ LeanFlagAlgebras/Logic/Defs.lean:93 :: theorem eqv_symm {f g : FlagAlgebra σ} (h : f ≡ₐ g) : g ≡ₐ f := by
- [theorem] eqv_trans @ LeanFlagAlgebras/Logic/Defs.lean:97 :: theorem eqv_trans {f g h : FlagAlgebra σ} (hfg : f ≡ₐ g) (hgh : g ≡ₐ h) : f ≡ₐ h := by
- [theorem] eqv_add @ LeanFlagAlgebras/Logic/Defs.lean:105 :: theorem eqv_add {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
- [theorem] eqv_sub @ LeanFlagAlgebras/Logic/Defs.lean:115 :: theorem eqv_sub {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
- [theorem] eqv_mul @ LeanFlagAlgebras/Logic/Defs.lean:125 :: theorem eqv_mul {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
- [theorem] eqv_smul @ LeanFlagAlgebras/Logic/Defs.lean:135 :: theorem eqv_smul (r : ℝ) {f g : FlagAlgebra σ} (hfg : f ≡ₐ g)
- [theorem] eval_le @ LeanFlagAlgebras/Logic/Defs.lean:145 :: theorem eval_le (f g : FlagAlgebra σ) (φ : PositiveHom σ)
- [theorem] isValid_le @ LeanFlagAlgebras/Logic/Defs.lean:150 :: theorem isValid_le (f g : FlagAlgebra σ)
- [theorem] eval_implies @ LeanFlagAlgebras/Logic/Defs.lean:155 :: theorem eval_implies (A B : Assert σ) (φ : PositiveHom σ)
- [theorem] isValid_implies @ LeanFlagAlgebras/Logic/Defs.lean:160 :: theorem isValid_implies (A B : Assert σ)
- [theorem] le_refl @ LeanFlagAlgebras/Logic/Defs.lean:164 :: theorem le_refl (f : FlagAlgebra σ) : isValid (f ≤ₐ f) := by
- [theorem] le_trans @ LeanFlagAlgebras/Logic/Defs.lean:168 :: theorem le_trans (f g h : FlagAlgebra σ)
- [theorem] le_antisymm_eq @ LeanFlagAlgebras/Logic/Defs.lean:173 :: theorem le_antisymm_eq (f g : FlagAlgebra σ)
- [theorem] eq_implies_le @ LeanFlagAlgebras/Logic/Defs.lean:178 :: theorem eq_implies_le (f g : FlagAlgebra σ)
- [theorem] eq_implies_le' @ LeanFlagAlgebras/Logic/Defs.lean:183 :: theorem eq_implies_le' (f g : FlagAlgebra σ)
- [theorem] le_add_right @ LeanFlagAlgebras/Logic/Defs.lean:188 :: theorem le_add_right (f g a : FlagAlgebra σ)
- [theorem] le_add_left @ LeanFlagAlgebras/Logic/Defs.lean:198 :: theorem le_add_left (f g a : FlagAlgebra σ)
- [theorem] le_smul_nonneg @ LeanFlagAlgebras/Logic/Defs.lean:208 :: theorem le_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (f g : FlagAlgebra σ)
- [theorem] implies_refl @ LeanFlagAlgebras/Logic/Defs.lean:216 :: theorem implies_refl (A : Assert σ) : isValid (A →ₐ A) := by
- [theorem] implies_trans @ LeanFlagAlgebras/Logic/Defs.lean:220 :: theorem implies_trans (A B C : Assert σ)
- [theorem] modus_ponens @ LeanFlagAlgebras/Logic/Defs.lean:225 :: theorem modus_ponens {A B : Assert σ}
- [theorem] entails_refl @ LeanFlagAlgebras/Logic/Defs.lean:231 :: theorem entails_refl (A : Assert σ) : A ⊢ₐ A :=
- [theorem] entails_trans @ LeanFlagAlgebras/Logic/Defs.lean:234 :: theorem entails_trans {A B C : Assert σ} (hAB : A ⊢ₐ B) (hBC : B ⊢ₐ C) : A ⊢ₐ C := by
- [theorem] eqv_iff_isValid_eq @ LeanFlagAlgebras/Logic/Defs.lean:245 :: theorem eqv_iff_isValid_eq (f g : FlagAlgebra σ) : (f ≡ₐ g) ↔ isValid (f =ₐ g) :=
- [theorem] entails_iff_isValid_implies @ LeanFlagAlgebras/Logic/Defs.lean:249 :: theorem entails_iff_isValid_implies (A B : Assert σ) : (A ⊢ₐ B) ↔ isValid (A →ₐ B) :=
- [def] parseFlagAlgebraIndices @ LeanFlagAlgebras/Logic/Tactic.lean:28 :: def parseFlagAlgebraIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
- [def] parseFlagIndices @ LeanFlagAlgebras/Logic/Tactic.lean:63 :: def parseFlagIndices? (nm : Name) : Option (Nat × Nat × Nat × Nat) := do
- [def] runForbiddenFlagExpansion @ LeanFlagAlgebras/Logic/Tactic.lean:98 :: def runForbiddenFlagExpansion (N : TSyntax `term) : TacticM Unit :=
- [def] runForbiddenFlagMul @ LeanFlagAlgebras/Logic/Tactic.lean:162 :: def runForbiddenFlagMul (N : TSyntax `term) : TacticM Unit :=

## Instructions
1. Write one coherent section draft in academic style.
2. Do not invent theorem names or file paths.
3. Ensure each nontrivial claim is grounded in Retrieved Evidence.
4. Respect Mandatory Considerations first, then adapt wording to Author Notes.
5. You may adjust section structure if it improves clarity, but explain the change briefly.
6. End with a short 'Evidence Coverage' list mapping key claims to evidence lines.
