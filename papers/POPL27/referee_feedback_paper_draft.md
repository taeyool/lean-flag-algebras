# Referee Report — "Formalizing Flag Algebras in Lean" (paper_draft.tex)

- 대상: `papers/POPL27/paper_draft.tex` (4,665행, 2026-07-16 기준 HEAD)
- 검토 방식: 논문 전문 정독 + 논문에 인용된 모든 Lean 선언·커맨드·택틱·수치를 저장소
  (`LeanFlagAlgebras/`) 실제 코드와 1:1 대조 + 수식 재검산 + 참고문헌 사실 확인.
- 관점: formalization 논문(POPL/ITP/CPP류) 심사자.

### 대응 로그 (Revision Log)

| 날짜 | 조치 | 상태 | 커밋 |
|---|---|---|---|
| 2026-07-16 | **용어 정리: 본문의 "ordinary" 수식어 제거** — 보고서 제출 이후 저자 요청으로 수행한 후속 정리. subgraph 구분용 `ordinary` 15곳 중 본문 12곳(§1 l.414·424, §5.2 l.3197·3202, §5.4 l.3366·3370, §8 l.3897·3898·4043×2·4128·4136)을 제거. §2 l.477의 규약 문장("an unqualified *subgraph* is an ordinary, not necessarily induced, subgraph")과 abstract 2곳(l.298, 307)은 유지, 다른 의미("보통의")의 `ordinary` 18곳은 불변. 수정 전후 라인 수 동일(11행 교체)이라 본 보고서의 행 번호 인용은 계속 유효함. | 반영 완료 | `d190e61` |
| 2026-07-16 | **§3-3 반영: §8 "non-degenerate" 정의 문구 수정** — l.3972의 "is non-degenerate for \(\mathcal K\): equivalently,"를 "is \emph{non-degenerate} for \(\mathcal K\): that is,"로 교체. 매달린 "equivalently"를 제거하고, 정의부임을 드러내기 위해 논문의 정의 관례(\emph{hereditary}, \emph{root-plantable} 등)에 맞춰 용어를 이탤릭 처리. 행 수 변화 없음(행 번호 인용 계속 유효). | 반영 완료 | `400f8a5` |
| 2026-07-16 | **용어 통일: `Ext_σ`를 "probability measure"로 통일** — 보고서 제출 이후 저자 요청으로 수행한 후속 정리. Ext_σ를 명사로 지칭할 때 distribution(4곳)/measure(5곳)가 혼용되던 것을 measure로 통일: §2.5 l.1044("a unique probability distribution"→"measure", Ext_σ 정의부), §3.5 l.2053("the distribution obtained by"→"the measure obtained by")·l.2057("drawn from this distribution"→"this measure")·l.2058("that distribution:"→"that measure:"). 근거: Definition 8.1의 집합 적용 `Ext_σ(φ₀)({χ|…})=1`과 §8의 supp() 정의(l.3978)가 measure 전제, Lean 타입 `ProbabilityMeasure`와의 정합, Razborov(2007) 원 정식화와의 정합. §3.4의 flag 표집 분포 3곳(l.1885·1902·1909)은 Ext_σ와 별개 대상이라 "distribution" 유지. 행 수 변화 없음(행 번호 인용 계속 유효). | 반영 완료 | `400f8a5` |
| 2026-07-16 | **용어 정리: root 어휘 앵커 + §5 "rooted" 제거** — (i) §2.1 라벨 정점 정의에 동의어 앵커 추가: "the \emph{labeled vertices}, or \emph{roots}, of F" — 이로써 §8의 root/rooted/random rooting 어휘와 "root-planting" 명명이 해독 가능해짐. (ii) §8 Q_σ 문단의 정의-전 사용 "It imposes no random-rooting requirement"는 저자의 §8 개정(커밋 4ecdbef 등)에서 해당 문단이 재작성되며 문장 자체가 삭제되어 자연 해소됨 — 리베이스 시 원격안 채택, 최종 반영분은 (i)+(iii). (iii) §5.1의 "rooted" 3곳을 "labeled"로 교체: "rooted three-vertex basis"→"labeled three-vertex basis", "the displayed rooted flag"→"the displayed labeled flag", "the two rooted flags"→"the two labeled flags" — §5에서 root 계열 어휘 전부 제거(grep 검증). §8의 "random rooting"을 정식 용어로 정의하는 방안은 저자 결정으로 채택하지 않음(§2.1 앵커로 갈음). | 반영 완료 | `400f8a5` |

- 미결(이 건 관련): abstract 2곳(l.298, 307)의 처리 방향 — 유지 / "(not necessarily induced)" 괄호 주석 / 제거 — 저자 결정 대기.
- 참고: "ordinary" 정리는 M2(induced-forbid 관계 `≤ᵢ[·]` 미서술)와 인접한 용어 문제이지만 **M2 자체를 해소하지는 않음**. 그 외 보고서 항목은 아직 미대응 — 개별 반영 현황은 위 표와 각 항목의 ✅ 표기 참조.
- 주의: 검토 이후 논문 개정이 계속되고 있어(§8 재작성, Mantel 인용 추가 등) 본 보고서의 행 번호 인용(검토 시점 4,665행 기준)은 어긋날 수 있음. 항목을 찾을 때는 섹션 태그와 인용 문구를 기준으로 할 것.

### 논문 섹션 구성 (아래 태그의 기준)

| 태그 | 섹션 |
|---|---|
| Abstract / §1 | Abstract / Introduction (Contributions·Organization 문단 포함) |
| §2 | Background: Flag Algebras — 2.1 Flag Types and Flags(그림 1) · 2.2 Subflag Densities · 2.3 The Flag Algebra · 2.4 Positive Homomorphisms and Semantic Order · 2.5 The Downward Operator |
| §3 | Formalizing Flag Algebras in Lean 4 — 3.1 Flag Types and Flags · 3.2 Subflag Densities · 3.3 The Flag Algebra · 3.4 Positive Homomorphisms and Semantic Order · 3.5 The Downward Operator · 3.6 Forbidden Graphs as Assumptions |
| §4 | The Reflection Layer — 4.1 Concrete Graph Representations and Finite Search · 4.2 Adequacy Theorems · 4.3 From Reflected Computations to Reusable Theorems |
| §5 | Automating Flag-Algebra Proofs — 5.1 How a Certificate Proves a Bound · 5.2 The Four-Part Compiler(Part 1–4, "The translator") · 5.3 Trust Model · 5.4 Evaluation(표 1) |
| §6 | Lower Bounds and Other Inequalities |
| §7 | Engineering Obstacles — 7.1 Isomorphism · 7.2 Auxiliary Expansion Size(HEq) · 7.3 Controlling Finite Enumerations · 7.4 Bijections |
| §8 | A Meta-Theory of Ensemble Semantics |
| §9 | Open Design Questions |
| §10 | Related Work |
| §11 | Conclusion |
| [부록*] | `\commentout` 처리된 비활성 부록 "Lessons for Future Formalizations" (Lesson 1–6) — 현재 컴파일 출력에는 미포함 |

참고: theorem/lemma/definition/example/remark가 섹션 단위 공용 카운터를 쓰므로 번호와
소절이 어긋나 보일 수 있다 — 예: **Definition 3.1은 §3.6에**, **Theorem 2.5(Lovász–Szegedy)는
§2.4에**, **Lemma 2.6(semantic-bound)도 §2.4에**, **Theorem 2.9(downward)와 Example 2.10
(만텔 유도)은 §2.5에** 있다.

---

## 0. 총평 (Summary & Overall Assessment)

**요약.** 이 논문은 Razborov flag algebra의 Lean 4 형식화를 보고한다. (i) 명세 계층(flag,
밀도, 몫대수, positive homomorphism, downward operator)[§3], (ii) 반사(reflection) 계층
(`Sym2Graph` 기반 실행 가능 표현 + adequacy 정리)[§4], (iii) Flagmatic SDP 인증서를 Lean 증명으로
컴파일하는 4단계 컴파일러와 7개 사례(만텔, 오각형 정리 포함)[§5–6], (iv) 제약(금지 그래프) 의미론에 대한
메타이론(quotient vs. ensemble, root-plantability 판별 기준, C₄-free 반례)과 그 자동
형식화[§8]까지, 범위가 넓고 완성도가 높다.

**강점.**
1. **[§5.4, §6, §8]** 실질적 수학·공학 기여가 모두 있다: 오각형 정리급 인증서의 end-to-end 기계 검증은 이 분야에서
   실제로 처음 수준의 결과로 보이며, ensemble/quotient 의미론 비교(§8)는 형식화가 새로운 수학을
   낳은 훌륭한 사례다.
2. **[§5.3]** 신뢰 모델(§5.3)이 이례적으로 정직하다. `native_decide` vs `decide +kernel`의 트러스트 경계,
   번역 충실성(fidelity)과 논리적 타당성(validity)의 구분을 명시적으로 서술한다.
3. **[§3·§4·§5.2·§6·§8 전반]** **논문 스니펫의 충실도가 높다.** 검토 과정에서 논문에 인용된 선언 60여 개를 실제 코드와
   대조했는데, 대부분(특히 §3의 명세 계층 전체, `exists_probMeasure_extend_emptyType_positiveHom`[§3.5],
   `psd_real_ldlt`[§5.2 Part 2], `blowUp`[§6], 메타이론 4개 정리명[§8])은 사실상 verbatim으로 일치한다.
   [부록* Lesson 3]이 주장하는 "10분 초과" 주석(`-- sort_at -- takes more than 10 minutes`)까지
   `ErdosPentagon/Lemmas.lean:445`에 그대로 존재한다.
4. **[§2.3, §2.5, §4.2, §5.1, §5.4, §6, §9]** 수치·계산 검산 결과 오류가 없다. 만텔 유도(Example 2.10[§2.5]의
   eq:mantel-key 및 §5.1), 곱셈 예시 Example 2.4[§2.3]의 곱 전개,
   q_σ(P̄₃•)=2/3[§4.2], 24/625 하한 산술[§6], 표 1의 bound 값(3/8, 3/4, 2/3, 1/2)[§5.4]을 모두 재검산했고
   전부 옳다. 오각형 통계 1,800/672/360[§9]도 독립 재계산으로 일치를 확인했다(아래 §6 참조).

**약점.**
1. **[§5]** §5(인증서 컴파일러)의 핵심 표기 `≤_{\mathcal H}`가 형식적으로 정의되지 않은 채 사용된다.
2. **[§3.6, §5, §6, §11]** 코드에는 두 개의 forbid 의미론(`≤[H]` subgraph판, `≤ᵢ[F]` induced판)이 있는데 논문은
   하나만 서술하며, 정작 오각형 상한·P₄ 사례는 induced판으로 진술되어 있다.
3. **[§4.3, §5.2 Part 1]** 생성 커맨드 계열 이름이 최근 리팩터링(커밋 `35eb0a4`, `b201a91`) 이후의 코드와 어긋난다
   (`generate_pruned_*` → 현재는 대부분 `generate_forbid_free_*`).
4. **[§5.4]** 정량 평가(LOC, 빌드 시간, 계층별 규모)가 없다.
5. **[참고문헌, §6, §8]** 참고문헌 오류 1건(B. Green), 무정의 용어 몇 건(O₃[§6], clone-closed 등[§8]).

**판정 제안: Minor–Major revision 경계 (수정 후 채택 권장).** 결과 자체는 견고하다. 아래
수정 사항은 대부분 서술·표기·아티팩트 정리 수준이며, 논문의 주장을 흔드는 결함은 발견하지 못했다.

---

## 1. 주요 코멘트 (Major)

### M1. `≤_{\mathcal H}` / `≤_{K_3}` 표기가 정의 없이 사용됨
**해당 위치: §5 전반(§5 도입부, §5.1의 만텔 유도, §5.2 Part 4); 관련: §3.6(Definition 3.1), §8(Definition 8.1)**

§5 도입부(l.2805 부근)부터 `[P] ≤_{\mathcal H} c·1`, §5.1의 만텔 유도에서 `≤_{K_3}`
(l.2925, 2936), Part 4 전체에서 `≤_H` (l.3220–3255)가 사용되지만, 이 기호는 어디에서도
정의되지 않는다. 가장 가까운 형식적 정의는 Definition 3.1[§3.6]의 `≤^{ens}_{H,σ}`와 §8의
`≤^{ens}_{K,σ}`(Definition 8.1)뿐이다. 제안: §5 도입부에 "이하 `f ≤_H g`는 `f ≤^{ens}_{H,∅ₜ} g`
(Lean의 `forbidLE H f g`, 코드 표기 `f ≤[H] g`)의 약기"라는 한 문장을 추가할 것.
또한 Definition 3.1은 단일 금지 그래프 H만 다루는데 §5은 family `\mathcal H` 첨자를
쓴다(실제 7개 사례 모두 singleton). 표기를 singleton으로 통일하거나 family 케이스의 의미를
명시하기 바란다.

### M2. induced-forbid 관계(`≤ᵢ[·]`)가 논문에 없음
**해당 위치: §3.6(Definition 3.1과 forbidLE 서술), §5.2 Part 3("two representations of subgraph-freeness"), §5.4(C₅-free 문단), §6(오각형 상·하한 결합), §11(K₄-free P₄ 문장)**

코드에는 두 관계가 공존한다 (`Forbid/Basic.lean:105–109`):

```
notation f "≤ᵢ[" F_forbid "]" g => inducedForbidLE F_forbid f g   -- induced 판
notation f "≤[" H "]" g       => forbidLE H f g                  -- subgraph 판 (논문의 Def 3.1)
```

그런데 실제 결과물 중 오각형 SOS 보조정리는 `C5.toFlagAlgebra ≤ᵢ[K3.toFinFlag] (24/625)•1`
(`ErdosPentagon/Lemmas.lean:420`)로, K₄-free P₄ 사례는 `P4_density ≤ᵢ[K4.toFinFlag] (32/9)•1`
(`Automation/K4freeP4.lean:91`)로 **induced 판**으로 진술되며, 브리지 보조정리
`inducedForbidLE_toFinFlag_imp_forbidLE`로 subgraph 판으로 이동한다. 완전그래프 금지에서는 두
개념이 일치하므로 수학적 문제는 없지만, (i) 논문이 서술하는 의미론과 아티팩트의 실제 진술이
다르고, (ii) §5.2 Part 3에서 "two representations of subgraph-freeness"를 언급하면서도 그
형식적 대응물(≤ᵢ vs ≤)은 소개하지 않는다. 두 관계와 브리지 정리를 §3.6이나 §5.2에서 명시적으로
소개할 것을 권한다.

### M3. `ℙ[φ₀]`의 정의와 유일성
**해당 위치: §2.5(배경의 "unique probability distribution" 주장), §3.5(존재 정리 `exists_probMeasure_…`), §3.6(Definition 3.1과 `forbidLEWith` 스니펫의 `ℙ[φ₀]`)**

Definition 3.1[§3.6]과 `forbidLEWith` 스니펫[§3.6]은 랜덤 확장 측도 `ℙ[φ₀]`를 canonical한 것처럼 다루지만,
실제 코드에서 `ℙ[φ₀]`는 존재 정리의 `Classical.choose`다
(`RandomHom.lean:1177–1186`: `probMeasure_extend_emptyType_positiveHom := Classical.choose
(exists_probMeasure_extend_emptyType_positiveHom …)` + notation). 논문에 인용된 정리[§3.5]도
존재(∃)만 진술한다. 수학적으로는 (§2.5에서 인용된 Razborov의) 유일성 덕에 선택과 무관하지만:

- Lean에서 유일성이 형식화되어 있는가? (메타이론 쪽에는 `MetaTheory/MeasureUniqueness.lean`
  — "Uniqueness of a measure on X_σ from its flag-integrals" — 이 존재한다. 핵심 라이브러리의
  `forbidLE`가 이것에 의존하는지, 아니면 선택된 측도에 대한 진술인지 본문에서 한 문장으로
  정리해야 한다.)
- 유일성이 코어에 없다면, `forbidLE`의 의미는 "적분 항등식을 만족하는 *선택된* 측도에 대한
  a.s. 부등식"이고, Definition 3.1("the random extension")과의 대응은 메타 수준 논증이 된다.
  트러스트 모델[§5.3]을 상세히 쓰는 논문이므로 이 지점도 명시할 가치가 있다.

### M4. 생성 커맨드 이름이 현재 코드와 불일치 (stale)
**해당 위치: §5.2 Part 1(커맨드 계열 서술), §4.3(예시 커맨드 4종 목록)**

§5.2 Part 1: "Complete-graph forbids use the `generate_pruned_*` commands, while a general
graph forbidden as a subgraph uses the parallel `generate_subgraph_free_*` commands."
— 커밋 `35eb0a4`/`b201a91`("Unify forbid-free … on the pruned …") 이후 pruned 구현이
canonical 이름으로 **개명**되어, 현재 라이브 코드의 완전그래프-금지 계열은
`generate_forbid_free_empty_typed_flags` / `generate_forbid_free_flags`
(`Flags/ForbidFreeGenerator.lean:242, 518`) / `generate_forbid_free_mul_theorems`
(`Flags/Densities/MulThmGenerator.lean:188`)이며, `generate_pruned_*`로 남은 것은
`generate_pruned_flag_pair_density_theorems` (`DensityThmGenerator.lean:620`) 하나뿐이다.
`generate_subgraph_free_*` 4종은 논문 서술대로 존재한다. §5.2 Part 1의 커맨드 계열 서술을
현재 이름으로 갱신하거나, 논문 스냅샷 커밋을 명시해야 한다.

또한 §4.3의 예시 두 줄 `generate_flag_pair_density_theorems_no_forbid 2 3 1 0`,
`generate_mul_theorems 2 3 1 0`은 커맨드 자체는 실재하지만 그 인자 조합의 호출은 저장소에
없다(라이브 호출은 `3 4 2 0`/`3 4 2 1`뿐, `Automation/CompleteGraphFreeP4.lean:95–99`).
예시로서는 무방하나 "the relevant commands have the following form"이 실제 소스에 있는
호출이라는 인상을 주므로, 예시임을 밝히거나 실존 호출로 교체하기 바란다.

### M5. Contributions/Abstract가 §6과 불일치 — Goodman은 컴파일러 사례가 아님
**해당 위치: Abstract, §1(Contributions 문단) ↔ §6("Additional Goodman-style consequences" 문단)**

Contributions[§1] 셋째 항목: "it demonstrates **the compiler** on machine-checked proofs of
Mantel's theorem, the Erdős pentagon theorem, **Goodman-type inequalities**, and a C₄-density
bound" — 그러나 §6은 Goodman 부등식들이 "outside the certificate pipeline"에서, 컴파일러가
아니라 동일 인프라(택틱·생성기)로 손수 증명되었다고 명시한다(코드도 그러함:
`MantelTheorem/GoodmanBound.lean`, `GoodmanRamsey.lean`). Abstract의 병치("As case studies,
we obtain … Goodman-type inequalities …")도 같은 오해를 유발한다. "compiler" 사례(표 1[§5.4]의 7개)와
"same infrastructure" 사례(Goodman, 하한[§6])를 문장 수준에서 분리할 것.

### M6. K₄-free P₄ 사례가 결론에서 처음 등장
**해당 위치: §11(Conclusion) — 본문(§5.4 또는 §6)에는 부재**

Conclusion[§11]의 "A further case study proves a K₄-free P₄ density bound using the same
automation layer."는 본문 어디에도 없다. 확인 결과 `Automation/K4freeP4.lean:91`의
`K4_free_P4_density_upper_bound : P4_density ≤ᵢ[K4.toFinFlag] (32/9 : ℝ) • 1`이며 sorry/axiom
없이 성립한다(단, induced 판, M2 참조). 본문(§5.4 또는 §6)에서 bound(32/9)와 함께 소개하거나
결론에서 제거할 것. **주의:** 같은 디렉터리의 일반화 버전
`Automation/CompleteGraphFreeP4.lean`은 명시적 `axiom` 2개(`Zykov_K4_density_bound`,
`Turan_limit_P4_density`)를 사용한다(파일 주석에 정직하게 문서화되어 있음). 논문이 이
일반화까지 암시한다면 axiom 의존을 반드시 공개해야 하고, r=3 특수화만 주장한다면 그 범위를
명확히 하기 바란다.

### M7. Theorem 2.5의 귀속(attribution)
**해당 위치: §2.4(Theorem 2.5 [Lovász–Szegedy]); 관련: 참고문헌 [lovasz2006limits], [razborov2007flag]**

Theorem 2.5(수렴열 ↔ positive hom)[§2.4]는 σ-flag 일반형으로 진술되었는데 인용은
Lovász–Szegedy [lovasz2006limits]뿐이다. 해당 논문은 unlabeled 그래프(그리고 hom 밀도)
설정이고, typed/σ-flag 버전과 (b) 방향의 표준 출처는 Razborov [razborov2007flag, §3]다.
"[lovasz2006limits]; the typed version we use is due to Razborov [razborov2007flag]" 정도로
보강할 것.

### M8. Turán 밀도 극한의 존재
**해당 위치: §1(π(P;H)의 lim 정의), §3.6(`generalizedTuranDensity` 전이 정리 주변 서술); 관련: §2.4(Lemma 2.6의 증명이 이 정의에 의존)**

§1의 π(P; H) 정의와 §3.6의 `generalizedTuranDensity` 서술 모두 극한 존재를 암묵 가정한다.
표준 평균화 논증으로 max-밀도가 단조 감소라 극한이 존재하지만 논문엔 언급이 없다. 실제 Lean
정의는 `limUnder atTop` (`Turan/GeneralizedTuran.lean:97–99`; 발산 시 junk value)이고 수렴은
`tendsto_generalizedTuranDensity` (`:253`)로 **별도 증명**되어 있다. 이는 형식화가 은근슬쩍
넘어가지 않았다는 좋은 사례이므로, 한 문장으로 언급하면 논문이 더 강해진다.

### M9. 정량 평가 부재
**해당 위치: §5.4(Evaluation, 표 1); 관련: §9(2,832 identities / 15 batches 수치가 여기 묻혀 있음)**

formalization 논문의 관례적 기대: 계층별 LOC(참고로 MetaTheory만 95개 파일이다), 전체/파일별
빌드 시간, `native_decide` 배치당 시간, 인증서별 생성 파일 크기·컴파일 시간, Mathlib 버전 고정
정보. 표 1에 두어 열 추가하는 것으로 충분하다. 현재 유일한 정량 데이터(2,832 identities /
15 batches)는 §9에 묻혀 있다.

### M10. 이중 익명성(double-blind)과 아티팩트
**해당 위치: §1(Contributions 문단의 GitHub 링크), 문서 서두 주석(acmart 전환 메모), 아티팩트(공개 저장소)**

- 헤더 주석대로 POPL 제출 시 `acmart, review, anonymous`로 전환해야 하는데, 본문
  Contributions[§1]의 `https://github.com/taeyool/lean-flag-algebras-release`는 저자 실명 계정
  링크다. 익명 아티팩트 링크(Zenodo anonymized 등)로 교체 필요.
- 공개 릴리스 저장소를 확인한 결과 **LICENSE 파일이 없다**. 아티팩트 평가(AEC) 대비 필수.
- 아티팩트 정리 제안: `Flagmatic/C5turan.lean`이 실제로는 `C5free_cert.json`을 컴파일하며
  (`C5turan_cert.json`은 같은 문제의 superseded 6×6 단일 블록 인증서로, 어느 .lean도 사용하지
  않음), 파일명이 혼동을 준다. 이름 정리 또는 README 설명을 권한다. [§5.4 표 1의 "Edge density
  / C₅" 행에 해당]

---

## 2. 논문 코드 ↔ 저장소 코드 대조 결과

### 2a. 불일치 (수정 또는 명시 필요)

| # | 논문 (해당 섹션) | 실제 코드 | 비고 |
|---|---|---|---|
| 1 | `labeledGraphListEqv` (§3.2) | `flagListEqv` (`FlagAlgebra/FlagDef.lean:772`) | 이름만 다름, 본문 동일 |
| 2 | `unlabel_labeledGraph` (§3.5) | `unlabeledGraph` (`FlagAlgebra/FlagOperators.lean:208`) | 이름만 다름 |
| 3 | `candidateMatches`, `candidateMatchesDecidable` (§4.1) | 라이브러리에 **없음**. 실제 메커니즘은 `predIsoSym2LabeledHl` + 익명 `DecidablePred` 인스턴스 (`Compute/FlagDensity.lean:716, 741`; 크기 기각 보조정리 `verts_card_of_coe_iso`는 실재 `:730`) | 두 이름은 `papers/POPL27/reflection_density_snippet.lean`에만 존재하는 논문용 단순화. 본문에 "일러스트용 단순화"임을 (셋 모두에 대해) 명시 권장 — 현재는 `sym2LabeledGraphDensity₁`에만 "illustrative" 표시가 있음 |
| 4 | `sym2LabeledGraphDensity₁` (§4.1) | 실제는 `sym2InducedLabeledSubgraphListDensity` (`FlagDensity.lean:970`) → `sym2FlagDensity₁` (`:1078`) | 위와 동일 사유. 스니펫 파일 내 이름도 `ReflectionDensitySnippet.sym2FlagDensity₁`로 논문과 다름 |
| 5 | `isoEmbeddingCount_Sym2LabeledGraph` (§4.2) | `isoEmbeddingCount_sym2LabeledGraph` (`Compute/Downward.lean:46`) | 대소문자 (S→s) |
| 6 | `downwardNormalizingFactor_Sym2LabeledGraph` (§4.2) | `downwardNormalizingFactor_sym2LabeledGraph` (`Compute/Downward.lean:94`) | 대소문자 (S→s) |
| 7 | `instance : Fintype (G1 ->g G2)` (§7.3) | 실제 인스턴스는 **`↪g`(임베딩)** (`Compute/Basic.lean:34`); `→g`(hom)용 Fintype 인스턴스는 없음 | 주석("retain the graph embeddings")과도 모순되는 오타 |
| 8 | `generate_pruned_*` 계열 (§5.2 Part 1) | 현재 `generate_forbid_free_*` (flags/mul), pruned 이름은 pair-density 하나만 잔존 | M4 참조 |
| 9 | `example : flagDensity₂ Sym2Flag_2_1_0_0.toFlag … = 1/2` (§4.2) | 실제는 브리지 상수를 쓰는 명명된 정리: `theorem flagDensity₂_Flag_2_1_0_0_Flag_2_1_0_1_Flag_3_1_0_1 : flagDensity₂ Flag_2_1_0_0 Flag_2_1_0_1 Flag_3_1_0_1 = 1/2` + `dsimp` 선행 (`MantelTheorem/FlagDensity.lean:194–200`) | rw+native_decide 패턴 자체는 일치 |
| 10 | `example : downwardNormalizingFactor Sym2Flag_3_1_0_1.toFlag = 2/3` (§4.2) | 라이브 코드에 이 리터럴 없음. 생성기(`Flags/FlagGenerator.lean:462–493`)가 배치 `native_decide`+투영으로 같은 사실을 생성; 손으로 쓴 형태는 Archive 전용 | 예시임을 명시 권장 |
| 11 | `def forbidLE …` (§3.6) | 실제는 `noncomputable def`이고 σ는 section variable; 코드 표기 `f ≤[H] g` 존재 (`Forbid/Basic.lean:101–109`) | 또한 논문 스니펫에서 `n₀`가 바인딩되지 않은 채 표시됨 — 스스로 선언한 "파라미터를 spell out한다"는 규약(§3 서두)과 어긋남 |
| 12 | `forbidLEWith` 스니펫 (§3.6) | 실제: positivity 가설이 이름 있는 바인더 `(hσ : φ₀ ⟨σ⟩₀ > 0)`, set-builder에 `: PositiveHomSpace σ` ascription 없음 (`Forbid/Basic.lean:72–77`) | `ℙ[φ₀]`가 notation+`Classical.choose`라는 사실은 M3 |
| 13 | `flagDensity₂ …` 인자 순서 (§4.2 본문 p(K₂•, K̄₂•; ·) vs Lean 예시 p(K̄₂•, K₂•; ·); 원 예시는 Example 2.4, §2.3) | — | 밀도의 순열 불변성으로 무해하나 각주로 언급하면 친절 |

### 2b. 정확히 일치함을 확인한 항목 (발췌, 소절별)

- **[§3.1]** `FlagType`(point-free abbrev), `LabeledGraph`(graph/type_embed),
  `LabeledGraphIso`(graph_iso/type_preserve, `infixl:50 " ≃f "`), `Flag`,
  `FinFlag`(`FlagWithSize` 경유의 `def`, Σ n:ℕ).
- **[§3.2]** `LabeledGraphList`, `labeledGraphListDensity`(`labeledGraphListCount`/
  `multinomialCoefficient`/`FintypeList`/`DecidableEqList` 모두 실재),
  `QuotLabeledGraphList`, `FlagList`(+`[F]ᶠ`, `[F,G]ᶠ` notation 실재), `FlagList.coe`,
  `flagDensity₁/₂`, `flagDensity_eq_sum_density_prods`(가설 hℓ₁/hℓ'/hℓ까지 일치).
- **[§3.3]** `FlagVector`, `basisVector`, `flagExpansion`, `zeroElement`, `zeroSet`,
  `ZeroSpace`, `flagVectorEqv`, `FlagAlgebra`, `flagMulWithSize`,
  `flagMul`(최소 크기 `F.1+F'.1−n₀`), `bilinearExtension`,
  `flagVector_mul_zeroSpace`, `flagMulWithSize_indep_on_size`(가설 `F₁.1+F₂.1 ≤ ℓᵢ+n₀` 일치).
- **[§3.4]** `FlagSeq`, `ConvergesTo`(`Increases`=StrictMono, `flagDensitySeq`), `Hom`,
  `PositiveHom`, `flagSeq_limit_mem_positiveHom`, `positiveHom_as_flagSeq_limit`,
  `FlagDensitySpace`, `PositiveHom.coe`, `semanticCone`, LE 인스턴스.
- **[§3.5]** `downwardNormalizingFactor(_labeledGraph)`, `isomorphismCount`, `unlabel`,
  `downwardFlag(Vector)(Quot)`, `linearExtension`, `downward`, `notation "⟦" f "⟧₀"`,
  `exists_probMeasure_extend_emptyType_positiveHom`(문장 verbatim, `⟨σ⟩₀` notation 실재),
  `downward_preserve_semanticCone`, `∅ₜ`(=`emptyType`).
- **[§3.6]** `ForbidCondition`(타입 별칭), `forbiddenCondition`/`familyForbiddenCondition`/
  `forbiddenFlags`(subgraph 포함 `IsContained` 사용),
  `generalizedTuranDensity_le_of_forbidLE`(`hc : 0 ≤ c` 포함), `SimpleGraph.toFlagAlgebra`.
- **[§4.1]** `Sym2Graph`/`Sym2FlagType`/`Sym2LabeledGraph`(**`SetLike.coe` 사용까지 일치**),
  `Sym2InducedLabeledSubgraph`(+`.edges`, filterMap 기반 Fintype 인스턴스),
  candidateMatches의 실제 메커니즘(`predIsoSym2LabeledHl`, 크기 기각), `sym2FlagDensity₁/₂`.
- **[§4.2]** `Sym2Flag`, `Sym2Flag.toFlag`, `flagDensity₁_eq_sym2FlagDensity₁`,
  `flagDensity₂_eq_sym2FlagDensity₂`, `downwardNormalizingFactor_Sym2Flag`,
  `downwardNormalizingFactor_eq`; 명명 규칙 `Sym2Flag_/Flag_/FlagAlgebra_{n}_{k}_{m}_{i}`
  (생성기 `Flags/FlagGenerator.lean:235–237, 395–427`에서 확인; §4.2 예시·§10 "Tactic
  metaprogramming" 문단·[부록* Lesson 3]의 서술과 부합).
- **[§4.3]** `generate_empty_typed_flags`/`generate_flags`의 존재와 인자 규약(n k m),
  실사용(`MantelTheorem/FlagDef.lean:21–25`); 배치 native_decide 메커니즘.
- **[§5.2 Part 1]** `Sym2EmptyTypedFlag`; `generate_subgraph_free_*` 4종.
- **[§5.2 Part 2]** `posSemidef_real_of_LDLt`; `psd_real_ldlt`(diagonal은 `fin_cases`+`norm_num`,
  인수분해 등식은 `decide +kernel` — 논문 서술과 정확히 일치).
- **[§5.2 Part 3]** `flag_expand_hfree N K hmem`(실사용:
  `flag_expand_hfree 3 K3 (completeSym2Graph_finFlag_mem_forbiddenFlags 3)`),
  `flag_expand_hfree_subgraph`(hmem 없음 — 논문 서술과 부합).
- **[§5.2 Part 4]** `forbidLEWith_add_QuadraticForm`(`FlagAlgebraVec`, `flagQuadraticForm` 실재),
  `reduce_downward_flagmul`, `expand_one_hfree_at`(+`_subgraph` 변형 — "the appropriate …
  tactic" 서술과 부합), `flagsum_ac_sort_rhs_pipeline`, `flag_nonneg`.
- **[§5.2 "The translator"]** `flagmatic_to_lean.py`의 `gen-skeleton`/`inspect` 서브커맨드와
  `--namespace`/`--force` 옵션, 인자 순서, LDLᵀ 계산, `M = R·Q'·Rᵀ` 재구성(JSON 필드
  `qdash_matrices`/`r_matrices`).
- **[§5.4]** 7개 생성 파일 모두 `Flagmatic/`에 체크인되어 있고 각각
  `-- Generator: … (gen-skeleton)` 헤더 보유(Mantel, K3forbidP3, K3forbidC4, K4turan,
  ErdosPentagon, K5turan, C5turan(=C5free cert)); 행렬 차원 8/6/5(오각형), 4/3(C₄),
  4×(8×8)(K₅, C₅) 모두 인증서 JSON 및 Lean `Matrix (Fin _)` 선언과 일치.
- **[§5.3+§5.4]** 라이브 코드에 활성 `sorry` 없음(주석 처리 2건, Archive 제외), 7개 생성
  파일에 axiom 없음 — 트러스트 모델·평가 절의 주장과 부합.
- **[§6]** `Turan_density_K3`(단, `turanDensity`는 Mathlib 정의 — 논문에 출처 언급 없음, 명시
  권장), `ErdosPentagon_Turan`/`ErdosPentagon_Turan_lowerBound`, `blowUp`(스니펫 verbatim;
  loopless는 auto-param으로 처리 — 실코드도 동일), `blowUp_K3_free`(`.Free`는 Mathlib
  `SimpleGraph.Free`), `subgraphCount_blowUp_C5_ge`(induced 카운트, `(Fin 5 → Fin n)` 단사
  구성 — 논문 서술과 일치), `Goodman_bound_on_triangle_density`(`K3 ≥ K2 * (2 • K2 - 1)`),
  `Goodman_theorem_on_Ramsey_multiplicity`(`O3 + K3 ≥ (1/4)•1`).
- **[§7.2]** `flagListDensity_HEq_eq`, `FlagList.permute`.
- **[§7.4]** `flagDensity_permute`, `flagDensity_insert_empty`, `setOfLabeledSubgraphListIsoHl`.
- **[§8]** `support_criterion`(`MetaTheory/SupportClosure.lean:139`),
  `blowupClosed_root_plantable`(`BlowupClosed.lean:530`),
  `heredClass_emptyType_rootPlantable`(`EmptyTypeCollapse.lean:180`),
  `c4free_not_rootPlantable`(`C4Free.lean:455`) — 4개 모두 실재, MetaTheory 전체 sorry 없음.
- **[§10]** graphon→hom 방향(`graphonHom`)만 있고 역방향은 명시적 가설(`hrep`)로 남아 있다는
  Related Work의 서술도 정확함.
- **[부록* Lesson 1]** `labeledGraphListCount_eq_sym2InducedSubgraphListCount` 실재
  (`Compute/FlagDensity.lean:200`).
- **[부록* Lesson 3]** `ac_sort_at_pipeline`/`sort_at` 실재, "10분 초과" 주석 verbatim
  (`ErdosPentagon/Lemmas.lean:445`).

### 2c. 권고
**해당 위치: §3 서두("expository version" 단서 문단), §5.3(Trust Model), §4.1(스니펫 파일)**

논문 §3 서두의 "expository version" 단서로 위 불일치 다수가 형식적으로는 면책되지만, §5.3
트러스트 모델이 "choices are **visible in the generated declarations**"라며 감사 가능성
(auditability)을 내세우는 만큼, **부록 또는 아티팩트 README에 '논문 표기 → 저장소 선언'
매핑 표**를 넣기를 강하게 권한다(위 2a 표가 그 초안이 될 수 있다). 또한
`papers/POPL27/reflection_density_snippet.lean`[§4.1의 스니펫 원본]이 실제 라이브러리를
import해 컴파일되는 훌륭한 장치이므로, lake 빌드/CI에 포함해 스니펫이 코드와 함께 검증되게
하면 좋다.

---

## 3. 수학·용어 세부 사항

1. **[§6; 관련 §2.1 그림 1]** **무정의 용어 `O₃`** (§6 "Additional Goodman-style consequences"):
   "O₃ + K₃ ≥ ¼·1"의 O₃(3정점 무변 그래프)가
   논문 어디에도 정의되지 않는다. 게다가 §2.1(그림 1)은 같은 그래프를 `K̄₃`로 표기한다. 코드
   이름(`O3 := FlagAlgebra_3_0_0_0`)을 따르려면 "O₃ (= K̄₃, the edgeless 3-vertex graph)"로
   1회 정의할 것.
2. **[§8]** **무정의 용어 "clone-closed", "true-clone-closed", "substitution-closed"** (§8
   "When root-plantability holds" 문단): 셋 다 정의 없이 등장한다. 각 1행 정의(독립집합
   파이버 / 완전그래프 파이버 / 임의 그래프 치환)면 충분하다.
3. **[§8]** **"non-degenerate" 정의 문구** (§8 "Random extensions and the root-planting
   space" 문단): "Assume that σ is non-degenerate for K:
   **equivalently**, there is some φ₀ ∈ Q₀ …" — 앞선 정의가 없는데 "equivalently"라고 쓴다.
   "that is" 또는 "meaning"으로 교체.
   **→ ✅ 반영 완료(2026-07-16, `400f8a5`):** "equivalently" → "that is" 교체 +
   `\emph{non-degenerate}` 강조 추가(정의부 표시). 대응 로그 참조.
4. **[§8]** **C₄-free 반례 문단** (§8 "Why the criterion is nontrivial"): "Every large C₄-free
   graph has o(n²) edges"는 Kővári–Sós–Turán(또는 Reiman) 인용이 필요하다.
5. **[§2.1 그림 1; §2.3–2.5의 예시들]** **기호 중의성**: 밑그래프가 P̄₃인 1-정점 타입 flag는
   두 개(뿌리가 고립점인 것 = 본문 그림의 E₃•류, 뿌리가 변 끝점인 것 = P̄₃•)인데, 그림 1과
   예시들은 그림으로 구분되지만 기호 `P̄₃•` 자체는 중의적이다. 각주 한 줄 권장. (검산 결과
   본문 계산 자체는 모두 옳다.)
6. **[§2.4; 관련 §3.6]** **Lemma 2.6 (semantic-bound)**: 이후 한 번도 참조되지 않는다(§3.6의
   전이 정리가 그 형식화 대응물인데 연결 언급이 없음). \Cref 한 번이면 독자에게 지도가 생긴다.
7. **[§3.1]** **FinFlag의 크기 범위**: 수학은 ⋃_{n≥k}, Lean은 Σ n:ℕ (n<k이면 빈 타입이라 무해).
   각주 권장.
8. **[§6]** **`blowUp`의 `[Fintype V]`**: 스니펫(그리고 실제 코드)에 있으나 정의에 불필요하다.
   사소하지만 정리 기회.
9. **[§6]** **Goodman 부등식 표기**: 논문 `K₂·(2K₂−1)` vs 코드 `K2 * (2 • K2 - 1)` (nsmul) —
   동치. 언급만 해 둔다.
10. **[§3.6]** **Definition 3.1 직후 배치**: 정의의 두 조건을 해설하는 문단("The first
    condition says…")이 Remark 3.2를 건너뛰고 나온다. 해설을 정의 바로 뒤로 옮기는 편이 읽기
    좋다.
11. **[Abstract ↔ §5.4]** **Abstract vs 표 1**: abstract는 사례를 4개(만텔, 오각형, Goodman,
    C₄)로 나열하나 표 1은 7개다. abstract에 "…, and further Turán-type edge-density bounds
    (K₄, K₅, C₅-free)" 식의 한 구를 추가하면 실제 기여가 더 잘 드러난다.
12. **[§5.4; 아티팩트]** **9번째/8번째 인증서**: `Flagmatic/Certificates/`에는 9개 JSON이 있다.
    논문의 7개 외에 (i) `K3forbidC6_cert.json` + `Flagmatic/K3forbidC6.lean` — **완전히
    작동하는 8번째 사례**(삼각형-free에서 C₆ 밀도, bound 92129/5242880), (ii)
    `C5turan_cert.json` — C5free와 동일 문제의 superseded 인증서(미사용). 전자는 표 1에
    추가할 후보이고(왜 제외했는지 최소한 각주), 후자는 아티팩트에서 제거/문서화 대상이다.
13. **[§7.3 ↔ §7.4]** **`let` vs `letI`**: §7.3의 첫 스니펫은 `let hS0 : Fintype S0 := …`,
    §7.4 스니펫은 `letI` — 인스턴스 바인딩이므로 `letI`로 통일이 자연스럽다.
14. **[§8]** **§8의 Lean 대응**: `support_criterion`은 순서(≤)가 아니라 비음성 술어
    (`QuotientNonneg`/`EnsembleNonneg`)의 동치로 형식화되어 있고,
    `blowupClosed_root_plantable`의 가설은 `0 < n₀`(+ `hc.constraintOf σ`) 형태다. 본문
    Theorem 8.2/8.3의 문구("for every pair f,g", "non-degenerate")와 Lean 진술의 정확한
    대응(비음성으로 충분한 이유, 비퇴화가 어디에 인코딩되는지)을 아티팩트 문서에 한 단락
    적어 주면 대조가 쉬워진다.

**검산 완료(이상 없음):** 곱셈 예시 Example 2.4의 곱(½P̄₃•+½P₃•)[§2.3], 만텔 핵심 부등식
(eq:mantel-key)의 다섯 항 전개와 downward 계수(1, ⅓, ⅔, ⅔, ⅓) 및 Step 2 산술(Example 2.10)
[§2.5], §5.1의 forward 유도[§5.1], q_σ(P̄₃•)=2/3[§4.2], 24/625 하한 부등식
(n⁵/C(5n,5) ≥ 24/625)[§6], 표 1의 5개 bound의 극단 그래프 정합성(K_{n/2,n/2} 등)[§5.4],
fit 조건[§2.2], sum-to-one 항등식(eq:sum-to-one)[§2.4], 다운워드 정규화 인자 정의(분모
m(m−1)⋯(m−k+1))[§2.5].

---

## 4. 통계 수치 검증 (§9)

**해당 위치: §9("Can the computational layer scale beyond five vertices?" 문단); 동일 수치가 [부록* Lesson 6]에도 등장**

"the three flag types require **1,800, 672, and 360** pair-density theorems … **2,832**
identities in **15** native-evaluation batches":

- 저장소 파일에는 1,800/672/360 리터럴이 없다(빌드 시 `logInfo`로만 출력). 총합 2,832와
  "~15 batches"는 `FlagAlgebra/Compute/DENSITY_COUNT_REFACTOR_ROADMAP.md:117` 및
  `Flags/Densities/DensityThmGenerator.lean:493`의 주석으로 뒷받침된다.
- **독립 재검산 결과 세 수치는 정확하다.** 오각형 인증서(N=5, K₃-free)의 세 타입은 3정점
  삼각형-free 그래프(K̄₃, P̄₃, P₃)이고 패턴 크기 4, 호스트 크기 5다. 타입별 크기-4 flag 수는
  8/6/5(= 표 1[§5.4]의 블록 차원과 일치), 대각 포함 무순서 패턴쌍은 36/21/15, 삼각형-free
  크기-5 호스트 flag는 각각 50/32/24개로, 36·50=1,800, 21·32=672, 15·24=360이 성립한다.
- 제안: 이 파생(타입별 flag 수 8/6/5 → 쌍 36/21/15 → 호스트 50/32/24)을 논문이나 아티팩트에
  한 줄 남기면 재현 검증이 쉬워진다. 빌드 로그를 아티팩트에 포함하는 것도 방법.

---

## 5. 참고문헌

1. **[참고문헌; 인용: §10]** **[gowers2025marton] 저자 오기: "D.~Green" → "B.~Green"**
   (Ben Green). 서지 확인: W. T. Gowers, B. Green, F. Manners, T. Tao, *On a conjecture of
   Marton*, Ann. of Math. 201(2):515–549, 2025 — 권·호·쪽수는 정확함.
2. **[참고문헌; 인용: §1, §2.4(Example 2.8)]** [hatami2012] 키는 2012인데 출판 연도는 2013
   (JCTA 120(3):722–732, 2013). 서지 자체는 정확하니 키만 정리 여부 판단.
3. **[참고문헌; 인용: §5 도입·§5.1·§10]** [vaughan2013flagmatic]
   `github.com/jsliacan/flagmatic-2.0` 실재 확인 — OK.
4. **[참고문헌; 인용: §10, §11]** [freer2026graphon] `github.com/cameronfreer/graphon` 실재
   확인, 본문 서술(cut distance, (weak) regularity, counting/inverse counting, compactness,
   수렴 동치)이 해당 저장소 README와 부합 — OK.
5. **[참고문헌; 인용: §2.4(Theorem 2.5)]** [lovasz2006limits] 서지 정확. 다만 M7의 귀속 문제
   참조.
6. **[참고문헌; 인용: 주로 §10]** 나머지(razborov2007/2013, dillies2022, mehta2022,
   subercaseaux2024, pfr2023, chlipala2013, cohen2013, harrison2007, parrilo2003, ebner2017,
   lovasz2012) 표본 검증에서 문제 없음. `\cite`↔`\bibitem` 상호 무결성 확인(고아/미사용 없음).

---

## 6. 오탈자·표기·LaTeX

1. **[§4.1]** l.2529: "exactly this **conditon** for tuples" → "condition".
2. **[§3.6; 관련 §3 서두 규약]** `forbidLE` 스니펫: `{m : ℕ} {σ : FlagType (Fin n₀)}`에서
   `n₀`가 바인딩되지 않음(자체 규약대로면 `{n₀ m : ℕ}`). `forbidLEWith` 스니펫도 σ, n₀ 바인더
   부재 — §3 서두의 "we spell them out at the definitions where they are used"와 어긋나는 두 곳.
3. **[§7.3]** 리스트링의 `G1 ->g G2` → `↪g` (2a-7과 동일 항목, 오타로도 분류).
4. **[전문(preamble)]** 미사용 draft 매크로 `\gw`, `\sh`, `\hy` — 제출 전 제거(본문 사용 0회
   확인).
5. **[문서 전반]** 라벨 위생: 중복 라벨 없음, 깨진 참조 없음(스크립트 검사). 미참조 라벨
   16개(대부분 §5의 legacy alias와 sec:intro 류) — 정리 선택 사항.
6. **[문서 전반/빌드]** LaTeX 로그에 stale-run 미해결 참조 경고가 있으니 최종본은 latexmk
   재실행으로 확인 (overfull hbox 0건은 양호).
7. **[문서 전반, 특히 §5]** 문체: "flag algebra"와 "flag-algebra"(수식어)의 하이픈 사용은
   대체로 일관되나 §5에서 몇 회 혼용. 통일 권장.
8. **[§5.1 각주 ↔ §2.3]** §5.1의 각주("Strictly, each picture denotes …")와 §2.3의
   bracket-omission 규약이 사실상 같은 내용을 두 번 설명 — 한쪽에서 다른 쪽을 참조해도 됨.

---

## 7. 저자 확인 질문 (Questions)

1. **[§3.5–3.6]** `ℙ[φ₀]`(=Classical.choose) 선택과 무관하게 `forbidLE`의 의미가 결정됨(측도
   유일성)을 Lean에서 증명했는가? (`MetaTheory/MeasureUniqueness.lean`이 있는 것으로 보이는데,
   코어 `Forbid` 계층이 그것에 의존하는가, 아니면 메타 수준 보증인가?)
2. **[§3.6, §5.2 Part 3, §6, §11]** 오각형·P₄ 상한이 induced 판(`≤ᵢ`)으로 진술된 이유와, 논문
   Definition 3.1(subgraph 판)과의 브리지(`inducedForbidLE_toFinFlag_imp_forbidLE`)를 본문에서
   다룰 계획이 있는가? (M2)
3. **[§5.4]** `K3forbidC6`(8번째 완성 사례)를 표 1에서 제외한 이유는? 지면 문제라면 각주로라도
   존재를 언급하는 것이 커버리지 주장에 유리하다.
4. **[§4.3, §5.2 Part 1]** `generate_*` 커맨드 개명(M4) 이후 논문 스냅샷 커밋을 아티팩트에
   고정할 계획은?
5. **[§4.1; 아티팩트]** `papers/POPL27/reflection_density_snippet.lean`을 CI에 포함해
   스니펫-코드 동기화를 기계적으로 보장할 수 있는가?
6. **[§9]** §9의 "1,800/672/360"은 빌드 로그 수치로 보이는데(파일에는 없음), 아티팩트에 로그
   또는 파생 근거를 포함할 수 있는가? (본 심사에서 조합론적으로 재확인은 했음 — §4 참조)

---

## 8. 검토 방법 요약 (for the record)

- 논문 4,665행 전문 정독. 상호참조/인용 무결성은 스크립트로 검사(중복·깨짐 0건).
- 논문에 등장하는 Lean 선언 약 60개, elaboration 커맨드 16개(전수), 택틱 10개, 번역기
  서브커맨드/옵션, 인증서 JSON 9개, 생성 Lean 파일 8개를 저장소 HEAD와 대조(파일:행 단위).
- 수식 검산: §2 예시 전부, §5.1 유도, 하한 산술, 표 1 bound 정합성, §9 통계의 조합론적
  재계산.
- 외부 사실 확인: Marton 논문 서지(Annals 201(2)), flagmatic-2.0/graphon/릴리스 저장소 실재
  및 내용.
