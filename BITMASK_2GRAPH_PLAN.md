# 2-graph 비트마스크 파이프라인 — 타당성 평가 및 계획

> 출처 분석: `lean-tetrahedron-turan-private`의 order-7 tetrahedron 인증서 파이프라인
> (`Core/Compute/Mask3.lean`, `Core/Compute/MaskInj.lean`, `Core/Examples/TetrahedronOrder7*.lean`)
> 을 읽고, `lean-flag-algebras`의 현재 2-graph 파이프라인
> (`FlagAlgebra/Compute/*`, `Flags/ForbidFree*`, `FORBID_PRUNING_ROADMAP.md`)과 대조한 결과.
> 작성일: 2026-08-21. 코드 변경 없음 — 계획 문서.

## 결론 요약

**적용 가능하다. 구조적 장애물은 없고, 오히려 절반은 이미 준비되어 있다.**
`Mask3.lean`에는 pair 랭크 함수 `pairIdx`가 이미 정의되어 있고 n=6,7에 대해
kernel 검증까지 되어 있다 (`finPairs 7 → List.range 21`). 3-graph용 기법의
2-graph 포팅은 triple→pair 치환의 기계적 작업이 대부분이다.

기대 효과의 핵심:
1. **host N=7 2-graph 계산이 확실히 사정권에 들어온다** (현재 예제는 N≤6).
   n=7 전체 마스크 스윕은 2^21 leaf로, tetrahedron 레포에서 이미 성공한
   2^20 스윕의 정확히 2배 규모.
2. **native_decide 없는 kernel-only 완전성 증명** (`Lean.ofReduceBool`,
   `Lean.trustCompiler` 축 제거)이 가능해진다.
3. n=8은 full sweep 불가(2^28, 실증 규모의 256배) — tetrahedron이 order-7에서
   쓴 2단계 방식(kernel sweep + native 확장 체크)으로만 접근 가능.

## 1. 기법이 실제로 하는 일 (tetrahedron 레포 분석)

용어 정리: "order-7" = 7-vertex 호스트 크기. 파이프라인은 두 층으로 나뉜다.

### (a) 6-vertex 층 — kernel 비트마스크 완전성 스윕 (핵심 기법)

- **표현**: 3-graph on n vertices = 자연수 하나. bit `triIdx n a b c`
  (닫힌 식으로 된 사전식 랭크)가 hyperedge {a,b,c}의 존재를 기록.
  `graphOfMask`/`maskOfGraph`로 `Sym3Graph`(Finset 기반)와 왕복, 라운드트립·단사성 증명 완비.
- **금지 그래프 검사**: 미리 계산한 위치 테이블(`quadIdxList`)에 대해 순수 testBit만으로
  판정 (`k4FreeMask`). hot path에 Finset/Fin 연산 없음.
- **동형 전송**: 단사 정점 사상 + 비트 대응 검사(`scanOK`)만으로
  `IsIso (graphOfMask m) (graphOfMask h)`를 얻는 정리 (`isIso_graphOfMask_of_bits`).
  각 인스턴스는 kernel `decide`로 판정 가능.
- **완전성 스윕**: `sweepMasks` — 비트에 대한 이진 트리로 2^20개 마스크 전부에
  leaf 판정 실행. 32개 파일 × 32개 lemma(각각 depth-10, 1024 마스크)로 쪼개
  `decide +kernel`로 병렬 빌드, `sweepMasks_of_pieces`로 조립.
  선언 단위로 쪼개는 이유: kernel 평가 캐시가 선언 사이에 해제되어 메모리를 수 GB 이하로 유지.
- **witness 테이블**: 각 마스크에 "어느 순열로 어느 대표에 붙는지"를 packed 자연수
  리터럴로 제공 (`TetrahedronOrder7Witness.lean`, 약 3.1 MB — 2^20 × 10 bit).
  테이블 자체는 외부에서 생성한 **비신뢰 데이터**이고, 스윕이 검증한다.
  720개 순열의 rank map 일관성은 일회성 검사(`permConsistent_of_lt`)로 담보.
- **결과**: "모든 K4-free 6-vertex 3-graph는 나열된 대표 중 하나와 동형" —
  admissible graph 열거의 완전성이 추가 축 없이 kernel로 증명됨.

### (b) 7-vertex 층 — native_decide 확장 체크

C(7,3)=35 bit라 2^35 full sweep은 불가. 7-vertex 조합론은 6-vertex 대표들로부터의
**확장 열거**(~3.2×10⁷ integer column을 native_decide로 평가)로 처리.
README 축 표가 명시하듯 이 층만 `ofReduceBool`/`trustCompiler`를 진다.

## 2. 2-graph 적용 가능성 판정

| 항목 | 판정 | 근거 |
|---|---|---|
| 랭크 함수 | **이미 있음** | `pairIdx` in `Mask3.lean:44`, n=6,7 kernel 검증 완료 |
| mask↔graph 브리지 | 기계적 포팅 | `graphOfMask`/`maskOfGraph`/`MaskInj`의 pair 버전. `sort3`→`sort2`(min/max)로 오히려 단순해짐 |
| 금지 검사 테이블 | 기계적 | K₃ = 삼각형별 3개 pair 위치 테이블 (n=7이면 C(7,3)=35 entry). 임의의 induced-F도 위치 테이블 방식 그대로 가능 |
| 동형 전송 정리 | 기계적 포팅 | `isIso_graphOfMask_of_bits`의 pair 버전 |
| n=7 full sweep 규모 | **실증된 규모의 2배** | 2^21 leaf vs 실증 2^20. leaf당 비용도 비슷(35 triple 검사 + 21 bit scan vs 15 quad + 20 bit scan) |
| witness 테이블 | 생성기 필요 | 2^21 × 13 bit(7!=5040) ≈ 추정 8 MB Lean 리터럴. 외부 스크립트로 생성, 스윕이 검증 |
| n=8 full sweep | **불가** | 2^28 = 2.7×10⁸ leaf, 실증 규모의 256배. 2단계 방식으로만 접근 |
| 기존 파이프라인 연결 | 추가 작업 | `Sym2Graph`/`genSym2Graphs` JSON 인덱스 순서와의 호환 레이어 필요 |

### 설계 포인트: forbid-무관 스윕이 더 낫다

tetrahedron 스윕은 K4-free 마스크만 정준화하지만, 2-graph n=7은 전체 동형류가
**1044개**뿐이므로 forbid 없이 "모든 2^21 마스크 → 1044 대표" 스윕 한 번이 낫다.
그러면 임의의 forbid는 1044개 대표에 대한 필터로 처리되어, **스윕 한 번이 모든
문제(K₃-free, K₄-free, C₄-free, …)에 재사용**된다. tetrahedron처럼 forbid별
스윕을 다시 돌릴 필요가 없다.

### 주의: 트리 가지치기(pruning)의 한계

`sweepMasks`는 전 마스크를 방문한다(비-free 마스크는 leaf에서 trivially 통과).
n=8을 노리고 "고정된 상위 비트에 이미 금지 그래프가 있으면 서브트리 통째로 스킵"
하는 가지치기를 넣으려면 금지 술어의 **비트 추가에 대한 단조성**이 필요 —
K_r(subgraph=induced 일치)는 가능하지만, 일반 induced-F는 비단조라 불가.
현 파이프라인의 D1(induced 의미론)과 충돌 지점이므로 n=8 시도 시에만 고려.

## 3. 기대 효과 (정량)

그래프 수 스케일:

| n | labeled 2^C(n,2) | 동형류 | K₃-free 동형류 |
|---|---|---|---|
| 6 | 32,768 | 156 | 38 |
| 7 | 2,097,152 | 1,044 | 107 |
| 8 | 268,435,456 | 12,346 | 410 |

1. **범위 확장**: host N=7 인증서가 실현 가능해짐. flagmatic 2-graph 결과의
   상당수가 N=7에서 나오므로(더 좋은 bound), 실질적 도달 범위 확대.
2. **축 제거**: 현재 모든 Flagmatic 예제는 native_decide 의존. 열거/완전성 층을
   kernel 스윕으로 대체하면 해당 부분이 축-무결해짐. (roadmap 9b가 지목한
   ~47 s native 컴파일 고정비용도 해당 층에서는 사라짐.)
3. **속도**: 현재 n=7 empty-typed 생성은 keyed dedup으로 83 s(native).
   마스크 스윕은 빌드 시간이 들지만 **한 번 빌드해 캐시되면 모든 문제가 재사용**.
   iso-dedup(roadmap이 지목한 진짜 병목)이 hot path에서 완전히 사라진다.
4. **한계 인지**: typed example의 지배 비용(pair-density native_decide, mul simp —
   roadmap 9b)은 이 작업이 직접 해결하지 않는다. 다만 order-7 파일들의
   `Induce5`/`CellWeight` 패턴처럼 density 계산 자체를 비트 레벨로 내리는
   후속 작업의 토대가 된다.

## 4. 리스크

- **witness 생성기**: 2^21 마스크 각각의 정준 대표·순열 인덱스를 뽑는 외부 스크립트
  (Python/C++) 신규 작성. 신뢰할 필요는 없지만(스윕이 검증) 만들어야 한다.
- **빌드 메모리/시간**: 8 MB 리터럴 + 1024×2개 `decide +kernel` lemma.
  tetrahedron과 같은 파일 분할 전략 필수. 실제 벤치 전까지 총 빌드 시간 불확실
  (0단계에서 측정).
- **두 레포의 이질성**: tetrahedron 레포는 자체 `RelTheory`/`Sym3Graph` 코어를 쓰고,
  lean-flag-algebras는 `Sym2Graph`+JSON 순서 호환에 묶여 있다. 포팅은 코드 복사가
  아니라 lean-flag-algebras의 타입에 맞춘 재구현이며, 완전성 정리를 기존
  `genSym2Graphs`/`prunedFreeFlags` 자리에 꽂는 어댑터 정리가 필요.
- **Lean/Mathlib 버전 차이**: 두 레포의 toolchain이 다를 수 있음(포팅 시 확인).

## 5. 단계별 계획

- `[x]` **0. 벤치 기준점.** tetrahedron 스윕을 직접 재지 않고 n=5/n=6 파일럿으로
  실측 대체: n=5 전체(2^10) 13 s, n=6 스윕 조각당(2^13) ~150 s → 2^15 전체
  ~600 CPU-s (4파일 병렬 wall ~3분). n=7(2^21) 추정 ≈ 18 CPU-h (병렬화 필수).
- `[x]` **1. Mask2 코어 포팅.** DONE — `LeanFlagAlgebras/BitMask/Mask2.lean`
  (사용자 지시로 두 레포를 연결하지 않고 독립 재구현). `pairIdx`(+kernel 검증
  examples n=3–8), `graphOfMask₂`/`maskOfGraph₂`/라운드트립/전사성
  (`exists_mask_graphOfMask₂`), `sort2`, 동형 전송 `graphOfMask₂_eqv_of_bits`
  (기존 `sym2GraphEqv_of_equiv`를 통해 **`∼sf`에 직접 착지** — 기존 파이프라인
  타입과 바로 호환), `sweepMasks`/`_spec`/`_of_pieces`(그대로 이식), 제네릭 체커
  (`pv`/`permFn`/`rankApply`/`scanOK`/`permConsistent`/`leafParts_eqv`,
  n ≤ 8 지원 패킹: 정점 3 bit, 랭크 5 bit). 첫 컴파일에 클린 통과.
- `[x]` **2. n=5 + n=6 파일럿.** DONE — **go/no-go 게이트 통과(go)**.
  - 데이터 생성기 `BitMask/gen_canon.py`(orbit 기반; 비신뢰 데이터, 스윕이 검증)
    + `gen_sweep6.py`(스윕 조각 파일 생성).
  - n=5: `Canon5Data.lean` + `Canon5.lean` — 1024 마스크 전체 kernel 스윕,
    34개 대표(정확히 5-vertex 동형류 수) 완전성. 빌드 13 s.
  - n=6: `Canon6Data.lean` + `Canon6Checker.lean`(35 s; 720개 순열 rank-map
    일관성 kernel 검증) + `Canon6Sweep0–3.lean`(각 8 × depth-10 `decide +kernel`,
    각 ~146–170 s, 병렬) + `Canon6.lean`(조립). 최종 정리
    `canon6_complete : ∀ G : Sym2Graph 6, ∃ h ∈ reps6, G ∼sf graphOfMask₂ 6 h`.
    156개 대표 = 6-vertex 동형류 수와 일치.
  - **Axiom 검증: 두 완전성 정리 모두 `[propext, Classical.choice, Quot.sound]`만
    의존** — `native_decide`(`ofReduceBool`/`trustCompiler`) 없음. 목표한 축 제거 달성.
  - aggregator(`LeanFlagAlgebras.lean`)에 BitMask 모듈 등록, 전체 빌드 그린.
  - **미완(스코프 이월)**: 기존 `genSym2Graphs 6` 인덱스 순서와의 브리지 lemma,
    Mantel 재증명 어댑터 — Task 4로 이월.
- `[x]` **3. n=7 스윕.** **DONE (2026-08-21)** — `canon7_complete : ∀ G : Sym2Graph 7,
  ∃ h ∈ reps7, G ∼sf graphOfMask₂ 7 h`, kernel-only(3-axiom 확인). 2^21 = 2,097,152
  마스크 전체를 64개 파일 × 32개 depth-10 `decide +kernel`로 스윕. **실측**: leaf당
  13 ms (n=6의 18 ms보다 개선 — rep-인덱스 O(1) 비교 + 행 단위 조회 덕), 조각 파일당
  427 s, 총 ≈ 7.6 CPU-h; 28코어/64 GB 머신에서 14개 배치 병렬(프로세스당 ~2.8 GB,
  총 ~45 GB 피크)로 **wall ~70분**. n=7 브리지 인스턴스(`maskFreeFlags7_toFinset_eq`,
  K₃-free 107개 kernel 카운트) 포함, aggregator 등록. 설계 교훈 반영 내역:
  - **대표 패킹**: `repsPacked7`(21 bit × 1044를 한 ℕ에) + witness에 rep 인덱스
    동봉(entry = permIdx 13 bit | repIdx << 13, 24 bit/mask) → leaf의 대표 확인이
    O(1) 시프트 비교. `repAt_eq_getD`/`repAt_mem`으로 리스트 멤버십에 연결.
  - **테이블 행 단위화**: perms/rankMaps를 30개 행 단위 중첩 리스트로(조회 ≤200
    스텝); witness chunk는 64행 × 32chunk × 1024마스크 × 24 bit.
  - 산출물: `gen_canon.py 7`(orbit 방식, ~4분) → `Canon7Data*.lean` 총 ~14.7 MB
    (W 파일 8개 분할); `gen_sweep7.py` → `Canon7Sweep00–63.lean`(각 32×depth-10
    `decide +kernel`) + `Canon7Glue.lean`; `Canon7Checker.lean`(168행 순열 검증을
    6개 그룹 lemma로) + `Canon7.lean`(reflection·완전성·브리지 인스턴스·K₃ 107개
    kernel 카운트). **주의: 대형 리스트 리터럴 파일은 `set_option maxRecDepth
    100000` 필요**(엘라보레이터 재귀 한도).
  - 남은 것: 64개 스윕 파일 빌드(예상 10–20 CPU-h, 병렬 wall 1–3h) + Canon7 최종
    빌드 + axiom 확인 + aggregator 등록.
- `[~]` **4. 파이프라인 연결.** **4a (theorem-level) DONE (2026-08-21)** —
  `BitMask/MaskBridge.lean`:
  - 제네릭: `maskRepFlags_toFinset_eq_univ`(대표 디코딩 = 전체 flag 완전성),
    `maskFreeFlags_toFinset_eq`(임의 forbid `F`에 대해 필터된 대표 디코딩 =
    `univ.filter (sym2EmptyTypeFlagDensity₁ ⟦F⟧ · = 0)`) — RHS가
    `prunedFreeFlags_toFinset_eq`와 동일해 **drop-in 대체 가능**. 둘 다 스윕
    완전성 가설로 파라미터화 (n=5/6/7 인스턴스 즉시 생성).
  - 비트 레벨 삼각형 검사: `triTable n`/`triFreeMask` + 정렬 witness 보조정리
    `hasTri_iff_sorted` + 테이블 가설(cover/sound, per-n `decide`)로 파라미터화한
    `triFreeMask_iff`. 제네릭 `decide (inducedContains …)`는 kernel에서 n=5 ~12 s,
    n=6 ~분, n=7 불가 수준이라 비트 검사가 스케일 핵심.
  - K₃ 인스턴스: `k3FreeReps5/6`(kernel 카운트 14/38 — 로드맵 수치와 일치),
    `k3FreeFlags5/6_toFinset_eq`. **전부 3-axiom(kernel-only) 확인.**
  - **4b (command surface) DONE (2026-08-21, 삼각형 forbid 한정)**:
    - 새 옵션 `flagGen.maskCompleteness` (`Flags/GeneratorOptions.lean`):
      `generate_forbid_free_empty_typed_flags`의 완전성 증명을 스윕 경로로 전환.
      기존 `flagGen.kernelDecide`는 pruned generator를 kernel로 돌려야 해서 n≤3
      전용이었는데, mask 경로는 n=5/6/7에서 kernel 증명을 실현.
    - 증명 레시피 (`runForbidFreeEmptyTypedClique`의 새 분기): 방출된 그래프
      리스트에 대해 두 개의 **Bool-레벨** side condition을 `decide +kernel`로 —
      (i) `hbitfree`: 각 그래프의 마스크가 `triFreeMask` 통과, (ii) `hbitcover`:
      모든 자유 대표가 `map canonOf`에 포함 — 그리고
      `emittedFreeFlags_toFinset_eq` + `hfree/hcover_of_triFreeMask` +
      `eq_triangleGraph`으로 마감. JSON 인덱스 상수(`Sym2Graph_n_0_0_i`)는 그대로
      유지되어 하위 파이프라인과 완전 호환.
    - **핵심 성능 교훈**: Prop `∀ _ ∈ _` decidable 인스턴스 체인은 kernel에서
      Bool `List.all`보다 ~18배 느림 (n=6 실측 ~90 s vs ~5 s) — side condition은
      반드시 sweep-leaf 스타일 Bool로. 또 `hasClique`(powerset 열거)·decode된
      Finset 연산도 kernel에서 무거워 전부 마스크/비트 레벨로 회피.
    - **검증** (`BitMask/MaskWiringTest.lean`, aggregator 등록): n=5 (14.6 s),
      n=6 (73 s, `flagGen.kernelDecide`와 병용) — 생성된 `sym2FlagSetHfree_…_eq`,
      `flagSetHfree_…_eq`, `flagSetHfree_…_val_eq` **전부 3-axiom**. 즉 empty-typed
      생성 층 전체가 kernel-only.
    - 한정/남은 것: 삼각형(completeSym2Graph 3) forbid만 — K₄/K₅는 clique 위치
      테이블(`triTable` 일반화, `hasClique_iff_sorted`류 정리)로 동일 패턴 확장
      가능. n=7은 증명 경로는 준비됐으나 커맨드의 elaboration 단계
      `evalCanonicalEdgeLists 7`(전체 1044클래스 native 열거)이 지배 비용 —
      마스크 대표를 직접 상수로 쓰는 전용 커맨드(JSON 인덱스 탈피)가 후속 과제.
      σ-typed/pair-density/mul 층의 native_decide는 Task 5 영역.
- `[~]` **5. density 비트화.** **5a (empty-typed 단일 패턴) DONE (2026-08-27)** —
  `BitMask/Density.lean` + `DensityTest.lean` (aggregator 등록).
  - **설계**: N ≤ 7에서 부분집합 열거는 `Finset (Finset (Fin N))`(≤128개)로 두고
    부분집합당 검사만 비트화. `vtxList`(finRange filter — **`Finset.sort`는
    mergeSort=WF 재귀라 kernel 환원 불가**, 정렬 불필요한 filter로 대체),
    `extractMask`(유도 부분그래프의 마스크 추출), `maskCount`.
  - **의미론 체인** (전부 sorry-free): `nonempty_extractIso`(추출 마스크의 디코딩
    ≃f V의 유도 부분그래프 — orderEmbOfFin 라벨링), `coe_iso_iff_extract_eqv`
    (placement 판정의 마스크 형태), `maskOfGraph₂_graphOfMask₂`(mask→graph→mask
    왕복, cover 가설), `eqv_iff_canonOf_eq`(**대표 distinctness ⟹ 정준형 완전
    불변량** — 유일성 문제 해결!), `listCount_eq_maskCount`(count 브리지, Fin-1
    placement와 부분집합의 card_bij), `sym2EmptyTypeFlagDensity₁_eq_maskCount`.
  - **m=5 인스턴스**: `reps5_distinct`(34² 쌍 kernel, `isEmptyIsoFast_bool` —
    이미 kernel 친화 설계였음) + `acc_canon5_spec` + `density₁_eq_maskCount5`.
    Density.lean 전체 빌드 33 s.
  - **검증**: C₅ 패턴 in (C₅+고립점) 호스트 = 1/6 — native `#eval`과 일치,
    kernel 증명 `density_val` **3-axiom**, 12 s.
  - **5a-확장 DONE (2026-08-27)**: 인스턴스 층 제네릭화(`distinct_of_bool(_deg)`,
    `acc_canon_spec`, `density₁_eq_maskCount_canon`) 후 m=2,3,4 미니 스윕
    (`Canon{2,3,4}Data` + `CanonSmall.lean`, 14 s) + m=6 인스턴스(`Density6.lean`).
    m=6 distinctness는 **degKey 프리체크 필수** — edge-card만 거르는
    `isEmptyIsoFast_bool` 직행은 같은 변 수의 비동형 쌍마다 720 순열을 소진해
    20분+에도 안 끝남; degKey 버킷팅으로 **410 s** 일회성 통과. m=7(1044²)은
    필요해질 때까지 보류. 검증(`DensityTest.lean`): 변밀도(C₅)=1/2,
    삼각형밀도(K₄)=1, C₅밀도=1/6, **C₆밀도(K3freeC6 target)=1** — 전부 3-axiom.
    이로써 패턴 크기 2–6 전 구간에서 empty-typed density가 kernel 계산.
  - **(5b) 진행 중 — 기반 층 DONE (2026-08-27, `BitMask/RootedMask.lean`)**:
    - `RootsMatch`(마스크의 루트-간 비트 = σ의 변) + `labeledGraphOfMask`
      (루트를 0..k−1에 둔 마스크의 σ-typed 디코딩, type_embed = `Fin.castLE`)
      + `labeledGraphOfMask_adj_iff`;
    - **rooted 전송** `labeledGraphOfMask_eqv_of_bits`: 루트를 점별 고정하는
      단사 사상 + 비트 대응 → **라벨 보존** `∼sf` (rooted 스윕의 leaf가 증명할
      형태; Mask2는 건드리지 않고 edge-transport 코어를 국소 복제 — Mask2 변경은
      스윕 전체 리빌드(7.6 CPU-h)를 유발하므로 금지);
    - **rooted 추출** `rootedVtxList`(루트 먼저 type_embed 순, 비루트 오름차순 —
      finRange filter; 루트 판정은 `∃ t, type_embed t = v` decide — `type_verts`
      자체는 Set 기계라 kernel 환원 불가) + `rootedExtractMask`(**min/max 정렬
      필수** — 루트-우선 리스트는 비단조!) + testBit/lt/getD(root·nonroot) 성질;
    - `rootedExtractMask_rootsMatch`: 모든 placement의 추출은 RootsMatch —
      항상 디코딩 가능.
    - **라벨 추출-iso DONE (2026-08-27, `BitMask/RootedDensity.lean`)**:
      기수 보조정리(`type_verts_card`/`k_le_of_placement`/`sdiff_card`) +
      `rootedVmap`(i<k ↦ type_embed i, 이외 ↦ (V\T)의 orderEmbOfFin) 단사·전사 +
      `labeledCoe_adj_iff_mem`(라벨 coe 인접 = ambient 변 멤버십) +
      **`nonempty_rootedExtractIso`**(rooted 추출의 디코딩 ≃f V의 라벨 유도
      subflag — type_preserve는 vmap 구성 + `LabeledSubgraph.embed_eq`로) +
      `labeledIso_trans`(기반 라이브러리에 없던 ≃f 합성) +
      **`labeledCoe_iso_iff_rootedExtract_eqv`**(rooted placement 판정의 마스크
      형태 — unrooted `coe_iso_iff_extract_eqv`의 라벨판, count 브리지가 소비할
      바로 그 정리).
    - **rooted canon 스윕 DONE (2026-08-27, `BitMask/RootedCanon.lean`)**:
      gen_canon에 `rooted <k> <m>` 모드(kfix — root-fixing 순열만; orbit 방식
      그대로), 데이터 `RCanon{k}_{m}Data.lean` — (1,2): 대표 2, (1,3): 6,
      (2,3): 8, (2,4): 40 (전부 검산 일치). 제네릭 조각: `permFixesRoots` +
      `permFn_fixes_of_permFixesRoots` + `sort2_of_le` +
      **`rleafParts_eqv`**(일관성+루트고정+scan → RootsMatch 전달 + 라벨 ∼sf —
      **σ에 대해 한 번에**, 스윕은 σ-무관). 4개 조합 각각 leaf/스윕/`rleaf_reflect`
      kernel 검증. (2,6)(K3freeC6 크기-6 flag)은 같은 템플릿 + 분할 스윕으로 후속.
    - **t=1 라벨 count 브리지 DONE (2026-08-27, `BitMask/RootedCount.lean` +
      `RootedCountTest.lean`)**: full-placement 보조정리(`nonempty_coe_univ_iso`),
      패턴 정규화(`rootedMaskOf` = 자기 자신에서의 univ-추출 +
      `eqv_decode_rootedMaskOf`), `rmaskCount`(루트 포함 부분집합 필터 — 루트
      판정은 kernel-환원 가능한 image 형태), **`labeledListCount_eq_rmaskCount`**
      (card_bij) + **`sym2FlagDensity₁_eq_rmaskCount`**(밀도 = count /
      multinomial (m−k) over (N−k)), 유일성 `eqv_iff_rcanonImage_eq`(reflect+dist
      가설로 패키징; RootsMatch-proof 교체는 정의적 proof-irrelevance로 공짜).
      **검증**: (1,2) 조합 — rooted K₃ 호스트에서 rooted edge flag의 σ-typed
      밀도 = 1, native `#eval` 일치, **3-axiom**. k=1은 `rootsMatch_one`으로
      RootsMatch가 공허 참이라 인스턴스화가 특히 가벼움.
    - **t=2 쌍 브리지 DONE (2026-08-27)** — **5b의 목표 정리 달성**:
      `rmaskCount₂`(루트 포함·루트 밖 서로소 부분집합 쌍의 비트 카운트) +
      `labeledListCount₂_eq_rmaskCount₂`(Fin 2 placement ↔ 쌍 card_bij; per-V
      판정은 t=1과 공유하는 `hone` 보조로) + **`sym2FlagDensity₂_eq_rmaskCount₂`**
      (쌍밀도 = count / multinomial (m₀−k, m₁−k) over (N−k)). **검증**: rooted
      K₃에서 edge·edge 쌍밀도 = 1 — count·계수·유리수 산술 전부 한 번의
      `decide +kernel`로, native 일치, **3-axiom**. 증명 팁: 밀도 정의 쪽
      match-람다는 별도 matcher로 elaborate되어 rw 패턴이 안 맞음 — 값 lemma
      rw 대신 브리지 적용 후 전체를 `decide +kernel`로 닫는 게 견고.
    - **k=2 인스턴스 + 예제 크기 검증 DONE (2026-08-27,
      `BitMask/RootedPairTest.lean`)**. 핵심 설계 개선: **역방향 전송**
      `bits_of_labeledEqv`(라벨 동치 → 루트-고정 단사 사상 + 비트 대응) +
      `rdist_of_maskCheck`로 distinctness가 **마스크 레벨·σ-무관**이 됨 —
      (2,4)의 40개 대표를 한 번의 kernel 검사(`rdist24_check`, ∃ over 4⁴=256
      함수)로 모든 type graph에 대해 처리 (σ별 라벨 iso 탐색 완전 회피). 그리고
      `racc_spec_of`(accept-spec의 제네릭 패키징). **검증**: K3freeC6 모양 —
      σ = edge type, 크기-4 패턴 2종, C6-target(루트 {0,1}) 호스트에서
      `sym2FlagDensity₁ = 1/6`, `sym2FlagDensity₂ = 0`(음성) 및 `= 1/6`(양성),
      전부 native 일치·**3-axiom**, 파일 전체 101 s. **중요 판명**: K3freeC6의
      pair density는 패턴이 크기 4라 **(2,6) 스윕 불필요** — (2,6)은 크기-6
      flag가 패턴으로 쓰일 때만 필요.
  - **(5c) 커맨드 연결 — pair-density DONE (2026-08-27)**:
    - `BitMask/RootedAccept.lean`: 조합별 `rdist_check`(마스크 레벨·σ-무관) +
      σ-generic `racc_spec` — (1,2),(1,3),(2,3),(2,4), 균일 이름으로 커맨드가
      interpolation 인용 (58 s).
    - 새 옵션 `flagGen.maskPairDensity` + `genPairDensityCoreOn`의 BitMask 분기:
      각 값 정리를 `delta → flagDensity₂_eq_sym2FlagDensity₂ → delta →
      sym2FlagDensity₂_eq_rmaskCount₂ → decide +kernel`로 방출. 지원:
      (k,patN) ∈ {(1,2),(1,3),(2,3),(2,4)}, host ≤ 7; 그 외 경고 + 기존 native
      배치 폴백.
    - **검증** (`BitMask/MaskPairDensityTest.lean`, aggregator 등록):
      CompleteGraphFreeP4 모양(3 4 2 0)에서 **200개 pair-density 정리를 kernel
      경로로 생성 — 71 s(개당 ~0.3 s), 전부 3-axiom**. RHS는 elaboration의 native
      계산값이므로 kernel decide 통과 자체가 값 교차검증.
    - **후속 완료 (2026-08-28, 진행 로그 참조)**: (3,4) 스윕 DONE; mul 감사 DONE
      (`flagGen.maskFlagSets` ② 배선 후 flagMul 3-axiom); shared-pass 배칭 DONE
      (`RootedMatrix.lean` + `flagGen.maskPairDensityShared`, host-6 호스트당
      ~20 s로 ~30× 절감). 남은 프런티어는 pruned typed ②(sym2FlagSetHfree) +
      (1,5),(3,5),(2,6) 스윕. 원 설계 메모: 대상:
    `sym2FlagDensity₂`(= `sym2InducedLabeledSubgraphListDensityLifted₂`). 구조
    정찰 결과: placement는 **루트(type_verts) 전체를 포함**하는 정점집합 쌍
    (V₀,V₁), 서로소 조건은 **루트 밖에서만**((Vᵢ\T)∩(Vⱼ\T)=∅), iso는 라벨 보존
    (`type_preserve` — 루트가 순서대로 대응). 비트화 설계:
    (i) **rooted 정준화 스윕**: 루트를 앞자리 0..k-1로 고정한 마스크에 대해
    루트-고정 순열군 S_{m-k}만으로 정준화 — gen_canon에 root-fixing perms 옵션
    추가, (k,m) 조합별 데이터 (예제가 쓰는 조합: (1,3),(2,4),(1,4),(2,6) 등);
    (ii) **rooted 추출**: V의 라벨링을 "루트 먼저(type_embed 순서), 비루트
    오름차순"으로 — vtxList 변형; (iii) t=2 count 브리지 — t=1 증명 골격 그대로
    (Fin 2 placement ↔ 부분집합 쌍 card_bij, 128² 쌍 kernel 열거는 N=7에서도
    가벼움); (iv) 정준형 유일성은 rooted distinctness로 동일 해법.
  - (5c) pair-density/mul 커맨드 연결 — 5b 후.
  n=8 2단계 확장(K_r 한정 pruning 스윕 또는 native 확장 체크)은 별도 후속.

## 최종 결과 (2026-09-03) — 11/11 완전-커널 🏆

**러너 5차 완주: 6/6 그린, 전체 빌드 그린(8,177 jobs), axiom 검사 전부 통과.**
`*_turanDensity` 메인 정리가 **11개 Flagmatic 예제 모두**
`[propext, Classical.choice, Quot.sound]` — `native_decide`
(`Lean.ofReduceBool`/`Lean.trustCompiler`) 완전 제거. 인증서(LDLᵀ PSD·목적
전개·정규화)까지 커널 검증이다.

| 예제 | 경로 | axioms |
|---|---|---|
| Mantel · K3freeP3 · K3freeC4 · K4freeEdge · ErdosPentagon | kernelDecide(기존) | 3-axiom |
| K5freeEdge / Clean / Reduced | +mask 밀도 | 3-axiom |
| K3freeC6 | +mask 밀도·플래그셋 (2,6) | 3-axiom |
| **C5freeEdge / Reduced** | **+서브그래프 mask 경로(SubHfree)** | **3-axiom** |

## 이전 최종 결과 (2026-09-02, 9/11 시점)

**러너 4차 완주: 6/6 타깃 그린, 전체 빌드 그린(8,176 jobs), axiom 검사 통과.**

| 예제 | 메인 정리 axioms |
|---|---|
| Mantel · K3freeP3 · K3freeC4 · K4freeEdge · ErdosPentagon | 3-axiom (기존) |
| **K5freeEdge / Clean / Reduced** | **`[propext, Classical.choice, Quot.sound]`** ✅ |
| **K3freeC6** | **`[propext, Classical.choice, Quot.sound]`** ✅ |
| C5freeEdge / Reduced | native 유지 (subgraph-route 후속 과제) |

**11개 Flagmatic 예제 중 9개가 완전-커널** — 인증서(LDLᵀ PSD 검사·목적 전개·
정규화)까지 포함해 `native_decide` 없이 검증된다. K3freeC6는 typed (2,6) 층
(245+135 플래그), pair-density 36,825개, mul, 청크형 downwardFactors 전부
kernel로 2시간 42분에 빌드됐다.

## 진행 로그 (2026-09-03 — C5/서브그래프 경로 커널화)

- **재시험(3번)**: 청크형 downwardFactors 이후에도 C5 kernelDecide 플립은 벌룬 —
  원인 확정: **서브그래프 경로의 완전성이 전체 quotient Fintype에 대한 직접
  `flag_bridge_decide`** (typed·empty-typed 모두; 클리크 경로만 pruned 처리였음).
- **(1)+(2) 구현** — `BitMask/SubHfree.lean`:
  - **풀백 그래프** `pullbackGraph f G`(f-역상 엣지) — subgraph 사본이 있으면
    그 상 위의 유도 부분그래프가 F의 초그래프로 family에 등재됨을 구성적으로 증명.
  - **피벗 정리** `supergraph_densities_iff_not_subgraphContains`:
    (∀ s ∈ supergraphSym2List F, 유도밀도 s = 0) ↔ ¬subgraphContains F G —
    비트 테이블 없이 **결정가능한 `subgraphContains` 자체를 마스크 술어로** 사용
    (n ≤ 5에서 충분히 저렴). + 라운드트립 형 `supergraph_densities_iff_maskTest`,
    empty-typed용 `emittedSubFreeFlags_toFinset_eq`.
  - **리팩터**: typed mask 공통 4종(mapEq/repsLt/nodup/청크 distinct)을
    `emitHfreeMaskCommon`으로 추출, 클리크·서브그래프 양 경로가 공유
    (maskFlagSetsPhase 디버그 가드는 제거). 서브그래프 typed·empty-typed 방출부에
    mask 분기 배선 (sound/cover는 subgraphContains-decide, hpq는 피벗 정리).
- **검증**: 클리크 회귀 그린 유지; **C5freeEdgeReduced 완전-커널 성공 —
  `C5freeEdge_reduced_flagAlgebra` 3-axiom, 469 s, 피크 27.8 GB** (기존 45 GB 스톨).
- C5 2종을 `--mask-density --mask-flagsets`로 재생성, 러너 5차 가동(생성기 변경으로
  6종 전체 재빌드 → 전체 빌드 → axiom 검사; **전부 통과 시 11/11 완전-커널**).

## 진행 로그

- **2026-08-21** — 문서 작성. tetrahedron 레포의 Mask3/MaskInj/Checker/Sweep 구조
  분석, lean-flag-algebras 현황(FORBID_PRUNING_ROADMAP 9a/9b)과 대조, 적용 가능
  판정. 코드 변경 없음.
- **2026-09-01** — **예제 전면 커널화: K5freeEdgeReduced 메인 정리 3-axiom 달성,
  6개 native 예제 마이그레이션 착수.**
  - **현황 조사**: Mantel·K3freeP3·K3freeC4·K4freeEdge·ErdosPentagon은 이미
    `flagGen.kernelDecide`로 완전-커널이었음(비트마스크 이전에 이행돼 있었음).
    native 잔존 = K3freeC6, K5freeEdge(+Clean/Reduced), C5freeEdge(+Reduced) 6개.
  - **plain kernelDecide 플립 실험(K5freeEdgeReduced)**: 배치형 pair-density의
    단일-선언 커널 캐시 벌룬으로 43 GB에서 정지 — 실패. **kernelDecide +
    maskPairDensity(+Shared) 조합**으로 재시도: 피크 ~25 GB, 35분, 전 층 통과.
  - **flag_certificate 센티널 버그 수정**: pair-density 검출 센티널이 배치 경로
    전용 이름(`pairDensityBatch_…_0`)이라 mask 경로(per-pair `flagDensity₂_*`)를
    못 찾고 sorryAx로 빠짐 — 센티널을 두 경로가 모두 방출하는 **첫 per-pair 값
    정리 이름**으로 교체(typed host의 첫 free 인덱스 계산 추가; Mantel로 배치
    경로 회귀 확인).
  - **검증**: `K5freeEdge_reduced_flagAlgebra` **3-axiom**
    `[propext, Classical.choice, Quot.sound]` — 인증서(LDLᵀ PSD·목적 전개·정규화)
    포함 전체 커널. 파일 옵션: kernelDecide + maskPairDensity + maskPairDensityShared.
  - **마이그레이션 적용**: `flagmatic_to_lean.py`에 `--mask-density`(pair-density
    옵션 2종 방출)·`--mask-flagsets`(maskCompleteness/maskFlagSets +
    `import ….BitMask.RCanon2_6` 방출) 플래그를 추가하고, 6개 파일을 **스크립트로
    정식 재생성**(K5×3·C5×2는 `--mask-density`, K3freeC6은 `--mask-density
    --mask-flagsets`) — 헤더의 재생성 명령이 커널 구성을 보존. 분리 실행 러너
    (kernel_migration_build.ps1, 스크래치)로 6개 순차 빌드(무거운 예제 동시 빌드
    금지 — 각 ~25-40 GB) → 전체 빌드 → axiom 검사 진행 중(로그:
    scratchpad\kernel_migration_build.log; 예상 ~11h, K3freeC6가 최장).
  - 참고: 러너 1차 가동분은 파일 재생성으로 해시가 바뀌어 재시작함(중복 빌드 방지).
  - **K3freeC6 1차 실패 → shared-pass 키 재설계**: 러너의 K3freeC6가 18분 만에
    exit 3221226505(0xC0000409, 스택 오버런)로 크래시(비동기 elaboration 때문에
    메시지 유실). 4096-원소 리터럴/멀티셋 decide 자체는 프로브 통과(192 s)했으나
    host-6 shared 재현이 47 GB 벌룬을 보여, `rootedPairKeys`를 **가드 통과 쌍만
    filter→map한 `Multiset (ℕ × ℕ)`**(Option 없음)로 재설계 — 리터럴이 4096개에서
    실제 placement 수(수십 개)로 줄고, `rmaskCount₂_eq_keyCount`는
    `count_map`+`filter_filter`+`filter_congr`로 재증명. 생성기는 `List (Nat × Nat)`
    평가/방출로 변경. host-4 회귀 24 s(기존 28.9 s) 그린. **host-6 실측(K3freeC6
    타입 2_0 층, 245 호스트 × 120 패턴쌍 = 29,400 정리)**: 41분(native 타입 생성
    ~10분 포함), 피크 24.7 GB — 기존 설계의 47 GB 벌룬 해소. 러너 재가동(3차).
  - **K3freeC6 2차 실패 → downwardFactors 청크화**: 필터형 키 적용 후에도
    K3freeC6가 17분에 스택 오버런 → 격리 결과 typed 6 2 1(135 플래그, kernelDecide
    포함)은 통과(682 s)하나 **typed 6 2 0(245 플래그) + kernelDecide가
    `std::bad_alloc`**(24.5분, 44 GB+) — 마지막 남은 대형 단일 커널 decide인
    `downwardFactors` 배치(245-원소 ℚ 리스트)가 원인. `emitChunkedQListEq` 헬퍼
    (FlagGenerator; 48개 단위 청크 선언 + `congrArg₂ (· ++ ·)` 접합, 리스트
    리터럴의 append 분해는 정의적)로 3개 방출 지점(FlagGenerator·ForbidFreeGenerator
    클리크/서브그래프 경로)을 교체. **함정**: 헬퍼를 GeneratorOptions(Mathlib
    미-import)에 두면 quotation의 `ℚ`/`congrArg₂`가 위생 식별자(`ℚ✝`)로 캡처돼
    방출 시 미해결 — FlagGenerator(Mathlib 가시)로 이동해 해결. 재검증:
    typed 6 2 0 + kernelDecide 통과(32.5분, 피크 31.8 GB, 3-axiom). 러너 4차 가동.
  - **C5 2종은 native로 유지(회귀)**: C5는 비클리크 forbid라 typed 생성이
    subgraph-route를 타는데, 그 완전성 브리지가 kernelDecide에서 단일-선언 커널
    캐시 벌룬(~45 GB, 스톨 궤적)을 일으킴 — subgraph-route 브리지의 청크화/마스크
    일반화가 후속 과제. `--native-decide`로 재생성해 기존 상태 복원, 러너에서는
    (native라 빠르게) 재빌드만 수행. 최종 러너 순서: K5Reduced → K5Clean → K5 →
    C5Reduced(native) → C5(native) → K3freeC6 → 전체 빌드 → axiom 검사.
- **2026-08-28 (2)** — **forbid-typed ②(pruned typed 완전성) 커널화 DONE —
  K3freeC6의 typed size-6 호스트층(245 플래그)까지 3-axiom.**
  - **신규 스윕 3종**: `gen_canon.py rooted` → (1,5) 90 reps·(3,5) 576 reps
    (RootedCanon에 네임스페이스 추가), **(2,6) 1992 reps**(2^15 마스크, S₄) —
    Canon6식 4분할(`RCanon2_6Checker/Sweep0–3/RCanon2_6`), 조각당 depth-10 ~15 s,
    총 ~2.9 CPU-h. 데이터 파일에 `maxRecDepth 100000` 필요(1992-원소 리터럴;
    emitRooted가 이제 자동 기입).
  - **`BitMask/RootedHfree.lean`**: 필터-완전성 브리지
    `labeledEmittedHfree_mem_iff`(q=마스크 forbid 테스트, isHfree와의 호환은
    `density_zero_iff_triFreeMask`로 — `underlyingGraph(decode h) = graphOfMask₂ h`가
    구조 eta로 rfl, 라운드트립은 rreps 경계 커널 체크), 제네릭
    `toFinset_eq_filter_of_mem_iff`, triTable{2,3,4} 인스턴스,
    unrooted-canon 불변성 `Canon{2..6}.rmaskCanonInv`, **`rootExtend` 인코딩**
    (비루트 이미지들만 ∃ — (2,6)에서 6^6=46656 후보·깊은 pi-Fintype 대신
    6^4=1296·얕은 재귀), `labeledEmitted_nodup_inv`(unrooted-canon 가드 +
    rootExtend-∃; 완전성 정리는 hdist-프리로 재구성).
  - **생성기 배선**: `runForbidFreeTypedClique`에 maskFlagSets 분기(삼각형 forbid,
    콤보 {(1,2),(1,3),(1,5),(2,3),(2,4),(2,6),(3,4),(3,5)}) — sound/cover/repsLt/
    nodup/distinct 커널 사이드컨디션 + sym2SetEqName·val_eq 대체.
    `generate_flags`(no_forbid)도 rootExtend+inv-가드 형태로 통일.
  - **핵심 시행착오** (반드시 기억):
    (i) `∃ f : Fin 6 → Fin 6` 커널 결정 = pi-Fintype 46656-리스트 → 스택 오버플로
    + 쌍당 ~12 s — rootExtend로 해결;
    (ii) **단일 거대 decide 선언의 커널 캐시는 해제되지 않음** — (2,6) distinct
    (245² 쌍)가 단일 선언일 때 ~50 GB 벌룬·스래싱. **행-청크(24행)별 선언 분할 +
    append-형 접합 정리**(내측 리스트는 전체 리터럴 유지 — simp의 map_append/
    all_append가 바인더 아래를 안 건드림)로 피크 15.9 GB;
    (iii) Lean 4.27 비동기 elaboration이 elab 중 stdout을 메시지로 캡처 —
    IO.println 디버깅은 프로세스 완료 전 안 보임(진단 교란 요인);
    (iv) 진단용 `flagGen.maskFlagSetsPhase` 옵션(단계별 방출)이 GeneratorOptions에
    남아 있음(기본 7 = 전체).
  - **검증**: (1,3)·(2,4)에서 `sym2FlagSetHfree_*_eq`/`flagSetHfree_*_val_eq`
    3-axiom(리포지토리 회귀 `BitMask/HfreeTypedTest.lean`); **(2,6) 245-플래그
    전체 494 s·피크 16 GB로 3-axiom** — K3freeC6 예제의 typed 층 커널화 준비 완료.
    no_forbid 회귀(MaskPairDensityTest: univ/val_eq/pair/mul 3-axiom)도 재검증 그린.
  - **남은 것**: K3freeC6 예제 자체의 마이그레이션(6 2 1 타입 포함, 예제 파일에
    옵션 적용 + shared-pass 밀도), downwardFactors·인증서층, 비삼각형 forbid의
    typed ② (C5 등 — q-마스크 테스트 일반화).
- **2026-08-28** — **"전부 다" 세션: (3,4) 스윕 + mul 감사 + ② no_forbid 커널 배선 +
  공유-패스 배칭 DONE. mul 정리 3-axiom 달성.**
  - **(3,4) 스윕**: `gen_canon.py rooted 3 4`(perm 1개, reps 64) →
    `RCanon3_4Data/RootedCanon/RootedAccept` + `comboSupported` 확장. 이로써 모든
    Flagmatic 예제의 pair-density **패턴** 조합 {(1,2),(1,3),(2,3),(2,4),(3,4)}이
    스윕 보유 완료(호스트는 밀도 계산에 스윕 불필요) — 밀도층은 전 예제 커널화 가능.
  - **mul 감사**: `MulThmGenerator` 자체에는 native 없음. `flagMul_*`에 남던 native는
    ② typed flagSet 완전성(`Sym2FlagList_…_eq` 한 건)뿐임을 실증.
  - **② no_forbid 커널 배선** (`flagGen.maskFlagSets`): RootedCount에
    `lcanonOf_spec_of`/`labeledEmitted_complete`/`labeledEmitted_nodup` +
    제네릭 α `toFinset_eq_univ_of_forall_mem`. `generate_flags` 분기: 커버·nodup을
    `decide +kernel`(방출 플래그들의 rooted canonical mask가 (a) 모든 RootsMatch
    대표를 커버, (b) 서로 다름) + `Flag_i ≡ map ⟦·⟧ labeled`는 rfl — native 리스트
    브리지는 **아예 방출 안 함**. 검증: (2,3)/(2,4)에서 `sym2FlagSet_eq_univ`/
    `flagSet_eq_univ`/`flagSet_val_eq` 전부 3-axiom, **mul 정리도 3-axiom**
    (`MaskPairDensityTest.lean` 갱신, 66 s 그린).
    함정 기록: (i) `Sym2Flag`는 def라 `⟦·⟧` 항이 `Quotient (setoid)` 헤드로 환원 →
    Sym2Flag-키 인스턴스가 매칭 안 됨. 정리는 리스트 완전성(∀ S, S ∈ map)으로
    인스턴스-프리하게 두고 호출부에서 제네릭 α 헬퍼로 toFinset=univ 변환;
    (ii) 생성기 파일이 quotation 안 리터럴 이름을 사전 해석하므로 FlagGenerator에
    `BitMask.RootedAccept` import 필수; (iii) `rw [$ident]`는 rwRule 스플라이스 불가 —
    `have hfl := $name; rw [hfl]` 패턴; (iv) `rreps{k}_{m}`은 RCanon{k}_{m} 네임스페이스 안.
  - **공유-패스 배칭** (`BitMask/RootedMatrix.lean` + `flagGen.maskPairDensityShared`):
    부분집합쌍마다 키 `rootedPairKey`(가드 통과 시 두 추출의 canonical mask 쌍,
    아니면 none) — 호스트당 키 멀티셋 `rootedPairKeys`를 **리터럴과 1회 kernel 대조**
    (리터럴은 compiler-backed `evalKeyMultiset`: Multiset의 런타임 표현이 리스트
    그 자체라 native 순서 == kernel 순서 → isPerm 선형 fast path), 각 pair 값은
    `rmaskCount₂_eq_keyCount`로 `Multiset.count` 투영. host-4 회귀: 200정리
    **28.9 s**(기존 per-pair 71 s). 증명 메모: `Multiset.count_map`이 곧바로
    card-filter 형태를 주므로 `filter_congr` 포인트와이즈로 마무리.
  - **host-6 주의**: K3freeC6 전체 파이프라인(typed (2,6) 생성 포함)을 스크래치
    한 파일에 쌓으면 elaboration 메모리 47 GB+ (64 GB 머신에서 스왑 직전, 중단).
    전면 마이그레이션은 예제 파일 단위로 별도 세션에서. **단일 호스트 공유 패스
    실측(K3freeC6 타깃, (2,4)-canon 키 4096개 전부 강제 평가): 파일 27 s**
    (imports 포함; 커널 패스 자체 ~15-20 s). 기존 per-pair 경로는 host-6에서
    정리당 ~25 s였으므로 호스트당 ~28쌍 기준 **~30× 절감** — K3freeC6 밀도층
    전체 예상 ~수십 분(호스트 수 × ~20 s).
  - **남은 프런티어**: pruned(=forbid) typed ② 변형(`sym2FlagSetHfree_…` —
    isHfree↔mask-forbid 호환 보조정리 + (1,5),(3,5),(2,6) 스윕 필요), empty-typed
    no_forbid univ, `downwardFactors_…_eq`, 인증서층 브리지.
- **2026-08-27** — **Task 4b DONE (삼각형 forbid, n=5/6), 전체 빌드 그린(8,144 jobs).**
  `flagGen.maskCompleteness` 옵션 + `runForbidFreeEmptyTypedClique` mask 분기 +
  `MaskBridge`의 커맨드용 정리들(`emittedFreeFlags_toFinset_eq`, `eq_triangleGraph`,
  `hfree/hcover_of_triFreeMask`, per-n `canonOf`/`canonOf_spec`). 검증:
  `BitMask/MaskWiringTest.lean`(aggregator 등록) — n=5/6에서 생성 lemma 전부 3-axiom.
  실측 교훈: (i) kernel side condition은 Prop `∀∈`가 아니라 **Bool `List.all`**로
  (~18배 차이); (ii) `hasClique`(powerset)·decode된 Finset 연산은 kernel에서 회피,
  전부 비트 레벨로; (iii) n=7은 증명 경로는 검증됐으나 커맨드의 elaboration 단계
  `evalCanonicalEdgeLists 7`(native 전체 열거, 호출마다 재계산)이 수십 분 규모라
  보류 — 스윕 대표를 직접 상수로 쓰는 전용 커맨드(JSON 인덱스 탈피)가 후속 과제;
  (iv) n=7 `_val_eq`의 nodup(107² 동형 쌍)은 kernel 불가 — 대표 유일성(canonical
  minimality) 기계가 필요. ForbidFreeGenerator에 MaskBridge import가 추가되어
  Flagmatic 예제 전체가 일회성 리빌드됨(문제없음). **다음: Task 5(density 비트화)
  또는 K₄/K₅ 위치 테이블 일반화.**
- **2026-08-21 (3)** — **Task 4a + Task 3 DONE.** 사용자 결정: "Task 4 다음 Task 3"
  순서로 진행. (i) `MaskBridge.lean` — 스윕→파이프라인 브리지(제네릭 + n=5/6
  인스턴스 + 비트 레벨 triFreeMask), 전부 kernel-only. (ii) n=7 전체 스윕 완료
  (위 Task 3 참조): 데이터 재설계(rep-인덱스 동봉 witness, packed reps, 행 단위
  테이블), `gen_canon.py 7`/`gen_sweep7.py`, Canon7Checker/Sweep00–63/Glue/Canon7.
  트러블슈팅: Python int→str 한도(`sys.set_int_max_str_digits`), 대형 리스트
  리터럴의 elaborator `maxRecDepth`(데이터 파일에 100000 설정), lake에 `-j`/`--jobs`
  옵션 없음 → 14개 타깃씩 배치 invocation으로 동시성 제한(메모리 보호; 무제한이면
  28 워커 × 2.8 GB ≈ 78 GB로 OOM 위험이었음). **다음: Task 4b(커맨드 연결) 또는
  Task 5(density 비트화).**
- **2026-08-21 (2)** — **Task 0–2 DONE, 게이트 통과.** `LeanFlagAlgebras/BitMask/`
  신설(사용자 지시: 두 레포 비연결, 독립 재구현): `Mask2.lean`(코어),
  `gen_canon.py`/`gen_sweep6.py`(데이터 생성기), `Canon5Data/Canon5.lean`(n=5),
  `Canon6Data/Canon6Checker/Canon6Sweep0–3/Canon6.lean`(n=6). 완전성 정리
  `canon5_complete`/`canon6_complete` — kernel 전용, 추가 axiom 없음
  (`#print axioms` 확인). 빌드: n=5 13 s; n=6 checker 35 s + 스윕 4×~150 s(병렬)
  + 조립 5 s. 트러블슈팅 기록: (i) 모놀리식 Canon6.lean(32 lemma 한 파일)의 빌드
  실패 원인은 스윕이 아니라 마지막 `reps6.length = 156 := by decide`의 elaborator
  `maxRecDepth` 초과 — `set_option maxRecDepth 8192`로 해결(스윕 자체는 문제없음,
  파일 분할은 병렬화·국소화 이득으로 유지); (ii) PowerShell `Out-File`의 UTF-8
  BOM이 Lean 파싱을 깨뜨림 — Lean 파일은 BOM 없는 UTF-8로 생성할 것;
  (iii) `Measure-Command`가 lake 진단 출력을 삼킴 — 타이밍 측정과 오류 진단을
  같은 실행에서 하지 말 것. **다음: Task 3(n=7) 또는 Task 4(파이프라인 연결)** —
  Task 4를 먼저 하면 n=6 수준에서 즉시 실용 가치(native_decide 제거) 실현.
