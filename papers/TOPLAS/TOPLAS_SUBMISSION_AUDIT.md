# TOPLAS 투고 전 전수검토 보고서

- 대상 원고: `papers/TOPLAS/paper_toplas.tex`
- 검토일: 2026-08-15
- 검토한 로컬 커밋: `a1784c2d62815110b55d8bcfb8827885c20f5e50`
- 확인한 공개 artifact HEAD: `06423a2e6c6f8d9435a8956e2b7409e210154b8c`
- 목적: TOPLAS 투고 전에 수학적 범위, Lean 정리와 논문 서술의 대응, trust claim,
  재현성, 관련 문헌, ACM 형식 및 참고문헌에서 심사자가 문제 삼을 수 있는 지점을 정리한다.

## 요약 판정

7개 사례의 수치, 인증서가 증명하는 상한, Mantel 및 Erdős pentagon 하한 구성에서는
반례나 상수 계산 오류를 찾지 못했다. LaTeX도 PDF 49쪽으로 정상 빌드되며 undefined
reference/citation과 overfull box는 없다.

투고 전에 우선적으로 고칠 부분은 다음과 같다.

1. 점근적 밀도 정리를 정확한 유한 extremal theorem처럼 부르는 표현
2. 인증서의 “모든 사실”을 Lean이 검증한다는 과도한 trust 문구
3. MetaTheory 본문 설명과 실제 Lean 구성·정리 사이의 간극
4. 연구 과정에서 사용한 생성형 AI에 대한 구체적인 methods 설명
5. mutable artifact, certificate dependency 미추적, raw benchmark 부재 등 재현성 문제

## 1. 반드시 수정할 사항

### 1.1 Erdős pentagon 결과의 범위를 점근형으로 명시

실제 Lean headline theorem은 다음 점근적 밀도 등식이다.

```lean
generalizedTuranDensity K3 C5 = 24 / 625
```

이는 모든 유한 `n`에 대한 정확한 extremal number와 extremal graph의 분류를 증명하는
정리가 아니다. 그러나 다음 위치에서는 이를 별도 한정 없이 “the Erdős pentagon
theorem”, “exact value”, “full result”, “first proof of the theorem”이라고 부른다.

- `paper_toplas.tex:365-369` — abstract
- `paper_toplas.tex:579-583` — contributions
- `paper_toplas.tex:2955-2961` — evaluation summary
- `paper_toplas.tex:3041-3055` — “full result”, “first machine-checked proof”
- `paper_toplas.tex:3994-3996` — conclusion

권장 표현은 다음과 같다.

> the asymptotic Erdős pentagon density theorem,
> \(\pi(C_5,K_3)=24/625\)

novelty claim도 다음처럼 좁히는 것이 안전하다.

> To our knowledge, this is the first proof-assistant formalization of the
> asymptotic density statement \(\pi(C_5,K_3)=24/625\).

Grzesik 및 Hatami–Hladký–Král’–Norine–Razborov의 결과는 점근적 결과다. 모든 유한
`n`에 대한 정확한 결과와 extremal characterization은 Lidický–Pfender가 다루며
`n = 8`의 예외도 포함한다. 이 논문을 반드시 추가 인용하는 것이 좋다.

- Hatami et al.: <https://arxiv.org/abs/1102.1634>
- Lidický–Pfender: <https://arxiv.org/abs/1712.08869>

“all known proofs”는 완전한 문헌조사를 입증하기 어려우므로 다음처럼 한정한다.

> The published proofs cited here use flag-algebra methods.

### 1.2 Mantel 결과도 점근형임을 명시

Lean에서 최종적으로 증명한 것은

```lean
turanDensity K3 = 1 / 2
```

이다. 유한형 Mantel theorem
`ex(n, K3) = floor(n^2 / 4)` 전체를 형식화한 것은 아니다. 본문 중 일부는 이미
asymptotic이라고 정확히 설명하지만 abstract, results, conclusion의 “Mantel's theorem”은
다음처럼 통일하는 편이 좋다.

> the asymptotic form of Mantel's theorem

관련 위치:

- `paper_toplas.tex:475-481`
- `paper_toplas.tex:1124-1129`
- `paper_toplas.tex:2955-2961`
- `paper_toplas.tex:2993-3038`
- `paper_toplas.tex:3994-3996`

### 1.3 인증서 trust claim을 실제 검사 범위에 맞게 축소

다음 표현은 현재 구현보다 강하다.

- `paper_toplas.tex:351-362` — Lean이 certificate가 주장하는 모든 사실을 재계산한다는 표현
- `paper_toplas.tex:2678-2681` — “takes none of these numbers on trust”

반면 `paper_toplas.tex:2794-2797`은 Lean이 재구성한 `M_t`와 certificate의 `Q'`, `R`
필드가 서로 일치하는지 검사하지 않는다고 정확히 설명한다. 최종 proof term이 실제로
사용하는 행렬과 정리문은 kernel이 확인하므로 theorem soundness가 곧바로 깨지는 것은
아니다. 그러나 certificate의 모든 필드를 검증한다고 말할 수는 없다.

권장 문구:

> Lean verifies every proof obligation actually used by the synthesized proof
> term. Fidelity between unused or redundant certificate fields and the
> reconstructed data is not part of the logical soundness argument.

또한 “compiler”의 입력 범위는 Flagmatic certificate 전체가 아니라 현재 지원하는
Flagmatic 2.0 JSON 형식의 부분집합이다. 다음을 명시해야 한다.

- 지원하는 JSON schema 및 certificate shape
- 거부하는 입력과 오류 조건
- source language, 내부 표현, 생성되는 Lean target
- proof-producing elaborator/tactic과 외부 scaffolding script의 역할 구분

### 1.4 MetaTheory의 논문 서술과 실제 Lean 정리를 맞춤

#### Constrained algebra 구성

`paper_toplas.tex:3462-3479`는 `K`에 속하는 flag만으로 constrained algebra를 별도로
구성한 다음 ambient algebra의 quotient와 canonical isomorphism을 얻는 것처럼 설명한다.
그러나 Lean의 `MetaTheory/ConstrainedClass.lean`에서는 `ConstrainedAlgebra`를 처음부터
quotient로 정의한다.

둘 중 하나를 선택해야 한다.

- 본문을 실제 형식화에 맞춰 “we model it directly as the quotient”로 수정한다.
- 별도의 `K`-기반 algebra와 canonical isomorphism을 실제로 형식화한다.

#### Forbidden ideal closure

`paper_toplas.tex:3465-3472`, `3520-3523`은 heredity 때문에 forbidden flags의 span이
ideal이라고 설명한다. 실제 `MetaTheory/ForbiddenIdeal.lean`의
`forbiddenIdeal_eq_span`은 다음 별도 가정을 받는다.

> 각 forbidden basis vector와 모든 `g`의 곱이 forbidden span에 속한다.

현재 확인한 범위에서는 일반 `HeredClass` 가정으로부터 이 algebraic closure 조건을
도출하는 Lean bridge theorem을 찾지 못했다. 따라서 다음 중 하나가 필요하다.

- heredity에서 해당 closure를 도출하는 정리를 추가한다.
- 논문에 “under the following algebraic closure hypothesis”라고 정확히 쓴다.

#### 새 수학 결과의 proof presentation

`paper_toplas.tex:3447-3449`은 MetaTheory 증명을 스케치만 하고 full account를
forthcoming paper로 넘긴다. TOPLAS 원고가 이를 새로운 수학적 기여로 내세우는 이상,
심사자가 사람이 읽을 수 있는 완전한 논증을 요구할 가능성이 높다.

권장 선택지:

- 핵심 정리의 human-readable proof를 appendix/supplement에 포함한다.
- 또는 본 논문에서는 MetaTheory를 compiler soundness의 범위 설명으로 축소하고 새 수학
  기여 주장을 낮춘다.

#### 그 밖의 정리문 대응

- 논문은 support criterion에서 non-degeneracy를 가정하지만 Lean의
  `support_criterion`은 해당 가정 없이 서술된다. 차이를 설명하거나 문장을 맞춘다.
- `blowupClosed_root_plantable`의 Lean 정리문과 논문의 class-nondegeneracy 조건을
  정확히 대조한다.
- `paper_toplas.tex:3687-3696`의 “the labeled vertex”는 일반 타입 `σ`에 여러 root가
  있을 수 있다는 점을 반영하여 다중 root iteration으로 설명한다.
- `paper_toplas.tex:3729-3733`은 `downward_preserve_semanticCone`을 ensemble-specific
  preservation처럼 소개한다. 실제 정리의 ambient semantic-cone 범위에 맞춰 다시 쓴다.
- C4-free counterexample에서 사용하는 `e(G)=o(n^2)`에 Kővári–Sós–Turán 인용을
  추가한다.

### 1.5 생성형 AI 사용을 methods 수준으로 공개

`paper_toplas.tex:4028-4039`은 다음을 밝힌다.

- 새 메타이론을 GPT Pro의 도움으로 도출
- Lean formalization을 Claude Code가 “entirely” 수행
- metaprogramming에 Claude 사용
- 논문 작성·수정에 Codex와 Claude 사용

이는 단순 문장 교정이 아니라 연구 결론, 코드, proof artifact 생성에 직접 관련된다.
현재 ACM 안내에 맞추려면 acknowledgments 한 문단보다 구체적인 methods subsection이
필요하다.

기록할 내용:

- 정확한 모델명, 가능한 경우 버전, 사용 시기
- 명제 탐색, proof 생성, metaprogram 구현 등 작업별 역할
- 각 결과에 대한 저자의 독립 검토 절차
- 문헌, citation, novelty 및 theorem-statement correspondence 검증 방법
- AI가 만든 실패한 명제·증명·코드를 배제한 기준
- 최종 연구 내용에 대한 저자의 책임과 소유권

“Lean이 type-check했다”는 사실은 의도한 정리를 형식화했는지, novelty가 맞는지,
논문 설명과 Lean statement가 일치하는지까지 보증하지 않는다는 점도 구분한다.

ACM 관련 안내:

<https://iss.acm.org/2026/authors/papers/>

### 1.6 Artifact를 immutable하고 재현 가능하게 만듦

`paper_toplas.tex:594`는 mutable GitHub `main`만 가리킨다. 다음을 추가한다.

- 제출용 tag/release
- commit SHA
- 가능하면 Zenodo DOI
- 7개 certificate JSON의 SHA-256
- Lean, Mathlib, Flagmatic 및 Python dependency 버전
- 정확한 검증 명령과 예상 결과
- 7개 headline theorem의 `#print axioms` 출력

`paper_toplas.tex:2981-2983`은 Lake가 certificate JSON 변경을 dependency로 추적하지
않아 stale `.olean`을 사용할 수 있음을 인정한다. 권장 해결책:

- CI에서 항상 clean build 수행
- certificate digest를 생성 Lean 파일에 삽입
- digest/stamp를 Lake dependency로 연결
- 최소한 artifact instructions에서 certificate 변경 후 `lake clean`을 요구

`--materialize` 결과도 어느 원본 certificate에서 왔는지 식별할 수 있도록 certificate
digest 또는 provenance comment를 포함하는 것이 좋다.

## 2. Axiom 및 공개 release 상태

### 2.1 로컬 작업 트리

로컬 커밋 `a1784c2…`에는 다음 사용자 정의 공리가 있다.

- `LeanFlagAlgebras/Automation/CompleteGraphFreeP4.lean:279`
  - `Zykov_K4_density_bound`
- `LeanFlagAlgebras/Automation/CompleteGraphFreeP4.lean:440`
  - `Turan_limit_P4_density`

로컬 `LeanFlagAlgebras.lean:42`도 이 파일을 import한다.

### 2.2 현재 온라인 release

현재 공개 release HEAD `06423a2…`의 `CompleteGraphFreeP4.lean`은 로컬과 다른,
사용자 정의 공리가 제거된 버전이다. 공개 저장소 전체에서 사용자 정의 `axiom`
선언은 발견되지 않았다.

<https://github.com/taeyool/lean-flag-algebras-release/tree/06423a2e6c6f8d9435a8956e2b7409e210154b8c>

따라서 이전 감사에서 “공개 README의 axiom-free 문구가 현재 거짓”이라고 판단했던
부분은 온라인 release에 대해서는 적용되지 않는다. 로컬과 공개 release의 버전 차이에서
생긴 문제다.

`K4freeP4.lean`과 `CompleteGraphFreeP4.lean`은 TOPLAS의 7개 사례에는 필요 없지만,
현재 공개 `MetaTheory/ParametricP4Slice.lean`과 `MetaTheory/TuranAut.lean`이 이를
직접 import한다. MetaTheory 전체를 유지하기로 했으므로 두 파일도 공개 release에
남겨 둔다.

주의사항:

- 다음 release 갱신 때 공리가 있는 로컬 `CompleteGraphFreeP4.lean`로 공개 버전을
  덮어쓰지 않는다.
- 공개 버전을 로컬로 역반영하거나, 양쪽 내용을 명시적으로 reconcile한다.
- headline theorem별 `#print axioms`를 CI에서 실행하면 이후 drift를 잡기 쉽다.

## 3. 중요한 내용 보완

### 3.1 일반 finite forbidden family와 compiler 지원 범위 구분

배경에서는 일반적인 finite forbidden family를 설명하지만 현재 compiler case study와
주요 bridge는 단일 forbidden graph `H`를 중심으로 한다. abstract의 복수형 “patterns”가
임의의 finite family를 compiler가 지원하는 것처럼 읽히지 않도록 범위를 명시한다.

### 3.2 Turán density limit의 존재

`paper_toplas.tex:1085-1091`에서 density를 limit로 정의한 직후, 해당 limit가
averaging/monotonicity 논증으로 존재한다는 문장을 추가한다. Lean에서 사용하는 존재
정리와 연결하면 좋다.

### 3.3 Goodman inequality의 order 표기

`paper_toplas.tex:3120-3140`의 부등식은 flag algebra에 내장된 literal order라기보다
모든 positive homomorphism으로 평가한 뒤의 semantic inequality다. `≤_H`,
`forbidLE`, 또는 “after evaluation by every admissible positive homomorphism”이라고
명시한다.

### 3.4 하한의 subsequence 논증

`paper_toplas.tex:3057` 부근의 “infinitely many graph sizes”는 다음처럼 쓰는 편이
엄밀하다.

> along an unbounded subsequence of graph sizes, followed by convergence of the
> normalized extremal sequence

### 3.5 Evaluation 강화

7개 성공 사례만으로 compiler의 지원 범위와 robustness를 평가하기에는 부족하다는
지적이 가능하다. 가능한 보강:

- malformed JSON 및 unsupported certificate에 대한 negative tests
- statement/certificate mismatch test
- 지원 schema와 completeness를 주장하지 않는 부분의 명시
- parsing, enumeration, lemma generation, PSD checking, normalization별 시간·메모리
- 기존 Flagmatic verifier 또는 수작업 Lean proof와의 비교

### 3.6 Benchmark의 사후 outlier 제거

`paper_toplas.tex:4074-4081`은 stalled run 하나를 사후 제외하고 새 run으로 대체했다고
설명한다. cherry-picking으로 보일 수 있으므로 다음을 권장한다.

- 6회 raw result 전체 공개
- 사전에 정한 exclusion criterion 기재
- mean만이 아니라 median/IQR도 보고
- 측정 스크립트와 raw log를 artifact에 포함

## 4. 관련 연구 및 novelty 점검

### 4.1 “first” 주장은 한정 유지

정확한 phrase 검색에서는 동일한 Lean formalization을 찾지 못했지만, 웹 검색으로
부재를 증명할 수는 없다. 모든 novelty 문구에 “to our knowledge”를 유지하고, 정확히
어느 theorem statement의 첫 formalization인지 명시한다.

### 4.2 arXiv 버전과 TOPLAS 원고 동기화

현재 arXiv v1은 제목, 페이지 수, MetaTheory 범위가 TOPLAS 원고와 다르다.

<https://arxiv.org/abs/2607.23500>

투고 전에 다음 중 하나를 한다.

- TOPLAS 원고에 맞춘 arXiv v2 업로드
- cover letter에서 v1 이후의 제목·범위·MetaTheory 변경을 명시

### 4.3 Spiegel 인용

`refs.bib:319-324`의 제목 “Computational flag algebras in Lean”은 Christoph Spiegel의
공식 페이지에 나타나는 발표 제목 “Formalizing Flag Algebras in Lean”과 다르다.

<https://iol.zib.de/team/christoph-spiegel.html>

또한 “fully inside Lean without an external solver”라는 구체적인 설명은 공개된 자료에서
확인되지 않았다. 정확한 slides를 인용하거나 personal communication으로 한정한다.

### 4.4 확인된 관련 프로젝트

다음 관련 연구 설명은 공개 자료와 대체로 일치했다.

- Local flag algebras: <https://arxiv.org/abs/2607.12461>
- Freer graphon formalization: <https://github.com/cameronfreer/graphon>
- Lean SOS: <https://github.com/leanprover/sos>

소프트웨어 인용은 mutable repository URL 대신 tag/commit 및 가능하면 repository의
`CITATION.cff`를 사용한다.

## 5. 참고문헌 정리

### 5.1 추가할 항목

- Lidický–Pfender의 정확한 유한 Erdős pentagon theorem
- C4-free edge bound에 대한 Kővári–Sós–Turán 원 논문 또는 적절한 현대 reference

### 5.2 현재 인용되지 않은 BibTeX 항목

다음 6개는 본문에서 인용되지 않는다. 사용할 계획이 없다면 제거한다.

```text
baber2012turan
balogh2017rainbow
parrilo2003minimizing
razborov2008triangles
razborov2010tetrahedron
sozeau2020metacoq
```

### 5.3 bibliographic metadata

- Davey arXiv 항목에 `eprint`, `archivePrefix`, `primaryClass`, `url`을 추가한다.
- GitHub software references에 release/tag/commit 및 access date를 추가한다.
- `refs.bib` 내부의 stale comment와 uncited-entry comment를 정리한다.
- BibTeX key `hatami2012`와 실제 publication year 차이는 출력 오류는 아니지만 유지보수상
  혼동을 줄 수 있다.

## 6. ACM/TOPLAS 형식 및 메타데이터

### 6.1 acmart 버전

현재 로컬 빌드는 acmart 2.12를 사용했다. 검토일 기준 공식 CTAN 배포판은 2.19다.
최신 버전과 공식 `acmsmall-submission` sample로 다시 빌드한다.

<https://ctan.org/tex-archive/macros/latex/contrib/acmart?lang=en>

`paper_toplas.tex:7`의

```latex
\documentclass[acmsmall,screen=true,acmthm=false]{acmart}
```

은 로컬 로그에서 unused global option 경고를 냈다. 실제 적용 여부와 별개로 최신
sample의 정확한 option syntax에 맞춘다.

### 6.2 placeholder production metadata 제거

`paper_toplas.tex:27`의 `\setcopyright{none}` 및 hard-coded `\acmYear{2026}` 때문에
PDF에 volume/issue/DOI placeholder가 출력된다. 제출용 공식 sample 및 submission
portal metadata에 맞춘다.

### 6.3 ORCID와 affiliation

- `paper_toplas.tex:251-253`의 ORCID TODO를 해결한다.
- `paper_toplas.tex:316-326`의 수동 `\authorsaddresses`는 일부 secondary affiliation을
  누락한다. 가능하면 acmart가 자동 생성하게 두거나 모든 affiliation을 포함한다.
- journal article에서는 저자 주소 metadata가 중요하므로 TAPS와 충돌하지 않게 한다.

### 6.4 short author 위치

`paper_toplas.tex:409`의 `\renewcommand{\shortauthors}{...}`가 `\maketitle` 뒤에 있다.
`\maketitle` 앞으로 옮긴다.

### 6.5 acmart spacing warning

`paper_toplas.tex:2440`의 `\medskip`이 acmart의 `\vspace` 경고를 발생시킨다. 이미
사용 중인 paragraph-heading macro 또는 표준 문단 구조로 대체한다.

### 6.6 분량과 TOPLAS 적합성

현재 출력은 49쪽이다. 확인된 명시적 page-limit 위반이라고 단정할 수는 없지만,
다음 세 축이 한 논문에 함께 있어 PL contribution의 초점이 흐려 보일 수 있다.

- flag algebra의 긴 수학적 배경과 수동 formalization
- Flagmatic-to-Lean compiler
- 별도의 새로운 ensemble-semantics MetaTheory

TOPLAS 적합성을 강화하려면 compiler의 다음 측면을 전면에 둔다.

- source/certificate language
- translation stages와 IR
- trust boundary
- failure semantics
- generated proof architecture
- reproducibility와 evaluation

MetaTheory의 긴 수학적 전개는 완전한 proof를 부록에 넣거나 별도 논문으로 분리하는
선택도 고려한다. CCS “Proof theory”보다 verified computation, proof assistants,
metaprogramming 또는 compiler 관련 분류가 더 적절할 수 있다.

## 7. 공개 artifact 문서에서 함께 고칠 사항

현재 공개 artifact:

<https://github.com/taeyool/lean-flag-algebras-release>

### 7.1 Python dependency

`Flagmatic/README.md`는 `flagmatic_to_lean.py` 실행에 Python standard library만 필요하다고
쓰지만, `graph_enumeration.py`는 `networkx`를 import하며 compiler가 해당 모듈을 실제로
사용한다. 다음 중 하나가 필요하다.

- README requirements에 정확한 NetworkX 버전을 추가한다.
- NetworkX 의존성을 제거하고 standard-library-only라는 주장을 유지한다.

세 Python 파일 `flagmatic_to_lean.py`, `flag_enumeration.py`,
`graph_enumeration.py`는 서로 연결된 compiler 구성요소이므로 삭제 대상이 아니다.

### 7.2 README scope

공개 README는 TOPLAS에 없는 relative Positivstellensatz, C5-free edge-type obstruction,
graphon/stability MetaTheory도 headline result로 소개한다. MetaTheory 전체를 공개
release에 남기는 것은 가능하지만, 다음을 구분하면 심사자가 artifact 범위를 이해하기
쉽다.

- 이 TOPLAS 논문에서 주장·평가하는 결과
- 저장소에 추가로 포함된 후속/별도 연구 결과

### 7.3 정확한 build target

전체 build가 매우 무거우므로 다음을 artifact instructions에 별도로 제공한다.

- 7개 case별 `lake build LeanFlagAlgebras.Flagmatic.<Case>`
- Mantel 및 Erdős lower-bound module
- TOPLAS에서 명시한 MetaTheory headline module
- 전체 clean build 명령과 예상 시간·메모리

## 8. 검증에서 통과한 항목

### 8.1 LaTeX

- `latexmk -pdf` 성공
- 49페이지 생성
- undefined reference 없음
- undefined citation 없음
- BibTeX error/warning 없음
- overfull box 없음
- 일부 underfull box와 font substitution warning은 있으나 치명적이지 않음

### 8.2 Lean build

- Lean toolchain: 4.27.0
- `lake build LeanFlagAlgebras.MetaTheory` 성공
- 8,019 build jobs 완료
- 실제 theorem/build error 없음
- 전체 `lake build LeanFlagAlgebras`는 600초 제한에 걸려 감사 중 완주하지 못함

마지막 항목은 build failure로 해석하면 안 되지만, 투고용 artifact에서는 전체 clean
build 성공 로그를 별도로 남겨야 한다.

### 8.3 7개 certificate 사례

논문의 표와 Lean 파일의 `H`, `F`, host size `N`, type/block 구조 및 bound를 대조했다.
다음 상한에서 수치 오류를 찾지 못했다.

| 사례 | 검증된 상한 |
|---|---:|
| K3-free edge density | `1/2` |
| K3-free P3 density | `3/4` |
| K3-free C4 density | `3/8` |
| K4-free edge density | `2/3` |
| K5-free edge density | `3/4` |
| C5-free edge density | `1/2` |
| K3-free C5 density | `24/625` |

Erdős 사례의 generated pair-density/multiplication lemma 수
`1800 + 672 + 360 = 2832`도 맞다.

### 8.4 하한 및 수학적 구성

- Mantel의 balanced complete bipartite construction 계산이 맞다.
- K3-free C5 문제의 balanced C5 blow-up 계산이 맞다.
- `24/625` 하한의 induced C5 count 및 normalization에 오류를 찾지 못했다.
- `blowUp_K3_free`, reindexing 및 unbounded-subsequence 논증의 핵심은 맞다.
- C4-free star witness counterexample의 아이디어는 맞다.
- ordinary subgraph와 induced subgraph의 혼동을 Lean 구현에서 찾지 못했다.
- forbidden flags는 underlying graph가 `H`를 ordinary subgraph로 포함하는 조건과
  올바르게 연결되어 있다.

### 8.5 computation trust mode

- 작은 5개 사례는 `flagGen.kernelDecide true`를 사용한다.
- K5-free edge와 C5-free edge 사례는 `native_decide`를 사용한다.
- 논문의 두 trust mode 구분은 실제 소스와 일치한다.

## 9. 감사의 한계

- 전체 root clean build는 시간 제한 때문에 완료하지 못했다.
- 모든 headline theorem을 한 파일에서 import한 fresh `#print axioms` audit도 180초
  제한 안에 완료되지 않았다.
- 웹 검색은 novelty의 부재를 증명할 수 없으므로 “first” 주장은 계속 한정해야 한다.
- 수학적으로 올바른 명제와 Lean statement 사이의 의미적 대응은 type checking만으로
  자동 보증되지 않는다.

## 10. 권장 수정 순서

1. Erdős 및 Mantel 결과를 점근형으로 정확히 명명
2. trust claim을 실제 proof obligations 범위로 축소
3. MetaTheory의 quotient/ideal/closure 서술과 Lean 정리문 대응 수정
4. AI research-use methods subsection 추가
5. artifact tag, commit, certificate hash 및 clean-build CI 마련
6. Lidický–Pfender와 Kővári–Sós–Turán 인용 추가
7. benchmark raw data와 negative tests 보강
8. acmart, ORCID, affiliation, copyright placeholder 정리
9. README와 dependency 설명 동기화

