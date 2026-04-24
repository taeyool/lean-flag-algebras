# Agentic Paper Writing System

이 디렉터리는 저장소 근거 기반으로 논문 초안을 생성하기 위한 최소 에이전트 파이프라인입니다.

## What It Produces
- 섹션별 에이전트 입력 프롬프트 파일
- 주장 근거 데이터(evidence_units.json)
- 고려사항(considerations.md) 자동 반영
- 기존 papers/paper.tex의 Contributions를 가져온 새 초안 파일
- Planner/Retriever/Writer/Verifier 자동 실행 로그 및 섹션 반영 결과

출력 위치: papers/agentic/out

중요: 기존 papers/paper.tex는 수정하지 않습니다. 읽기 전용 소스로만 사용합니다.

## Files
- pipeline.py: 증거 추출 + 섹션별 프롬프트 생성
- run_multi_agent.py: 다중 에이전트 자동 실행기 (Planner -> Retriever -> Writer -> Verifier)
- config.json: 섹션/소스/추출 범위 설정
- considerations.md: 논문 작성 시 반드시 고려할 항목
- draft_tex_output: 새로 생성할 초안 TeX 경로 (source와 분리)

## Quality Control With Exemplar Papers
- config.json의 quality_profile.formalization_examples_dir에 있는 파일 목록이 자동으로 task 프롬프트에 주입된다.
- 현재 기본값은 papers/References/Formalization 이며, 해당 예시 논문들의 품질 수준을 목표로 작성하도록 유도한다.
- quality_profile.quality_requirements를 수정하면 문체/깊이 기준을 프로젝트에 맞게 조정할 수 있다.
- 수식의 출처 기준은 quality_profile.equation_reference_pdfs로 지정하며, 기본값은 papers/References/Razborov07.pdf 와 papers/References/GrzesikThesis14.pdf 이다.
- section_blueprints에 섹션별 최소 subsection/문단/수식/코드근거 조건을 넣으면 writer/verifier task에서 하드 제약으로 처리된다.

## Quick Start
1. considerations.md를 프로젝트 상황에 맞게 수정한다.
2. config.json에서 섹션별 source 파일 목록을 조정한다.
3. 저장소 루트에서 아래 명령으로 실행한다.

python papers/agentic/pipeline.py --root . --config papers/agentic/config.json

4. papers/agentic/out/prompt_*.md를 각 에이전트(Planner/Retriever/Writer/Verifier)에 입력한다.

5. papers/agentic/out/paper_draft_from_contributions.tex를 새 논문 초안 베이스로 사용한다.

## One-Command Auto Draft
기본 실행(외부 API 키 없이 Copilot 작업 큐 생성):

python papers/agentic/run_multi_agent.py --root . --config papers/agentic/config.json

- 이 명령은 기존 papers/paper.tex를 수정하지 않고,
  papers/agentic/out/paper_draft_from_contributions.tex를 갱신한다.
- 섹션별 Copilot 작업 파일은 papers/agentic/out/agent_runs에 저장된다.
- 큐 매니페스트: papers/agentic/out/agent_runs/copilot_queue_manifest.json

외부 API 직접 호출 모드(선택):

python papers/agentic/run_multi_agent.py --root . --config papers/agentic/config.json --execution-mode api

API 키 없이 API 모드 점검만 하고 싶으면:

python papers/agentic/run_multi_agent.py --root . --config papers/agentic/config.json --execution-mode api --dry-run

주의:
- copilot-queue 모드는 OPENAI_API_KEY 없이 동작한다.
- api 모드에서만 config.json의 llm 설정과 OPENAI_API_KEY 환경 변수가 필요하다.
- 모델 이름은 config.json의 llm.model 또는 AGENTIC_MODEL 환경 변수로 지정할 수 있다.

## Recommended Agent Order
1. Planner: 섹션 목적/핵심 주장 스켈레톤 수립
2. Retriever: 프롬프트의 Retrieved Evidence 보강
3. Writer: 섹션 본문 작성
4. Verifier: claim-evidence 매핑 검증 및 과장 표현 제거
5. Editor: 문체/용어 일관성 정리

## How Considerations Are Enforced
- pipeline.py가 considerations.md를 읽어 모든 섹션 프롬프트의 Mandatory Considerations 블록으로 삽입한다.
- 따라서 항목을 업데이트하면 다음 실행에서 자동 반영된다.

## Practical Tips
- Abstract는 항상 마지막에 생성한다.
- Application 섹션은 Mantel과 Erdos Pentagon을 분리해 각각 검증한다.
- 근거가 부족한 섹션은 config.json의 source를 늘린 뒤 재실행한다.
