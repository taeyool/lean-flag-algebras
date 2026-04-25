from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pipeline import (
    EvidenceUnit,
    extract_abstract_from_tex,
    extract_contributions_from_tex,
    extract_evidence,
    extract_section_body_from_tex,
    read_text,
    render_seed_draft_tex,
)


def list_formalization_exemplars(root: Path, config: dict[str, Any]) -> list[str]:
    quality_cfg = config.get("quality_profile", {})
    rel_dir = quality_cfg.get(
        "formalization_examples_dir", "papers/References/Formalization"
    )
    abs_dir = root / rel_dir
    if not abs_dir.exists() or not abs_dir.is_dir():
        return []

    paths: list[str] = []
    for child in sorted(abs_dir.iterdir()):
        if not child.is_file():
            continue
        if child.suffix.lower() not in {".pdf", ".tex", ".md"}:
            continue
        paths.append(str(child.relative_to(root)).replace("\\", "/"))
    return paths


def section_depth_target(section: str) -> str:
    s = section.strip().lower()
    if s == "abstract":
        return "1 compact paragraph (5-8 sentences) with problem, method, contributions, and application outcome."
    if s == "conclusion":
        return "2-3 substantial paragraphs with summary, limitations, and concrete next steps."
    if s == "application":
        return "3-5 substantial paragraphs with pipeline details, trust boundary, and what is formally verified."
    return "3-5 substantial paragraphs with clear logical flow, not a short overview."


def render_section_blueprint(config: dict[str, Any], section: str) -> str:
    blueprints = config.get("section_blueprints", {})
    bp = blueprints.get(section, {})
    if not isinstance(bp, dict) or not bp:
        return "- (no section blueprint configured)"

    lines: list[str] = []
    for key, value in bp.items():
        if isinstance(value, list):
            if not value:
                lines.append(f"- {key}: []")
                continue
            lines.append(f"- {key}:")
            for item in value:
                lines.append(f"  - {item}")
        else:
            lines.append(f"- {key}: {value}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Planner/Retriever/Writer/Verifier to draft sections automatically."
    )
    parser.add_argument("--root", default=".", help="Repository root path")
    parser.add_argument(
        "--config", default="papers/agentic/config.json", help="Config path"
    )
    parser.add_argument(
        "--sections",
        default="",
        help="Comma-separated section names to run. Empty means default_sections.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Run without external model calls and generate placeholder section content.",
    )
    parser.add_argument(
        "--execution-mode",
        choices=["copilot-queue", "api"],
        default="copilot-queue",
        help="copilot-queue: generate task files for Copilot chat workflow, api: run external API calls.",
    )
    return parser.parse_args()


def strip_fence(text: str) -> str:
    s = text.strip()
    if s.startswith("```") and s.endswith("```"):
        lines = s.splitlines()
        if len(lines) >= 3:
            return "\n".join(lines[1:-1]).strip()
    return s


def parse_json_block(text: str) -> dict[str, Any] | None:
    s = text.strip()
    try:
        val = json.loads(s)
        if isinstance(val, dict):
            return val
    except json.JSONDecodeError:
        pass

    m = re.search(r"```json\s*(.*?)```", s, flags=re.DOTALL | re.IGNORECASE)
    if m:
        block = m.group(1).strip()
        try:
            val = json.loads(block)
            if isinstance(val, dict):
                return val
        except json.JSONDecodeError:
            return None
    return None


def section_to_filename(section: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", section).strip("_").lower()


def render_evidence_list(units: list[EvidenceUnit], limit: int) -> str:
    lines: list[str] = []
    for idx, u in enumerate(units[:limit], start=1):
        lines.append(
            f"{idx}. [{u.symbol_kind}] {u.symbol_name} @ {u.source_path}:{u.line_number} :: {u.snippet}"
        )
    if not lines:
        return "(No evidence extracted for this section.)"
    return "\n".join(lines)


def chat_openai_compat(
    api_url: str,
    api_key: str,
    model: str,
    messages: list[dict[str, str]],
    temperature: float,
    max_tokens: int,
    timeout_sec: int,
) -> str:
    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
    }
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        api_url,
        data=data,
        method="POST",
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_sec) as resp:
            body = resp.read().decode("utf-8", errors="ignore")
    except urllib.error.HTTPError as e:
        detail = e.read().decode("utf-8", errors="ignore")
        raise RuntimeError(f"LLM HTTP error {e.code}: {detail}") from e
    except urllib.error.URLError as e:
        raise RuntimeError(f"LLM request failed: {e.reason}") from e

    try:
        parsed = json.loads(body)
        return parsed["choices"][0]["message"]["content"].strip()
    except Exception as e:
        raise RuntimeError(f"Unexpected LLM response format: {body[:1000]}") from e


def ask_agent(
    role_name: str,
    system_prompt: str,
    user_prompt: str,
    llm_cfg: dict[str, Any],
    dry_run: bool,
) -> str:
    if dry_run:
        return f"[DRY-RUN:{role_name}]\n{user_prompt[:1200]}"

    api_key_env = llm_cfg.get("api_key_env", "OPENAI_API_KEY")
    api_key = os.getenv(api_key_env, "").strip()
    if not api_key:
        raise RuntimeError(
            f"Missing API key in environment variable: {api_key_env}. "
            "Set it or run with --dry-run."
        )

    api_url = llm_cfg.get("api_url", "https://api.openai.com/v1/chat/completions")
    model = os.getenv("AGENTIC_MODEL", llm_cfg.get("model", "gpt-4.1"))
    temperature = float(llm_cfg.get("temperature", 0.2))
    max_tokens = int(llm_cfg.get("max_tokens", 2500))
    timeout_sec = int(llm_cfg.get("timeout_sec", 120))

    return chat_openai_compat(
        api_url=api_url,
        api_key=api_key,
        model=model,
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        temperature=temperature,
        max_tokens=max_tokens,
        timeout_sec=timeout_sec,
    )


def replace_abstract(tex: str, abstract_body: str) -> str:
    pattern = re.compile(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.DOTALL)
    repl = "\\begin{abstract}\n" + abstract_body.strip() + "\n\\end{abstract}"
    if pattern.search(tex):
        return pattern.sub(lambda _: repl, tex, count=1)

    marker = "\\maketitle"
    pos = tex.find(marker)
    if pos == -1:
        return tex
    insert_at = pos + len(marker)
    return tex[:insert_at] + "\n\n" + repl + tex[insert_at:]


def replace_section_body(tex: str, section_title: str, body: str) -> str:
    sec_pat = re.compile(rf"\\section\{{{re.escape(section_title)}\}}")
    m = sec_pat.search(tex)
    if not m:
        end_doc = tex.find("\\end{document}")
        if end_doc == -1:
            return tex + f"\n\n\\section{{{section_title}}}\n" + body.strip() + "\n"
        return (
            tex[:end_doc]
            + f"\n\n\\section{{{section_title}}}\n"
            + body.strip()
            + "\n\n"
            + tex[end_doc:]
        )

    body_start = m.end()
    next_sec = re.search(r"\n\\section\{", tex[body_start:])
    end_doc_pos = tex.find("\\end{document}")

    if next_sec:
        body_end = body_start + next_sec.start()
    elif end_doc_pos != -1:
        body_end = end_doc_pos
    else:
        body_end = len(tex)

    new_body = "\n" + body.strip() + "\n\n"
    return tex[:body_start] + new_body + tex[body_end:]


def build_common_context(
    config: dict[str, Any],
    considerations: str,
    author_notes: str,
    global_instructions: list[str],
    exemplar_paths: list[str],
    section: str,
) -> str:
    section_instructions = config.get("section_instructions", {}).get(section, [])
    global_block = "\n".join(f"- {x}" for x in global_instructions) or "- (none)"
    section_block = "\n".join(f"- {x}" for x in section_instructions) or "- (none)"
    exemplar_block = (
        "\n".join(f"- {x}" for x in exemplar_paths) or "- (no exemplar files found)"
    )

    quality_cfg = config.get("quality_profile", {})
    quality_requirements = quality_cfg.get(
        "quality_requirements",
        [
            "Avoid shallow summary style; write argument-driven paragraphs.",
            "State design rationale, not just feature lists.",
            "Include explicit links between formal definitions and proof goals.",
            "Prefer precise claims over broad marketing language.",
        ],
    )
    quality_block = "\n".join(f"- {x}" for x in quality_requirements) or "- (none)"
    eq_sources = quality_cfg.get("equation_reference_pdfs", [])
    eq_source_block = "\n".join(f"- {x}" for x in eq_sources) or "- (none)"
    blueprint_block = render_section_blueprint(config, section)

    return (
        f"Project: {config['project_name']}\n"
        f"Target Section: {section}\n\n"
        f"Depth Target:\n- {section_depth_target(section)}\n\n"
        f"Section Blueprint (Hard Constraints):\n{blueprint_block}\n\n"
        f"Equation Source PDFs (for mathematical formulas):\n{eq_source_block}\n\n"
        f"Exemplar Formalization Papers (quality bar):\n{exemplar_block}\n\n"
        f"Quality Requirements:\n{quality_block}\n\n"
        f"Mandatory Considerations:\n{considerations}\n\n"
        f"Author Notes:\n{author_notes}\n\n"
        f"Global Instructions:\n{global_block}\n\n"
        f"Section-Specific Instructions:\n{section_block}\n"
    )


def generate_copilot_task_pack(
    *,
    section_log_dir: Path,
    section: str,
    draft_tex_output: str,
    common_context: str,
    evidence_rendered: str,
    selected_rendered: str,
    ref_section_body: str = "",
) -> None:
    # Build the reference draft block included in writer and verifier tasks.
    if ref_section_body:
        ref_block = (
            "\nReference Section Draft (your primary starting point — improve and refine this):\n"
            "---BEGIN REFERENCE DRAFT---\n"
            + ref_section_body
            + "\n---END REFERENCE DRAFT---\n\n"
        )
        writer_action = (
            f"Improve and refine the Reference Draft above for section: {section}.\n"
            "Identify gaps and weak arguments, add missing technical detail, fix any imprecision.\n"
            "Preserve accurate technical content already present. Do not remove verified claims.\n"
        )
    else:
        ref_block = ""
        writer_action = (
            f"Write publication-grade LaTeX body for section: {section}.\n"
            "Write explicit transitions, motivation, and technical substance.\n"
        )

    planner_task = (
        "# Planner Task\n\n"
        + common_context
        + "\n"
        + ref_block
        + "Produce a publication-grade improvement plan (not a terse outline).\n"
        + ("If a Reference Draft is provided, identify what is already strong, what is missing or weak, and what should be restructured.\n" if ref_section_body else "")
        + "The plan must enforce the same quality bar as exemplar formalization papers.\n\n"
        + "Hard gate: fail the plan if any Section Blueprint item is missing.\n"
        + "For formula-heavy sections, equation choices must be sourced from the listed Equation Source PDFs.\n\n"
        + "Candidate evidence list:\n"
        + evidence_rendered
        + "\n\n"
        + "Output format (JSON only):\n"
        + "{\n"
        + '  "writing_goal": "...",\n'
        + '  "subsection_plan": ["..."],\n'
        + '  "claim_plan": ["..."],\n'
        + '  "evidence_needs": ["..."],\n'
        + '  "gaps_in_reference_draft": ["..."],\n'
        + '  "risk_checks": ["..."]\n'
        + "}\n"
    )

    retriever_task = (
        "# Retriever Task\n\n"
        + common_context
        + "\n"
        + "Read planner_output.json first, then select evidence IDs.\n\n"
        + "Candidate evidence list:\n"
        + evidence_rendered
        + "\n\n"
        + "Output format (JSON only):\n"
        + "{\n"
        + '  "selected_ids": [1,2,3],\n'
        + '  "selection_rationale": ["..."],\n'
        + '  "missing_evidence": ["..."]\n'
        + "}\n"
    )

    writer_task = (
        "# Writer Task\n\n"
        + common_context
        + "\n"
        + "Read planner_output.json and retriever_output.json first.\n\n"
        + "Selected evidence:\n"
        + selected_rendered
        + "\n\n"
        + ref_block
        + writer_action
        + "Hard gate: satisfy all Section Blueprint constraints (subsections, equations, code references where required).\n"
        + "For mathematical formulas, derive and align notation from the listed Equation Source PDFs.\n"
        + "Do not include \\section{...}.\n"
        + "Save output as writer_output.md.\n"
    )

    verifier_task = (
        "# Verifier Task\n\n"
        + common_context
        + "\n"
        + "Read writer_output.md first.\n\n"
        + "Selected evidence:\n"
        + selected_rendered
        + "\n\n"
        + ref_block
        + "Revise to remove unsupported claims and strengthen evidence alignment.\n"
        + "If the prose is shallow, expand it to match exemplar-paper depth while staying evidence-grounded.\n"
        + "Hard gate: reject output if Section Blueprint constraints are not satisfied.\n"
        + "For equation-heavy sections, verify formulas and notation are consistent with the listed Equation Source PDFs.\n"
        + "Return only final LaTeX section body without markdown fences and without \\section{...}.\n"
        + "Save output as verifier_output.md.\n"
    )

    apply_task = (
        "# Apply Task\n\n"
        + f"Target draft file: {draft_tex_output}\n"
        + f"Target section: {section}\n\n"
        + "Take verifier_output.md and replace only the body of the target section.\n"
        + "Do not modify the contribution list and do not edit source papers/paper_claude.tex.\n"
    )

    (section_log_dir / "planner_task.md").write_text(planner_task, encoding="utf-8")
    (section_log_dir / "retriever_task.md").write_text(retriever_task, encoding="utf-8")
    (section_log_dir / "writer_task.md").write_text(writer_task, encoding="utf-8")
    (section_log_dir / "verifier_task.md").write_text(verifier_task, encoding="utf-8")
    (section_log_dir / "apply_task.md").write_text(apply_task, encoding="utf-8")


def judge_verifier_alignment(
    *,
    common_context: str,
    selected_rendered: str,
    verifier_out: str,
    llm_cfg: dict[str, Any],
    dry_run: bool,
) -> dict[str, Any]:
    """Ask a strict judge agent whether verifier output should be retried."""
    if dry_run:
        return {
            "retry_required": False,
            "reason": "Dry-run mode skips alignment judge.",
            "focus_points": [],
        }

    judge_user = (
        common_context
        + "\n"
        + "Selected evidence:\n"
        + selected_rendered
        + "\n\n"
        + "Verifier output:\n"
        + verifier_out
        + "\n\n"
        + "Decide if the output has evidence mismatch risk. "
        + "Return strict JSON with keys: retry_required (bool), reason (string), focus_points (list of strings). "
        + "Set retry_required=true only when claims likely exceed evidence or are too vague to verify."
    )

    judge_out = ask_agent(
        role_name="VerifierJudge",
        system_prompt=(
            "You are a strict evidence-alignment judge. "
            "Be conservative and return only valid JSON."
        ),
        user_prompt=judge_user,
        llm_cfg=llm_cfg,
        dry_run=dry_run,
    )
    parsed = parse_json_block(judge_out)
    if isinstance(parsed, dict):
        return parsed
    return {
        "retry_required": False,
        "reason": "Judge output was not valid JSON; fallback to no retry.",
        "focus_points": [],
    }


def run() -> None:
    args = parse_args()
    root = Path(args.root).resolve()
    config_path = root / args.config
    if not config_path.exists():
        raise FileNotFoundError(f"Config not found: {config_path}")

    config = json.loads(read_text(config_path))
    out_dir = root / config["output_dir"]
    out_dir.mkdir(parents=True, exist_ok=True)

    source_paper_tex = config["paper_tex"]
    contribution_source_tex = config.get("contribution_source_tex", source_paper_tex)
    draft_tex_output = config.get(
        "draft_tex_output", "papers/agentic/out/paper_draft_from_contributions.tex"
    )

    contribution_source_path = root / contribution_source_tex
    draft_output_path = root / draft_tex_output
    draft_output_path.parent.mkdir(parents=True, exist_ok=True)

    source_tex_text = (
        read_text(contribution_source_path) if contribution_source_path.exists() else ""
    )
    contributions = extract_contributions_from_tex(source_tex_text)

    # Load the reference (base) draft: if base_draft_tex is configured, copy it as the
    # seed so agents start from a high-quality existing draft rather than a blank skeleton.
    base_draft_tex_path = config.get("base_draft_tex", "")
    reference_tex = ""
    if base_draft_tex_path:
        ref_path = root / base_draft_tex_path
        if ref_path.exists():
            reference_tex = read_text(ref_path)

    if reference_tex:
        draft_output_path.write_text(reference_tex, encoding="utf-8")
    else:
        draft_output_path.write_text(
            render_seed_draft_tex(config["project_name"], contributions), encoding="utf-8"
        )

    considerations_path = root / config["considerations_file"]
    author_notes_path = root / config.get("author_notes_file", "")
    considerations = (
        read_text(considerations_path)
        if considerations_path.exists()
        else "(Missing considerations file)"
    )
    author_notes = (
        read_text(author_notes_path)
        if author_notes_path.exists()
        else "(No author notes provided)"
    )

    default_sections: list[str] = config["default_sections"]
    sections = (
        [s.strip() for s in args.sections.split(",") if s.strip()]
        if args.sections.strip()
        else default_sections
    )

    max_lines = int(config["retrieval"]["max_lines_per_file"])
    section_sources = config["section_sources"]
    global_instructions = config.get("global_instructions", [])
    exemplar_paths = list_formalization_exemplars(root, config)
    llm_cfg = config.get("llm", {})
    executor_cfg = config.get("executor", {})
    max_evidence_per_section = int(executor_cfg.get("max_evidence_per_section", 120))
    selected_evidence_limit = int(executor_cfg.get("selected_evidence_limit", 24))
    max_verifier_retries = int(executor_cfg.get("max_verifier_retries", 1))

    run_log_dir = root / executor_cfg.get(
        "run_log_dir", "papers/agentic/out/agent_runs"
    )
    run_log_dir.mkdir(parents=True, exist_ok=True)

    system_prompt = (
        "You are an expert academic writing agent for formalized mathematics. "
        "Follow evidence strictly, avoid unsupported claims, and produce precise LaTeX-ready text."
    )

    current_tex = read_text(draft_output_path)
    execution_mode = args.execution_mode
    queue_manifest: list[dict[str, str]] = []

    for section in sections:
        section_safe = section_to_filename(section)
        section_log_dir = run_log_dir / section_safe
        section_log_dir.mkdir(parents=True, exist_ok=True)

        # Extract the existing section body from the reference draft for use in prompts.
        if reference_tex:
            if section.lower() == "abstract":
                ref_section_body = extract_abstract_from_tex(reference_tex)
            else:
                ref_section_body = extract_section_body_from_tex(reference_tex, section)
        else:
            ref_section_body = ""

        evidence_units = extract_evidence(
            section=section,
            root=root,
            source_paths=section_sources.get(section, []),
            max_lines=max_lines,
        )
        evidence_rendered = render_evidence_list(
            evidence_units, max_evidence_per_section
        )
        common_context = build_common_context(
            config=config,
            considerations=considerations,
            author_notes=author_notes,
            global_instructions=global_instructions,
            exemplar_paths=exemplar_paths,
            section=section,
        )

        if execution_mode == "copilot-queue":
            selected_units = evidence_units[:selected_evidence_limit]
            selected_rendered = render_evidence_list(
                selected_units, selected_evidence_limit
            )
            generate_copilot_task_pack(
                section_log_dir=section_log_dir,
                section=section,
                draft_tex_output=draft_tex_output,
                common_context=common_context,
                evidence_rendered=evidence_rendered,
                selected_rendered=selected_rendered,
                ref_section_body=ref_section_body,
            )
            queue_manifest.append(
                {
                    "section": section,
                    "task_dir": str(section_log_dir),
                    "planner_task": str(section_log_dir / "planner_task.md"),
                    "retriever_task": str(section_log_dir / "retriever_task.md"),
                    "writer_task": str(section_log_dir / "writer_task.md"),
                    "verifier_task": str(section_log_dir / "verifier_task.md"),
                    "apply_task": str(section_log_dir / "apply_task.md"),
                }
            )
            continue

        planner_user = (
            common_context
            + "\n"
            + "Return JSON with keys: writing_goal, subsection_plan, claim_plan, evidence_needs, risk_checks.\n"
            + f"Section: {section}\n"
            + "Do not draft prose yet."
        )
        planner_out = ask_agent(
            role_name="Planner",
            system_prompt=system_prompt,
            user_prompt=planner_user,
            llm_cfg=llm_cfg,
            dry_run=args.dry_run,
        )
        (section_log_dir / "planner.md").write_text(planner_out, encoding="utf-8")

        planner_json = parse_json_block(planner_out) or {}

        retriever_user = (
            common_context
            + "\n"
            + "Planner output:\n"
            + json.dumps(planner_json, ensure_ascii=False, indent=2)
            + "\n\n"
            + "Candidate evidence list:\n"
            + evidence_rendered
            + "\n\n"
            + "Return JSON with keys: selected_ids (list of integers), selection_rationale (list), missing_evidence (list)."
        )
        retriever_out = ask_agent(
            role_name="Retriever",
            system_prompt=system_prompt,
            user_prompt=retriever_user,
            llm_cfg=llm_cfg,
            dry_run=args.dry_run,
        )
        (section_log_dir / "retriever.md").write_text(retriever_out, encoding="utf-8")

        retriever_json = parse_json_block(retriever_out) or {}
        selected_ids = retriever_json.get("selected_ids", [])
        selected_units: list[EvidenceUnit] = []
        if isinstance(selected_ids, list):
            for raw_idx in selected_ids:
                try:
                    idx = int(raw_idx)
                except (TypeError, ValueError):
                    continue
                if 1 <= idx <= len(evidence_units):
                    selected_units.append(evidence_units[idx - 1])
        if not selected_units:
            selected_units = evidence_units[:selected_evidence_limit]

        selected_rendered = render_evidence_list(
            selected_units, selected_evidence_limit
        )

        ref_block_api = ""
        if ref_section_body:
            ref_block_api = (
                "\nReference Section Draft (your primary starting point — improve and refine this):\n"
                "---BEGIN REFERENCE DRAFT---\n"
                + ref_section_body
                + "\n---END REFERENCE DRAFT---\n\n"
                "Improve and refine the Reference Draft above. Preserve accurate technical content. "
                "Identify gaps and strengthen weak arguments. "
            )

        writer_user = (
            common_context
            + "\n"
            + "Planner output:\n"
            + json.dumps(planner_json, ensure_ascii=False, indent=2)
            + "\n\n"
            + "Retriever output:\n"
            + json.dumps(retriever_json, ensure_ascii=False, indent=2)
            + "\n\n"
            + "Selected evidence:\n"
            + selected_rendered
            + "\n\n"
            + ref_block_api
            + "Write LaTeX body for this section only. Do not include \\section{...}."
        )
        writer_out = ask_agent(
            role_name="Writer",
            system_prompt=system_prompt,
            user_prompt=writer_user,
            llm_cfg=llm_cfg,
            dry_run=args.dry_run,
        )
        (section_log_dir / "writer.md").write_text(writer_out, encoding="utf-8")

        verifier_user = (
            common_context
            + "\n"
            + "Selected evidence:\n"
            + selected_rendered
            + "\n\n"
            + ref_block_api
            + "Draft section body (writer output to verify):\n"
            + writer_out
            + "\n\n"
            + "Revise the draft to remove unsupported claims and strengthen evidence alignment. "
            + "Hard gate: reject output if Section Blueprint constraints are not satisfied.\n"
            + "For equation-heavy sections, verify formulas and notation are consistent with the listed Equation Source PDFs.\n"
            + "Return only final LaTeX section body without markdown fences and without \\section{...}."
        )
        verifier_out = ask_agent(
            role_name="Verifier",
            system_prompt=system_prompt,
            user_prompt=verifier_user,
            llm_cfg=llm_cfg,
            dry_run=args.dry_run,
        )
        (section_log_dir / "verifier.md").write_text(verifier_out, encoding="utf-8")

        judge_result = judge_verifier_alignment(
            common_context=common_context,
            selected_rendered=selected_rendered,
            verifier_out=verifier_out,
            llm_cfg=llm_cfg,
            dry_run=args.dry_run,
        )
        (section_log_dir / "verifier_judge.json").write_text(
            json.dumps(judge_result, ensure_ascii=False, indent=2), encoding="utf-8"
        )

        retry_required = bool(judge_result.get("retry_required", False))
        retry_count = 0
        while retry_required and retry_count < max_verifier_retries:
            retry_count += 1
            focus_points = judge_result.get("focus_points", [])
            if not isinstance(focus_points, list):
                focus_points = []
            focus_block = (
                "\n".join(f"- {x}" for x in focus_points)
                or "- Keep claims tightly grounded in selected evidence."
            )

            verifier_retry_user = (
                common_context
                + "\n"
                + "Selected evidence:\n"
                + selected_rendered
                + "\n\n"
                + "Previous verifier output:\n"
                + verifier_out
                + "\n\n"
                + "Alignment issue summary:\n"
                + str(judge_result.get("reason", "No reason provided."))
                + "\n\n"
                + "Focus points for revision:\n"
                + focus_block
                + "\n\n"
                + "Rewrite this section to remove evidence mismatch risk. "
                + "Return only final LaTeX section body without markdown fences and without \\section{...}."
            )
            verifier_out = ask_agent(
                role_name=f"VerifierRetry{retry_count}",
                system_prompt=system_prompt,
                user_prompt=verifier_retry_user,
                llm_cfg=llm_cfg,
                dry_run=args.dry_run,
            )
            (section_log_dir / f"verifier_retry_{retry_count}.md").write_text(
                verifier_out, encoding="utf-8"
            )

            judge_result = judge_verifier_alignment(
                common_context=common_context,
                selected_rendered=selected_rendered,
                verifier_out=verifier_out,
                llm_cfg=llm_cfg,
                dry_run=args.dry_run,
            )
            (section_log_dir / f"verifier_judge_retry_{retry_count}.json").write_text(
                json.dumps(judge_result, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            retry_required = bool(judge_result.get("retry_required", False))

        final_body = strip_fence(verifier_out)
        if args.dry_run and final_body.startswith("[DRY-RUN:"):
            final_body = (
                "% DRY-RUN placeholder generated by run_multi_agent.py\n"
                f"TODO: Replace with model-generated content for section: {section}.\n"
            )

        if section.lower() == "abstract":
            current_tex = replace_abstract(current_tex, final_body)
        else:
            current_tex = replace_section_body(current_tex, section, final_body)

    draft_output_path.write_text(current_tex, encoding="utf-8")

    if execution_mode == "copilot-queue":
        manifest_path = run_log_dir / "copilot_queue_manifest.json"
        manifest_path.write_text(
            json.dumps(queue_manifest, ensure_ascii=False, indent=2), encoding="utf-8"
        )
        guide_path = run_log_dir / "copilot_queue_guide.md"
        guide_path.write_text(
            "# Copilot Queue Guide\n\n"
            "1. For each section directory, run planner_task.md in Copilot chat and save JSON to planner_output.json.\n"
            "2. Run retriever_task.md and save JSON to retriever_output.json.\n"
            "3. Run writer_task.md and save text to writer_output.md.\n"
            "4. Run verifier_task.md and save text to verifier_output.md.\n"
            "5. Apply verifier_output.md to the target section in draft using apply_task.md.\n"
            "\n"
            f"Draft target: {draft_tex_output}\n",
            encoding="utf-8",
        )

    print(f"Draft written to: {draft_output_path}")
    print(f"Sections processed: {len(sections)}")
    print(f"Contributions imported from source: {len(contributions)}")
    print(f"Run logs: {run_log_dir}")
    if execution_mode == "copilot-queue":
        print("Execution mode: copilot-queue")
        print(f"Queue manifest: {run_log_dir / 'copilot_queue_manifest.json'}")


if __name__ == "__main__":
    run()
