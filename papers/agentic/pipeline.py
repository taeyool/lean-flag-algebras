from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable


DECL_RE = re.compile(r"^\s*(theorem|lemma|def|structure|class)\s+([A-Za-z0-9_'.]+)")

# Broad keyword set for extracting meaningful lines from .tex and other text files.
# Covers both mathematical content and Lean-specific terms appearing in paper_claude.tex.
TEX_KEYWORDS = [
    "flag", "density", "mantel", "pentagon", "proof", "compute",
    "theorem", "lemma", "definition", "algebra", "formaliz", "lean",
    "reflect", "tactic", "quotient", "homomorphism", "semidefinit",
    "positiv", "isomorphism", "combinatori", "extremal",
    "concrete", "decidabl", "native_decide", "kernel",
    "ldl", "sdp", "certificate", "embedding", "induced", "subflag",
    "graph", "vertex", "edge", "abstract", "section", "turán",
    "razborov", "erdős", "pentagon", "triangle", "bipartite",
    "elaborat", "syntax", "ast", "naming", "convention", "sort",
    "expand", "multipli", "normaliz", "adequacy", "sym2",
    "forbid", "downward", "measure", "probabil", "convergent",
    "quotient", "module", "ring", "commutative", "algebra",
]


@dataclass
class EvidenceUnit:
    section: str
    source_path: str
    symbol_kind: str
    symbol_name: str
    line_number: int
    snippet: str


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def extract_contributions_from_tex(tex: str) -> list[str]:
    lines = tex.splitlines()
    in_contrib_subsection = False
    in_itemize = False
    current_item: list[str] = []
    items: list[str] = []

    for raw_line in lines:
        line = raw_line.strip()

        if not in_contrib_subsection:
            if line.startswith(r"\subsection{Contributions}"):
                in_contrib_subsection = True
            continue

        if not in_itemize:
            if line.startswith(r"\begin{itemize}"):
                in_itemize = True
            continue

        if line.startswith(r"\end{itemize}"):
            if current_item:
                items.append(" ".join(part for part in current_item if part).strip())
            break

        if line.startswith(r"\item"):
            if current_item:
                items.append(" ".join(part for part in current_item if part).strip())
            current_item = [line[len(r"\item") :].strip()]
        elif current_item:
            current_item.append(line)

    return [item for item in items if item]


def render_seed_draft_tex(project_name: str, contributions: list[str]) -> str:
    contribution_lines = "\n".join(f"    \\item {item}" for item in contributions)
    if not contribution_lines:
        contribution_lines = "    \\item TODO: Add contributions from source paper."

    return f"""\\documentclass{{article}}

\\usepackage{{hyperref}}
\\usepackage{{amsmath}}
\\usepackage{{mathtools}}
\\usepackage{{amssymb}}
\\usepackage{{amsthm}}

\\title{{{project_name}}}
\\date{{}}

\\begin{{document}}
\\maketitle

\\begin{{abstract}}
TODO: Write an abstract.
\\end{{abstract}}

\\section{{Introduction}}

\\subsection{{Contributions}}
\\begin{{itemize}}
{contribution_lines}
\\end{{itemize}}

\\section{{Background on Flag Algebra}}
TODO

\\section{{Formalization of Flag Algebra}}
TODO

\\section{{Computable Definition of Flags}}
TODO

\\section{{Application}}
TODO

\\section{{Conclusion}}
TODO

\\end{{document}}
"""


def iter_source_files(root: Path, source_paths: Iterable[str]) -> Iterable[Path]:
    for rel in source_paths:
        p = root / rel
        if p.exists() and p.is_file():
            yield p


def extract_evidence(
    section: str, root: Path, source_paths: list[str], max_lines: int
) -> list[EvidenceUnit]:
    units: list[EvidenceUnit] = []
    for file_path in iter_source_files(root, source_paths):
        if file_path.suffix not in {".lean", ".py", ".tex", ".md", ".json"}:
            continue

        lines = read_text(file_path).splitlines()
        capped = lines[:max_lines]

        if file_path.suffix == ".lean":
            for i, line in enumerate(capped, start=1):
                m = DECL_RE.match(line)
                if m:
                    units.append(
                        EvidenceUnit(
                            section=section,
                            source_path=str(file_path.relative_to(root)).replace(
                                "\\", "/"
                            ),
                            symbol_kind=m.group(1),
                            symbol_name=m.group(2),
                            line_number=i,
                            snippet=line.strip(),
                        )
                    )
        else:
            # For non-Lean files, keep high-signal lines as plain evidence snippets.
            for i, line in enumerate(capped, start=1):
                if len(line.strip()) < 12:
                    continue
                if any(tok in line.lower() for tok in TEX_KEYWORDS):
                    units.append(
                        EvidenceUnit(
                            section=section,
                            source_path=str(file_path.relative_to(root)).replace(
                                "\\", "/"
                            ),
                            symbol_kind="text",
                            symbol_name="line",
                            line_number=i,
                            snippet=line.strip(),
                        )
                    )

    return units


def extract_section_body_from_tex(tex: str, section_name: str) -> str:
    """Return the body of a named \\section{} from a TeX string (empty string if not found)."""
    sec_pat = re.compile(rf"\\section\{{{re.escape(section_name)}\}}")
    m = sec_pat.search(tex)
    if not m:
        return ""
    body_start = m.end()
    next_sec = re.search(r"\n\\section\{", tex[body_start:])
    end_doc = tex.find("\\end{document}")
    if next_sec:
        body_end = body_start + next_sec.start()
    elif end_doc != -1:
        body_end = end_doc
    else:
        body_end = len(tex)
    return tex[body_start:body_end].strip()


def extract_abstract_from_tex(tex: str) -> str:
    """Return the abstract body from a TeX string (empty string if not found)."""
    m = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, re.DOTALL)
    return m.group(1).strip() if m else ""


def build_agent_prompt(
    project_name: str,
    section: str,
    paper_tex_path: str,
    considerations: str,
    author_notes: str,
    global_instructions: list[str],
    section_instructions: list[str],
    evidence: list[EvidenceUnit],
) -> str:
    evidence_lines = []
    for u in evidence[:80]:
        evidence_lines.append(
            f"- [{u.symbol_kind}] {u.symbol_name} @ {u.source_path}:{u.line_number} :: {u.snippet}"
        )

    if not evidence_lines:
        evidence_block = "- (No evidence found. Expand sources in config.json.)"
    else:
        evidence_block = "\n".join(evidence_lines)

    section_instruction_block = "\n".join(f"- {item}" for item in section_instructions)
    if not section_instruction_block:
        section_instruction_block = "- (No section-specific instructions configured.)"

    global_instruction_block = "\n".join(f"- {item}" for item in global_instructions)
    if not global_instruction_block:
        global_instruction_block = "- (No global instructions configured.)"

    return f"""# Agent Task: Draft Section\n\nProject: {project_name}\nTarget Section: {section}\nTarget TeX: {paper_tex_path}\n\n## Mandatory Considerations\n{considerations}\n\n## Author Notes\n{author_notes}\n\n## Global Instructions\n{global_instruction_block}\n\n## Section-Specific Instructions\n{section_instruction_block}\n\n## Retrieved Evidence\n{evidence_block}\n\n## Instructions\n1. Write one coherent section draft in academic style.\n2. Do not invent theorem names or file paths.\n3. Ensure each nontrivial claim is grounded in Retrieved Evidence.\n4. Respect Mandatory Considerations first, then adapt wording to Author Notes.\n5. You may adjust section structure if it improves clarity, but explain the change briefly.\n6. End with a short 'Evidence Coverage' list mapping key claims to evidence lines.\n"""


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate prompt bundles for an agentic paper-writing workflow."
    )
    parser.add_argument("--root", default=".", help="Repository root path")
    parser.add_argument(
        "--config", default="papers/agentic/config.json", help="Config path"
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    config_path = root / args.config

    if not config_path.exists():
        raise FileNotFoundError(f"Config not found: {config_path}")

    config = json.loads(read_text(config_path))
    project_name = config["project_name"]
    source_paper_tex = config["paper_tex"]
    contribution_source_tex = config.get("contribution_source_tex", source_paper_tex)
    draft_tex_output = config.get(
        "draft_tex_output", "papers/agentic/out/paper_draft_from_contributions.tex"
    )
    considerations_path = root / config["considerations_file"]
    author_notes_path = root / config.get("author_notes_file", "")
    out_dir = root / config["output_dir"]
    default_sections = config["default_sections"]
    section_sources = config["section_sources"]
    section_instructions_map = config.get("section_instructions", {})
    global_instructions = config.get("global_instructions", [])
    max_lines = int(config["retrieval"]["max_lines_per_file"])

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
    out_dir.mkdir(parents=True, exist_ok=True)

    # Determine seed draft: use base_draft_tex if configured, else generate a minimal skeleton.
    base_draft_tex = config.get("base_draft_tex", "")
    contribution_source_path = root / contribution_source_tex
    draft_output_path = root / draft_tex_output
    source_tex_text = (
        read_text(contribution_source_path) if contribution_source_path.exists() else ""
    )
    contributions = extract_contributions_from_tex(source_tex_text)
    draft_output_path.parent.mkdir(parents=True, exist_ok=True)

    base_draft_path = root / base_draft_tex if base_draft_tex else None
    if base_draft_path and base_draft_path.exists():
        import shutil
        shutil.copy2(base_draft_path, draft_output_path)
    else:
        draft_output_path.write_text(
            render_seed_draft_tex(project_name=project_name, contributions=contributions),
            encoding="utf-8",
        )

    all_units: list[EvidenceUnit] = []

    for section in default_sections:
        sources = section_sources.get(section, [])
        units = extract_evidence(
            section=section, root=root, source_paths=sources, max_lines=max_lines
        )
        all_units.extend(units)

        prompt = build_agent_prompt(
            project_name=project_name,
            section=section,
            paper_tex_path=draft_tex_output,
            considerations=considerations,
            author_notes=author_notes,
            global_instructions=global_instructions,
            section_instructions=section_instructions_map.get(section, []),
            evidence=units,
        )

        safe_name = re.sub(r"[^A-Za-z0-9]+", "_", section).strip("_").lower()
        (out_dir / f"prompt_{safe_name}.md").write_text(prompt, encoding="utf-8")

    evidence_json = [asdict(u) for u in all_units]
    (out_dir / "evidence_units.json").write_text(
        json.dumps(evidence_json, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    print(f"Generated prompts and evidence in: {out_dir}")
    print(f"Generated seeded draft TeX: {draft_output_path}")
    print(f"Imported contributions: {len(contributions)}")
    print(f"Total evidence units: {len(all_units)}")


if __name__ == "__main__":
    main()
