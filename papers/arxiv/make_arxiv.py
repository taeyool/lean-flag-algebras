#!/usr/bin/env python3
"""Generate the arXiv-ready source `paper_arxiv.tex` from `paper_draft.tex`.

What it strips (and nothing else):
  * every `\\sh{...}` / `\\gw{...}` / `\\hy{...}` review note (brace-matched,
    multi-line safe), plus the three `\\newcommand` definitions themselves;
    if removing a note leaves a line blank, the whole line is dropped so no
    spurious paragraph break is introduced;
  * comment text: full-line `%` comments are deleted; for inline comments the
    text after `%` is dropped but the `%` itself is kept, so end-of-line
    whitespace suppression (`...{%`) behaves exactly as before;
  * runs of blank lines are collapsed to a single blank line.

What it protects:
  * the bodies of `lstlisting` / `verbatim` environments (copied verbatim);
  * escaped percents `\\%` (an unescaped `%` is always a comment in TeX, so
    outside verbatim contexts stripping is semantics-preserving).

Usage (from `papers/POPL27/`):  python make_arxiv.py
Re-run right before every arXiv submission; do not edit paper_arxiv.tex by hand.
"""

from __future__ import annotations

import io
import re
from pathlib import Path

SRC = Path(__file__).with_name("paper_draft.tex")
DST = Path(__file__).with_name("paper_arxiv.tex")

NOTE_MACROS = ("\\sh{", "\\gw{", "\\hy{")
NOTE_DEF_RE = re.compile(r"^\\newcommand\{\\(?:sh|gw|hy)\}")
VERBATIM_BEGIN = re.compile(r"\\begin\{(lstlisting|verbatim)[*]?\}")
VERBATIM_END = re.compile(r"\\end\{(lstlisting|verbatim)[*]?\}")


def find_note(text: str) -> tuple[int, int] | None:
    """Return (start, end) of the first review-note macro call, brace-matched."""
    starts = [(text.find(m), m) for m in NOTE_MACROS if text.find(m) != -1]
    if not starts:
        return None
    start, macro = min(starts)
    depth = 1
    i = start + len(macro)
    while i < len(text) and depth > 0:
        c = text[i]
        if c == "\\" and i + 1 < len(text):
            i += 2  # skip escaped character (e.g. \{, \})
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        i += 1
    if depth != 0:
        raise SystemExit(f"unbalanced braces in review note at offset {start}")
    return start, i


def strip_notes(text: str) -> str:
    """Remove every review-note call; drop the line if it becomes blank."""
    while True:
        span = find_note(text)
        if span is None:
            return text
        start, end = span
        line_start = text.rfind("\n", 0, start) + 1
        line_end = text.find("\n", end)
        line_end = len(text) if line_end == -1 else line_end
        rest = text[line_start:start] + text[end:line_end]
        if rest.strip() == "":
            # the note was the whole line (possibly spanning lines): drop it
            text = text[:line_start] + text[line_end + 1 if line_end < len(text) else line_end:]
        else:
            text = text[:start] + text[end:]


def first_comment_pos(line: str) -> int | None:
    """Index of the first unescaped % in `line`, or None."""
    i = 0
    while i < len(line):
        c = line[i]
        if c == "\\":
            i += 2  # \% or any escaped char
            continue
        if c == "%":
            return i
        i += 1
    return None


def main() -> None:
    text = io.open(SRC, encoding="utf-8").read()
    text = strip_notes(text)

    out: list[str] = []
    in_verbatim = False
    for line in text.split("\n"):
        if in_verbatim:
            out.append(line)
            if VERBATIM_END.search(line):
                in_verbatim = False
            continue
        if VERBATIM_BEGIN.search(line):
            out.append(line)
            if not VERBATIM_END.search(line):
                in_verbatim = True
            continue
        if NOTE_DEF_RE.match(line):
            continue  # drop the \sh / \gw / \hy definitions
        pos = first_comment_pos(line)
        if pos is not None:
            if line[:pos].strip() == "":
                continue  # full-line comment: drop
            line = line[: pos + 1]  # keep the %, drop the comment text
        out.append(line)

    # Collapse runs of blank lines (outside verbatim nothing needs >1 blank).
    collapsed: list[str] = []
    verbatim = False
    for line in out:
        if VERBATIM_BEGIN.search(line):
            verbatim = True
        elif VERBATIM_END.search(line):
            verbatim = False
        if not verbatim and line.strip() == "" and collapsed and collapsed[-1].strip() == "":
            continue
        collapsed.append(line)

    header = (
        "% Generated from paper_draft.tex by make_arxiv.py (review notes and\n"
        "% comments stripped for arXiv). Do not edit; regenerate instead.\n"
    )
    io.open(DST, "w", encoding="utf-8", newline="\n").write(header + "\n".join(collapsed))
    print(f"wrote {DST.name}: {len(collapsed)} lines (from {len(text.splitlines())})")


if __name__ == "__main__":
    main()
