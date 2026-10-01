"""Check that the Lean names displayed in paper_afm.tex exist in the code.

Every identifier in a \\lean{...} command or in an lstlisting block is looked
up as a declaration in

  * the development repo (this repository, excluding LeanFlagAlgebras/Archive,
    which is not built),
  * the public release repo (a sibling checkout, if present),
  * Mathlib and Lean core.

Identifiers declared nowhere are listed with their first plain-text hit in
the development repo, for manual review.  Most of them are local variables or
LaTeX residue; the ones that matter are names of definitions or theorems.

Usage (from the repository root):

    PYTHONUTF8=1 python papers/AFM/name_audit.py
        [--release ../lean-flag-algebras-release]
        [--core <toolchain>/src/lean]

Last run against the development repo (main) on 2026-10-01; re-run against the
release commit once the release repo has been synced.
"""
import argparse
import os
import re
import subprocess
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))

MATH = [
    (r"\sigma", "σ"), (r"\mathbb{N}", "ℕ"), (r"\mathbb{Q}", "ℚ"), (r"\mathbb{R}", "ℝ"),
    (r"\mathbb{P}", "ℙ"), (r"\phi_0", "φ₀"), (r"\phi", "φ"), (r"\ell_0", "ℓ₀"),
    (r"\ell_1", "ℓ₁"), (r"\ell_2", "ℓ₂"), (r"\ell", "ℓ"), (r"\emptyt", "∅ₜ"),
    (r"\leansmul", "•"), (r"\Sigma", "Σ"), (r"\pi", "π"), (r"\times", "×"),
    (r"\llbracket", " "), (r"\rrbracket", " "), (r"\langle", " "), (r"\rangle", " "),
    (r"\simeq", " "), (r"\hookrightarrow", " "), (r"\circ", " "), (r"\leq", " "),
    (r"\wedge", " "), (r"\subseteq", " "), (r"\in", " "), (r"\partial", " "),
    (r"\itshape", " "), (r"\forall", " "), (r"\exists", " "), (r"\neg", " "),
    (r"_0", "₀"), (r"_1", "₁"), (r"_2", "₂"), (r"\to", " "),
]
IDENT = re.compile(r"[A-Za-z_ασφπℓ][A-Za-z0-9_.'ασφπℓ₀-₉!?]*")
SKIP = set("""def theorem lemma instance structure class abbrev noncomputable where fun let
have by exact rw if then else Type Prop variable notation infixl at with do return show from
example import open namespace end section in dsimp infer_instance isFalse some none true false
Sort decide kernel native_decide this mul le r iseqv elems complete Adj symm loopless rfl
mathcal mathtt textcolor texttt sorry partial json cert""".split())
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|instance|inductive|alias|opaque|axiom|register_option)\s+"
    r"([^\s:({\[]+)")


def demath(s):
    s = re.sub(r"\\(textcolor|mathcal|mathtt)\{[^}]*\}", " ", s)
    s = re.sub(r"\\texttt\{", "{", s)
    s = s.replace(r"\_", "_").replace(r"\allowbreak", "").replace(r"\,", " ")
    for a, b in MATH:
        s = s.replace(a, b)
    return s.replace("$", "")


def lean_args(text):
    for m in re.finditer(r"\\lean\{", text):
        i, depth = m.end(), 1
        while i < len(text) and depth:
            depth += {"{": 1, "}": -1}.get(text[i], 0)
            i += 1
        yield text.count("\n", 0, m.start()) + 1, text[m.end():i - 1]


def paper_idents(path):
    text = open(path, encoding="utf-8").read()
    found = defaultdict(set)
    for line, arg in lean_args(text):
        for tok in IDENT.findall(demath(arg)):
            found[tok.rstrip(".")].add(line)
    for m in re.finditer(r"\\begin\{lstlisting\}(\[[^\]]*\])?(.*?)\\end\{lstlisting\}", text, re.S):
        if m.group(1) and "language={}" in m.group(1):
            continue
        base = text.count("\n", 0, m.start()) + 1
        body = re.sub(r"\(\*@(.*?)@\*\)", lambda e: demath(e.group(1)), m.group(2), flags=re.S)
        for k, ln in enumerate(body.split("\n")):
            for tok in IDENT.findall(ln.split("--")[0]):
                found[tok.rstrip(".")].add(base + k)
    return {k: v for k, v in found.items() if len(k) > 1 and k not in SKIP}


def lean_files(root, skip_archive):
    for dp, dirs, fs in os.walk(root):
        dirs[:] = [d for d in dirs if d != ".lake" and not (skip_archive and d == "Archive")]
        for f in fs:
            if f.endswith(".lean"):
                yield os.path.join(dp, f)


def index_decls(root, skip_archive=False):
    idx = defaultdict(list)
    if not root or not os.path.isdir(root):
        return idx
    for p in lean_files(root, skip_archive):
        try:
            lines = open(p, encoding="utf-8").read().split("\n")
        except Exception:
            continue
        for n, ln in enumerate(lines, 1):
            m = DECL.match(ln)
            if m:
                parts = m.group(1).split(".")
                for i in range(len(parts)):
                    idx[".".join(parts[i:])].append(f"{os.path.relpath(p, root)}:{n}")
    return idx


def first_text_hit(root, tok):
    pat = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(tok) + r"(?![A-Za-z0-9_])")
    for p in lean_files(root, skip_archive=True):
        try:
            for n, ln in enumerate(open(p, encoding="utf-8"), 1):
                if pat.search(ln):
                    return f"{os.path.relpath(p, root)}:{n}: {ln.strip()[:90]}"
        except Exception:
            pass
    return "no text hit"


def default_core():
    try:
        prefix = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True).stdout.strip()
        return os.path.join(prefix, "src", "lean")
    except Exception:
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper", default=os.path.join(HERE, "paper_afm.tex"))
    ap.add_argument("--dev", default=ROOT)
    ap.add_argument("--release", default=os.path.join(ROOT, "..", "lean-flag-algebras-release"))
    ap.add_argument("--mathlib", default=os.path.join(ROOT, ".lake", "packages", "mathlib", "Mathlib"))
    ap.add_argument("--core", default=default_core())
    a = ap.parse_args()

    dev_lib = os.path.join(a.dev, "LeanFlagAlgebras")
    rel_lib = os.path.join(a.release, "LeanFlagAlgebras")
    idx = {
        "dev": index_decls(dev_lib, skip_archive=True),
        "release": index_decls(rel_lib),
        "mathlib": index_decls(a.mathlib),
        "core": index_decls(a.core),
    }
    names = paper_idents(a.paper)
    ours, external, missing = [], [], []
    for tok in sorted(names):
        where = {k: v[0] for k, v in ((k, idx[k].get(tok)) for k in idx) if v}
        if "dev" in where or "release" in where:
            ours.append((tok, where))
        elif where:
            external.append((tok, where))
        else:
            missing.append(tok)

    print(f"identifiers: {len(names)}  ours: {len(ours)}  Mathlib/core: {len(external)}  undeclared: {len(missing)}")
    if os.path.isdir(rel_lib):
        print("in dev but not release:", [t for t, w in ours if "release" not in w])
        print("in release but not dev:", [t for t, w in ours if "dev" not in w])
    else:
        print(f"(release repo not found at {a.release}; skipped)")
    print("--- undeclared: check by hand (most are local variables or LaTeX residue) ---")
    for tok in missing:
        print(f"{tok:45s} paper:{sorted(names[tok])[:3]}  {first_text_hit(dev_lib, tok)}")


if __name__ == "__main__":
    main()
