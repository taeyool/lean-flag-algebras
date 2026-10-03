"""Generate the artifact tables of Appendix B from a pinned release commit.

Writes three LaTeX tables into paper_afm.tex, between the markers

    %% BEGIN GENERATED: artifact tables (papers/AFM/artifact_appendix.py)
    %% END GENERATED: artifact tables

  * the statement-to-declaration table: every row links to the declaration's
    file and line at the pinned commit on GitHub;
  * the SHA-256 digests of the seven certificate files;
  * the size of each component (files, lines, source declarations) and the
    number of declarations each certificate file elaborates to.

Everything is read from the release repository at the given ref with
`git show`, so the working tree does not matter.  The elaborated-declaration
counts come from `checks/artifact_counts.txt`, the output of
`lake env lean papers/AFM/checks/CountGen.lean` run in the release checkout.

Usage (from the repository root):

    PYTHONUTF8=1 python papers/AFM/artifact_appendix.py
        [--release ../lean-flag-algebras-release] [--ref v1.0]

Re-run it whenever the release tag moves.
"""
import argparse
import hashlib
import os
import re
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
PAPER = os.path.join(HERE, "paper_afm.tex")
COUNTS = os.path.join(HERE, "checks", "artifact_counts.txt")
URL = "https://github.com/taeyool/lean-flag-algebras-release"
BEGIN = "%% BEGIN GENERATED: artifact tables (papers/AFM/artifact_appendix.py)"
END = "%% END GENERATED: artifact tables"
BS = "\\"

# (paper reference, statement, [declarations], path hint or None)
ROWS = [
    (r"\Cref{lem:chain-rule}", "Chain rule", ["flagDensity_eq_sum_density_prods"], None),
    (r"\Cref{sec:background-densities}", "Product independent of the auxiliary size",
     ["flagMulWithSize_indep_on_size"], None),
    (r"\Cref{thm:convergent-hom}(a)", "Limits of convergent sequences are positive homomorphisms",
     ["flagSeq_limit_mem_positiveHom"], None),
    (r"\Cref{thm:convergent-hom}(b)", "Every positive homomorphism is such a limit",
     ["positiveHom_as_flagSeq_limit"], None),
    (r"\Cref{sec:background-downward}", "Random extension of an empty-type homomorphism",
     ["exists_probMeasure_extend_emptyType_positiveHom"], None),
    (r"\Cref{thm:downward-nonneg}", "The downward operator preserves non-negativity",
     ["downward_preserve_semanticCone"], None),
    (r"\Cref{thm:downward-nonneg}", "The same in the $H$-free order used by certificates",
     ["downward_forbidLEWith_nonneg"], None),
    (r"\Cref{sec:lowerbounds}", "Cauchy--Schwarz for the downward operator",
     ["Cauchy_Schwarz_inequality_unit"], None),
    (r"\Cref{sec:forbidden}", "The Tur\\'an density is a limit", ["tendsto_generalizedTuranDensity"], None),
    (r"\Cref{lem:semantic-bound}", "A semantic inequality bounds the Tur\\'an density",
     ["generalizedTuranDensity_le_of_forbidLE"], None),
    (r"\Cref{def:ensemble-semantic-order}", "Ensemble semantic order", ["forbidLE"], "Forbid/"),
    (r"\Cref{sec:reflection-adequacy}", "Adequacy of the computable densities",
     ["flagDensity₁_eq_sym2FlagDensity₁", "flagDensity₂_eq_sym2FlagDensity₂"], None),
    (r"\Cref{sec:reflection-adequacy}", "Adequacy of the downward factors",
     ["downwardNormalizingFactor_eq"], "FlagAlgebra/Compute/"),
    (r"\Cref{sec:reflection-adequacy}", "Densities are invariant under relabeling",
     ["flagDensity_permute"], None),
    (r"\Cref{sec:flagmatic-background}", "PSD from a rational $LDL^{\\top}$ factorization",
     ["posSemidef_real_of_LDLt"], None),
    (r"\Cref{sec:flagmatic-background}", "Adding a downward quadratic form",
     ["forbidLEWith_add_QuadraticForm"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "Edge density, $K_3$-free", ["Mantel_turanDensity"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "$P_3$ density, $K_3$-free", ["K3freeP3_turanDensity"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "$C_4$ density, $K_3$-free", ["K3freeC4_turanDensity"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "Edge density, $K_4$-free", ["K4freeEdge_turanDensity"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "$C_5$ density, $K_3$-free", ["ErdosPentagon_turanDensity"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "Edge density, $K_5$-free", ["K5freeEdge_turanDensity"], None),
    (r"\Cref{tab:flagmatic-scenarios}", "Edge density, $C_5$-free", ["C5freeEdge_turanDensity"], None),
    (r"\Cref{ex:mantel}", "Asymptotic Mantel theorem", ["Mantel_Turan"], None),
    (r"\Cref{ex:pentagon}", "Asymptotic Erd\\H{o}s pentagon theorem", ["ErdosPentagon_Turan"], None),
    (r"\Cref{sec:lowerbounds}", "Pentagon lower bound", ["ErdosPentagon_Turan_lowerBound"], None),
    (r"\Cref{sec:lowerbounds}", "$C_5$ and the certificate's target agree",
     ["C5_toFlagAlgebra_eq_certificate"], None),
    (r"\Cref{sec:lowerbounds}", "Goodman's triangle bound", ["Goodman_bound_on_triangle_density"], None),
    (r"\Cref{sec:lowerbounds}", "Goodman's Ramsey multiplicity bound",
     ["Goodman_theorem_on_Ramsey_multiplicity"], None),
    (r"\Cref{def:two-constrained-orders}", "Quotient and ensemble orders",
     ["QuotientNonneg", "EnsembleNonneg"], None),
    (r"\Cref{thm:support-closure-summary}", "Support-closure criterion",
     ["quotient_implies_ensemble", "support_criterion"], None),
    (r"\Cref{thm:blowup-root-plantability-summary}", "Blow-up closure implies root-plantability",
     ["blowupClosed_root_plantable", "heredClass_emptyType_rootPlantable"], None),
    (r"\Cref{sec:metatheory}", "The $C_4$-free class is not root-plantable",
     ["c4free_not_rootPlantable", "Sσ_subset_Qσ"], None),
]

CERTS = [("Mantel", "Mantel_cert.json"), ("$P_3$, $K_3$-free", "K3freeP3_cert.json"),
         ("$C_4$, $K_3$-free", "K3freeC4_cert.json"), ("Edge, $K_4$-free", "K4freeEdge_cert.json"),
         ("Erd\\H{o}s pentagon", "ErdosPentagon_cert.json"), ("Edge, $K_5$-free", "K5freeEdge_cert.json"),
         ("Edge, $C_5$-free", "C5freeEdge_cert.json")]

# component label, directory prefixes (relative to LeanFlagAlgebras/), excluded prefixes
COMPONENTS = [
    ("Specification (flags, densities, flag algebras)", ["FlagAlgebra/", "GraphAlgebra/", "Utils/"],
     ["FlagAlgebra/Compute/"]),
    ("Reflection (computable densities, generators, bit masks)",
     ["FlagAlgebra/Compute/", "Flags/", "BitMask/"], []),
    ("Certificate checking and the seven certificates", ["Automation/", "Flagmatic/"], []),
    ("Forbidden subgraphs and Tur\\'an densities", ["Forbid/", "Turan/"], []),
    ("Mantel, pentagon, and Goodman theorems", ["MantelTheorem/", "ErdosPentagon/"], []),
    ("Meta-theory", ["MetaTheory/", "MetaTheory.lean"], []),
]
CASE_MODULES = ["Mantel", "K3freeP3", "K3freeC4", "K4freeEdge", "ErdosPentagon", "K5freeEdge", "C5freeEdge"]

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
    r"(theorem|lemma|alias|def|abbrev|instance|structure|class|inductive|opaque)\b\s*([^\s:({\[]*)",
    re.M)


def git(release, *args, binary=False):
    out = subprocess.run(["git", "-C", release, *args], capture_output=True, check=True)
    return out.stdout if binary else out.stdout.decode("utf-8")


def tex_name(name):
    s = name.replace("_", BS + "_")
    for u, t in (("₁", "$_1$"), ("₂", "$_2$"), ("σ", "$" + BS + "sigma$")):
        s = s.replace(u, t)
    return BS + "lean{" + s + "}"


def tex_path(path):
    return path.replace("_", BS + "_")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--release", default=os.path.join(ROOT, "..", "lean-flag-algebras-release"))
    ap.add_argument("--ref", default="v1.0")
    args = ap.parse_args()
    rel = os.path.normpath(args.release)
    sha = git(rel, "rev-parse", args.ref + "^{commit}").strip()
    files = [f for f in git(rel, "ls-tree", "-r", "--name-only", sha).split("\n") if f]
    lean = {f: git(rel, "show", f"{sha}:{f}") for f in files
            if f.startswith("LeanFlagAlgebras/") and f.endswith(".lean")}

    # ---- statement-to-declaration table
    def locate(name, hint):
        hits = []
        for f, src in lean.items():
            for m in DECL.finditer(src):
                decl = m.group(2)
                if decl == name or decl.endswith("." + name):
                    hits.append((f, src.count("\n", 0, m.start()) + 1))
        if hint:
            hits = [h for h in hits if h[0].startswith("LeanFlagAlgebras/" + hint)] or hits
        if len(hits) != 1:
            raise SystemExit(f"{name}: expected one declaration, found {hits}")
        return hits[0]

    rows = []
    for ref, stmt, names, hint in ROWS:
        decls, locs = [], []
        for n in names:
            f, line = locate(n, hint)
            short = f[len("LeanFlagAlgebras/"):]
            decls.append(tex_name(n))
            locs.append(BS + "href{" + f"{URL}/blob/{sha}/{f}" + BS + f"#L{line}" + "}{"
                        + BS + "nolinkurl{" + short + f":{line}" + "}}")
        nl = " " + BS + "newline "
        rows.append(f"    {ref} & {stmt} & {nl.join(decls)} & {nl.join(locs)} " + BS + BS)

    # ---- certificates
    cert_rows = []
    for label, fn in CERTS:
        path = f"LeanFlagAlgebras/Flagmatic/Certificates/{fn}"
        digest = hashlib.sha256(git(rel, "show", f"{sha}:{path}", binary=True)).hexdigest()
        cert_rows.append(f"    {label} & " + BS + "texttt{" + tex_path(fn) + "} & "
                         + BS + "texttt{" + digest[:32] + "}" + BS + BS + "[-2pt]"
                         + " & & " + BS + "texttt{" + digest[32:] + "} " + BS + BS)

    # ---- sizes
    def in_comp(f, incl, excl):
        rel_f = f[len("LeanFlagAlgebras/"):]
        return any(rel_f.startswith(p) for p in incl) and not any(rel_f.startswith(p) for p in excl)

    size_rows, tot = [], [0, 0, 0, 0]
    for label, incl, excl in COMPONENTS:
        fs = [f for f in lean if in_comp(f, incl, excl)]
        nlines = sum(lean[f].count("\n") + (0 if lean[f].endswith("\n") else 1) for f in fs)
        thms = defs = 0
        for f in fs:
            for m in DECL.finditer(lean[f]):
                if m.group(1) in ("theorem", "lemma", "alias"):
                    thms += 1
                else:
                    defs += 1
        for i, v in enumerate((len(fs), nlines, thms, defs)):
            tot[i] += v
        size_rows.append(f"    {label} & {len(fs)} & {nlines:,} & {thms:,} & {defs:,} " + BS + BS)
    size_rows.append(BS + "midrule")
    size_rows.append(f"    Total & {tot[0]} & {tot[1]:,} & {tot[2]:,} & {tot[3]:,} " + BS + BS)

    counts = {}
    if os.path.exists(COUNTS):
        for line in open(COUNTS, encoding="utf-8"):
            m = re.match(r"MODDECLS LeanFlagAlgebras\.Flagmatic\.(\w+) (\d+)", line.strip())
            if m:
                counts[m.group(1)] = int(m.group(2))
            m = re.match(r"PREFIXDECLS LeanFlagAlgebras (\d+)", line.strip())
            if m:
                counts["__all__"] = int(m.group(1))
    gen_cells = []
    for c in CASE_MODULES:
        f = f"LeanFlagAlgebras/Flagmatic/{c}.lean"
        src_decls = len(DECL.findall(lean[f]))
        gen_cells.append((c, lean[f].count("\n"), src_decls, counts.get(c)))

    out = [BEGIN, "% Generated from " + URL + " at " + args.ref + " = " + sha + "; do not edit by hand.",
           "{" + BS + "small" + BS + "setlength{" + BS + "LTcapwidth}{" + BS + "linewidth}",
           BS + "begin{longtable}{@{}p{0.15" + BS + "linewidth}p{0.25" + BS + "linewidth}"
           ">{" + BS + "raggedright" + BS + "arraybackslash}p{0.28" + BS + "linewidth}"
           ">{" + BS + "raggedright" + BS + "arraybackslash}p{0.24" + BS + "linewidth}@{}}",
           BS + "caption{Statements of the paper and the Lean declarations that formalize them, at "
           + BS + "texttt{" + args.ref + "} (commit " + BS + "texttt{" + sha[:12] + "}). Locations are relative to "
           + BS + "texttt{LeanFlagAlgebras/} and link to the tagged source.}" + BS + "label{tab:statement-declaration}" + BS + BS,
           BS + "toprule", "Paper & Statement & Lean declaration & Location " + BS + BS, BS + "midrule",
           BS + "endfirsthead", BS + "toprule", "Paper & Statement & Lean declaration & Location " + BS + BS,
           BS + "midrule", BS + "endhead", BS + "bottomrule", BS + "endfoot",
           *rows, BS + "end{longtable}", "}", "",
           BS + "begin{table}[ht]", BS + "centering", BS + "small",
           BS + "caption{SHA-256 digests of the seven certificate files in "
           + BS + "texttt{LeanFlagAlgebras/Flagmatic/Certificates/} at " + BS + "texttt{" + args.ref + "}.}",
           BS + "label{tab:certificates}", BS + "begin{tabular}{@{}lll@{}}", BS + "toprule",
           "Case & File & SHA-256 " + BS + BS, BS + "midrule", *cert_rows, BS + "bottomrule",
           BS + "end{tabular}", BS + "end{table}", "",
           BS + "begin{table}[ht]", BS + "centering", BS + "small",
           BS + "caption{Size of the development at " + BS + "texttt{" + args.ref + "}, by component: "
           "Lean files, lines, and source declarations (theorems and lemmas; definitions, "
           "abbreviations, instances, structures and classes). Declarations emitted by the "
           "generation commands are not counted here; see " + BS + "Cref{tab:generated}.}",
           BS + "label{tab:size}", BS + "begin{tabular}{@{}lrrrr@{}}", BS + "toprule",
           "Component & Files & Lines & Theorems & Definitions " + BS + BS, BS + "midrule",
           *size_rows, BS + "bottomrule", BS + "end{tabular}"]
    if all(c[3] is not None for c in gen_cells):
        out += [BS + "bigskip",
                BS + "caption{Source size of each certificate file and the number of constants it "
                "adds to the Lean environment (non-internal names), including everything the "
                "generation commands emit"
                + (f"; the whole library adds {counts['__all__']:,}" if "__all__" in counts else "")
                + ".}", BS + "label{tab:generated}", BS + "begin{tabular}{@{}lrrr@{}}", BS + "toprule",
                "File & Lines & Source declarations & Constants " + BS + BS, BS + "midrule"]
        for c, nl, sd, ed in gen_cells:
            out.append("    " + BS + "texttt{" + c + ".lean} & " + f"{nl} & {sd} & {ed:,} " + BS + BS)
        out += [BS + "bottomrule", BS + "end{tabular}"]
    out += [BS + "end{table}", END]
    block = "\n".join(out)

    text = open(PAPER, encoding="utf-8").read()
    if BEGIN in text:
        a = text.index(BEGIN)
        b = text.index(END, a) + len(END)
        text = text[:a] + block + text[b:]
    else:
        raise SystemExit("markers not found in paper_afm.tex; add them where the tables belong")
    open(PAPER, "w", encoding="utf-8").write(text)
    print(f"wrote {len(rows)} statement rows, {len(cert_rows)} certificates, "
          f"{len(COMPONENTS)} components at {args.ref} = {sha}")


if __name__ == "__main__":
    main()
