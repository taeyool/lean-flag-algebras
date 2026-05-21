"""Convert Flagmatic certificates to Lean (flag-algebra API) code.

Flagmatic encodes graphs as strings:

  "N:e1e2..."          unlabeled graph on vertices 1..N with edges given as
                       2-digit position pairs (each digit is one vertex)
  "k:edges"            a type (same form, all vertices labeled by convention)
  "m:edges(k)"         a sigma-flag: m vertices, edges as above, and the
                       parenthesized integer k is the type size. By
                       convention the first k vertices (positions 1..k) are
                       the type vertices in label order.

The Lean side stores canonical representatives in:

  LeanFlagAlgebras/Flags/Graphs/graphs_<n>.json
  LeanFlagAlgebras/Flags/Flags/flags_<m>_<k>_<typeNum>.json

----------------------------------------------------------------------
This file has two layers:

  (1) Library functions — parsing, isomorphism lookup, identifier mapping:
        parse_flagmatic, graph_to_lean, type_to_lean, sigma_flag_to_lean,
        check_dependencies, render_flag_vectors, render_dependency_report

  (2) CLI subcommands — used as a script. Three are provided:

        inspect       certificate -> Lean-identifier mapping dump
        check-deps    list required JSON files (with [OK]/[MISSING]) and
                      emit ready-to-paste imports / opens / `load_*` commands
        gen-skeleton  write a complete starter Lean file (imports + opens +
                      namespace + load_* + M_t/dM_t/LM_t with PSD lemmas +
                      σ_t/v_t + TODO stub for the main theorem)
        gen-matrices  append only the M_t / dM_t / LM_t defs and PSD lemmas
        gen-vectors   append only σ_t and v_t definitions

Future subcommands (gen-matrices, gen-theorem, ...) will reuse layer (1).

----------------------------------------------------------------------
USAGE EXAMPLES (PowerShell; use `\\` on bash):

  # 1. Quick sanity check on a new certificate — does every flagmatic
  #    string resolve to a canonical Lean identifier?
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py inspect `
      LeanFlagAlgebras/Flagmatic/mantel_sparse_cert.json

  # 2. Find out which JSON files this certificate needs and whether
  #    they exist on disk. Exit code is 0 if all present, 1 otherwise.
  #    Also prints the exact `load_*` commands to paste into Lean.
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py check-deps `
      LeanFlagAlgebras/Flagmatic/c4turan_sparse_cert.json

  # 3. Generate a complete starter Lean file: imports, opens, namespace,
  #    load_* commands, σ_t / v_t definitions, and TODO stubs for the
  #    matrix definitions and the main theorem body.
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton `
      LeanFlagAlgebras/Flagmatic/mantel_sparse_cert.json `
      LeanFlagAlgebras/API/MyNewProof.lean

  # 4. Or, if you already have a Lean file and only want to append σ/v
  #    definitions to it:
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-vectors `
      LeanFlagAlgebras/Flagmatic/mantel_sparse_cert.json `
      LeanFlagAlgebras/API/MyNewProof.lean

Typical workflow for a fresh certificate:
  inspect  ->  check-deps  ->  (add missing JSONs if any)  ->  gen-skeleton
   ->  fill in the M / dM / LM definitions and the main theorem body.

For per-command help: `python flagmatic_to_lean.py <subcommand> --help`.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from fractions import Fraction
from itertools import permutations
from pathlib import Path
from typing import Iterable

# Make stdout UTF-8 capable on Windows so σ / subscripts render correctly.
if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

REPO_ROOT = Path(__file__).resolve().parents[2]
GRAPHS_DIR = REPO_ROOT / "LeanFlagAlgebras" / "Flags" / "Graphs"
FLAGS_DIR = REPO_ROOT / "LeanFlagAlgebras" / "Flags" / "Flags"
DENSITIES_DIR = REPO_ROOT / "LeanFlagAlgebras" / "Flags" / "Densities"
CERT_DIR = REPO_ROOT / "LeanFlagAlgebras" / "Flagmatic"


def _rel(p: Path) -> str:
    """Path relative to the repo root, as a forward-slash string."""
    try:
        return p.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return p.as_posix()


# =========================================================================== #
# (1) Library — parsing / isomorphism / identifier mapping
# =========================================================================== #


# --------------------------------------------------------------------------- #
# Parsing
# --------------------------------------------------------------------------- #

_FLAGMATIC_RE = re.compile(r"^\s*(\d+)\s*:\s*([0-9]*)\s*(?:\(([0-9]+)\))?\s*$")


def parse_flagmatic(s: str) -> tuple[int, frozenset[tuple[int, int]], tuple[int, ...] | None]:
    """Parse "N:edges" or "N:edges(k)".

    Returns (n, edges_zero_indexed_frozenset, label_positions_or_None).
    label_positions[j] is the 0-indexed vertex carrying label j.
    """
    m = _FLAGMATIC_RE.match(s)
    if not m:
        raise ValueError(f"not a flagmatic string: {s!r}")
    n = int(m.group(1))
    edge_digits = m.group(2) or ""
    labels = m.group(3)

    if len(edge_digits) % 2 != 0:
        raise ValueError(f"odd-length edge field in {s!r}")
    edges = []
    for i in range(0, len(edge_digits), 2):
        u = int(edge_digits[i]) - 1
        v = int(edge_digits[i + 1]) - 1
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError(f"bad edge {edge_digits[i:i+2]} in {s!r} (n={n})")
        a, b = sorted((u, v))
        edges.append((a, b))
    edge_set = frozenset(edges)
    if len(edge_set) != len(edges):
        raise ValueError(f"duplicate edge in {s!r}")

    label_positions: tuple[int, ...] | None = None
    if labels is not None:
        # Flagmatic convention: parenthesized integer is the type size k;
        # the first k vertices (positions 1..k) are the labeled type vertices
        # in order (label j = position j+1).
        type_size = int(labels)
        if not (0 <= type_size <= n):
            raise ValueError(f"bad type size {type_size} in {s!r}")
        label_positions = tuple(range(type_size))

    return n, edge_set, label_positions


# --------------------------------------------------------------------------- #
# Loading the canonical Lean JSON
# --------------------------------------------------------------------------- #


def _edges_to_set(edges: Iterable[Iterable[int]]) -> frozenset[tuple[int, int]]:
    return frozenset(tuple(sorted(e)) for e in edges)


def load_graphs(n: int) -> list[frozenset[tuple[int, int]]]:
    path = GRAPHS_DIR / f"graphs_{n}.json"
    with path.open() as f:
        data = json.load(f)
    return [_edges_to_set(g) for g in data]


def load_flags(m: int, k: int, type_num: int) -> dict:
    path = FLAGS_DIR / f"flags_{m}_{k}_{type_num}.json"
    with path.open() as f:
        return json.load(f)


# --------------------------------------------------------------------------- #
# Isomorphism helpers (brute force; n is small)
# --------------------------------------------------------------------------- #


def _relabel(edges: frozenset[tuple[int, int]], perm: tuple[int, ...]) -> frozenset[tuple[int, int]]:
    """Send vertex `i` to `perm[i]`."""
    return frozenset(tuple(sorted((perm[u], perm[v]))) for (u, v) in edges)


def find_unlabeled_index(n: int, edges: frozenset[tuple[int, int]]) -> int:
    """Return the index `i` such that `graphs_n.json[i]` is isomorphic to (n, edges)."""
    candidates = load_graphs(n)
    for i, g in enumerate(candidates):
        if len(g) != len(edges):
            continue
        for perm in permutations(range(n)):
            if _relabel(edges, perm) == g:
                return i
    raise LookupError(f"no graph in graphs_{n}.json isomorphic to edges={sorted(edges)}")


def find_sigma_flag_index(
    m: int,
    edges: frozenset[tuple[int, int]],
    label_positions: tuple[int, ...],
    k: int,
    type_num: int,
) -> int:
    """Look up a sigma-flag in flags_<m>_<k>_<type_num>.json.

    `label_positions[j]` is the 0-indexed input vertex carrying label j.
    Returns the index in the file's `flags` list.
    """
    data = load_flags(m, k, type_num)
    assert data["n"] == m and data["k"] == k and data["type_num"] == type_num
    underlying_idx = find_unlabeled_index(m, edges)

    for flag_idx, entry in enumerate(data["flags"]):
        if entry["underlying_graph_num"] != underlying_idx:
            continue
        stored_edges = _edges_to_set(entry["edges"])
        type_indices = entry["type_indices"]  # type_indices[j] = canonical vertex for label j

        # Need a permutation `perm` (input vertex -> canonical vertex) such that
        # _relabel(edges, perm) == stored_edges
        # AND perm[label_positions[j]] == type_indices[j] for every j.
        forced = {label_positions[j]: type_indices[j] for j in range(k)}
        if len(set(forced.values())) != len(forced):
            continue

        free_inputs = [v for v in range(m) if v not in forced]
        free_outputs = [v for v in range(m) if v not in forced.values()]
        for assignment in permutations(free_outputs):
            perm = [0] * m
            for src, dst in forced.items():
                perm[src] = dst
            for src, dst in zip(free_inputs, assignment):
                perm[src] = dst
            if _relabel(edges, tuple(perm)) == stored_edges:
                return flag_idx
    raise LookupError(
        f"no entry in flags_{m}_{k}_{type_num}.json matches edges={sorted(edges)} "
        f"with labels at positions {label_positions}"
    )


# --------------------------------------------------------------------------- #
# Public string-to-identifier API
# --------------------------------------------------------------------------- #


def graph_to_lean(s: str) -> tuple[str, int]:
    """`"N:edges"` (unlabeled) -> ("FlagAlgebra_N_0_0_<i>", i)."""
    n, edges, labels = parse_flagmatic(s)
    if labels is not None:
        raise ValueError(f"expected unlabeled graph, got labels: {s!r}")
    i = find_unlabeled_index(n, edges)
    return f"FlagAlgebra_{n}_0_0_{i}", i


def type_to_lean(s: str) -> tuple[str, int, int]:
    """`"k:edges"` -> ("FlagType_k_<i>", k, i)."""
    k, edges, labels = parse_flagmatic(s)
    if labels is not None:
        raise ValueError(f"expected a type (no labels parenthesis), got: {s!r}")
    i = find_unlabeled_index(k, edges)
    return f"FlagType_{k}_{i}", k, i


def sigma_flag_to_lean(s: str, type_str: str) -> tuple[str, int, int, int, int]:
    """`"m:edges(k)"` plus its type "k:..." -> ("FlagAlgebra_m_k_<typeIdx>_<flagIdx>", ...)."""
    m, edges, labels = parse_flagmatic(s)
    if labels is None:
        raise ValueError(f"expected a sigma-flag with (k), got: {s!r}")
    _, k, type_idx = type_to_lean(type_str)
    if len(labels) != k:
        raise ValueError(
            f"sigma-flag {s!r} has {len(labels)} labels but type {type_str!r} has size {k}"
        )
    flag_idx = find_sigma_flag_index(m, edges, labels, k, type_idx)
    return f"FlagAlgebra_{m}_{k}_{type_idx}_{flag_idx}", m, k, type_idx, flag_idx


# --------------------------------------------------------------------------- #
# Certificate inspection: which JSON files will be needed?
# --------------------------------------------------------------------------- #


def _guess_forbid_tag(n: int, edges_str: str) -> str | None:
    """Guess the Lean tag for a forbidden graph string (e.g. "K3"). None if unknown."""
    if len(edges_str) == n * (n - 1):
        return f"K{n}"
    return None


class Dep:
    """A required Lean JSON file with diagnostics for code generation.

    Attributes:
      path       : absolute Path expected on disk (or one candidate when alternates exist)
      purpose    : human-readable reason why this file is needed
      load_cmd   : the Lean `load_*` command that imports it (None for raw flag/graph defs)
      alternates : other paths that would also satisfy the requirement (e.g. with/without
                   `_forbid_<tag>` suffix). The resolved one is in `path`.
      present    : whether `path` (or any alternate) exists on disk
      resolved   : actual existing Path if found, else None
    """

    __slots__ = ("path", "purpose", "load_cmd", "alternates", "present", "resolved")

    def __init__(
        self,
        path: Path,
        purpose: str,
        load_cmd: str | None = None,
        alternates: list[Path] | None = None,
    ) -> None:
        self.path = path
        self.purpose = purpose
        self.load_cmd = load_cmd
        self.alternates = alternates or []
        # Resolve: prefer `path`, then any alternate that exists
        if path.exists():
            self.present = True
            self.resolved = path
        else:
            self.resolved = next((p for p in self.alternates if p.exists()), None)
            self.present = self.resolved is not None


def check_dependencies(cert: dict) -> list[Dep]:
    """Return the list of Lean JSON files this certificate needs, with presence info."""
    deps: list[Dep] = []
    N = int(cert["order_of_admissible_graphs"])

    # Forbid tag (from description) — needed to pin down the correct density loader / forbid index.
    desc = cert.get("description", "")
    m_forbid = re.search(r"forbid\s+(\d+):([0-9]*)", desc)
    forbid_tag: str | None = None
    if m_forbid:
        forbid_tag = _guess_forbid_tag(int(m_forbid.group(1)), m_forbid.group(2))

    # (a) host graphs file — for admissible graph identifiers
    deps.append(Dep(
        path=GRAPHS_DIR / f"graphs_{N}.json",
        purpose=f"admissible {N}-vertex graph definitions (used by FlagAlgebra_{N}_0_0_*)",
    ))

    # (b) forbid-free indices file — used by `load_forbid_density_theorems`
    if forbid_tag is not None:
        fpath = DENSITIES_DIR / f"graphs_{N}_{forbid_tag}_free_indices.json"
        deps.append(Dep(
            path=fpath,
            purpose=f"{forbid_tag}-free index list for {N}-vertex graphs",
            load_cmd=f'load_forbid_density_theorems "{_rel(fpath)}"',
        ))
    else:
        deps.append(Dep(
            path=DENSITIES_DIR / f"graphs_{N}_???_free_indices.json",
            purpose="forbid-free index list (could not detect forbid tag from description)",
            load_cmd=None,
        ))

    seen_type_dims: set[tuple[int, int]] = set()
    for t, type_str in enumerate(cert["types"]):
        k, _, _ = parse_flagmatic(type_str)
        first_flag = cert["flags"][t][0]
        m, _, _ = parse_flagmatic(first_flag)
        _, _, type_idx = type_to_lean(type_str)

        # (c) type-size graphs file — only if different from host
        if (k, 0) not in seen_type_dims and k != N:
            deps.append(Dep(
                path=GRAPHS_DIR / f"graphs_{k}.json",
                purpose=f"underlying graphs for block {t + 1} type σ = {type_str!r}",
            ))
            seen_type_dims.add((k, 0))

        # (d) sigma-flags file
        deps.append(Dep(
            path=FLAGS_DIR / f"flags_{m}_{k}_{type_idx}.json",
            purpose=(
                f"σ-flag vector v{_subscript(t + 1) if len(cert['types']) > 1 else ''}"
                f" (block {t + 1}): {m}-vertex flags over type {type_str!r}"
            ),
        ))

        # (e) density loader — try `_forbid_<tag>` and plain variants
        base = f"density_{N}_{k}_{type_idx}_from_{m}_{k}_{type_idx}"
        candidates = [DENSITIES_DIR / f"{base}_forbid_{forbid_tag}.json"] if forbid_tag else []
        candidates.append(DENSITIES_DIR / f"{base}.json")
        primary = candidates[0]
        alternates = candidates[1:]
        deps.append(Dep(
            path=primary,
            purpose=f"density coefficients connecting host {N}-vertex flags to block {t + 1}'s {m}-vertex σ-flags",
            load_cmd=(
                f'load_flag_pair_density_theorems "{_rel(primary)}"'
                + "\n"
                + f'load_forbid_mul_theorems "{_rel(primary)}"'
            ),
            alternates=alternates,
        ))

    return deps


def required_json_files(cert: dict) -> dict[str, list[str]]:
    """Backward-compatible wrapper: bucketed file-name list (no presence info).

    Prefer `check_dependencies` for new code — it returns presence info and the
    Lean `load_*` commands.
    """
    out: dict[str, list[str]] = {"graphs": [], "flags": [], "forbid_indices": [], "density_loaders": []}
    for d in check_dependencies(cert):
        name = d.path.name
        if name.startswith("graphs_") and "_free_indices" in name:
            out["forbid_indices"].append(name)
        elif name.startswith("graphs_"):
            out["graphs"].append(name)
        elif name.startswith("flags_"):
            out["flags"].append(name)
        elif name.startswith("density_"):
            out["density_loaders"].append(name)
    return out


# =========================================================================== #
# (2) Code generators — render Lean fragments
# =========================================================================== #


SUBSCRIPT_DIGITS = "₀₁₂₃₄₅₆₇₈₉"


def _subscript(n: int) -> str:
    return "".join(SUBSCRIPT_DIGITS[int(c)] for c in str(n))


# --------------------------------------------------------------------------- #
# Matrix assembly: M_t = R_t · Q'_t · R_tᵀ  +  exact LDLᵀ decomposition
# --------------------------------------------------------------------------- #


def _parse_rat(s: object) -> Fraction:
    """Accept int, "n", or "n/d" → Fraction."""
    if isinstance(s, int):
        return Fraction(s)
    if isinstance(s, str):
        if "/" in s:
            num_s, den_s = s.split("/", 1)
            return Fraction(int(num_s), int(den_s))
        return Fraction(int(s))
    raise TypeError(f"unexpected rational format: {s!r}")


def _parse_qdash(qdash: list) -> list[list[Fraction]]:
    """Flagmatic stores Q'_t as upper-triangular row-by-row: row i contains
    [Q[i,i], Q[i,i+1], ..., Q[i,n-1]]. Returns the full symmetric matrix."""
    n = len(qdash)
    Q = [[Fraction(0)] * n for _ in range(n)]
    for i, row in enumerate(qdash):
        if len(row) != n - i:
            raise ValueError(
                f"qdash row {i}: expected {n - i} entries (upper-tri), got {len(row)}"
            )
        for off, val in enumerate(row):
            j = i + off
            v = _parse_rat(val)
            Q[i][j] = v
            Q[j][i] = v
    return Q


def _matmul(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    rows, mid = len(A), len(A[0])
    if len(B) != mid:
        raise ValueError(f"matmul dim mismatch: {rows}x{mid} times {len(B)}x{len(B[0])}")
    cols = len(B[0])
    return [
        [sum((A[i][k] * B[k][j] for k in range(mid)), Fraction(0)) for j in range(cols)]
        for i in range(rows)
    ]


def _transpose(M: list[list[Fraction]]) -> list[list[Fraction]]:
    return [list(row) for row in zip(*M)]


def assemble_block_matrix(qdash: list, r: list) -> list[list[Fraction]]:
    """Compute M_t = R · Q' · Rᵀ from a certificate block's qdash and r data."""
    Q = _parse_qdash(qdash)
    R = [[_parse_rat(x) for x in row] for row in r]
    return _matmul(_matmul(R, Q), _transpose(R))


def ldl_decomposition(
    M: list[list[Fraction]],
) -> tuple[list[list[Fraction]], list[Fraction]]:
    """Exact rational LDLᵀ of a symmetric PSD matrix. Returns (L, D) with L
    unit lower triangular. Raises ValueError if M is not symmetric PSD."""
    n = len(M)
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    for i in range(n):
        L[i][i] = Fraction(1)
        D[i] = M[i][i] - sum((L[i][k] * L[i][k] * D[k] for k in range(i)), Fraction(0))
        if D[i] < 0:
            raise ValueError(f"LDL: D[{i}] = {D[i]} < 0, matrix is not PSD")
        for j in range(i + 1, n):
            num = M[j][i] - sum(
                (L[j][k] * L[i][k] * D[k] for k in range(i)), Fraction(0)
            )
            if D[i] == 0:
                if num != 0:
                    raise ValueError(
                        f"LDL: D[{i}] = 0 but residual M[{j},{i}] = {num} ≠ 0, "
                        f"matrix is not PSD"
                    )
                L[j][i] = Fraction(0)
            else:
                L[j][i] = num / D[i]
    return L, D


def _lean_rat(q: Fraction) -> str:
    """Format a Fraction as a Lean ℚ literal matching the project's style."""
    if q == 0:
        return "0"
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} / {q.denominator} : ℚ)"


def _lean_matrix_lit(M: list[list[Fraction]], indent: str = "    ") -> str:
    """Format a rational matrix as `!![...; ...]` on multiple lines."""
    body = (";\n" + indent).join(
        ", ".join(_lean_rat(x) for x in row) for row in M
    )
    return "!![" + body + "]"


def _lean_vector_lit(v: list[Fraction]) -> str:
    return "![" + ", ".join(_lean_rat(x) for x in v) + "]"


def render_matrices(cert: dict) -> str:
    """Render M_t / dM_t / LM_t and the PSD lemma cluster for every SDP block.

    The output matches the structure used in `LeanFlagAlgebras/API/{Mantel,
    C4Turan}API.lean`: rational matrix, real cast, LDLᵀ data, then six lemmas
    (dM_nonneg / M_eq_LDL / M_posSemidef and their real counterparts).
    """
    total = len(cert["types"])
    blocks: list[str] = []
    for t in range(total):
        try:
            M = assemble_block_matrix(cert["qdash_matrices"][t], cert["r_matrices"][t])
            L, D = ldl_decomposition(M)
        except ValueError as e:
            raise ValueError(f"block {t + 1}: {e}") from e
        n = len(M)
        suffix = "" if total == 1 else _subscript(t + 1)
        M_name = f"M{suffix}"
        dM_name = f"dM{suffix}"
        LM_name = f"LM{suffix}"
        M_real = f"{M_name}_real"
        M_lit = _lean_matrix_lit(M)
        L_lit = _lean_matrix_lit(L)
        D_lit = _lean_vector_lit(D)
        blocks.append(
            f"""/-- SDP certificate matrix for block {t + 1} (rational, {n}×{n}),
paired with `v{suffix}`. Assembled as R·Q'·Rᵀ from the flagmatic certificate. -/
def {M_name} : Matrix (Fin {n}) (Fin {n}) ℚ :=
  {M_lit}
noncomputable def {M_real} : Matrix (Fin {n}) (Fin {n}) ℝ :=
  ratMatrixToReal {M_name}
def {dM_name} : Fin {n} → ℚ :=
  {D_lit}
def {LM_name} : Matrix (Fin {n}) (Fin {n}) ℚ :=
  {L_lit}
lemma {dM_name}_nonneg (i : Fin {n}) : 0 ≤ {dM_name} i := by
  fin_cases i <;> norm_num [{dM_name}]
lemma {M_name}_eq_LDL : {M_name} = {LM_name} * Matrix.diagonal {dM_name} * {LM_name}ᵀ := by
  decide +kernel
theorem {M_name}_posSemidef : {M_name}.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose {dM_name}_nonneg {M_name}_eq_LDL
lemma {dM_name}_real_nonneg (i : Fin {n}) : 0 ≤ ({dM_name} i : ℝ) := by
  exact_mod_cast {dM_name}_nonneg i
lemma {M_real}_eq_LDL :
    {M_real} = (ratMatrixToReal {LM_name} * Matrix.diagonal (fun i => ({dM_name} i : ℝ))) * (ratMatrixToReal {LM_name})ᵀ := by
  calc
    {M_real} = ratMatrixToReal ({LM_name} * Matrix.diagonal {dM_name} * {LM_name}ᵀ) := by
      simp [{M_real}, ratMatrixToReal, {M_name}_eq_LDL]
    _ = (ratMatrixToReal {LM_name} * Matrix.diagonal (fun i => ({dM_name} i : ℝ))) * (ratMatrixToReal {LM_name})ᵀ := by
      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]
/-- `{M_real}` is positive semidefinite (via its real LDLᵀ factorization). -/
theorem {M_real}_posSemidef : {M_real}.PosSemidef := by
  exact posSemidef_of_eq_mul_diagonal_mul_transpose_real {dM_name}_real_nonneg {M_real}_eq_LDL
"""
        )
    return "\n".join(blocks)


# --------------------------------------------------------------------------- #
# Main theorem statement (objective ≤[forbid] bound · 1)
# --------------------------------------------------------------------------- #


_DESC_OBJ_RE = re.compile(r"maximize\s+(\S+)\s+density", re.IGNORECASE)
_DESC_FORBID_RE = re.compile(r"forbid\s+(\S+)", re.IGNORECASE)


def _lean_real_literal(s) -> str:
    """Format a rational number (int or "n/d" string) as a Lean ℝ literal."""
    q = _parse_rat(s)
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"


def _objective_from_description(desc: str) -> tuple[str, int]:
    """Return (Lean identifier, host-size n) for the objective flag.

    Reads the `maximize <flagmatic> density` part of the description. The
    flagmatic string is unlabeled (no parenthesized type size).
    """
    m = _DESC_OBJ_RE.search(desc)
    if not m:
        raise ValueError(f"could not parse `maximize ... density` from description: {desc!r}")
    flagmatic_str = m.group(1)
    ident, _idx = graph_to_lean(flagmatic_str)
    n, _, _ = parse_flagmatic(flagmatic_str)
    return ident, n


def _forbid_expr_from_description(desc: str) -> tuple[str | None, str | None]:
    """Return (Lean forbid expression, tag) parsed from description.

    e.g. "forbid 3:121323" → ("K3.toFinFlag", "K3"). For non-complete graphs
    returns (None, None) so the caller can emit a TODO placeholder.
    """
    m = _DESC_FORBID_RE.search(desc)
    if not m:
        return None, None
    n, edges, _ = parse_flagmatic(m.group(1))
    tag = _guess_forbid_tag(n, m.group(1).split(":", 1)[1])
    if tag is None:
        return None, None
    return f"{tag}.toFinFlag", tag


def render_theorem_statement(cert: dict, theorem_name: str) -> str:
    """Render the main `theorem` declaration with `sorry` for the proof body.

    Falls back to placeholders (`/- TODO: ... -/`) when description parsing
    is incomplete; never raises so a partial skeleton can still be generated.
    """
    desc = cert.get("description", "")
    try:
        objective_ident, _n_obj = _objective_from_description(desc)
        obj_repr = objective_ident
    except (ValueError, LookupError) as e:
        obj_repr = f"/- TODO: objective flag (parsing failed: {e}) -/"

    forbid_expr, _tag = _forbid_expr_from_description(desc)
    if forbid_expr is None:
        forbid_expr = "/- TODO: forbid expression (no K_n match in description) -/"

    bound = cert.get("bound", "0")
    try:
        bound_lit = _lean_real_literal(bound)
    except (TypeError, ValueError):
        bound_lit = f"/- TODO: bound `{bound!r}` -/ (0 : ℝ)"

    return (
        f"/-- **Main theorem (auto-generated statement, proof body TODO).**\n"
        f"Certificate description: {desc!r}\n"
        f"Bound: {bound!r}. -/\n"
        f"theorem {theorem_name}\n"
        f"    : {obj_repr} ≤[{forbid_expr}] {bound_lit} • (1 : FlagAlgebra ∅ₜ)\n"
        f"  := by\n"
        f"  sorry\n"
    )


def render_flag_vectors(cert: dict) -> str:
    """Render σ_t and v_t Lean definitions for every SDP block in the certificate."""
    types = cert["types"]
    flags = cert["flags"]
    assert len(types) == len(flags), "types and flags must have the same length"

    blocks: list[str] = []
    for t, (type_str, flag_list) in enumerate(zip(types, flags)):
        sigma_ident, k, _type_idx = type_to_lean(type_str)
        flag_idents = [sigma_flag_to_lean(fs, type_str)[0] for fs in flag_list]
        n_flags = len(flag_idents)
        m, _, _ = parse_flagmatic(flag_list[0])
        suffix = "" if len(types) == 1 else _subscript(t + 1)
        sigma_name = f"σ{suffix}"
        v_name = f"v{suffix}"
        joined = ",\n  ".join(flag_idents)
        blocks.append(
            f"/-- Label type for block {t + 1}"
            f" (flagmatic type {type_str!r}). -/\n"
            f"def {sigma_name} : FlagType (Fin {k}) := {sigma_ident}\n"
            f"/-- Flag vector for block {t + 1}:"
            f" the {n_flags} σ-type {m}-vertex flags paired with M{suffix}. -/\n"
            f"noncomputable def {v_name} : FlagAlgebraVec {sigma_name} {n_flags} := ![\n"
            f"  {joined}\n"
            f"]\n"
        )

    header = (
        f"-- Auto-generated from Flagmatic certificate "
        f"(description: {cert.get('description', '')!r}).\n"
        f"-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py\n"
    )
    return header + "\n".join(blocks)


# =========================================================================== #
# (3) CLI — subcommands
# =========================================================================== #


LEAN_OPENS: list[str] = [
    "open FlagAlgebras Forbid FlagAlgebras.API",
    "open SimpleGraph Matrix",
]


def required_lean_load_commands(cert: dict) -> list[str]:
    """Return the in-namespace `load_*` lines for this certificate's dependencies.

    Uses the same resolution logic as `check_dependencies`: when a `_forbid_<tag>`
    variant of a density file exists on disk, it is preferred over the plain
    variant; otherwise we fall back to the plain path.
    """
    out: list[str] = []
    seen: set[str] = set()
    for d in check_dependencies(cert):
        if not d.load_cmd:
            continue
        cmd = d.load_cmd
        if d.resolved is not None and d.resolved != d.path:
            cmd = cmd.replace(_rel(d.path), _rel(d.resolved))
        if cmd in seen:
            continue
        seen.add(cmd)
        out.extend(cmd.splitlines())
    return out


def required_lean_imports(cert: dict) -> list[str]:
    """Return the Lean `import` lines this certificate's API file needs.

    A baseline set is always emitted (API.Basic + matrix/PSD utilities + the two
    density loaders that `check-deps` recommends). If a forbid tag was detected
    from the certificate description we also include `Forbid.CommonGraphs`,
    which is where `K3.toFinFlag`, `K4.toFinFlag`, ... are defined.
    """
    imports = [
        "import LeanFlagAlgebras.Flags.FlagDef",
        "import LeanFlagAlgebras.API.Basic",
        "import LeanFlagAlgebras.API.ReduceFlagMul",
        "import LeanFlagAlgebras.Flags.Densities.MulLoader",
        "import LeanFlagAlgebras.Flags.Densities.DensityLoader",
        "import LeanFlagAlgebras.Utils.SortTactic",
        "import LeanFlagAlgebras.Utils.Matrix.PosSemiDef",
    ]
    desc = cert.get("description", "")
    if re.search(r"forbid\s+\d+:", desc):
        imports.append("import LeanFlagAlgebras.Forbid.CommonGraphs")
    return imports


def render_dependency_report(cert: dict) -> tuple[str, bool]:
    """Pretty-print the dependency check. Returns (text, all_present)."""
    deps = check_dependencies(cert)
    lines = [f"Dependency check for: {cert.get('description', '<no description>')}"]
    all_present = True
    for d in deps:
        mark = "OK     " if d.present else "MISSING"
        shown = _rel(d.resolved) if d.resolved is not None else _rel(d.path)
        lines.append(f"  [{mark}] {shown}")
        lines.append(f"          purpose: {d.purpose}")
        if not d.present and d.alternates:
            for alt in d.alternates:
                lines.append(f"          alt:     {_rel(alt)}")
        if not d.present:
            all_present = False

    lines.append("")
    lines.append("Lean imports (paste at the top of the API file):")
    for imp in required_lean_imports(cert):
        lines.append(f"  {imp}")
    lines.append(
        "  -- problem-specific helper lemmas (e.g. host-flag expansion under the"
    )
    lines.append(
        "  -- forbid relation) may need an extra `import LeanFlagAlgebras.<Problem>.Lemmas`."
    )

    lines.append("")
    lines.append("Lean opens (paste at the top of the API file, after imports):")
    for op in LEAN_OPENS:
        lines.append(f"  {op}")

    lines.append("")
    lines.append("Lean load commands (paste into the API file's namespace):")
    for cmd in required_lean_load_commands(cert):
        lines.append(f"  {cmd}")

    return "\n".join(lines), all_present


def render_skeleton(cert: dict, namespace: str, theorem_name: str = "main") -> str:
    """Render a complete starter Lean API file: imports, opens, namespace,
    load commands, and σ_t / v_t definitions. Matrix defs and the main theorem
    body are left as TODO stubs."""
    imports = "\n".join(required_lean_imports(cert))
    opens = "\n".join(LEAN_OPENS)
    loads = "\n".join(required_lean_load_commands(cert))
    matrices_body = render_matrices(cert)
    vectors_body = render_flag_vectors(cert)
    # render_flag_vectors prepends a 2-line auto-gen header; strip it so the
    # skeleton has a single top-level header instead.
    vectors_body = "\n".join(
        line for line in vectors_body.splitlines()
        if not line.startswith("-- Auto-generated") and not line.startswith("-- Generator:")
    ).lstrip("\n")

    header = (
        f"-- Auto-generated from Flagmatic certificate "
        f"(description: {cert.get('description', '')!r}).\n"
        f"-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-skeleton)\n"
        f"-- Matrix defs (M_t, dM_t, LM_t) and PSD proofs are filled in; the main\n"
        f"-- theorem body still needs to be written (see TODO at the bottom).\n"
    )

    theorem_block = (
        f"set_option maxHeartbeats 0\n"
        f"set_option maxRecDepth 1500\n"
        f"\n"
        f"{render_theorem_statement(cert, theorem_name)}"
    )

    return (
        f"{header}\n"
        f"{imports}\n"
        f"\n"
        f"{opens}\n"
        f"\n"
        f"namespace {namespace}\n"
        f"\n"
        f"{loads}\n"
        f"\n"
        f"{matrices_body}\n"
        f"{vectors_body}\n"
        f"\n"
        f"{theorem_block}"
        f"\n"
        f"end {namespace}\n"
    )


def _derive_theorem_name(cert_path: Path) -> str:
    """Suggest a theorem name from the certificate filename.

    Strips common flagmatic export suffixes (`_sparse_cert`, `_cert`, ...) and
    appends `_flagAlgebra` (e.g. `mantel_cert.json` -> `mantel_flagAlgebra`).
    """
    stem = cert_path.stem
    for suffix in ("_sparse_cert", "_dense_cert", "_cert", "_sdp_output", "_sdp"):
        if stem.endswith(suffix):
            stem = stem[: -len(suffix)]
            break
    if not stem:
        stem = "main"
    return f"{stem}_flagAlgebra"


def _cmd_gen_matrices(args: argparse.Namespace) -> None:
    with args.certificate.open() as f:
        cert = json.load(f)
    text = render_matrices(cert)
    header = (
        f"-- Auto-generated from Flagmatic certificate "
        f"(description: {cert.get('description', '')!r}).\n"
        f"-- Generator: LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py (gen-matrices)\n"
    )
    full = header + text

    if args.target.exists():
        existing = args.target.read_text(encoding="utf-8")
        sep = "" if existing.endswith("\n\n") else ("\n" if existing.endswith("\n") else "\n\n")
        with args.target.open("a", encoding="utf-8") as f:
            f.write(sep + full)
    else:
        args.target.parent.mkdir(parents=True, exist_ok=True)
        args.target.write_text(full, encoding="utf-8")

    print(f"wrote {len(full)} chars to {args.target} ({len(cert['types'])} block(s))")


def _cmd_gen_skeleton(args: argparse.Namespace) -> int:
    with args.certificate.open() as f:
        cert = json.load(f)
    namespace = args.namespace or args.target.stem
    if not namespace.isidentifier():
        print(
            f"error: derived namespace {namespace!r} is not a valid Lean identifier; "
            f"pass --namespace explicitly",
            file=sys.stderr,
        )
        return 2
    if args.target.exists() and not args.force:
        print(
            f"error: {args.target} already exists. Pass --force to overwrite, "
            f"or use `gen-vectors` to append σ/v defs to an existing file.",
            file=sys.stderr,
        )
        return 2
    theorem_name = args.theorem_name or _derive_theorem_name(args.certificate)
    text = render_skeleton(cert, namespace, theorem_name)
    args.target.parent.mkdir(parents=True, exist_ok=True)
    args.target.write_text(text, encoding="utf-8")
    print(f"wrote {len(text)} chars to {args.target} (namespace {namespace})")
    return 0


def _cmd_check_deps(args: argparse.Namespace) -> int:
    with args.certificate.open() as f:
        cert = json.load(f)
    text, ok = render_dependency_report(cert)
    print(text)
    return 0 if ok else 1


def _cmd_inspect(args: argparse.Namespace) -> None:
    with args.certificate.open() as f:
        cert = json.load(f)

    print(f"=== {args.certificate.name} ===")
    print(f"description: {cert['description']}")
    print(f"bound: {cert['bound']}")

    print("\nadmissible graphs (host-size):")
    for s, dens in zip(cert["admissible_graphs"], cert["admissible_graph_densities"]):
        ident, _ = graph_to_lean(s)
        print(f"  {s!r:>20}  ->  {ident:<22}  density={dens!r}")

    print("\ntypes:")
    for s in cert["types"]:
        ident, _, _ = type_to_lean(s)
        print(f"  {s!r:>10}  ->  {ident}")

    print("\nsigma-flags per type:")
    for t, (type_s, flag_list) in enumerate(zip(cert["types"], cert["flags"])):
        print(f"  type {t} ({type_s!r}):")
        for s in flag_list:
            ident, *_ = sigma_flag_to_lean(s, type_s)
            print(f"    {s!r:>20}  ->  {ident}")

    print("\nrequired JSON files:")
    for k, v in required_json_files(cert).items():
        print(f"  {k}: {v}")


def _cmd_gen_vectors(args: argparse.Namespace) -> None:
    with args.certificate.open() as f:
        cert = json.load(f)
    text = render_flag_vectors(cert)

    if args.target.exists():
        existing = args.target.read_text(encoding="utf-8")
        sep = "" if existing.endswith("\n\n") else ("\n" if existing.endswith("\n") else "\n\n")
        with args.target.open("a", encoding="utf-8") as f:
            f.write(sep + text)
    else:
        args.target.write_text(text, encoding="utf-8")

    print(f"wrote {len(text)} chars to {args.target} ({len(cert['types'])} block(s))")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(
        prog="flagmatic_to_lean",
        description="Convert Flagmatic certificates to Lean flag-algebra API code.",
        epilog=(
            "Examples:\n"
            "  python flagmatic_to_lean.py inspect       mantel_sparse_cert.json\n"
            "  python flagmatic_to_lean.py check-deps    c4turan_sparse_cert.json\n"
            "  python flagmatic_to_lean.py gen-skeleton  mantel_sparse_cert.json out.lean\n"
            "  python flagmatic_to_lean.py gen-matrices  mantel_sparse_cert.json out.lean\n"
            "  python flagmatic_to_lean.py gen-vectors   mantel_sparse_cert.json out.lean\n"
            "\nTypical workflow:  inspect  ->  check-deps  ->  gen-skeleton\n"
            "Per-command help:  flagmatic_to_lean.py <subcommand> --help\n"
            "Full reference:    see the module docstring at the top of this file."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_inspect = sub.add_parser("inspect", help="print certificate -> Lean identifier mapping")
    p_inspect.add_argument("certificate", type=Path)
    p_inspect.set_defaults(func=_cmd_inspect)

    p_gen = sub.add_parser("gen-vectors", help="append σ_t and v_t Lean definitions to a file")
    p_gen.add_argument("certificate", type=Path)
    p_gen.add_argument("target", type=Path, help="Lean file to append to (created if absent)")
    p_gen.set_defaults(func=_cmd_gen_vectors)

    p_chk = sub.add_parser(
        "check-deps",
        help="report which Lean JSON files this certificate needs, and whether they exist",
    )
    p_chk.add_argument("certificate", type=Path)
    p_chk.set_defaults(func=_cmd_check_deps)

    p_mat = sub.add_parser(
        "gen-matrices",
        help="append M_t / dM_t / LM_t Lean definitions and PSD lemmas to a file",
    )
    p_mat.add_argument("certificate", type=Path)
    p_mat.add_argument("target", type=Path, help="Lean file to append to (created if absent)")
    p_mat.set_defaults(func=_cmd_gen_matrices)

    p_skel = sub.add_parser(
        "gen-skeleton",
        help="write a complete starter Lean file (imports + opens + namespace + loads + σ/v + TODOs)",
    )
    p_skel.add_argument("certificate", type=Path)
    p_skel.add_argument("target", type=Path, help="Lean file to create")
    p_skel.add_argument(
        "--namespace",
        default=None,
        help="Lean namespace name (default: target file stem)",
    )
    p_skel.add_argument(
        "--theorem-name",
        dest="theorem_name",
        default=None,
        help=(
            "name of the main theorem. Default: derived from the certificate "
            "filename, e.g. `mantel_cert.json` -> `mantel_flagAlgebra`."
        ),
    )
    p_skel.add_argument("--force", action="store_true", help="overwrite the target if it exists")
    p_skel.set_defaults(func=_cmd_gen_skeleton)

    args = ap.parse_args(argv)
    rc = args.func(args)
    if isinstance(rc, int):
        raise SystemExit(rc)


if __name__ == "__main__":
    main()
