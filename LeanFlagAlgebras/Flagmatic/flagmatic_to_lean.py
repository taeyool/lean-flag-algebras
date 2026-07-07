# =============================================================================
# CURRENT (updated 2026-06-22) -- targets the edge-based, pruning-backed,
# JSON-free Lean pipeline. `gen-skeleton` emits proof files that compile as-is.
#
# What it generates (see `render_pruned_commands` / `render_skeleton`):
#   * the forbidden graph as a `Sym2Graph` term  `def K{r} := completeSym2Graph r`
#     (decision D2 -- no canonical forbidden flag, no `generate_complete_graph`);
#   * the edge-based pruned generation / density / multiplication commands
#       generate_pruned_forbid_free_empty_typed_flags <n> K{r}
#       generate_pruned_forbid_free_flags             <n> <k> <m> K{r}
#       generate_pruned_flag_pair_density_theorems    <patN> <hostN> <k> <m> K{r}
#       generate_pruned_forbid_free_mul_theorems      <patN> <hostN> <k> <m> K{r} (completeGraph (Fin r)) (completeSym2Graph_finFlag_mem_forbiddenFlags r)
#     (densities are computed inside Lean -- no `*.json`, no Python regeneration);
#   * M_t / dM_t / LM_t + the one-line `psd_real_ldlt` PSD proof, the σ_t / v_t flag vectors, the forbid-free
#     objective expansion (branch B, closed by `flag_expand_hfree`), and the
#     auto-proved main theorem (`≤[completeGraph (Fin r)]`, ordinary forbid).
#
# NO JSON ON DISK is required: the canonical graph/flag enumeration (which fixes
# the `FlagAlgebra_…` identifier indices, in lockstep with the Lean generators'
# order) is computed in-memory by `graph_enumeration.py` / `flag_enumeration.py`
# (this directory), imported below. Verified end-to-end: regenerating the four
# `Certificates/*_cert.json` reproduces the committed `Flagmatic/*.lean` (modulo
# cosmetics) and `lake build` accepts the generated proofs.
#
# Scope: any forbidden graph. A complete graph K_r takes Route A (`completeSym2Graph`,
# `generate_pruned_*`); any other graph takes Route B (an explicit edge set forbidden as a
# non-induced subgraph, `generate_subgraph_free_*`). Both are auto-generated end to end
# (see the K3/K4/K5 and C5 examples in this directory).
# `inspect` reports against those generation commands too: it dumps the
# cert -> Lean-identifier mapping (every flag string resolved via the in-memory
# enumeration) and prints the command block -- there are no JSON
# files to locate. (The old JSON-pipeline machinery -- `check_dependencies`, the
# `Dep` class, `required_json_files`, the CommonGraphs/FlagDef parsers -- has
# been removed; see git history if you need it.)
# =============================================================================

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

  (1) Library functions — parsing, isomorphism lookup, identifier mapping,
      matrix assembly, branch-A/B proof rendering:
        parse_flagmatic, graph_to_lean, type_to_lean, sigma_flag_to_lean,
        assemble_block_matrix, ldl_decomposition, induced_density,
        render_pruned_commands, render_matrices, render_flag_vectors,
        render_expand_under_forbid, render_proof_body,
        render_theorem_statement, render_skeleton

  (2) CLI subcommands — used as a script. Four are provided:

        inspect       certificate -> Lean-identifier mapping dump + the
                      `generate_pruned_*` command block it maps to (every
                      flagmatic string is resolved via the in-memory
                      enumeration, so this also validates the cert)
        gen-skeleton  write a complete starter Lean file: imports + opens +
                      namespace + `def K{r} := completeSym2Graph r` + the
                      `generate_pruned_*` commands + M_t/dM_t/LM_t with PSD
                      lemmas + σ_t/v_t + auto-proved main theorem (branch A) or
                      forbid-free expand lemma (`flag_expand_hfree`) + main
                      theorem (branch B). For an unsupported description
                      (non-complete-graph forbid, etc.) falls back to a
                      `sorry`-bodied stub.
        gen-matrices  append only the M_t / dM_t / LM_t defs and PSD theorem
        gen-vectors   append only σ_t and v_t definitions

----------------------------------------------------------------------
USAGE EXAMPLES (PowerShell; use `\\` on bash):

  # 1. Quick sanity check on a new certificate — does every flagmatic
  #    string resolve to a canonical Lean identifier, and what commands will
  #    gen-skeleton emit? (`inspect` resolves every string, so it also
  #    validates the cert; it raises on the first string that fails to resolve.)
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py inspect `
      LeanFlagAlgebras/Flagmatic/Certificates/mantel_cert.json

  # 2. Generate a complete starter Lean file with auto-proved main theorem.
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton `
      LeanFlagAlgebras/Flagmatic/Certificates/mantel_cert.json `
      LeanFlagAlgebras/Flagmatic/Mantel.lean --namespace Mantel --force

  # 3. Or, append-mode helpers when you have an existing file:
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-matrices `
      <cert>.json <target>.lean
  python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-vectors `
      <cert>.json <target>.lean

Typical workflow for a fresh certificate:
  inspect  ->  gen-skeleton
   ->  lake build LeanFlagAlgebras.Flagmatic.<Name>

For per-command help: `python flagmatic_to_lean.py <subcommand> --help`.

----------------------------------------------------------------------
VERIFIED SCENARIOS (see Certificates/ for inputs, *.lean for outputs):

  cert                 forbid  N  n_obj  branch  blocks  bound
  -------------------  ------  -  -----  ------  ------  -----
  mantel_cert          K3      3    2      B        1     1/2
  K3forbidC4_cert      K3      4    4      A        2     3/8
  K4turan_cert         K4      4    2      B        2     2/3
  ErdosPentagon_cert   K3      5    5      A        3   24/625

What's covered:
  * Branch A (n_obj == N) and Branch B (n_obj < N)
  * K_n forbid auto-recognition (K3, K4 currently defined in CommonGraphs)
  * Block counts 1, 2, 3
  * Host sizes N = 3, 4, 5
  * Both smul and bare-mul shapes in `reduce_downward_flagmul`

What's NOT yet exercised (but should work):
  * Non-K_n forbid (P_n, C_n, K_{a,b}, ...). The code is general — just
    add `def X : SimpleGraph (Fin n) := ...` + `X_toFinFlag_eq` to
    `Forbid/CommonGraphs.lean` and the parser picks it up via iso lookup.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from fractions import Fraction
from itertools import combinations, permutations
from math import comb
from pathlib import Path
from typing import Iterable

# Make stdout UTF-8 capable on Windows so σ / subscripts render correctly.
if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

# The canonical graph/flag enumeration lives alongside this script (in
# `Flagmatic/`). Import it in-memory so identifier lookups need no JSON on disk:
# `canonical_graphs` / `canonical_flags` reproduce exactly the order the Lean
# generators (`genSym2Graphs` / `genFlagData`) use, so the indices we compute
# match the generated `FlagAlgebra_…` constants. (Running this file as a script
# already puts its own directory on `sys.path`; the insert keeps imports working
# when this module is imported from elsewhere.)
sys.path.insert(0, str(Path(__file__).resolve().parent))
import graph_enumeration as _graph_enum  # noqa: E402
import flag_enumeration as _flag_enum  # noqa: E402


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
    """Canonical ``n``-vertex graphs as edge sets, computed in-memory (no JSON).

    Order matches ``graphs_<n>.json`` / the Lean ``genSym2Graphs`` enumeration,
    so list position is the canonical graph index used in identifier names.
    """
    return [_edges_to_set(g) for g in _graph_enum.canonical_graphs(n)]


def load_flags(m: int, k: int, type_num: int) -> dict:
    """Flag data for type ``graphs_k[type_num]`` over ``m`` vertices, in-memory
    (no JSON). Same dict shape as the old ``flags_<m>_<k>_<type_num>.json``
    (keys ``n``, ``k``, ``type_num``, ``type_edges``, ``flags``)."""
    return _flag_enum.canonical_flags(m, k, type_num)


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
    raise LookupError(
        f"no graph in graphs_{n}.json isomorphic to edges={sorted(edges)}")


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
        # type_indices[j] = canonical vertex for label j
        type_indices = entry["type_indices"]

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
        raise ValueError(
            f"expected a type (no labels parenthesis), got: {s!r}")
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
# Forbid-graph recognition (complete-graph K_n detection)
# --------------------------------------------------------------------------- #


def _parse_forbid_edges(n: int, edges_str: str) -> frozenset[tuple[int, int]] | None:
    """Parse flagmatic 2-digit edge digits to a 0-indexed edge set, or None if malformed."""
    if len(edges_str) % 2 != 0:
        return None
    edges: list[tuple[int, int]] = []
    for i in range(0, len(edges_str), 2):
        u, v = int(edges_str[i]) - 1, int(edges_str[i + 1]) - 1
        if u == v or not (0 <= u < n and 0 <= v < n):
            return None
        edges.append(tuple(sorted((u, v))))
    return frozenset(edges)


def _predict_forbid_tag(n: int, edges_str: str) -> str | None:
    """The tag we WILL use for filenames even if the forbid graph is not yet
    defined in `CommonGraphs.lean`.

    Complete graphs get the canonical `K{n}` tag — that is exactly what
    `generate_complete_graph` produces on the Lean side and what
    `gen_free_indices.py --forbid-Kn n` / `calculate_densities.py` default to, so
    we can name the data files concretely before anything is defined. For
    non-complete graphs the user must pick a tag, so we return None and callers
    fall back to a `???` placeholder.
    """
    edges = _parse_forbid_edges(n, edges_str)
    if edges is None:
        return None
    if edges == frozenset(combinations(range(n), 2)):
        return f"K{n}"
    return None


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
        raise ValueError(
            f"matmul dim mismatch: {rows}x{mid} times {len(B)}x{len(B[0])}")
    cols = len(B[0])
    return [
        [sum((A[i][k] * B[k][j] for k in range(mid)), Fraction(0))
         for j in range(cols)]
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
        D[i] = M[i][i] - sum((L[i][k] * L[i][k] * D[k]
                             for k in range(i)), Fraction(0))
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
    """Render M_t / M_t_real / dM_t / LM_t and the PSD theorem for every SDP block.

    Only the data (rational matrix, real cast, and the LDLᵀ factors `dM`/`LM`) is
    emitted; the entire PSD proof collapses to a single `psd_real_ldlt` tactic call
    (from `Automation/Matrix/PosSemiDef.lean`), which discharges the diagonal-nonnegativity
    and `M = LM·diag(dM)·LMᵀ` side goals internally. The intermediate lemmas the old
    template spelled out (dM_nonneg / M_eq_LDL / rational M_posSemidef / dM_real_nonneg
    / M_real_eq_LDL) are no longer needed — nothing downstream consumes them; the proof
    only uses `M_t_real` and `M_t_real_posSemidef`.
    """
    total = len(cert["types"])
    blocks: list[str] = []
    for t in range(total):
        try:
            M = assemble_block_matrix(
                cert["qdash_matrices"][t], cert["r_matrices"][t])
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
/-- `{M_real}` is positive semidefinite (via its rational LDLᵀ factorization). -/
theorem {M_real}_posSemidef : {M_real}.PosSemidef := by
  psd_real_ldlt {M_name} {LM_name} {dM_name}
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
        raise ValueError(
            f"could not parse `maximize ... density` from description: {desc!r}")
    flagmatic_str = m.group(1)
    ident, _idx = graph_to_lean(flagmatic_str)
    n, _, _ = parse_flagmatic(flagmatic_str)
    return ident, n


def _forbid_finflag_expr(tag: str) -> str:
    """The edge-based forbid as a `FinFlag ∅ₜ`, e.g.
    `(⟨_, Sym2EmptyTypedFlag.toFlag ⟦K3⟧⟩ : FinFlag ∅ₜ)`. This is the form the
    migrated pruned pipeline uses in `≤[…]` / `=[…]` and in the proof tactics —
    no canonical forbidden flag, no `.toFinFlag`."""
    return f"(⟨_, Sym2EmptyTypedFlag.toFlag ⟦{tag}⟧⟩ : FinFlag ∅ₜ)"


def _forbid_graph_from_description(desc: str):
    """Parse the ``forbid n:edges`` clause.

    Returns ``(n, edges_frozenset, tag)``: ``tag = "K{n}"`` for a **complete-graph** forbid
    (defined on the Lean side as ``completeSym2Graph n``, induced pipeline), or ``tag = None`` for a
    **non-complete** forbid (still returning ``n``/``edges`` — handled by the *subgraph* pipeline,
    Route B). Returns ``(None, None, None)`` only when the ``forbid …`` clause cannot be parsed.
    """
    m = _DESC_FORBID_RE.search(desc)
    if not m:
        return None, None, None
    n, edges, _ = parse_flagmatic(m.group(1))
    tag = _predict_forbid_tag(n, m.group(1).split(":", 1)[1])  # "K{n}" iff complete; else None
    return n, edges, tag


# --------------------------------------------------------------------------- #
# Branch-B helpers: induced density + `expand_under_forbid` lemma rendering
# --------------------------------------------------------------------------- #


def induced_density(
    obj_n: int,
    obj_edges: frozenset[tuple[int, int]],
    host_n: int,
    host_edges: frozenset[tuple[int, int]],
) -> Fraction:
    """Induced density d(obj; host): the fraction of `obj_n`-vertex subsets of
    `host` whose induced subgraph is isomorphic to `obj`.

    Counts vertex subsets S ⊆ [host_n] of size obj_n with host[S] ≅ obj, then
    divides by C(host_n, obj_n). All graphs are 0-indexed unlabeled simple."""
    if obj_n > host_n:
        return Fraction(0)
    total = comb(host_n, obj_n)
    if total == 0:
        return Fraction(0)
    count = 0
    for S in combinations(range(host_n), obj_n):
        idx = {v: i for i, v in enumerate(S)}
        induced = frozenset(
            tuple(sorted((idx[u], idx[v])))
            for (u, v) in host_edges
            if u in idx and v in idx
        )
        # Brute-force iso check (obj_n is small — typically ≤ 5).
        for perm in permutations(range(obj_n)):
            if _relabel(obj_edges, perm) == induced:
                count += 1
                break
    return Fraction(count, total)


def subgraph_contains(
    sub_n: int,
    sub_edges: frozenset[tuple[int, int]],
    host_n: int,
    host_edges: frozenset[tuple[int, int]],
) -> bool:
    """Does `host` contain `sub` as a *(not necessarily induced)* subgraph? I.e. is there an
    injection of `sub`'s vertices into `host`'s that maps every `sub`-edge to a `host`-edge (extra
    host edges among the image are allowed). This is the Lean `subgraphContains` predicate, and the
    correct free/forbidden split for **subgraph** forbidding. For a *complete* `sub = K_r` it agrees
    with `induced_density(K_r; host) ≠ 0` (a `K_r` subgraph is automatically induced), so using it
    everywhere keeps the existing complete-graph examples unchanged."""
    if sub_n > host_n:
        return False
    for verts in permutations(range(host_n), sub_n):
        if all(tuple(sorted((verts[u], verts[v]))) in host_edges for (u, v) in sub_edges):
            return True
    return False


def _expansion_coefficients(
    obj_flagmatic: str, N: int, forbid_n: int, forbid_edges: frozenset[tuple[int, int]]
) -> tuple[list[tuple[int, Fraction]], list[tuple[int, Fraction]]]:
    """Compute the expansion of `obj` over all N-vertex graphs, split by forbid.

    Returns `(admissible_terms, forbidden_terms)`, each a list of
    `(host_index_in_graphs_N, density)` pairs with density != 0 only, sorted by
    host index ascending.

    The split is computed **in-memory** (no JSON): a host graph is *forbidden*
    iff it contains the forbid graph as a **(non-induced) subgraph**
    (`subgraph_contains`) — the same semantics the `generate_subgraph_free_*`
    pruned generators use. For a complete forbid `K_r` this coincides with
    `induced_density(K_r; host) ≠ 0`, so complete-graph examples are unchanged.
    """
    obj_n, obj_edges, _ = parse_flagmatic(obj_flagmatic)
    hosts = load_graphs(N)
    admissible: list[tuple[int, Fraction]] = []
    forbidden: list[tuple[int, Fraction]] = []
    for i, host_edges in enumerate(hosts):
        d = induced_density(obj_n, obj_edges, N, host_edges)
        if d == 0:
            continue
        is_free = not subgraph_contains(forbid_n, forbid_edges, N, host_edges)
        (admissible if is_free else forbidden).append((i, d))
    return admissible, forbidden


def _lean_term(coef: Fraction, flag_ident: str) -> str:
    """Format a single `(c : ℝ) • flag` summand. Drops `•` when c == 1."""
    if coef == 1:
        return flag_ident
    if coef.denominator == 1:
        return f"({coef.numerator} : ℝ) • {flag_ident}"
    return f"({coef.numerator} / {coef.denominator} : ℝ) • {flag_ident}"


def _format_expansion(terms: list[tuple[int, Fraction]], N: int) -> str:
    """`(c0 : ℝ) • Flag_..._0 + Flag_..._3 + ...`"""
    parts = [_lean_term(c, f"FlagAlgebra_{N}_0_0_{i}") for (i, c) in terms]
    return " + ".join(parts)


def _density_value_literal(q: Fraction) -> str:
    """Format a rational density for the RHS of an auto-generated
    `flagDensity₁ Flag_X Flag_Y = <q>` simp lemma."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator} / {q.denominator}"


def render_density_simp_lemmas(
    obj_flagmatic: str, N: int, skip_indices: frozenset[int] = frozenset()
) -> tuple[str, dict[int, Fraction]]:
    """Auto-generate `@[simp]` lemmas `flagDensity₁ Flag_obj Flag_host_i = <d_i>`
    for every host index i in graphs_<N>.json. These are what `flag_expand_hfree
    N K{r}` needs to close goals when the RHS omits zero-density terms.

    `skip_indices` are host indices to omit — used for the forbid-containing
    hosts, whose `Flag_N_0_0_i` is never generated by the pruned commands, so a
    lemma naming it would reference an undefined constant.

    Returns `(lean_text, densities_by_index)`.
    """
    obj_n, obj_edges, _ = parse_flagmatic(obj_flagmatic)
    # Parse the objective flag indices for the Lean Flag name
    obj_idx = find_unlabeled_index(obj_n, obj_edges)
    obj_flag = f"Flag_{obj_n}_0_0_{obj_idx}"

    hosts = load_graphs(N)
    densities: dict[int, Fraction] = {}
    blocks: list[str] = []
    for i, host_edges in enumerate(hosts):
        d = induced_density(obj_n, obj_edges, N, host_edges)
        densities[i] = d
        if i in skip_indices:
            continue
        host_flag = f"Flag_{N}_0_0_{i}"
        thm_name = f"auto_flagDensity1_{obj_n}_0_0_{obj_idx}_{N}_0_0_{i}"
        blocks.append(
            f"@[simp]\n"
            f"private theorem {thm_name}\n"
            f"    : flagDensity₁ {obj_flag} {host_flag} = {_density_value_literal(d)}\n"
            f"  := by\n"
            f"  dsimp [{obj_flag}, {host_flag}]\n"
            f"  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]\n"
            f"  native_decide\n"
        )
    return "\n".join(blocks), densities


def render_expand_under_forbid(
    cert: dict,
    obj_ident: str,
    obj_flagmatic: str,
    N: int,
    forbid_expr: str,
    forbid_tag: str,
    lemma_name: str,
) -> str | None:
    """Auto-generate the helper lemma `obj =[forbid] (admissible expansion)`.

    Returns the Lean text for the standalone `lemma` declaration, or `None` if
    the post-forbid expansion would be empty (no admissible nonzero density —
    shouldn't happen for a valid certificate).
    """
    forbid_n, forbid_edges, _tag = _forbid_graph_from_description(
        cert.get("description", ""))
    if forbid_n is None:
        return None
    subgraph_mode = _tag is None
    forbid_graph_expr = (f"{forbid_tag}.toLabeledGraph.graph" if subgraph_mode
                         else f"completeGraph (Fin {forbid_n})")
    expand_tac = (f"flag_expand_hfree_subgraph {N} {forbid_tag}" if subgraph_mode
                  else f"flag_expand_hfree {N} {forbid_tag} "
                       f"(completeSym2Graph_finFlag_mem_forbiddenFlags {forbid_n})")
    admissible, forbidden = _expansion_coefficients(
        obj_flagmatic, N, forbid_n, forbid_edges)
    if not admissible:
        return None

    # Auto-generate the @[simp] density-evaluation lemmas — these are what
    # `flag_expand_hfree N F` needs to close (it relies on `flagDensity₁`
    # evaluating to concrete rationals via simp). **Every** forbid-containing host
    # is skipped (not just the nonzero-objective-density ones in `forbidden`): the
    # pruned commands never generate its `Flag_N_0_0_i`, so naming one — even in a
    # `= 0` lemma — would reference an undefined constant. Uses subgraph containment
    # so the skip set exactly matches the `generate_subgraph_free_*` output.
    skip = frozenset(
        i for i, he in enumerate(load_graphs(N))
        if subgraph_contains(forbid_n, forbid_edges, N, he))
    density_lemmas, _densities = render_density_simp_lemmas(
        obj_flagmatic, N, skip_indices=skip)

    # The pruned generator's `flagSetHfree` already excludes the forbidden hosts,
    # so the stated RHS is just the admissible (forbid-free) expansion and the
    # whole lemma is closed by `flag_expand_hfree` — no manual term peeling.
    admissible_expr = _format_expansion(admissible, N)

    return (
        f"-- Auto-generated `flagDensity₁` evaluation table (used by\n"
        f"-- `flag_expand_hfree {N} {forbid_tag}` to evaluate density coefficients).\n"
        f"{density_lemmas}\n"
        f"/-- Edge-based forbid-free expansion of the objective: `{obj_ident}` is\n"
        f"expanded directly over the {forbid_tag}-free {N}-vertex flags via\n"
        f"`flag_expand_hfree {N} {forbid_tag}` (`basisVector_quot_forbidEq_sum` rewritten onto\n"
        f"`flagSetHfree_{N}_0_0_{forbid_tag}`; the forbidden terms are dropped automatically). -/\n"
        f"lemma {lemma_name}\n"
        f"    : {obj_ident} =[{forbid_graph_expr}] {admissible_expr}\n"
        f"  := by\n"
        f"  {expand_tac}\n"
    )


# `Fin.sum_univ_<name>` lemmas used to expand `flagQuadraticForm`'s double sum.
# Mathlib provides two..eight; nine..sixteen are added by
# `LeanFlagAlgebras/Automation/FinSumUniv.lean` (imported only when a block exceeds 8 —
# see `required_lean_imports`). Bump both this table and that file in lockstep to
# support still-larger SDP blocks.
_FIN_SUM_NAMES = {
    2: "two", 3: "three", 4: "four", 5: "five",
    6: "six", 7: "seven", 8: "eight", 9: "nine",
    10: "ten", 11: "eleven", 12: "twelve", 13: "thirteen",
    14: "fourteen", 15: "fifteen", 16: "sixteen",
}

# Mathlib ships `Fin.sum_univ_*` only up to eight; sizes above this come from
# `LeanFlagAlgebras/Automation/FinSumUniv.lean`.
_MATHLIB_FIN_SUM_MAX = 8


def _max_block_size(cert: dict) -> int:
    """Largest SDP block (number of σ-flags), i.e. the biggest `Fin n` the
    quadratic-form expansion sums over. 0 if the cert has no blocks."""
    flags = cert.get("flags", [])
    return max((len(block) for block in flags), default=0)


def _block_names(t: int, total: int) -> dict[str, str]:
    """Identifier conventions matching `render_matrices` / `render_flag_vectors`."""
    suf = "" if total == 1 else _subscript(t + 1)
    return {
        "M": f"M{suf}",
        "M_real": f"M{suf}_real",
        "M_real_psd": f"M{suf}_real_posSemidef",
        "v": f"v{suf}",
    }


def render_proof_body(
    cert: dict, theorem_name: str = "main"
) -> tuple[str | None, str | None]:
    """Auto-generate the tactic block for the main theorem.

    Returns `(proof_body, helper_lemma)`:
      * `proof_body` — tactic block with 2-space indent, ready to follow `:= by`.
      * `helper_lemma` — when present, the standalone `lemma` text for the
        objective-expansion-under-forbid (branch B). Caller must emit this
        BEFORE the main theorem.

    Returns `(None, None)` if proof generation is unsupported (description
    parse failure, non-K_n forbid, or block size with no `Fin.sum_univ_*`).
    """
    desc = cert.get("description", "")
    try:
        obj_ident, n_obj = _objective_from_description(desc)
        obj_flagmatic = _DESC_OBJ_RE.search(desc).group(1)
    except (ValueError, LookupError, AttributeError):
        return None, None
    N = int(cert["order_of_admissible_graphs"])
    forbid_n, _forbid_edges, forbid_tag = _forbid_graph_from_description(desc)
    if forbid_n is None:
        return None, None
    subgraph_mode = forbid_tag is None  # non-complete forbid → subgraph semantics (Route B)
    if subgraph_mode:
        forbid_tag = "ForbidGraph"
        forbid_graph_expr = f"{forbid_tag}.toLabeledGraph.graph"
        forbid_expr = forbid_tag  # the `Sym2Graph` term itself
    else:
        forbid_graph_expr = f"completeGraph (Fin {forbid_n})"
        forbid_expr = _forbid_finflag_expr(forbid_tag)

    # The proof works entirely in the ordinary `forbidLEWith`/`forbidEqWith` framework.
    # The goal is already `≤[…]`, so no induced-bridge preamble is needed.
    prefix = ""

    # Branch detection: when n_obj < N we need an expand_under_forbid lemma.
    helper_lemma: str | None = None
    expand_rewrite: str = ""
    if n_obj < N:
        helper_name = f"{theorem_name}_expand_under_forbid"
        helper_lemma = render_expand_under_forbid(
            cert, obj_ident, obj_flagmatic, N, forbid_expr, forbid_tag, helper_name
        )
        if helper_lemma is None:
            return None, None
        # Step 4: expand the objective under the forbid relation. When T ≥ 2,
        # the LHS arrives as left-associated `((obj + Q1) + Q2) + ...`, but
        # `forbidLEWith_rw_left_add_right` matches the pattern `obj + ?` only
        # at the top-level `+`. Pre-rewrite with `add_assoc` to right-associate
        # the sum so the pattern hits. For T = 1 this step is unnecessary
        # (and `simp only` would error with "made no progress").
        T_blocks = len(cert["types"])
        if T_blocks >= 2:
            expand_rewrite = (
                f"  simp only [add_assoc]\n"
                f"  rw [forbidLEWith_rw_left_add_right {helper_name}]\n"
            )
        else:
            expand_rewrite = f"  rw [forbidLEWith_rw_left_add_right {helper_name}]\n"

    T = len(cert["types"])
    if T == 0:
        return None, None

    # Step 1: `have quadraticForm_trans` building obj ≤ obj + Σ ⟦v_tᵀ M_t v_t⟧
    have_rhs = obj_ident
    for t in range(T):
        n = _block_names(t, T)
        have_rhs += f" + ⟦flagQuadraticForm {n['M_real']} {n['v']}⟧₀"

    # Inner proof of `have` — stack `forbidLEWith_add_QuadraticForm` calls in
    # reverse order (the outermost + on the RHS gets peeled first), then
    # close with reflexivity.
    have_lines: list[str] = []
    for t in reversed(range(T)):
        n = _block_names(t, T)
        have_lines.append(
            f"    apply forbidLEWith_add_QuadraticForm {n['M_real']} "
            f"{n['M_real_psd']} {n['v']}"
        )
    have_lines.append(f"    exact forbidLEWith_refl _ {obj_ident}")
    have_block = "\n".join(have_lines)

    # Step 5: per-block simp expanding the quadratic form. To keep the file
    # warning-free we tailor each simp's argument list:
    #   * `flagQuadraticForm` only on the first simp (already unfolded after).
    #   * `Fin.sum_univ_<n_t>` and `add_assoc` only the FIRST time we see a
    #     given dimension n_t; once Lean has expanded one Σ over `Fin n_t`
    #     and right-associated the resulting sum, repeating these on a later
    #     block of the same dimension makes simp's linter flag them unused.
    simp_lines: list[str] = []
    seen_finsum_sizes: set[int] = set()
    for t in range(T):
        n = _block_names(t, T)
        n_t = len(cert["flags"][t])
        finsum = _FIN_SUM_NAMES.get(n_t)
        if finsum is None:
            return None, None
        pieces: list[str] = []
        if t == 0:
            pieces.append("flagQuadraticForm")
        pieces.extend([n["v"], n["M_real"], "ratMatrixToReal", n["M"]])
        if n_t not in seen_finsum_sizes:
            pieces.append(f"Fin.sum_univ_{finsum}")
            pieces.append("add_assoc")
            seen_finsum_sizes.add(n_t)
        simp_lines.append(f"  simp [{', '.join(pieces)}]")
    simp_block = "\n".join(simp_lines)

    if subgraph_mode:
        one_expand_line = (
            f"  apply forbidLEWith_trans_forbidEqWith_right ?_  "
            f"(forbidEqWith_smul (forbidEqWith_symm "
            f"(one_forbidEq_forbidExpand_one_subgraph {forbid_tag} {N})))\n"
        )
        expand_one_line = f"  expand_one_hfree_at_subgraph {N} {forbid_tag}\n"
    else:
        one_expand_line = (
            f"  apply forbidLEWith_trans_forbidEqWith_right ?_  "
            f"(forbidEqWith_smul (forbidEqWith_symm "
            f"(one_forbidEq_forbidExpand_one_ofMem {forbid_expr} "
            f"(completeSym2Graph_finFlag_mem_forbiddenFlags {forbid_n}) {N})))\n"
        )
        expand_one_line = f"  expand_one_hfree_at {N} {forbid_tag}\n"

    proof = (
        f"{prefix}"
        f"  have quadraticForm_trans : {obj_ident} ≤[{forbid_graph_expr}]\n"
        f"            {have_rhs}\n"
        f"    := by\n"
        f"{have_block}\n"
        f"  apply forbidLEWith_trans quadraticForm_trans\n"
        f"{one_expand_line}"
        f"{expand_rewrite}"
        f"\n"
        f"{simp_block}\n"
        f"  reduce_downward_flagmul\n"
        f"\n"
        f"{expand_one_line}"
        f"\n"
        # `downward_neg` / `downward_zero` are needed alongside `downward_add` / `downward_smul`:
        # reduce's neg branch produces `downward (-(c • F))` summands (and `downward 0`), and without
        # these lemmas the outer negation blocks `downward` from distributing, leaving the term stuck.
        f"  simp [smul_smul, downward_add, downward_smul, downward_neg, downward_zero]\n"
        f"  flagsum_ac_sort_rhs_pipeline\n"
        f"\n"
        f"  apply forbidLEWith_of_le\n"
        f"  flag_nonneg"
    )
    return proof, helper_lemma


def render_theorem_statement(cert: dict, theorem_name: str, proof_body: str | None = None) -> str:
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

    # The statement forbids the complete graph as a `SimpleGraph` term
    # `completeGraph (Fin r)` (ordinary `forbidLE`); the proof works directly in the
    # ordinary `forbidLEWith`/`forbidEqWith` framework (no induced bridge).
    forbid_n, _edges, _tag = _forbid_graph_from_description(desc)
    if forbid_n is None:
        forbid_expr = "/- TODO: forbid expression (could not parse the `forbid …` clause) -/"
    elif _tag is None:
        forbid_expr = "ForbidGraph.toLabeledGraph.graph"  # non-complete → subgraph semantics
    else:
        forbid_expr = f"completeGraph (Fin {forbid_n})"

    bound = cert.get("bound", "0")
    try:
        bound_lit = _lean_real_literal(bound)
    except (TypeError, ValueError):
        bound_lit = f"/- TODO: bound `{bound!r}` -/ (0 : ℝ)"

    if proof_body is None:
        tactic_block = "  sorry"
        note = "auto-generated statement, proof body TODO"
    else:
        tactic_block = proof_body
        note = "auto-generated"

    return (
        f"/-- **Main theorem ({note}).**\n"
        f"Certificate description: {desc!r}\n"
        f"Bound: {bound!r}. -/\n"
        f"theorem {theorem_name}\n"
        f"    : {obj_repr} ≤[{forbid_expr}] {bound_lit} • (1 : FlagAlgebra ∅ₜ)\n"
        f"  := by\n"
        f"{tactic_block}\n"
    )


def render_flag_vectors(cert: dict) -> str:
    """Render σ_t and v_t Lean definitions for every SDP block in the certificate."""
    types = cert["types"]
    flags = cert["flags"]
    assert len(types) == len(
        flags), "types and flags must have the same length"

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
    "open FlagAlgebras Forbid FlagAlgebras.Automation",
    "open SimpleGraph Matrix",
    "open FlagAlgebras.Compute",
]


def render_pruned_commands(cert: dict) -> str:
    """Emit the `def K{r}` forbid graph + the edge-based pruned generation /
    density / multiplication commands this certificate needs.

    Command-set rule (derived from the `generate_pruned_*` elab prerequisites):
      * empty-typed sizes = {objective size} ∪ {host N} ∪ {pattern size per block}
        (a σ-typed `generate_pruned_forbid_free_flags n …` needs empty-typed at n;
        the objective + host expansion name `FlagAlgebra_{n_obj/N}_0_0_*`);
      * typed flags        = (patN, k, m) and (N, k, m) per block;
      * pair-density + mul = (patN, N, k, m) per block.
    Only complete-graph forbids are supported (the forbid is `completeSym2Graph r`).
    """
    desc = cert.get("description", "")
    forbid_n, forbid_edges, tag = _forbid_graph_from_description(desc)
    if forbid_n is None:
        return "-- TODO: forbid graph (could not parse the `forbid …` clause)"
    subgraph_mode = tag is None  # non-complete forbid → subgraph semantics
    if subgraph_mode:
        tag = "ForbidGraph"
    N = int(cert["order_of_admissible_graphs"])

    # Objective size — the empty-typed flags the objective / its expansion name.
    try:
        _obj_ident, n_obj = _objective_from_description(desc)
    except (ValueError, LookupError):
        n_obj = N

    empty_sizes: set[int] = {n_obj, N}
    typed_triples: set[tuple[int, int, int]] = set()   # (n, k, m)
    block_params: list[tuple[int, int, int]] = []       # (patN, k, m) per block
    for t, type_str in enumerate(cert["types"]):
        k, _, _ = parse_flagmatic(type_str)
        _, _, type_idx = type_to_lean(type_str)
        patN, _, _ = parse_flagmatic(cert["flags"][t][0])
        empty_sizes.add(patN)
        typed_triples.add((patN, k, type_idx))
        typed_triples.add((N, k, type_idx))
        block_params.append((patN, k, type_idx))

    if subgraph_mode:
        # Non-complete forbid → *subgraph* semantics (Route B). The forbidden graph is an explicit
        # `Sym2Graph` term, and the `generate_subgraph_free_*` commands emit the subgraph-`F`-free
        # flags whose completeness bridges to the subgraph capstone's filter.
        edge_terms = ", ".join(f"s({u}, {v})" for (u, v) in sorted(forbid_edges))
        lines = [
            f"-- Subgraph-forbidding generation (Route B): `{tag}` is forbidden as a (non-induced)",
            f"-- subgraph. The `generate_subgraph_free_*` commands emit only the subgraph-`{tag}`-free",
            f"-- flags + completeness bridging to the subgraph capstone filter (`supergraphFamily`).",
            f"def {tag} : Sym2Graph {forbid_n} where",
            f"  edges := {{{edge_terms}}}",
            f"  edges_valid := by decide",
        ]
        for n in sorted(empty_sizes):
            lines.append(f"generate_subgraph_free_empty_typed_flags {n} {tag}")
        for (n, k, m) in sorted(typed_triples):
            lines.append(f"generate_subgraph_free_flags {n} {k} {m} {tag}")
        for (patN, k, m) in block_params:
            lines.append(f"generate_subgraph_free_flag_pair_density_theorems {patN} {N} {k} {m} {tag}")
            lines.append(f"generate_subgraph_free_mul_theorems {patN} {N} {k} {m} {tag}")
        return "\n".join(lines)

    lines = [
        f"-- Edge-based, pruning-backed forbid-free generation (decision D2): the forbidden",
        f"-- graph is the `Sym2Graph {forbid_n}` term `{tag} := completeSym2Graph {forbid_n}` (no canonical",
        f"-- forbidden flag, no `generate_complete_graph`); the {tag}-containing flags are never",
        f"-- generated. The pruned commands emit only the {tag}-free flags, their completeness, and",
        f"-- the forbid-free pair-density / multiplication theorems consumed by the proof below.",
        f"def {tag} : Sym2Graph {forbid_n} := completeSym2Graph {forbid_n}",
    ]
    for n in sorted(empty_sizes):
        lines.append(f"generate_pruned_forbid_free_empty_typed_flags {n} {tag}")
    for (n, k, m) in sorted(typed_triples):
        lines.append(f"generate_pruned_forbid_free_flags {n} {k} {m} {tag}")
    for (patN, k, m) in block_params:
        lines.append(
            f"generate_pruned_flag_pair_density_theorems {patN} {N} {k} {m} {tag}")
        lines.append(
            f"generate_pruned_forbid_free_mul_theorems {patN} {N} {k} {m} {tag}"
            f" (completeGraph (Fin {forbid_n})) (completeSym2Graph_finFlag_mem_forbiddenFlags {forbid_n})")
    return "\n".join(lines)


def required_lean_imports(cert: dict, branch_b: bool = False) -> list[str]:
    """Return the Lean `import` lines for the edge-based pruned pipeline.

    Base set (matches the migrated `Flagmatic/*.lean` files): the flag /
    forbid-free / density / mul generators, the Automation layer + matrix PSD
    utilities, and `Forbid.CommonGraphs` (where `completeSym2Graph` lives).

    `branch_b` (objective size < host N) additionally pulls in `Automation.FlagExpand`
    (the `flag_expand_hfree` tactic) and `FlagAlgebra.Compute.FlagDensity` (the
    `flagDensity₁` reflection lemma for the auto-generated `@[simp]` density
    table) — both unused, hence omitted, when the objective is itself a host flag.
    """
    base = [
        "import LeanFlagAlgebras.Flags.FlagGenerator",
        "import LeanFlagAlgebras.Flags.ForbidFreeGenerator",
        "import LeanFlagAlgebras.Flags.Densities.MulThmGenerator",
        "import LeanFlagAlgebras.Flags.Densities.DensityThmGenerator",
        "import LeanFlagAlgebras.Automation.Basic",
        "import LeanFlagAlgebras.Automation.FlagMulReduce",
        "import LeanFlagAlgebras.Automation.FlagSumSort",
        "import LeanFlagAlgebras.Automation.Matrix.PosSemiDef",
    ]
    if branch_b:
        base += [
            "import LeanFlagAlgebras.Automation.FlagExpand",
            "import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity",
        ]
    # Blocks with more than eight σ-flags expand their quadratic form with
    # `Fin.sum_univ_{nine..}`, which mathlib does not provide — pull in our
    # continuation lemmas. Omitted for the small examples so their regeneration
    # stays byte-for-byte with the committed files.
    if _max_block_size(cert) > _MATHLIB_FIN_SUM_MAX:
        base.append("import LeanFlagAlgebras.Automation.FinSumUniv")
    base.append("import LeanFlagAlgebras.Forbid.CommonGraphs")
    return base


def render_skeleton(cert: dict, namespace: str, theorem_name: str = "main") -> str:
    """Render a complete starter Lean API file for the edge-based pruned pipeline:
    imports, opens, namespace, `def K{r}` + `generate_pruned_*` commands, the
    matrix/PSD defs, σ_t / v_t definitions, the forbid-free objective expansion
    (branch B), and the auto-proved main theorem."""
    opens = "\n".join(LEAN_OPENS)
    commands = render_pruned_commands(cert)
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
    )

    proof_body, helper_lemma = render_proof_body(cert, theorem_name)
    # Branch B (objective expanded under the forbid) needs the extra
    # `flag_expand_hfree` / `flagDensity₁` imports; branch A does not.
    import_list = required_lean_imports(cert, branch_b=helper_lemma is not None)
    fallback_note = ""
    if proof_body is None:
        fallback_note = (
            "-- Proof body not auto-generated (unsupported description / "
            "forbid / block size).\n"
        )

    # Branch B emits a standalone objective-expansion lemma before the theorem;
    # branch A (objective is itself a host flag) has none. All required imports /
    # opens are already in the fixed edge-based set, so no conditional wiring.
    helper_section = helper_lemma + "\n" if helper_lemma is not None else ""

    imports = "\n".join(import_list)

    theorem_block = (
        # `maxHeartbeats 0` already disables the heartbeat limit (0 = unlimited). `maxRecDepth` is
        # bumped well above the 2000 default: the AC-sort / re-association on a long RHS sum (large
        # SDP blocks, e.g. subgraph forbids) otherwise hits "maximum recursion depth has been reached".
        f"set_option maxHeartbeats 0\n"
        f"set_option maxRecDepth 1000000\n"
        f"\n"
        f"{helper_section}"
        f"{fallback_note}"
        f"{render_theorem_statement(cert, theorem_name, proof_body)}"
    )

    return (
        f"{header}\n"
        f"{imports}\n"
        f"\n"
        f"{opens}\n"
        f"\n"
        f"namespace {namespace}\n"
        f"\n"
        f"{commands}\n"
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
        sep = "" if existing.endswith("\n\n") else (
            "\n" if existing.endswith("\n") else "\n\n")
        with args.target.open("a", encoding="utf-8") as f:
            f.write(sep + full)
    else:
        args.target.parent.mkdir(parents=True, exist_ok=True)
        args.target.write_text(full, encoding="utf-8")

    print(
        f"wrote {len(full)} chars to {args.target} ({len(cert['types'])} block(s))")


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


def _cmd_inspect(args: argparse.Namespace) -> None:
    with args.certificate.open() as f:
        cert = json.load(f)

    print(f"=== {args.certificate.name} ===")
    print(f"description: {cert['description']}")
    print(f"bound: {cert['bound']}")

    # Forbid graph: the edge-based pipeline forbids an inline-generated `Sym2Graph`
    # term — no canonical forbidden flag, no CommonGraphs.lean edit. A complete graph
    # takes Route A (`completeSym2Graph`, induced == subgraph); any other graph takes
    # Route B (an explicit edge set, forbidden as a non-induced subgraph). Both are
    # generated by `gen-skeleton`; only an unparseable `forbid …` clause is a real problem.
    forbid_n, forbid_edges, tag = _forbid_graph_from_description(cert.get("description", ""))
    m_forbid = re.search(r"forbid\s+(\S+)", cert.get("description", ""))
    forbid_str = m_forbid.group(1) if m_forbid else "<none>"
    if forbid_n is None:
        print(f"forbid graph: {forbid_str}  ->  UNPARSEABLE (could not read the `forbid …` clause)")
    elif tag is not None:
        print(f"forbid graph: {forbid_str} = K_{forbid_n}  ->  def {tag} : Sym2Graph {forbid_n} := completeSym2Graph {forbid_n}   (Route A: complete)")
        print(f"              bound stated as  ≤[completeGraph (Fin {forbid_n})]  (ordinary forbid)")
    else:
        edge_terms = ", ".join(f"s({u}, {v})" for (u, v) in sorted(forbid_edges))
        print(f"forbid graph: {forbid_str}  ->  def ForbidGraph : Sym2Graph {forbid_n} where edges := {{{edge_terms}}}   (Route B: subgraph)")
        print(f"              bound stated as  ≤[ForbidGraph.toLabeledGraph.graph]  (subgraph forbid)")

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

    print("\ngeneration commands (what gen-skeleton emits; no JSON on disk):")
    for cmd in render_pruned_commands(cert).splitlines():
        if cmd.startswith("--") or not cmd.strip():
            continue
        print(f"  {cmd}")


def _cmd_gen_vectors(args: argparse.Namespace) -> None:
    with args.certificate.open() as f:
        cert = json.load(f)
    text = render_flag_vectors(cert)

    if args.target.exists():
        existing = args.target.read_text(encoding="utf-8")
        sep = "" if existing.endswith("\n\n") else (
            "\n" if existing.endswith("\n") else "\n\n")
        with args.target.open("a", encoding="utf-8") as f:
            f.write(sep + text)
    else:
        args.target.write_text(text, encoding="utf-8")

    print(
        f"wrote {len(text)} chars to {args.target} ({len(cert['types'])} block(s))")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(
        prog="flagmatic_to_lean",
        description="Convert Flagmatic certificates to Lean flag-algebra API code.",
        epilog=(
            "Examples:\n"
            "  python flagmatic_to_lean.py inspect       mantel_sparse_cert.json\n"
            "  python flagmatic_to_lean.py gen-skeleton  mantel_sparse_cert.json out.lean\n"
            "  python flagmatic_to_lean.py gen-matrices  mantel_sparse_cert.json out.lean\n"
            "  python flagmatic_to_lean.py gen-vectors   mantel_sparse_cert.json out.lean\n"
            "\nTypical workflow:  inspect  ->  gen-skeleton\n"
            "Per-command help:  flagmatic_to_lean.py <subcommand> --help\n"
            "Full reference:    see the module docstring at the top of this file."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_inspect = sub.add_parser(
        "inspect", help="print certificate -> Lean identifier mapping")
    p_inspect.add_argument("certificate", type=Path)
    p_inspect.set_defaults(func=_cmd_inspect)

    p_gen = sub.add_parser(
        "gen-vectors", help="append σ_t and v_t Lean definitions to a file")
    p_gen.add_argument("certificate", type=Path)
    p_gen.add_argument("target", type=Path,
                       help="Lean file to append to (created if absent)")
    p_gen.set_defaults(func=_cmd_gen_vectors)

    p_mat = sub.add_parser(
        "gen-matrices",
        help="append M_t / dM_t / LM_t Lean definitions and the PSD theorem to a file",
    )
    p_mat.add_argument("certificate", type=Path)
    p_mat.add_argument("target", type=Path,
                       help="Lean file to append to (created if absent)")
    p_mat.set_defaults(func=_cmd_gen_matrices)

    p_skel = sub.add_parser(
        "gen-skeleton",
        help=(
            "write a complete starter Lean file "
            "(imports + opens + namespace + loads + matrices + σ/v + auto-proved main theorem)"
        ),
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
    p_skel.add_argument("--force", action="store_true",
                        help="overwrite the target if it exists")
    p_skel.set_defaults(func=_cmd_gen_skeleton)

    args = ap.parse_args(argv)
    rc = args.func(args)
    if isinstance(rc, int):
        raise SystemExit(rc)


if __name__ == "__main__":
    main()
