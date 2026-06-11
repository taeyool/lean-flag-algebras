"""Compute pair densities p(F1, F2; G) over forbidden-subgraph-free graphs.

Reads a host graph JSON file and a pattern graph JSON file (each either a
list-of-edge-lists like ``Graphs/graphs_n.json`` or a flag object like
``Flags/flags_n_k_m.json``), discards every host/pattern containing the chosen
forbidden subgraph (``K3``, ``K4``, or an arbitrary graph in flagmatic
notation), and for each unordered pair (with replacement) of forbidden-free
patterns and each forbidden-free host computes the subflag-multiplication
density ``p(F1, F2; G)`` exactly as a Fraction.

Output JSON (``density_<host_tag>_from_<pattern_tag>.json`` by default) has
fields ``host``, ``pattern``, ``forbid``, ``host_free_indices``,
``pattern_free_indices``, and ``densities`` (rows ``[patternIdx1, patternIdx2,
hostIdx, value]``). This file is consumed on the Lean side by
``load_flag_pair_density_theorems`` (DensityLoader.lean) and
``load_forbid_mul_theorems`` (MulLoader.lean).

Example:
    python calculate_densities.py --host ../Flags/flags_4_2_0.json \\
        --pattern ../Flags/flags_3_2_0.json --forbid-K3
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple


Edge = Tuple[int, int]


@dataclass(frozen=True)
class GraphRecord:
    """One graph/flag: its index in the source file, edges, vertex count, and
    the labeled (type) vertex indices."""
    index: int
    edges: Tuple[Edge, ...]
    n: int
    labels: Tuple[int, ...]


def normalize_edges(edges: Iterable[Sequence[int]]) -> Tuple[Edge, ...]:
    """Return edges as a sorted tuple of (u, v) pairs with u < v; reject loops."""
    normalized: List[Edge] = []
    for pair in edges:
        if len(pair) != 2:
            raise ValueError(f"Edge must have 2 endpoints, got: {pair}")
        u = int(pair[0])
        v = int(pair[1])
        if u == v:
            raise ValueError(f"Self-loop ({u}, {v}) is not allowed")
        if u > v:
            u, v = v, u
        normalized.append((u, v))
    normalized.sort()
    return tuple(normalized)


def infer_n_from_filename(path: Path) -> int | None:
    """Infer the vertex count from a ``flags_n_..`` / ``graphs_n`` filename."""
    # Supports names like flags_5_3_1.json or graphs_5.json.
    m = re.search(r"_(\d+)(?:_\d+_\d+)?\.json$", path.name)
    if not m:
        return None
    return int(m.group(1))


def infer_n_from_edges(edges: Tuple[Edge, ...]) -> int:
    """Infer the vertex count as one more than the largest endpoint."""
    if not edges:
        return 0
    return max(max(u, v) for u, v in edges) + 1


def parse_graph_records(path: Path) -> Tuple[str, List[GraphRecord]]:
    """Load a graphs/flags JSON file into a file tag and list of GraphRecords.

    Accepts either a top-level list of edge lists or a flag object with a
    ``flags`` key (carrying per-flag ``type_indices``).
    """
    with path.open("r", encoding="utf-8") as f:
        raw = json.load(f)

    tag = extract_file_tag(path)

    if isinstance(raw, dict) and "flags" in raw:
        n_top = raw.get("n")
        k_top = raw.get("k", 0)
        records: List[GraphRecord] = []
        for idx, item in enumerate(raw["flags"]):
            edges = normalize_edges(item.get("edges", []))
            n_val = int(n_top) if n_top is not None else infer_n_from_edges(edges)
            labels_raw = item.get("type_indices")
            if labels_raw is None:
                labels = tuple(range(int(k_top)))
            else:
                labels = tuple(int(x) for x in labels_raw)
            records.append(GraphRecord(index=idx, edges=edges, n=n_val, labels=labels))
        return tag, records

    if isinstance(raw, list):
        n_guess = infer_n_from_filename(path)
        records = []
        for idx, edges_raw in enumerate(raw):
            edges = normalize_edges(edges_raw)
            n_val = n_guess if n_guess is not None else infer_n_from_edges(edges)
            records.append(GraphRecord(index=idx, edges=edges, n=n_val, labels=tuple()))
        return tag, records

    raise ValueError(
        "Unsupported JSON format. Expected either list-of-graphs or object with key 'flags'."
    )


def extract_file_tag(path: Path) -> str:
    """Extract the ``n_k_m`` tag from a ``flags_*.json`` name (else the stem)."""
    # Example: flags_5_3_1.json -> 5_3_1
    m = re.search(r"flags_(\d+_\d+_\d+)\.json$", path.name)
    if m:
        return m.group(1)
    # Fallback: filename without extension
    return path.stem


def parse_flagmatic_notation(s: str) -> Tuple[int, Tuple[Edge, ...]]:
    """Parse flagmatic graph notation like '3:122331' or '4:121314232434'.

    Vertices are 1-indexed in the notation; returned edges are 0-indexed.
    Each consecutive pair of characters in the edge string is one edge.
    """
    parts = s.split(":")
    if len(parts) != 2:
        raise ValueError(
            f"Invalid flagmatic notation {s!r}. Expected 'n:edge_pairs', e.g. '3:122331'."
        )
    try:
        n = int(parts[0])
    except ValueError:
        raise ValueError(f"Cannot parse vertex count from {parts[0]!r}")
    if n < 1:
        raise ValueError(f"Vertex count must be at least 1, got {n}")

    edge_str = parts[1]
    if len(edge_str) % 2 != 0:
        raise ValueError(
            f"Edge string must have even length (pairs of vertices), got {edge_str!r}"
        )

    raw_edges: List[Edge] = []
    for i in range(0, len(edge_str), 2):
        try:
            u = int(edge_str[i]) - 1      # convert 1-indexed → 0-indexed
            v = int(edge_str[i + 1]) - 1
        except ValueError:
            raise ValueError(
                f"Non-digit character in edge string at position {i}: {edge_str!r}"
            )
        if u < 0 or v < 0 or u >= n or v >= n:
            raise ValueError(
                f"Vertex index out of range [1,{n}] in edge string {edge_str!r}"
            )
        if u == v:
            raise ValueError(f"Self-loop not allowed (vertex {u + 1})")
        raw_edges.append((u, v))

    # deduplicate and sort
    seen: set[Edge] = set()
    deduped: List[Edge] = []
    for u, v in raw_edges:
        e: Edge = (u, v) if u < v else (v, u)
        if e not in seen:
            seen.add(e)
            deduped.append(e)

    return n, normalize_edges(deduped)




def contains_forbidden_subgraph(
    host_edges: Tuple[Edge, ...],
    host_n: int,
    forbid_edges: Tuple[Edge, ...],
    forbid_n: int,
) -> bool:
    """Return True if host contains the forbidden graph as a (not necessarily induced) subgraph."""
    if not forbid_edges:
        return True
    if host_n < forbid_n:
        return False
    host_edge_set = set(host_edges)
    for mapping in itertools.permutations(range(host_n), forbid_n):
        if all(
            (min(mapping[u], mapping[v]), max(mapping[u], mapping[v])) in host_edge_set
            for u, v in forbid_edges
        ):
            return True
    return False


def forbid_free_only(
    records: Sequence[GraphRecord],
    forbid_edges: Tuple[Edge, ...],
    forbid_n: int,
) -> List[GraphRecord]:
    """Keep only the records that do not contain the forbidden subgraph."""
    return [
        r for r in records
        if not contains_forbidden_subgraph(r.edges, r.n, forbid_edges, forbid_n)
    ]


def relabel_edges(edges: Tuple[Edge, ...], perm: Sequence[int]) -> Tuple[Edge, ...]:
    """Apply a vertex permutation to the edges and renormalize."""
    relabeled: List[Edge] = []
    for u, v in edges:
        nu = perm[u]
        nv = perm[v]
        if nu > nv:
            nu, nv = nv, nu
        relabeled.append((nu, nv))
    relabeled.sort()
    return tuple(relabeled)


def canonical_form(edges: Tuple[Edge, ...], k: int) -> Tuple[Edge, ...]:
    """Lexicographically smallest edge list over all relabelings of k vertices."""
    if k <= 1:
        return tuple()
    best = None
    for perm in itertools.permutations(range(k)):
        candidate = relabel_edges(edges, perm)
        if best is None or candidate < best:
            best = candidate
    return best if best is not None else tuple()


def canonical_labeled_form(edges: Tuple[Edge, ...], n: int, labels: Tuple[int, ...]) -> Tuple[Edge, ...]:
    """Canonical edge list with the labeled vertices fixed as 0..k-1 and the
    unlabeled tail permuted to its lexicographically smallest form."""
    k = len(labels)
    if len(set(labels)) != k:
        raise ValueError("Label indices must be distinct")
    if any(v < 0 or v >= n for v in labels):
        raise ValueError("Label index out of range")

    unlabeled = [v for v in range(n) if v not in set(labels)]
    base_map_old_to_new = {}
    for t, v in enumerate(labels):
        base_map_old_to_new[v] = t
    for i, v in enumerate(unlabeled):
        base_map_old_to_new[v] = k + i

    base_perm = [base_map_old_to_new[v] for v in range(n)]
    base_edges = relabel_edges(edges, base_perm)

    if n == k:
        return base_edges

    best = None
    tail = list(range(k, n))
    for perm_tail in itertools.permutations(tail):
        full_perm = list(range(n))
        for pos, target in enumerate(perm_tail):
            full_perm[k + pos] = target
        candidate = relabel_edges(base_edges, full_perm)
        if best is None or candidate < best:
            best = candidate
    return best if best is not None else base_edges


def induced_edges_on_subset(host_edge_set: set[Edge], subset: Tuple[int, ...]) -> Tuple[Edge, ...]:
    """Return the subgraph induced on ``subset``, re-indexed to 0..k-1."""
    induced: List[Edge] = []
    k = len(subset)
    for i in range(k):
        for j in range(i + 1, k):
            a = subset[i]
            b = subset[j]
            edge = (a, b) if a < b else (b, a)
            if edge in host_edge_set:
                induced.append((i, j))
    induced.sort()
    return tuple(induced)


def frac_to_str(value: Fraction) -> str:
    """Format a Fraction as ``"num"`` or ``"num/den"``."""
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def density_p_f1_f2_given_g(host: GraphRecord, f1: GraphRecord, f2: GraphRecord) -> Fraction:
    """Exact subflag-multiplication density p(F1, F2; G).

    Counts the fraction of ways to split the unlabeled host vertices into two
    disjoint groups (sizes m1-k and m2-k, sharing the k labeled vertices) whose
    induced labeled subflags equal F1 and F2 respectively.
    """
    n_host = host.n
    m1 = f1.n
    m2 = f2.n
    k = len(host.labels)

    if len(f1.labels) != k or len(f2.labels) != k:
        return Fraction(0, 1)
    if k > m1 or k > m2:
        return Fraction(0, 1)
    if len(set(host.labels)) != k:
        return Fraction(0, 1)

    r1 = m1 - k
    r2 = m2 - k
    if n_host < k + r1 + r2:
        return Fraction(0, 1)

    host_edge_set = set(host.edges)
    f1_canonical = canonical_labeled_form(f1.edges, m1, f1.labels)
    f2_canonical = canonical_labeled_form(f2.edges, m2, f2.labels)

    label_set = tuple(host.labels)
    label_set_set = set(label_set)
    unlabeled_vertices = [v for v in range(n_host) if v not in label_set_set]

    total = 0
    good = 0

    for a_extra in itertools.combinations(unlabeled_vertices, r1):
        a_extra_set = set(a_extra)
        a_vertices = label_set + tuple(a_extra)
        a_local = {v: i for i, v in enumerate(a_vertices)}
        a_edges: List[Edge] = []
        for i in range(len(a_vertices)):
            for j in range(i + 1, len(a_vertices)):
                u = a_vertices[i]
                w = a_vertices[j]
                e = (u, w) if u < w else (w, u)
                if e in host_edge_set:
                    a_edges.append((a_local[u], a_local[w]))
        a_edges_tuple = tuple(sorted(a_edges))
        a_labels = tuple(range(k))
        a_canonical = canonical_labeled_form(a_edges_tuple, m1, a_labels)

        remaining = [v for v in unlabeled_vertices if v not in a_extra_set]
        for b_extra in itertools.combinations(remaining, r2):
            total += 1
            if a_canonical != f1_canonical:
                continue

            b_vertices = label_set + tuple(b_extra)
            b_local = {v: i for i, v in enumerate(b_vertices)}
            b_edges: List[Edge] = []
            for i in range(len(b_vertices)):
                for j in range(i + 1, len(b_vertices)):
                    u = b_vertices[i]
                    w = b_vertices[j]
                    e = (u, w) if u < w else (w, u)
                    if e in host_edge_set:
                        b_edges.append((b_local[u], b_local[w]))
            b_edges_tuple = tuple(sorted(b_edges))
            b_labels = tuple(range(k))
            b_canonical = canonical_labeled_form(b_edges_tuple, m2, b_labels)
            if b_canonical == f2_canonical:
                good += 1

    if total == 0:
        return Fraction(0, 1)
    return Fraction(good, total)


def resolve_input_path(path_str: str) -> Path:
    """Resolve an input path relative to CWD, falling back to the script dir."""
    p = Path(path_str)
    if p.is_absolute():
        return p
    cwd_candidate = (Path.cwd() / p).resolve()
    if cwd_candidate.exists():
        return cwd_candidate
    return (Path(__file__).resolve().parent / p).resolve()


def resolve_output_path(path_str: str) -> Path:
    """Resolve an output path relative to the current working directory."""
    p = Path(path_str)
    if p.is_absolute():
        return p
    return (Path.cwd() / p).resolve()


def complete_graph_edges(n: int) -> Tuple[Edge, ...]:
    """Edges of the complete graph K_n on vertices 0..n-1 (sorted, 0-indexed)."""
    return tuple((u, v) for u in range(n) for v in range(u + 1, n))


def main() -> None:
    """CLI: parse host/pattern/forbid args and write the density JSON file."""
    parser = argparse.ArgumentParser(
        description=(
            "Compute p(F1, F2; G) for all forbidden-graph-free hosts G "
            "and all unordered pairs (with replacement) of forbidden-graph-free patterns."
        )
    )
    parser.add_argument("--host", required=True, help="Host graph JSON path (usually flags_i_j_k.json)")
    parser.add_argument("--pattern", required=True, help="Pattern graph JSON path (usually flags_i_j_k.json)")
    parser.add_argument("--out", required=False, help="Output JSON path")
    parser.add_argument(
        "--tag",
        default=None,
        help=(
            "Override the forbid tag (and output filename tag) with a clean Lean identifier, "
            "e.g. 'C4'. Needed for non-clique '--forbid' graphs so the JSON tag matches "
            "a `def <tag>` on the Lean side. The Kn shorthands already emit a clean 'KN' tag."
        ),
    )

    forbid_group = parser.add_mutually_exclusive_group(required=False)
    forbid_group.add_argument(
        "--forbid",
        metavar="NOTATION",
        help=(
            "Forbidden graph in flagmatic notation, e.g. '3:122331' (triangle) "
            "or '4:121314232434' (K4). Vertices are 1-indexed; "
            "each consecutive character pair in the edge string is one edge."
        ),
    )
    forbid_group.add_argument(
        "--forbid-K3",
        action="store_true",
        default=False,
        help="Forbid triangle (K3). Shorthand for --forbid 3:122331.",
    )
    forbid_group.add_argument(
        "--forbid-K4",
        action="store_true",
        default=False,
        help="Forbid complete graph K4. Shorthand for --forbid 4:121314232434.",
    )
    forbid_group.add_argument(
        "--forbid-K5",
        action="store_true",
        default=False,
        help="Forbid complete graph K5. Shorthand for --forbid-Kn 5.",
    )
    forbid_group.add_argument(
        "--forbid-Kn",
        metavar="N",
        type=int,
        default=None,
        help="Forbid the complete graph K_N for any N >= 1 (tag 'KN').",
    )

    args = parser.parse_args()

    # Resolve forbidden graph (None means no filtering)
    # First collapse all complete-graph shorthands to a single clique size.
    if args.forbid_Kn is not None:
        clique_n: int | None = args.forbid_Kn
    elif args.forbid_K3:
        clique_n = 3
    elif args.forbid_K4:
        clique_n = 4
    elif args.forbid_K5:
        clique_n = 5
    else:
        clique_n = None

    if clique_n is not None:
        if clique_n < 1:
            parser.error(f"--forbid-Kn requires N >= 1, got {clique_n}")
        forbid_n: int | None = clique_n
        forbid_edges: Tuple[Edge, ...] | None = complete_graph_edges(clique_n)
        forbid_tag: str = f"K{clique_n}"
    elif args.forbid:
        forbid_n, forbid_edges = parse_flagmatic_notation(args.forbid)
        forbid_tag = args.forbid  # e.g. "3:122331"
    else:
        forbid_n = None
        forbid_edges = None
        forbid_tag = "none"

    # A clean explicit tag (e.g. "C4") overrides the tag so non-clique forbids can
    # name the matching Lean `def`. Only meaningful when a graph is forbidden.
    if args.tag is not None:
        if forbid_edges is None:
            parser.error("--tag requires a forbidden graph (use with --forbid / --forbid-Kn / --forbid-K3 ...)")
        forbid_tag = args.tag

    host_path = resolve_input_path(args.host)
    pattern_path = resolve_input_path(args.pattern)

    host_tag, host_all = parse_graph_records(host_path)
    pattern_tag, pattern_all = parse_graph_records(pattern_path)

    if forbid_edges is not None:
        host_free = forbid_free_only(host_all, forbid_edges, forbid_n)
        pattern_free = forbid_free_only(pattern_all, forbid_edges, forbid_n)
    else:
        host_free = list(host_all)
        pattern_free = list(pattern_all)

    density_rows = []
    pattern_pairs = itertools.combinations_with_replacement(pattern_free, 2)
    for f1, f2 in pattern_pairs:
        i = min(f1.index, f2.index)
        j = max(f1.index, f2.index)
        f1_use = f1 if f1.index == i else f2
        f2_use = f2 if f2.index == j else f1
        for g in host_free:
            val = density_p_f1_f2_given_g(g, f1_use, f2_use)
            density_rows.append([i, j, g.index, frac_to_str(val)])

    forbid_field = (
        None
        if forbid_edges is None
        else {
            "tag": forbid_tag,
            "n": forbid_n,
            "edges": [list(e) for e in forbid_edges],
        }
    )

    output = {
        "host": host_tag,
        "pattern": pattern_tag,
        "forbid": forbid_field,
        "host_free_indices": [g.index for g in host_free],
        "pattern_free_indices": [f.index for f in pattern_free],
        "densities": density_rows,
    }

    if args.out:
        out_path = resolve_output_path(args.out)
    else:
        if forbid_edges is None:
            out_name = f"density_{host_tag}_from_{pattern_tag}_no_forbid.json"
        else:
            # Always tag the output filename with the forbid identifier so
            # two computations under different forbids (e.g. K3 vs K5) do
            # not silently overwrite each other. Replace any non-alphanum
            # characters in the tag (e.g. flagmatic strings like "3:122331")
            # with underscores so it's filename-safe.
            safe_tag = re.sub(r"[^A-Za-z0-9]", "_", forbid_tag)
            out_name = f"density_{host_tag}_from_{pattern_tag}_forbid_{safe_tag}.json"
        out_path = Path(__file__).resolve().parent / out_name

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(output, f, indent=2)

    if forbid_edges is None:
        print("Forbidden graph: none (all graphs included)")
        print(f"Host graphs total: {len(host_all)} (all included)")
        print(f"Pattern graphs total: {len(pattern_all)} (all included)")
    else:
        print(f"Forbidden graph: {forbid_tag} (n={forbid_n}, edges={forbid_edges})")
        print(f"Host graphs total: {len(host_all)}, {forbid_tag}-free: {len(host_free)}")
        print(f"Pattern graphs total: {len(pattern_all)}, {forbid_tag}-free: {len(pattern_free)}")
    print(f"Saved densities: {len(density_rows)} rows")
    print(f"Output: {out_path}")


if __name__ == "__main__":
    main()
