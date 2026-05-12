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
    index: int
    edges: Tuple[Edge, ...]
    n: int
    labels: Tuple[int, ...]


def normalize_edges(edges: Iterable[Sequence[int]]) -> Tuple[Edge, ...]:
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
    # Supports names like flags_5_3_1.json or graphs_5.json.
    m = re.search(r"_(\d+)(?:_\d+_\d+)?\.json$", path.name)
    if not m:
        return None
    return int(m.group(1))


def infer_n_from_edges(edges: Tuple[Edge, ...]) -> int:
    if not edges:
        return 0
    return max(max(u, v) for u, v in edges) + 1


def parse_graph_records(path: Path) -> Tuple[str, List[GraphRecord]]:
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
    return [
        r for r in records
        if not contains_forbidden_subgraph(r.edges, r.n, forbid_edges, forbid_n)
    ]


def relabel_edges(edges: Tuple[Edge, ...], perm: Sequence[int]) -> Tuple[Edge, ...]:
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
    if k <= 1:
        return tuple()
    best = None
    for perm in itertools.permutations(range(k)):
        candidate = relabel_edges(edges, perm)
        if best is None or candidate < best:
            best = candidate
    return best if best is not None else tuple()


def canonical_labeled_form(edges: Tuple[Edge, ...], n: int, labels: Tuple[int, ...]) -> Tuple[Edge, ...]:
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
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def density_p_f1_f2_given_g(host: GraphRecord, f1: GraphRecord, f2: GraphRecord) -> Fraction:
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
    p = Path(path_str)
    if p.is_absolute():
        return p
    cwd_candidate = (Path.cwd() / p).resolve()
    if cwd_candidate.exists():
        return cwd_candidate
    return (Path(__file__).resolve().parent / p).resolve()


def resolve_output_path(path_str: str) -> Path:
    p = Path(path_str)
    if p.is_absolute():
        return p
    return (Path.cwd() / p).resolve()


# Known shorthands: (n, 0-indexed edges)
_K3_EDGES: Tuple[Edge, ...] = ((0, 1), (0, 2), (1, 2))
_K4_EDGES: Tuple[Edge, ...] = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Compute p(F1, F2; G) for all forbidden-graph-free hosts G "
            "and all unordered pairs (with replacement) of forbidden-graph-free patterns."
        )
    )
    parser.add_argument("--host", required=True, help="Host graph JSON path (usually flags_i_j_k.json)")
    parser.add_argument("--pattern", required=True, help="Pattern graph JSON path (usually flags_i_j_k.json)")
    parser.add_argument("--out", required=False, help="Output JSON path")

    forbid_group = parser.add_mutually_exclusive_group(required=True)
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

    args = parser.parse_args()

    # Resolve forbidden graph
    if args.forbid_K3:
        forbid_n: int = 3
        forbid_edges: Tuple[Edge, ...] = _K3_EDGES
        forbid_tag: str = "K3"
    elif args.forbid_K4:
        forbid_n = 4
        forbid_edges = _K4_EDGES
        forbid_tag = "K4"
    else:
        forbid_n, forbid_edges = parse_flagmatic_notation(args.forbid)
        forbid_tag = args.forbid  # e.g. "3:122331"

    host_path = resolve_input_path(args.host)
    pattern_path = resolve_input_path(args.pattern)

    host_tag, host_all = parse_graph_records(host_path)
    pattern_tag, pattern_all = parse_graph_records(pattern_path)

    host_free = forbid_free_only(host_all, forbid_edges, forbid_n)
    pattern_free = forbid_free_only(pattern_all, forbid_edges, forbid_n)

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

    output = {
        "host": host_tag,
        "pattern": pattern_tag,
        "forbid": {
            "tag": forbid_tag,
            "n": forbid_n,
            "edges": [list(e) for e in forbid_edges],
        },
        "host_free_indices": [g.index for g in host_free],
        "pattern_free_indices": [f.index for f in pattern_free],
        "densities": density_rows,
    }

    if args.out:
        out_path = resolve_output_path(args.out)
    else:
        out_name = f"density_{host_tag}_from_{pattern_tag}.json"
        out_path = Path(__file__).resolve().parent / out_name

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(output, f, indent=2)

    print(f"Forbidden graph: {forbid_tag} (n={forbid_n}, edges={forbid_edges})")
    print(f"Host graphs total: {len(host_all)}, {forbid_tag}-free: {len(host_free)}")
    print(f"Pattern graphs total: {len(pattern_all)}, {forbid_tag}-free: {len(pattern_free)}")
    print(f"Saved densities: {len(density_rows)} rows")
    print(f"Output: {out_path}")


if __name__ == "__main__":
    main()
