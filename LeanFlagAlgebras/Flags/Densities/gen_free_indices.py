"""List the indices of graphs that avoid a given forbidden subgraph.

Reads a ``graphs_n.json`` file (a top-level list of edge lists), checks each
graph for the chosen forbidden subgraph (``K3``, ``K4``, or an arbitrary graph
in flagmatic notation), and writes a JSON file recording ``n``, the forbidden
graph, the total number of graphs, and ``free_graph_indices`` (the indices of
graphs that do NOT contain the forbidden subgraph).

Output (``<input_stem>_<tag>_free_indices.json`` by default) is consumed on the
Lean side by the ``load_forbid_density_theorems`` macro in DensityLoader.lean
(and indirectly supports the forbidden-subgraph reasoning in MulLoader.lean).

Example:
    python gen_free_indices.py ../Graphs/graphs_4.json --forbid-K3
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
from pathlib import Path
from typing import List, Sequence, Tuple


Edge = Tuple[int, int]


def infer_n_from_filename(path: Path) -> int | None:
    """Infer the vertex count ``n`` from a ``graphs_n.json`` filename."""
    match = re.search(r"graphs_(\d+)\.json$", path.name)
    if match:
        return int(match.group(1))
    return None


def parse_flagmatic_notation(s: str) -> Tuple[int, Tuple[Edge, ...]]:
    """Parse flagmatic notation like '3:122331'. Returns (n, 0-indexed edges)."""
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
        raise ValueError(f"Edge string must have even length, got {edge_str!r}")

    seen: set[Edge] = set()
    edges: List[Edge] = []
    for i in range(0, len(edge_str), 2):
        try:
            u = int(edge_str[i]) - 1
            v = int(edge_str[i + 1]) - 1
        except ValueError:
            raise ValueError(f"Non-digit at position {i} in {edge_str!r}")
        if u < 0 or v < 0 or u >= n or v >= n:
            raise ValueError(f"Vertex index out of range in {edge_str!r}")
        if u == v:
            raise ValueError("Self-loop not allowed")
        e: Edge = (u, v) if u < v else (v, u)
        if e not in seen:
            seen.add(e)
            edges.append(e)
    edges.sort()
    return n, tuple(edges)


def notation_to_filename(notation: str) -> str:
    """Convert a flagmatic notation string to a filename-safe string (colon → underscore)."""
    return notation.replace(":", "_")


def contains_forbidden_subgraph(
    host_edges: Sequence[Sequence[int]],
    host_n: int,
    forbid_edges: Tuple[Edge, ...],
    forbid_n: int,
) -> bool:
    """Return True if host contains the forbidden graph as a subgraph."""
    if not forbid_edges:
        return True
    if host_n < forbid_n:
        return False
    host_edge_set = {(min(u, v), max(u, v)) for u, v in host_edges}
    for mapping in itertools.permutations(range(host_n), forbid_n):
        if all(
            (min(mapping[u], mapping[v]), max(mapping[u], mapping[v])) in host_edge_set
            for u, v in forbid_edges
        ):
            return True
    return False


def collect_free_indices(
    graphs: list[list[list[int]]],
    forbid_edges: Tuple[Edge, ...],
    forbid_n: int,
    n_hint: int | None,
) -> list[int]:
    """Return the indices of graphs that do not contain the forbidden subgraph."""
    indices = []
    for idx, edges in enumerate(graphs):
        host_n = n_hint if n_hint is not None else (
            max((max(u, v) for u, v in edges), default=-1) + 1
        )
        if not contains_forbidden_subgraph(edges, host_n, forbid_edges, forbid_n):
            indices.append(idx)
    return indices


_K3_EDGES: Tuple[Edge, ...] = ((0, 1), (0, 2), (1, 2))
_K4_EDGES: Tuple[Edge, ...] = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))


def main() -> None:
    """CLI: parse the input path and forbid args and write the free-indices JSON."""
    parser = argparse.ArgumentParser(
        description=(
            "Read graphs_n.json and write a JSON file containing the total number "
            "of graphs and indices of forbidden-graph-free graphs."
        )
    )
    parser.add_argument("input_path", help="Path to input graphs JSON file")
    parser.add_argument(
        "-o", "--output",
        default=None,
        help="Output JSON path (default: <script_dir>/<input_stem>_<tag>_free_indices.json)",
    )

    forbid_group = parser.add_mutually_exclusive_group(required=True)
    forbid_group.add_argument(
        "--forbid",
        metavar="NOTATION",
        help=(
            "Forbidden graph in flagmatic notation, e.g. '3:122331' (triangle) "
            "or '4:121314232434' (K4)."
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
        help="Forbid K4. Shorthand for --forbid 4:121314232434.",
    )

    args = parser.parse_args()

    if args.forbid_K3:
        forbid_n, forbid_edges = 3, _K3_EDGES
        forbid_tag = "K3"
        forbid_filename_tag = "K3"
    elif args.forbid_K4:
        forbid_n, forbid_edges = 4, _K4_EDGES
        forbid_tag = "K4"
        forbid_filename_tag = "K4"
    else:
        forbid_n, forbid_edges = parse_flagmatic_notation(args.forbid)
        forbid_tag = args.forbid                         # e.g. "3:122331"
        forbid_filename_tag = notation_to_filename(args.forbid)  # e.g. "3_122331"

    input_path = Path(args.input_path)
    n_hint = infer_n_from_filename(input_path)
    script_dir = Path(__file__).resolve().parent
    output_path = (
        Path(args.output)
        if args.output
        else script_dir / f"{input_path.stem}_{forbid_filename_tag}_free_indices.json"
    )

    with input_path.open("r", encoding="utf-8") as f:
        graphs = json.load(f)

    free_indices = collect_free_indices(graphs, forbid_edges, forbid_n, n_hint=n_hint)

    graph_n = n_hint if n_hint is not None else "unknown"
    result = {
        "n": graph_n,
        "forbid": {
            "tag": forbid_tag,
            "n": forbid_n,
            "edges": [list(e) for e in forbid_edges],
        },
        "total_graphs": len(graphs),
        "free_graph_indices": free_indices,
    }

    with output_path.open("w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)

    print(f"Forbidden graph: {forbid_tag} (n={forbid_n}, edges={list(forbid_edges)})")
    print(f"Total graphs: {len(graphs)}")
    print(f"Free graphs: {len(free_indices)}")
    print(f"Saved result to: {output_path}")


if __name__ == "__main__":
    main()
