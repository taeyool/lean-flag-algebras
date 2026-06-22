"""Canonical non-isomorphic graph enumeration, for the Flagmatic-to-Lean automation.

Uses NetworkX's graph atlas (supported for ``n <= 7``) to list every
non-isomorphic ``n``-vertex graph and computes a canonical (lexicographically
smallest) edge list for each. :func:`canonical_graphs` returns them sorted by
``(edge count, edge list)`` — the same order the Lean ``genSym2Graphs`` generator
reproduces, so list position is the canonical graph index used in identifier
names. This is the in-memory enumeration imported by ``flagmatic_to_lean.py``
(and by ``flag_enumeration.py``); it reads no JSON.

The legacy ``generate_graphs_json`` / CLI still *write*
``LeanFlagAlgebras/Flags/Graphs/graphs_<n>.json``, kept for the old loaders; the
active Lean build no longer consumes them.

Run the legacy JSON dump via ``python graph_enumeration.py`` (the ``n`` is
hard-coded in the ``__main__`` block).
"""

import networkx as nx
import json
import itertools

_ATLAS = None


def _atlas():
    """Lazily build (and cache) the NetworkX graph atlas.

    Building the atlas is slow, so we defer it until first use — this keeps
    ``import generate_graphs`` cheap for callers (e.g. the Flagmatic automation)
    that only need a few small ``n`` on demand.
    """
    global _ATLAS
    if _ATLAS is None:
        _ATLAS = nx.graph_atlas_g()
    return _ATLAS


def get_canonical_edges(G):
    """
    Finds the lexicographically smallest edge list representation for graph G.
    It tries all permutations of node labels to find the 'cleanest' version.
    
    Args:
        G: A networkx Graph
    Returns:
        A sorted list of edges (e.g., [[0, 1], [2, 3]])
    """
    n = len(G)
    nodes = range(n)
    
    # 1. Relabel nodes to 0..n-1 initially to ensure we have standard integers
    mapping_init = {node: i for i, node in enumerate(G.nodes())}
    G_int = nx.relabel_nodes(G, mapping_init)
    
    best_edges = None

    # 2. Try all permutations of node labels (0 to n-1)
    #    For n=5, 5! = 120 iterations (very fast)
    for perm in itertools.permutations(nodes):
        # Create a mapping from current label -> new label based on permutation
        mapping = {i: perm[i] for i in nodes}
        
        # Apply mapping
        H = nx.relabel_nodes(G_int, mapping)
        
        # Extract edges:
        # - Each edge (u, v) is sorted so u < v
        # - The list of edges is sorted lexicographically
        edges = []
        for u, v in H.edges():
            if u > v:
                u, v = v, u
            edges.append([u, v])
        edges.sort()
        
        # Compare with the best found so far
        # Python lists compare lexicographically by default:
        # [[0, 1]] < [[3, 4]] is True
        if best_edges is None or edges < best_edges:
            best_edges = edges
            
    return best_edges

def canonical_graphs(n):
    """All non-isomorphic ``n``-vertex graphs as canonical edge lists, in the
    file order used by ``graphs_<n>.json`` (sorted by ``(edge count, edge list)``).

    This is the in-memory core shared with :func:`generate_graphs_json` (which
    writes the same data to disk) and imported by the Flagmatic automation so it
    can resolve flag indices without reading any JSON. Because the Lean
    ``genSym2Graphs`` enumeration reproduces this exact order, indices computed
    here agree with the generated ``FlagAlgebra_n_0_0_i`` constants.
    """
    if n > 7:
        raise ValueError("Not supported for n > 7 due to performance")

    # Each edge as an ordered [min, max] pair; graphs sorted by (len, edge list)
    # so the order is deterministic (and matches the Lean / JSON ordering).
    graph_data = [get_canonical_edges(G) for G in _atlas() if len(G) == n]
    graph_data.sort(key=lambda x: (len(x), x))
    return graph_data


def generate_graphs_json(n):
    """Write the canonical edge lists of all n-vertex graphs to the legacy
    ``LeanFlagAlgebras/Flags/Graphs/graphs_<n>.json`` (no longer consumed by the
    active Lean build; kept for the old loaders)."""
    graph_data = canonical_graphs(n)

    # Repo-root-relative so the legacy JSON still lands in Flags/Graphs/ regardless
    # of where this module now lives (Flagmatic/) or the current working directory.
    from pathlib import Path
    repo_root = Path(__file__).resolve().parents[2]
    out_dir = repo_root / "LeanFlagAlgebras" / "Flags" / "Graphs"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"graphs_{n}.json"
    with out_path.open('w', encoding='utf-8') as f:
        json.dump(graph_data, f, indent=2)

    print(f"Saved {len(graph_data)} canonical graphs to '{out_path}'")

if __name__ == "__main__":
    generate_graphs_json(0)