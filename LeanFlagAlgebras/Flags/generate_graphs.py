"""Enumerate all non-isomorphic graphs on ``n`` vertices as canonical JSON.

Uses NetworkX's graph atlas (supported for ``n <= 7``) to list every
non-isomorphic ``n``-vertex graph, computes a canonical (lexicographically
smallest) edge list for each, and writes them sorted to
``LeanFlagAlgebras/Flags/Graphs/graphs_<n>.json`` as a top-level array of edge
lists.

This file is consumed on the Lean side by the ``load_empty_typed_flags`` macro
in ``FlagLoader.lean`` (invoked from ``Flags/FlagDef.lean``), and also serves
as the type/underlying-graph source for ``generate_flags.py``.

Run via ``python generate_graphs.py`` (the ``n`` is hard-coded in the
``__main__`` block; edit the ``generate_graphs_json`` argument to change it).
"""

import networkx as nx
import json
import itertools

ATLAS = nx.graph_atlas_g()

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

def generate_graphs_json(n):
    """Write the canonical edge lists of all n-vertex graphs to graphs_<n>.json."""
    if n > 7:
        raise ValueError("Not supported for n > 7 due to performance")

    graph_data = []
    
    count = 0
    for G in ATLAS:
        if len(G) == n:
            # Get the cleanest edge representation
            canonical_edges = get_canonical_edges(G)
            graph_data.append(canonical_edges)
            count += 1

    # Sort the whole list of graphs to ensure the file order is also deterministic
    # (Optional: ATLAS is usually already sorted by edge count, but this ensures strict order)
    graph_data.sort(key=lambda x: (len(x), x))

    filename=f"LeanFlagAlgebras/Flags/Graphs/graphs_{n}.json"
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(graph_data, f, indent=2)
    
    print(f"Saved {count} canonical graphs to '{filename}'")

if __name__ == "__main__":
    generate_graphs_json(0)