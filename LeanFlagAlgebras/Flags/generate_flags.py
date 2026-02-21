import json
import itertools
import os


def get_canonical_flag(edges, n, k):
    """
    Fixes the type vertices (0 to k-1) and permutes only the remaining
    non-type vertices (k to n-1) to return the lexicographically
    smallest (canonical) edge list representation.
    """
    non_type_vertices = list(range(k, n))
    best_edges = None

    # Iterate through all permutations of the non-type vertices
    for p in itertools.permutations(non_type_vertices):
        # Create a mapping: type vertices map to themselves
        mapping = {v: v for v in range(k)}
        for idx, v in enumerate(non_type_vertices):
            mapping[v] = p[idx]

        # Generate the new edge list based on the current permutation
        new_edges = []
        for u, v in edges:
            nu, nv = mapping[u], mapping[v]
            # Ensure each edge is represented as (smaller, larger)
            if nu > nv:
                nu, nv = nv, nu
            new_edges.append((nu, nv))

        # Sort the edges to compare them lexicographically
        new_edges.sort()
        new_edges_tuple = tuple(new_edges)

        # Keep track of the lexicographically smallest edge list
        if best_edges is None or new_edges_tuple < best_edges:
            best_edges = new_edges_tuple

    return best_edges


def generate_flags_with_type(n, k, type_index):
    """
    Generates all non-isomorphic n-vertex flags for a given type of size k,
    and saves the results along with the type's structural information into a JSON file.

    Args:
        n (int): Total number of vertices in the flag.
        k (int): Number of vertices in the base type.
        type_index (int): The index of the graph in type_{k}.json to be used as the type.
    """
    if n < k:
        raise ValueError(
            "The number of vertices 'n' in the flag must be greater than or equal to 'k'."
        )

    type_filename = f"LeanFlagAlgebras/Flags/Types/types_{k}.json"
    if not os.path.exists(type_filename):
        raise FileNotFoundError(f"The file {type_filename} does not exist.")

    # Load the base graphs for the type
    with open(type_filename, "r", encoding="utf-8") as f:
        types = json.load(f)

    if type_index >= len(types):
        raise IndexError(f"Index {type_index} is out of bounds for {type_filename}.")

    sigma_edges = types[type_index]
    sigma_edges_tuples = [tuple(e) for e in sigma_edges]

    type_vertices = list(range(k))
    non_type_vertices = list(range(k, n))
    potential_edges = []

    # 1. Potential edges between type vertices and non-type vertices
    for u in type_vertices:
        for v in non_type_vertices:
            potential_edges.append((u, v))

    # 2. Potential edges strictly among non-type vertices
    for u, v in itertools.combinations(non_type_vertices, 2):
        potential_edges.append((u, v))

    unique_flags = set()

    # Generate the power set of all potential edges
    for r in range(len(potential_edges) + 1):
        for new_edges in itertools.combinations(potential_edges, r):
            # Combine the type's edges with the newly selected edges
            current_edges = sigma_edges_tuples + list(new_edges)

            # Find the canonical representation to filter out isomorphic flags
            canonical_edges = get_canonical_flag(current_edges, n, k)
            unique_flags.add(canonical_edges)

    # Sort the unique flags: first by number of edges, then lexicographically
    sorted_flags = sorted(list(unique_flags), key=lambda x: (len(x), x))
    flags_list = [list(edges) for edges in sorted_flags]

    # [Modified] Construct a dictionary containing n, k, and type information
    # This structure allows Lean to easily read and reconstruct the type graph.
    output_data = {
        "n": n,
        "k": k,
        "type_index": type_index,
        "type_edges": sigma_edges,  # Used by Lean to create the Type graph
        "flags": flags_list,
    }

    # Save to JSON
    output_filename = f"LeanFlagAlgebras/Flags/Flags/flags_{n}_{k}_{type_index}.json"
    with open(output_filename, "w", encoding="utf-8") as f:
        json.dump(output_data, f, indent=2)

    print(
        f"[{output_filename}] Saved successfully: Contains type info and {len(flags_list)} non-isomorphic flags."
    )


if __name__ == "__main__":
    # Example usage:
    generate_flags_with_type(n=5, k=3, type_index=1)
