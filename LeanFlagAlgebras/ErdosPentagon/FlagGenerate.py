import networkx as nx
import json
import os

# Load the graph atlas from NetworkX
ATLAS = nx.graph_atlas_g()


def generate_graph_json(n):
    """
    Extracts all graphs with 'n' vertices from the graph atlas,
    relabels nodes to 0..n-1, and saves the edge lists to a JSON file.

    Args:
        n (int): Number of vertices (must be <= 7).
        filename (str): Output filename.
    """
    if n > 7:
        raise ValueError("Graph atlas only supports n <= 7")

    graph_data = []

    # Iterate through the atlas to find graphs with size n
    for G in ATLAS:
        if len(G) == n:
            # 1. Relabel nodes to standard integers 0 to n-1
            #    This is crucial for mapping to Lean's `Fin n` type.
            mapping = {
                old_label: new_label for new_label, old_label in enumerate(G.nodes())
            }
            H = nx.relabel_nodes(G, mapping)

            # 2. Extract edges as a list of tuples (u, v)
            edges = list(H.edges())
            graph_data.append(edges)

    # 3. Save the list of edge lists to a JSON file
    filename = f"graphs_{n}.json"
    with open(filename, "w", encoding="utf-8") as f:
        json.dump(graph_data, f, indent=2)

    print(f"Successfully saved {len(graph_data)} graphs with n={n} to '{filename}'.")


if __name__ == "__main__":
    # Generate data for n=5
    generate_graph_json(5)
