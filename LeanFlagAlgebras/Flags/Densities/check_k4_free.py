import argparse
import itertools
import json
import re
from pathlib import Path


def infer_n_from_filename(path: Path) -> int | None:
    match = re.search(r"graphs_(\d+)\.json$", path.name)
    if match:
        return int(match.group(1))
    return None


def has_k4(edges: list[list[int]], n_hint: int | None = None) -> bool:
    if len(edges) < 6:
        return False

    edge_set = {tuple(sorted((u, v))) for u, v in edges}

    if n_hint is not None:
        n = n_hint
    elif edge_set:
        n = max(max(u, v) for u, v in edge_set) + 1
    else:
        n = 0

    if n < 4:
        return False

    for a, b, c, d in itertools.combinations(range(n), 4):
        if (
            (a, b) in edge_set
            and (a, c) in edge_set
            and (a, d) in edge_set
            and (b, c) in edge_set
            and (b, d) in edge_set
            and (c, d) in edge_set
        ):
            return True
    return False


def collect_k4_free_indices(
    graphs: list[list[list[int]]], n_hint: int | None
) -> list[int]:
    indices = []
    for idx, edges in enumerate(graphs):
        if not has_k4(edges, n_hint=n_hint):
            indices.append(idx)
    return indices


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Read graphs_n.json and write a JSON file containing the total number "
            "of graphs and indices of K4-free graphs."
        )
    )
    parser.add_argument("input_path", help="Path to input graphs JSON file")
    parser.add_argument(
        "-o",
        "--output",
        default=None,
        help=(
            "Output JSON path "
            "(default: this script directory/<input_stem>_k4_free_indices.json)"
        ),
    )
    args = parser.parse_args()

    input_path = Path(args.input_path)
    script_dir = Path(__file__).resolve().parent
    output_path = (
        Path(args.output)
        if args.output
        else script_dir / f"{input_path.stem}_k4_free_indices.json"
    )

    with input_path.open("r", encoding="utf-8") as f:
        graphs = json.load(f)

    n_hint = infer_n_from_filename(input_path)
    k4_free_indices = collect_k4_free_indices(graphs, n_hint=n_hint)

    result = {
        "input_file": str(input_path),
        "total_graphs": len(graphs),
        "k4_free_graph_indices": k4_free_indices,
    }

    with output_path.open("w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)

    print(f"Saved result to: {output_path}")
    print(f"Total graphs: {len(graphs)}")
    print(f"K4-free graphs: {len(k4_free_indices)}")


if __name__ == "__main__":
    main()
