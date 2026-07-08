"""Draw a flag graph (JSON-free, in-memory enumeration).

An earlier version of this script loaded ``Flags/Flags/flags_<n>_<k>_<type_num>.json``.
The migrated pipeline no longer writes those files: the canonical flag data is
computed in-memory by ``Flagmatic/flag_enumeration.py`` (which in turn uses
``Flagmatic/graph_enumeration.py``), exactly the way ``Flagmatic/flagmatic_to_lean.py``
resolves flag indices. This script does the same — it puts the ``Flagmatic/``
directory on ``sys.path``, imports the enumeration in-process, and calls
``canonical_flags(n, k, type_num)`` to get the same dict shape the JSON had
(keys ``n``, ``k``, ``type_num``, ``type_edges``, ``flags``). No JSON on disk.

Because ``canonical_flags`` reproduces the Lean ``genFlagData`` order, the
``flagIndex`` here is the exact index in the generated ``FlagAlgebra_n_k_m_i``
constants — the same index ``flagmatic_to_lean.py`` prints.

Requirements:
    - pip install matplotlib networkx

Input format:
    - Pass either ``Flag_n_k_typeNum_flagIndex`` or ``n_k_typeNum_flagIndex``.
    - Example: ``Flag_3_0_0_1`` or ``3_0_0_1``.
    - For unlabeled graphs use ``k = typeNum = 0`` (then flagIndex is the
      canonical graph index): ``Flag_4_0_0_3``.

Usage:
    python DrawFlag.py Flag_3_1_0_2
    python DrawFlag.py Flag_3_1_0_2 out.png   # save instead of showing
"""

from __future__ import annotations

import math
import re
import sys
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


FLAG_NAME_PATTERN = re.compile(r"^(?:Flag_)?(\d+)_(\d+)_(\d+)_(\d+)$", re.IGNORECASE)


# The canonical enumeration lives in the sibling ``Flagmatic/`` directory. Put it
# on ``sys.path`` and import it in-process — the same trick ``flagmatic_to_lean.py``
# uses so index lookups need no JSON. ``flag_enumeration`` imports ``graph_enumeration``
# by bare name, so that directory must be importable.
_FLAGMATIC_DIR = Path(__file__).resolve().parents[1] / "Flagmatic"
if str(_FLAGMATIC_DIR) not in sys.path:
    sys.path.insert(0, str(_FLAGMATIC_DIR))


def parse_flag_name(flag_name: str) -> Tuple[int, int, int, int]:
    """Parse a name like Flag_3_0_0_1 into (n, k, type_num, flag_index)."""
    m = FLAG_NAME_PATTERN.fullmatch(flag_name.strip())
    if m is None:
        raise ValueError(
            "Invalid flag name format. Expected Flag_n_k_typeNum_flagIndex, "
            "for example: Flag_3_0_0_1"
        )
    return tuple(int(x) for x in m.groups())  # type: ignore[return-value]


def load_flag_data(n: int, k: int, type_num: int, flag_index: int) -> Tuple[Dict, Dict]:
    """Compute the flag data in-memory and return (full_data, selected_flag).

    Args:
        n, k, type_num: Identify which type/size the flags live over.
        flag_index: Index of the flag within the computed "flags" list.

    Returns the canonical top-level dict (containing e.g. "type_edges", the same
    shape the old ``flags_*.json`` had) and the single flag dict at flag_index.
    Raises whatever ``canonical_flags`` raises (e.g. IndexError for a bad
    ``type_num``) and IndexError if ``flag_index`` is out of range.
    """
    import flag_enumeration  # imported lazily so import errors surface with a clear message

    data = flag_enumeration.canonical_flags(n, k, type_num)

    flags: List[Dict] = data.get("flags", [])
    if not (0 <= flag_index < len(flags)):
        raise IndexError(
            f"Flag index out of range: {flag_index}. "
            f"Valid range is 0..{max(len(flags) - 1, 0)} "
            f"({len(flags)} flag(s) for type graphs_{k}[{type_num}] over {n} vertices)"
        )

    return data, flags[flag_index]


def circular_layout(n: int, radius: float = 1.0) -> Dict[int, Tuple[float, float]]:
    """Return node positions on a circle."""
    positions: Dict[int, Tuple[float, float]] = {}
    for i in range(n):
        angle = (2.0 * math.pi * i) / n
        positions[i] = (radius * math.cos(angle), radius * math.sin(angle))
    return positions


def type_edges_in_graph(
    type_edges: Sequence[Sequence[int]], type_indices: Sequence[int]
) -> set[Tuple[int, int]]:
    """Map type edges (local indices) into graph vertex indices."""
    mapped: set[Tuple[int, int]] = set()
    for a_local, b_local in type_edges:
        a = type_indices[a_local]
        b = type_indices[b_local]
        mapped.add((min(a, b), max(a, b)))
    return mapped


def draw_flag(
    n: int,
    k: int,
    type_num: int,
    flag_index: int,
    data: Dict,
    flag: Dict,
    save_path: str | None = None,
) -> None:
    """Render the flag as a matplotlib figure on a circular node layout.

    Vertices are labeled in flag-canonical order: the ``k`` type vertices come
    first, labeled ``0, 1, …, k-1`` by their position in the type's label order
    and drawn in red; the remaining (unlabeled) vertices continue ``k, k+1, …``
    in ascending graph-index order, drawn in black. This keeps every label
    unique while giving the type vertices the clean ``0,1,2,…`` numbering. Type
    edges (those induced by the root type) are red, other edges black. If
    ``save_path`` is given the figure is written there; otherwise an interactive
    window is opened via ``plt.show()``. Requires matplotlib.
    """
    try:
        import matplotlib
        if save_path is not None:
            matplotlib.use("Agg")  # headless backend when we only save to a file
        import matplotlib.pyplot as plt
    except ImportError as ex:
        raise ImportError(
            "matplotlib is required to draw graphs. Install it with: pip install matplotlib"
        ) from ex

    edges: List[List[int]] = flag.get("edges", [])
    type_indices: List[int] = flag.get("type_indices", [])
    root_type_edges: List[List[int]] = data.get("type_edges", [])
    type_order_by_vertex = {vertex: i for i, vertex in enumerate(type_indices)}

    pos = circular_layout(n)

    fig, ax = plt.subplots(figsize=(5.2, 5.2))
    ax.set_aspect("equal", "box")
    ax.axis("off")

    type_edge_set = type_edges_in_graph(root_type_edges, type_indices) if k > 0 else set()

    # Flag-canonical display labels: type vertices get 0..k-1 by type order, the
    # rest continue k, k+1, ... in ascending graph-index order. Unique labels, and
    # the type vertices are numbered 0,1,2,... regardless of their graph index.
    display_label: Dict[int, int] = {}
    for node, type_order in type_order_by_vertex.items():
        display_label[node] = type_order
    next_label = len(type_indices)
    for node in range(n):
        if node not in display_label:
            display_label[node] = next_label
            next_label += 1

    for u, v in edges:
        (x1, y1), (x2, y2) = pos[u], pos[v]
        edge_key = (min(u, v), max(u, v))
        is_type_edge = edge_key in type_edge_set
        ax.plot(
            [x1, x2],
            [y1, y2],
            color=("#d62828" if is_type_edge else "#111827"),
            linewidth=(2.2 if is_type_edge else 1.8),
            zorder=1,
        )

    for node in range(n):
        x, y = pos[node]
        is_type_vertex = node in type_indices
        label_text = str(display_label[node])
        label_color = "#d62828" if is_type_vertex else "#111827"
        ax.scatter(
            [x],
            [y],
            s=320,
            c="#ffffff",
            edgecolors=("#d62828" if is_type_vertex else "#111827"),
            linewidths=(2.2 if is_type_vertex else 1.8),
            zorder=2,
        )
        ax.text(
            x,
            y,
            label_text,
            ha="center",
            va="center",
            fontsize=11,
            fontweight="bold",
            color=label_color,
            zorder=3,
        )

    title = f"Flag_{n}_{k}_{type_num}_{flag_index}"
    ax.set_title(title, fontsize=12, pad=16)

    # Legend proxies to explain the color coding.
    type_proxy = plt.Line2D([0], [0], marker="o", color="w", label="Type vertex (labeled 0..k-1 by type order)", markerfacecolor="#ffffff", markeredgecolor="#d62828", markeredgewidth=1.9, markersize=8)
    other_proxy = plt.Line2D([0], [0], marker="o", color="w", label="Other vertex (labeled k, k+1, ...)", markerfacecolor="#ffffff", markeredgecolor="#111827", markeredgewidth=1.7, markersize=8)
    type_edge_proxy = plt.Line2D([0], [0], color="#d62828", lw=2.2, label="Type edge")
    other_edge_proxy = plt.Line2D([0], [0], color="#111827", lw=1.8, label="Other edge")
    ax.legend(
        handles=[type_proxy, other_proxy, type_edge_proxy, other_edge_proxy],
        loc="upper center",
        bbox_to_anchor=(0.5, -0.04),
        ncol=2,
        frameon=True,
        facecolor="#ffffff",
        edgecolor="#d1d5db",
        fontsize=8.5,
        borderaxespad=0.25,
        handlelength=1.8,
        columnspacing=1.0,
    )

    plt.tight_layout(rect=(0.0, 0.07, 1.0, 1.0))
    if save_path is not None:
        fig.savefig(save_path, dpi=150, bbox_inches="tight")
        plt.close(fig)
        print(f"Saved figure to {save_path}")
    else:
        plt.show()


def main(argv: List[str]) -> int:
    if not (2 <= len(argv) <= 3):
        print("Usage: python DrawFlag.py Flag_n_k_typeNum_flagIndex [out.png]")
        print("Example: python DrawFlag.py Flag_3_1_0_2")
        return 1

    flag_name = argv[1]
    save_path = argv[2] if len(argv) == 3 else None
    try:
        n, k, type_num, flag_index = parse_flag_name(flag_name)
        data, flag = load_flag_data(n, k, type_num, flag_index)
        draw_flag(n, k, type_num, flag_index, data, flag, save_path=save_path)
    except Exception as ex:  # noqa: BLE001 — surface any failure as a clean CLI error
        print(f"Error: {ex}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
