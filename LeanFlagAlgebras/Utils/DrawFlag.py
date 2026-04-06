"""Draw a flag graph from flag JSON files.

Requirements:
	- Install plotting library: pip install matplotlib

Input format:
	- You can pass either Flag_n_k_typeNum_flagIndex or n_k_typeNum_flagIndex.
	- Example: Flag_3_0_0_1 or 3_0_0_1
"""

from __future__ import annotations

import json
import math
import re
import sys
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


FLAG_NAME_PATTERN = re.compile(r"^(?:Flag_)?(\d+)_(\d+)_(\d+)_(\d+)$", re.IGNORECASE)


def parse_flag_name(flag_name: str) -> Tuple[int, int, int, int]:
	"""Parse a name like Flag_3_0_0_1 into (n, k, type_num, flag_index)."""
	m = FLAG_NAME_PATTERN.fullmatch(flag_name.strip())
	if m is None:
		raise ValueError(
			"Invalid flag name format. Expected Flag_n_k_typeNum_flagIndex, "
			"for example: Flag_3_0_0_1"
		)
	return tuple(int(x) for x in m.groups())  # type: ignore[return-value]


def get_flags_json_path(n: int, k: int, type_num: int) -> Path:
	base_dir = Path(__file__).resolve().parents[1] / "Flags" / "Flags"
	return base_dir / f"flags_{n}_{k}_{type_num}.json"


def load_flag_data(n: int, k: int, type_num: int, flag_index: int) -> Tuple[Dict, Dict]:
	json_path = get_flags_json_path(n, k, type_num)
	if not json_path.exists():
		raise FileNotFoundError(f"Flag data file not found: {json_path}")

	with json_path.open("r", encoding="utf-8") as f:
		data = json.load(f)

	flags: List[Dict] = data.get("flags", [])
	if not (0 <= flag_index < len(flags)):
		raise IndexError(
			f"Flag index out of range: {flag_index}. "
			f"Valid range is 0..{max(len(flags) - 1, 0)}"
		)

	return data, flags[flag_index]


def circular_layout(n: int, radius: float = 1.0) -> Dict[int, Tuple[float, float]]:
	"""Return node positions on a circle."""
	positions: Dict[int, Tuple[float, float]] = {}
	for i in range(n):
		angle = (2.0 * math.pi * i) / n
		positions[i] = (radius * math.cos(angle), radius * math.sin(angle))
	return positions


def type_edges_in_graph(type_edges: Sequence[Sequence[int]], type_indices: Sequence[int]) -> set[Tuple[int, int]]:
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
) -> None:
	try:
		import matplotlib.pyplot as plt
	except ImportError as ex:
		raise ImportError(
			"matplotlib is required to draw graphs. Install it with: pip install matplotlib"
		) from ex

	edges: List[List[int]] = flag.get("edges", [])
	type_indices: List[int] = flag.get("type_indices", [])
	root_type_edges: List[List[int]] = data.get("type_edges", [])

	pos = circular_layout(n)

	fig, ax = plt.subplots(figsize=(5.2, 5.2))
	ax.set_aspect("equal", "box")
	ax.axis("off")

	type_edge_set = type_edges_in_graph(root_type_edges, type_indices) if k > 0 else set()

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
			str(node),
			ha="center",
			va="center",
			fontsize=12,
			fontweight="bold",
			color="#111827",
			zorder=3,
		)

	title = f"Flag_{n}_{k}_{type_num}_{flag_index}"
	ax.set_title(title, fontsize=12, pad=16)

	# Legend proxies to explain the color coding.
	type_proxy = plt.Line2D([0], [0], marker="o", color="w", label="Type vertex", markerfacecolor="#ffffff", markeredgecolor="#d62828", markeredgewidth=1.9, markersize=8)
	other_proxy = plt.Line2D([0], [0], marker="o", color="w", label="Other vertex", markerfacecolor="#ffffff", markeredgecolor="#111827", markeredgewidth=1.7, markersize=8)
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
	plt.show()


if len(sys.argv) != 2:
	print("Usage: python DrawFlag.py Flag_n_k_typeNum_flagIndex")
	print("Example: python DrawFlag.py Flag_3_0_0_1")
	raise SystemExit(1)

flag_name = sys.argv[1]
try:
	n, k, type_num, flag_index = parse_flag_name(flag_name)
	data, flag = load_flag_data(n, k, type_num, flag_index)

	json_path = get_flags_json_path(n, k, type_num)
	# print(f"Flag name           : Flag_{n}_{k}_{type_num}_{flag_index}")
	# print(f"JSON path           : {json_path}")
	# print(f"Underlying graph #  : {flag.get('underlying_graph_num')}")
	# print(f"Type indices        : {flag.get('type_indices', [])}")
	# print(f"Type edges (local)  : {data.get('type_edges', [])}")
	# print(f"Edges               : {flag.get('edges', [])}")
	# print(f"Downward coeff      : {flag.get('downward_coeff')}")
	draw_flag(n, k, type_num, flag_index, data, flag)
except Exception as ex:
	print(f"Error: {ex}")
	raise SystemExit(2)
