"""Enumerate flags of a given type and emit them as enriched JSON.

Given a total size ``n``, a type size ``k``, and a type index ``type_num``,
this script reads the precomputed non-isomorphic graphs from
``Graphs/graphs_k.json`` (the type sigma) and ``Graphs/graphs_n.json`` (the
candidate underlying graphs). For each ``n``-vertex graph it finds all
embeddings of the type, groups them into automorphism orbits, and emits one
flag per orbit together with its ``downward_coeff`` (orbit size divided by the
number of injections of the ``k`` labels into ``n`` vertices).

Output: ``Flags/flags_<n>_<k>_<type_num>.json`` with fields ``n``, ``k``,
``type_num``, ``type_edges``, and ``flags`` (each having
``underlying_graph_num``, ``edges``, ``type_indices``, ``downward_coeff``).
This file is consumed on the Lean side by the ``load_flags`` macro in
``FlagLoader.lean`` (invoked from ``Flags/FlagDef.lean``), which synthesizes
the ``Sym2Flag_n_k_m_i`` / ``Flag_n_k_m_i`` / ``downward_n_k_m_i`` constants.

Example:
    python generate_flags.py 4 2 0
"""

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple


Edge = Tuple[int, int]
Embedding = Tuple[int, ...]


def normalize_edges(edges: Iterable[Sequence[int]]) -> Tuple[Edge, ...]:
	"""Return edges as a sorted tuple of (u, v) pairs with u < v; reject loops."""
	normalized: List[Edge] = []
	for u_raw, v_raw in edges:
		u = int(u_raw)
		v = int(v_raw)
		if u == v:
			raise ValueError(f"Self-loop ({u}, {v}) is not allowed.")
		if u > v:
			u, v = v, u
		normalized.append((u, v))
	normalized.sort()
	return tuple(normalized)


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


def induced_edges_on_embedding(graph_edges_set: Set[Edge], embedding: Embedding) -> Tuple[Edge, ...]:
	"""Return the subgraph induced on ``embedding``, re-indexed to 0..k-1."""
	k = len(embedding)
	induced: List[Edge] = []
	for i in range(k):
		for j in range(i + 1, k):
			a = embedding[i]
			b = embedding[j]
			edge = (a, b) if a < b else (b, a)
			if edge in graph_edges_set:
				induced.append((i, j))
	induced.sort()
	return tuple(induced)


def find_automorphisms(edges: Tuple[Edge, ...], n: int) -> List[Tuple[int, ...]]:
	"""Return all vertex permutations that fix the graph (its automorphisms)."""
	automorphisms: List[Tuple[int, ...]] = []
	for perm in itertools.permutations(range(n)):
		if relabel_edges(edges, perm) == edges:
			automorphisms.append(tuple(perm))
	return automorphisms


def find_valid_embeddings(
	graph_edges: Tuple[Edge, ...], sigma_edges: Tuple[Edge, ...], n: int, k: int
) -> Set[Embedding]:
	"""Return all k-vertex orderings whose induced subgraph equals the type."""
	graph_edges_set = set(graph_edges)
	valid: Set[Embedding] = set()
	for emb in itertools.permutations(range(n), k):
		if induced_edges_on_embedding(graph_edges_set, emb) == sigma_edges:
			valid.add(tuple(emb))
	return valid


def orbit_of_embedding(
	embedding: Embedding, automorphisms: Sequence[Tuple[int, ...]], valid_embeddings: Set[Embedding]
) -> Set[Embedding]:
	"""Return the orbit of ``embedding`` under the graph's automorphism group."""
	orbit: Set[Embedding] = set()
	for perm in automorphisms:
		moved = tuple(perm[v] for v in embedding)
		if moved in valid_embeddings:
			orbit.add(moved)
	return orbit


def to_fraction_string(value: Fraction) -> str:
	"""Format a Fraction as ``"num"`` or ``"num/den"``."""
	if value.denominator == 1:
		return str(value.numerator)
	return f"{value.numerator}/{value.denominator}"


def generate_flag_json(n: int, k: int, type_num: int) -> Dict:
	"""Build the flag JSON for type ``graphs_k[type_num]`` over ``n`` vertices.

	One flag is emitted per automorphism orbit of valid type embeddings, with
	its downward coefficient = orbit size / (number of label injections).
	"""
	if n < k:
		raise ValueError("n must be greater than or equal to k.")

	base_dir = Path(__file__).resolve().parent
	types_dir = base_dir / "Graphs"
	flags_dir = base_dir / "Flags"
	flags_dir.mkdir(parents=True, exist_ok=True)

	type_k_file = types_dir / f"graphs_{k}.json"
	type_n_file = types_dir / f"graphs_{n}.json"

	if not type_k_file.exists():
		raise FileNotFoundError(f"Missing file: {type_k_file}")
	if not type_n_file.exists():
		raise FileNotFoundError(f"Missing file: {type_n_file}")

	with type_k_file.open("r", encoding="utf-8") as f:
		types_k_raw = json.load(f)
	with type_n_file.open("r", encoding="utf-8") as f:
		types_n_raw = json.load(f)

	if type_num < 0 or type_num >= len(types_k_raw):
		raise IndexError(f"type_num={type_num} out of range for {type_k_file.name}")

	sigma_edges = normalize_edges(types_k_raw[type_num])
	all_n_graphs = [normalize_edges(g_edges) for g_edges in types_n_raw]

	all_injections = Fraction(1, 1)
	for t in range(k):
		all_injections *= (n - t)

	flags: List[Dict] = []

	for underlying_graph_num, graph_edges in enumerate(all_n_graphs):
		valid_embeddings = find_valid_embeddings(graph_edges, sigma_edges, n, k)
		if not valid_embeddings:
			continue

		automorphisms = find_automorphisms(graph_edges, n)

		remaining = set(valid_embeddings)
		while remaining:
			seed = min(remaining)
			orbit = orbit_of_embedding(seed, automorphisms, valid_embeddings)
			if not orbit:
				orbit = {seed}

			representative = min(orbit)
			coeff = Fraction(len(orbit), 1) / all_injections

			flags.append(
				{
					"underlying_graph_num": underlying_graph_num,
					"edges": [list(e) for e in graph_edges],
					"type_indices": list(representative),
					"downward_coeff": to_fraction_string(coeff),
				}
			)

			remaining.difference_update(orbit)

	flags.sort(key=lambda x: (x["underlying_graph_num"], x["type_indices"]))

	return {
		"n": n,
		"k": k,
		"type_num": type_num,
		"type_edges": [list(e) for e in sigma_edges],
		"flags": flags,
	}


def main() -> None:
	"""CLI: parse n, k, type_num and write Flags/flags_<n>_<k>_<type_num>.json."""
	parser = argparse.ArgumentParser(
		description="Generate enriched flag JSON from Graphs/graphs_k.json and Graphs/graphs_n.json"
	)
	parser.add_argument("n", type=int, help="Total number of vertices")
	parser.add_argument("k", type=int, help="Type size (number of labeled vertices)")
	parser.add_argument("type_num", type=int, help="Index in Graphs/graphs_k.json")
	args = parser.parse_args()

	output = generate_flag_json(args.n, args.k, args.type_num)

	out_path = Path(__file__).resolve().parent / "Flags" / f"flags_{args.n}_{args.k}_{args.type_num}.json"
	with out_path.open("w", encoding="utf-8") as f:
		json.dump(output, f, indent=2)

	print(f"Saved {len(output['flags'])} flags to {out_path}")


if __name__ == "__main__":
	main()
