import LeanFlagAlgebras.Flags.FlagLoader

/-! # Flag data instantiation

This module is the entry point of the Flags data pipeline on the Lean side: it
invokes the loader macros (`load_empty_typed_flags` / `load_flags`, defined in
`FlagLoader.lean`) on the precomputed JSON files produced by the Python scripts
(`generate_graphs.py` → `Graphs/*.json`, `generate_flags.py` → `Flags/*.json`).

Each `load_*` line reads one JSON file at elaboration time and synthesizes the
corresponding named Lean constants/theorems. Generated names use the
`_<n>_<k>_<m>_<i>` suffix convention: `n` vertices; `k`,`m` describe the type σ
(`0_0` denotes the empty type ∅ₜ); `i` is the enumeration index within the file.

The `#print`/`#check` lines at the end sanity-check that representative
generated declarations exist.
-/

load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_0.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_1.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_2.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_3.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_4.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_5.json"

load_flags "LeanFlagAlgebras/Flags/Flags/flags_1_1_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_2_1_0.json"

load_flags "LeanFlagAlgebras/Flags/Flags/flags_3_1_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_3_2_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_3_2_1.json"

load_flags "LeanFlagAlgebras/Flags/Flags/flags_4_2_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_4_2_1.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_4_3_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_4_3_1.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_4_3_2.json"

load_flags "LeanFlagAlgebras/Flags/Flags/flags_5_3_0.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_5_3_1.json"
load_flags "LeanFlagAlgebras/Flags/Flags/flags_5_3_2.json"

#print Sym2LabeledGraph_3_1_0_2
#check downward_3_1_0_2
#check flagSet_3_0_0_eq_univ
#check flagSet_3_1_0_val_eq
