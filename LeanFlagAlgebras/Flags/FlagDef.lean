import LeanFlagAlgebras.Flags.FlagLoader

/-! # Flag data instantiation

This module is the entry point of the Flags data pipeline on the Lean side.

The empty-typed flags (type ∅ₜ) are produced by `generate_empty_typed_flags n`,
a self-contained Lean enumeration (`FlagLoader.lean` / `Compute/Generate.lean`):
it evaluates `genSym2Graphs n` — one canonical representative per isomorphism
class — at elaboration time, with completeness (`… = Finset.univ`) discharged by
the mathematically-proved `genEmptyTypedFlagSet_eq_univ` rather than by
enumerating the entire quotient `Fintype`.

The general typed flags (type σ the `m`-th `k`-vertex graph) are produced
analogously by `generate_flags k m n`: it evaluates the self-contained Lean
enumeration `genFlagData k m n` — one orbit representative per flag, in the
canonical order — at elaboration time, synthesizing the same named constants the
old JSON loader (`load_flags`) did, with no JSON file read.

Each line synthesizes named constants/theorems at elaboration time. Generated
names use the `_<n>_<k>_<m>_<i>` suffix convention: `n` vertices; `k`,`m` describe
the type σ (`0_0` denotes the empty type ∅ₜ); `i` is the enumeration index.

The `#print`/`#check` lines at the end sanity-check that representative
generated declarations exist.
-/

generate_empty_typed_flags 0
generate_empty_typed_flags 1
generate_empty_typed_flags 2
generate_empty_typed_flags 3
generate_empty_typed_flags 4
generate_empty_typed_flags 5

generate_flags 1 0 1
generate_flags 1 0 2

generate_flags 1 0 3
generate_flags 2 0 3
generate_flags 2 1 3

generate_flags 2 0 4
generate_flags 2 1 4
generate_flags 3 0 4
generate_flags 3 1 4
generate_flags 3 2 4
generate_flags 3 3 4

generate_flags 3 0 5
generate_flags 3 1 5
generate_flags 3 2 5
generate_flags 3 3 5

#print Sym2LabeledGraph_3_1_0_2
#check downward_3_1_0_2
#check flagSet_3_0_0_eq_univ
#check flagSet_3_1_0_val_eq
