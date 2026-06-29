# `LeanFlagAlgebras/Flagmatic/` - Flagmatic certificate to Lean automation

This directory contains the tools that **turn Flagmatic SDP certificates into
Lean 4 flag-algebra proofs automatically**, together with the generated proof
artifacts.

```
Flagmatic/
├── flagmatic_to_lean.py   ← main automation script (parser/generator/CLI)
├── Certificates/          ← input: sparse SDP JSON exported by Flagmatic
│   ├── mantel_cert.json
│   ├── K3forbidC4_cert.json
│   ├── K4turan_cert.json
│   └── ErdosPentagon_cert.json
└── *.lean                 ← output: proof files generated from the certificates
    ├── Mantel.lean
    ├── K3forbidC4.lean
    ├── K4turan.lean
    └── ErdosPentagon.lean
```

---

## One-line automation

```powershell
python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton `
    LeanFlagAlgebras/Flagmatic/Certificates/<problem>_cert.json `
    LeanFlagAlgebras/Flagmatic/<Problem>.lean `
    --namespace <Problem> --force
```

This single command generates imports, opens, namespace declarations, load
commands, matrix/PSD proofs, sigma/v definitions, and the main theorem
(auto-proved by tactics).

For other subcommands, run `python flagmatic_to_lean.py --help` or check the
docstring at the top of `flagmatic_to_lean.py`.

---

## Verified scenario matrix

| Cert | Forbid | N | n_obj | Branch | Blocks T | Notes |
|---|---|---|---|---|---|---|
| `mantel_cert.json` | K₃ | 3 | 2 | B | 1 | Bound `1/2`. Smallest case, branch B, single block |
| `K3forbidC4_cert.json` | K₃ | 4 | 4 | A | 2 | Bound `3/8`. Branch A, multi-block |
| `K4turan_cert.json` | K₄ | 4 | 2 | B | 2 | Bound `2/3`. K₄ forbid, branch B, bare-mul case |
| `ErdosPentagon_cert.json` | K₃ | 5 | 5 | A | 3 | Bound `24/625`. N = 5 scale, 3 blocks |

Coverage already verified by the automation:
- ✅ Both Branch A (`n_obj == N`) and Branch B (`n_obj < N`)
- ✅ Automatic recognition of K_n forbiddens (K3, K4)
- ✅ Block counts 1, 2, and 3
- ✅ Host sizes N = 3, 4, and 5
- ✅ Both the smul branch and the bare-mul branch of `reduce_downward_flagmul`

Not yet tested:
- ⏳ Non-K_n forbiddens such as P_n, C_n, and K_{a,b}. The code is general; it will recognize them immediately once you add the corresponding `def` and `_toFinFlag_eq` lines in `CommonGraphs.lean`.

---

## Workflow for a new certificate

```powershell
# 1. Optional: mapping sanity check (also validates the cert — every flagmatic
#    string is resolved to a canonical Lean identifier, raising on any failure).
python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py inspect <cert>.json

# 2. Generate the Lean file (flags, densities and products are all generated
#    inside Lean by the `generate_pruned_*` commands — no JSON files on disk).
python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton `
    LeanFlagAlgebras/Flagmatic/Certificates/<name>_cert.json `
    LeanFlagAlgebras/Flagmatic/<Name>.lean --namespace <Name> --force

# 3. Build
lake build LeanFlagAlgebras.Flagmatic.<Name>

# 4. Optional: add the import to the root manifest LeanFlagAlgebras.lean
```

---

## Adding a new forbidden graph

To add a new forbidden graph `X` (for example C₄, P₄, ...), follow these steps:

1. **Lean**: Add two lines to `LeanFlagAlgebras/Forbid/CommonGraphs.lean`:
   ```lean
   def X : SimpleGraph (Fin n) := ⟨...⟩
   lemma X_toFinFlag_eq : X.toFinFlag = ⟨n, Flag_n_0_0_<i>⟩ := by ...
   ```
    Here, `<i>` is the canonical index of `X` in `LeanFlagAlgebras/Flags/Graphs/graphs_<n>.json`.
    Follow the same pattern used for K3 and K4.

2. **Data**: Generate the required `graphs_<N>_X_free_indices.json` and `density_*_forbid_X.json` files using `gen_free_indices.py` and `calculate_densities.py`.

3. **Automatic recognition**: No Python changes are needed. `flagmatic_to_lean.py` parses `CommonGraphs.lean` and uses graph isomorphism to map the certificate's forbidden graph to the corresponding `X` tag.

---

## Flagmatic certificate format (reference)

```json
{
  "description": "2-graph; maximize <objective_str> density; forbid <forbid_str>",
  "bound": "1/2",
  "order_of_admissible_graphs": 3,
  "number_of_admissible_graphs": 3,
  "admissible_graphs": ["3:", "3:12", "3:1213"],
  "number_of_types": 1,
  "types": ["1:"],
  "numbers_of_flags": [2],
  "flags": [["2:(1)", "2:12(1)"]],
  "qdash_matrices": [[[2]]],
  "r_matrices": [[["1/2"], ["-1/2"]]],
  "admissible_graph_densities": [0, "1/3", "2/3"]
}
```

### Flagmatic string encoding

- Vertices are 1-indexed and written as single digits when possible (vertex ≤ 9).
- Edges are encoded as two-digit pairs. For example, `"4:121324"` means vertex 4 with edges {1-2, 1-3, 2-4}.
- Sigma-flag labels use the form `"3:12(2)"`, meaning 3 vertices with the first 2 as type vertices (labels 0 and 1).

### How the automation uses the certificate

| Lean output | Source |
|---|---|
| Objective identifier (e.g. `FlagAlgebra_2_0_0_1`) | `description`'s `maximize ...` clause, resolved by graph isomorphism |
| Forbidden graph term (e.g. `K3.toFinFlag`) | `description`'s `forbid ...` clause, matched against `CommonGraphs.lean` |
| Bound (e.g. `(1 / 2 : ℝ)`) | `cert["bound"]` |
| Host size N | `cert["order_of_admissible_graphs"]` |
| σ_t, v_t | `cert["types"]`, `cert["flags"]` |
| M_t matrix | `R_t · Q'_t · R_tᵀ` (`qdash` stores the upper-triangular rows) |
| LDLᵀ decomposition | Exact rational LDL decomposition computed from `M_t` |
| Branch decision | `parse_flagmatic(objective).n` vs `N` |
| Branch B auxiliary lemma | Exhaustive computation of induced densities over all vertex subsets of the host graph |

---

## Next problems to try

Good candidates for exposing another dimension of the automation:

1. **C₄-free edge density** - first non-K_n forbidden-graph test (try the workflow after adding C4 to `CommonGraphs.lean`)
2. **K₅-free edge density** - add K₅ to `CommonGraphs.lean`
3. **An N = 6 case larger than the Erdős pentagon instance** - check the scaling limit (requires `graphs_6.json`)
