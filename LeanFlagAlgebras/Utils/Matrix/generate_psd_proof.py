"""Emit a Lean LDLᵀ certificate proving a symmetric rational matrix is PSD.

Given a square symmetric matrix of exact rationals, this script computes an
exact (Fraction-based) LDLᵀ decomposition M = L · diag(d) · Lᵀ, sanity-checks
it by reconstruction, and emits Lean 4 code that:
  - defines the matrix, the L factor, and the diagonal d over ℚ,
  - proves d is entrywise nonnegative and M = L · diag(d) · Lᵀ,
  - concludes M.PosSemidef via a configurable helper theorem,
  - and derives the analogous ℝ-valued statements via `ratMatrixToReal`.

This produces the SOS / PSD certificates that the flag-algebra density
proofs in this repository depend on. The generated block relies on
`ratMatrixToReal`, `posSemidef_of_eq_mul_diagonal_mul_transpose`, and
`posSemidef_of_eq_mul_diagonal_mul_transpose_real` from
`LeanFlagAlgebras/Utils/Matrix/PosSemiDef.lean`.

Inputs: a JSON matrix passed inline (--matrix) or via a file (--input), as a
list of rows whose entries are ints/floats/rational strings like "1/2".
Output: Lean source printed to stdout or appended/written to --out.

Example:
    python generate_psd_proof.py --input matrix.json --name P \\
        --out path/to/Output.lean --write-mode append
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from fractions import Fraction
from typing import List, Sequence


def parse_number(value) -> Fraction:
    """Coerce an int, float, or numeric/rational string into an exact Fraction."""
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        return Fraction(str(value))
    if isinstance(value, str):
        return Fraction(value.strip())
    raise TypeError(f"Unsupported number type: {type(value)}")


def parse_matrix(raw) -> List[List[Fraction]]:
    """Validate that raw is a non-empty square list-of-lists and return it as Fractions."""
    if not isinstance(raw, list) or len(raw) == 0:
        raise ValueError("Matrix must be a non-empty list of rows")
    mat = []
    width = None
    for row in raw:
        if not isinstance(row, list) or len(row) == 0:
            raise ValueError("Each row must be a non-empty list")
        if width is None:
            width = len(row)
        elif len(row) != width:
            raise ValueError("All rows must have same length")
        mat.append([parse_number(x) for x in row])
    if len(mat) != width:
        raise ValueError("Matrix must be square")
    return mat


def is_symmetric(mat: Sequence[Sequence[Fraction]]) -> bool:
    """Return True iff mat[i][j] == mat[j][i] for all i, j."""
    n = len(mat)
    for i in range(n):
        for j in range(i + 1, n):
            if mat[i][j] != mat[j][i]:
                return False
    return True


def ldlt_decompose(
    mat: List[List[Fraction]],
) -> tuple[List[List[Fraction]], List[Fraction]]:
    """Compute an exact LDLᵀ decomposition of a symmetric matrix.

    Returns (L, d) where L is unit lower-triangular and d is the diagonal
    vector such that mat == L · diag(d) · Lᵀ. Zero pivots (d[k] == 0) are
    handled by leaving the corresponding subcolumn of L at zero, which
    keeps the factorization exact for PSD inputs with rank deficiency.
    """
    n = len(mat)
    l = [[Fraction(1 if i == j else 0, 1) for j in range(n)] for i in range(n)]
    d = [Fraction(0, 1) for _ in range(n)]

    for k in range(n):
        s = sum(l[k][s] * l[k][s] * d[s] for s in range(k))
        d[k] = mat[k][k] - s

        if d[k] == 0:
            for i in range(k + 1, n):
                l[i][k] = Fraction(0, 1)
            continue

        for i in range(k + 1, n):
            s2 = sum(l[i][s] * l[k][s] * d[s] for s in range(k))
            l[i][k] = (mat[i][k] - s2) / d[k]

    return l, d


def reconstruct(
    ld: tuple[List[List[Fraction]], List[Fraction]],
) -> List[List[Fraction]]:
    """Reconstruct L · diag(d) · Lᵀ from an (L, d) pair (used to verify the decomposition)."""
    l, d = ld
    n = len(l)
    out = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            out[i][j] = sum(l[i][k] * d[k] * l[j][k] for k in range(n))
    return out


def frac_to_lean(q: Fraction) -> str:
    """Render a Fraction as a Lean ℚ literal, e.g. (3 / 4 : ℚ) or (5 : ℚ)."""
    if q == 0:
        return "0"
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} / {q.denominator} : ℚ)"


def vec_to_lean_bang(vec: Sequence[Fraction]) -> str:
    """Render a vector as Lean Matrix/Fin `![...]` notation."""
    return "![" + ", ".join(frac_to_lean(x) for x in vec) + "]"


def matrix_to_lean_bang(mat: Sequence[Sequence[Fraction]]) -> str:
    """Render a matrix as Lean `!![row; row; ...]` notation."""
    rows = [", ".join(frac_to_lean(x) for x in row) for row in mat]
    return "!![" + ";\n   ".join(rows) + "]"


def emit_lean_block(
    mat_name: str,
    l_name: str,
    d_name: str,
    mat: List[List[Fraction]],
    l: List[List[Fraction]],
    d: List[Fraction],
    psd_helper_name: str,
    psd_helper_real_name: str,
) -> str:
    """Build the full Lean proof block for the PSD certificate.

    Emits the ℚ definitions (matrix, L, d), the d-nonneg lemma, the
    M = L·diag(d)·Lᵀ equality, the `PosSemidef` theorem via psd_helper_name,
    and the ℝ-valued counterparts derived through `ratMatrixToReal` using
    psd_helper_real_name. Returns the block as a single newline-joined string.
    """
    n = len(mat)

    real_mat_name = f"{mat_name}_real"
    real_d_nonneg_name = f"{d_name}_real_nonneg"
    real_eq_ldl_name = f"{mat_name}_real_eq_LDL"

    lines = []
    lines.append(f"def {mat_name} : Matrix (Fin {n}) (Fin {n}) ℚ :=")
    lines.append(f"  {matrix_to_lean_bang(mat)}")
    lines.append("")

    lines.append(f"def {d_name} : Fin {n} → ℚ :=")
    lines.append(f"  {vec_to_lean_bang(d)}")
    lines.append("")

    lines.append(f"def {l_name} : Matrix (Fin {n}) (Fin {n}) ℚ :=")
    lines.append(f"  {matrix_to_lean_bang(l)}")
    lines.append("")

    lines.append(f"lemma {d_name}_nonneg (i : Fin {n}) : 0 ≤ {d_name} i := by")
    lines.append(f"  fin_cases i <;> norm_num [{d_name}]")
    lines.append("")

    lines.append(
        f"lemma {mat_name}_eq_LDL : {mat_name} = {l_name} * Matrix.diagonal {d_name} * {l_name}ᵀ := by"
    )
    lines.append("  decide +kernel")
    lines.append("")

    lines.append(f"theorem {mat_name}_posSemidef : {mat_name}.PosSemidef := by")
    lines.append(f"  exact {psd_helper_name} {d_name}_nonneg {mat_name}_eq_LDL")
    lines.append("")

    # Real-valued counterpart, derived from the rational LDLᵀ certificate above.
    lines.append(
        f"noncomputable def {real_mat_name} : Matrix (Fin {n}) (Fin {n}) ℝ :="
    )
    lines.append(f"  ratMatrixToReal {mat_name}")
    lines.append("")

    lines.append(
        f"lemma {real_d_nonneg_name} (i : Fin {n}) : 0 ≤ ({d_name} i : ℝ) := by"
    )
    lines.append(f"  exact_mod_cast {d_name}_nonneg i")
    lines.append("")

    lines.append(f"lemma {real_eq_ldl_name} :")
    lines.append(
        f"    {real_mat_name} = (ratMatrixToReal {l_name} * Matrix.diagonal (fun i => ({d_name} i : ℝ))) * (ratMatrixToReal {l_name})ᵀ := by"
    )
    lines.append("  calc")
    lines.append(
        f"    {real_mat_name} = ratMatrixToReal ({l_name} * Matrix.diagonal {d_name} * {l_name}ᵀ) := by"
    )
    lines.append(f"      simp [{real_mat_name}, ratMatrixToReal, {mat_name}_eq_LDL]")
    lines.append(
        f"    _ = (ratMatrixToReal {l_name} * Matrix.diagonal (fun i => ({d_name} i : ℝ))) * (ratMatrixToReal {l_name})ᵀ := by"
    )
    lines.append(
        "      simp [ratMatrixToReal, Matrix.map_mul_ratCast, Matrix.transpose_map, mul_assoc]"
    )
    lines.append("")

    lines.append(
        f"theorem {real_mat_name}_posSemidef : {real_mat_name}.PosSemidef := by"
    )
    lines.append(
        f"  exact {psd_helper_real_name} {real_d_nonneg_name} {real_eq_ldl_name}"
    )

    return "\n".join(lines)


def main() -> None:
    """CLI entry point: parse args, decompose the matrix, and emit/write Lean code."""
    script_dir = Path(__file__).resolve().parent

    def resolve_local_path(path_str: str) -> Path:
        p = Path(path_str)
        if p.is_absolute():
            return p
        return script_dir / p

    parser = argparse.ArgumentParser(
        description="Generate Lean LDLᵀ certificate (d, L) from a symmetric rational matrix list."
    )
    parser.add_argument(
        "--matrix",
        type=str,
        help='JSON matrix string, e.g. \'[["1/2","0"],["0","3/2"]]\'',
    )
    parser.add_argument(
        "--input", type=str, help="Path to JSON file containing matrix as list of lists"
    )
    parser.add_argument(
        "--name", type=str, default="P", help="Lean matrix name prefix (default: P)"
    )
    parser.add_argument(
        "--psd-helper",
        type=str,
        default="posSemidef_of_eq_mul_diagonal_mul_transpose",
        help="Lean theorem name used to conclude PosSemidef over ℚ from (d_nonneg, eq_LDL)",
    )
    parser.add_argument(
        "--psd-helper-real",
        type=str,
        default="posSemidef_of_eq_mul_diagonal_mul_transpose_real",
        help="Lean theorem name used to conclude PosSemidef over ℝ from (d_real_nonneg, real_eq_LDL)",
    )
    parser.add_argument(
        "--out", type=str, help="Output Lean file path. If omitted, prints to stdout"
    )
    parser.add_argument(
        "--write-mode",
        choices=["append", "overwrite"],
        default="append",
        help="When --out is set: append (default) or overwrite the target file",
    )
    args = parser.parse_args()

    if bool(args.matrix) == bool(args.input):
        raise SystemExit("Provide exactly one of --matrix or --input")

    if args.matrix:
        raw = json.loads(args.matrix)
    else:
        input_path = resolve_local_path(args.input)
        with open(input_path, "r", encoding="utf-8") as f:
            raw = json.load(f)

    mat = parse_matrix(raw)
    if not is_symmetric(mat):
        raise SystemExit(
            "Input matrix is not symmetric, so LDLᵀ (symmetric form) is not applicable"
        )

    l, d = ldlt_decompose(mat)
    rec = reconstruct((l, d))
    if rec != mat:
        raise SystemExit(
            "Internal check failed: reconstructed matrix does not match input"
        )

    name = args.name
    lean = emit_lean_block(
        name,
        f"L{name}",
        f"d{name}",
        mat,
        l,
        d,
        args.psd_helper,
        args.psd_helper_real,
    )

    nonneg = all(x >= 0 for x in d)
    header = (
        f"-- LDLᵀ generated for {name}, size={len(mat)}, diagonal nonnegative={nonneg}"
    )

    if args.out:
        out_path = resolve_local_path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        mode = "a" if args.write_mode == "append" else "w"
        with open(out_path, mode, encoding="utf-8") as f:
            if mode == "a":
                f.write("\n\n")
            f.write(header + "\n")
            f.write(lean)
            f.write("\n")
        print(f"Wrote Lean code to '{out_path}' ({args.write_mode})")
    else:
        print(header)
        print(lean)


# Save the target matrix in matrix.json, then run with e.g.
#   python generate_psd_proof.py --input matrix.json --name P --out path/to/Output.lean
# The generated block depends on `ratMatrixToReal`, `posSemidef_of_eq_mul_diagonal_mul_transpose`,
# and `posSemidef_of_eq_mul_diagonal_mul_transpose_real` from
# `LeanFlagAlgebras/Utils/Matrix/PosSemiDef.lean`. Make sure the consuming file imports it.
if __name__ == "__main__":
    main()
