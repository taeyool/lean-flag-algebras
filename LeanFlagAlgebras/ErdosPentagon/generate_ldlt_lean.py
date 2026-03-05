from __future__ import annotations

import argparse
import json
from pathlib import Path
from fractions import Fraction
from typing import List, Sequence


def parse_number(value) -> Fraction:
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        return Fraction(str(value))
    if isinstance(value, str):
        return Fraction(value.strip())
    raise TypeError(f"Unsupported number type: {type(value)}")


def parse_matrix(raw) -> List[List[Fraction]]:
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
    n = len(mat)
    for i in range(n):
        for j in range(i + 1, n):
            if mat[i][j] != mat[j][i]:
                return False
    return True


def ldlt_decompose(mat: List[List[Fraction]]) -> tuple[List[List[Fraction]], List[Fraction]]:
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


def reconstruct(ld: tuple[List[List[Fraction]], List[Fraction]]) -> List[List[Fraction]]:
    l, d = ld
    n = len(l)
    out = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            out[i][j] = sum(l[i][k] * d[k] * l[j][k] for k in range(n))
    return out


def frac_to_lean(q: Fraction) -> str:
    if q == 0:
        return "0"
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} / {q.denominator} : ℚ)"


def vec_to_lean_bang(vec: Sequence[Fraction]) -> str:
    return "![" + ", ".join(frac_to_lean(x) for x in vec) + "]"


def matrix_to_lean_bang(mat: Sequence[Sequence[Fraction]]) -> str:
    rows = [", ".join(frac_to_lean(x) for x in row) for row in mat]
    return "!![" + ";\n   ".join(rows) + "]"


def emit_lean_block(mat_name: str, l_name: str, d_name: str, mat: List[List[Fraction]], l: List[List[Fraction]], d: List[Fraction]) -> str:
    n = len(mat)

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

    lines.append(f"lemma {mat_name}_eq_LDL : {mat_name} = {l_name} * Matrix.diagonal {d_name} * {l_name}ᵀ := by")
    lines.append("  native_decide")

    return "\n".join(lines)


def main() -> None:
    script_dir = Path(__file__).resolve().parent

    def resolve_local_path(path_str: str) -> Path:
        p = Path(path_str)
        if p.is_absolute():
            return p
        return script_dir / p

    parser = argparse.ArgumentParser(
        description="Generate Lean LDLᵀ certificate (d, L) from a symmetric rational matrix list."
    )
    parser.add_argument("--matrix", type=str, help="JSON matrix string, e.g. '[[\"1/2\",\"0\"],[\"0\",\"3/2\"]]'")
    parser.add_argument("--input", type=str, help="Path to JSON file containing matrix as list of lists")
    parser.add_argument("--name", type=str, default="P", help="Lean matrix name prefix (default: P)")
    parser.add_argument("--out", type=str, help="Output Lean file path. If omitted, prints to stdout")
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
        raise SystemExit("Input matrix is not symmetric, so LDLᵀ (symmetric form) is not applicable")

    l, d = ldlt_decompose(mat)
    rec = reconstruct((l, d))
    if rec != mat:
        raise SystemExit("Internal check failed: reconstructed matrix does not match input" )

    name = args.name
    lean = emit_lean_block(name, f"L{name}", f"d{name}", mat, l, d)

    nonneg = all(x >= 0 for x in d)
    header = f"-- LDLᵀ generated for {name}, size={len(mat)}, diagonal nonnegative={nonneg}"

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


# After saving the desired matrix in matrix.json, run the script with the target file and matrix name as follows:
# --input matrix.json --out PosSemiDef.lean --name P 
if __name__ == "__main__":
    main()

