"""Generate the four 6-vertex sweep piece files (Canon6Sweep0-3.lean).

Each file covers 8192 masks via 8 depth-10 `decide +kernel` lemmas in
separate declarations (the kernel releases its evaluation cache between
declarations), glued into a depth-13 subrange verdict; `Canon6.lean`
assembles the four subranges into the full `2^15` sweep.

Usage (from the repository root):
    python LeanFlagAlgebras/BitMask/gen_sweep6.py
"""
import os

BASE = os.path.dirname(os.path.abspath(__file__))

for k in range(4):
    lines = []
    lines.append("import LeanFlagAlgebras.BitMask.Canon6Checker")
    lines.append("")
    lines.append(f"/-! Completeness sweep piece {k} of 4: masks `{k * 8192}`–`{(k + 1) * 8192 - 1}`.")
    lines.append("")
    lines.append("Machine-generated (gen_sweep6.py). The subrange is covered by 8")
    lines.append("separate depth-10 kernel evaluations rather than one depth-13")
    lines.append("evaluation, so the kernel releases its evaluation cache between")
    lines.append("declarations; `sweepMasks_of_pieces` glues them back together. -/")
    lines.append("")
    lines.append("namespace FlagAlgebras.Compute.BitMask.Canon6")
    lines.append("")
    lines.append("open FlagAlgebras.Compute.BitMask")
    lines.append("")
    for j in range(8):
        lines.append("set_option maxRecDepth 65536 in")
        lines.append(f"private lemma s{j} : sweepMasks leaf6 10 ({k} * 8 + {j}) = true := by")
        lines.append("  decide +kernel")
    lines.append("")
    lines.append(f"/-- Subrange {k} of the completeness sweep. -/")
    lines.append(f"lemma sweep6_piece_{k} : sweepMasks leaf6 13 {k} = true := by")
    lines.append(f"  refine sweepMasks_of_pieces leaf6 10 3 {k} fun j hj => ?_")
    lines.append("  match j, hj with")
    for j in range(8):
        lines.append(f"  | {j}, _ => exact s{j}")
    lines.append("  | n + 8, h => exact absurd h (by omega)")
    lines.append("")
    lines.append("end FlagAlgebras.Compute.BitMask.Canon6")
    lines.append("")
    with open(os.path.join(BASE, f"Canon6Sweep{k}.lean"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    print(f"wrote Canon6Sweep{k}.lean")
