"""Generate the 64 seven-vertex sweep piece files (Canon7Sweep00-63.lean)
and the glue file (Canon7Glue.lean).

Each piece file covers 32768 masks via 32 depth-10 `decide +kernel`
lemmas in separate declarations (the kernel releases its evaluation
cache between declarations), glued into a depth-15 subrange verdict;
`Canon7Glue.lean` assembles the 64 subranges into the full `2^21`
sweep verdict `sweep7`.

Usage (from the repository root):
    python LeanFlagAlgebras/BitMask/gen_sweep7.py
"""
import os

BASE = os.path.dirname(os.path.abspath(__file__))

for k in range(64):
    lines = []
    lines.append("import LeanFlagAlgebras.BitMask.Canon7Checker")
    lines.append("")
    lines.append(f"/-! Completeness sweep piece {k} of 64: masks "
                 f"`{k * 32768}`–`{(k + 1) * 32768 - 1}`.")
    lines.append("")
    lines.append("Machine-generated (gen_sweep7.py). The subrange is covered by 32")
    lines.append("separate depth-10 kernel evaluations rather than one depth-15")
    lines.append("evaluation, so the kernel releases its evaluation cache between")
    lines.append("declarations; `sweepMasks_of_pieces` glues them back together. -/")
    lines.append("")
    lines.append("namespace FlagAlgebras.Compute.BitMask.Canon7")
    lines.append("")
    lines.append("open FlagAlgebras.Compute.BitMask")
    lines.append("")
    for j in range(32):
        lines.append("set_option maxRecDepth 65536 in")
        lines.append(f"private lemma s{j:02d} : sweepMasks leaf7 10 ({k} * 32 + {j}) = true := by")
        lines.append("  decide +kernel")
    lines.append("")
    lines.append(f"/-- Subrange {k} of the completeness sweep. -/")
    lines.append(f"lemma sweep7_piece_{k:02d} : sweepMasks leaf7 15 {k} = true := by")
    lines.append(f"  refine sweepMasks_of_pieces leaf7 10 5 {k} fun j hj => ?_")
    lines.append("  match j, hj with")
    for j in range(32):
        lines.append(f"  | {j}, _ => exact s{j:02d}")
    lines.append("  | n + 32, h => exact absurd h (by omega)")
    lines.append("")
    lines.append("end FlagAlgebras.Compute.BitMask.Canon7")
    lines.append("")
    with open(os.path.join(BASE, f"Canon7Sweep{k:02d}.lean"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

lines = []
for k in range(64):
    lines.append(f"import LeanFlagAlgebras.BitMask.Canon7Sweep{k:02d}")
lines.append("")
lines.append("/-! Machine-generated glue (gen_sweep7.py): assembles the 64 subrange")
lines.append("verdicts into the full `2^21` completeness sweep. -/")
lines.append("")
lines.append("namespace FlagAlgebras.Compute.BitMask.Canon7")
lines.append("")
lines.append("open FlagAlgebras.Compute.BitMask")
lines.append("")
lines.append("/-- The assembled completeness sweep: `leaf7` holds on all `2^21`")
lines.append("masks. -/")
lines.append("lemma sweep7 : sweepMasks leaf7 21 0 = true := by")
lines.append("  refine sweepMasks_of_pieces leaf7 15 6 0 fun k hk => ?_")
lines.append("  rw [zero_mul, zero_add]")
lines.append("  match k, hk with")
for k in range(64):
    lines.append(f"  | {k}, _ => exact sweep7_piece_{k:02d}")
lines.append("  | n + 64, h => exact absurd h (by omega)")
lines.append("")
lines.append("end FlagAlgebras.Compute.BitMask.Canon7")
lines.append("")
with open(os.path.join(BASE, "Canon7Glue.lean"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines))

print("wrote Canon7Sweep00-63.lean and Canon7Glue.lean")
