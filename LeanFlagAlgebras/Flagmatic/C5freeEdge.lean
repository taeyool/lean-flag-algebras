-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 5:1223344551').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/C5freeEdge_cert.json \
--     LeanFlagAlgebras/Flagmatic/C5freeEdge.lean --namespace C5freeEdge --mask-density --mask-flagsets --force
-- The main theorem is proved by `flag_certificate`, which reads the
-- certificate file at elaboration time; pass --materialize to emit the
-- fully expanded proof instead (no build-time certificate dependence).

import LeanFlagAlgebras.Automation.FlagCertificate
import LeanFlagAlgebras.BitMask.RCanon2_6

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace C5freeEdge

-- The forbidden graph, as the 5-vertex `Sym2Graph` term `ForbidGraph`. It is forbidden
-- as a subgraph, not necessarily an induced one, so a copy of `ForbidGraph` may carry extra
-- edges. The generation commands below prune against it: a flag containing `ForbidGraph` is
-- never enumerated, and they emit the subgraph-`ForbidGraph`-free flags, the completeness lemma
-- for that set, and the pair-density / multiplication theorems the proof consumes.
def ForbidGraph : Sym2Graph 5 where
  edges := {s(0, 1), s(0, 4), s(1, 2), s(2, 3), s(3, 4)}
  edges_valid := by decide
-- Every generated bridging lemma is proved by `decide +kernel`, so this file
-- introduces no compiled-evaluation axiom: `#print axioms` on the main theorem
-- below lists only Lean's own three.
set_option flagGen.kernelDecide true
-- The pair densities route through the BitMask rooted sweeps (shared
-- subset-pair pass), keeping each kernel check a small declaration -- the
-- batched `decide +kernel` alternative balloons the kernel's evaluation cache.
set_option flagGen.maskPairDensity true
set_option flagGen.maskPairDensityShared true
-- The flag-set completeness layers route through the BitMask
-- canonicalization sweeps (triangle forbids at swept combinations).
set_option flagGen.maskCompleteness true
set_option flagGen.maskFlagSets true
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 2 ForbidGraph
generate_forbid_free_empty_typed_flags 4 ForbidGraph
generate_forbid_free_empty_typed_flags 5 ForbidGraph
generate_forbid_free_flags 4 3 0 ForbidGraph
generate_forbid_free_flags 4 3 1 ForbidGraph
generate_forbid_free_flags 4 3 2 ForbidGraph
generate_forbid_free_flags 4 3 3 ForbidGraph
generate_forbid_free_flags 5 3 0 ForbidGraph
generate_forbid_free_flags 5 3 1 ForbidGraph
generate_forbid_free_flags 5 3 2 ForbidGraph
generate_forbid_free_flags 5 3 3 ForbidGraph
generate_forbid_free_flag_pair_density_theorems 4 5 3 0 ForbidGraph
generate_forbid_free_mul_theorems 4 5 3 0 ForbidGraph
generate_forbid_free_flag_pair_density_theorems 4 5 3 1 ForbidGraph
generate_forbid_free_mul_theorems 4 5 3 1 ForbidGraph
generate_forbid_free_flag_pair_density_theorems 4 5 3 2 ForbidGraph
generate_forbid_free_mul_theorems 4 5 3 2 ForbidGraph
generate_forbid_free_flag_pair_density_theorems 4 5 3 3 ForbidGraph
generate_forbid_free_mul_theorems 4 5 3 3 ForbidGraph
generate_forbid_free_flag_density_theorems 2 1 5 ForbidGraph

/-- **Main theorem (auto-generated).**
Every graph with no C₅ subgraph has edge density at most 1/2.

Proved directly from the certificate file by `flag_certificate`: the
matrices, exact-rational `LDLᵀ` PSD checks, objective expansion, and the
closing normalization are synthesized at elaboration time; the certificate
is candidate data only.  Replace the call with `flag_certificate?` for a
one-click `Try this:` materialization of the explicit tactic script.

Certificate description: '2-graph; maximize 2:12 density; forbid 5:1223344551'
Bound: '1/2'. -/
theorem C5freeEdge_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[ForbidGraph.toLabeledGraph.graph] (1 / 2 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  flag_certificate "LeanFlagAlgebras/Flagmatic/Certificates/C5freeEdge_cert.json" ForbidGraph

/-- The certificate's target graph as a `Sym2Graph` term, in the canonical
labeling: the same edge list as the generated `Sym2Graph_2_0_0_1`,
so the two are equal by `decide`. -/
def TargetGraph : Sym2Graph 2 where
  edges := {s(0, 1)}
  edges_valid := by decide

/-- **Turán-density form (auto-generated).**
Every graph with no C₅ subgraph has edge density at most 1/2.

Restates `C5freeEdge_flagAlgebra` through the spec-level bridge
`generalizedTuranDensity_le_of_forbidLE`: the asymptotic density of induced
copies of `TargetGraph` among ForbidGraph-free graphs is at most '1/2'.
Unlike the flag-algebra statement, this one mentions no generated constant:
the target is the explicit edge list above, decoded by `toLabeledGraph.graph`. -/
theorem C5freeEdge_turanDensity
    : generalizedTuranDensity (ForbidGraph.toLabeledGraph.graph) TargetGraph.toLabeledGraph.graph ≤ (1 / 2 : ℝ)
  := by
  apply generalizedTuranDensity_le_of_forbidLE (by norm_num)
  have htarget : TargetGraph = Sym2Graph_2_0_0_1 := by decide
  have hobj : TargetGraph.toLabeledGraph.graph.toFlagAlgebra
      = FlagAlgebra_2_0_0_1 := by
    rw [htarget]; rfl
  rw [hobj]
  exact C5freeEdge_flagAlgebra

end C5freeEdge
