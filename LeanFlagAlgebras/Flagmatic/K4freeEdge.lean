-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 4:121314232434').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/K4freeEdge_cert.json \
--     LeanFlagAlgebras/Flagmatic/K4freeEdge.lean --namespace K4freeEdge --force
-- The main theorem is proved by `flag_certificate`, which reads the
-- certificate file at elaboration time; pass --materialize to emit the
-- fully expanded proof instead (no build-time certificate dependence).

import LeanFlagAlgebras.Automation.FlagCertificate

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K4freeEdge

-- The forbidden graph, as the 4-vertex `Sym2Graph` term `K4`: the complete graph
-- K₄, for which containing a copy and containing an induced copy coincide.
-- The generation commands below prune against it: a flag containing K4 is never
-- enumerated, and they emit the K4-free flags, the completeness lemma for that set, and
-- the pair-density / multiplication theorems the proof consumes.
def K4 : Sym2Graph 4 := completeSym2Graph 4
-- Every generated bridging lemma is proved by `decide +kernel`, so this file
-- introduces no compiled-evaluation axiom: `#print axioms` on the main theorem
-- below lists only Lean's own three.
set_option flagGen.kernelDecide true
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 2 K4
generate_forbid_free_empty_typed_flags 3 K4
generate_forbid_free_empty_typed_flags 4 K4
generate_forbid_free_flags 3 2 0 K4
generate_forbid_free_flags 3 2 1 K4
generate_forbid_free_flags 4 2 0 K4
generate_forbid_free_flags 4 2 1 K4
generate_forbid_free_flag_pair_density_theorems 3 4 2 0 K4
generate_forbid_free_mul_theorems 3 4 2 0 K4
generate_forbid_free_flag_pair_density_theorems 3 4 2 1 K4
generate_forbid_free_mul_theorems 3 4 2 1 K4
generate_forbid_free_flag_density_theorems 2 1 4 K4

/-- **Main theorem (auto-generated).**
Every graph with no K₄ subgraph has edge density at most 2/3.

Proved directly from the certificate file by `flag_certificate`: the
matrices, exact-rational `LDLᵀ` PSD checks, objective expansion, and the
closing normalization are synthesized at elaboration time; the certificate
is candidate data only.  Replace the call with `flag_certificate?` for a
one-click `Try this:` materialization of the explicit tactic script.

Certificate description: '2-graph; maximize 2:12 density; forbid 4:121314232434'
Bound: '2/3'. -/
theorem K4freeEdge_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 4)] (2 / 3 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  flag_certificate "LeanFlagAlgebras/Flagmatic/Certificates/K4freeEdge_cert.json" K4

/-- The certificate's target graph as a `Sym2Graph` term, in the canonical
labeling: the same edge list as the generated `Sym2Graph_2_0_0_1`,
so the two are equal by `decide`. -/
def TargetGraph : Sym2Graph 2 where
  edges := {s(0, 1)}
  edges_valid := by decide

/-- **Turán-density form (auto-generated).**
Every graph with no K₄ subgraph has edge density at most 2/3.

Restates `K4freeEdge_flagAlgebra` through the spec-level bridge
`generalizedTuranDensity_le_of_forbidLE`: the asymptotic density of induced
copies of `TargetGraph` among K4-free graphs is at most '2/3'.
Unlike the flag-algebra statement, this one mentions no generated constant:
the target is the explicit edge list above, decoded by `toLabeledGraph.graph`. -/
theorem K4freeEdge_turanDensity
    : generalizedTuranDensity (completeGraph (Fin 4)) TargetGraph.toLabeledGraph.graph ≤ (2 / 3 : ℝ)
  := by
  apply generalizedTuranDensity_le_of_forbidLE (by norm_num)
  have htarget : TargetGraph = Sym2Graph_2_0_0_1 := by decide
  have hobj : TargetGraph.toLabeledGraph.graph.toFlagAlgebra
      = FlagAlgebra_2_0_0_1 := by
    rw [htarget]; rfl
  rw [hobj]
  exact K4freeEdge_flagAlgebra

end K4freeEdge
