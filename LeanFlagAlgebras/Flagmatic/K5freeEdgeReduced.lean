-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 2:12 density; forbid 5:12131415232425343545').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/K5freeEdge_reduced_cert.json \
--     LeanFlagAlgebras/Flagmatic/K5freeEdgeReduced.lean --namespace K5freeEdgeReduced --native-decide --force
-- The main theorem is proved by `flag_certificate`, which reads the
-- certificate file at elaboration time; pass --materialize to emit the
-- fully expanded proof instead (no build-time certificate dependence).

import LeanFlagAlgebras.Automation.FlagCertificate

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K5freeEdgeReduced

-- The forbidden graph, as the 5-vertex `Sym2Graph` term `K5`: the complete graph
-- K₅, for which containing a copy and containing an induced copy coincide.
-- The generation commands below prune against it: a flag containing K5 is never
-- enumerated, and they emit the K5-free flags, the completeness lemma for that set, and
-- the pair-density / multiplication theorems the proof consumes.
def K5 : Sym2Graph 5 := completeSym2Graph 5
-- Generated bridging lemmas are proved by `native_decide`, so the main theorem below
-- additionally depends on the `Lean.ofReduceBool` and `Lean.trustCompiler` axioms,
-- which trust Lean's compiler and runtime for the evaluated decision procedures.
-- Regenerating without `--native-decide` proves the same lemmas by `decide +kernel`
-- and removes both, at a higher build cost.
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 2 K5
generate_forbid_free_empty_typed_flags 4 K5
generate_forbid_free_empty_typed_flags 5 K5
generate_forbid_free_flags 4 3 0 K5
generate_forbid_free_flags 4 3 2 K5
generate_forbid_free_flags 4 3 3 K5
generate_forbid_free_flags 5 3 0 K5
generate_forbid_free_flags 5 3 2 K5
generate_forbid_free_flags 5 3 3 K5
generate_forbid_free_flag_pair_density_theorems 4 5 3 0 K5
generate_forbid_free_mul_theorems 4 5 3 0 K5
generate_forbid_free_flag_pair_density_theorems 4 5 3 2 K5
generate_forbid_free_mul_theorems 4 5 3 2 K5
generate_forbid_free_flag_pair_density_theorems 4 5 3 3 K5
generate_forbid_free_mul_theorems 4 5 3 3 K5
generate_forbid_free_flag_density_theorems 2 1 5 K5

/-- **Main theorem (auto-generated).**
Every graph with no K₅ subgraph has edge density at most 3/4.

Proved directly from the certificate file by `flag_certificate`: the
matrices, exact-rational `LDLᵀ` PSD checks, objective expansion, and the
closing normalization are synthesized at elaboration time; the certificate
is candidate data only.  Replace the call with `flag_certificate?` for a
one-click `Try this:` materialization of the explicit tactic script.

Certificate description: '2-graph; maximize 2:12 density; forbid 5:12131415232425343545'
Bound: '3/4'. -/
theorem K5freeEdge_reduced_flagAlgebra
    : FlagAlgebra_2_0_0_1 ≤[completeGraph (Fin 5)] (3 / 4 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  flag_certificate "LeanFlagAlgebras/Flagmatic/Certificates/K5freeEdge_reduced_cert.json" K5

/-- The certificate's target graph as a `Sym2Graph` term, in the canonical
labeling: the same edge list as the generated `Sym2Graph_2_0_0_1`,
so the two are equal by `decide`. -/
def TargetGraph : Sym2Graph 2 where
  edges := {s(0, 1)}
  edges_valid := by decide

/-- **Turán-density form (auto-generated).**
Every graph with no K₅ subgraph has edge density at most 3/4.

Restates `K5freeEdge_reduced_flagAlgebra` through the spec-level bridge
`generalizedTuranDensity_le_of_forbidLE`: the asymptotic density of induced
copies of `TargetGraph` among K5-free graphs is at most '3/4'.
Unlike the flag-algebra statement, this one mentions no generated constant:
the target is the explicit edge list above, decoded by `toLabeledGraph.graph`. -/
theorem K5freeEdge_reduced_turanDensity
    : generalizedTuranDensity (completeGraph (Fin 5)) TargetGraph.toLabeledGraph.graph ≤ (3 / 4 : ℝ)
  := by
  apply generalizedTuranDensity_le_of_forbidLE (by norm_num)
  have htarget : TargetGraph = Sym2Graph_2_0_0_1 := by decide
  have hobj : TargetGraph.toLabeledGraph.graph.toFlagAlgebra
      = FlagAlgebra_2_0_0_1 := by
    rw [htarget]; rfl
  rw [hobj]
  exact K5freeEdge_reduced_flagAlgebra

end K5freeEdgeReduced
