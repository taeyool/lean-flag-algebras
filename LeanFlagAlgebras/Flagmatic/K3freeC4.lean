-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 4:12132434 density; forbid 3:121323').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/K3freeC4_cert.json \
--     LeanFlagAlgebras/Flagmatic/K3freeC4.lean --namespace K3freeC4 --force
-- The main theorem is proved by `flag_certificate`, which reads the
-- certificate file at elaboration time; pass --materialize to emit the
-- fully expanded proof instead (no build-time certificate dependence).

import LeanFlagAlgebras.Automation.FlagCertificate

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace K3freeC4

-- The forbidden graph, as the 3-vertex `Sym2Graph` term `K3`: the complete graph
-- K₃, for which containing a copy and containing an induced copy coincide.
-- The generation commands below prune against it: a flag containing K3 is never
-- enumerated, and they emit the K3-free flags, the completeness lemma for that set, and
-- the pair-density / multiplication theorems the proof consumes.
def K3 : Sym2Graph 3 := completeSym2Graph 3
-- Every generated bridging lemma is proved by `decide +kernel`, so this file
-- introduces no compiled-evaluation axiom: `#print axioms` on the main theorem
-- below lists only Lean's own three.
set_option flagGen.kernelDecide true
-- The generation commands run large decision procedures during elaboration, and the
-- closing normalization recurses over a long flag sum; both limits are lifted for the
-- rest of the file.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
generate_forbid_free_empty_typed_flags 3 K3
generate_forbid_free_empty_typed_flags 4 K3
generate_forbid_free_flags 3 2 0 K3
generate_forbid_free_flags 3 2 1 K3
generate_forbid_free_flags 4 2 0 K3
generate_forbid_free_flags 4 2 1 K3
generate_forbid_free_flag_pair_density_theorems 3 4 2 0 K3
generate_forbid_free_mul_theorems 3 4 2 0 K3
generate_forbid_free_flag_pair_density_theorems 3 4 2 1 K3
generate_forbid_free_mul_theorems 3 4 2 1 K3

/-- **Main theorem (auto-generated).**
Every graph with no K₃ subgraph has C₄ density at most 3/8.

Proved directly from the certificate file by `flag_certificate`: the
matrices, exact-rational `LDLᵀ` PSD checks, objective expansion, and the
closing normalization are synthesized at elaboration time; the certificate
is candidate data only.  Replace the call with `flag_certificate?` for a
one-click `Try this:` materialization of the explicit tactic script.

Certificate description: '2-graph; maximize 4:12132434 density; forbid 3:121323'
Bound: '3/8'. -/
theorem K3freeC4_flagAlgebra
    : FlagAlgebra_4_0_0_8 ≤[completeGraph (Fin 3)] (3 / 8 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  flag_certificate "LeanFlagAlgebras/Flagmatic/Certificates/K3freeC4_cert.json" K3

/-- The certificate's target graph as a `Sym2Graph` term, in the canonical
labeling: the same edge list as the generated `Sym2Graph_4_0_0_8`,
so the two are equal by `decide`. -/
def TargetGraph : Sym2Graph 4 where
  edges := {s(0, 1), s(0, 2), s(1, 3), s(2, 3)}
  edges_valid := by decide

/-- **Turán-density form (auto-generated).**
Every graph with no K₃ subgraph has C₄ density at most 3/8.

Restates `K3freeC4_flagAlgebra` through the spec-level bridge
`generalizedTuranDensity_le_of_forbidLE`: the asymptotic density of induced
copies of `TargetGraph` among K3-free graphs is at most '3/8'.
Unlike the flag-algebra statement, this one mentions no generated constant:
the target is the explicit edge list above, decoded by `toLabeledGraph.graph`. -/
theorem K3freeC4_turanDensity
    : generalizedTuranDensity (completeGraph (Fin 3)) TargetGraph.toLabeledGraph.graph ≤ (3 / 8 : ℝ)
  := by
  apply generalizedTuranDensity_le_of_forbidLE (by norm_num)
  have htarget : TargetGraph = Sym2Graph_4_0_0_8 := by decide
  have hobj : TargetGraph.toLabeledGraph.graph.toFlagAlgebra
      = FlagAlgebra_4_0_0_8 := by
    rw [htarget]; rfl
  rw [hobj]
  exact K3freeC4_flagAlgebra

end K3freeC4
