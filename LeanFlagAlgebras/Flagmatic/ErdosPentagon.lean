-- Auto-generated from Flagmatic certificate (description: '2-graph; maximize 5:1213243545 density; forbid 3:121323').
-- Do not edit by hand; regenerate with
--   python LeanFlagAlgebras/Flagmatic/flagmatic_to_lean.py gen-skeleton \
--     LeanFlagAlgebras/Flagmatic/Certificates/ErdosPentagon_cert.json \
--     LeanFlagAlgebras/Flagmatic/ErdosPentagon.lean --namespace ErdosPentagon --force
-- The main theorem is proved by `flag_certificate`, which reads the
-- certificate file at elaboration time; pass --materialize to emit the
-- fully expanded proof instead (no build-time certificate dependence).

import LeanFlagAlgebras.Automation.FlagCertificate

open FlagAlgebras Forbid FlagAlgebras.Automation
open SimpleGraph Matrix
open FlagAlgebras.Compute

namespace ErdosPentagon

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
generate_forbid_free_empty_typed_flags 4 K3
generate_forbid_free_empty_typed_flags 5 K3
generate_forbid_free_flags 4 3 0 K3
generate_forbid_free_flags 4 3 1 K3
generate_forbid_free_flags 4 3 2 K3
generate_forbid_free_flags 5 3 0 K3
generate_forbid_free_flags 5 3 1 K3
generate_forbid_free_flags 5 3 2 K3
generate_forbid_free_flag_pair_density_theorems 4 5 3 0 K3
generate_forbid_free_mul_theorems 4 5 3 0 K3
generate_forbid_free_flag_pair_density_theorems 4 5 3 1 K3
generate_forbid_free_mul_theorems 4 5 3 1 K3
generate_forbid_free_flag_pair_density_theorems 4 5 3 2 K3
generate_forbid_free_mul_theorems 4 5 3 2 K3

/-- **Main theorem (auto-generated).**
Every graph with no K₃ subgraph has C₅ density at most 24/625.

Proved directly from the certificate file by `flag_certificate`: the
matrices, exact-rational `LDLᵀ` PSD checks, objective expansion, and the
closing normalization are synthesized at elaboration time; the certificate
is candidate data only.  Replace the call with `flag_certificate?` for a
one-click `Try this:` materialization of the explicit tactic script.

Certificate description: '2-graph; maximize 5:1213243545 density; forbid 3:121323'
Bound: '24/625'. -/
theorem ErdosPentagon_flagAlgebra
    : FlagAlgebra_5_0_0_19 ≤[completeGraph (Fin 3)] (24 / 625 : ℝ) • (1 : FlagAlgebra ∅ₜ)
  := by
  flag_certificate "LeanFlagAlgebras/Flagmatic/Certificates/ErdosPentagon_cert.json" K3

/-- The certificate's target graph as a `Sym2Graph` term, in the canonical
labeling: the same edge list as the generated `Sym2Graph_5_0_0_19`,
so the two are equal by `decide`. -/
def TargetGraph : Sym2Graph 5 where
  edges := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 4)}
  edges_valid := by decide

/-- **Turán-density form (auto-generated).**
Every graph with no K₃ subgraph has C₅ density at most 24/625.

Restates `ErdosPentagon_flagAlgebra` through the spec-level bridge
`generalizedTuranDensity_le_of_forbidLE`: the asymptotic density of induced
copies of `TargetGraph` among K3-free graphs is at most '24/625'.
Unlike the flag-algebra statement, this one mentions no generated constant:
the target is the explicit edge list above, decoded by `toLabeledGraph.graph`. -/
theorem ErdosPentagon_turanDensity
    : generalizedTuranDensity (completeGraph (Fin 3)) TargetGraph.toLabeledGraph.graph ≤ (24 / 625 : ℝ)
  := by
  apply generalizedTuranDensity_le_of_forbidLE (by norm_num)
  have htarget : TargetGraph = Sym2Graph_5_0_0_19 := by decide
  have hobj : TargetGraph.toLabeledGraph.graph.toFlagAlgebra
      = FlagAlgebra_5_0_0_19 := by
    rw [htarget]; rfl
  rw [hobj]
  exact ErdosPentagon_flagAlgebra

end ErdosPentagon
