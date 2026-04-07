import LeanFlagAlgebras.GraphAlgebra.SubgraphDensity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/--
`generalizedExtremalNumber n H F` is the maximum number of induced copies of `F`
among all `H`-free graphs on `n` vertices.

This generalizes `extremalNumber n H`, where the optimized statistic is the edge count.
-/
noncomputable def generalizedExtremalNumber (n : ℕ) (H : SimpleGraph U) (F : SimpleGraph W) : ℕ :=
  by
    classical
    exact sup { G : SimpleGraph (Fin n) | H.Free G }
      (fun (G : SimpleGraph (Fin n)) ↦ GraphAlgebras.subgraphCount F G)

/--
The generalized Turán density associated to a forbidden graph `H` and a target graph `F`.

It is defined as the limit of
`generalizedExtremalNumber n H F / n.choose (Fintype.card W)` as `n → ∞`.
-/
noncomputable def generalizedTuranDensity (H : SimpleGraph U) (F : SimpleGraph W) : ℝ :=
  limUnder atTop fun n ↦
    (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ)

omit [Fintype U] [DecidableEq U] [DecidableEq W] in
/--
Placeholder monotonicity statement for normalized generalized extremal numbers.

TODO: prove this via a subgraph-count double counting argument.
-/
theorem antitoneOn_generalizedExtremalNumber_div_choose
    (H : SimpleGraph U) (F : SimpleGraph W) :
    AntitoneOn
      (fun n ↦ (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ))
      (Set.Ici (Fintype.card W)) := by
  sorry

omit [Fintype U] [DecidableEq U] [DecidableEq W] in
/--
The generalized Turán density is well-defined as the limit of the normalized generalized
extremal numbers.
-/
theorem tendsto_generalizedTuranDensity
    (H : SimpleGraph U) (F : SimpleGraph W) :
    Tendsto
      (fun n ↦ (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ))
      atTop (𝓝 (generalizedTuranDensity H F)) := by
  have hmono := antitoneOn_generalizedExtremalNumber_div_choose H F
  let f := fun n ↦ (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ)
  suffices h : ∃ x, Tendsto (fun n ↦ f (n + Fintype.card W)) atTop (𝓝 x) by
    obtain ⟨_, h⟩ := by simpa [tendsto_add_atTop_iff_nat (Fintype.card W)] using h
    simpa [generalizedTuranDensity, f, ← Tendsto.limUnder_eq h] using h
  use ⨅ n, f (n + Fintype.card W)
  apply tendsto_atTop_ciInf
  · rw [antitone_add_nat_iff_antitoneOn_nat_Ici]
    simpa [f] using hmono
  · use 0
    intro n ⟨_, hn⟩
    rw [← hn]
    positivity

end SimpleGraph
