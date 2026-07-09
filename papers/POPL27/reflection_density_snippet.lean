import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity

/-!
This file contains the small reflection-layer density snippet displayed in
`paper_draft.tex`.  It is intentionally a one-candidate specialization of the
implementation's density code, so that the paper can present the core
decidability mechanism without the full product-density API.
-/

namespace FlagAlgebras.Compute

/-- The induced candidate `H` is isomorphic to the concrete pattern `F`. -/
def candidateMatches
    {k m n : ℕ} {σ : Sym2FlagType k}
    (F : Sym2LabeledGraph σ m)
    {G : Sym2LabeledGraph σ n}
    (H : Sym2InducedLabeledSubgraph G) : Prop :=
  Nonempty ((H.toLabeledSubgraph).coe ≃f F.toLabeledGraph)

/-- Lean can decide `candidateMatches F H` for each finite candidate `H`. -/
instance candidateMatchesDecidable
    {k m n : ℕ} {σ : Sym2FlagType k}
    (F : Sym2LabeledGraph σ m) (G : Sym2LabeledGraph σ n) :
    DecidablePred (fun H : Sym2InducedLabeledSubgraph G =>
      candidateMatches F H) :=
  fun H => by
    have : Fintype H.toLabeledSubgraph.subgraph.verts := by
      simp [Sym2InducedLabeledSubgraph.toLabeledSubgraph]
      exact H.verts.fintypeCoeSort
    have : DecidableRel (H.toLabeledSubgraph).coe.graph.Adj := by
      simp [Sym2InducedLabeledSubgraph.toLabeledSubgraph, SimpleGraph.Subgraph.coe]
      intro x y
      exact Finset.decidableMem (Sym2.mk (x.1, y.1)) H.edges
    have : DecidableRel F.toLabeledGraph.graph.Adj := by
      intro a b
      simp [Sym2LabeledGraph.toLabeledGraph]
      exact instDecidableAnd
    exact if hsize : H.verts.card = m then
      (by
        dsimp [candidateMatches]
        infer_instance)
    else
      isFalse (fun hIso => hsize (verts_card_of_coe_iso H F hIso))

namespace ReflectionDensitySnippet

/-- A one-pattern illustrative version of the reflected flag-density computation. -/
def sym2FlagDensity₁
    {k m n : ℕ} {σ : Sym2FlagType k}
    (F : Sym2LabeledGraph σ m) (G : Sym2LabeledGraph σ n)
    [DecidablePred (fun H : Sym2InducedLabeledSubgraph G =>
      candidateMatches F H)] : ℚ :=
  ((Finset.univ : Finset (Sym2InducedLabeledSubgraph G)).filter
    (fun H => candidateMatches F H)).card / Nat.choose (n - k) (m - k)

end ReflectionDensitySnippet

end FlagAlgebras.Compute
