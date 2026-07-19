module

public import LeanFlagAlgebras.Archive.Compute.Basic_

@[expose] public section

example : (@Finset.univ ((SimpleGraph.completeGraph (Fin 3)) ≃g (SimpleGraph.completeGraph (Fin 3)))).card = 6 := by decide
