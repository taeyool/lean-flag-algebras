import «LeanFlagAlgebras».PositiveHom

open FlagAlgebras

def labeledK2 : LabeledGraph ∅ₜ (Fin 2) where
  graph := completeGraph (Fin 2)
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj (completeGraph (Fin 2)).Adj

def labeledK3 : LabeledGraph ∅ₜ (Fin 3) where
  graph := completeGraph (Fin 3)
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj (completeGraph (Fin 3)).Adj

noncomputable def K2 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨2, ⟦labeledK2⟧⟩⟧

noncomputable def K3 : FlagAlgebra ∅ₜ :=
  ⟦unitVector ⟨3, ⟦labeledK3⟧⟩⟧

theorem mantel_theorem
    : K2 ≤ (1 / 2) • 1 + K3
  :=
  sorry
