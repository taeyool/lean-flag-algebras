import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.Forbid.TuranDensity

open FlagAlgebras

namespace Forbid

def _root_.SimpleGraph.toFinFlag
    {n : ℕ} (G : SimpleGraph (Fin n)) : FinFlag ∅ₜ
  :=
  let F : FlagWithSize ∅ₜ n := ⟦{
    graph := G,
    type_embed := RelEmbedding.ofIsEmpty _ _
  }⟧
  ⟨n, F⟩

noncomputable def _root_.SimpleGraph.toFlagAlgebra
    {n : ℕ} (G : SimpleGraph (Fin n)) : FlagAlgebra ∅ₜ
  :=
  ⟦unitVector G.toFinFlag⟧

theorem generalizedTuranDensity_le_of_forbidLE
    {n m : ℕ} (H : SimpleGraph (Fin n)) (F : SimpleGraph (Fin m))
    {c : ℝ} (h : F.toFlagAlgebra ≤[H.toFinFlag] c • 1)
    : generalizedTuranDensity H F ≤ c
  := by
  sorry

end Forbid
