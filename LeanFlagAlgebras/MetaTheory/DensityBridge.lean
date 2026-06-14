import LeanFlagAlgebras.FlagAlgebra.FlagAlgebra

/-! # The flag-density bridge (entry point)

Infrastructure for §5 `lem:planted-estimate` of `MetaTheory/paper.tex`.

The planted blow-up estimate compares the flag density `p(F₀, ·)` on a blow-up with its value
on the base graph.  To reason about it quantitatively we first expose the abstract
`flagDensity₁` as the concrete *card ratio* it is by definition:

  `p(F, G) = flagDensity₁ F G = (labeledGraphCount F G) / ((|G| − k) choose (|F| − k))`,

i.e. the number of induced labelled copies of `F` in `G` divided by the number of ways to
choose the `|F| − k` non-root vertices of such a copy among the `|G| − k` non-root vertices of
`G`.  This is the entry point for the subset-sampling argument of `lem:planted-estimate`.
-/

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- The single-flag density is the subflag density (the singleton-list specialisation). -/
lemma flagDensity₁_eq_subflagDensity {U W : Type} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (F : Flag σ U) (G : Flag σ W) : flagDensity₁ F G = subflagDensity F G :=
  (subflagDensity_eq_flagListDensity F G).symm

/-- On representatives, the flag density is the labelled-graph density (any finite hosts). -/
lemma flagDensity₁_mk {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (Hrep : LabeledGraph σ U) (Grep : LabeledGraph σ W) :
    flagDensity₁ (⟦Hrep⟧ : Flag σ U) (⟦Grep⟧ : Flag σ W) = labeledGraphDensity Hrep Grep := by
  rw [flagDensity₁_eq_subflagDensity]; rfl

/-- **Density as a card ratio** (the bridge entry point): the flag density of `H` in `G`
equals the number of induced labelled copies of `H`, divided by the binomial counting the
choices of non-root vertices.  Stated for any finite host vertex type (needed for the blow-up,
whose host is the sigma type `Σ v, Fin (m v)`). -/
lemma flagDensity₁_eq_count_div {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (Hrep : LabeledGraph σ U) (Grep : LabeledGraph σ W) :
    flagDensity₁ (⟦Hrep⟧ : Flag σ U) (⟦Grep⟧ : Flag σ W)
      = (labeledGraphCount Hrep Grep : ℚ)
          / ((Grep.size - σ.size).choose (Hrep.size - σ.size)) := by
  rw [flagDensity₁_mk]; rfl

end FlagAlgebras.MetaTheory
