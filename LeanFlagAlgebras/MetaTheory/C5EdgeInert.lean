import LeanFlagAlgebras.MetaTheory.C5EdgeObstruction
import LeanFlagAlgebras.MetaTheory.CertificateCones
import LeanFlagAlgebras.MetaTheory.VanishingIdeal

/-! # The `C₅`-free edge-type gap is closed-cone inert (paper §10, `cor:c5-edge-closed-inert`)

The `C₅`-free class fails root-plantability at the two-root edge type `τ`
(`c5free_edge_not_rootPlantable`, §9.5) — yet this gap is invisible to asymptotic
density bounds:

* `c5free_edge_no_closed_certificate_gap` (**`cor:c5-edge-closed-inert`**) — the
  quotient and ensemble certificate cones at `(c5FreeClass, edgeType)` have the same
  `Q₀`-closure: ensemble-relaxed edge-type labelled terms do not improve any asymptotic
  `C₅`-free density bound.  (A direct instance of `no_closed_certificate_gap`.)
* The pinned witness is even more inert: the triangle flag `F_△` vanishes on the whole
  root-planting set `S_τ` (`c5free_Ftri_zero_on_Sσ`, from the a.s. pinning
  `ae_Ftri_eq_zero_of_pinned` of §9.5), so by `prop:ideal-zero` it and all its
  flag-multiples unlabel to zero on `Q₀` (`c5free_Ftri_mul_downward_eq_zero`; the case
  `h = 1` recovers §9.5's `Ftri_downward_zero`).
-/

namespace FlagAlgebras.MetaTheory

/-- The triangle flag vanishes on the whole root-planting set of the `C₅`-free class at
the edge type (`cor:c5-edge-pinned` upgraded from almost-sure to everywhere-on-`S_τ`,
via `Sσ_subset_eval_eq_of_ae_pinned`). -/
theorem c5free_Ftri_zero_on_Sσ :
    ∀ χ ∈ Sσ (c5FreeClass.constraintOf edgeType),
      (PositiveHomSpace.toPosHom χ) F_tri = 0 := by
  have h := Sσ_subset_eval_eq_of_ae_pinned (c5FreeClass.constraintOf edgeType) F_tri 0
    (fun φ₀ hφ₀ hσ => ae_Ftri_eq_zero_of_pinned hφ₀ hσ)
  exact fun χ hχ => h hχ

/-- **`cor:c5-edge-closed-inert`**: for the `C₅`-free class at the edge type, the
quotient and ensemble certificate cones have the same closure in the `Q₀`-seminorm —
even though the type is not root-plantable (`c5free_edge_not_rootPlantable`). -/
theorem c5free_edge_no_closed_certificate_gap (u : FlagAlgebra ∅ₜ) :
    MemQ0Closure (c5FreeClass.constraintOf edgeType).forb0 (quotCone edgeType) u ↔
      MemQ0Closure (c5FreeClass.constraintOf edgeType).forb0
        (ensCone (c5FreeClass.constraintOf edgeType)) u :=
  no_closed_certificate_gap (c5FreeClass.constraintOf edgeType) u

/-- The pinned witness `F_△` and all its flag-multiples unlabel to zero on `Q₀`
(`prop:ideal-zero` applied to the §9.5 pinning). -/
theorem c5free_Ftri_mul_downward_eq_zero (h : FlagAlgebra edgeType)
    {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ (c5FreeClass.constraintOf edgeType).forb0) :
    φ₀ (⟦F_tri * h⟧₀ : FlagAlgebra ∅ₜ) = 0 :=
  downward_mul_eval_eq_zero_of_zero_on_Sσ (c5FreeClass.constraintOf edgeType)
    c5free_Ftri_zero_on_Sσ h hφ₀

end FlagAlgebras.MetaTheory
