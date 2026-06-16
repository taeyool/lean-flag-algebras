import LeanFlagAlgebras.MetaTheory.SubstitutionClosed

/-! # Complete blow-ups and true twins: root-plantability (paper §6)

A hereditary class is **true-clone-closed** (`def:true-clone-closed`) if every complete blow-up
`G^{m,+}` of a member is a member — the true-twin analogue of clone-closure, replacing each vertex
by a *clique* rather than an independent set.  The complete blow-up is `completeBlowup`, the special
case `W = ⊤` of the generalised blow-up `subBlowup`.

`thm:true-clone-root-plantable`: every true-clone-closed hereditary class is root-plantable at every
non-degenerate type.  This is `subst_root_plantable` with the closure witness `W = fun _ => ⊤`.
-/

open MeasureTheory
open SimpleGraph

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-- A hereditary class is **true-clone-closed** (`def:true-clone-closed`) if every complete blow-up
of a member is a member. -/
def TrueCloneClosed (hc : HeredClass) : Prop :=
  ∀ {n : ℕ} (Γ : SimpleGraph (Fin n)), hc.Mem Γ → ∀ (m : Fin n → ℕ),
    hc.Mem (completeBlowup Γ m)

/-- **True-clone-closed classes are root-plantable** (`thm:true-clone-root-plantable`).  For any
true-clone-closed hereditary class `hc` and any non-degenerate type `σ`, the constraint
`hc.constraintOf σ` is root-plantable, `S_σ = Q_σ`.  The uniform complete `(M+1)`-blow-up of an
in-class base stays in the class (`W = ⊤`), which is exactly the closure witness
`subst_root_plantable` needs. -/
theorem true_clone_root_plantable (hc : HeredClass) (htcc : TrueCloneClosed hc)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) :
    RootPlantable (hc.constraintOf σ) :=
  subst_root_plantable hc σ hn₀ (by
    intro n Γ hΓ M
    exact ⟨fun _ => (⊤ : SimpleGraph (Fin (M + 1))), htcc Γ hΓ (fun _ => M + 1)⟩)

/-- **Quotient/ensemble equivalence for a true-clone-closed class** (`thm:true-clone-root-plantable`,
final assertion).  Once `S_σ = Q_σ`, quotient non-negativity and ensemble non-negativity agree for
every flag-algebra element. -/
theorem true_clone_quotient_iff_ensemble (hc : HeredClass) (htcc : TrueCloneClosed hc)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) (f : FlagAlgebra σ) :
    QuotientNonneg (hc.constraintOf σ) f ↔ EnsembleNonneg (hc.constraintOf σ) f :=
  (support_criterion _).mpr (true_clone_root_plantable hc htcc σ hn₀) f

end FlagAlgebras.MetaTheory
