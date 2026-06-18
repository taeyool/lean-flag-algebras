import LeanFlagAlgebras.MetaTheory.BlowupClosed

/-! # Complete blow-ups and true twins: root-plantability (paper §6)

A hereditary class is **true-clone-closed** (`def:true-clone-closed`) if every complete blow-up
`G^{m,+}` of a member is a member — the true-twin analogue of clone-closure, replacing each vertex
by a *clique* rather than an independent set.  The complete blow-up is `completeBlowup`, the special
case `W = ⊤` of the generalised blow-up `subBlowup`.

`thm:true-clone-root-plantable`: every true-clone-closed hereditary class is root-plantable at every
non-degenerate type.  Since true-clone-closure implies blow-up-closure (blow up a vertex to a
clique, `TrueCloneClosed.toBlowupClosed`), this is now a **corollary of the unified theorem**
`blowupClosed_root_plantable` (paper `cor:closures-imply-blowup`(2)).
-/

open MeasureTheory
open SimpleGraph

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-- A hereditary class is **true-clone-closed** (`def:true-clone-closed`) if every complete blow-up
of a member is a member. -/
def TrueCloneClosed (hc : HeredClass) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hc.Mem G → ∀ (m : V → ℕ),
    hc.Mem (completeBlowup G m)

/-- **True-clone-closed ⟹ blow-up-closed** (`cor:closures-imply-blowup`(2)): blow up a vertex to a
clique `K_N`, which is a one-vertex complete blow-up, in the class by true-clone-closure. -/
theorem TrueCloneClosed.toBlowupClosed {hc : HeredClass} (htcc : TrueCloneClosed hc) :
    BlowupClosed hc := by
  intro V _ _ G v N hG
  refine ⟨(⊤ : SimpleGraph (Fin N)), ?_⟩
  -- `oneBlowup G v ⊤ ≃g subBlowup G (oneFamily v ⊤) = completeBlowup G (oneSize v N)`.
  rw [hc.Mem_congr (oneBlowup_iso G v (⊤ : SimpleGraph (Fin N))), subBlowup_oneFamily_top G v N]
  exact htcc G hG (oneSize v N)

/-- **True-clone-closed classes are root-plantable** (`thm:true-clone-root-plantable`), now a
corollary of the unified `blowupClosed_root_plantable`. -/
theorem true_clone_root_plantable (hc : HeredClass) (htcc : TrueCloneClosed hc)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) :
    RootPlantable (hc.constraintOf σ) :=
  blowupClosed_root_plantable htcc.toBlowupClosed σ hn₀

/-- **Quotient/ensemble equivalence for a true-clone-closed class** (`thm:true-clone-root-plantable`,
final assertion).  Once `S_σ = Q_σ`, quotient non-negativity and ensemble non-negativity agree for
every flag-algebra element. -/
theorem true_clone_quotient_iff_ensemble (hc : HeredClass) (htcc : TrueCloneClosed hc)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) (f : FlagAlgebra σ) :
    QuotientNonneg (hc.constraintOf σ) f ↔ EnsembleNonneg (hc.constraintOf σ) f :=
  (support_criterion _).mpr (true_clone_root_plantable hc htcc σ hn₀) f

end FlagAlgebras.MetaTheory
