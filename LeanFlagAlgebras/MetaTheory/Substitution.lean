import LeanFlagAlgebras.MetaTheory.SubstitutionClosed

/-! # Substitution-closed graph classes: root-plantability (paper §7)

A hereditary class is **substitution-closed** (`def:substitution-closed`) if the substitution
`G[H_v : v ∈ V(G)]` is a member whenever `G` and all the fibres `H_v` are members.  The substitution
`G[H_v]` — the disjoint union of the `H_v` with all edges between `H_v` and `H_w` for `vw ∈ E(G)` —
is exactly `subBlowup G Hs` with `Hs v = H_v` (between-fibre adjacency = `G`, within-fibre = `H_v`).

`thm:substitution-root-plantable`: every infinite substitution-closed hereditary class is
root-plantable at every non-degenerate type.  This is `subst_root_plantable` with the closure
witness built from in-class fibres of the right size (which exist because the class has graphs of
every order).
-/

open MeasureTheory
open SimpleGraph

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-- A hereditary class is **substitution-closed** (`def:substitution-closed`) if substituting
in-class fibres into the vertices of an in-class graph yields an in-class graph. -/
def SubstitutionClosed (hc : HeredClass) : Prop :=
  ∀ {n : ℕ} (Γ : SimpleGraph (Fin n)), hc.Mem Γ →
    ∀ {s : Fin n → ℕ} (Hs : ∀ v, SimpleGraph (Fin (s v))),
      (∀ v, hc.Mem (Hs v)) → hc.Mem (subBlowup Γ Hs)

/-- **Substitution-closed classes are root-plantable** (`thm:substitution-root-plantable`).  For an
infinite (here: containing a graph of every order `hinf`) substitution-closed hereditary class `hc`
and any non-degenerate type `σ`, the constraint `hc.constraintOf σ` is root-plantable, `S_σ = Q_σ`.
The uniform substitution of an in-class base by in-class fibres of size `M+1` stays in the class,
which is the closure witness `subst_root_plantable` needs. -/
theorem substitution_root_plantable (hc : HeredClass) (hsc : SubstitutionClosed hc)
    (hinf : ∀ N : ℕ, ∃ H : SimpleGraph (Fin N), hc.Mem H)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) :
    RootPlantable (hc.constraintOf σ) :=
  subst_root_plantable hc σ hn₀ (by
    intro n Γ hΓ M
    obtain ⟨Hfib, hHfib⟩ := hinf (M + 1)
    exact ⟨fun _ => Hfib, hsc Γ hΓ (fun _ => Hfib) (fun _ => hHfib)⟩)

/-- **Quotient/ensemble equivalence for a substitution-closed class**
(`thm:substitution-root-plantable`, final assertion). -/
theorem substitution_quotient_iff_ensemble (hc : HeredClass) (hsc : SubstitutionClosed hc)
    (hinf : ∀ N : ℕ, ∃ H : SimpleGraph (Fin N), hc.Mem H)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) (f : FlagAlgebra σ) :
    QuotientNonneg (hc.constraintOf σ) f ↔ EnsembleNonneg (hc.constraintOf σ) f :=
  (support_criterion _).mpr (substitution_root_plantable hc hsc hinf σ hn₀) f

end FlagAlgebras.MetaTheory
