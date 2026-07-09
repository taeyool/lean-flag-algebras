import LeanFlagAlgebras.MetaTheory.BlowupClosed

/-! # Substitution-closed graph classes: root-plantability (paper §7)

A hereditary class is **substitution-closed** (`def:substitution-closed`) if the substitution
`G[H_v : v ∈ V(G)]` is a member whenever `G` and all the fibres `H_v` are members.  The substitution
`G[H_v]` — the disjoint union of the `H_v` with all edges between `H_v` and `H_w` for `vw ∈ E(G)` —
is exactly `subBlowup G Hs` with `Hs v = H_v` (between-fibre adjacency = `G`, within-fibre = `H_v`).

`thm:substitution-root-plantable`: every infinite substitution-closed hereditary class is
root-plantable at every non-degenerate type.  Since infinite substitution-closure implies
blow-up-closure (blow up a vertex to an in-class graph of the right size,
`SubstitutionClosed.toBlowupClosed`), this is now a **corollary of the unified theorem**
`blowupClosed_root_plantable` (paper `cor:closures-imply-blowup`(3)).
-/

open SimpleGraph

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-- A hereditary class is **substitution-closed** (`def:substitution-closed`) if substituting
in-class fibres into the vertices of an in-class graph yields an in-class graph. -/
def SubstitutionClosed (hc : HeredClass) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hc.Mem G →
    ∀ {s : V → ℕ} (Hs : ∀ v, SimpleGraph (Fin (s v))),
      (∀ v, hc.Mem (Hs v)) → hc.Mem (subBlowup G Hs)

/-- **Infinite substitution-closed ⟹ blow-up-closed** (`cor:closures-imply-blowup`(3)): blow up a
vertex to an in-class graph `H` of order `N` (which exists by infinitude), a one-vertex substitution
in the class by substitution-closure. -/
theorem SubstitutionClosed.toBlowupClosed {hc : HeredClass} (hsc : SubstitutionClosed hc)
    (hinf : ∀ N : ℕ, ∃ H : SimpleGraph (Fin N), hc.Mem H) : BlowupClosed hc := by
  -- Every singleton-vertex graph is in the class (an in-class one exists by `hinf 1`, and all
  -- graphs on `Fin 1` are edgeless, hence equal to `⊥`).
  have h1 : hc.Mem (⊥ : SimpleGraph (Fin 1)) := by
    obtain ⟨H₁, hH₁⟩ := hinf 1
    have hH₁bot : H₁ = ⊥ := by
      ext a b
      have hab : a = b := Subsingleton.elim a b
      subst hab
      simp [SimpleGraph.irrefl]
    rwa [hH₁bot] at hH₁
  intro V _ _ G v N hG
  -- Pick an in-class interior `H` of order `N`.
  obtain ⟨H, hH⟩ := hinf N
  refine ⟨H, ?_⟩
  -- `oneBlowup G v H ≃g subBlowup G (oneFamily v H)`, in the class by substitution-closure
  -- (each fibre of `oneFamily v H` is in the class).
  rw [hc.Mem_congr (oneBlowup_iso G v H)]
  exact hsc G hG (oneFamily v H) (fun w => oneFamily_mem v H hH h1 w)

/-- **Substitution-closed classes are root-plantable** (`thm:substitution-root-plantable`), now a
corollary of the unified `blowupClosed_root_plantable`. -/
theorem substitution_root_plantable (hc : HeredClass) (hsc : SubstitutionClosed hc)
    (hinf : ∀ N : ℕ, ∃ H : SimpleGraph (Fin N), hc.Mem H)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) :
    RootPlantable (hc.constraintOf σ) :=
  blowupClosed_root_plantable (hsc.toBlowupClosed hinf) σ hn₀

/-- **Quotient/ensemble equivalence for a substitution-closed class**
(`thm:substitution-root-plantable`, final assertion). -/
theorem substitution_quotient_iff_ensemble (hc : HeredClass) (hsc : SubstitutionClosed hc)
    (hinf : ∀ N : ℕ, ∃ H : SimpleGraph (Fin N), hc.Mem H)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) (f : FlagAlgebra σ) :
    QuotientNonneg (hc.constraintOf σ) f ↔ EnsembleNonneg (hc.constraintOf σ) f :=
  (support_criterion _).mpr (substitution_root_plantable hc hsc hinf σ hn₀) f

end FlagAlgebras.MetaTheory
