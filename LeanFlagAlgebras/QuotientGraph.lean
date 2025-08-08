import Mathlib.Combinatorics.SimpleGraph.Maps

open Classical

def graph_eqv (G₀ G₁ : SimpleGraph V) : Prop
  :=
  Nonempty (G₀ ≃g G₁)

theorem graph_eqv.refl (G : SimpleGraph V)
    : graph_eqv G G
  :=
  instNonemptyOfInhabited

theorem graph_eqv.symm
    : ∀ {G₀ G₁ : SimpleGraph V}, graph_eqv G₀ G₁ → graph_eqv G₁ G₀
  := by
  intro G₀ G₁ h
  let ⟨f, hf⟩ := h
  refine ⟨f.symm, ?_⟩
  intro a b
  have := @hf (f.symm a) (f.symm b)
  simp [Equiv.apply_symm_apply] at this
  exact this.symm

theorem graph_eqv.trans
    : ∀ {G₀ G₁ G₂ : SimpleGraph V}, graph_eqv G₀ G₁ → graph_eqv G₁ G₂ → graph_eqv G₀ G₂
  :=
  fun ⟨f01, hf01⟩ ⟨f12, hf12⟩ ↦ ⟨f01.trans f12, hf12.trans hf01⟩

instance graphSetoid (V : Type) [Fintype V] [DecidableEq V]
    : Setoid (SimpleGraph V)
  where
    r     := graph_eqv
    iseqv := {
      refl  := graph_eqv.refl,
      symm  := graph_eqv.symm,
      trans := graph_eqv.trans
    }

def QuotSimpleGraph (V : Type) [Fintype V] [DecidableEq V] : Type :=
  Quotient (graphSetoid V)

noncomputable instance quotSimpleGraphFintype (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (QuotSimpleGraph V)
  := Quotient.fintype (graphSetoid V)
