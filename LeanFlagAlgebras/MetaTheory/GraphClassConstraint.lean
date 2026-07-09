import LeanFlagAlgebras.MetaTheory.HeredClass
import LeanFlagAlgebras.MetaTheory.Blowup

/-! # Clone-closed graph classes (paper §5)

A `GraphClass` is a hereditary class ([`HeredClass`](./HeredClass.lean)) that is in addition closed
under **independent blow-ups** (`clone_closed`).  It is the class hypothesis of the §5 capstone
`thm:clone-root-plantable`.

Heredity and the constraint machinery — `constraintOf`, the consumption lemmas
`mem_of_forbiddenFree` (F1) and `forbiddenFree_of_mem` (F2), and `graphFlag` — are inherited from
`HeredClass` (they never use the closure assumption, and §6–§7 reuse the very same lemmas for their
own closure operations).  This file adds only the clone-closure layer and the `K_r`-free instance.

The standalone `constraintOf` / `mem_of_forbiddenFree` / `forbiddenFree_of_mem` below are thin
wrappers over the `HeredClass` versions on `gc.toHeredClass`, kept so the §5 capstone can keep
writing `constraintOf gc σ` etc.

Finally `cliqueFreeClass r` instantiates the framework with the `K_r`-free class, using
`SimpleGraph.CliqueFree.comap` (heredity) and `cliqueFree_independentBlowup` (clone-closure).
-/

open FlagAlgebras

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The clone-closed graph-class structure -/

/-- A hereditary, clone-closed graph class: a `HeredClass` (membership + heredity) that is in
addition preserved under independent blow-ups. -/
structure GraphClass extends HeredClass where
  /-- Clone-closure: independent blow-ups of a member are members. -/
  clone_closed : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (m : V → ℕ),
            Mem G → Mem (independentBlowup G m)

/-! ## The constraint and consumption lemmas (wrappers over `HeredClass`) -/

variable {n₀ : ℕ}

/-- The constraint of a clone-closed class — the `HeredClass` constraint of its underlying
hereditary class. -/
def constraintOf (gc : GraphClass) (σ : FlagType (Fin n₀)) : Constraint σ :=
  gc.toHeredClass.constraintOf σ

/-- **F1** for a `GraphClass`: a self-forbidding flag is in the class (delegates to
`HeredClass.mem_of_forbiddenFree`). -/
theorem mem_of_forbiddenFree (gc : GraphClass) {σ : FlagType (Fin n₀)}
    {N : ℕ} (G : LabeledGraph σ (Fin N))
    (hff : ∀ F : FinFlag σ, (constraintOf gc σ).forbσ F →
        flagDensity₁ F.2 (⟦G⟧ : Flag σ (Fin N)) = 0) :
    gc.Mem G.graph :=
  gc.toHeredClass.mem_of_forbiddenFree G hff

/-- **F2** for a `GraphClass`: a graph in the class is forbidden-free (delegates to
`HeredClass.forbiddenFree_of_mem`). -/
theorem forbiddenFree_of_mem (gc : GraphClass) {σ : FlagType (Fin n₀)}
    {N : ℕ} (H : SimpleGraph (Fin N)) (hH : gc.Mem H)
    (D : FinFlag ∅ₜ) (hD : (constraintOf gc σ).forb0 D) :
    flagDensity₁ D.2 (graphFlag H) = 0 :=
  gc.toHeredClass.forbiddenFree_of_mem H hH D hD

/-! ## The `K_r`-free instance -/

/-- The class of `K_r`-free graphs as a `GraphClass`: heredity is `SimpleGraph.CliqueFree.comap`,
clone-closure is `cliqueFree_independentBlowup`. -/
def cliqueFreeClass (r : ℕ) : GraphClass where
  Mem {_V} _ _ G := G.CliqueFree r
  comap f hG := hG.comap f
  clone_closed G m hG := cliqueFree_independentBlowup G m hG

end FlagAlgebras.MetaTheory
