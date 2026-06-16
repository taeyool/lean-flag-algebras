import LeanFlagAlgebras.MetaTheory.InducedContainment
import LeanFlagAlgebras.MetaTheory.SupportClosure
import LeanFlagAlgebras.MetaTheory.GraphClassConstraint

/-! # Hereditary graph classes without a closure assumption (paper §6–§7)

The §5 `GraphClass` bundles *independent-blow-up closure* (`clone_closed`).  Sections 6 and 7 use
different closure operations — complete blow-ups (`def:true-clone-closed`) and substitution
(`def:substitution-closed`) — and `cor:cluster-graphs` even exhibits a class (cluster graphs) that
is *not* clone-closed but is still root-plantable.  We therefore separate the heredity from the
closure: a `HeredClass` is just a membership predicate closed under induced subgraphs, and the
closure operation enters the root-plantability theorem as an explicit hypothesis.

The data and the two consumption lemmas mirror `GraphClassConstraint` exactly (they never use
`clone_closed`):

* `HeredClass.constraintOf` — the `Constraint` whose forbidden flags are those whose underlying
  graph leaves the class.
* `mem_of_forbiddenFree` (F1) — a flag with zero density of every forbidden flag is in the class.
* `forbiddenFree_of_mem` (F2) — a graph in the class has zero density of every forbidden flag.
-/

open FlagAlgebras

namespace FlagAlgebras.MetaTheory

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-! ## The hereditary-class structure -/

/-- A **hereditary graph class**: a membership predicate on finite simple graphs preserved under
taking induced subgraphs (along any graph embedding).  Unlike `GraphClass`, no blow-up closure is
assumed. -/
structure HeredClass where
  /-- The class membership predicate. -/
  Mem : {V : Type} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop
  /-- Heredity: an induced subgraph (along an embedding `H ↪g G`) of a member is a member. -/
  comap : ∀ {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
            {G : SimpleGraph V} {H : SimpleGraph W}, (H ↪g G) → Mem G → Mem H

/-- Every §5 `GraphClass` forgets to a `HeredClass`. -/
def GraphClass.toHeredClass (gc : GraphClass) : HeredClass where
  Mem := gc.Mem
  comap := gc.comap

/-! ## The underlying-graph membership predicate (mirrors `GraphClassConstraint`) -/

/-- Membership of the underlying graph of an unlabelled flag in the class. -/
def HeredClass.underlyingMem (hc : HeredClass) {V : Type} [Fintype V] [DecidableEq V] :
    Flag ∅ₜ V → Prop :=
  Quotient.lift (fun G : LabeledGraph ∅ₜ V => hc.Mem G.graph)
    (by
      intro G G' h
      obtain ⟨φ⟩ := h
      have hiso : G.graph ≃g G'.graph := φ.graph_iso
      apply propext
      exact ⟨fun hG => hc.comap hiso.symm.toEmbedding hG,
             fun hG' => hc.comap hiso.toEmbedding hG'⟩)

@[simp]
lemma HeredClass.underlyingMem_mk (hc : HeredClass) {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph ∅ₜ V) : hc.underlyingMem (⟦G⟧ : Flag ∅ₜ V) = hc.Mem G.graph := rfl

lemma HeredClass.underlyingMem_unlabel_mk (hc : HeredClass) {V : Type} [Fintype V] [DecidableEq V]
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} (G : LabeledGraph σ V) :
    hc.underlyingMem (unlabel (⟦G⟧ : Flag σ V)) = hc.Mem G.graph := by
  show hc.underlyingMem (unlabeledGraphQuot G) = hc.Mem G.graph
  rfl

/-! ## The constraint -/

/-- The constraint built from a hereditary class: a flag is forbidden iff its underlying graph
leaves the class. -/
def HeredClass.constraintOf (hc : HeredClass) {n₀ : ℕ} (σ : FlagType (Fin n₀)) : Constraint σ where
  forbσ F := ¬ hc.underlyingMem (unlabel F.2)
  forb0 D := ¬ hc.underlyingMem D.2
  unlabel_forb := fun F hF => hF

/-! ## The two consumption lemmas -/

/-- **F1 (self-forbidding ⟹ in class).**  A flag whose density of every forbidden flag is zero has
its underlying graph in the class. -/
theorem HeredClass.mem_of_forbiddenFree (hc : HeredClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {N : ℕ} (G : LabeledGraph σ (Fin N))
    (hff : ∀ F : FinFlag σ, (hc.constraintOf σ).forbσ F →
        flagDensity₁ F.2 (⟦G⟧ : Flag σ (Fin N)) = 0) :
    hc.Mem G.graph := by
  by_contra hG
  set F : FinFlag σ := ⟨N, (⟦G⟧ : Flag σ (Fin N))⟩ with hF
  have hforb : (hc.constraintOf σ).forbσ F := by
    show ¬ hc.underlyingMem (unlabel (⟦G⟧ : Flag σ (Fin N)))
    rw [hc.underlyingMem_unlabel_mk]; exact hG
  have hzero := hff F hforb
  have hone : flagDensity₁ (⟦G⟧ : Flag σ (Fin N)) (⟦G⟧ : Flag σ (Fin N)) = 1 :=
    flagDensity_self _
  rw [hF] at hzero
  simp only at hzero
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- **F2 (in class ⟹ forbidden-free).**  A graph `H` in the class has zero density of every
forbidden unlabelled flag `D`. -/
theorem HeredClass.forbiddenFree_of_mem (hc : HeredClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {N : ℕ} (Hgr : SimpleGraph (Fin N)) (hH : hc.Mem Hgr)
    (D : FinFlag ∅ₜ) (hD : (hc.constraintOf σ).forb0 D) :
    flagDensity₁ D.2 (graphFlag Hgr) = 0 := by
  by_contra hne
  set Hrep : LabeledGraph ∅ₜ (Fin N) :=
    {graph := Hgr, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj Hgr.Adj} with hHrep
  set Drep : LabeledGraph ∅ₜ (Fin D.1) := D.2.out with hDrep
  have hD2 : D.2 = (⟦Drep⟧ : Flag ∅ₜ (Fin D.1)) := (Quotient.out_eq D.2).symm
  have hgraphFlag : graphFlag Hgr = (⟦Hrep⟧ : Flag ∅ₜ (Fin N)) := rfl
  rw [hD2, hgraphFlag] at hne
  obtain ⟨f⟩ := exists_graph_embedding_of_flagDensity₁_ne_zero Drep Hrep hne
  have hmem : hc.Mem Drep.graph := hc.comap f hH
  apply hD
  rw [hD2]
  show hc.underlyingMem (⟦Drep⟧ : Flag ∅ₜ (Fin D.1))
  rw [hc.underlyingMem_mk]
  exact hmem

end FlagAlgebras.MetaTheory
