import LeanFlagAlgebras.MetaTheory.InducedContainment
import LeanFlagAlgebras.MetaTheory.SupportClosure

/-! # Hereditary graph classes — the shared class framework (paper §3, §5–§7)

A **hereditary graph class** is a membership predicate on finite simple graphs that is closed under
taking induced subgraphs.  This is the common base shared by every constrained class in the
development:

* §5's clone-closed classes ([`GraphClass`](./GraphClassConstraint.lean)) add closure under
  *independent* blow-ups;
* §6's true-clone-closed and §7's substitution-closed classes
  ([`TrueClone`](./TrueClone.lean) / [`Substitution`](./Substitution.lean)) add their own closure
  operations — and cluster graphs ([`ClusterGraph`](./ClusterGraph.lean)) are hereditary yet *not*
  clone-closed, which is exactly why heredity must be separated from any closure assumption.

The data here is closure-agnostic and reused by all of them:

* `graphFlag G` — a graph viewed as an unlabelled (`∅ₜ`) flag.
* `HeredClass` — the membership predicate `Mem` together with its heredity `comap`.
* `HeredClass.constraintOf` — the [`Constraint`](./SupportClosure.lean) whose forbidden flags are
  exactly those whose underlying graph leaves the class.
* `HeredClass.mem_of_forbiddenFree` (F1) — a flag with zero density of every forbidden flag has its
  underlying graph in the class (via `flagDensity_self = 1`).
* `HeredClass.forbiddenFree_of_mem` (F2) — a graph in the class has zero density of every forbidden
  flag (via the containment bridge + `comap`).

These two consumption lemmas are the entire interface the root-plantability capstones consume from a
class; they never mention any closure operation, so they live here once and serve §5, §6 and §7.
-/

open FlagAlgebras

namespace FlagAlgebras.MetaTheory

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-! ## A graph as an unlabelled flag -/

/-- The unlabelled flag of a graph `G`: the underlying graph viewed as an `∅ₜ`-flag, with the
empty type embedding. -/
def graphFlag {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Flag ∅ₜ V :=
  ⟦{graph := G, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj}⟧

/-! ## The hereditary-class structure -/

/-- A **hereditary graph class**: a membership predicate on finite simple graphs that is preserved
under taking induced subgraphs (along any graph embedding).  No blow-up/closure assumption — those
are added by the structures and predicates that build on this one (`GraphClass`, `TrueCloneClosed`,
`SubstitutionClosed`). -/
structure HeredClass where
  /-- The class membership predicate. -/
  Mem : {V : Type} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop
  /-- Heredity: an induced subgraph (along an embedding `H ↪g G`) of a member is a member. -/
  comap : ∀ {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
            {G : SimpleGraph V} {H : SimpleGraph W}, (H ↪g G) → Mem G → Mem H

/-! ## The underlying-graph membership predicate -/

/-- Membership of the underlying graph of an unlabelled flag in the class, lifted from
representatives.  Well-defined because a labeled-graph iso gives a graph iso in both directions, and
`comap` transports membership along the resulting embeddings. -/
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

/-- `unlabel` preserves the underlying graph: the underlying-class membership of a `σ`-flag's
unlabelling agrees with applying `underlyingMem` to the flag's underlying graph. -/
lemma HeredClass.underlyingMem_unlabel_mk (hc : HeredClass) {V : Type} [Fintype V] [DecidableEq V]
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} (G : LabeledGraph σ V) :
    hc.underlyingMem (unlabel (⟦G⟧ : Flag σ V)) = hc.Mem G.graph := by
  show hc.underlyingMem (unlabeledGraphQuot G) = hc.Mem G.graph
  rfl

/-! ## The constraint -/

/-- The constraint built from a hereditary class: a `σ`-flag (resp. an unlabelled flag) is forbidden
iff its underlying graph leaves the class.  The unlabelling link holds because `unlabel` preserves
the underlying graph. -/
def HeredClass.constraintOf (hc : HeredClass) {n₀ : ℕ} (σ : FlagType (Fin n₀)) : Constraint σ where
  forbσ F := ¬ hc.underlyingMem (unlabel F.2)
  forb0 D := ¬ hc.underlyingMem D.2
  unlabel_forb := fun _ hF => hF

/-! ## The two consumption lemmas -/

/-- **F1 (self-forbidding ⟹ in class).**  A `σ`-flag (a labeled graph on `Fin N`) whose density of
every forbidden flag is zero has its underlying graph in the class. -/
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

/-- **F2 (in class ⟹ forbidden-free).**  A graph `Hgr` in the class has zero density of every
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
