import LeanFlagAlgebras.MetaTheory.InducedContainment
import LeanFlagAlgebras.MetaTheory.SupportClosure
import LeanFlagAlgebras.MetaTheory.Blowup

/-! # Graph-class constraints (paper §5, the hereditary clone-closed package)

A `GraphClass` packages a hereditary, clone-closed family of finite simple graphs:
membership is preserved under taking induced subgraphs (`comap`) and under independent
blow-ups (`clone_closed`).  From such a class we synthesise a `Constraint` (the data the
support-closure capstone consumes), whose forbidden flags/graphs are exactly the ones whose
underlying graph leaves the class.

The two *consumption lemmas* the capstone needs are (`F1`/`F2` are this file's own mnemonics, not
paper labels):

* `mem_of_forbiddenFree` (F1): a `σ`-flag that has zero density of every forbidden flag has
  its underlying graph in the class.
* `forbiddenFree_of_mem` (F2): a graph in the class has zero density of every forbidden
  unlabelled flag.

Finally `cliqueFreeClass r` instantiates the framework with the `K_r`-free class, using
`SimpleGraph.CliqueFree.comap` (heredity) and `cliqueFree_independentBlowup` (clone-closure).
-/

open FlagAlgebras

namespace FlagAlgebras.MetaTheory

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-! ## The graph-class structure -/

/-- A hereditary, clone-closed graph class: a membership predicate on finite simple graphs
that is preserved under taking induced subgraphs (along any graph embedding) and under
independent blow-ups. -/
structure GraphClass where
  /-- The class membership predicate. -/
  Mem : {V : Type} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop
  /-- Heredity: an induced subgraph (along an embedding `H ↪g G`) of a member is a member. -/
  comap : ∀ {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
            {G : SimpleGraph V} {H : SimpleGraph W}, (H ↪g G) → Mem G → Mem H
  /-- Clone-closure: independent blow-ups of a member are members. -/
  clone_closed : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (m : V → ℕ),
            Mem G → Mem (independentBlowup G m)

/-! ## The underlying-graph membership predicate -/

variable {n₀ : ℕ}

/-- The unlabelled flag of a graph `G`: the underlying graph viewed as an `∅ₜ`-flag, with the
empty type embedding. -/
def graphFlag {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Flag ∅ₜ V :=
  ⟦{graph := G, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj}⟧

/-- Membership of the underlying graph of an unlabelled flag in the class, lifted from
representatives.  Well-defined because a labeled-graph iso gives a graph iso in both
directions, and `gc.comap` transports membership along the resulting embeddings. -/
def underlyingMem (gc : GraphClass) {V : Type} [Fintype V] [DecidableEq V] :
    Flag ∅ₜ V → Prop :=
  Quotient.lift (fun G : LabeledGraph ∅ₜ V => gc.Mem G.graph)
    (by
      intro G G' h
      obtain ⟨φ⟩ := h
      have hiso : G.graph ≃g G'.graph := φ.graph_iso
      apply propext
      constructor
      · intro hG
        exact gc.comap hiso.symm.toEmbedding hG
      · intro hG'
        exact gc.comap hiso.toEmbedding hG')

@[simp]
lemma underlyingMem_mk (gc : GraphClass) {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph ∅ₜ V) : underlyingMem gc (⟦G⟧ : Flag ∅ₜ V) = gc.Mem G.graph := rfl

/-- `unlabel` preserves the underlying graph: the underlying-class membership of a `σ`-flag's
unlabelling agrees with applying `underlyingMem` to the flag's unlabelling. -/
lemma underlyingMem_unlabel_mk (gc : GraphClass) {V : Type} [Fintype V] [DecidableEq V]
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} (G : LabeledGraph σ V) :
    underlyingMem gc (unlabel (⟦G⟧ : Flag σ V)) = gc.Mem G.graph := by
  show underlyingMem gc (unlabeledGraphQuot G) = gc.Mem G.graph
  rfl

/-! ## The constraint -/

/-- The constraint built from a graph class: a `σ`-flag (resp. an unlabelled flag) is
forbidden iff its underlying graph leaves the class.  The unlabelling link holds because
`unlabel` preserves the underlying graph. -/
def constraintOf (gc : GraphClass) {n₀ : ℕ} (σ : FlagType (Fin n₀)) : Constraint σ where
  forbσ F := ¬ underlyingMem gc (unlabel F.2)
  forb0 D := ¬ underlyingMem gc D.2
  unlabel_forb := by
    intro F hF
    -- `forb0 ⟨F.1, unlabel F.2⟩` is `¬ underlyingMem gc (unlabel F.2)`, definitionally `forbσ F`.
    exact hF

/-! ## The two consumption lemmas -/

/-- **F1 (self-forbidding ⟹ in class).**  A `σ`-flag (here a labeled graph on `Fin N`) whose
density of every forbidden flag is zero has its underlying graph in the class. -/
theorem mem_of_forbiddenFree (gc : GraphClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {N : ℕ} (G : LabeledGraph σ (Fin N))
    (hff : ∀ F : FinFlag σ, (constraintOf gc σ).forbσ F →
        flagDensity₁ F.2 (⟦G⟧ : Flag σ (Fin N)) = 0) :
    gc.Mem G.graph := by
  by_contra hG
  -- View `⟦G⟧` as a `FinFlag σ` and feed it to `hff`.
  set F : FinFlag σ := ⟨N, (⟦G⟧ : Flag σ (Fin N))⟩ with hF
  have hforb : (constraintOf gc σ).forbσ F := by
    show ¬ underlyingMem gc (unlabel (⟦G⟧ : Flag σ (Fin N)))
    rw [underlyingMem_unlabel_mk]
    exact hG
  have hzero := hff F hforb
  -- but the density of a flag in itself is `1`
  have hone : flagDensity₁ (⟦G⟧ : Flag σ (Fin N)) (⟦G⟧ : Flag σ (Fin N)) = 1 :=
    flagDensity_self _
  rw [hF] at hzero
  simp only at hzero
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- **F2 (in class ⟹ forbidden-free).**  A graph `H` in the class has zero density of every
forbidden unlabelled flag `D`. -/
theorem forbiddenFree_of_mem (gc : GraphClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {N : ℕ} (H : SimpleGraph (Fin N)) (hH : gc.Mem H)
    (D : FinFlag ∅ₜ) (hD : (constraintOf gc σ).forb0 D) :
    flagDensity₁ D.2 (graphFlag H) = 0 := by
  by_contra hne
  -- Write both sides as quotients of explicit labeled graphs.
  set Hrep : LabeledGraph ∅ₜ (Fin N) :=
    {graph := H, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj H.Adj} with hHrep
  set Drep : LabeledGraph ∅ₜ (Fin D.1) := D.2.out with hDrep
  have hD2 : D.2 = (⟦Drep⟧ : Flag ∅ₜ (Fin D.1)) := (Quotient.out_eq D.2).symm
  have hgraphFlag : graphFlag H = (⟦Hrep⟧ : Flag ∅ₜ (Fin N)) := rfl
  rw [hD2, hgraphFlag] at hne
  -- positive density yields a graph embedding `Drep.graph ↪g Hrep.graph = H`
  obtain ⟨f⟩ := exists_graph_embedding_of_flagDensity₁_ne_zero Drep Hrep hne
  -- so `Drep.graph` is in the class by heredity
  have hmem : gc.Mem Drep.graph := gc.comap f hH
  -- contradicting that `D` is forbidden
  apply hD
  rw [hD2]
  show underlyingMem gc (⟦Drep⟧ : Flag ∅ₜ (Fin D.1))
  rw [underlyingMem_mk]
  exact hmem

/-! ## The `K_r`-free instance -/

/-- The class of `K_r`-free graphs as a `GraphClass`: heredity is
`SimpleGraph.CliqueFree.comap`, clone-closure is `cliqueFree_independentBlowup`. -/
def cliqueFreeClass (r : ℕ) : GraphClass where
  Mem {_V} _ _ G := G.CliqueFree r
  comap f hG := hG.comap f
  clone_closed G m hG := cliqueFree_independentBlowup G m hG

end FlagAlgebras.MetaTheory
