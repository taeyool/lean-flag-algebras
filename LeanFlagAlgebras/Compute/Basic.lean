-- flagDensity₁ : Flag σ U → Flag σ W → ℚ @ SubflagListDensity.lean L371
-- flagListDensity : FlagList σ t Vl → Flag σ W → ℚ @ SubflagListDensity.lean L304
-- quotLabeledSubgraphListDensity : QuotLabeledGraphList σ t Vl → Flag σ W → ℚ @ SubflagListDensity.lean L289
-- labledSubgraphListDensityLifted : LabeledGraphList σ t Vl → Flag σ W → ℚ @ SubflagListDensity.lean L271
-- labeledSubgraphListCount : LabeledGraphList σ t Vl → LabeledGraph σ W → ℕ @ SubflagListDensity.lean L59
-- setOfLabeledSubgraphListIsoHl : (G : LabeledGraph σ U) → LabeledGraphList σ t Vl → Set (LabeledSubgraphList σ t G) @ SubflagListDensity.lean L54
-- predIsoLabeledHl : LabeledGraph σ V → LabeledGraphList σ t Vl → LabeledSubgraphList σ t G → Prop @ SubflagListDensity.lean L47
-- predDisjointLabeledSubgraphList : LabeledSubgraphList σ t G → Prop @ SubflagListDensity.lean L42
-- FlagList : (Vl : Fin t → Type) → ∀ i, Flag σ (Vl i) @ FlagDef.lean L739
-- flagToList : Flag σ V → FlagList σ 1 (fun _ ↦ V) @ FlagDef.lean L758
-- Flag : FlagType T → Type → Type @ FlagDef.lean L560
-- labeledGraphSetoid : (σ : FlagType T) → (V : Type) → Setoid (LabeledGraph σ V) @ FlagDef.lean L550
-- LabeledGraph : (σ : FlagType T) → (V : Type) → LabeledGraph σ V @ FlagDef.lean L20
-- flagEqv : LabeledGraph σ V → LabeledGraph σ V → Prop @ FlagDef.lean L518 
-- LabeledGraphIso : (G : LabeledGraph σ V) → (G' : LabeledGraph σ W) → LabeledGraphIso G G' @ FlagDef.lean L307
-- FlagType := SimpleGraph @ FlagDef.lean L13

import Mathlib

/-!
This file along with other files in the `Compute` directory will work on computable version of flag algebra.
-/

namespace Compute

instance
    {V : Type*} [DecidableEq V] [Fintype V]
    {W : Type*} [DecidableEq W] [Fintype W] :
    Fintype (V ↪ W) where
  elems := ((@Finset.univ (V → W)).filterMap fun f ↦
    if h : Function.Injective f
    then Option.some ⟨f, h⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.toFun, e.inj'

instance
    {V : Type*} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
    Fintype (G₁ ↪g G₂) where
  elems := ((@Finset.univ (V ↪ W)).filterMap fun e ↦
    if h : ∀ u v, G₂.Adj (e u) (e v) ↔ G₁.Adj u v
    then Option.some ⟨e, h _ _⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.toEmbedding, fun _ _ ↦ e.map_rel_iff

instance
    {V : Type*} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
    DecidableEq (G₁ ↪g G₂) := fun e f ↦
  if h : ∀ g, e g = f g
  then .isTrue (by ext; exact h _)
  else .isFalse (by rintro rfl; exact h (fun _ ↦ rfl))

instance
    {V : Type*} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
    Fintype (G₁ ≃g G₂) where
  elems := ((@Finset.univ (V ≃ W)).filterMap fun e ↦
      if h : ∀ u v, G₂.Adj (e u) (e v) ↔ G₁.Adj u v
      then Option.some ⟨e, h _ _⟩
      else Option.none) (by grind)
  complete e := by
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some,
      Option.some.injEq, true_and]
    use e.toEquiv, fun _ _ ↦ e.map_rel_iff

instance
    {V : Type*} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
    DecidableEq (G₁ ≃g G₂) := fun e f ↦
  if h : ∀ g, e g = f g
  then .isTrue (by ext; exact h _)
  else .isFalse (by rintro rfl; exact h (fun _ ↦ rfl))

example : (@Finset.univ ((SimpleGraph.completeGraph (Fin 3)) ≃g (SimpleGraph.completeGraph (Fin 3)))).card = 6 := by decide

/-- A labeled graph is a `SimpleGraph` with a homomorphism from `σ`. -/
structure LabeledGraph {T : Type*} (σ : SimpleGraph T) (V : Type*) where
  /-- The underlying graph. -/
  graph : SimpleGraph V
  /-- The homomorphism from `σ` to `graph`. -/
  type_embed : σ ↪g graph

/-- Isomorphism between `LabeledGraph`s. -/
@[ext]
structure LabeledGraphIso
    {T : Type*} {σ : SimpleGraph T}
    {V : Type*} (G : LabeledGraph σ V)
    {W : Type*} (G' : LabeledGraph σ W) where
  /-- Isomorphism of `LabeledGraph`s are isomorphisms of underlying graphs. -/
  graph_iso : G.graph ≃g G'.graph
  /-- Isomorphism of `LabeledGraph`s preserves flag types up to given graph isomorphism. -/
  type_preserve : graph_iso ∘ G.type_embed = G'.type_embed

@[inherit_doc] infix:50 " ≃f " => LabeledGraphIso

instance
    {T : Type*} {σ : SimpleGraph T}
    {V : Type*} {G : LabeledGraph σ V}
    {W : Type*} {G' : LabeledGraph σ W} :
    FunLike (G ≃f G') V W where
  coe e := e.graph_iso
  coe_injective' _ _ h := LabeledGraphIso.ext <| DFunLike.coe_fn_eq.mp h

instance
    {T : Type*} [Fintype T] {σ : SimpleGraph T}
    {V : Type*} [DecidableEq V] [Fintype V] (G : LabeledGraph σ V) [DecidableRel G.graph.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] (G' : LabeledGraph σ W) [DecidableRel G'.graph.Adj] :
    Fintype (G ≃f G') where
  elems := ((@Finset.univ (G.graph ≃g G'.graph)).filterMap fun e ↦
    if h : e.toFun ∘ G.type_embed = G'.type_embed
    then Option.some ⟨e, h⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Finset.mem_filterMap, Finset.mem_univ,
      Option.dite_none_right_eq_some, Option.some.injEq, true_and]
    use e.graph_iso, e.type_preserve

instance
    {T : Type*} {σ : SimpleGraph T}
    {V : Type*} [Fintype V] {G : LabeledGraph σ V}
    {W : Type*} [DecidableEq W] {G' : LabeledGraph σ W} :
    DecidableEq (G ≃f G') := fun e f ↦
  if h : e.graph_iso = f.graph_iso
  then .isTrue <| LabeledGraphIso.ext h
  else .isFalse (h <| · ▸ rfl)

/-- A flag. -/
structure Flag {T : Type*} (σ : SimpleGraph T) (V : Type*) where
  /-- A partition corresponding to the flag. -/
  flagPartition : Set (LabeledGraph σ V)
  /-- Partition is nonempty. -/
  flagPartition_nonempty : flagPartition.Nonempty
  /-- Partition contains all elements of the **__**. -/
  flagPartition_complete {G : LabeledGraph σ V} (hG : G ∈ flagPartition) :
    ∀ ⦃G' : LabeledGraph σ V⦄, G' ∈ flagPartition ↔ Nonempty (G ≃f G')

/-- A `FlagList`. -/
abbrev FlagList
    {T : Type*} (σ : SimpleGraph T) {t : ℕ} (Vl : Fin t → Type*) :=
    (i : Fin t) → Flag σ (Vl i)

/-- A `LabeledGraphList`. -/
abbrev LabeledGraphList
    {T : Type*} (σ : SimpleGraph T) {t : ℕ} (Vl : Fin t → Type*) :=
  (i : Fin t) → LabeledGraph σ (Vl i)

/-- A `LabeledGraphToList`. -/
def labeledGraphToList {T : Type*} {σ : SimpleGraph T} {V : Type*} (G : LabeledGraph σ V) :
    LabeledGraphList σ fun _ : Fin 1 ↦ V :=
  fun _ ↦ G

@[ext]
structure LabeledSubgraph
    {T : Type*} (σ : SimpleGraph T)
    {V : Type*} (G : LabeledGraph σ V) where
  subgraph : G.graph.Subgraph
  type_embed : σ ↪g subgraph.coe
  embed_eq : ∀ (t : T), type_embed t = G.type_embed t

instance
    {T : Type*} [Fintype T] {σ : SimpleGraph T}
    {V : Type*} [DecidableEq V] [Fintype V] {G : LabeledGraph σ V} [DecidableRel G.graph.Adj] :
    Fintype (LabeledSubgraph σ G) where
  elems :=
    let subgraphs := (@Finset.univ G.graph.Subgraph _)
    let embeddings := subgraphs.biUnion fun x ↦ (@Finset.univ (σ ↪g x) _)
    sorry
  complete := sorry

abbrev LabeledSubgraphList (σ : SimpleGraph T) (t : ℕ) (G : LabeledGraph σ U)
  := Fin t → LabeledSubgraph σ G

def LabeledSubgraph.IsInduced {σ : SimpleGraph T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : Prop
  :=
  H.subgraph.IsInduced

def LabeledSubgraphList.IsInduced
    {σ : SimpleGraph T} {t : ℕ} {G : LabeledGraph σ U} (Hl : LabeledSubgraphList σ t G) : Prop
  := ∀ (i : Fin t), (Hl i).IsInduced

-- def predDisjointLabeledSubgraphList
--     {σ : SimpleGraph T} {G : LabeledGraph σ V} (Gl : LabeledSubgraphList σ t G) : Prop
--   :=
--   ∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅
-- 
-- def predIsoLabeledHl
--     {σ : FlagType T} (G : LabeledGraph σ V) (Hl : LabeledGraphList σ t Vl)
--     : LabeledSubgraphList σ t G → Prop
--   := fun Gl ↦
--       (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i))
--       ∧ predDisjointLabeledSubgraphList Gl
-- 
-- 

-- abbrev FlagType := SimpleGraph
-- def flagEqv {σ : FlagType T} (G G' : LabeledGraph σ V) : Prop := Nonempty (G ≃f G')
-- def Flag {T : Type u} (σ : FlagType T) (V : Type v) := Quotient (labeledGraphSetoid σ V)
-- abbrev FlagList (σ : FlagType T) {t : ℕ} (Vl : Fin t → Type) := (i : Fin t) → Flag σ (Vl i)
-- def quotLabeledSubgraphListDensity (qlgl : QuotLabeledGraphList σ t Vl) (f : Flag σ W) : ℚ := sorry
-- def flagListDensity (fl : FlagList σ t Vl) (f : Flag σ W) : ℚ := sorry

end Compute

#min_imports
-- #lint
