import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Perm

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
    {V : Type*} [Fintype V] {G₁ : SimpleGraph V}
    {W : Type*} [DecidableEq W] {G₂ : SimpleGraph W} :
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
    {V : Type*} [Fintype V] {G₁ : SimpleGraph V}
    {W : Type*} [DecidableEq W] {G₂ : SimpleGraph W} :
    DecidableEq (G₁ ≃g G₂) := fun e f ↦
  if h : ∀ g, e g = f g
  then .isTrue (by ext; exact h _)
  else .isFalse (by rintro rfl; exact h (fun _ ↦ rfl))

#check SimpleGraph.Subgraph.instFintypeOfDecidableEqOfDecidableRelAdj

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

@[symm]
def LabeledGraphIso.symm
    {T V W : Type*} {σ : SimpleGraph T} {G : LabeledGraph σ V} {H : LabeledGraph σ W} (h : G ≃f H) :
    H ≃f G where
  graph_iso := h.graph_iso.symm
  type_preserve := by funext; simp [← h.type_preserve]

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

/- -------------------------------------------------------------- -/

abbrev FlagType := SimpleGraph

noncomputable def FlagType.size {T : Type*} [Fintype T] (_ : FlagType T) : ℕ
  :=
  Fintype.card T

def flagEqv {σ : FlagType T} (G G' : LabeledGraph σ V) : Prop
  :=
  Nonempty (G ≃f G')

infixl:50 " ∼f " => flagEqv

def emptyType : FlagType (Fin 0) := SimpleGraph.emptyGraph (Fin 0)

notation "∅ₜ" => emptyType

theorem emptyType_size : ∅ₜ.size = 0 := by
  dsimp only [emptyType, SimpleGraph.emptyGraph_eq_bot, FlagType.size]
  simp only [Fintype.card_eq_zero]

variable {n₀ n : ℕ} {σ : FlagType (Fin n₀)}

instance :
    Fintype (LabeledGraph σ (Fin n)) where
  elems := ((@Finset.univ (SimpleGraph (Fin n))).sigma (fun G ↦ (@Finset.univ (σ ↪g G) _))).map
      (fun ⟨G, e⟩ ↦ { graph := G, type_embed := e }) (by grind)
  complete e := by
    sorry

instance
    (G : LabeledGraph σ (Fin n)) :
    DecidablePred fun (H : LabeledGraph σ (Fin n)) ↦ G.graph = H.graph ∧ G ∼f H
  := by
  sorry

def isoLabeledGraphSetWithSameGraph
    (G : LabeledGraph σ (Fin n)) : Finset (LabeledGraph σ (Fin n))
  :=
  { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H }

end Compute
