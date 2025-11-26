import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Perm

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

instance instGraphEmbeddingFintype
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

structure LabeledGraph.LabeledSubgraph
    {T : Type*} {σ : SimpleGraph T} {V : Type*} (G : LabeledGraph σ V) where
  subgraph : G.graph.Subgraph
  type_embed : σ ↪g subgraph.coe
  embed_eq : ∀ (t : T), type_embed t = G.type_embed t

@[ext]
theorem LabeledGraph.LabeledSubgraph.ext
    {T : Type*} {σ : SimpleGraph T} {V : Type*} {G : LabeledGraph σ V}
    (H₁ H₂ : G.LabeledSubgraph) (h₁ : H₁.subgraph = H₂.subgraph) (h₂ : ∀ x, (H₁.type_embed x : V) = H₂.type_embed x) :
    H₁ = H₂ := by
  rcases H₁; rcases H₂; rcases h₁
  simp_all only [LabeledGraph.LabeledSubgraph.mk.injEq, true_and]
  rw [heq_eq_eq]
  ext
  grind only

instance
    {V : Type*} [Fintype V]
    {G : SimpleGraph V}
    {H₁ : G.Subgraph} [DecidableRel H₁.Adj] [DecidablePred (· ∈ H₁.verts)]
    {H₂ : G.Subgraph} [DecidableRel H₂.Adj] [DecidablePred (· ∈ H₂.verts)] :
    Decidable (H₁ = H₂) :=
  if h₁ : (∀ v : V, v ∈ H₁.verts ↔ v ∈ H₂.verts) ∧ (∀ u v, H₁.Adj u v ↔ H₂.Adj u v)
  then .isTrue (by ext <;> simp only [h₁])
  else .isFalse (by rintro rfl; simp_all only [implies_true, and_self, not_true_eq_false])

instance
    {T V : Type*} [Fintype T] [DecidableEq V] {σ : SimpleGraph T}
    {G : LabeledGraph σ V} [DecidableEq G.graph.Subgraph] :
    DecidableEq (G.LabeledSubgraph) := fun H₁ H₂ ↦
  if h₁ : H₁.subgraph = H₂.subgraph ∧ ∀ ⦃x⦄, (H₁.type_embed x : V) = H₂.type_embed x
  then .isTrue (by ext <;> simp_all only)
  else .isFalse (by rintro rfl; simp_all)

-- SimpleGraph.Subgraph.instFintypeOfDecidableEqOfDecidableRelAdj
instance
    {T V : Type*} [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V]
    {σ : SimpleGraph T} [DecidableRel σ.Adj]
    {G : LabeledGraph σ V} [DecidableEq G.graph.Subgraph] [DecidableRel G.graph.Adj]
    [∀ H : G.graph.Subgraph, Fintype H.verts] [∀ H : G.graph.Subgraph, DecidableRel H.Adj] :
    Fintype G.LabeledSubgraph where
  elems := (Finset.univ (α := G.graph.Subgraph)).biUnion fun H ↦
    ((@Finset.univ (σ ↪g H.coe) instGraphEmbeddingFintype).filterMap fun e ↦
      if h : ∀ x, e x = G.type_embed x
      then .some ⟨H, e, h⟩
      else .none) (by grind)
  complete e := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filterMap,
      Option.dite_none_right_eq_some, Option.some.injEq, true_and]
    use e.subgraph, e.type_embed
    simp only [exists_prop, and_true, e.embed_eq, implies_true]

def LabeledGraph.LabeledSubgraph.coe
    {T : Type*} {σ : SimpleGraph T} {V : Type*} {G : LabeledGraph σ V} (H : G.LabeledSubgraph) :
    LabeledGraph σ H.subgraph.verts where
  graph := H.subgraph.coe
  type_embed := H.type_embed

instance {V : Type*} {G : SimpleGraph V} {H : G.Subgraph} [DecidableRel H.Adj] :
    DecidableRel H.coe.Adj := fun u v ↦
  if h : H.Adj u.val v.val then .isTrue h else .isFalse h

instance
    {T : Type*} [Fintype T] {σ : SimpleGraph T}
    {V : Type*} [DecidableEq V] {G : LabeledGraph σ V}
    {H : G.LabeledSubgraph} [Fintype H.subgraph.verts] [DecidableRel H.subgraph.Adj]
    {W : Type*} [DecidableEq W] [Fintype W] {G' : LabeledGraph σ W} [DecidableRel G'.graph.Adj] :
    Fintype (H.coe ≃f G') where
  elems := ((@Finset.univ (H.subgraph.coe ≃g G'.graph)).filterMap fun e ↦
    if h : e.toFun ∘ H.type_embed = G'.type_embed
    then Option.some ⟨e, h⟩
    else Option.none) (by grind)
  complete e := by
    simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Finset.mem_filterMap, Finset.mem_univ,
      Option.dite_none_right_eq_some, Option.some.injEq, true_and]
    use e.graph_iso, e.type_preserve

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

def LabeledGraph.typeVerts
    {T : Type*} {σ : SimpleGraph T} {V : Type*} (G : LabeledGraph σ V) :
    Set V :=
  G.type_embed '' Set.univ

instance {T V : Type*} [Fintype T] [DecidableEq V] {σ : SimpleGraph T} {G : LabeledGraph σ V} :
    DecidablePred (· ∈ G.typeVerts) := fun x ↦
  if h : ∃ y, G.type_embed y = x
  then .isTrue (by simp [LabeledGraph.typeVerts, h])
  else .isFalse (by simp [LabeledGraph.typeVerts, h])

def LabeledGraph.typeVerts'
    {T : Type*} [Fintype T] {σ : SimpleGraph T} {V : Type*} [DecidableEq V] (G : LabeledGraph σ V) :
    Finset V :=
  Finset.univ.image G.type_embed

theorem LabeledGraph.mem_typeVerts_iff_mem_typeVerts'
    {T : Type*} [Fintype T] {σ : SimpleGraph T} {V : Type*} [DecidableEq V] {G : LabeledGraph σ V} {v : V} :
    v ∈ G.typeVerts ↔ v ∈ G.typeVerts' := by
  simp [typeVerts, typeVerts']

abbrev LabeledGraph.LabeledSubgraphList
    {T U : Type*} {σ : SimpleGraph T} (t : ℕ) (G : LabeledGraph σ U)
  := Fin t → G.LabeledSubgraph

-- instance
--     {T U : Type*} [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U]
--     {σ : SimpleGraph T} [DecidableRel σ.Adj]
--     {t : ℕ} {G : LabeledGraph σ U} [DecidableEq G.graph.Subgraph] [DecidableRel G.graph.Adj]
--     [∀ H : G.graph.Subgraph, Fintype H.verts] [∀ H : G.graph.Subgraph, DecidableRel H.Adj] :
--     Fintype (G.LabeledSubgraphList t) :=
--   inferInstance

def LabeledGraph.LabeledSubgraph.IsInduced
    {T : Type*} {σ : SimpleGraph T}
    {V : Type*} {G : LabeledGraph σ V} (H : G.LabeledSubgraph) : Prop :=
  H.subgraph.IsInduced

-- instance
--     {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
--     {H : G.Subgraph} [DecidablePred (· ∈ H.verts)] [DecidableRel H.Adj] :
--     Decidable H.IsInduced :=
--   if h : ∀ ⦃v⦄, v ∈ H.verts → ∀ ⦃w⦄, w ∈ H.verts → G.Adj v w → H.Adj v w
--   then .isTrue h else .isFalse h
--
-- instance
--     {T : Type*} {σ : SimpleGraph T} {V : Type*} [Fintype V]
--     {G : LabeledGraph σ V} [DecidableRel G.graph.Adj]
--     {H : LabeledSubgraph σ G} [DecidablePred (· ∈ H.subgraph.verts)] [DecidableRel H.subgraph.Adj] :
--     Decidable H.IsInduced :=
--   if h : H.subgraph.IsInduced then .isTrue h else .isFalse h

def LabeledGraph.LabeledSubgraphList.IsInduced
    {T : Type*} {σ : SimpleGraph T} {t : ℕ} {U : Type*}
    {G : LabeledGraph σ U} (Hl : G.LabeledSubgraphList t) : Prop :=
  ∀ (i : Fin t), (Hl i).IsInduced

def predDisjointLabeledSubgraphList
    {T : Type*} {σ : SimpleGraph T} {V : Type*} {G : LabeledGraph σ V}
    {t : ℕ} (Gl : G.LabeledSubgraphList t) : Prop :=
  ∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts ⊆ G.typeVerts

def predIsoLabeledHl
    {T : Type*} {σ : SimpleGraph T} {V : Type*} {G : LabeledGraph σ V}
    {t : ℕ} {Vl : Fin t → Type*} (Hl : LabeledGraphList σ Vl) :
    G.LabeledSubgraphList t → Prop := fun Gl ↦
    (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i)) ∧ predDisjointLabeledSubgraphList Gl

instance
    {T V : Type*} [Fintype T] {σ : SimpleGraph T} [Fintype V] [DecidableEq V]
    {G : LabeledGraph σ V} [DecidablePred (· ∈ G.typeVerts)]
    {t : ℕ} {Vl : Fin t → Type*} [∀ i, Fintype (Vl i)] [∀ i, DecidableEq (Vl i)]
    {Hl : LabeledGraphList σ Vl} [∀ i, DecidableRel (Hl i).graph.Adj]
    {Gl : G.LabeledSubgraphList t} [∀ i, DecidablePred (· ∈ (Gl i).subgraph.verts)]
    [∀ i, Fintype (Gl i).subgraph.verts] [∀ i, DecidableRel (Gl i).subgraph.Adj] :
    Decidable (predIsoLabeledHl Hl Gl) :=
  if h₁ : ∀ i, (Finset.univ (α := (Gl i).coe ≃f Hl i)).Nonempty
  then
    if h₂ : ∀ i j, i ≠ j → ∀ {e}, e ∈ (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts → e ∈ G.typeVerts
    then .isTrue <| by
      refine ⟨fun i ↦ ?_, h₂⟩
      obtain ⟨x, -⟩ := h₁ i
      exact ⟨x⟩
    else .isFalse <| by
      simp only [predIsoLabeledHl]
      tauto
  else .isFalse <| by
    simp only [predIsoLabeledHl, not_and]
    intro h₂
    exfalso
    apply h₁
    simp

def setOfLabeledSubgraphListIsoHl
    {T : Type*} {σ : SimpleGraph T} {U : Type*} (G : LabeledGraph σ U)
    {t : ℕ} {Vl : Fin t → Type*} (Hl : LabeledGraphList σ Vl) :
    Set (G.LabeledSubgraphList t) :=
  { Gl | Gl.IsInduced ∧ predIsoLabeledHl Hl Gl }

/-- TODO: Check if instance cleanup is required. -/
def finsetOfLabeledSubgraphListIsoHl
    {T : Type*} [Fintype T] [DecidableEq T] {σ : SimpleGraph T} [DecidableRel σ.Adj]
    {U : Type*} [Fintype U] [DecidableEq U] (G : LabeledGraph σ U) [DecidableRel G.graph.Adj]
    {t : ℕ} {Vl : Fin t → Type*} [∀ i, Fintype (Vl i)]
    (Hl : LabeledGraphList σ Vl) [∀ i, DecidableRel (Hl i).graph.Adj]
    [∀ Gl : G.LabeledSubgraphList t, Decidable Gl.IsInduced]
    [∀ Gl : G.LabeledSubgraphList t, Decidable (predIsoLabeledHl Hl Gl)] :
    Finset (G.LabeledSubgraphList t) :=
  (Finset.univ (α := G.LabeledSubgraphList t)).filter fun Gl ↦
    Gl.IsInduced ∧ predIsoLabeledHl Hl Gl

-- def predDisjointLabeledSubgraphList
--     {σ : SimpleGraph T} {G : LabeledGraph σ V} (Gl : LabeledSubgraphList t G) : Prop
--   :=
--   ∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅
--
--
--

-- abbrev FlagType := SimpleGraph
-- def flagEqv {σ : FlagType T} (G G' : LabeledGraph σ V) : Prop := Nonempty (G ≃f G')
-- def Flag {T : Type u} (σ : FlagType T) (V : Type v) := Quotient (labeledGraphSetoid σ V)
-- abbrev FlagList (σ : FlagType T) {t : ℕ} (Vl : Fin t → Type) := (i : Fin t) → Flag σ (Vl i)
-- def quotLabeledSubgraphListDensity (qlgl : QuotLabeledGraphList σ t Vl) (f : Flag σ W) : ℚ := sorry
-- def flagListDensity (fl : FlagList σ t Vl) (f : Flag σ W) : ℚ := sorry

end Compute
