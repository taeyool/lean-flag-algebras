import «LeanFlagAlgebras».FlagAlgebra.FlagOperators
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Perm

namespace Archive.Compute

open FlagAlgebras
open SimpleGraph

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
    {V : Type} [DecidableEq V] [Fintype V] {G₁ : SimpleGraph V} [DecidableRel G₁.Adj]
    {W : Type} [DecidableEq W] [Fintype W] {G₂ : SimpleGraph W} [DecidableRel G₂.Adj] :
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
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V] (G : LabeledGraph σ V) [DecidableRel G.graph.Adj]
    {W : Type} [DecidableEq W] [Fintype W] (G' : LabeledGraph σ W) [DecidableRel G'.graph.Adj] :
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
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V] (G : LabeledGraph σ V) [DecidableRel G.graph.Adj]
    {W : Type} [DecidableEq W] [Fintype W] (G' : LabeledGraph σ W) [DecidableRel G'.graph.Adj] :
    Decidable (Nonempty (G ≃f G'))
  := by
  rw [← exists_true_iff_nonempty]
  exact Fintype.decidableExistsFintype

instance
    {T : Type} [Fintype T] {σ : SimpleGraph T}
    {V : Type} [DecidableEq V] [Fintype V]
    (G G' : LabeledGraph σ V) [DecidableRel G.graph.Adj] [DecidableRel G'.graph.Adj] :
    Decidable (G ∼f G')
  := by
  rw [flagEqv]
  infer_instance

@[ext]
structure Sym2LabeledGraph {T : Type} (σ : FlagType T) (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  edges_valid : ∀ e ∈ edges, ¬e.IsDiag
  type_embed : σ ↪g (fromEdgeSet (SetLike.coe edges))

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ} :
    Fintype (Sym2LabeledGraph σ n) where
  elems :=
    let S := (@Finset.univ (Finset (Sym2 (Fin n)))).sigma (fun E ↦ (@Finset.univ (σ ↪g fromEdgeSet (SetLike.coe E)) _))
    S.filterMap (fun ⟨E, emb⟩ ↦
      if hE : ∀ e ∈ E, ¬e.IsDiag
      then .some ⟨E, hE, emb⟩
      else .none) (by grind)
  complete e := by
    rcases e with ⟨E, hE, emb⟩
    simp_all

def Sym2LabeledGraph.type_verts
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Finset (Fin n)
  := by
  have : DecidablePred (Membership.mem (G.type_embed '' Set.univ)) := by
    intro i
    simp only [Set.image_univ, Set.mem_range]
    exact Fintype.decidableExistsFintype
  have : Fintype (G.type_embed '' Set.univ) := setFintype _
  exact (G.type_embed '' Set.univ).toFinset

theorem Sym2LabeledGraph.mem_type_verts
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n) (t : T) :
    G.type_embed t ∈ G.type_verts
  := by
  simp [type_verts]

def Sym2LabeledGraph.toLabeledGraph
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : LabeledGraph σ (Fin n)
  :=
  ⟨fromEdgeSet (SetLike.coe G.edges), G.type_embed⟩

theorem Sym2LabeledGraph.toLabeledGraph_type_embed_eq
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : Sym2LabeledGraph σ n) (t : T) :
    G.toLabeledGraph.type_embed t = G.type_embed t
  := by
  simp [Sym2LabeledGraph.toLabeledGraph]

theorem Sym2LabeledGraph.toLabeledGraph_type_verts_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    G.toLabeledGraph.type_verts = G.type_verts
  := by
  simp [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.type_verts, Sym2LabeledGraph.type_verts]

theorem Sym2LabeledGraph.toLabeledGraph_injective
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G₁ G₂ : Sym2LabeledGraph σ n)
    (h : G₁.toLabeledGraph = G₂.toLabeledGraph) :
    G₁ = G₂
  := by
  simp only [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.mk.injEq] at h
  obtain ⟨h_graph, h_type_embed⟩ := h
  ext e
  · have h : (fromEdgeSet G₁.edges).edgeSet = SetLike.coe G₁.edges := by
      simp only [edgeSet_fromEdgeSet, sdiff_eq_left]
      refine Set.disjoint_left.mpr ?_
      intro e' he'
      simp only [Sym2.mem_diagSet_iff_isDiag]
      exact G₁.edges_valid e' he'
    simp only [h_graph, edgeSet_fromEdgeSet] at h
    have h_edges : SetLike.coe G₁.edges = SetLike.coe G₂.edges := by
      rw [← h]
      simp only [sdiff_eq_left]
      refine Set.disjoint_left.mpr ?_
      intro e' he'
      simp only [Sym2.mem_diagSet_iff_isDiag]
      exact G₂.edges_valid e' he'
    exact Eq.to_iff (congrFun h_edges e)
  · exact h_type_embed

theorem Sym2LabeledGraph.toLabeledGraph_adj_iff
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : Sym2LabeledGraph σ n) (u v : Fin n) :
    G.toLabeledGraph.graph.Adj u v ↔ Sym2.mk (u, v) ∈ G.edges
  := by
  simp [Sym2LabeledGraph.toLabeledGraph, fromEdgeSet]
  intro h
  exact G.edges_valid (Sym2.mk (u, v)) h

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    DecidableRel G.toLabeledGraph.graph.Adj
  := by
  intro a b
  rw [G.toLabeledGraph_adj_iff]
  exact Finset.decidableMem s(a, b) G.edges

end Archive.Compute

namespace FlagAlgebras
open Archive.Compute

noncomputable def LabeledGraph.toSym2LabeledGraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledGraph σ (Fin n)) : Sym2LabeledGraph σ n where
  edges := by
    have : Fintype G.graph.edgeSet := Fintype.ofFinite G.graph.edgeSet
    exact (SimpleGraph.edgeSet G.graph).toFinset
  edges_valid := by
    intro e he
    simp only [Set.mem_toFinset] at he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G.graph he
  type_embed := by
    simp only [Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
    exact G.type_embed

theorem LabeledGraph.toSym2LabeledGraph_toLabeledGraph_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledGraph σ (Fin n)) :
    G.toSym2LabeledGraph.toLabeledGraph = G
  := by
  simp only [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.toSym2LabeledGraph]
  congr
  · simp only [Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
  · simp only [eq_mpr_eq_cast, cast_heq]

end FlagAlgebras

namespace Archive.Compute
open FlagAlgebras
open SimpleGraph

theorem Sym2LabeledGraph.toLabeledGraph_toSym2LabeledGraph_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    G.toLabeledGraph.toSym2LabeledGraph = G
  := by
  simp only [Sym2LabeledGraph.toLabeledGraph, LabeledGraph.toSym2LabeledGraph]
  congr
  · simp only [edgeSet_fromEdgeSet, Set.toFinset_diff, Finset.toFinset_coe, sdiff_eq_left]
    refine Finset.disjoint_left.mpr ?_
    intro e he
    simp only [Set.mem_toFinset, Sym2.mem_diagSet_iff_isDiag]
    exact G.edges_valid e he
  · exact proof_irrel_heq _ _
  · simp only [eq_mpr_eq_cast, cast_heq]

def sym2LabeledGraphEqv
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G G' : Sym2LabeledGraph σ n) : Prop
  :=
  G.toLabeledGraph ∼f G'.toLabeledGraph

infixl:50 " ∼sf " => sym2LabeledGraphEqv

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G G' : Sym2LabeledGraph σ n) :
    Decidable (G ∼sf G')
  := by
  dsimp [sym2LabeledGraphEqv]
  infer_instance

theorem sym2LabeledGraphEqv.refl
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    G ∼sf G
  :=
  flagEqv.refl _

theorem sym2LabeledGraphEqv.symm
    {T : Type} {σ : FlagType T} {n : ℕ}
    {G G' : Sym2LabeledGraph σ n}
    (h : G ∼sf G') :
    G' ∼sf G
  :=
  flagEqv.symm h

theorem sym2LabeledGraphEqv.trans
    {T : Type} {σ : FlagType T} {n : ℕ}
    {G G' G'' : Sym2LabeledGraph σ n}
    (h₁ : G ∼sf G') (h₂ : G' ∼sf G'') :
    G ∼sf G''
  :=
  flagEqv.trans h₁ h₂

instance sym2LabeledGraphSetoid
    {T : Type} (σ : FlagType T) (n : ℕ) :
    Setoid (Sym2LabeledGraph σ n)
  where
    r     := sym2LabeledGraphEqv
    iseqv := {
      refl  := sym2LabeledGraphEqv.refl,
      symm  := sym2LabeledGraphEqv.symm,
      trans := sym2LabeledGraphEqv.trans
    }

def Sym2Flag {T : Type} (σ : FlagType T) (n : ℕ) : Type :=
  Quotient (sym2LabeledGraphSetoid σ n)

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ} :
    Fintype (Sym2Flag σ n)
  := by
  refine @Quotient.fintype _ _ (sym2LabeledGraphSetoid σ n) ?_
  intro G G'
  show Decidable (G ∼sf G')
  infer_instance

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ} :
    DecidableEq (Sym2Flag σ n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  show Decidable (G ∼sf G')
  infer_instance

def Sym2LabeledGraph.toFlag
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Flag σ (Fin n)
  :=
  ⟦G.toLabeledGraph⟧

theorem Sym2LabeledGraph.toFlag_respect_eqv
    {T : Type} {σ : FlagType T} {n : ℕ}
    (G G' : Sym2LabeledGraph σ n) (h : G ∼sf G') :
    G.toFlag = G'.toFlag
  :=
  Quotient.sound h

def Sym2Flag.toFlag
    {T : Type} {σ : FlagType T} {n : ℕ} (G : Sym2Flag σ n) :
    Flag σ (Fin n)
  :=
  Quotient.lift Sym2LabeledGraph.toFlag Sym2LabeledGraph.toFlag_respect_eqv G

theorem Sym2Flag.toFlag_injective
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (F F' : Sym2Flag σ n) (h : F.toFlag = F'.toFlag) :
    F = F'
  := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  rcases Quotient.exists_rep F' with ⟨G', rfl⟩
  apply Quotient.sound
  dsimp [Sym2Flag.toFlag, Sym2LabeledGraph.toFlag] at h
  have h' : G.toLabeledGraph ∼f G'.toLabeledGraph := Quotient.exact h
  exact h'

end Archive.Compute

namespace FlagAlgebras
open Archive.Compute

noncomputable def LabeledGraph.toSym2Flag
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : LabeledGraph σ (Fin n)) : Sym2Flag σ n
  :=
  ⟦G.toSym2LabeledGraph⟧

theorem LabeledGraph.toSym2Flag_respect_eqv
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G G' : LabeledGraph σ (Fin n)) (h : G ∼f G') :
    G.toSym2Flag = G'.toSym2Flag
  := by
  dsimp only [toSym2Flag]
  apply Quotient.sound
  show G.toSym2LabeledGraph ∼sf G'.toSym2LabeledGraph
  dsimp only [sym2LabeledGraphEqv]
  rw [G.toSym2LabeledGraph_toLabeledGraph_eq, G'.toSym2LabeledGraph_toLabeledGraph_eq]
  exact h

noncomputable def Flag.toSym2Flag
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (F : Flag σ (Fin n)) : Sym2Flag σ n
  :=
  Quotient.lift LabeledGraph.toSym2Flag LabeledGraph.toSym2Flag_respect_eqv F

theorem Flag.toSym2Flag_toFlag_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (F : Flag σ (Fin n)) :
    F.toSym2Flag.toFlag = F
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  apply Quotient.sound
  rw [F.toSym2LabeledGraph_toLabeledGraph_eq]

end FlagAlgebras

namespace Archive.Compute
open FlagAlgebras
open SimpleGraph

theorem Sym2Flag.toFlag_toSym2Flag_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (F : Sym2Flag σ n) :
    F.toFlag.toSym2Flag = F
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  apply Quotient.sound
  rw [F.toLabeledGraph_toSym2LabeledGraph_eq]

theorem Sym2Flag.toFlag_univ_eq_univ
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ} :
    Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } (Finset.univ : Finset (Sym2Flag σ n))
    = (Finset.univ : Finset (Flag σ (Fin n)))
  := by
  ext F
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, iff_true]
  use F.toSym2Flag
  exact Flag.toSym2Flag_toFlag_eq F

end Archive.Compute
