import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Flag

abbrev FlagType := SimpleGraph

structure LabeledGraph [Fintype T] (σ : FlagType T) (V : Type) where
  graph : SimpleGraph V
  type_embed : σ ↪g graph

structure LabeledGraphIso [Fintype T] {σ : FlagType T} {V W : Type}
  (G : LabeledGraph σ V) (G' : LabeledGraph σ W) where
  graph_iso : G.graph ≃g G'.graph
  type_preserve : graph_iso ∘ G.type_embed = G'.type_embed

infixl:50 " ≃f " => LabeledGraphIso

namespace LabeledGraphIso

variable [Fintype T] {σ : FlagType T}
  {G : LabeledGraph σ V} {G' : LabeledGraph σ W} {G'' : LabeledGraph σ U}

def refl : G ≃f G := sorry

def symm (h : G ≃f G') : G' ≃f G := sorry

def trans (h : G ≃f G') (h' : G' ≃f G'') : G ≃f G'' := sorry

end LabeledGraphIso

end Flag
