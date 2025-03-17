import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph

variable {T : Type} [Fintype T]

abbrev FlagType := SimpleGraph

def FlagType.size (_ : FlagType T) : ℕ
  :=
  Fintype.card T

@[ext]
structure LabeledGraph (σ : FlagType T) (V : Type) where
  graph : SimpleGraph V
  type_embed : σ ↪g graph

noncomputable instance labeledGraphFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (LabeledGraph σ V)
  :=
  let f : LabeledGraph σ V → SimpleGraph V × (T → V) :=
    fun ⟨G, embed⟩ ↦ (G, embed.toFun)
  have f_inj : Function.Injective f := by
    intro ⟨G, φ⟩ ⟨G', φ'⟩ h_eq
    dsimp [f] at h_eq
    simp_all only [Prod.mk.injEq, LabeledGraph.mk.injEq, true_and]
    obtain ⟨left, right⟩ := h_eq
    subst left
    simp_all only [DFunLike.coe_fn_eq, heq_eq_eq]
  have : Fintype (SimpleGraph V × (T → V)) := Fintype.ofFinite (SimpleGraph V × (T → V))
  Fintype.ofInjective f f_inj

def LabeledGraph.size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (_ : LabeledGraph σ V) : ℕ
  :=
  Fintype.card V

@[ext]
structure LabeledSubgraph (σ : FlagType T) {V : Type} (G : LabeledGraph σ V) where
  subgraph : G.graph.Subgraph
  type_embed : σ ↪g subgraph.coe
  embed_eq : ∀ (t : T), type_embed t = G.type_embed t

initialize_simps_projections LabeledSubgraph (subgraph → coe)

namespace LabeledSubgraph

@[simps]
def coe {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G)
    : LabeledGraph σ H.subgraph.verts where
  graph := H.subgraph.coe
  type_embed := H.type_embed

def IsInduced {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : Prop
  :=
  H.subgraph.IsInduced

noncomputable instance labeledSubgraphFintype
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (G : LabeledGraph σ V) : Fintype (LabeledSubgraph σ G)
  :=
  let f : LabeledSubgraph σ G → G.graph.Subgraph × (T → V) :=
    fun ⟨G', embed, _⟩ ↦ (G', fun t ↦ embed t)
  have f_inj : Function.Injective f := by
    intro ⟨G, φ, _⟩ ⟨G', φ', _⟩ h_eq
    dsimp [f] at h_eq
    simp_all only [Prod.mk.injEq, and_true, mk.injEq, true_and]
    subst h_eq
    simp_all only [heq_eq_eq]
    ext x : 2
    simp_all only
  have : Fintype (G.graph.Subgraph) := by
    let g : G.graph.Subgraph → Set V × Set (V × V) :=
      fun H ↦ (H.verts, { (u, v) | H.Adj u v })
    have g_inj : Function.Injective g := by
      intro H H' h_eq
      dsimp [g] at h_eq
      simp_all only [Prod.mk.injEq, f]
      obtain ⟨left, right⟩ := h_eq
      ext u v
      · simp_all only
      · constructor
        · intro e
          have : (u, v) ∈ {x | H.Adj x.1 x.2} := e
          rw [right] at this
          exact this
        · intro e
          have : (u, v) ∈ {x | H'.Adj x.1 x.2} := e
          rw [←right] at this
          exact this
    exact Fintype.ofInjective g g_inj
  have : Fintype (G.graph.Subgraph × (T → V)) := Fintype.ofFinite (G.graph.Subgraph × (T → V))
  Fintype.ofInjective f f_inj

end LabeledSubgraph

structure LabeledGraphIso {σ : FlagType T} {V W : Type}
  (G : LabeledGraph σ V) (G' : LabeledGraph σ W) where
  graph_iso : G.graph ≃g G'.graph
  type_preserve : graph_iso ∘ G.type_embed = G'.type_embed

infixl:50 " ≃f " => LabeledGraphIso

namespace LabeledGraphIso

variable {T : Type} [Fintype T] {σ : FlagType T} {V W U : Type}
variable {G : LabeledGraph σ V} {G' : LabeledGraph σ W} {G'' : LabeledGraph σ U}

def refl : G ≃f G where
  graph_iso := by rfl
  type_preserve := by ext t ; simp

def symm (h : G ≃f G') : G' ≃f G where
  graph_iso := h.graph_iso.symm
  type_preserve := by
    ext t
    simp [←h.type_preserve]

def trans (h : G ≃f G') (h' : G' ≃f G'') : G ≃f G'' where
  graph_iso := RelIso.trans h.graph_iso h'.graph_iso
  type_preserve := by
    ext t
    simp [←h.type_preserve, ←h'.type_preserve]

end LabeledGraphIso

variable {T : Type} [Fintype T] {V : Type}

def flagEqv {σ : FlagType T} (G G' : LabeledGraph σ V) : Prop
  :=
  Nonempty (G ≃f G')

infixl:50 " ∼f " => flagEqv

omit [Fintype T] in
theorem flagEqv.refl {σ : FlagType T} (G : LabeledGraph σ V)
    : G ∼f G
  :=
  Nonempty.intro LabeledGraphIso.refl

omit [Fintype T] in
theorem flagEqv.symm {σ : FlagType T}
    : ∀ {G G' : LabeledGraph σ V}, G ∼f G' → G' ∼f G
  := by
  intro G G' h
  have G_iso : G ≃f G' := Classical.choice h
  exact Nonempty.intro G_iso.symm

omit [Fintype T] in
theorem flagEqv.trans {σ : FlagType T}
    : ∀ {G G' G'' : LabeledGraph σ V}, G ∼f G' → G' ∼f G'' → G ∼f G''
  := by
  intro G G' G'' h h'
  have G_iso : G ≃f G' := Classical.choice h
  have G'_iso : G' ≃f G'' := Classical.choice h'
  exact Nonempty.intro (G_iso.trans G'_iso)

variable [DecidableEq T]

instance labeledGraphSetoid (σ : FlagType T) (V : Type) [DecidableEq V]
    : Setoid (LabeledGraph σ V)
  where
    r     := flagEqv
    iseqv := {
      refl  := flagEqv.refl,
      symm  := flagEqv.symm,
      trans := flagEqv.trans
    }

def Flag (σ : FlagType T) (V : Type) [DecidableEq V] : Type :=
  Quotient (labeledGraphSetoid σ V)

noncomputable instance FlagFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V] : Fintype (Flag σ V)
  := by
  classical
  exact Quotient.fintype (labeledGraphSetoid σ V)
