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

noncomputable instance subgraphFintype
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Fintype (G.Subgraph)
  :=
  let f : G.Subgraph → Set V × Set (V × V) :=
    fun G' => (G'.verts, { (u, v) | G'.Adj u v })
  have f_inj : Function.Injective f := by
    intro G1 G2 h_eq
    dsimp [f] at h_eq
    ext u v
    . have h_eq_verts : G1.verts = G2.verts := (Prod.ext_iff.mp h_eq).1
      exact Eq.to_iff (congrFun h_eq_verts u)
    . have h_eq_edges := (Prod.ext_iff.mp h_eq).2
      exact Eq.to_iff (congrFun h_eq_edges (u, v))
  Fintype.ofInjective f f_inj

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

instance labeledGraphSetoid (σ : FlagType T) (V : Type)
    : Setoid (LabeledGraph σ V)
  where
    r     := flagEqv
    iseqv := {
      refl  := flagEqv.refl,
      symm  := flagEqv.symm,
      trans := flagEqv.trans
    }

def Flag (σ : FlagType T) (V : Type) : Type :=
  Quotient (labeledGraphSetoid σ V)

noncomputable instance FlagFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V] : Fintype (Flag σ V)
  := by
  classical
  exact Quotient.fintype (labeledGraphSetoid σ V)

class FintypeList {t : ℕ} (V : Fin t → Type) where
  fintype_all : ∀ (i : Fin t), Fintype (V i)

class DecidableEqList {t : ℕ} (V : Fin t → Type) where
  decidable_eq_all : ∀ (i : Fin t), DecidableEq (V i)

instance fintype_V {t : ℕ} (V : Fin t → Type) [FintypeList V] (i : Fin t) : Fintype (V i)
  :=
  FintypeList.fintype_all i

instance decidable_eq_V {t : ℕ} (V : Fin t → Type) [DecidableEqList V] (i : Fin t) : DecidableEq (V i)
  :=
  DecidableEqList.decidable_eq_all i

abbrev LabeledGraphList (σ : FlagType T) (t : ℕ) (V : Fin t → Type) := ∀ (i : Fin t), LabeledGraph σ (V i)

def flagListEqv {σ : FlagType T} {t : ℕ} {V : Fin t → Type} (Gl Gl' : LabeledGraphList σ t V) : Prop
  :=
  ∀ (i : Fin t), Gl i ∼f Gl' i

infixl:50 " ∼fl " => flagListEqv

omit [Fintype T] in
theorem flagListEqv.refl {σ : FlagType T} {t : ℕ} {V : Fin t → Type} (Gl : LabeledGraphList σ t V)
    : Gl ∼fl Gl
  :=
  fun i => flagEqv.refl (Gl i)

omit [Fintype T] in
theorem flagListEqv.symm {σ : FlagType T} {t : ℕ} {V : Fin t → Type}
    : ∀ {Gl Gl' : LabeledGraphList σ t V}, Gl ∼fl Gl' → Gl' ∼fl Gl
  :=
  fun h i => flagEqv.symm (h i)

omit [Fintype T] in
theorem flagListEqv.trans {σ : FlagType T} {t : ℕ} {V : Fin t → Type}
    : ∀ {Gl Gl' Gl'' : LabeledGraphList σ t V}, Gl ∼fl Gl' → Gl' ∼fl Gl'' → Gl ∼fl Gl''
  :=
  fun h h' i => flagEqv.trans (h i) (h' i)

instance labeledGraphListSetoid (σ : FlagType T) (t : ℕ) (V : Fin t → Type)
    : Setoid (LabeledGraphList σ t V)
  where
    r     := flagListEqv
    iseqv := {
      refl  := flagListEqv.refl,
      symm  := flagListEqv.symm,
      trans := flagListEqv.trans
    }

def QuotlabeledGraphList (σ : FlagType T) (t : ℕ) (V : Fin t → Type) : Type :=
  Quotient (labeledGraphListSetoid σ t V)

abbrev FlagList (σ : FlagType T) (t : ℕ) (V : Fin t → Type) := ∀ (i : Fin t), Flag σ (V i)

def Flag.toSingletonList {σ : FlagType T} {V : Type} (F : Flag σ V)
    : FlagList σ 1 (fun _ => V)
  :=
  fun _ => F

instance fintypeSingletonList {V : Type} [Fintype V]
    : @FintypeList 1 (fun _ => V)
  :=
  { fintype_all := fun _ ↦ inferInstance }

instance DecidableEqSingletonList {V : Type} [DecidableEq V]
    : @DecidableEqList 1 (fun _ => V)
  :=
  { decidable_eq_all := fun _ ↦ inferInstance }

noncomputable instance eqv_QuotlabeledGraphList_FlagList (σ : FlagType T) (t : ℕ) (V : Fin t → Type)
    : QuotlabeledGraphList σ t V ≃ FlagList σ t V where
  toFun := fun Gl (i : Fin t) => ⟦Gl.out i⟧
  invFun := fun Fl => ⟦fun (i : Fin t) => (Fl i).out⟧
  left_inv Gl := by
    rw [← Quotient.out_eq Gl]
    apply Quotient.sound
    intro i
    simp
    apply Quotient.mk_out (Gl.out i)
  right_inv Fl := by
    simp; ext i
    rw [← Quotient.out_eq (Fl i)]
    apply Quotient.sound
    apply flagEqv.trans
    · show _ ∼f (fun i ↦ Quotient.out (Fl i)) i
      have : ⟦fun i ↦ Quotient.out (Fl i)⟧.out ∼fl (fun i ↦ Quotient.out (Fl i)) := by
        apply Quotient.mk_out (fun i ↦ Quotient.out (Fl i))
      exact this i
    · simp
      exact flagEqv.refl (Quotient.out (Fl i))

@[simp]
noncomputable def QuotlabeledGraphList.coe {σ : FlagType T} {t : ℕ} {V : Fin t → Type} (Fl : QuotlabeledGraphList σ t V)
    : FlagList σ t V
  :=
  (eqv_QuotlabeledGraphList_FlagList σ t V).toFun Fl

@[simp]
noncomputable def FlagList.coe {σ : FlagType T} {t : ℕ} {V : Fin t → Type} (Fl : FlagList σ t V)
    : QuotlabeledGraphList σ t V
  :=
  (eqv_QuotlabeledGraphList_FlagList σ t V).invFun Fl
