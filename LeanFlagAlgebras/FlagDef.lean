import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open Classical

def Fin.coe {t : ℕ} (i : Fin (t + 1)) (hi : i.val ≠ t) : Fin t
  :=
  ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.is_lt) hi⟩

namespace FlagAlgebras

variable {T : Type} [Fintype T]

abbrev FlagType := SimpleGraph

noncomputable def FlagType.size (_ : FlagType T) : ℕ
  :=
  Fintype.card T

@[ext]
structure LabeledGraph (σ : FlagType T) (V : Type) where
  graph : SimpleGraph V
  type_embed : σ ↪g graph

def LabeledGraph.type_verts (G : LabeledGraph σ V) : Set V :=
  G.type_embed '' Set.univ

omit [Fintype T] in
lemma LabeledGraph.type_verts_contain {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (t : T)
  : G.type_embed t ∈ G.type_verts := by
  unfold LabeledGraph.type_verts
  exact Set.mem_image_of_mem G.type_embed (Set.mem_univ t)

noncomputable def LabeledGraph.iso_type_G
     {σ : FlagType T} (G : LabeledGraph σ V) : T ≃ G.type_verts := by
  let f : T → G.type_verts := by
    intro t
    use G.type_embed t
    unfold LabeledGraph.type_verts
    exact Set.mem_image_of_mem (⇑G.type_embed) (Set.mem_univ t)
  have h_bij : Function.Bijective f := by
    constructor
    · intro t₁ t₂ h_eq
      dsimp [f] at h_eq
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
      exact h_eq
    · intro u
      unfold LabeledGraph.type_verts at u
      obtain ⟨t, h_t⟩ := u
      simp only [Subtype.mk.injEq, f]
      simp only [Set.image_univ, Set.mem_range] at h_t
      exact h_t
  let f_bij : T ≃ G.type_verts := Equiv.ofBijective f h_bij
  exact f_bij

noncomputable instance labeledGraphFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (LabeledGraph σ V)
  :=
  let f : LabeledGraph σ V → SimpleGraph V × (T → V) :=
    fun ⟨G, embed⟩ ↦ (G, embed.toFun)
  have f_inj : Function.Injective f := by
    intro ⟨G, φ⟩ ⟨G', φ'⟩ h_eq
    dsimp [f] at h_eq
    simp only [Prod.mk.injEq] at h_eq
    obtain ⟨left, right⟩ := h_eq
    subst left
    simp only [LabeledGraph.mk.injEq, true_and, heq_eq_eq]
    apply DFunLike.coe_fn_eq.mp right
  have : Fintype (SimpleGraph V × (T → V)) := Fintype.ofFinite (SimpleGraph V × (T → V))
  Fintype.ofInjective f f_inj

noncomputable def LabeledGraph.size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (_ : LabeledGraph σ V) : ℕ
  :=
  Fintype.card V

omit [Fintype T] in
theorem type_embed_Adj_iff
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (u v : T)
    : σ.Adj u v ↔ G.graph.Adj (G.type_embed u) (G.type_embed v)
  :=
  Iff.symm (SimpleGraph.Embedding.map_adj_iff G.type_embed)

def emptyLabeledGraph (σ : FlagType T) : LabeledGraph σ T
  :=
  ⟨σ, SimpleGraph.Embedding.refl⟩

@[ext]
structure LabeledSubgraph (σ : FlagType T) {V : Type} (G : LabeledGraph σ V) where
  subgraph : G.graph.Subgraph
  type_embed : σ ↪g subgraph.coe
  embed_eq : ∀ (t : T), type_embed t = G.type_embed t

def LabeledGraph.top (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  {
    subgraph := {
      verts := Set.univ
      Adj := G.graph.Adj
      adj_sub := fun a ↦ a
      edge_vert := fun _ ↦ trivial
      symm := by simp only [SimpleGraph.symm]
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, trivial⟩
      inj' := by
        intro t₁ t₂ h_eq
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact h_eq
      map_rel_iff' := by
        intro t₁ t₂
        simp only [Function.Embedding.coeFn_mk, SimpleGraph.Subgraph.coe_adj, SimpleGraph.Embedding.map_adj_iff]
    }
    embed_eq := by
      intro t
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  }

lemma LabeledGraph.top_isInduced (G : LabeledGraph σ V)
  : G.top.subgraph.IsInduced := fun _ _ h_adj ↦ h_adj

def LabeledGraph.bottom (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  {
    subgraph := {
      verts := G.type_verts
      Adj := fun u v => u ∈ G.type_verts ∧ v ∈ G.type_verts ∧ G.graph.Adj u v
      adj_sub := by simp only [and_imp, imp_self, implies_true]
      edge_vert := by
        intro u v ⟨hu, _⟩
        exact hu
      symm := by
        intro u v ⟨hu, hv, h_uv⟩
        exact ⟨hv, hu, h_uv.symm⟩
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, G.type_verts_contain t⟩
      inj' := by
        intro t₁ t₂ h_eq
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact h_eq
      map_rel_iff' := by
        intro t₁ t₂
        simp only [Function.Embedding.coeFn_mk, SimpleGraph.Subgraph.coe_adj, SimpleGraph.Embedding.map_adj_iff]
        constructor
        · intro ⟨_, _, h_adj⟩
          exact h_adj
        · intro h_adj
          have ht₁: G.type_embed t₁ ∈ G.type_verts := G.type_verts_contain t₁
          have ht₂: G.type_embed t₂ ∈ G.type_verts := G.type_verts_contain t₂
          exact ⟨ht₁, ht₂, h_adj⟩
    }
    embed_eq := by
      intro t
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  }

lemma LabeledGraph.bottom_isInduced (G : LabeledGraph σ V)
  : G.bottom.subgraph.IsInduced := fun h_u h_v h_adj ↦ ⟨h_u, ⟨h_v, h_adj⟩⟩

namespace LabeledSubgraph

noncomputable def size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : ℕ
  :=
  Fintype.card H.subgraph.verts

@[simps]
def coe {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G)
    : LabeledGraph σ H.subgraph.verts where
  graph := H.subgraph.coe
  type_embed := H.type_embed

omit [Fintype T] in
theorem coe_adj_iff
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) (u v : H.subgraph.verts)
    : H.coe.graph.Adj u v ↔ H.subgraph.Adj u.val v.val
  :=
  Eq.to_iff rfl

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
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (G : LabeledGraph σ V)
    : Fintype (LabeledSubgraph σ G)
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

omit [Fintype T] in
theorem labeledSubgraph_contain_type_verts
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (H : LabeledSubgraph σ G)
    : G.type_verts ⊆ H.subgraph.verts
  := by
  intro v hv
  simp only [LabeledGraph.type_verts, Set.image_univ, Set.mem_range] at hv
  obtain ⟨t, ht⟩ := hv
  rw [← ht, ← H.embed_eq t]
  simp only [Subtype.coe_prop]

def inducedSubgraph
    {V : Type} (G : SimpleGraph V) (S : Set V)
    : G.Subgraph where
  verts := S
  Adj := fun (u v : V) => G.Adj u v ∧ u ∈ S ∧ v ∈ S
  adj_sub := by
    intro v w a
    simp_all only
  edge_vert := by
    intro v w a
    simp_all only
  symm := fun u v h => ⟨G.symm h.1, h.2.2, h.2.1⟩

@[simp]
theorem inducedSubgraph_verts
    {V : Type} (G : SimpleGraph V) (S : Set V)
    : (inducedSubgraph G S).verts = S
  := by
  simp only [inducedSubgraph]

@[simp]
theorem inducedSubgraph_isInduced
    {V : Type} (G : SimpleGraph V) (S : Set V)
    : (inducedSubgraph G S).IsInduced
  := by
  intro u v h_u h_v h_adj
  simp [inducedSubgraph] at *
  (repeat' constructor) <;> assumption

def inducedLabeledSubgraph
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : LabeledSubgraph σ G where
  subgraph := inducedSubgraph G.graph S
  type_embed := {
    toFun := by
      simp only [inducedSubgraph_verts]
      intro t
      have ht : G.type_embed t ∈ G.type_verts := by
        dsimp [LabeledGraph.type_verts]
        exact Set.mem_image_of_mem G.type_embed trivial
      have ht' : G.type_embed t ∈ S := h ht
      exact ⟨G.type_embed t, ht'⟩
    inj' := by
      intro t u h_tu
      simp at h_tu
      exact h_tu
    map_rel_iff' := by
      intro t u
      dsimp [inducedSubgraph_verts, inducedSubgraph]
      simp only [SimpleGraph.Embedding.map_adj_iff, and_iff_left_iff_imp]
      intro _
      constructor
      · apply h
        simp [LabeledGraph.type_verts]
      · apply h
        simp [LabeledGraph.type_verts]
  }
  embed_eq := by
    intro t
    simp only [eq_mpr_eq_cast, cast_eq, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_verts
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).subgraph.verts = S
  := by
  simp only [inducedLabeledSubgraph, eq_mpr_eq_cast, cast_eq, inducedSubgraph_verts]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).size = Fintype.card S
  := by
  dsimp [inducedLabeledSubgraph, inducedSubgraph, LabeledSubgraph.size]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_isInduced
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).IsInduced
  := by
  simp only [inducedLabeledSubgraph, eq_mpr_eq_cast, cast_eq, inducedSubgraph_isInduced]
  intro t u h_t h_u h_adj
  (repeat' constructor) <;> assumption

omit [Fintype T] in
theorem isInduced_exist_induce_set
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) (h_ind : H.IsInduced)
    : ∃ (S : Set V) (h : G.type_verts ⊆ S), inducedLabeledSubgraph G S h = H
  := by
  let S := H.subgraph.verts
  have h : G.type_verts ⊆ S := labeledSubgraph_contain_type_verts G H
  use S, h
  dsimp [inducedLabeledSubgraph]
  have hH_graph : inducedSubgraph G.graph S = H.subgraph := by
    dsimp [inducedSubgraph]
    dsimp [LabeledSubgraph.IsInduced, SimpleGraph.Subgraph.IsInduced] at h_ind
    congr
    funext u v
    simp only [eq_iff_iff]
    constructor
    · intro ⟨h_adj, h_u, h_v⟩
      exact h_ind h_u h_v h_adj
    · intro h_adj
      repeat' constructor
      · exact H.subgraph.adj_sub h_adj
      · exact H.subgraph.edge_vert h_adj
      · symm at h_adj
        exact H.subgraph.edge_vert h_adj
  congr
  · funext u v
    simp [hH_graph]
  · funext t
    congr
    exact Eq.symm (H.embed_eq t)
  · apply proof_irrel_heq
  · apply proof_irrel_heq

end LabeledSubgraph

structure LabeledGraphIso {σ : FlagType T} {V W : Type}
  (G : LabeledGraph σ V) (G' : LabeledGraph σ W) where
  graph_iso : G.graph ≃g G'.graph
  type_preserve : graph_iso ∘ G.type_embed = G'.type_embed

infixl:50 " ≃f " => LabeledGraphIso

omit [Fintype T] in
theorem labeledGraphIso_size_eq
    {σ : FlagType T} {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : LabeledGraph σ V) (G' : LabeledGraph σ W) (h_iso : G ≃f G')
    : G.size = G'.size
  := by
  dsimp [LabeledGraph.size]
  rw [Fintype.card_congr h_iso.graph_iso.toEquiv]

namespace LabeledGraphIso

variable {T : Type} [Fintype T] {σ : FlagType T} {V W U : Type}
variable {G : LabeledGraph σ V} {G' : LabeledGraph σ W} {G'' : LabeledGraph σ U}

@[refl]
def refl : G ≃f G where
  graph_iso := by rfl
  type_preserve := by ext t ; simp

@[symm]
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

instance : Trans (@flagEqv T V σ) (@flagEqv T V σ) (@flagEqv T V σ) where
  trans := flagEqv.trans

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

noncomputable instance FlagFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (Flag σ V)
  := by
  classical
  exact Quotient.fintype (labeledGraphSetoid σ V)

theorem Flag.type_eq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} (h_Vl_eq : Vl' = Vl) (i : Fin t)
    : Flag σ (Vl' i) = Flag σ (Vl i) := by
  rw [h_Vl_eq]

omit [Fintype T] in
theorem flagEqv.sound {σ : FlagType T} {V : Type} {G G' : LabeledGraph σ V} (h : G ∼f G')
    : (⟦G⟧ : Flag σ V) = (⟦G'⟧ : Flag σ V)
  := by
  apply Quotient.sound
  exact h

def emptyFlag (σ : FlagType T) : Flag σ T
  :=
  ⟦emptyLabeledGraph σ⟧

/- FlagList -/

class FintypeList {t : ℕ} (Vl : Fin t → Type) where
  fintype_all : ∀ (i : Fin t), Fintype (Vl i)

class DecidableEqList {t : ℕ} (Vl : Fin t → Type) where
  decidable_eq_all : ∀ (i : Fin t), DecidableEq (Vl i)

noncomputable instance fintype_V {t : ℕ} (Vl : Fin t → Type) [FintypeList Vl] (i : Fin t) : Fintype (Vl i)
  :=
  FintypeList.fintype_all i

noncomputable instance decidable_eq_V {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (i : Fin t) : DecidableEq (Vl i)
  :=
  DecidableEqList.decidable_eq_all i

abbrev LabeledGraphList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) := ∀ (i : Fin t), LabeledGraph σ (Vl i)

def labeledGraphToList
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
    : LabeledGraphList σ 1 (fun _ => V)
  :=
  fun _ => G

def labeledGraphPairToList
    {σ : FlagType T} {V W : Type} (G : LabeledGraph σ V) (H : LabeledGraph σ W)
    : LabeledGraphList σ 2 (fun i => match i with | 0 => V | 1 => W)
  :=
  fun i => match i with | 0 => G | 1 => H

notation "[" G "]ᵍ" => (labeledGraphToList G)
notation "[" G "," H "]ᵍ" => (labeledGraphPairToList G H)

def flagListEqv {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Gl Gl' : LabeledGraphList σ t Vl) : Prop
  :=
  ∀ (i : Fin t), Gl i ∼f Gl' i

infixl:50 " ∼fl " => flagListEqv

omit [Fintype T] in
theorem flagListEqv.refl {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Gl : LabeledGraphList σ t Vl)
    : Gl ∼fl Gl
  :=
  fun i => flagEqv.refl (Gl i)

omit [Fintype T] in
theorem flagListEqv.symm {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    : ∀ {Gl Gl' : LabeledGraphList σ t Vl}, Gl ∼fl Gl' → Gl' ∼fl Gl
  :=
  fun h i => flagEqv.symm (h i)

omit [Fintype T] in
theorem flagListEqv.trans {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    : ∀ {Gl Gl' Gl'' : LabeledGraphList σ t Vl}, Gl ∼fl Gl' → Gl' ∼fl Gl'' → Gl ∼fl Gl''
  :=
  fun h h' i => flagEqv.trans (h i) (h' i)

instance : Trans (@flagListEqv T σ t Vl) (@flagListEqv T σ t Vl) (@flagListEqv T σ t Vl) where
  trans := flagListEqv.trans

instance labeledGraphListSetoid (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type)
    : Setoid (LabeledGraphList σ t Vl)
  where
    r     := flagListEqv
    iseqv := {
      refl  := flagListEqv.refl,
      symm  := flagListEqv.symm,
      trans := flagListEqv.trans
    }

def QuotLabeledGraphList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) : Type :=
  Quotient (labeledGraphListSetoid σ t Vl)

abbrev FlagList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) := ∀ (i : Fin t), Flag σ (Vl i)

theorem FlagList.type_eq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} (h_Vl_eq : Vl' = Vl)
    : FlagList σ t Vl' = FlagList σ t Vl := by
  rw [h_Vl_eq]

theorem flagList_HEq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_Fl_eq : ∀ (i : Fin t), Fl i = cast (Flag.type_eq h_Vl_eq i) (Fl' i))
    : HEq Fl Fl' := by
  have h_Fl_cast : Fl = cast (FlagList.type_eq h_Vl_eq) Fl' := by
    subst h_Vl_eq
    simp_all only [cast_eq]
    ext1 x
    simp_all only
  subst h_Vl_eq
  subst h_Fl_cast
  simp_all only [cast_eq, heq_eq_eq]

def flagToList {σ : FlagType T} {V : Type} (F : Flag σ V)
    : FlagList σ 1 (fun _ => V)
  :=
  fun _ => F

def flagPairToList {σ : FlagType T} {V W : Type} (F : Flag σ V) (G : Flag σ W)
    : FlagList σ 2 (fun i => match i with | 0 => V | 1 => W)
  :=
  fun i => match i with | 0 => F | 1 => G

def flagTripleToList {σ : FlagType T} {V W U : Type} (F : Flag σ V) (G : Flag σ W) (H : Flag σ U)
    : FlagList σ 3 (fun i => match i with | 0 => V | 1 => W | 2 => U)
  :=
  fun i => match i with | 0 => F | 1 => G | 2 => H

notation "[" F "]ᶠ" => (flagToList F)
notation "[" F "," G "]ᶠ" => (flagPairToList F G)
notation "[" F "," G "," H "]ᶠ" => (flagTripleToList F G H)

instance fintypeSingletonList {V : Type} [Fintype V]
    : FintypeList (fun (_ : Fin 1) => V)
  :=
  { fintype_all := fun _ ↦ inferInstance }

instance decidableEqSingletonList {V : Type} [DecidableEq V]
    : DecidableEqList (fun (_ : Fin 1) => V)
  :=
  { decidable_eq_all := fun _ ↦ inferInstance }

instance fintypePairList {V W : Type} [Fintype V] [Fintype W]
    : FintypeList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance decidableEqPairList {V W : Type} [DecidableEq V] [DecidableEq W]
    : DecidableEqList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance fintypeTripleList {V W U : Type} [Fintype V] [Fintype W] [Fintype U]
    : FintypeList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

instance decidableEqTripleList {V W U : Type} [DecidableEq V] [DecidableEq W] [DecidableEq U]
    : DecidableEqList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

noncomputable instance eqv_QuotLabeledGraphList_FlagList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type)
    : QuotLabeledGraphList σ t Vl ≃ FlagList σ t Vl where
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
noncomputable def QuotLabeledGraphList.coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Fl : QuotLabeledGraphList σ t Vl)
    : FlagList σ t Vl
  :=
  (eqv_QuotLabeledGraphList_FlagList σ t Vl).toFun Fl

@[simp]
noncomputable def FlagList.coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Fl : FlagList σ t Vl)
    : QuotLabeledGraphList σ t Vl
  :=
  (eqv_QuotLabeledGraphList_FlagList σ t Vl).invFun Fl

omit [Fintype T] in
theorem list_quot_eq_quot_list_singleton
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
    : ⟦[G]ᵍ⟧ = [⟦G⟧]ᶠ.coe
  := by
  dsimp [eqv_QuotLabeledGraphList_FlagList, flagToList]
  apply Quotient.sound
  intro i
  dsimp [labeledGraphToList]
  exact (Quotient.mk_out G).symm

omit [Fintype T] in
theorem list_quot_eq_quot_list_pair
    {σ : FlagType T} {V W : Type} (G : LabeledGraph σ V) (G' : LabeledGraph σ W)
    : ⟦[G, G']ᵍ⟧ = [⟦G⟧, ⟦G'⟧]ᶠ.coe
  := by
  dsimp [eqv_QuotLabeledGraphList_FlagList, flagToList]
  apply Quotient.sound
  intro i
  dsimp [labeledGraphPairToList]
  match i with
  | 0 => exact (Quotient.mk_out G).symm
  | 1 => exact (Quotient.mk_out G').symm

/- FlagList.insert -/

def listTypeInsert {t : ℕ} (Vl : Fin t → Type) (W : Type)
    : Fin (t + 1) → Type
  :=
  fun i => if h : i.val = t then W else Vl (i.coe h)

theorem listTypeInsert_eq {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val = t)
    : W = listTypeInsert Vl W i
  := by
  simp [listTypeInsert, hi]

theorem listTypeInsert_eq' {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Vl (i.coe hi) = listTypeInsert Vl W i
  := by
  simp [listTypeInsert, hi]

noncomputable instance fintypeListInsert
    {t : ℕ} (Vl : Fin t → Type) (W : Type) [Fintype W] [FintypeList Vl]
    : @FintypeList (t + 1) (listTypeInsert Vl W) where
  fintype_all i := if h : i.val = t
    then (by rw [← listTypeInsert_eq h]; infer_instance)
    else (by rw [← listTypeInsert_eq' h]; infer_instance)

noncomputable instance decidableEqListInsert
    {t : ℕ} (Vl : Fin t → Type) (W : Type) [DecidableEq W] [DecidableEqList Vl]
    : @DecidableEqList (t + 1) (listTypeInsert Vl W) where
  decidable_eq_all i := if h : i.val = t
    then (by rw [← listTypeInsert_eq h]; infer_instance)
    else (by rw [← listTypeInsert_eq' h]; infer_instance)

omit [Fintype T] in
theorem flag_listTypeInsert_eq {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val = t)
    : Flag σ W = Flag σ (listTypeInsert Vl W i)
  := by
  rw [← listTypeInsert_eq hi]

omit [Fintype T] in
theorem flag_listTypeInsert_eq' {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Flag σ (Vl (i.coe hi)) = Flag σ (listTypeInsert Vl W i)
  := by
  rw [← listTypeInsert_eq' hi]

def FlagList.insert {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    : FlagList σ (t + 1) (listTypeInsert Vl W)
  :=
  fun i => if hi : i.val = t
    then (cast (flag_listTypeInsert_eq hi) F)
    else (cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi)))

omit [Fintype T] in
theorem flaglist_heq_of_idx_eq {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {Fl : FlagList σ t Vl}
    {i i' : Fin t} (h : i = i')
    : HEq (Fl i) (Fl i') := by
  subst h; rfl

def flag_heq_to_iso {σ : FlagType T} {W : Type} {V : Type}
    {F₁ : Flag σ W} {F₂ : Flag σ V} (type_eq : W = V) (HEq : HEq F₁ F₂)
    : F₁.out ≃f F₂.out := by
  subst type_eq
  simp_all only [heq_eq_eq]
  subst HEq
  rfl

omit [Fintype T] in
theorem insert_new_flag_cast_iso {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (_ : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val = t)
    : Nonempty (F.out ≃f (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F).out) := by
  apply Nonempty.intro
  have h : HEq F (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F) := by
    apply HEq.symm
    apply cast_heq
  exact flag_heq_to_iso (listTypeInsert_eq hi) h

omit [Fintype T] in
theorem insert_preserves_existing_flags {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (_ : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Nonempty ((Fl (i.coe hi)).out ≃f (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))).out) := by
  apply Nonempty.intro
  have h : HEq (Fl (i.coe hi)) (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))) := by
    apply HEq.symm
    apply cast_heq
  exact flag_heq_to_iso (listTypeInsert_eq' hi) h

omit [Fintype T] in
theorem insert_preserves_existing_flags_coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin t} (hi : i.val ≠ t)
    : Nonempty ((Fl i).out ≃f (Fl.insert F i).out) := by
  apply Nonempty.intro
  dsimp [FlagList.insert]
  split
  next hi' =>
    exfalso
    have : i % (t + 1) = i := by
      simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact Nat.lt_succ_of_lt i.isLt
    rw [this] at hi'
    exact hi hi'
  next hi =>
    have hi' : (i : Fin (t + 1)).val ≠ t := by
      simp_all only [ne_eq, Fin.coe_eq_castSucc, Fin.coe_castSucc, not_false_eq_true]
    have cast_heq : HEq (Fl (i.coe hi)) (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))) := by
      apply HEq.symm
      apply cast_heq
    have  cast_iso := flag_heq_to_iso (listTypeInsert_eq' hi') cast_heq
    have type_eq : (Vl i) = (Vl ((i : Fin (t + 1)).coe hi)) := by
      simp_all only [ne_eq, Fin.coe_eq_castSucc]; rfl
    have idx_heq : HEq (Fl i) (Fl ((i : Fin (t + 1)).coe hi)) := by
      apply flaglist_heq_of_idx_eq
      simp_all only [ne_eq, Fin.coe_eq_castSucc]; rfl
    have idx_iso := flag_heq_to_iso type_eq idx_heq
    exact idx_iso.trans cast_iso

omit [Fintype T] in
theorem cast_preserves_flag_size {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    [FintypeList Vl] [DecidableEqList Vl] [Fintype W] [DecidableEq W]
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val = t)
    : F.out.size = (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F).out.size
  := labeledGraphIso_size_eq (Quotient.out F)
                             (Quotient.out (cast (flag_listTypeInsert_eq hi) F))
                             (Classical.choice (insert_new_flag_cast_iso Fl F hi))

omit [Fintype T] in
theorem cast_preserves_flag_size' {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    [FintypeList Vl] [DecidableEqList Vl] [Fintype W] [DecidableEq W]
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : (Fl (i.coe hi)).out.size = (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))).out.size
  := Eq.symm (labeledGraphIso_size_eq (Quotient.out (cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi))))
                                      (Quotient.out (Fl (i.coe hi)))
                                      (id (Classical.choice (insert_preserves_existing_flags Fl F hi)).symm))

/- FlagList.permute -/

abbrev Perm (t : ℕ) := Fin t ≃ Fin t

def listTypePermute {t : ℕ} (Vl : Fin t → Type) (π : Perm t)
    : Fin t → Type
  :=
  fun i => Vl (π i)

noncomputable instance fintypeListPermute
    {t : ℕ} (Vl : Fin t → Type) [FintypeList Vl] (π : Perm t)
    : @FintypeList t (listTypePermute Vl π) where
  fintype_all i := by
    simp [listTypePermute]
    infer_instance

noncomputable instance decidableEqListPermute
    {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (π : Perm t)
    : @DecidableEqList t (listTypePermute Vl π) where
  decidable_eq_all i := by
    simp [listTypePermute]
    infer_instance

def FlagList.permute {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    (Fl : FlagList σ t Vl) (π : Perm t)
    : FlagList σ t (listTypePermute Vl π)
  :=
  fun i => Fl (π i)

end FlagAlgebras
