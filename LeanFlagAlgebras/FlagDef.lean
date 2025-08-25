import «LeanFlagAlgebras».SubgraphUtil

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
lemma LabeledGraph.mem_type_verts {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} {v : V} :
    v ∈ G.type_verts ↔ ∃ t, G.type_embed t = v := by
  simp only [type_verts, Set.image_univ, Set.mem_range]

noncomputable instance {σ : FlagType T} (G : LabeledGraph σ V) :
    Fintype G.type_verts :=
  Set.univ.fintypeImage G.type_embed

lemma LabeledGraph.type_verts_card_eq {σ : FlagType T} {V : Type} (G : LabeledGraph σ V)
  : Fintype.card G.type_verts = σ.size := by
  dsimp [LabeledGraph.type_verts, FlagType.size]
  rw [Set.univ.card_image_of_injective G.type_embed.injective]
  exact (set_fintype_card_eq_univ_iff Set.univ).mpr rfl

omit [Fintype T] in
lemma LabeledGraph.type_verts_contain {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (t : T)
  : G.type_embed t ∈ G.type_verts :=
  LabeledGraph.mem_type_verts.mpr ⟨t, rfl⟩

noncomputable def LabeledGraph.iso_type_G
     {σ : FlagType T} (G : LabeledGraph σ V) : T ≃ G.type_verts := by
  let f : T → G.type_verts := by
    intro t
    use G.type_embed t
    rw [mem_type_verts]
    use t
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
  exact Equiv.ofBijective f h_bij

omit [Fintype T] in
lemma iso_type_G_eq_type_embed
    {σ : FlagType T} (G : LabeledGraph σ U) (t : T)
    : G.iso_type_G t = G.type_embed t
  :=
  rfl

noncomputable instance labeledGraphFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V]
    : Fintype (LabeledGraph σ V)
  :=
  let f : LabeledGraph σ V → SimpleGraph V × (T → V) :=
    fun ⟨G, embed⟩ ↦ (G, embed.toFun)
  have f_inj : Function.Injective f := by
    rintro ⟨G, φ⟩ ⟨G', φ'⟩ h_eq
    obtain ⟨rfl, right⟩ := Prod.mk.injEq _ _ _ _ ▸ h_eq
    congr
    exact DFunLike.coe_fn_eq.mp right
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
  (SimpleGraph.Embedding.map_adj_iff G.type_embed).symm

omit [Fintype T] in
theorem iso_type_Adj_iff
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (u v : G.type_verts)
    : σ.Adj (G.iso_type_G.symm u) (G.iso_type_G.symm v) ↔ G.graph.Adj u v := by
  let u_t := G.iso_type_G.symm u
  have h_ut : G.iso_type_G u_t = u := G.iso_type_G.apply_symm_apply u
  let v_t := G.iso_type_G.symm v
  have h_vt : G.iso_type_G v_t = v := G.iso_type_G.apply_symm_apply v
  rw [type_embed_Adj_iff G u_t v_t, ← h_ut, ← h_vt]
  rfl


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
    subgraph := ⊤
    type_embed := {
      toFun t := ⟨G.type_embed t, trivial⟩
      inj' := by
        intro t₁ t₂ h_eq
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact h_eq
      map_rel_iff' := by
        intro t₁ t₂
        simp only [SimpleGraph.Subgraph.top_adj, Function.Embedding.coeFn_mk,
          SimpleGraph.Subgraph.coe_adj, SimpleGraph.Embedding.map_adj_iff]
    }
    embed_eq := by
      intro t
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  }

lemma LabeledGraph.top_isInduced (G : LabeledGraph σ V)
  : G.top.subgraph.IsInduced := fun _ _ _ _ ↦ id

def LabeledGraph.bottom (G : LabeledGraph σ V) : LabeledSubgraph σ G :=
  {
    subgraph := {
      verts := G.type_verts
      Adj := fun u v => u ∈ G.type_verts ∧ v ∈ G.type_verts ∧ G.graph.Adj u v
      adj_sub := by tauto
      edge_vert := by tauto
      symm := by tauto
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, G.type_verts_contain t⟩
      inj' := by
        intro t₁ t₂ h_eq
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_eq
        exact h_eq
      map_rel_iff' := by
        simp only [Function.Embedding.coeFn_mk, SimpleGraph.Subgraph.coe_adj,
          SimpleGraph.Embedding.map_adj_iff, G.type_verts_contain, true_and, implies_true]
    }
    embed_eq := by
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, implies_true]
  }

lemma LabeledGraph.bottom_isInduced (G : LabeledGraph σ V)
  : G.bottom.subgraph.IsInduced := by tauto

namespace LabeledSubgraph

def IsInduced {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) : Prop
  :=
  H.subgraph.IsInduced

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
  rfl.to_iff

noncomputable instance labeledSubgraphFintype
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V] (G : LabeledGraph σ V)
    : Fintype (LabeledSubgraph σ G)
  :=
  let f : LabeledSubgraph σ G → G.graph.Subgraph × (T → V) :=
    fun ⟨G', embed, _⟩ ↦ (G', fun t ↦ embed.toFun t)
  have f_inj : Function.Injective f := by
    rintro ⟨G, φ, embed_eq⟩ ⟨G', φ', embed_eq'⟩ h_eq
    obtain ⟨rfl, _⟩ := Prod.mk.injEq _ _ _ _ ▸ h_eq
    simp only [mk.injEq, true_and, heq_eq_eq]
    ext x; simp only [embed_eq, embed_eq']
  Fintype.ofInjective f f_inj

omit [Fintype T] in
theorem labeledSubgraph_contain_type_verts
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (H : LabeledSubgraph σ G)
    : G.type_verts ⊆ H.subgraph.verts
  := by
  intro v hv
  obtain ⟨t, rfl⟩ := LabeledGraph.mem_type_verts.mp hv
  exact H.embed_eq t ▸ Subtype.coe_prop _

def inducedLabeledSubgraph
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : LabeledSubgraph σ G where
  subgraph := inducedSubgraph G.graph S
  type_embed := {
    toFun := by
      intro t
      exact ⟨G.type_embed t, h (LabeledGraph.type_verts_contain _ _)⟩
    inj' := by
      intro t u h_tu
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h_tu
      exact h_tu
    map_rel_iff' := by
      intros
      dsimp [inducedSubgraph]
      simp only [SimpleGraph.Embedding.map_adj_iff, and_iff_left_iff_imp]
      intro _
      constructor <;> exact h (LabeledGraph.type_verts_contain _ _)
  }
  embed_eq := by
    intro; simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_verts
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).subgraph.verts = S
  := by
  simp only [inducedLabeledSubgraph, inducedSubgraph_verts]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_size
    {σ : FlagType T} {V : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).size = Fintype.card S
  := by
  dsimp [LabeledSubgraph.size]
  rw [inducedLabeledSubgraph_verts G S h]

omit [Fintype T] in
@[simp]
theorem inducedLabeledSubgraph_isInduced
    {σ : FlagType T} {V : Type} (G : LabeledGraph σ V) (S : Set V) (h : G.type_verts ⊆ S)
    : (inducedLabeledSubgraph G S h).IsInduced
  :=
  inducedSubgraph_isInduced G.graph S

omit [Fintype T] in
theorem inducedLabeledSubgraph_eq
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} {H : LabeledSubgraph σ G} (h_H_ind : H.IsInduced)
    : H = inducedLabeledSubgraph G H.subgraph.verts (labeledSubgraph_contain_type_verts G H)
  := by
  dsimp [inducedLabeledSubgraph]
  congr!
  . exact inducedSubgraph_eq h_H_ind
  . simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, H.embed_eq]

omit [Fintype T] in
theorem isInduced_exist_induce_set
    {σ : FlagType T} {V : Type} {G : LabeledGraph σ V} (H : LabeledSubgraph σ G) (h_ind : H.IsInduced)
    : ∃ (S : Set V) (h : G.type_verts ⊆ S), inducedLabeledSubgraph G S h = H
  := by
  let S := H.subgraph.verts
  have h : G.type_verts ⊆ S := labeledSubgraph_contain_type_verts G H
  use S, h
  dsimp [inducedLabeledSubgraph]
  have hH_graph : inducedSubgraph G.graph S = H.subgraph := Eq.symm (inducedSubgraph_eq h_ind)
  congr
  · congr!
  · funext t
    congr
    exact (H.embed_eq t).symm
  all_goals apply proof_irrel_heq

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

variable {T : Type} [Fintype T] {σ : FlagType T}
variable {V W U : Type}
variable {G : LabeledGraph σ V} {G' : LabeledGraph σ W} {G'' : LabeledGraph σ U}

@[refl]
def refl : G ≃f G where
  graph_iso := by rfl
  type_preserve := by ext t; rw [Function.comp_apply, RelIso.refl_apply]

@[symm]
def symm (h : G ≃f G') : G' ≃f G where
  graph_iso := h.graph_iso.symm
  type_preserve := by
    ext t
    rw [←h.type_preserve]
    simp only [Function.comp_apply, RelIso.symm_apply_apply]

def trans (h : G ≃f G') (h' : G' ≃f G'') : G ≃f G'' where
  graph_iso := RelIso.trans h.graph_iso h'.graph_iso
  type_preserve := by
    rw [← h'.type_preserve, ← h.type_preserve]
    simp only [SimpleGraph.Iso.coe_comp]
    exact rfl

def labeledSubgraphIso_eq
  {G : LabeledGraph σ V} {F F' : LabeledSubgraph σ G} (h : F = F') : F.coe ≃f F'.coe := h ▸ LabeledGraphIso.refl

end LabeledGraphIso

/-- Suggestion: Use `Inhabited` instead of `Nonempty`. -/
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
  exact Quotient.fintype (labeledGraphSetoid σ V)

theorem Flag.type_eq
    {T : Type} {σ : FlagType T} {Vl Vl' : Fin t → Type} (h_Vl_eq : Vl' = Vl) (i : Fin t)
    : Flag σ (Vl' i) = Flag σ (Vl i) := by
  rw [h_Vl_eq]

omit [Fintype T] in
theorem flagEqv.sound {σ : FlagType T} {V : Type} {G G' : LabeledGraph σ V} (h : G ∼f G')
    : (⟦G⟧ : Flag σ V) = (⟦G'⟧ : Flag σ V)
  :=
  Quotient.sound h

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
    {σ : FlagType T} {U V : Type} (G₀ : LabeledGraph σ U) (G₁ : LabeledGraph σ V)
    : LabeledGraphList σ 2 (fun i => match i with | 0 => U | 1 => V)
  :=
  fun i => match i with | 0 => G₀ | 1 => G₁

def labeledGraphTripleToList
    {σ : FlagType T} {U V W : Type} (G₀ : LabeledGraph σ U) (G₁ : LabeledGraph σ V) (G₂ : LabeledGraph σ W)
    : LabeledGraphList σ 3 (fun i => match i with | 0 => U | 1 => V | 2 => W)
  :=
  fun i => match i with | 0 => G₀ | 1 => G₁ | 2 => G₂

notation "[" G "]ᵍ" => (labeledGraphToList G)
notation "[" G₀ "," G₁ "]ᵍ" => (labeledGraphPairToList G₀ G₁)
notation "[" G₀ "," G₁ "," G₂ "]ᵍ" => (labeledGraphTripleToList G₀ G₁ G₂)

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
    rw [cast_eq]
    ext1 i
    exact h_Fl_eq i
  subst h_Vl_eq h_Fl_cast
  exact HEq.refl Fl

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
    rw [← Gl.out_eq]
    apply Quotient.sound
    intro i
    simp only [Quotient.out_eq]
    exact Quotient.mk_out (Gl.out i)
  right_inv Fl := by
    simp only; ext i
    refine (Fl i).out_eq ▸ Quotient.sound (flagEqv.trans ?_ (flagEqv.refl (Quotient.out (Fl i))))
    show _ ∼f Quotient.out (Fl i)
    have : ⟦fun i ↦ Quotient.out (Fl i)⟧.out ∼fl (fun i ↦ Quotient.out (Fl i)) :=
      Quotient.mk_out fun i ↦ (Fl i).out
    exact this i

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
  :=
  Quotient.sound fun _ ↦ flagEqv.symm (Quotient.mk_out G)

omit [Fintype T] in
theorem list_quot_eq_quot_list_pair
    {σ : FlagType T} {V W : Type} (G : LabeledGraph σ V) (G' : LabeledGraph σ W)
    : ⟦[G, G']ᵍ⟧ = [⟦G⟧, ⟦G'⟧]ᶠ.coe
  :=
  Quotient.sound fun i ↦ match i with
  | 0 => flagEqv.symm (Quotient.mk_out G)
  | 1 => flagEqv.symm (Quotient.mk_out G')

omit [Fintype T] in
theorem list_quot_eq_quot_list_triple
    {σ : FlagType T} {V W U : Type} (G : LabeledGraph σ V) (G' : LabeledGraph σ W) (G'' : LabeledGraph σ U)
    : ⟦[G, G', G'']ᵍ⟧ = [⟦G⟧, ⟦G'⟧, ⟦G''⟧]ᶠ.coe
  :=
  Quotient.sound fun i ↦ match i with
  | 0 => flagEqv.symm (Quotient.mk_out G)
  | 1 => flagEqv.symm (Quotient.mk_out G')
  | 2 => flagEqv.symm (Quotient.mk_out G'')

/- FlagList.insert -/

def listTypeInsert {t : ℕ} (Vl : Fin t → Type) (W : Type)
    : Fin (t + 1) → Type
  :=
  fun i => if h : i.val = t then W else Vl (i.coe h)

theorem listTypeInsert_eq {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val = t)
    : W = listTypeInsert Vl W i
  := by
  simp only [listTypeInsert, hi, ↓reduceDIte]

theorem listTypeInsert_eq' {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Vl (i.coe hi) = listTypeInsert Vl W i
  := by
  simp only [listTypeInsert, hi, ↓reduceDIte]

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

noncomputable def flag_heq_to_iso {σ : FlagType T} {W : Type} {V : Type}
    {F₁ : Flag σ W} {F₂ : Flag σ V} (type_eq : W = V) (hHEq : HEq F₁ F₂)
    : F₁.out ≃f F₂.out := by
  subst type_eq hHEq
  rfl

omit [Fintype T] in
theorem insert_new_flag_cast_iso {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (_ : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val = t)
    : Nonempty (F.out ≃f (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F).out) :=
  Nonempty.intro <| flag_heq_to_iso (listTypeInsert_eq hi) (cast_heq _ _).symm

omit [Fintype T] in
theorem insert_preserves_existing_flags {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (_ : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : Nonempty ((Fl (i.coe hi)).out ≃f (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))).out) :=
  Nonempty.intro <| flag_heq_to_iso (listTypeInsert_eq' hi) (cast_heq _ _).symm

omit [Fintype T] in
theorem insert_preserves_existing_flags_coe {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin t} (hi₀ : i.val ≠ t)
    : Nonempty ((Fl i).out ≃f (Fl.insert F i.castSucc).out) := by
  dsimp [FlagList.insert]
  split
  next hi' =>
    have : i % (t + 1) = i := by rw [Nat.mod_succ_eq_iff_lt]; omega
    exact (hi₀ (this ▸ hi')).elim
  next hi =>
    have hi' : i.castSucc.val ≠ t := hi
    let cast_iso := Classical.choice (insert_preserves_existing_flags Fl F hi')
    have idx_heq : HEq (Fl i) (Fl (i.castSucc.coe hi)) := flaglist_heq_of_idx_eq rfl
    exact Nonempty.intro <| (flag_heq_to_iso rfl idx_heq).trans cast_iso

omit [Fintype T] in
theorem cast_preserves_flag_size {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    [FintypeList Vl] [DecidableEqList Vl] [Fintype W] [DecidableEq W]
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val = t)
    : F.out.size = (cast (@flag_listTypeInsert_eq T σ t Vl W i hi) F).out.size
  := labeledGraphIso_size_eq F.out
                             (cast (flag_listTypeInsert_eq hi) F).out
                             (Classical.choice (insert_new_flag_cast_iso Fl F hi))

omit [Fintype T] in
theorem cast_preserves_flag_size' {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    [FintypeList Vl] [DecidableEqList Vl] [Fintype W] [DecidableEq W]
    (Fl : FlagList σ t Vl) (F : Flag σ W)
    {i : Fin (t + 1)} (hi : i.val ≠ t)
    : (Fl (i.coe hi)).out.size = (cast (@flag_listTypeInsert_eq' T σ t Vl W i hi) (Fl (i.coe hi))).out.size
  := labeledGraphIso_size_eq (Fl (i.coe hi)).out
                             (cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi))).out
                             (Classical.choice (insert_preserves_existing_flags Fl F hi))


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
    dsimp [listTypePermute]
    infer_instance

noncomputable instance decidableEqListPermute
    {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (π : Perm t)
    : @DecidableEqList t (listTypePermute Vl π) where
  decidable_eq_all i := by
    infer_instance

def FlagList.permute {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    (Fl : FlagList σ t Vl) (π : Perm t)
    : FlagList σ t (listTypePermute Vl π)
  :=
  fun i => Fl (π i)

end FlagAlgebras
