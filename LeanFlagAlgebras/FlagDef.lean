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

def emptyLabeledGraph (σ : FlagType T) : LabeledGraph σ T
  :=
  ⟨σ, SimpleGraph.Embedding.refl⟩

@[ext]
structure LabeledSubgraph (σ : FlagType T) {V : Type} (G : LabeledGraph σ V) where
  subgraph : G.graph.Subgraph
  type_embed : σ ↪g subgraph.coe
  embed_eq : ∀ (t : T), type_embed t = G.type_embed t

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

noncomputable instance FlagFintype (σ : FlagType T) (V : Type) [Fintype V] [DecidableEq V] : Fintype (Flag σ V)
  := by
  classical
  exact Quotient.fintype (labeledGraphSetoid σ V)

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

/-- TODO START --/
class FintypeList {t : ℕ} (Vl : Fin t → Type) where
  fintype_all : ∀ (i : Fin t), Fintype (Vl i)

class DecidableEqList {t : ℕ} (Vl : Fin t → Type) where
  decidable_eq_all : ∀ (i : Fin t), DecidableEq (Vl i)

instance fintype_V {t : ℕ} (Vl : Fin t → Type) [FintypeList Vl] (i : Fin t) : Fintype (Vl i)
  :=
  FintypeList.fintype_all i

instance decidable_eq_V {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (i : Fin t) : DecidableEq (Vl i)
  :=
  DecidableEqList.decidable_eq_all i
/-- TODO END --/

abbrev LabeledGraphList (σ : FlagType T) := List (Σ (V : Type), LabeledGraph σ V)

def flagListEqv {σ : FlagType T} (Gl Gl' : LabeledGraphList σ) : Prop
  :=
  if hl_eq : Gl.length = Gl'.length
  then ∀ (i : Fin Gl.length), Gl[i].1 = Gl'[i].1 ∧ Nonempty (Gl[i].2 ≃f Gl'[i].2)
  else false

infixl:50 " ∼fl' " => flagListEqv

omit [Fintype T] in
theorem flagListEqv.refl {σ : FlagType T} (Gl : LabeledGraphList σ)
    : Gl ∼fl' Gl
  := by
  simp [flagListEqv]
  intro i
  apply flagEqv.refl

omit [Fintype T] in
theorem flagListEqv.symm {σ : FlagType T}
    : ∀ {Gl Gl' : LabeledGraphList σ}, Gl ∼fl' Gl' → Gl' ∼fl' Gl
  := by
  intro Gl Gl'
  simp [flagListEqv]
  intro h₀ h₁
  use h₀.symm
  intro i
  obtain ⟨h_fst, h_snd⟩ := h₁ (i.cast h₀.symm)
  simp_all [Fin.coe_cast]
  exact Nonempty.intro (Classical.choice h_snd).symm

omit [Fintype T] in
theorem flagListEqv.trans {σ : FlagType T}
    : ∀ {Gl Gl' Gl'' : LabeledGraphList σ}, Gl ∼fl' Gl' → Gl' ∼fl' Gl'' → Gl ∼fl' Gl''
  := by
  intro Gl Gl' Gl''
  simp [flagListEqv]
  intro h₀ h₁ h₀' h₁'
  use (h₀.trans h₀')
  intro i
  obtain ⟨h_fst, h_snd⟩ := h₁ i
  obtain ⟨h_fst', h_snd'⟩ := h₁' (i.cast h₀)
  simp [Fin.coe_cast] at *
  constructor
  · exact h_fst.trans h_fst'
  · exact Nonempty.intro ((Classical.choice h_snd).trans (Classical.choice h_snd'))

instance {σ : FlagType T} : Trans (@flagListEqv T σ) (@flagListEqv T σ) (@flagListEqv T σ) where
  trans := flagListEqv.trans

instance labeledGraphListSetoid (σ : FlagType T)
    : Setoid (LabeledGraphList σ)
  where
    r     := flagListEqv
    iseqv := {
      refl  := flagListEqv.refl,
      symm  := flagListEqv.symm,
      trans := flagListEqv.trans
    }

def QuotLabeledGraphList (σ : FlagType T) : Type 1 :=
  Quotient (labeledGraphListSetoid σ)

abbrev FlagList (σ : FlagType T) := List (Σ (V : Type), Flag σ V)

def flagToList {σ : FlagType T} {V : Type} (F : Flag σ V)
    : FlagList σ
  :=
  [⟨V, F⟩]

def flagPairToList {σ : FlagType T} {V W : Type} (F : Flag σ V) (G : Flag σ W)
    : FlagList σ
  :=
  [⟨V, F⟩, ⟨W, G⟩]

def flagTripleToList {σ : FlagType T} {V W U : Type} (F : Flag σ V) (G : Flag σ W) (H : Flag σ U)
    : FlagList σ
  :=
  [⟨V, F⟩, ⟨W, G⟩, ⟨U, H⟩]

notation "[" F "]ᶠ" => (flagToList F)
notation "[" F "," G "]ᶠ" => (flagPairToList F G)
notation "[" F "," G "," H "]ᶠ" => (flagTripleToList F G H)

/-- TODO START --/
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
/-- TODO END --/

def labeledGraphList_to_flagList {σ : FlagType T} (Gl : LabeledGraphList σ)
    : FlagList σ
  :=
  Gl.map (fun ⟨V, G⟩ => ⟨V, ⟦G⟧⟩)

noncomputable def flagList_to_labeledGraphList {σ : FlagType T} (Fl : FlagList σ)
    : LabeledGraphList σ
  :=
  Fl.map (fun ⟨V, F⟩ => ⟨V, F.out⟩)

omit [Fintype T] in
theorem flagList_to_labeledGraphList_to_flagList
    {σ : FlagType T} (Fl : FlagList σ)
    : labeledGraphList_to_flagList (flagList_to_labeledGraphList Fl) = Fl
  := by
  simp [flagList_to_labeledGraphList, labeledGraphList_to_flagList]
  apply List.map_id''
  simp

theorem List.ext_getElem' {A B : List α} (hl : A.length = B.length) (h : ∀ (i : Fin A.length), A[i] = B[i]) : A = B := by
  apply List.ext_get_iff.mpr
  constructor
  · exact hl
  · intro i h' _
    exact h ⟨i, h'⟩

omit [Fintype T] in
theorem quot_labeledGraph_HEq {σ : FlagType T} {V W : Type} (h_type_eq : V = W)
    {G : LabeledGraph σ V} {G' : LabeledGraph σ W} (h_iso : Nonempty (G ≃f G'))
    : HEq (⟦G⟧ : Flag σ V) (⟦G'⟧ : Flag σ W)
  := by
  subst h_type_eq
  simp_all only [heq_eq_eq, Quotient.eq]
  exact h_iso

lemma labeledGraphList_to_flagList_eq {Gl Gl' : LabeledGraphList σ} (h_eqv : Gl ∼fl' Gl')
    : labeledGraphList_to_flagList Gl = labeledGraphList_to_flagList Gl'
  := by
  simp [flagListEqv] at h_eqv
  obtain ⟨hl, h⟩ := h_eqv
  simp [labeledGraphList_to_flagList]
  apply List.ext_getElem'
  · intro i
    simp [List.getElem_map]
    have hl_eq := @List.length_map (Σ (V : Type), LabeledGraph σ V) (Σ (V : Type), Flag σ V) Gl (fun ⟨V, G⟩ => ⟨V, ⟦G⟧⟩)
    have h_type_eq := (h (i.cast hl_eq)).1
    have h_iso := (h (i.cast hl_eq)).2
    constructor
    · exact h_type_eq
    · exact quot_labeledGraph_HEq h_type_eq h_iso
  · rw [List.length_map, List.length_map]
    exact hl

noncomputable instance eqv_QuotLabeledGraphList_FlagList (σ : FlagType T)
    : QuotLabeledGraphList σ ≃ FlagList σ where
  toFun := fun Gl => Gl.out.map (fun ⟨V, G⟩ => ⟨V, ⟦G⟧⟩)
  invFun := fun Fl => ⟦Fl.map (fun ⟨V, F⟩ => ⟨V, F.out⟩)⟧
  left_inv Gl := by
    nth_rw 2 [← Quotient.out_eq Gl]
    apply Quotient.sound
    show flagListEqv _ _
    simp [flagListEqv]
    intro i
    apply Nonempty.intro
    repeat rw [List.getElem_map]
    simp
    exact Classical.choice (Quotient.mk_out (Gl.out[i].2))
  right_inv Fl := by
    show labeledGraphList_to_flagList _ = Fl
    nth_rw 2 [← flagList_to_labeledGraphList_to_flagList Fl]
    apply labeledGraphList_to_flagList_eq
    show ⟦flagList_to_labeledGraphList Fl⟧.out ∼fl' _
    apply Quotient.mk_out (flagList_to_labeledGraphList Fl)

@[simp]
noncomputable def QuotLabeledGraphList.coe {σ : FlagType T} (Gl : QuotLabeledGraphList σ)
    : FlagList σ
  :=
  (eqv_QuotLabeledGraphList_FlagList σ).toFun Gl

@[simp]
noncomputable def FlagList.coe {σ : FlagType T} (Fl : FlagList σ)
    : QuotLabeledGraphList σ
  :=
  (eqv_QuotLabeledGraphList_FlagList σ).invFun Fl
