import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph

class FintypeExist (α : Type) where
  fintype_exist : Nonempty (Fintype α)

class DecidableEqExist (α : Type) where
  decidable_eq_exist : Nonempty (DecidableEq α)

noncomputable instance (α : Type) [FintypeExist α] : Fintype α
  :=
  Classical.choice (FintypeExist.fintype_exist)

noncomputable instance (α : Type) [DecidableEqExist α] : DecidableEq α
  :=
  Classical.choice (DecidableEqExist.decidable_eq_exist)

variable {T : Type} [FintypeExist T]

abbrev FlagType := SimpleGraph

noncomputable def FlagType.size (_ : FlagType T) : ℕ
  :=
  Fintype.card T

@[ext]
structure LabeledGraph (σ : FlagType T) (V : Type) where
  graph : SimpleGraph V
  type_embed : σ ↪g graph

noncomputable instance labeledGraphFintype (σ : FlagType T) (V : Type) [FintypeExist V] [DecidableEqExist V]
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

noncomputable def LabeledGraph.size
    {σ : FlagType T} {V : Type} [FintypeExist V] [DecidableEqExist V] (_ : LabeledGraph σ V) : ℕ
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
    {V : Type} [FintypeExist V] [DecidableEqExist V] (G : SimpleGraph V) : Fintype (G.Subgraph)
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
    {σ : FlagType T} {V : Type} [FintypeExist V] [DecidableEqExist V] (G : LabeledGraph σ V)
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

end LabeledSubgraph

structure LabeledGraphIso {σ : FlagType T} {V W : Type}
  (G : LabeledGraph σ V) (G' : LabeledGraph σ W) where
  graph_iso : G.graph ≃g G'.graph
  type_preserve : graph_iso ∘ G.type_embed = G'.type_embed

infixl:50 " ≃f " => LabeledGraphIso

namespace LabeledGraphIso

variable {T : Type} [FintypeExist T] {σ : FlagType T} {V W U : Type}
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

omit [FintypeExist T] in
theorem flagEqv.refl {σ : FlagType T} (G : LabeledGraph σ V)
    : G ∼f G
  :=
  Nonempty.intro LabeledGraphIso.refl

omit [FintypeExist T] in
theorem flagEqv.symm {σ : FlagType T}
    : ∀ {G G' : LabeledGraph σ V}, G ∼f G' → G' ∼f G
  := by
  intro G G' h
  have G_iso : G ≃f G' := Classical.choice h
  exact Nonempty.intro G_iso.symm

omit [FintypeExist T] in
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

noncomputable instance FlagFintype (σ : FlagType T) (V : Type) [FintypeExist V] [DecidableEqExist V]
    : Fintype (Flag σ V)
  := by
  classical
  exact Quotient.fintype (labeledGraphSetoid σ V)

omit [FintypeExist T] in
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
  fintype_all : ∀ (i : Fin t), FintypeExist (Vl i)

class DecidableEqList {t : ℕ} (Vl : Fin t → Type) where
  decidable_eq_all : ∀ (i : Fin t), DecidableEqExist (Vl i)

noncomputable instance fintype_V {t : ℕ} (Vl : Fin t → Type) [FintypeList Vl] (i : Fin t) : FintypeExist (Vl i)
  :=
  FintypeList.fintype_all i

noncomputable instance decidable_eq_V {t : ℕ} (Vl : Fin t → Type) [DecidableEqList Vl] (i : Fin t) : DecidableEqExist (Vl i)
  :=
  DecidableEqList.decidable_eq_all i

abbrev LabeledGraphList (σ : FlagType T) (t : ℕ) (Vl : Fin t → Type) := ∀ (i : Fin t), LabeledGraph σ (Vl i)

def flagListEqv {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Gl Gl' : LabeledGraphList σ t Vl) : Prop
  :=
  ∀ (i : Fin t), Gl i ∼f Gl' i

infixl:50 " ∼fl " => flagListEqv

omit [FintypeExist T] in
theorem flagListEqv.refl {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} (Gl : LabeledGraphList σ t Vl)
    : Gl ∼fl Gl
  :=
  fun i => flagEqv.refl (Gl i)

omit [FintypeExist T] in
theorem flagListEqv.symm {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    : ∀ {Gl Gl' : LabeledGraphList σ t Vl}, Gl ∼fl Gl' → Gl' ∼fl Gl
  :=
  fun h i => flagEqv.symm (h i)

omit [FintypeExist T] in
theorem flagListEqv.trans {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type}
    : ∀ {Gl Gl' Gl'' : LabeledGraphList σ t Vl}, Gl ∼fl Gl' → Gl' ∼fl Gl'' → Gl ∼fl Gl''
  :=
  fun h h' i => flagEqv.trans (h i) (h' i)

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

instance fintypeSingletonList {V : Type} [FintypeExist V]
    : FintypeList (fun (_ : Fin 1) => V)
  :=
  { fintype_all := fun _ ↦ inferInstance }

instance decidableEqSingletonList {V : Type} [DecidableEqExist V]
    : DecidableEqList (fun (_ : Fin 1) => V)
  :=
  { decidable_eq_all := fun _ ↦ inferInstance }

instance fintypePairList {V W : Type} [FintypeExist V] [FintypeExist W]
    : FintypeList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance decidableEqPairList {V W : Type} [DecidableEqExist V] [DecidableEqExist W]
    : DecidableEqList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance fintypeTripleList {V W U : Type} [FintypeExist V] [FintypeExist W] [FintypeExist U]
    : FintypeList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

instance decidableEqTripleList {V W U : Type} [DecidableEqExist V] [DecidableEqExist W] [DecidableEqExist U]
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

/- FlagList.insert -/

def Fin.coe {t : ℕ} (i : Fin (t + 1)) (hi : i.val ≠ t) : Fin t
  :=
  ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.is_lt) hi⟩

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
    {t : ℕ} (Vl : Fin t → Type) (W : Type) [FintypeExist W] [FintypeList Vl]
    : @FintypeList (t + 1) (listTypeInsert Vl W) where
  fintype_all i := if h : i.val = t
    then (by rw [← listTypeInsert_eq h]; infer_instance)
    else (by rw [← listTypeInsert_eq' h]; infer_instance)

noncomputable instance decidableEqListInsert
    {t : ℕ} (Vl : Fin t → Type) (W : Type) [DecidableEqExist W] [DecidableEqList Vl]
    : @DecidableEqList (t + 1) (listTypeInsert Vl W) where
  decidable_eq_all i := if h : i.val = t
    then (by rw [← listTypeInsert_eq h]; infer_instance)
    else (by rw [← listTypeInsert_eq' h]; infer_instance)

omit [FintypeExist T] in
theorem flag_listTypeInsert_eq {σ : FlagType T} {t : ℕ} {Vl : Fin t → Type} {W : Type}
    {i : Fin (t + 1)} (hi : i.val = t)
    : Flag σ W = Flag σ (listTypeInsert Vl W i)
  := by
  rw [← listTypeInsert_eq hi]

omit [FintypeExist T] in
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
