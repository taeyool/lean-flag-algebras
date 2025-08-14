import «LeanFlagAlgebras».FlagDef
import «LeanFlagAlgebras».SubflagDensity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


open FlagAlgebras
open LabeledSubgraph
open Classical

variable {T : Type}  [Fintype T]  [DecidableEq T]
variable {V : Type}  [Fintype V]  [DecidableEq V]
variable {W : Type}  [Fintype W]  [DecidableEq W]
variable {U : Type}  [Fintype U]  [DecidableEq U]
variable {U₁ : Type} [Fintype U₁] [DecidableEq U₁]
variable {U₂ : Type} [Fintype U₂] [DecidableEq U₂]
variable {U₃ : Type} [Fintype U₃] [DecidableEq U₃]
variable {σ : FlagType T} {t : ℕ}
variable {Vl  : Fin t → Type} [FintypeList Vl]  [DecidableEqList Vl]
variable {Vl' : Fin t → Type} [FintypeList Vl'] [DecidableEqList Vl']

abbrev LabeledSubgraphList (σ : FlagType T) (t : ℕ) (G : LabeledGraph σ U)
  := Fin t → LabeledSubgraph σ G

def LabeledSubgraphList.IsInduced
    {σ : FlagType T} {t : ℕ} {G : LabeledGraph σ U} (Hl : LabeledSubgraphList σ t G) : Prop
  := ∀ (i : Fin t), (Hl i).IsInduced

def predIsoLabeledHl
    {σ : FlagType T} (G : LabeledGraph σ V) (Hl : LabeledGraphList σ t Vl)
    : LabeledSubgraphList σ t G → Prop
  := fun Gl ↦
      (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i))
      ∧ (∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅)

def setOfLabeledSubgraphListIsoHl (G : LabeledGraph σ U) (Hl : LabeledGraphList σ t Vl)
      : Set (LabeledSubgraphList σ t G)
  :=
  { Gl | Gl.IsInduced ∧ predIsoLabeledHl G Hl Gl }

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℕ
  :=
  have : Fintype (setOfLabeledSubgraphListIsoHl G Hl) := Fintype.ofFinite _
  (setOfLabeledSubgraphListIsoHl G Hl).toFinset.card

def multinomialCoefficient
    (r_list : Fin t → ℕ) (n : ℕ) : ℕ
  :=
  let r_sum := ∑ i : Fin t, r_list i
  if _ : n ≥ r_sum then
    Nat.factorial n / ((∏ i : Fin t, Nat.factorial (r_list i)) * Nat.factorial (n - r_sum))
  else 0

lemma multinomialCoefficient_eq
    {r_list₁ r_list₂ : Fin t → ℕ} (n : ℕ) (heq : r_list₁ = r_list₂)
    : multinomialCoefficient r_list₁ n = multinomialCoefficient r_list₂ n
  := by subst heq; rfl

lemma multinomialCoefficient_pos
    (r_list : Fin t → ℕ) (n : ℕ) (h_n : n ≥ ∑ i : Fin t, r_list i) :
    multinomialCoefficient r_list n > 0
  := by
  dsimp [multinomialCoefficient]
  split
  next h_sum_le_n =>
    let r_sum := ∑ i : Fin t, r_list i
    let C₀ := ∏ i : Fin t, (r_list i).factorial
    let C₁ := (n - r_sum).factorial
    let C := C₀ * C₁
    show n.factorial / C > 0
    have h_n_factorial_pos : n.factorial > 0 := Nat.factorial_pos n
    have h_dvd : C ∣ n.factorial := by
      have h₀ : C₀ ∣ r_sum.factorial := by
        dsimp [C₀, r_sum]
        exact Nat.prod_factorial_dvd_factorial_sum Finset.univ r_list
      have h₁ : C ∣ r_sum.factorial * C₁ := Nat.mul_dvd_mul_right h₀ C₁
      have h₂ : r_sum.factorial * C₁ ∣ n.factorial :=
        Nat.factorial_mul_factorial_dvd_factorial h_sum_le_n
      exact dvd_trans h₁ h₂
    exact (Nat.lt_div_iff_mul_lt' h_dvd 0).mpr h_n_factorial_pos
  next h_not_sum_lt_n =>
    exact False.elim (h_not_sum_lt_n h_n)


noncomputable def labeledSubgraphListDensity
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list (i : Fin t) := (Hl i).size - σ.size
  labeledSubgraphListCount Hl G / multinomialCoefficient r_list (G.size - σ.size)

def relOfLabeledSubgraphList
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraphList σ t G₀)
    (H₁ : LabeledSubgraphList σ t G₁) : Prop
  :=
  ∀ (i : Fin t), relOfLabeledSubgraph φ (H₀ i) (H₁ i)

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma relOfLabeledSubgraphList_symm
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} {φ : G₀ ≃f G₁}
    {H₀ : LabeledSubgraphList σ t G₀} {H₁ : LabeledSubgraphList σ t G₁}
    (h_rel : relOfLabeledSubgraphList φ H₀ H₁)
    : relOfLabeledSubgraphList φ.symm H₁ H₀
  := by
  intro i
  exact relOfLabeledSubgraph_symm (h_rel i)

omit [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma relOfLabeledSubgraphList_indep
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} {φ : G₀ ≃f G₁}
    {Hl₀ : LabeledSubgraphList σ t G₀} {Hl₁ : LabeledSubgraphList σ t G₁}
    (h_rel : relOfLabeledSubgraphList φ Hl₀ Hl₁)
    : ∀ (i j : Fin t),
        (((Hl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Hl₀ j).subgraph.verts \ G₀.type_verts) = ∅)
        → (((Hl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Hl₁ j).subgraph.verts \ G₁.type_verts) = ∅)
  := by
  have h (k : Fin t) : φ.graph_iso '' ((Hl₀ k).subgraph.verts \ G₀.type_verts) = ((Hl₁ k).subgraph.verts \ G₁.type_verts)
    := by
    have ⟨h_Hl_verts, _⟩ := h_rel k
    have h_G_verts : G₁.type_verts = φ.graph_iso '' G₀.type_verts := by
      dsimp [LabeledGraph.type_verts]
      rw [←Set.image_comp φ.graph_iso G₀.type_embed Set.univ]
      rw [φ.type_preserve]
    rw [h_G_verts, h_Hl_verts]
    exact Set.image_diff φ.graph_iso.injective (Hl₀ k).subgraph.verts G₀.type_verts
  intro i j h_empty
  rw [←(h i), ←(h j)]
  rw [←Set.image_inter φ.graph_iso.injective, h_empty]
  exact Set.image_empty ⇑φ.graph_iso

def relOfPredOnLabeledSubgraphList
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraphList σ t G₀ → Prop) (p₁ : LabeledSubgraphList σ t G₁ → Prop) : Prop
  :=
  ∀ (H₀: LabeledSubgraphList σ t G₀) (H₁: LabeledSubgraphList σ t G₁),
      (relOfLabeledSubgraphList φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

omit [Fintype T] [DecidableEq T]
     [Fintype V] [DecidableEq V]
     [Fintype W] [DecidableEq W]
     [FintypeList Vl] [DecidableEqList Vl]
     [FintypeList Vl'] [DecidableEqList Vl'] in
lemma predIsoLabeledHl_related
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    {Hl₀ : LabeledGraphList σ t Vl} {Hl₁ : LabeledGraphList σ t Vl'} (ψ : ∀ (i : Fin t), Hl₀ i ≃f Hl₁ i)
    : relOfPredOnLabeledSubgraphList φ (predIsoLabeledHl G₀ Hl₀) (predIsoLabeledHl G₁ Hl₁)
  := by
  dsimp [relOfPredOnLabeledSubgraphList]
  intro Gl₀ Gl₁ h_rel
  constructor
  · intro ⟨h_1₀, h_2₀⟩
    have h_1₁ : ∀ (i : Fin t), Nonempty ((Gl₁ i).coe ≃f Hl₁ i)
      := fun i ↦ predIsoLabeledH_related_support φ (ψ i) (Gl₀ i) (Gl₁ i) (h_rel i) (h_1₀ i)
    have h_2₁ : ∀ (i j : Fin t), i ≠ j →
                  ((Gl₁ i).subgraph.verts \ G₁.type_verts) ∩ ((Gl₁ j).subgraph.verts \ G₁.type_verts) = ∅
      := fun i j h_ij ↦ relOfLabeledSubgraphList_indep h_rel i j (h_2₀ i j h_ij)
    exact ⟨h_1₁, h_2₁⟩
  · intro ⟨h_1₁, h_2₁⟩
    have h_rel_symm : relOfLabeledSubgraphList φ.symm Gl₁ Gl₀
      := fun i ↦ relOfLabeledSubgraph_symm (h_rel i)
    have h_1₀ : ∀ (i : Fin t), Nonempty ((Gl₀ i).coe ≃f Hl₀ i)
      := fun i ↦ predIsoLabeledH_related_support φ.symm (ψ i).symm (Gl₁ i) (Gl₀ i) (h_rel_symm i) (h_1₁ i)
    have h_2₀ : ∀ (i j : Fin t), i ≠ j →
                  ((Gl₀ i).subgraph.verts \ G₀.type_verts) ∩ ((Gl₀ j).subgraph.verts \ G₀.type_verts) = ∅
      := fun i j h_ij ↦ relOfLabeledSubgraphList_indep h_rel_symm i j (h_2₁ i j h_ij)
    exact ⟨h_1₀, h_2₀⟩

def inducedLabeledSubgraphList
    {σ : FlagType T} (G : LabeledGraph σ U) (Sl : Fin t → Set U) (hSl : ∀ i : Fin t, G.type_verts ⊆ Sl i)
    : LabeledSubgraphList σ t G
  := fun i ↦ inducedLabeledSubgraph G (Sl i) (hSl i)

omit [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U] in
lemma inducedLabeledSubgraphList_isInduced
    {σ : FlagType T} (G : LabeledGraph σ U) (Sl : Fin t → Set U) (hSl : ∀ i : Fin t, G.type_verts ⊆ Sl i)
    : (inducedLabeledSubgraphList G Sl hSl).IsInduced
  := fun i ↦ inducedLabeledSubgraph_isInduced G (Sl i) (hSl i)

def inducedLabeledSubgraphListByIso
    {σ : FlagType T} {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V}
    (φ : G₀ ≃f G₁) (Hl₀ : LabeledSubgraphList σ t G₀)
    : LabeledSubgraphList σ t G₁
  :=
  fun i ↦ inducedLabeledSubgraphByIso φ (Hl₀ i)

omit [Fintype T] [DecidableEq T]
     [Fintype U] [DecidableEq U]
     [Fintype V] [DecidableEq V] in
lemma inducedLabeledSubgraphListByIso_isInduced
    {σ : FlagType T} {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V}
    (φ : G₀ ≃f G₁) (Hl₀ : LabeledSubgraphList σ t G₀)
    : (inducedLabeledSubgraphListByIso φ Hl₀).IsInduced
  :=
  fun i ↦ inducedLabeledSubgraphByIso_isInduced φ (Hl₀ i)

omit [Fintype T] [DecidableEq T]
     [Fintype U] [DecidableEq U]
     [Fintype V] [DecidableEq V] in
lemma inducedLabeledSubgraphList_related
    {σ : FlagType T} {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    (Hl₀ : LabeledSubgraphList σ t G₀) (h_ind₀ : Hl₀.IsInduced)
    : relOfLabeledSubgraphList φ Hl₀ (inducedLabeledSubgraphListByIso φ Hl₀)
  := by
  dsimp [relOfLabeledSubgraphList, inducedLabeledSubgraphListByIso]
  intro i
  exact inducedLabeledSubgraph_related φ (Hl₀ i) (h_ind₀ i)

omit [Fintype T] [DecidableEq T]
     [Fintype U] [DecidableEq U]
     [Fintype V] [DecidableEq V] in
lemma Hl_eq_reverseinduced_induced_Hl
    {σ : FlagType T} {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V}
    (φ : G₀ ≃f G₁) (Hl₀ : LabeledSubgraphList σ t G₀) (h_ind₀ : Hl₀.IsInduced)
    : Hl₀ = inducedLabeledSubgraphListByIso φ.symm (inducedLabeledSubgraphListByIso φ Hl₀)
  := by
  funext i
  exact H_eq_reverseinduced_induced_H φ (Hl₀ i) (h_ind₀ i)

noncomputable def isoSetOfInducedLabeledSubgraphList
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraphList σ t G₀ → Prop) (p₁ : LabeledSubgraphList σ t G₁ → Prop)
    (h_rel : relOfPredOnLabeledSubgraphList φ p₀ p₁)
    : { Gl : LabeledSubgraphList σ t G₀ | Gl.IsInduced ∧ p₀ Gl } ≃ { Gl : LabeledSubgraphList σ t G₁ | Gl.IsInduced ∧ p₁ Gl }
  :=
  let S₀ := { Gl : LabeledSubgraphList σ t G₀ | Gl.IsInduced ∧ p₀ Gl }
  let S₁ := { Gl : LabeledSubgraphList σ t G₁ | Gl.IsInduced ∧ p₁ Gl }
  let f : S₀ → S₁ := by
    intro s₀
    let ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
    let Hl₁ := inducedLabeledSubgraphListByIso φ Hl₀
    let h_ind₁ : Hl₁.IsInduced := inducedLabeledSubgraphListByIso_isInduced φ Hl₀
    have : relOfLabeledSubgraphList φ Hl₀ Hl₁ := inducedLabeledSubgraphList_related φ Hl₀ h_ind₀
    have h_p₁ : p₁ Hl₁ := (h_rel Hl₀ Hl₁ this).mp h_p₀
    exact ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv : S₁ → S₀ := by
    intro s₁
    let ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let Hl₀ := inducedLabeledSubgraphListByIso φ.symm Hl₁
    let h_ind₀ : Hl₀.IsInduced := inducedLabeledSubgraphListByIso_isInduced φ.symm Hl₁
    have : relOfLabeledSubgraphList φ.symm Hl₁ Hl₀ := inducedLabeledSubgraphList_related φ.symm Hl₁ h_ind₁
    have : relOfLabeledSubgraphList φ Hl₀ Hl₁ := relOfLabeledSubgraphList_symm this
    have h_p₀ : p₀ Hl₀ := (h_rel Hl₀ Hl₁ this).mpr h_p₁
    exact ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv]
      simp only [Subtype.mk.injEq]
      symm
      exact Hl_eq_reverseinduced_induced_Hl φ Hl₀ h_ind₀
    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv]
      simp only [Subtype.mk.injEq]
      symm
      exact Hl_eq_reverseinduced_induced_Hl φ.symm Hl₁ h_ind₁
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedLabeledSubgraphListFromIsoGHl
    {G : LabeledGraph σ V} {G' : LabeledGraph σ W} (φ : G ≃f G')
    {Hl : LabeledGraphList σ t Vl} {Hl' : LabeledGraphList σ t Vl'} (ψ : ∀ (i : Fin t), Hl i ≃f Hl' i)
    : { Gl : LabeledSubgraphList σ t G | Gl.IsInduced ∧ predIsoLabeledHl G Hl Gl }
      ≃ { Gl : LabeledSubgraphList σ t G' | Gl.IsInduced ∧ predIsoLabeledHl G' Hl' Gl }
  :=
  isoSetOfInducedLabeledSubgraphList φ
    (predIsoLabeledHl G Hl)
    (predIsoLabeledHl G' Hl')
    (predIsoLabeledHl_related φ ψ)

omit [DecidableEq T] in
lemma labeledSubgraphListDensity_respect_eqv
    {Hl₀ : LabeledGraphList σ t Vl} {Hl₁ : LabeledGraphList σ t Vl'} (ψ : ∀ (i : Fin t), Hl₀ i ≃f Hl₁ i)
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    : labeledSubgraphListDensity Hl₀ G₀ = labeledSubgraphListDensity Hl₁ G₁
  := by
  dsimp [labeledSubgraphListDensity]
  let S₀ := { Gl : LabeledSubgraphList σ t G₀ | Gl.IsInduced ∧ predIsoLabeledHl G₀ Hl₀ Gl}
  let S₁ := { Gl : LabeledSubgraphList σ t G₁ | Gl.IsInduced ∧ predIsoLabeledHl G₁ Hl₁ Gl}
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedLabeledSubgraphListFromIsoGHl φ ψ
  have h_count : labeledSubgraphListCount Hl₀ G₀ = labeledSubgraphListCount Hl₁ G₁ := by
    dsimp only [labeledSubgraphListCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.toFinset_card]
  have h_G_size : G₀.size = G₁.size := labeledGraphIso_size_eq G₀ G₁ φ
  rw [h_count, h_G_size]
  have h_Hl_sizes : ∀ i : Fin t, (Hl₀ i).size = (Hl₁ i).size :=
    fun i ↦ labeledGraphIso_size_eq (Hl₀ i) (Hl₁ i) (ψ i)
  simp only [h_Hl_sizes]

noncomputable def labeledSubgraphListDensityLifted
    (Hl : LabeledGraphList σ t Vl) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G => labeledSubgraphListDensity Hl G)
  intro _ _ h_eqv
  exact labeledSubgraphListDensity_respect_eqv (fun _ ↦ LabeledGraphIso.refl) h_eqv.some

omit [DecidableEq T] in
lemma labeledSubgraphListDensityLifted_respect_eqv
    {Hl : LabeledGraphList σ t Vl} {Hl' : LabeledGraphList σ t Vl'}
    (ψ : ∀ (i : Fin t), Hl i ≃f Hl' i) (G : Flag σ W)
    : labeledSubgraphListDensityLifted Hl G = labeledSubgraphListDensityLifted Hl' G
  := by
  dsimp [labeledSubgraphListDensityLifted]
  congr
  ext Grep
  exact labeledSubgraphListDensity_respect_eqv ψ LabeledGraphIso.refl

noncomputable def quotLabeledSubgraphListDensity
    : QuotLabeledGraphList σ t Vl → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphListDensityLifted
  intro _ _ ψ
  ext G
  exact labeledSubgraphListDensityLifted_respect_eqv (fun i ↦ (ψ i).some) G

omit [DecidableEq T] in
lemma quotLabeledSubgraphListDensity_respect_eqv
    {Hl Hl' : LabeledGraphList σ t Vl} (h : Hl ∼fl Hl') (G : Flag σ W)
    : quotLabeledSubgraphListDensity ⟦Hl⟧ G = quotLabeledSubgraphListDensity ⟦Hl'⟧ G
  :=
  labeledSubgraphListDensityLifted_respect_eqv (fun i ↦ (h i).some) G

noncomputable def flagListDensity
    : FlagList σ t Vl → Flag σ W → ℚ
  :=
  fun Fl => quotLabeledSubgraphListDensity Fl.coe

omit [DecidableEq T] in
theorem flagListDensity_HEq_eq
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_HEq : HEq Fl Fl') (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity Fl' G
  := by
  subst h_Vl_eq
  have h_Fl_eq : Fl = Fl' := by rw [←heq_eq_eq Fl Fl']; exact h_HEq
  subst h_Fl_eq
  dsimp [flagListDensity, quotLabeledSubgraphListDensity, eqv_QuotLabeledGraphList_FlagList]
  dsimp [labeledSubgraphListDensityLifted, labeledSubgraphListDensity]
  congr!

omit [DecidableEq T] in
theorem subflagDensity_eq_flagListDensity
    {σ : FlagType T} (F : Flag σ U) (G : Flag σ W)
    : subflagDensity F G = flagListDensity (flagToList F) G
  := by
  rcases Quotient.exists_rep F with ⟨Frep, hFrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  have h_count : labeledSubgraphCount Frep Grep = labeledSubgraphListCount (fun (_ : Fin 1) => Frep) Grep := by
    dsimp [labeledSubgraphCount, labeledSubgraphListCount]
    apply Finset.card_bij
    · intro H hH
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hH
      show (fun (_ : Fin 1) => H) ∈ _
      simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
        ne_eq, forall_const, true_and,
        Set.coe_setOf, Set.toFinset_setOf, Set.inter_self,
        Finset.mem_filter, Finset.mem_univ]
      refine ⟨hH.1, hH.2, ?_⟩
      intro i j hij
      have : i = j := by
        rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      contradiction
    · intro H _ H' _ h_eq
      calc
        H = (fun (_ : Fin 1) => H) 0 := by simp only
        _ = (fun (_ : Fin 1) => H') 0 := by rw [h_eq]
        _ = H' := by simp only
    · intro Hl hHl
      use Hl 0
      simp_all only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
        ne_eq, true_and, and_self, exists_const,
        Set.coe_setOf, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ]
      ext1 i
      rw [Fin.fin_one_eq_zero i]
  calc
    subflagDensity F G = labeledSubgraphDensity Frep Grep := by
      subst hFrep hGrep
      rfl
    _ = labeledSubgraphListDensity (fun (_ : Fin 1) => Frep) Grep := by
      dsimp [labeledSubgraphDensity, labeledSubgraphListDensity]
      rw [← h_count]
      congr
      dsimp [multinomialCoefficient]
      rw [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Finset.prod_singleton]
      split <;> rename_i h
      · exact Nat.choose_eq_factorial_div_factorial h
      · exact Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)
    _ = quotLabeledSubgraphListDensity [F]ᶠ.coe G := by
      have : [F]ᶠ.coe = ⟦fun (_ : Fin 1) => Frep⟧ := by
        dsimp [eqv_QuotLabeledGraphList_FlagList]
        apply Quotient.sound
        intro i
        simp only [flagToList, ← hFrep]
        apply Quotient.mk_out Frep
      rw [this, ← hGrep]
      rfl
    _ = flagListDensity [F]ᶠ G := rfl

noncomputable def flagDensity₁ (F : Flag σ U) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F]ᶠ G

noncomputable def flagDensity₂ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂]ᶠ G

noncomputable def flagDensity₃ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (F₃ : Flag σ U₃) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂, F₃]ᶠ G

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagListDensity
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity Fl G = flagListDensity (QuotLabeledGraphList.coe ⟦Fl⟧) ⟦G⟧
  := by
  show quotLabeledSubgraphListDensity ⟦Fl⟧ ⟦G⟧ = flagListDensity (QuotLabeledGraphList.coe ⟦Fl⟧) ⟦G⟧
  dsimp [flagListDensity, eqv_QuotLabeledGraphList_FlagList]
  apply quotLabeledSubgraphListDensity_respect_eqv
  calc
    Fl ∼fl (fun i => ⟦Fl⟧.out i) := flagListEqv.symm (Quotient.mk_out Fl)
    _ ∼fl (fun i => ⟦⟦Fl⟧.out i⟧.out) := by
      dsimp [flagListEqv]
      intro i
      exact flagEqv.symm (Quotient.mk_out (⟦Fl⟧.out i))

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagDensity₁
    (F : LabeledGraph σ U) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity [F]ᵍ G = flagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  rw [labeledSubgraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_singleton]
  simp only [QuotLabeledGraphList.coe, FlagList.coe,
    Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, flagDensity₁]

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagDensity₂
    (F₁ : LabeledGraph σ U₁) (F₂ : LabeledGraph σ U₂) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity [F₁, F₂]ᵍ G = flagDensity₂ ⟦F₁⟧ ⟦F₂⟧ ⟦G⟧
  := by
  rw [labeledSubgraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_pair]
  simp only [QuotLabeledGraphList.coe, FlagList.coe,
    Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, flagDensity₂]

omit [DecidableEq T] in
theorem labeledSubgraphListDensity_eq_flagDensity₃
    (F₁ : LabeledGraph σ U₁) (F₂ : LabeledGraph σ U₂) (F₃ : LabeledGraph σ U₃) (G : LabeledGraph σ W)
    : labeledSubgraphListDensity [F₁, F₂, F₃]ᵍ G = flagDensity₃ ⟦F₁⟧ ⟦F₂⟧ ⟦F₃⟧ ⟦G⟧
  := by
  rw [labeledSubgraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_triple]
  simp only [QuotLabeledGraphList.coe, FlagList.coe,
    Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, flagDensity₃]

theorem flagDensity_empty
    (F : Flag σ W) : flagDensity₁ (emptyFlag σ) F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity (emptyFlag σ) F]
  exact subflagDensity_empty F

omit [DecidableEq T] in
theorem flagDensity_self
    (F : Flag σ W) : flagDensity₁ F F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F]
  exact subflagDensity_self F

omit [DecidableEq T] in
theorem flagDensity_other
    {F F' : Flag σ W} (h_neq : F ≠ F') : flagDensity₁ F F' = 0
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F']
  exact subflagDensity_other h_neq

lemma sum_perm_eq
    (f : Fin t → ℕ) (π : Perm t)
    : ∑ i : Fin t, f i = ∑ i : Fin t, f (π i)
  := by
  apply Finset.sum_bij
          (fun i _ => π.invFun i)
          (by simp only [Finset.mem_univ, Equiv.invFun_as_coe, imp_self, implies_true])
          (by simp only [Finset.mem_univ, Equiv.invFun_as_coe, imp_self, implies_true,
                         EmbeddingLike.apply_eq_iff_eq])
  · intro i _
    use π i
    simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply, Finset.mem_univ, exists_const]
  · intro i _
    have : i = π (π.invFun i) := (Equiv.symm_apply_eq π).mp rfl
    rw [←this]

lemma prod_perm_eq
    (f : Fin t → ℕ) (π : Perm t)
    : ∏ i : Fin t, f i = ∏ i : Fin t, f (π i)
  := by
  apply Finset.prod_bij
          (fun i _ => π.invFun i)
          (by simp only [Finset.mem_univ, Equiv.invFun_as_coe, imp_self, implies_true])
          (by simp only [Finset.mem_univ, Equiv.invFun_as_coe, imp_self, implies_true,
                         EmbeddingLike.apply_eq_iff_eq])
  · intro i _
    use π i
    simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply, Finset.mem_univ, exists_const]
  · intro i _
    have : i = π (π.invFun i) := (Equiv.symm_apply_eq π).mp rfl
    rw [←this]

noncomputable def setOfLabeledSubgraphListIsoHl_permute
    (G : LabeledGraph σ V) (Hl : LabeledGraphList σ t Vl) (π : Perm t)
    : setOfLabeledSubgraphListIsoHl G Hl ≃ setOfLabeledSubgraphListIsoHl G (fun i ↦ Hl (π i))
  :=
  let S₀ := setOfLabeledSubgraphListIsoHl G Hl
  let S₁ := setOfLabeledSubgraphListIsoHl G (fun i => Hl (π i))
  let f : S₀ → S₁ := by
    intro s₀
    dsimp [S₀, setOfLabeledSubgraphListIsoHl] at s₀
    let ⟨Hl₀, h_ind₀, h_p₀⟩ := s₀
    let Hl₁ : LabeledSubgraphList σ t G :=  fun i ↦ Hl₀ (π i)
    let h_ind₁ : Hl₁.IsInduced := fun i ↦ @h_ind₀ (π i)
    let h_p₁ : predIsoLabeledHl G (fun i ↦ Hl (π i)) Hl₁ := by
      simp_all only [predIsoLabeledHl, ne_eq, implies_true, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, and_self, Hl₁]
    exact ⟨Hl₁, h_ind₁, h_p₁⟩
  have h_inj_f : Function.Injective f := by
    intro ⟨Hl₀, h_ind₀, h_p₀⟩ ⟨Hl₁, h_ind₁, h_p₁⟩ h_eq
    simp only [f, Subtype.mk.injEq] at h_eq
    simp only [Subtype.mk.injEq]
    funext i
    have : Hl₀ (π (π.invFun i)) = Hl₁ (π (π.invFun i)) := congrFun h_eq (π.invFun i)
    rwa [Equiv.invFun_as_coe, Equiv.apply_symm_apply] at this
  have h_surj_f : Function.Surjective f := by
    intro ⟨Hl₁, h_ind₁, h_p₁⟩
    let Hl₀ : LabeledSubgraphList σ t G := fun i ↦ Hl₁ (π.invFun i)
    let h_ind₀ : Hl₀.IsInduced := fun i ↦ @h_ind₁ (π.invFun i)
    let h_p₀ : predIsoLabeledHl G Hl Hl₀ := by
      constructor
      · intro i
        dsimp [Hl₀]
        have : Nonempty ((Hl₀ i).coe ≃f (Hl i)) := by
          have h_eq : π (π.invFun i) = i := by apply Equiv.apply_symm_apply
          have : Nonempty ((Hl₁ (π.invFun i)).coe ≃f (Hl (π (π.invFun i)))) := h_p₁.1 (π.invFun i)
          rw [h_eq] at this
          exact this
        exact this
      · intro i j h_ij
        simp_all only [predIsoLabeledHl, ne_eq, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, Hl₀]
    use ⟨Hl₀, h_ind₀, h_p₀⟩
    simp_all only [f, Equiv.invFun_as_coe, Equiv.symm_apply_apply, Hl₀]
  Equiv.ofBijective f ⟨h_inj_f, h_surj_f⟩

omit [DecidableEq T] in
theorem flagDensity_permute
    (Fl : FlagList σ t Vl) (G : Flag σ W) (π : Perm t)
    : flagListDensity Fl G = flagListDensity (Fl.permute π) G
  := by
  dsimp [flagListDensity, quotLabeledSubgraphListDensity]
  congr; ext Grep
  let S₀ := setOfLabeledSubgraphListIsoHl Grep (fun i => Quotient.out (Fl i))
  let S₁ := setOfLabeledSubgraphListIsoHl Grep (fun i => Quotient.out (Fl (π i)))
  let f_iso_S₀_S₁ : S₀ ≃ S₁ := setOfLabeledSubgraphListIsoHl_permute Grep (fun i => Quotient.out (Fl i)) π
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  have h_count : labeledSubgraphListCount (fun i => Quotient.out (Fl.permute π i)) Grep
                 = labeledSubgraphListCount (fun i => Quotient.out (Fl i)) Grep
    := by
    dsimp only [labeledSubgraphListCount]
    show S₁.toFinset.card = S₀.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr f_iso_S₀_S₁
    simp_all only [Set.toFinset_card]
  have h_coeff : multinomialCoefficient (fun i ↦ (Quotient.out (Fl i)).size - σ.size) (Grep.size - σ.size)
                 = multinomialCoefficient (fun i ↦ (Quotient.out (Fl.permute π i)).size - σ.size) (Grep.size - σ.size)
    := by
    dsimp [multinomialCoefficient]; simp only [ge_iff_le]
    have sum_sizes_perm_eq : ∑ i : Fin t, ((Quotient.out (Fl i)).size - σ.size)
                             = ∑ i : Fin t, ((Quotient.out (Fl.permute π i)).size - σ.size)
      := by
      dsimp [FlagList.permute]
      let g : Fin t → ℕ := fun i ↦ ((Quotient.out (Fl i)).size - σ.size)
      exact sum_perm_eq g π
    have prod_factorials_perm_eq : ∏ i : Fin t, ((Quotient.out (Fl i)).size - σ.size).factorial
                                   = ∏ i : Fin t, ((Quotient.out (Fl.permute π i)).size - σ.size).factorial
      := by
      dsimp [FlagList.permute]
      let g : Fin t → ℕ := fun i ↦ ((Quotient.out (Fl i)).size - σ.size).factorial
      exact prod_perm_eq g π
    rw [sum_sizes_perm_eq, prod_factorials_perm_eq]
  dsimp [labeledSubgraphListDensity]
  rw [h_count, h_coeff]

instance {V W : Type} [Fintype V] [Fintype W]
    : FintypeList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance {V W : Type} [DecidableEq V] [DecidableEq W]
    : DecidableEqList (fun (i : Fin 2) => match i with | 0 => V | 1 => W)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance }

instance {V W U : Type} [Fintype V] [Fintype W] [Fintype U]
    : FintypeList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { fintype_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

instance {V W U : Type} [DecidableEq V] [DecidableEq W] [DecidableEq U]
    : DecidableEqList (fun (i : Fin 3) => match i with | 0 => V | 1 => W | 2 => U)
  :=
  { decidable_eq_all := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance }

omit [DecidableEq T] in
theorem flagPairDensity_comm
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₂ F₁ F₂ G = flagDensity₂ F₂ F₁ G
  := by
  let Fl₁ := [F₁, F₂]ᶠ
  let Fl₂ := [F₂, F₁]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  let π : Perm 2 := by
    let f : Fin 2 → Fin 2 := fun i => match i with | 0 => 1 | 1 => 0
    refine ⟨f, f, ?_, ?_⟩
    · intro i; match i with | 0 => rfl | 1 => rfl
    · intro i; match i with | 0 => rfl | 1 => rfl
  rw [flagDensity_permute Fl₁ G π]
  have h_Vl_eq : (fun (i : Fin 2) => match i with | 0 => U₂ | 1 => U₁)
      = (listTypePermute (fun (i : Fin 2) => match i with | 0 => U₁ | 1 => U₂) π) := by
    ext i; split <;> rfl
  have h_Fl_eq : ∀ (i : Fin 2), (Fl₁.permute π) i = cast (Flag.type_eq h_Vl_eq i) (Fl₂ i) := by
    intro i
    dsimp [Fl₁, Fl₂, flagPairToList]
    split <;> (simp_all only [cast_eq, π]; rfl)
  refine flagListDensity_HEq_eq h_Vl_eq ?_ G
  exact flagList_HEq h_Vl_eq h_Fl_eq

omit [DecidableEq T] in
theorem flagTripleDensity_comm
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (F₃ : Flag σ U₃) (G : Flag σ W)
    : flagDensity₃ F₁ F₂ F₃ G = flagDensity₃ F₂ F₃ F₁ G
  := by
  let Fl₁ := [F₁, F₂, F₃]ᶠ
  let Fl₂ := [F₂, F₃, F₁]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  let π : Perm 3 := by
    let f : Fin 3 → Fin 3 := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0
    let f_inv : Fin 3 → Fin 3 := fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1
    refine ⟨f, f_inv, ?_, ?_⟩
    · intro i; match i with | 0 => rfl | 1 => rfl | 2 => rfl
    · intro i; match i with | 0 => rfl | 1 => rfl | 2 => rfl
  rw [flagDensity_permute Fl₁ G π]
  have h_Vl_eq : (fun (i : Fin 3) => match i with | 0 => U₂ | 1 => U₃ | 2 => U₁)
      = (listTypePermute (fun (i : Fin 3) => match i with | 0 => U₁ | 1 => U₂ | 2 => U₃) π) := by
    ext i; split <;> rfl
  have h_Fl_eq : ∀ (i : Fin 3), (Fl₁.permute π) i = cast (Flag.type_eq h_Vl_eq i) (Fl₂ i) := by
    intro i
    dsimp [Fl₁, Fl₂, flagTripleToList]
    split <;> (simp_all only [cast_eq, π]; rfl)
  refine flagListDensity_HEq_eq h_Vl_eq ?_ G
  exact flagList_HEq h_Vl_eq h_Fl_eq


noncomputable def setOfLabeledSubgraphListIsoHl_insert_empty
    (G : LabeledGraph σ V) (Fl : FlagList σ t Vl)
    : setOfLabeledSubgraphListIsoHl G (fun i ↦ Quotient.out (Fl i))
      ≃ setOfLabeledSubgraphListIsoHl G (fun i ↦ Quotient.out (Fl.insert (emptyFlag σ) i))
  :=
  let S₀ := setOfLabeledSubgraphListIsoHl G (fun i => Quotient.out (Fl i))
  let S₁ := setOfLabeledSubgraphListIsoHl G (fun i => Quotient.out (Fl.insert (emptyFlag σ) i))
  let f : S₀ → S₁ := by
    intro ⟨Hl₀, h_ind₀, h_p₀⟩
    let Hl₁ : LabeledSubgraphList σ (t+1) G :=
      fun i ↦ if h : i.val < t then Hl₀ ⟨i.val, h⟩ else G.bottom
    let h_ind₁ : Hl₁.IsInduced := by
      intro i
      dsimp [Hl₁]
      split
      next hi =>
        exact h_ind₀ ⟨i, hi⟩
      next _ =>
        exact G.bottom_isInduced
    let h_p₁ : predIsoLabeledHl G (fun i ↦ Quotient.out (Fl.insert (emptyFlag σ) i)) Hl₁ := by
      constructor
      · intro i
        apply Nonempty.intro; symm
        dsimp [FlagList.insert]
        split
        next hi =>
          dsimp [Hl₁]
          have empty_equiv : Nonempty (G.bottom.coe ≃f emptyLabeledGraph σ) := labeledSubgraph_eq_bot_iff_iso_emptyLabeledGraph.mp rfl
          have empty_iso := Classical.choice empty_equiv
          have h_Hl₁ : (if h : ↑i < t then Hl₀ ⟨↑i, h⟩ else G.bottom) = G.bottom := by
            simp_all only [lt_self_iff_false, ↓reduceDIte]
          rw [h_Hl₁]
          have insert_iso := (Classical.choice (insert_new_flag_cast_iso Fl (emptyFlag σ) hi)).symm
          have quotient_iso : Quotient.out (emptyFlag σ) ≃f emptyLabeledGraph σ := Classical.choice (Quotient.mk_out (emptyLabeledGraph σ))
          exact (insert_iso.trans quotient_iso).trans empty_iso.symm
        next hi =>
          have hi_lt : i.val < t := by omega
          let i' : Fin t := ⟨i.val, hi_lt⟩
          dsimp [Hl₁]
          have h_Hl₁ :  (if h : ↑i < t then Hl₀ ⟨↑i, h⟩ else G.bottom) = Hl₀ ⟨↑i, hi_lt⟩ := by
            simp only [hi_lt, ↓reduceDIte]
          rw [h_Hl₁]
          have iso_from_existing := Classical.choice (h_p₀.1 i')
          dsimp [i'] at iso_from_existing
          have preserv_iso := Classical.choice (insert_preserves_existing_flags Fl (emptyFlag σ) hi)
          exact (iso_from_existing.trans preserv_iso).symm
      · intro i j h_ij
        dsimp [Hl₁]
        have h_bottom_verts : G.bottom.subgraph.verts \ G.type_verts = ∅ := Set.diff_eq_empty.mpr fun ⦃a⦄ a ↦ a
        split <;> split
        next h1 h2 =>
          let i' : Fin t := ⟨i, h1⟩
          let j' : Fin t := ⟨j, h2⟩
          have h_ij' : i' ≠ j' := by
            rwa [ne_eq, Fin.mk.injEq, ← ne_eq, ← Fin.ne_iff_vne]
          exact h_p₀.2 i' j' h_ij'
        next _ _ =>
          simp only [h_bottom_verts, Set.inter_empty]
        next _ _ =>
          simp only [h_bottom_verts, Set.empty_inter]
        next _ _ =>
          simp only [h_bottom_verts, Set.inter_self]
    exact ⟨Hl₁, h_ind₁, h_p₁⟩
  let f_inv : S₁ → S₀ := by
    intro ⟨Hl₁, h_ind₁, h_p₁⟩
    let Hl₀ : LabeledSubgraphList σ t G := fun i ↦ Hl₁ i.castSucc
    let h_ind₀ : Hl₀.IsInduced := fun i ↦ h_ind₁ i.castSucc
    let h_p₀ : predIsoLabeledHl G (fun i ↦ Quotient.out (Fl i)) Hl₀ := by
      constructor
      · intro i
        apply Nonempty.intro
        have hi : i.val ≠ t := i.isLt.ne
        dsimp [Hl₀]
        let h_iso := Classical.choice (h_p₁.1 i.castSucc)
        have h_iso' := (Classical.choice (insert_preserves_existing_flags_coe Fl (emptyFlag σ) hi)).symm
        exact h_iso.trans h_iso'
      · intro i j h_ij
        refine h_p₁.2 i.castSucc j.castSucc ?h_ij'
        simp only [ne_eq, Fin.castSucc_inj, h_ij, not_false_eq_true]
    exact ⟨Hl₀, h_ind₀, h_p₀⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      intro ⟨Hl₀, h_ind₀, h_p₀⟩
      dsimp [f, f_inv]
      simp only [Subtype.mk.injEq]
      funext i
      simp only [Fin.is_lt]
      rfl
    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv]
      simp only [Subtype.mk.injEq]
      funext i
      split
      next _ =>
        simp only
      next hi =>
        have hi : ↑i = t := Nat.eq_of_lt_succ_of_not_lt i.isLt hi
        have iso_exist := Classical.choice (h_p₁.1 i)
        dsimp [FlagList.insert] at iso_exist
        have h_Fl : (if hi : ↑i = t then cast (flag_listTypeInsert_eq hi) (emptyFlag σ) else cast (flag_listTypeInsert_eq' hi) (Fl (i.coe hi))) = cast (flag_listTypeInsert_eq hi) (emptyFlag σ) := by
          simp_all only [↓reduceDIte]
        rw [h_Fl] at iso_exist
        have Hl₁_iso : Quotient.out (emptyFlag σ) ≃f (Hl₁ i).coe := (iso_exist.trans (Classical.choice (insert_new_flag_cast_iso Fl (emptyFlag σ) hi)).symm).symm
        have quotient_iso : Quotient.out (emptyFlag σ) ≃f emptyLabeledGraph σ := Classical.choice (Quotient.mk_out (emptyLabeledGraph σ))
        have h_iso := Hl₁_iso.symm.trans quotient_iso
        symm; apply (@labeledSubgraph_eq_bot_iff_iso_emptyLabeledGraph T σ V G (Hl₁ i)).mpr (Nonempty.intro h_iso)
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij


lemma sum_eq_sum_plus_last
    (f : Fin (t + 1) → ℕ) : ∑ i : Fin (t + 1), f i = (∑ i : Fin t, f i.castSucc) + (f (Fin.last t))
  :=
  Fin.sum_univ_castSucc f

lemma prod_eq_prod_mul_last
    (f : Fin (t + 1) → ℕ) : ∏ i : Fin (t + 1), f i = (∏ i : Fin t, f i.castSucc) * (f (Fin.last t))
  :=
  Fin.prod_univ_castSucc f

theorem flagDensity_insert_empty
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity (Fl.insert (emptyFlag σ)) G
  := by
  dsimp [flagListDensity, quotLabeledSubgraphListDensity]
  congr; ext Grep
  dsimp [labeledSubgraphListDensity, labeledSubgraphListCount]
  let S₀ := setOfLabeledSubgraphListIsoHl Grep (fun i => Quotient.out (Fl i))
  let S₁ := setOfLabeledSubgraphListIsoHl Grep (fun i => Quotient.out (Fl.insert (emptyFlag σ) i))
  let h_S₀ : Fintype S₀ := Fintype.ofFinite S₀
  let h_S₁ : Fintype S₁ := Fintype.ofFinite S₁
  let Z₀ := multinomialCoefficient (fun i ↦ (Fl i).out.size - σ.size) (Grep.size - σ.size)
  let Z₁ := multinomialCoefficient (fun i ↦ (Fl.insert (emptyFlag σ) i).out.size - σ.size) (Grep.size - σ.size)
  show (S₀.toFinset.card : ℚ) / Z₀ = (S₁.toFinset.card : ℚ) / Z₁
  let h_count : S₁.toFinset.card = S₀.toFinset.card := by
    let f_iso_S₀_S₁ : S₀ ≃ S₁ := setOfLabeledSubgraphListIsoHl_insert_empty Grep Fl
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr f_iso_S₀_S₁
    simp_all only [Set.toFinset_card]
  have h_eq : σ.size = (Fl.insert (emptyFlag σ) (Fin.last t)).out.size := by
    simp only [FlagType.size, LabeledGraph.size]
    have : T = listTypeInsert Vl T (Fin.last t) := listTypeInsert_eq (Fin.val_last t)
    simp only [← this]
  have h_eq' : ∀ i : Fin t, (Fl i).out.size = (Fl.insert (emptyFlag σ) i.castSucc).out.size := by
    intro i
    dsimp [LabeledGraph.size]
    let i' := i.castSucc
    have hi' : i'.val ≠ t := Nat.ne_of_lt i.isLt
    have : Vl (i'.coe hi') = listTypeInsert Vl T i' := listTypeInsert_eq' hi'
    congr!
  have h_coeff : Z₀ = Z₁ := by
    simp only [Z₀, Z₁, multinomialCoefficient, ge_iff_le]
    have sum_sizes_perm_eq : ∑ i : Fin t, ((Fl i).out.size - σ.size)
                             = ∑ i : Fin (t + 1), ((Fl.insert (emptyFlag σ) i).out.size - σ.size)
      := by
      symm
      calc
        ∑ i : Fin (t + 1), ((Fl.insert (emptyFlag σ) i).out.size - σ.size)
        _ = (∑ i : Fin t, ((Fl.insert (emptyFlag σ) i.castSucc).out.size - σ.size))
            + ((Fl.insert (emptyFlag σ) (Fin.last t)).out.size - σ.size)
              := by
              rw [sum_eq_sum_plus_last]
        _ = ∑ i : Fin t, ((Fl.insert (emptyFlag σ) i.castSucc).out.size - σ.size)
              := by
              rw [← h_eq]
              simp only [le_refl, tsub_eq_zero_of_le, add_zero]
        _ = ∑ i : Fin t, ((Fl i).out.size - σ.size)
              := by
              congr
              ext i
              rw [h_eq' i]
    have prod_factorials_perm_eq : ∏ i : Fin t, ((Fl i).out.size - σ.size).factorial
                                   = ∏ i : Fin (t + 1), ((Fl.insert (emptyFlag σ) i).out.size - σ.size).factorial
      := by
      symm
      calc
        ∏ i : Fin (t + 1), ((Fl.insert (emptyFlag σ) i).out.size - σ.size).factorial
        _ = (∏ i : Fin t, ((Fl.insert (emptyFlag σ) i.castSucc).out.size - σ.size).factorial)
            * ((Fl.insert (emptyFlag σ) (Fin.last t)).out.size - σ.size).factorial
              := by
              rw [prod_eq_prod_mul_last]
        _ = ∏ i : Fin t, ((Fl.insert (emptyFlag σ) i.castSucc).out.size - σ.size).factorial
              := by
              rw [← h_eq]
              simp only [le_refl, tsub_eq_zero_of_le, Nat.factorial_zero, mul_one]
        _ = ∏ i : Fin t, ((Fl i).out.size - σ.size).factorial
              := by
              congr
              ext i
              rw [h_eq' i]
    rw [sum_sizes_perm_eq, prod_factorials_perm_eq]
  rw [h_count, h_coeff]

theorem flagPairDensity_empty
    (F : Flag σ U) (G : Flag σ W)
    : flagDensity₂ (emptyFlag σ) F G = flagDensity₁ F G
  := by
  rw [flagPairDensity_comm]
  let Fl₁ := [F, emptyFlag σ]ᶠ
  let Fl₂ := [F]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  have h_insert : flagListDensity (Fl₂.insert (emptyFlag σ)) G = flagListDensity Fl₁ G := by
    have h_Vl_eq : (fun (i : Fin 2) => match i with | 0 => U | 1 => T) = (listTypeInsert (fun _ => U) T)
      := by
      ext i; split <;> rfl
    have h_Fl_eq : ∀ (i : Fin 2), (Fl₂.insert (emptyFlag σ)) i = cast (Flag.type_eq h_Vl_eq i) (Fl₁ i)
      := by
      intro i
      dsimp [Fl₁, Fl₂, flagPairToList]
      split <;> (simp_all only [cast_eq]; rfl)
    refine flagListDensity_HEq_eq h_Vl_eq ?_ G
    exact flagList_HEq h_Vl_eq h_Fl_eq
  rw [← h_insert]
  exact (flagDensity_insert_empty Fl₂ G).symm

theorem flagPairDensity_empty'
    (F : Flag σ U) (G : Flag σ W)
    : flagDensity₂ F (emptyFlag σ) G = flagDensity₁ F G
  := by
  rw [flagPairDensity_comm]
  exact flagPairDensity_empty F G

theorem flagTripleDensity_empty
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₃ (emptyFlag σ) F₁ F₂ G = flagDensity₂ F₁ F₂ G
  := by
  rw [flagTripleDensity_comm]
  let Fl₁ := [F₁, F₂, emptyFlag σ]ᶠ
  let Fl₂ := [F₁, F₂]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  have h_insert : flagListDensity (Fl₂.insert (emptyFlag σ)) G = flagListDensity Fl₁ G := by
    have h_Vl_eq : (fun (i : Fin 3) => match i with | 0 => U₁ | 1 => U₂ | 2 => T)
        = (listTypeInsert (fun (i : Fin 2) => match i with | 0 => U₁ | 1 => U₂) T)
      := by
      ext i; split <;> rfl
    have h_Fl_eq : ∀ (i : Fin 3), (Fl₂.insert (emptyFlag σ)) i = cast (Flag.type_eq h_Vl_eq i) (Fl₁ i)
      := by
      intro i
      dsimp [Fl₁, Fl₂, flagTripleToList]
      split <;> (simp_all only [cast_eq]; rfl)
    refine flagListDensity_HEq_eq h_Vl_eq ?_ G
    exact flagList_HEq h_Vl_eq h_Fl_eq
  rw [← h_insert]
  exact (flagDensity_insert_empty Fl₂ G).symm

theorem flagTripleDensity_empty'
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₃ F₁ F₂ (emptyFlag σ) G = flagDensity₂ F₁ F₂ G
  := by
  rw [← flagTripleDensity_comm]
  exact flagTripleDensity_empty F₁ F₂ G

/- Chain rules -/

variable {ℓ₀ : ℕ} {σ : FlagType (Fin ℓ₀)}

lemma labeledGraphTripleCount_eq_sum_density_prods'
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : (Nat.choose (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃) (ℓ' + ℓ₀ - ℓ₁ - ℓ₂))
        * labeledSubgraphListCount [H₁, H₂, H₃]ᵍ G
      = ∑ G' : Flag σ (Fin ℓ'),
          labeledSubgraphListCount [H₁, H₂]ᵍ G'.out * labeledSubgraphListCount [G'.out, H₃]ᵍ G
  := by
  let ℓ_other := (ℓ - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀) - (ℓ₃ - ℓ₀)
  let ℓ'_other := (ℓ' - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀)
  have hℓ_other : ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃ = ℓ_other := by omega
  have hℓ'_other : ℓ' + ℓ₀ - ℓ₁ - ℓ₂ = ℓ'_other := by omega
  rw [hℓ_other, hℓ'_other]
  let S_LHS := (Finset.univ : Finset (Fin ℓ_other)).powersetCard ℓ'_other
                × (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset
  let S_RHS := (G' : Flag σ (Fin ℓ'))
               × (setOfLabeledSubgraphListIsoHl G'.out [H₁, H₂]ᵍ).toFinset
               × (setOfLabeledSubgraphListIsoHl G [G'.out, H₃]ᵍ).toFinset
  let h_iso : S_LHS ≃ S_RHS := sorry
  calc
    (Nat.choose ℓ_other ℓ'_other) * (labeledSubgraphListCount [H₁, H₂, H₃]ᵍ G)
    _ = (Nat.choose ℓ_other ℓ'_other) * (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset.card := by
            dsimp [labeledSubgraphListCount]
            congr!
    _ = ((Finset.univ : Finset (Fin ℓ_other)).powersetCard ℓ'_other).card
        * (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset.card := by
            simp only [Set.toFinset_card, Fintype.card_ofFinset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ = (Fintype.card S_LHS) := by sorry
    _ = (Fintype.card S_RHS) :=
            Fintype.card_congr h_iso
    _ = ∑ G' : Flag σ (Fin ℓ'),
          labeledSubgraphListCount [H₁, H₂]ᵍ G'.out * labeledSubgraphListCount [G'.out, H₃]ᵍ G := by sorry

set_option maxHeartbeats 400000 in
lemma labeledGraphTripleCount_eq_sum_density_prods
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    :     multinomialCoefficient
            (fun i : Fin 2 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀)
            (ℓ' - ℓ₀)
        * multinomialCoefficient
            (fun i : Fin 2 ↦ match i with | 0 => ℓ' - ℓ₀ | 1 => ℓ₃ - ℓ₀)
            (ℓ - ℓ₀)
        * labeledSubgraphListCount [H₁, H₂, H₃]ᵍ G
      =
          multinomialCoefficient
            (fun i : Fin 3 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀ | 2 => ℓ₃ - ℓ₀)
            (ℓ - ℓ₀)
        * ∑ G' : Flag σ (Fin ℓ'),
            labeledSubgraphListCount [H₁, H₂]ᵍ G'.out * labeledSubgraphListCount [G'.out, H₃]ᵍ G
  := by
  rw [← labeledGraphTripleCount_eq_sum_density_prods' ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ]
  have : multinomialCoefficient
           (fun i : Fin 2 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀)
           (ℓ' - ℓ₀)
         * multinomialCoefficient
             (fun i : Fin 2 ↦ match i with | 0 => ℓ' - ℓ₀ | 1 => ℓ₃ - ℓ₀)
             (ℓ - ℓ₀)
         = multinomialCoefficient
             (fun i : Fin 3 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀ | 2 => ℓ₃ - ℓ₀)
             (ℓ - ℓ₀)
           * (Nat.choose (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃) (ℓ' + ℓ₀ - ℓ₁ - ℓ₂))
    := by
    dsimp [multinomialCoefficient]
    have h_leq_choose :  (ℓ' + ℓ₀ - ℓ₁ - ℓ₂) ≤ (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃) := by omega
    rw [Nat.choose_eq_factorial_div_factorial h_leq_choose]
    simp only [ge_iff_le, mul_ite, ite_mul, zero_mul, mul_zero,
               Fin.sum_univ_two, Fin.sum_univ_three,
               Fin.prod_univ_two, Fin.prod_univ_three]
    repeat (split <;> try omega)
    have h_rw₀ : ℓ' - ℓ₀ - (ℓ₁ - ℓ₀ + (ℓ₂ - ℓ₀)) = ℓ' + ℓ₀ - ℓ₁ - ℓ₂ := by omega
    have h_rw₁ : ℓ - ℓ₀ - (ℓ' - ℓ₀ + (ℓ₃ - ℓ₀)) = ℓ - ℓ' + ℓ₀ - ℓ₃ := by omega
    have h_rw₂ : ℓ - ℓ₀ - (ℓ₁ - ℓ₀ + (ℓ₂ - ℓ₀) + (ℓ₃ - ℓ₀)) = ℓ + 2*ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃ := by omega
    have h_rw₃ : ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃ - (ℓ' + ℓ₀ - ℓ₁ - ℓ₂) = ℓ - ℓ' + ℓ₀ - ℓ₃ := by omega
    rw [h_rw₀, h_rw₁, h_rw₂, h_rw₃]
    have h_dvd₀ : ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial) ∣ (ℓ' - ℓ₀).factorial :=
      have h₀ : (ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial ∣ (ℓ₁ + ℓ₂ - 2 * ℓ₀).factorial := by
        have : ℓ₂ - ℓ₀ = (ℓ₁ + ℓ₂ - 2 * ℓ₀) - (ℓ₁ - ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      have h₁ : (ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial
                ∣ (ℓ₁ + ℓ₂ - 2 * ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial :=
        Nat.mul_dvd_mul h₀ (by simp)
      have h₂ : (ℓ₁ + ℓ₂ - 2 * ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial ∣ (ℓ' - ℓ₀).factorial := by
        have : ℓ' + ℓ₀ - ℓ₁ - ℓ₂  = (ℓ' - ℓ₀) - (ℓ₁ + ℓ₂ - 2 * ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      Nat.dvd_trans h₁ h₂
    have h_dvd₁ : ((ℓ' - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial) ∣ (ℓ - ℓ₀).factorial :=
      have h₀ : (ℓ' - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial ∣ (ℓ' + ℓ₃ - 2 * ℓ₀).factorial := by
        have : ℓ₃ - ℓ₀ = (ℓ' + ℓ₃ - 2 * ℓ₀) - (ℓ' - ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      have h₁ : (ℓ' - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial
                ∣ (ℓ' + ℓ₃ - 2 * ℓ₀).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial :=
        Nat.mul_dvd_mul h₀ (by simp)
      have h₂ : (ℓ' + ℓ₃ - 2 * ℓ₀).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial ∣ (ℓ - ℓ₀).factorial := by
        have : ℓ - ℓ' + ℓ₀ - ℓ₃  = (ℓ - ℓ₀) - (ℓ' + ℓ₃ - 2 * ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      Nat.dvd_trans h₁ h₂
    have h_dvd₂ : ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial) ∣ (ℓ - ℓ₀).factorial :=
      have h₀ : (ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial ∣ (ℓ₁ - ℓ₀ + ℓ₂ - ℓ₀).factorial := by
        have : ℓ₂ - ℓ₀ = (ℓ₁ - ℓ₀ + ℓ₂ - ℓ₀) - (ℓ₁ - ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      have h₁ : (ℓ₃ - ℓ₀).factorial * (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial ∣ (ℓ + ℓ₀ - ℓ₁ - ℓ₂).factorial := by
        have : ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃ = (ℓ + ℓ₀ - ℓ₁ - ℓ₂) - (ℓ₃ - ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      have h₃ : (ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial  * (ℓ₃ - ℓ₀).factorial * (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial
                ∣ (ℓ₁ - ℓ₀ + ℓ₂ - ℓ₀).factorial * (ℓ + ℓ₀ - ℓ₁ - ℓ₂).factorial := by
        have := mul_assoc ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial) (ℓ₃ - ℓ₀).factorial (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial
        rw [this]
        exact Nat.mul_dvd_mul h₀ h₁
      have h₄ : (ℓ₁ - ℓ₀ + ℓ₂ - ℓ₀).factorial * (ℓ + ℓ₀ - ℓ₁ - ℓ₂).factorial ∣ (ℓ - ℓ₀).factorial := by
        have : ℓ + ℓ₀ - ℓ₁ - ℓ₂ = ℓ - ℓ₀ - (ℓ₁ - ℓ₀ + ℓ₂ - ℓ₀) := by omega
        rw [this]
        exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
      Nat.dvd_trans h₃ h₄
    have h_dvd₃ : ((ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial) ∣ (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial := by
      rw [←h_rw₃]
      exact Nat.factorial_mul_factorial_dvd_factorial (by omega)
    calc
      (ℓ' - ℓ₀).factorial / ((ℓ₁ - ℓ₀).factorial *
                             (ℓ₂ - ℓ₀).factorial *
                             (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial)
      * ((ℓ - ℓ₀).factorial / ((ℓ' - ℓ₀).factorial *
                               (ℓ₃ - ℓ₀).factorial *
                               (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial))
      _ = ((ℓ' - ℓ₀).factorial * (ℓ - ℓ₀).factorial)
          / (((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial) *
             ((ℓ' - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) := by
                  rw [Nat.div_mul_div_comm h_dvd₀ h_dvd₁]
      _ = ((ℓ' - ℓ₀).factorial * (ℓ - ℓ₀).factorial)
          / ((ℓ' - ℓ₀).factorial *
             ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) := by
                  ring_nf
      _ = (ℓ - ℓ₀).factorial
          / ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial) := by
                  rw [Nat.mul_div_mul_left _ _ (Nat.factorial_pos (ℓ' - ℓ₀))]
      _ = ((ℓ + 2*ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial * (ℓ - ℓ₀).factorial)
          / ((ℓ + 2*ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial *
             ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) := by
                  rw [Nat.mul_div_mul_left _ _ (Nat.factorial_pos (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃))]
      _ =  ((ℓ - ℓ₀).factorial * (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial)
          / (((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial) *
             ((ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) := by
                  ring_nf
      _ =  (ℓ - ℓ₀).factorial / ((ℓ₁ - ℓ₀).factorial *
                                 (ℓ₂ - ℓ₀).factorial *
                                 (ℓ₃ - ℓ₀).factorial *
                                 (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial)
           * ((ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).factorial / ((ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial *
                                                       (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) := by
                  rw [Nat.div_mul_div_comm h_dvd₂ h_dvd₃]
  rw [this]
  ring


lemma fintype_card_match_comm_two
    (ℓ₀ ℓ₁ ℓ₂ : ℕ)
    : (fun i : Fin 2 ↦ @Fintype.card
                         (match i with | 0 => Fin ℓ₁ | 1 => Fin ℓ₂)
                         (@fintype_V 2
                            (fun i : Fin 2 ↦ match i with | 0 => Fin ℓ₁ | 1 => Fin ℓ₂)
                            (@fintypePairList (Fin ℓ₁) (Fin ℓ₂) (Fin.fintype ℓ₁) (Fin.fintype ℓ₂))
                            i)
                        - ℓ₀)
      =
      (fun i : Fin 2 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀)
  := by
  funext i
  split <;> simp only [Fin.isValue, Fintype.card_fin]

lemma fintype_card_match_comm_three
    (ℓ₀ ℓ₁ ℓ₂ ℓ₃ : ℕ)
    : (fun i : Fin 3 ↦ @Fintype.card
                         (match i with | 0 => Fin ℓ₁ | 1 => Fin ℓ₂ | 2 => Fin ℓ₃)
                         (fintype_V (fun i : Fin 3 ↦ match i with | 0 => (Fin ℓ₁) | 1 => (Fin ℓ₂) | 2 => (Fin ℓ₃)) i)
                        - ℓ₀)
      =
      (fun i : Fin 3 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀ | 2 => ℓ₃ - ℓ₀)
  := by
  funext i
  split <;> simp only [Fin.isValue, Fintype.card_fin]

-- set_option pp.all true in
lemma labeledGraphTripleDensity_eq_sum_density_prods
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : labeledSubgraphListDensity [H₁, H₂, H₃]ᵍ G
      =
      ∑ G' : Flag σ (Fin ℓ'), labeledSubgraphListDensity [H₁, H₂]ᵍ G'.out
                              * labeledSubgraphListDensity [G'.out, H₃]ᵍ G
  := by
  let C_lhs  := multinomialCoefficient
                  (fun i : Fin 3 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀ | 2 => ℓ₃ - ℓ₀)
                  (ℓ - ℓ₀)
  have h_C_lhs_pos : C_lhs > 0 := multinomialCoefficient_pos
                                    (fun i : Fin 3 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀ | 2 => ℓ₃ - ℓ₀)
                                    (ℓ - ℓ₀)
                                    (by simp only [Fin.sum_univ_three]; omega)
  let C_rhs₀ := multinomialCoefficient
                  (fun i : Fin 2 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀)
                  (ℓ' - ℓ₀)
  have h_C_rhs₀_pos : C_rhs₀ > 0 := multinomialCoefficient_pos
                                      (fun i : Fin 2 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀)
                                      (ℓ' - ℓ₀)
                                      (by simp only [Fin.sum_univ_two]; omega)
  let C_rhs₁ := multinomialCoefficient
                  (fun i : Fin 2 ↦ match i with | 0 => ℓ' - ℓ₀ | 1 => ℓ₃ - ℓ₀)
                  (ℓ - ℓ₀)
  have h_C_rhs₁_pos : C_rhs₁ > 0 := multinomialCoefficient_pos
                                      (fun i : Fin 2 ↦ match i with | 0 => ℓ' - ℓ₀ | 1 => ℓ₃ - ℓ₀)
                                      (ℓ - ℓ₀)
                                      (by simp only [Fin.sum_univ_two]; omega)
  let C := C_lhs * C_rhs₀ * C_rhs₁
  have h_C_pos : C > 0 := by
    dsimp [C]
    simp only [gt_iff_lt, mul_pos_iff_of_pos_left, h_C_lhs_pos, h_C_rhs₀_pos, h_C_rhs₁_pos]
  suffices C * labeledSubgraphListDensity [H₁, H₂, H₃]ᵍ G
           =
           C * ∑ G' : Flag σ (Fin ℓ'), labeledSubgraphListDensity [H₁, H₂]ᵍ G'.out
                                       * labeledSubgraphListDensity [G'.out, H₃]ᵍ G
  by exact (mul_right_inj' (by exact_mod_cast h_C_pos.ne')).mp this
  {
    have h_σ_size : σ.size = ℓ₀ := Fintype.card_fin ℓ₀
    have h_fintype_two₀ := fintype_card_match_comm_two ℓ₀ ℓ₁ ℓ₂
    have h_fintype_two₁ := fintype_card_match_comm_two ℓ₀ ℓ' ℓ₃
    have h_fintype_three := fintype_card_match_comm_three ℓ₀ ℓ₁ ℓ₂ ℓ₃
    have pair_density_eq_count_over_coeff :
        ∑ G' : Flag σ (Fin ℓ'),
          labeledSubgraphListDensity (labeledGraphPairToList H₁ H₂) G'.out *
          labeledSubgraphListDensity (labeledGraphPairToList G'.out H₃) G
        =
        ∑ G' : Flag σ (Fin ℓ'),
          @Nat.cast ℚ Rat.instNatCast ((labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) G'.out)) / (C_rhs₀) *
          ((labeledSubgraphListCount (labeledGraphPairToList G'.out H₃) G) / C_rhs₁)
      := by
      apply Finset.sum_congr rfl
      intro G' _
      congr!
      · dsimp [labeledSubgraphListDensity]
        congr
        · dsimp [labeledGraphPairToList, LabeledGraph.size]
          rw [h_σ_size, ← h_fintype_two₀]
          rfl
        · dsimp [LabeledGraph.size]
          exact Fintype.card_fin ℓ'
      · dsimp [labeledSubgraphListDensity]
        congr
        · dsimp [labeledGraphPairToList, LabeledGraph.size]
          rw [h_σ_size, ← h_fintype_two₁]
          rfl
        · dsimp [LabeledGraph.size]
          exact Fintype.card_fin ℓ
    rw [pair_density_eq_count_over_coeff]
    have triple_density_eq_count_over_coeff :
        labeledSubgraphListDensity (labeledGraphTripleToList H₁ H₂ H₃) G
        =
        (labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) / C_lhs
      := by
      dsimp [labeledSubgraphListDensity]
      congr
      · dsimp [labeledGraphTripleToList, LabeledGraph.size]
        rw [h_σ_size, ← h_fintype_three]
        rfl
      · dsimp [LabeledGraph.size]
        exact Fintype.card_fin ℓ
    rw [triple_density_eq_count_over_coeff]
    calc
      (C : ℚ) * (↑(labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) / ↑C_lhs)
      _ = ((C : ℚ) / ↑C_lhs) * ↑(labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                ring
      _ = ((C_lhs : ℚ) * ↑C_rhs₀ * ↑C_rhs₁ / ↑C_lhs) *
          ↑(labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                rw [Nat.cast_mul, Nat.cast_mul]
      _ = ((C_lhs : ℚ) * ((↑C_rhs₀ * ↑C_rhs₁) / ↑C_lhs)) *
          ↑(labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                ring
      _ = (C_rhs₀ : ℚ) * ↑C_rhs₁ *
          ↑(labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                field_simp
      _ = ↑(C_rhs₀ * C_rhs₁ * labeledSubgraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                simp only [Nat.cast_mul]
      _ = ↑(C_lhs * ∑ G' : Flag σ (Fin ℓ'),
                      (labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
                      (labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)) := by
                rw [labeledGraphTripleCount_eq_sum_density_prods ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ]
      _ = ↑C_lhs * ∑ G' : Flag σ (Fin ℓ'),
                      ↑(labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
                      ↑(labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G) := by
                simp only [Nat.cast_mul, Nat.cast_sum]
      _ = ((C_lhs : ℚ) * (↑C_rhs₀ * ↑C_rhs₁) / (↑C_rhs₀ * ↑C_rhs₁))
          * ∑ G' : Flag σ (Fin ℓ'),
              ↑(labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
              (↑(labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)) := by
                field_simp
      _ = ((C : ℚ) / (↑C_rhs₀ * ↑C_rhs₁))
          * ∑ G' : Flag σ (Fin ℓ'),
              ↑(labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
              (↑(labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)) := by
                rw [Nat.cast_mul, Nat.cast_mul]
                ring
      _ = (C : ℚ)
          * ((∑ G' : Flag σ (Fin ℓ'),
                ↑(labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
                (↑(labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)))
             / (↑C_rhs₀ * ↑C_rhs₁)) := by
                field_simp
      _ = (C : ℚ)
          * ∑ G' : Flag σ (Fin ℓ'),
              (↑(labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
               ↑(labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G))
              / (↑C_rhs₀ * ↑C_rhs₁) := by
                rw [Finset.sum_div]
      _ = (C : ℚ)
          * ∑ G' : Flag σ (Fin ℓ'),
            ↑(labeledSubgraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) / ↑C_rhs₀ *
            (↑(labeledSubgraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G) / ↑C_rhs₁) := by
                field_simp
  }

theorem flagTripleDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (F₃ : Flag σ (Fin ℓ₃)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : flagDensity₃ F₁ F₂ F₃ G = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ F₁ F₂ G' * flagDensity₂ G' F₃ G
  := by
  rw [←F₁.out_eq, ←F₂.out_eq, ←F₃.out_eq, ←G.out_eq]
  rw [←labeledSubgraphListDensity_eq_flagDensity₃ F₁.out F₂.out F₃.out G.out]
  have h : ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ ⟦F₁.out⟧ ⟦F₂.out⟧ G' * flagDensity₂ G' ⟦F₃.out⟧ ⟦G.out⟧
           = ∑ (G' : Flag σ (Fin ℓ')), labeledSubgraphListDensity [F₁.out, F₂.out]ᵍ G'.out * labeledSubgraphListDensity [G'.out, F₃.out]ᵍ G.out
    := by
    apply Finset.sum_congr (by rfl)
    intros G'
    rw [←G'.out_eq]
    rw [←labeledSubgraphListDensity_eq_flagDensity₂ F₁.out F₂.out G'.out]
    rw [←labeledSubgraphListDensity_eq_flagDensity₂ G'.out F₃.out G.out]
    simp only [Quotient.out_eq, Finset.mem_univ, imp_self]
  rw [h]
  exact labeledGraphTripleDensity_eq_sum_density_prods ℓ' F₁.out F₂.out F₃.out G.out hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ

theorem flagPairDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' ≤ ℓ)
    : flagDensity₂ F₁ F₂ G
      = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ F₁ F₂ G' * flagDensity₁ G' G
  := by
  rw [← flagTripleDensity_empty', flagTripleDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty']

theorem flagPairDensity_eq_sum_density_prods'
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ' : ℓ₁ ≤ ℓ') (hℓ : ℓ' + ℓ₂ ≤ ℓ + ℓ₀)
    : flagDensity₂ F₁ F₂ G
      = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₁ F₁ G' * flagDensity₂ G' F₂ G
  := by
  rw [← flagTripleDensity_empty, flagTripleDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty]

theorem flagDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ' : ℓ₁ ≤ ℓ') (hℓ : ℓ' ≤ ℓ)
    : flagDensity₁ F₁ G = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₁ F₁ G' * flagDensity₁ G' G
  := by
  rw [← flagPairDensity_empty, flagPairDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty]

alias density_chain_rule₁₁ := flagDensity_eq_sum_density_prods
alias density_chain_rule₁₂ := flagPairDensity_eq_sum_density_prods'
alias density_chain_rule₂₁ := flagPairDensity_eq_sum_density_prods
alias density_chain_rule₂₂ := flagTripleDensity_eq_sum_density_prods
