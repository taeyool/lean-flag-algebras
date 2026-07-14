import «LeanFlagAlgebras».Utils.Partitions
import «LeanFlagAlgebras».FlagAlgebra.SubflagDensity
import Batteries.Logic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Subset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/-!
# Densities of flags relative to a list of subflags

This file generalizes `SubflagDensity` from a single subflag to a finite *list* of
subflags. It defines `labeledGraphListDensity` (the fraction of vertex-class
arrangements realizing a whole list of disjoint, prescribed flags simultaneously),
lifts it through the flag quotient to `flagListDensity`, and specializes it to the
fixed-arity helpers `flagDensity₁` / `flagDensity₂` / `flagDensity₃`.

The technical core proves that `flagDensity₁` agrees with `subflagDensity`, that
list density is invariant under permutation / empty-flag insertion / isomorphism,
and culminates in the flag-algebra *chain rules* (`density_chain_rule₁₁` …
`density_chain_rule₂₂`): a product-flag density expands as a sum over intermediate
flags of products of densities. These chain rules are the key identities consumed
by `FlagAlgebra` to manipulate the quotient algebra `Aˢ`.
-/


namespace FlagAlgebras

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

/-- A length-`t` list of labeled subgraphs of a common host graph `G`, indexed by `Fin t`. -/
abbrev LabeledSubgraphList (σ : FlagType T) (t : ℕ) (G : LabeledGraph σ U)
  := Fin t → LabeledSubgraph σ G

/-- A subgraph list is induced when every member is an induced subgraph of `G`. -/
def LabeledSubgraphList.IsInduced
    {σ : FlagType T} {t : ℕ} {G : LabeledGraph σ U} (Hl : LabeledSubgraphList σ t G) : Prop
  := ∀ (i : Fin t), (Hl i).IsInduced

/-- The members of a subgraph list are pairwise disjoint outside the shared type
vertices: distinct entries share no non-type vertex. -/
def predDisjointLabeledSubgraphList
    {σ : FlagType T} {G : LabeledGraph σ V} (Gl : LabeledSubgraphList σ t G) : Prop
  :=
  ∀ (i j : Fin t), i ≠ j → ((Gl i).subgraph.verts \ G.type_verts) ∩ ((Gl j).subgraph.verts \ G.type_verts) = ∅

/-- A subgraph list realizes the prescribed flag list `Hl`: each member is
isomorphic to the corresponding `Hl i`, and the members are pairwise disjoint. -/
def predIsoLabeledHl
    {σ : FlagType T} (G : LabeledGraph σ V) (Hl : LabeledGraphList σ t Vl)
    : LabeledSubgraphList σ t G → Prop
  := fun Gl ↦
      (∀ (i : Fin t), Nonempty ((Gl i).coe ≃f Hl i))
      ∧ predDisjointLabeledSubgraphList Gl

/-- The set of induced subgraph lists of `G` that realize the prescribed flag list
`Hl`; its cardinality is the numerator of the list density. -/
def setOfLabeledSubgraphListIsoHl (G : LabeledGraph σ U) (Hl : LabeledGraphList σ t Vl)
      : Set (LabeledSubgraphList σ t G)
  :=
  { Gl | Gl.IsInduced ∧ predIsoLabeledHl G Hl Gl }

/-- The number of induced subgraph lists of `G` realizing the flag list `Hl`
(the numerator of the list density). -/
noncomputable def labeledGraphListCount
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℕ
  :=
  have : Fintype (setOfLabeledSubgraphListIsoHl G Hl) := Fintype.ofFinite _
  (setOfLabeledSubgraphListIsoHl G Hl).toFinset.card


/-- The density of the flag list `Hl` in `G`: the count of realizing subgraph lists
normalized by the multinomial coefficient counting ways to distribute the non-type
vertices among the list members. The list generalization of `labeledGraphDensity`. -/
noncomputable def labeledGraphListDensity
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list (i : Fin t) := (Hl i).size - σ.size
  labeledGraphListCount Hl G / multinomialCoefficient r_list (G.size - σ.size)

/-- Two subgraph lists correspond entrywise under the host isomorphism `φ`. -/
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

/-- Predicates `p₀`, `p₁` on subgraph lists correspond under `φ`: they agree on
every pair of `φ`-related lists. -/
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

/-- The list of induced subgraphs of `G` cut out by a list of vertex sets `Sl`,
each containing the type vertices. -/
def inducedLabeledSubgraphList
    {σ : FlagType T} (G : LabeledGraph σ U) (Sl : Fin t → Set U) (hSl : ∀ i : Fin t, G.type_verts ⊆ Sl i)
    : LabeledSubgraphList σ t G
  := fun i ↦ inducedLabeledSubgraph G (Sl i) (hSl i)

omit [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U] in
lemma inducedLabeledSubgraphList_isInduced
    {σ : FlagType T} (G : LabeledGraph σ U) (Sl : Fin t → Set U) (hSl : ∀ i : Fin t, G.type_verts ⊆ Sl i)
    : (inducedLabeledSubgraphList G Sl hSl).IsInduced
  := fun i ↦ inducedLabeledSubgraph_isInduced G (Sl i) (hSl i)

/-- Transport a subgraph list of `G₀` to `G₁` along the host isomorphism `φ`,
taking the induced image of each member. -/
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

/-- A host isomorphism `φ` carrying compatible predicates `p₀ ↔ p₁` induces a
bijection between the corresponding sets of induced subgraph lists. -/
def isoSetOfInducedLabeledSubgraphList
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
  have h_leftinv : Function.LeftInverse f_inv f := by
    rintro ⟨Hl₀, ⟨h_ind₀, h_p₀⟩⟩
    dsimp [f, f_inv]
    simp only [Subtype.mk.injEq]
    exact (Hl_eq_reverseinduced_induced_Hl φ Hl₀ h_ind₀).symm
  have h_rightinv : Function.RightInverse f_inv f := by
    rintro ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
    dsimp [f, f_inv]
    simp only [Subtype.mk.injEq]
    exact (Hl_eq_reverseinduced_induced_Hl φ.symm Hl₁ h_ind₁).symm
  ⟨f, f_inv, h_leftinv, h_rightinv⟩

/-- The instance of `isoSetOfInducedLabeledSubgraphList` for the realization
predicate `predIsoLabeledHl`, given a host isomorphism and an entrywise
isomorphism of the prescribed flag lists. -/
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
/-- List density is invariant under isomorphism of both the flag list and the host
graph; this well-definedness is what lets it descend to the flag quotient. -/
lemma labeledGraphListDensity_respect_eqv
    {Hl₀ : LabeledGraphList σ t Vl} {Hl₁ : LabeledGraphList σ t Vl'} (ψ : ∀ (i : Fin t), Hl₀ i ≃f Hl₁ i)
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁)
    : labeledGraphListDensity Hl₀ G₀ = labeledGraphListDensity Hl₁ G₁
  := by
  dsimp [labeledGraphListDensity]
  let S₀ := { Gl : LabeledSubgraphList σ t G₀ | Gl.IsInduced ∧ predIsoLabeledHl G₀ Hl₀ Gl}
  let S₁ := { Gl : LabeledSubgraphList σ t G₁ | Gl.IsInduced ∧ predIsoLabeledHl G₁ Hl₁ Gl}
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedLabeledSubgraphListFromIsoGHl φ ψ
  have h_count : labeledGraphListCount Hl₀ G₀ = labeledGraphListCount Hl₁ G₁ := by
    dsimp only [labeledGraphListCount]
    show S₀.toFinset.card = S₁.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.toFinset_card]
  have h_G_size : G₀.size = G₁.size := labeledGraphIso_size_eq G₀ G₁ φ
  rw [h_count, h_G_size]
  have h_Hl_sizes : ∀ i : Fin t, (Hl₀ i).size = (Hl₁ i).size :=
    fun i ↦ labeledGraphIso_size_eq (Hl₀ i) (Hl₁ i) (ψ i)
  simp only [h_Hl_sizes]

/-! ## Lifting list density through the flag quotients -/

/-- `labeledGraphListDensity Hl` lifted to accept a quotient `Flag σ W` host. -/
noncomputable def labeledGraphListDensityLifted
    (Hl : LabeledGraphList σ t Vl) : Flag σ W → ℚ :=
  Quotient.lift (fun G => labeledGraphListDensity Hl G)
    fun _ _ h_eqv => labeledGraphListDensity_respect_eqv (fun _ ↦ LabeledGraphIso.refl) h_eqv.some

omit [DecidableEq T] in
lemma labeledGraphListDensityLifted_respect_eqv
    {Hl : LabeledGraphList σ t Vl} {Hl' : LabeledGraphList σ t Vl'}
    (ψ : ∀ (i : Fin t), Hl i ≃f Hl' i) (G : Flag σ W)
    : labeledGraphListDensityLifted Hl G = labeledGraphListDensityLifted Hl' G
  := by
  dsimp [labeledGraphListDensityLifted]
  congr
  ext Grep
  exact labeledGraphListDensity_respect_eqv ψ LabeledGraphIso.refl

/-- List density with both arguments taken in their respective quotients:
a quotient flag list and a quotient flag host. -/
noncomputable def quotLabeledGraphListDensity
    : QuotLabeledGraphList σ t Vl → Flag σ W → ℚ :=
  Quotient.lift labeledGraphListDensityLifted
    fun _ _ ψ => funext fun G => labeledGraphListDensityLifted_respect_eqv (fun i ↦ (ψ i).some) G

omit [DecidableEq T] in
lemma quotLabeledGraphListDensity_respect_eqv
    {Hl Hl' : LabeledGraphList σ t Vl} (h : Hl ∼fl Hl') (G : Flag σ W)
    : quotLabeledGraphListDensity ⟦Hl⟧ G = quotLabeledGraphListDensity ⟦Hl'⟧ G
  :=
  labeledGraphListDensityLifted_respect_eqv (fun i ↦ (h i).some) G

/-- The density of a `FlagList` (a list of flags) inside a host flag `G`. This is
the headline list-density operator consumed downstream by `FlagAlgebra`. -/
noncomputable def flagListDensity
    : FlagList σ t Vl → Flag σ W → ℚ
  :=
  fun Fl => quotLabeledGraphListDensity Fl.coe

omit [DecidableEq T] in
theorem flagListDensity_HEq_eq
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (h_Vl_eq : Vl' = Vl) (h_HEq : HEq Fl Fl') (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity Fl' G
  := by
  subst h_Vl_eq
  have h_Fl_eq : Fl = Fl' := by rw [←heq_eq_eq Fl Fl']; exact h_HEq
  subst h_Fl_eq
  dsimp [flagListDensity, quotLabeledGraphListDensity, eqv_QuotLabeledGraphList_FlagList]
  dsimp [labeledGraphListDensityLifted, labeledGraphListDensity]
  congr!

omit [DecidableEq T] in
/-- The single-subflag density agrees with the list density of the singleton list,
connecting this file to `SubflagDensity`. -/
theorem subflagDensity_eq_flagListDensity
    {σ : FlagType T} (F : Flag σ U) (G : Flag σ W)
    : subflagDensity F G = flagListDensity (flagToList F) G
  := by
  rcases Quotient.exists_rep F with ⟨Frep, hFrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  have h_count : labeledGraphCount Frep Grep = labeledGraphListCount (fun (_ : Fin 1) => Frep) Grep := by
    dsimp [labeledGraphCount, labeledGraphListCount]
    apply Finset.card_bij
    · intro H hH
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hH
      show (fun (_ : Fin 1) => H) ∈ _
      simp only [setOfLabeledSubgraphListIsoHl, LabeledSubgraphList.IsInduced, predIsoLabeledHl,
        forall_const, true_and, Set.coe_setOf, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ]
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
        true_and, and_self, exists_const, Set.coe_setOf, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ]
      ext1 i
      rw [Fin.fin_one_eq_zero i]
  calc
    subflagDensity F G = labeledGraphDensity Frep Grep := by
      subst hFrep hGrep
      rfl
    _ = labeledGraphListDensity (fun (_ : Fin 1) => Frep) Grep := by
      dsimp [labeledGraphDensity, labeledGraphListDensity]
      rw [← h_count, multinomialCoefficient_fin_one]; congr
    _ = quotLabeledGraphListDensity [F]ᶠ.coe G := by
      have : [F]ᶠ.coe = ⟦fun (_ : Fin 1) => Frep⟧ := by
        dsimp [eqv_QuotLabeledGraphList_FlagList]
        apply Quotient.sound
        intro i
        simp only [flagToList, ← hFrep]
        apply Quotient.mk_out Frep
      rw [this, ← hGrep]
      rfl
    _ = flagListDensity [F]ᶠ G := rfl

/-- Density of a single flag `F` in `G` (the list density of `[F]`). -/
noncomputable def flagDensity₁ (F : Flag σ U) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F]ᶠ G

/-- Joint density of two disjoint flags `F₁, F₂` in `G` (the list density of
`[F₁, F₂]`); the product appearing on the right-hand side of the chain rules. -/
noncomputable def flagDensity₂ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂]ᶠ G

/-- Joint density of three disjoint flags in `G` (the list density of
`[F₁, F₂, F₃]`); the most general case driving the chain-rule recursion. -/
noncomputable def flagDensity₃ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (F₃ : Flag σ U₃) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂, F₃]ᶠ G

omit [DecidableEq T] in
/-! ## Bridging representatives and quotients; basic invariants -/

/-- Computing list density on labeled-graph representatives equals computing
`flagListDensity` on their quotient images. -/
theorem labeledGraphListDensity_eq_flagListDensity
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : labeledGraphListDensity Fl G = flagListDensity (QuotLabeledGraphList.coe ⟦Fl⟧) ⟦G⟧
  := by
  show quotLabeledGraphListDensity ⟦Fl⟧ ⟦G⟧ = flagListDensity (QuotLabeledGraphList.coe ⟦Fl⟧) ⟦G⟧
  dsimp [flagListDensity, eqv_QuotLabeledGraphList_FlagList]
  apply quotLabeledGraphListDensity_respect_eqv
  calc
    Fl ∼fl (fun i => ⟦Fl⟧.out i) := flagListEqv.symm (Quotient.mk_out Fl)
    _ ∼fl (fun i => ⟦⟦Fl⟧.out i⟧.out) := by
      dsimp [flagListEqv]
      intro i
      exact flagEqv.symm (Quotient.mk_out (⟦Fl⟧.out i))

omit [DecidableEq T] in
theorem labeledGraphListDensity_eq_flagDensity₁
    (F : LabeledGraph σ U) (G : LabeledGraph σ W)
    : labeledGraphListDensity [F]ᵍ G = flagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  rw [labeledGraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_singleton]
  simp only [QuotLabeledGraphList.coe, FlagList.coe,
    Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, flagDensity₁]

omit [DecidableEq T] in
theorem labeledGraphListDensity_eq_flagDensity₂
    (F₁ : LabeledGraph σ U₁) (F₂ : LabeledGraph σ U₂) (G : LabeledGraph σ W)
    : labeledGraphListDensity [F₁, F₂]ᵍ G = flagDensity₂ ⟦F₁⟧ ⟦F₂⟧ ⟦G⟧
  := by
  rw [labeledGraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_pair]
  simp only [QuotLabeledGraphList.coe, FlagList.coe,
    Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, flagDensity₂]

omit [DecidableEq T] in
theorem labeledGraphListDensity_eq_flagDensity₃
    (F₁ : LabeledGraph σ U₁) (F₂ : LabeledGraph σ U₂) (F₃ : LabeledGraph σ U₃) (G : LabeledGraph σ W)
    : labeledGraphListDensity [F₁, F₂, F₃]ᵍ G = flagDensity₃ ⟦F₁⟧ ⟦F₂⟧ ⟦F₃⟧ ⟦G⟧
  := by
  rw [labeledGraphListDensity_eq_flagListDensity, list_quot_eq_quot_list_triple]
  simp only [QuotLabeledGraphList.coe, FlagList.coe,
    Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, flagDensity₃]

/-- The empty flag has density `1` in every host. -/
theorem flagDensity_empty
    (F : Flag σ W) : flagDensity₁ (emptyFlag σ) F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity (emptyFlag σ) F]
  exact subflagDensity_empty F

omit [DecidableEq T] in
/-- A flag has density `1` in itself. -/
theorem flagDensity_self
    (F : Flag σ W) : flagDensity₁ F F = 1
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F]
  exact subflagDensity_self F

omit [DecidableEq T] in
/-- Distinct flags of the same size have density `0` in each other. -/
theorem flagDensity_other
    {F F' : Flag σ W} (h_neq : F ≠ F') : flagDensity₁ F F' = 0
  := by
  dsimp [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity F F']
  exact subflagDensity_other h_neq

omit [DecidableEq T] in
/-- Positive density forces the subflag to be no larger than the host. -/
theorem flagDensity_le_card
    {F : Flag σ V} {G : Flag σ W} (h : flagDensity₁ F G > 0)
    : Fintype.card V ≤ Fintype.card W
  := by
  obtain ⟨Grep, hGrep⟩ := Quotient.exists_rep G
  obtain ⟨Frep, hFrep⟩ := Quotient.exists_rep F
  dsimp [flagDensity₁] at h
  rw [← subflagDensity_eq_flagListDensity F G, ← hGrep, ← hFrep] at h
  dsimp [subflagDensity, labeledGraphDensityLifted, labeledGraphDensity] at h
  have : labeledGraphCount Frep Grep > 0 := by
    apply Nat.pos_of_ne_zero
    intro h_zero
    rw [h_zero] at h
    simp only [Nat.cast_zero, zero_div, gt_iff_lt, lt_self_iff_false] at h
  simp only [labeledGraphCount, Set.toFinset_setOf, gt_iff_lt, Finset.card_pos] at this
  obtain ⟨G_sub, hG_sub⟩ := this
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG_sub
  obtain ⟨h_ind, h_iso⟩ := hG_sub
  let h_iso := h_iso.some
  have h_G_sub_Frep : G_sub.size = Frep.size := labeledGraphIso_size_eq G_sub.coe Frep h_iso
  have : G_sub.size ≤ Grep.size := by
    simp only [size, Fintype.card_ofFinset, LabeledGraph.size]
    exact Finset.card_le_univ (Finset.filter (Membership.mem G_sub.subgraph.verts) Finset.univ)
  rw [h_G_sub_Frep] at this
  exact this

omit [DecidableEq T] in
theorem flagDensity_le_card'
    {F : Flag σ V} {F' : Flag σ U} {G : Flag σ W} (h : flagDensity₂ F F' G > 0)
    : Fintype.card V ≤ Fintype.card W ∧ Fintype.card U ≤ Fintype.card W
  := by
  obtain ⟨Grep, hGrep⟩ := Quotient.exists_rep G
  obtain ⟨Frep, hFrep⟩ := Quotient.exists_rep F
  obtain ⟨F'rep, hF'rep⟩ := Quotient.exists_rep F'
  rw [← hFrep, ← hF'rep, ← hGrep, ← labeledGraphListDensity_eq_flagDensity₂ Frep F'rep Grep] at h
  dsimp [labeledGraphListDensity] at h
  have h_count_pos : 0 < labeledGraphListCount (labeledGraphPairToList Frep F'rep) Grep := by
    apply Nat.pos_of_ne_zero
    intro h_zero
    rw [h_zero] at h
    simp only [Nat.cast_zero, zero_div, gt_iff_lt, lt_self_iff_false] at h
  simp only [labeledGraphListCount, setOfLabeledSubgraphListIsoHl, Set.toFinset_card] at h_count_pos
  have ⟨⟨Gl, hGl⟩, _⟩ := Finset.card_pos.mp h_count_pos
  simp only [predIsoLabeledHl, Set.mem_setOf_eq] at hGl
  let h_iso := (hGl.2.1 0).some
  let h_iso' := (hGl.2.1 1).some
  have h_Gl_Frep : (Gl 0).size = Frep.size := labeledGraphIso_size_eq (Gl 0).coe Frep h_iso
  have h_Gl_F'rep : (Gl 1).size = F'rep.size := labeledGraphIso_size_eq (Gl 1).coe F'rep h_iso'
  have h_Gl0_le_Grep : (Gl 0).size ≤ Grep.size := by
    simp only [size, Fintype.card_ofFinset, LabeledGraph.size]
    exact Finset.card_le_univ (Finset.filter (Membership.mem (Gl 0).subgraph.verts) Finset.univ)
  have h_Gl1_le_Grep : (Gl 1).size ≤ Grep.size := by
    simp only [size, Fintype.card_ofFinset, LabeledGraph.size]
    exact Finset.card_le_univ (Finset.filter (Membership.mem (Gl 1).subgraph.verts) Finset.univ)
  rw [h_Gl_Frep] at h_Gl0_le_Grep
  rw [h_Gl_F'rep] at h_Gl1_le_Grep
  exact ⟨h_Gl0_le_Grep, h_Gl1_le_Grep⟩

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

/-! ## Symmetry: permuting and inserting empty flags -/

/-- Permuting the prescribed flag list by `π` bijects the realizing-subgraph-list
sets, so the count is permutation-invariant. -/
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
      simp_all only [predIsoLabeledHl, predDisjointLabeledSubgraphList,
        ne_eq, implies_true, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, and_self, Hl₁]
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
        have h_eq : π (π.invFun i) = i := π.apply_symm_apply _
        have : Nonempty ((Hl₁ (π.invFun i)).coe ≃f (Hl (π (π.invFun i)))) := h_p₁.1 (π.invFun i)
        rw [h_eq] at this
        exact this
      · intro i j h_ij
        simp_all only [predIsoLabeledHl, predDisjointLabeledSubgraphList,
          ne_eq, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, Hl₀]
    use ⟨Hl₀, h_ind₀, h_p₀⟩
    simp_all only [f, Equiv.invFun_as_coe, Equiv.symm_apply_apply, Hl₀]
  Equiv.ofBijective f ⟨h_inj_f, h_surj_f⟩

omit [DecidableEq T] in
/-- List density is invariant under permuting the list of flags. -/
theorem flagDensity_permute
    (Fl : FlagList σ t Vl) (G : Flag σ W) (π : Perm t)
    : flagListDensity Fl G = flagListDensity (Fl.permute π) G
  := by
  dsimp [flagListDensity, quotLabeledGraphListDensity]
  congr; ext Grep
  let S₀ := setOfLabeledSubgraphListIsoHl Grep (fun i => Quotient.out (Fl i))
  let S₁ := setOfLabeledSubgraphListIsoHl Grep (fun i => Quotient.out (Fl (π i)))
  let f_iso_S₀_S₁ : S₀ ≃ S₁ := setOfLabeledSubgraphListIsoHl_permute Grep (fun i => Quotient.out (Fl i)) π
  let hS₀ : Fintype S₀ := Fintype.ofFinite S₀
  let hS₁ : Fintype S₁ := Fintype.ofFinite S₁
  have h_count : labeledGraphListCount (fun i => Quotient.out (Fl.permute π i)) Grep
                 = labeledGraphListCount (fun i => Quotient.out (Fl i)) Grep
    := by
    dsimp only [labeledGraphListCount]
    show S₁.toFinset.card = S₀.toFinset.card
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr f_iso_S₀_S₁
    simp_all only [Set.toFinset_card]
  have h_coeff : multinomialCoefficient (fun i ↦ (Quotient.out (Fl i)).size - σ.size) (Grep.size - σ.size)
                 = multinomialCoefficient (fun i ↦ (Quotient.out (Fl.permute π i)).size - σ.size) (Grep.size - σ.size)
    := (multinomialCoefficient_eq_of_perm (Grep.size - σ.size)).symm
  dsimp [labeledGraphListDensity]
  rw [h_count, h_coeff]

/-! ### `FintypeList` / `DecidableEqList` instances for 2- and 3-element type families

Routine type-class plumbing so that pair/triple flag lists (`[F₁, F₂]ᶠ`,
`[F₁, F₂, F₃]ᶠ`) can be formed and their densities computed. -/

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
/-- The joint density of two flags is symmetric in the two flags. -/
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
/-- The joint density of three flags is invariant under cyclic rotation. -/
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


/-- Appending an empty flag to the prescribed list does not change the set of
realizing subgraph lists (up to a canonical bijection). -/
def setOfLabeledSubgraphListIsoHl_insert_empty
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
  have h_leftinv : Function.LeftInverse f_inv f := by
    intro ⟨Hl₀, h_ind₀, h_p₀⟩
    dsimp [f, f_inv]
    simp only [Subtype.mk.injEq, Fin.is_lt]
    rfl
  have h_rightinv : Function.RightInverse f_inv f := by
    rintro ⟨Hl₁, ⟨h_ind₁, h_p₁⟩⟩
    dsimp [f, f_inv]
    simp only [Subtype.mk.injEq]
    funext i
    split
    next _ =>
      rfl
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
  ⟨f, f_inv, h_leftinv, h_rightinv⟩

/-- Inserting an empty flag into the list leaves the list density unchanged.
Used to reduce fixed-arity densities to each other (e.g. pair to single). -/
theorem flagDensity_insert_empty
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity (Fl.insert (emptyFlag σ)) G
  := by
  dsimp [flagListDensity, quotLabeledGraphListDensity]
  congr; ext Grep
  dsimp [labeledGraphListDensity, labeledGraphListCount]
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
    simp only [Z₀, Z₁, multinomialCoefficient, dite_eq_ite]
    simp_rw [sum_eq_sum_plus_last, prod_eq_prod_mul_last, ← h_eq, tsub_self,
      add_zero, h_eq', Nat.factorial_zero, mul_one]
  rw [h_count, h_coeff]

/-- Pairing a flag with the empty flag reduces to the single-flag density. -/
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

/-- A triple density with one empty flag reduces to the pair density; used to
specialize the triple chain rule down to the pair and single chain rules. -/
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


omit [DecidableEq T] in
/-! ## Density is a probability: bounds in `[0, 1]` -/

/-- List density is nonnegative. -/
theorem labeledGraphListDensity_ge_zero
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : 0 ≤ labeledGraphListDensity Fl G := by
    dsimp [labeledGraphListDensity]
    apply div_nonneg <;> simp only [Nat.cast_nonneg]

omit [DecidableEq T] in
/-- List density is at most `1` (the realizing lists inject into the partitions of
the non-type vertices counted by the multinomial normalizer). -/
theorem labeledGraphListDensity_le_one
    (Fl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W)
    : labeledGraphListDensity Fl G ≤ 1 := by
    dsimp only [labeledGraphListDensity, labeledGraphListCount, setOfLabeledSubgraphListIsoHl, Set.coe_setOf]
    apply div_le_one_of_le₀ <;> try simp only [Nat.cast_nonneg]
    let VG := (Finset.univ : Finset W) \ G.type_verts.toFinset
    have h_VG : VG.card = G.size - σ.size := by
      simp only [VG, LabeledGraph.size, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      rw [Set.toFinset_card, Finset.card_univ, LabeledGraph.type_verts_card_eq]
    let r_list : Fin t → ℕ := fun i => (Fl i).size - σ.size
    rw [← h_VG, ← partition_card VG (r_list), Nat.cast_le]
    let f : (Fin t → LabeledSubgraph σ G) → (Fin t → Finset W) := fun Gl i => (Gl i).subgraph.verts.toFinset \ G.type_verts.toFinset
    apply Finset.card_le_card_of_injOn f
    · rintro Gl hGl
      dsimp only [partitions, ne_eq, f]
      simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_univ, forall_const,
        Finset.coe_filter, true_and, Set.mem_setOf_eq]
      simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hGl
      obtain ⟨_, hGl_iso, hGl_disj⟩ := hGl
      refine ⟨fun i ↦ ⟨?_, ?_⟩, fun i j hij ↦ ?_, fun i ↦ ?_⟩
      · refine Finset.sdiff_subset_sdiff ?h.hf.right.left.left.hst fun ⦃a⦄ a ↦ a
        simp_all only [Finset.subset_univ]
      · have : G.type_verts.toFinset ⊆ (Gl i).subgraph.verts.toFinset := by
          simp only [Set.subset_toFinset, Set.coe_toFinset]
          exact labeledSubgraph_contain_type_verts G (Gl i)
        rw [Finset.card_sdiff_of_subset this, Set.toFinset_card, Set.toFinset_card, LabeledGraph.type_verts_card_eq]
        dsimp only [r_list]
        congr!
        exact labeledGraphIso_size_eq (Gl i).coe (Fl i) (Classical.choice (hGl_iso i))
      · rw [Finset.disjoint_left]
        intro w h_wi h_wj
        rw [Finset.mem_sdiff] at h_wi h_wj
        obtain ⟨h_w_mem_i, h_w_not_type⟩ := h_wi
        obtain ⟨h_w_mem_j, _⟩ := h_wj
        rw [Set.mem_toFinset] at h_w_mem_i h_w_mem_j h_w_not_type
        have h_w_in_inter : w ∈ (Gl i).subgraph.verts \ G.type_verts ∩ ((Gl j).subgraph.verts \ G.type_verts) := by
          rw [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff]
          exact ⟨⟨h_w_mem_i, h_w_not_type⟩, ⟨h_w_mem_j, h_w_not_type⟩⟩
        rw [hGl_disj i j hij] at h_w_in_inter
        exact h_w_in_inter
      · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) fun ⦃a⦄ ↦ id
    · intro Gl₁ hGl₁ Gl₂ hGl₂ h_eq
      rw [funext_iff] at h_eq
      dsimp [f] at h_eq
      simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hGl₁ hGl₂
      obtain ⟨hGl₁_ind, _, _⟩ := hGl₁
      obtain ⟨hGl₂_ind, _, _⟩ := hGl₂
      funext i
      apply labeledSubgraph_eq_from_subgraph_eq
      have hGl₁_i_ind := @hGl₁_ind i
      have hGl₂_i_ind := @hGl₂_ind i
      specialize h_eq i
      rw [← Set.toFinset_diff, ← Set.toFinset_diff, Set.toFinset_inj] at h_eq
      have h_eq_verts : (Gl₁ i).subgraph.verts = (Gl₂ i).subgraph.verts := by
        calc
          (Gl₁ i).subgraph.verts = (Gl₁ i).subgraph.verts \ G.type_verts ∪ G.type_verts := by
            exact (Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl₁ i))).symm
          _ = (Gl₂ i).subgraph.verts \ G.type_verts ∪ G.type_verts := by rw [h_eq]
          _ = (Gl₂ i).subgraph.verts := by
            exact (Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl₂ i)))
      calc
        (Gl₁ i).subgraph = (⊤ : G.graph.Subgraph).induce (Gl₁ i).subgraph.verts := by
          exact (hGl₁_i_ind.induce_top_verts).symm
        _ = (⊤ : G.graph.Subgraph).induce (Gl₂ i).subgraph.verts := by rw [h_eq_verts]
        _  = (Gl₂ i).subgraph := by exact hGl₂_i_ind.induce_top_verts

omit [DecidableEq T] in
theorem quotLabeledGraphListDensity_ge_zero
    (Fl : QuotLabeledGraphList σ t Vl) (G :Flag σ W)
    : 0 ≤ quotLabeledGraphListDensity Fl G
  := by
  rcases Quot.exists_rep Fl with ⟨Flrep, hFlrep⟩
  rcases Quot.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hFlrep, ← hGrep]
  apply labeledGraphListDensity_ge_zero

omit [DecidableEq T] in
theorem quotLabeledGraphListDensity_le_one
    (Fl : QuotLabeledGraphList σ t Vl) (G :Flag σ W)
    : quotLabeledGraphListDensity Fl G ≤ 1
  := by
  rcases Quot.exists_rep Fl with ⟨Flrep, hFlrep⟩
  rcases Quot.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hFlrep, ← hGrep]
  apply labeledGraphListDensity_le_one

omit [DecidableEq T] in
/-- `flagListDensity` is nonnegative. -/
theorem flagListDensity_ge_zero
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : 0 ≤ flagListDensity Fl G
  := by
  dsimp [flagListDensity]
  apply quotLabeledGraphListDensity_ge_zero

omit [DecidableEq T] in
/-- `flagListDensity` is at most `1`. -/
theorem flagListDensity_le_one
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G ≤ 1
  := by
  dsimp [flagListDensity]
  apply quotLabeledGraphListDensity_le_one

omit [DecidableEq T] in
theorem flagListDensity₁_ge_zero
    (F : Flag σ V) (G : Flag σ W)
    : 0 ≤ flagDensity₁ F G
  := by
  apply flagListDensity_ge_zero

omit [DecidableEq T] in
theorem flagListDensity₁_le_one
    (F : Flag σ V) (G : Flag σ W)
    : flagDensity₁ F G ≤ 1
  := by
  apply flagListDensity_le_one

omit [DecidableEq T] in
theorem flagListDensity₂_ge_zero
    (F : Flag σ V) (F' : Flag σ U) (G : Flag σ W)
    : 0 ≤ flagDensity₂ F F' G
  := by
  apply flagListDensity_ge_zero

omit [DecidableEq T] in
theorem flagListDensity₂_le_one
    (F : Flag σ V) (F' : Flag σ U) (G : Flag σ W)
    : flagDensity₂ F F' G ≤ 1
  := by
  apply flagListDensity_le_one

omit [DecidableEq T] in
theorem flagDensity_le_card_contra
    {F : Flag σ V} {G : Flag σ W}
    : Fintype.card V > Fintype.card W → flagDensity₁ F G = 0
  := by
  contrapose!
  intro h
  exact flagDensity_le_card (lt_of_le_of_ne (flagListDensity₁_ge_zero F G) (Ne.symm h))

omit [DecidableEq T] in
theorem flagDensity_le_card_contra'
    {F : Flag σ V} {F' : Flag σ U} {G : Flag σ W}
    : Fintype.card V > Fintype.card W ∨ Fintype.card U > Fintype.card W → flagDensity₂ F F' G = 0
  := by
  contrapose!
  intro h
  exact flagDensity_le_card' (lt_of_le_of_ne (flagListDensity₂_ge_zero F F' G) (Ne.symm h))

/- Chain rules -/

variable {ℓ₀ : ℕ} {σ : FlagType (Fin ℓ₀)}

lemma labeledSubgraph_card_from_iso
    (G : LabeledGraph σ (Fin ℓ)) (G' : LabeledSubgraph σ G) (H₁ : LabeledGraph σ (Fin ℓ₁)) (h : Nonempty (G'.coe ≃f H₁))
    : (G'.subgraph.verts \ G.type_verts).toFinset.card = ℓ₁ - ℓ₀
  := by
  let V' : Set (Fin ℓ) := G'.subgraph.verts \ G.type_verts
  have h_G'_verts_card : (Fintype.card G'.subgraph.verts) = ℓ₁ := by
    have : ℓ₁ = (Fintype.card (Fin ℓ₁) : ℕ) := Eq.symm (Fintype.card_fin ℓ₁)
    rw [this]
    exact Fintype.card_congr h.some.graph_iso
  have h_G_type_verts_subset_G'_verts : G.type_verts ⊆ G'.subgraph.verts :=
    labeledSubgraph_contain_type_verts G G'
  have h_G_type_verts_card : (Fintype.card G.type_verts) = ℓ₀ := by
    rw [G.type_verts_card_eq]
    dsimp [FlagType.size]
    exact (Fintype.card_fin ℓ₀)
  have h : V'.toFinset.card = ℓ₁ - ℓ₀ :=
    calc
      V'.toFinset.card = (G'.subgraph.verts.toFinset \ G.type_verts.toFinset).card := by
            dsimp [V']; simp only [Set.toFinset_diff]
      _ = G'.subgraph.verts.toFinset.card - G.type_verts.toFinset.card :=
            Finset.card_sdiff_of_subset (by simp only [Set.subset_toFinset, Set.coe_toFinset, h_G_type_verts_subset_G'_verts])
      _ = Fintype.card G'.subgraph.verts - Fintype.card G.type_verts := by
            simp only [Set.toFinset_card, Fintype.card_ofFinset]
      _ = ℓ₁ - ℓ₀ := by
            rw [h_G'_verts_card, h_G_type_verts_card]
  rw [←h]

lemma inducedLabeledSubgraph_iso_from_iso
    {G : LabeledGraph σ (Fin ℓ)} {G₁ : LabeledSubgraph σ G} (h_ind : G₁.IsInduced)
    {H₁ : LabeledGraph σ (Fin ℓ₁)} (h_iso : Nonempty (G₁.coe ≃f H₁))
    : Nonempty ((inducedLabeledSubgraph G
                    ((G₁.subgraph.verts \ G.type_verts) ∪ G.type_verts)
                    Set.subset_union_right).coe
                ≃f H₁)
  := by
  let V₁ := G₁.subgraph.verts \ G.type_verts
  have type_verts_subset_subgraph_verts := labeledSubgraph_contain_type_verts G G₁
  have h_G₁_verts : G₁.subgraph.verts = V₁ ∪ G.type_verts := by
    rw [G₁.subgraph.verts.union_empty.symm, Set.diff_union_self, Set.union_empty,
      Set.union_eq_self_of_subset_right type_verts_subset_subgraph_verts]
  let G₁' := inducedLabeledSubgraph G G₁.subgraph.verts type_verts_subset_subgraph_verts
  let G₁'' := inducedLabeledSubgraph G (V₁ ∪ G.type_verts) Set.subset_union_right
  have h_eq₀ : G₁ = G₁' := inducedLabeledSubgraph_eq h_ind
  have h_eq₁ : G₁' = G₁'' := by dsimp [G₁', G₁'']; congr!
  rw [h_eq₀, h_eq₁] at h_iso
  exact h_iso

/-- The list of non-type vertex sets carried by the members of a subgraph list. -/
def vertexSetListFromLabeledSubgraphList
    {G : LabeledGraph σ (Fin ℓ)} (Gl : LabeledSubgraphList σ t G) : (i : Fin t) → Set (Fin ℓ)
  := fun i ↦(Gl i).subgraph.verts \ G.type_verts

lemma disjointLabeledSubgraphList_induce_disjointVertexSetList
  {G : LabeledGraph σ (Fin ℓ)} (Gl : LabeledSubgraphList σ t G) (h_disj : predDisjointLabeledSubgraphList Gl)
  : Set.univ.PairwiseDisjoint (vertexSetListFromLabeledSubgraphList Gl)
  := by
  intro i _ j _ h_ij_neq
  dsimp [Function.onFun, vertexSetListFromLabeledSubgraphList]
  exact Set.disjoint_iff_inter_eq_empty.mpr (h_disj i j h_ij_neq)

/-! ## The triple chain rule: bijection construction and counting

The next group builds, in four explicit steps (`…_step0` … `…_step3`), a
bijection identifying choices of a realizing triple in `G` with choices of an
intermediate flag `G'` together with realizing pairs in `G'` and in `G`. This is
the combinatorial heart of the chain rule for triple densities. -/

/-- A choice of bijection `Fin ℓ₀ ≃ X₀` from a finite set `X₀` of known size `ℓ₀`. -/
noncomputable def isoFromFinToFiniteSet
    {ℓ ℓ₀ : ℕ} (X₀ : Set (Fin ℓ)) (h : X₀.toFinset.card = ℓ₀)
    : Fin ℓ₀ ≃ X₀
  :=
  let f₀ : Fin ℓ₀ ≃ Fin X₀.toFinset.card := by rw [h]
  let f₁ : Fin X₀.toFinset.card ≃ X₀.toFinset := X₀.toFinset.equivFin.symm
  let f₂ : X₀.toFinset ≃ X₀ := Equiv.subtypeEquivRight (by simp only [Set.mem_toFinset, implies_true])
  (f₀.trans f₁).trans f₂

/-- Chain-rule bijection, step 0: rephrase a powerset choice paired with a
realizing triple in `G` as a pair of a set and a vertex-set triple satisfying the
realization/disjointness conditions. -/
noncomputable def
  powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step0
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    (ℓ_other : ℕ) (h_ℓ_other :  ℓ_other = (ℓ - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀) - (ℓ₃ - ℓ₀))
    (ℓ'_other : ℕ) (h_ℓ'_other : ℓ'_other = (ℓ' - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀))
    (Hl_size : Fin 3 → ℕ) (h_Hl_size : Hl_size 0 = ℓ₁ ∧ Hl_size 1 = ℓ₂ ∧ Hl_size 2 = ℓ₃)
    (Hl : (i : Fin 3) → LabeledGraph σ (Fin (Hl_size i))) (h_Hl : Hl 0 ≍ H₁ ∧ Hl 1 ≍ H₂ ∧ Hl 2 ≍ H₃)
    : (Finset.univ : Finset (Fin ℓ_other)).powersetCard ℓ'_other
      × (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset
      ≃
      { ⟨X, Vl⟩ : Finset (Fin ℓ_other) × (Fin 3 → Set (Fin ℓ))
                | X.card = ℓ'_other
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }
  :=
  let LHS := (Finset.univ : Finset (Fin ℓ_other)).powersetCard ℓ'_other
             × (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset

  let S₀ := { ⟨X, Gl'⟩ : Finset (Fin ℓ_other) × LabeledSubgraphList σ 3 G
                | X.card = ℓ'_other
                ∧ Gl'.IsInduced
                ∧ predIsoLabeledHl G [H₁, H₂, H₃]ᵍ Gl' }
  let S₁ := { ⟨X, Vl⟩ : Finset (Fin ℓ_other) × (Fin 3 → Set (Fin ℓ))
                | X.card = ℓ'_other
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }

  let ⟨h_Hl_size₀, h_Hl_size₁, h_Hl_size₂⟩ := h_Hl_size

  let ⟨h_Hl₀, h_Hl₁, h_Hl₂⟩ := h_Hl
  let iso_Hl₀ : H₁ ≃f Hl 0 := by
    subst h_Hl_size₀
    simp only [Fin.isValue, heq_eq_eq] at h_Hl₀
    rw [h_Hl₀]
  let iso_Hl₁ : H₂ ≃f Hl 1 := by
    subst h_Hl_size₁
    simp only [Fin.isValue, heq_eq_eq] at h_Hl₁
    rw [h_Hl₁]
  let iso_Hl₂ : H₃ ≃f Hl 2 := by
    subst h_Hl_size₂
    simp only [Fin.isValue, heq_eq_eq] at h_Hl₂
    rw [h_Hl₂]
  let iso_Hl : (i : Fin 3) → labeledGraphTripleToList H₁ H₂ H₃ i ≃f Hl i := by
    intro i
    match i with
    | 0 => exact iso_Hl₀
    | 1 => exact iso_Hl₁
    | 2 => exact iso_Hl₂

  let f_LHS_S₀ : LHS ≃ S₀ :=
    let f_LHS_S₀_fwd : LHS → S₀ := by
      intro ⟨⟨X,h_X⟩, ⟨Gl',h_Gl'⟩⟩
      refine ⟨⟨X, Gl'⟩, ?h⟩
      have h_X_card : X.val.card = ℓ'_other := by
        simp_all only [
          Finset.mem_powersetCard, Finset.subset_univ, true_and,
          Set.mem_toFinset, Finset.card_val]
      let ⟨h_Gl'_ind, h_Gl'_other⟩ : Gl'.IsInduced ∧ predIsoLabeledHl G [H₁, H₂, H₃]ᵍ Gl' := by
        dsimp [setOfLabeledSubgraphListIsoHl] at h_Gl'
        simp_all only [
          Finset.mem_powersetCard, Finset.subset_univ, true_and, Set.toFinset_setOf,
          Finset.mem_filter, Finset.mem_univ, Finset.card_val, and_self]
      exact ⟨h_X_card, h_Gl'_ind, h_Gl'_other⟩

    have h_f_LHS_S₀_inj : Function.Injective f_LHS_S₀_fwd := by
      intro ⟨⟨X₁, Gl₁⟩, h₁⟩ ⟨⟨X₂, Gl₂⟩, h₂⟩ h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq, f_LHS_S₀_fwd] at h_eq
      let ⟨h_eq_X, h_eq_h'⟩ := h_eq
      have h_eq_h : h₁ = h₂ := Subtype.ext h_eq_h'
      simp only [h_eq_X, h_eq_h]

    have h_f_LHS_S₀_surj : Function.Surjective f_LHS_S₀_fwd := by
      intro ⟨⟨X, Gl⟩, h_X_card, h_Gl_ind, h_Gl_other⟩
      have h_X : X ∈ Finset.powersetCard ℓ'_other Finset.univ := by
        simp only [Finset.mem_powersetCard, Finset.subset_univ, h_X_card, and_self]
      have h_Gl : Gl ∈ (setOfLabeledSubgraphListIsoHl G (labeledGraphTripleToList H₁ H₂ H₃)).toFinset := by
        simp only [setOfLabeledSubgraphListIsoHl, Set.mem_setOf_eq, Set.toFinset_setOf,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h_Gl_ind, h_Gl_other⟩
      use ⟨⟨X, h_X⟩, ⟨Gl, h_Gl⟩⟩

    Equiv.ofBijective f_LHS_S₀_fwd ⟨h_f_LHS_S₀_inj, h_f_LHS_S₀_surj⟩

  let f_S₀_S₁ : S₀ ≃ S₁ :=
    let f_S₀_S₁_fwd : S₀ → S₁ := by
      intro ⟨⟨X, Gl'⟩, h_X_card, h_Gl'_ind, h_Gl'_other⟩
      let Vl (i : Fin 3) := (Gl' i).subgraph.verts \ G.type_verts
      let ⟨h_Gl'_other_iso', h_Gl'_other_disj⟩ := h_Gl'_other
      have h_Gl'_other_iso : ∀ i : Fin 3, Nonempty ((Gl' i).coe ≃f Hl i) := by
        intro i
        let f_iso₁ : (Gl' i).coe ≃f labeledGraphTripleToList H₁ H₂ H₃ i := (h_Gl'_other_iso' i).some
        let f_iso₂ : labeledGraphTripleToList H₁ H₂ H₃ i ≃f Hl i := iso_Hl i
        exact Nonempty.intro (f_iso₁.trans f_iso₂)
      have h_Vl_card : ∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀ := by
        intro i
        exact labeledSubgraph_card_from_iso G (Gl' i) (Hl i) (h_Gl'_other_iso i)
      have h_Vl_iso : ∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)) := by
        intro i
        exact inducedLabeledSubgraph_iso_from_iso (h_Gl'_ind i) (h_Gl'_other_iso i)
      have h_Vl_disj_G_type_verts : ∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅ := by
        intro i
        dsimp [Vl]
        exact Set.diff_inter_self
      have h_Vl_disj_pairwise : Set.univ.PairwiseDisjoint Vl := by
        intro i _ j _ h_ij_neq
        exact Set.disjoint_iff_inter_eq_empty.mpr (h_Gl'_other_disj i j h_ij_neq)
      exact ⟨⟨X, Vl⟩,
        h_X_card, (by intro i; rw [←h_Vl_card i]; congr!),
        h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    have h_f_S₀_S₁_inj : Function.Injective f_S₀_S₁_fwd := by
      intro ⟨⟨X₀, Gl'₀⟩, h_X₀_card, h_Gl'₀_ind, h_Gl'₀_other⟩
        ⟨⟨X₁, Gl'₁⟩, h_X₁_card, h_Gl'₁_ind, h_Gl'₁_other⟩
        h_eq
      dsimp [f_S₀_S₁_fwd] at h_eq
      split at h_eq
      split at h_eq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h_eq
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      obtain ⟨_, h_eq_Gl_verts⟩ := h_eq
      funext i
      have h_eq_verts : (Gl'₀ i).subgraph.verts = (Gl'₁ i).subgraph.verts :=
        calc
          (Gl'₀ i).subgraph.verts
          _ = ((Gl'₀ i).subgraph.verts \ G.type_verts) ∪ G.type_verts := by
              exact (Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl'₀ i))).symm
          _ = ((fun j ↦ ((Gl'₀ j).subgraph.verts \ G.type_verts)) i) ∪ G.type_verts := by
              rfl
          _ = ((fun j ↦ ((Gl'₁ j).subgraph.verts \ G.type_verts)) i) ∪ G.type_verts := by
              rw [h_eq_Gl_verts]
          _ = (Gl'₁ i).subgraph.verts \ G.type_verts ∪ G.type_verts := by
              rfl
          _ = (Gl'₁ i).subgraph.verts := by
              exact (Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl'₁ i)))
      rw [inducedLabeledSubgraph_eq (h_Gl'₀_ind i)]
      rw [inducedLabeledSubgraph_eq (h_Gl'₁_ind i)]
      congr!

    have h_f_S₀_S₁_surj : Function.Surjective f_S₀_S₁_fwd := by
      intro ⟨⟨X, Vl⟩, h_X_card, h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩
      let Gl (i : Fin 3) := inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right
      have h_Gl_ind : ∀ i : Fin 3, (Gl i).IsInduced := by
        intro i
        exact inducedLabeledSubgraph_isInduced G ((Vl i) ∪ G.type_verts) Set.subset_union_right
      have h_Gl_other_iso : ∀ (i : Fin 3), Nonempty ((Gl i).coe ≃f labeledGraphTripleToList H₁ H₂ H₃ i) := by
        intro i
        let f_iso₁ : (Gl i).coe ≃f Hl i := (h_Vl_iso i).some
        let f_iso₂ : Hl i ≃f labeledGraphTripleToList H₁ H₂ H₃ i := (iso_Hl i).symm
        exact Nonempty.intro (f_iso₁.trans f_iso₂)
      have h_Gl_other_disj : predDisjointLabeledSubgraphList Gl := by
        dsimp [predDisjointLabeledSubgraphList]
        intro i j h_neq
        rw [inducedLabeledSubgraph_verts G ((Vl i) ∪ G.type_verts) Set.subset_union_right]
        rw [inducedLabeledSubgraph_verts G ((Vl j) ∪ G.type_verts) Set.subset_union_right]
        simp only [Set.union_diff_right]
        rw [←Set.diff_inter_distrib_right G.type_verts (Vl i) (Vl j)]
        suffices Vl i ∩ Vl j = ∅ by simp only [this, Set.empty_diff]
        exact Disjoint.inter_eq (h_Vl_disj_pairwise trivial trivial h_neq)
      use ⟨⟨X, Gl⟩, h_X_card, h_Gl_ind, ⟨h_Gl_other_iso, h_Gl_other_disj⟩⟩
      dsimp [f_S₀_S₁_fwd]
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      funext i
      rw [inducedLabeledSubgraph_verts G ((Vl i) ∪ G.type_verts) Set.subset_union_right]
      apply Set.union_diff_cancel_right
      simp only [h_Vl_disj_G_type_verts i, subset_refl]

    Equiv.ofBijective f_S₀_S₁_fwd ⟨h_f_S₀_S₁_inj, h_f_S₀_S₁_surj⟩

  f_LHS_S₀.trans f_S₀_S₁

/-- Chain-rule bijection, step 1: replace the abstract `Fin ℓ_other` powerset
choice by an actual subset `V` of the host's leftover vertices. -/
noncomputable def
  powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step1
    (ℓ' : ℕ) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    (ℓ_other : ℕ) (h_ℓ_other : ℓ_other =  (ℓ - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀) - (ℓ₃ - ℓ₀))
    (ℓ'_other : ℕ)
    (Hl_size : Fin 3 → ℕ) (h_Hl_size : Hl_size 0 = ℓ₁ ∧ Hl_size 1 = ℓ₂ ∧ Hl_size 2 = ℓ₃)
    (Hl : (i : Fin 3) → LabeledGraph σ (Fin (Hl_size i)))
    : { ⟨X, Vl⟩ : Finset (Fin ℓ_other) × (Fin 3 → Set (Fin ℓ))
                | X.card = ℓ'_other
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }
      ≃
      { ⟨V, Vl⟩ : Set (Fin ℓ) × (Fin 3 → Set (Fin ℓ))
                | V.toFinset.card = ℓ'_other
                ∧ (∀ i : Fin 3, V ∩ (Vl i) = ∅)
                ∧ V ∩ G.type_verts = ∅
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }
  :=
  let LHS := { ⟨X, Vl⟩ : Finset (Fin ℓ_other) × (Fin 3 → Set (Fin ℓ))
                | X.card = ℓ'_other
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }
  let RHS := { ⟨V, Vl⟩ : Set (Fin ℓ) × (Fin 3 → Set (Fin ℓ))
                | V.toFinset.card = ℓ'_other
                ∧ (∀ i : Fin 3, V ∩ (Vl i) = ∅)
                ∧ V ∩ G.type_verts = ∅
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }

  let ⟨h_Hl_size₀, h_Hl_size₁, h_Hl_size₂⟩ := h_Hl_size

  have h_G_type_verts_card_eq_ℓ₀ : Fintype.card ↑G.type_verts = ℓ₀ := by
    simp only [G.type_verts_card_eq]
    dsimp [FlagType.size]
    exact Fintype.card_fin ℓ₀

  have h_V_other_properties :
      ∀ (Vl : Fin 3 → Set (Fin ℓ)),
      ∀ (V_other : Set (Fin ℓ)),
          (h_V_other : V_other = ((⋃ i, Vl i) ∪ G.type_verts)ᶜ)
        → (h_Vl_card : ∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
        → (h_Vl_disj_G_type_verts : ∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
        → (h_Vl_disj_pairwise : Set.univ.PairwiseDisjoint Vl)
        → (V_other.toFinset.card = ℓ_other ∧ V_other ∩ G.type_verts = ∅ ∧ ∀ (i : Fin 3), V_other ∩ Vl i = ∅)
    := by
    intro Vl V_other h_V_other h_Vl_card h_Vl_disj_G_type_verts h_Vl_disj_pairwise
    let unionVl := ⋃ i, Vl i
    have h_unionVl_disj : unionVl ∩ G.type_verts = ∅ := by
      rw [Set.iUnion_inter G.type_verts Vl]
      rw [Set.iUnion_congr h_Vl_disj_G_type_verts]
      exact Set.iUnion_empty
    have h_unionVl_card : unionVl.toFinset.card = (ℓ₁ - ℓ₀) + (ℓ₂ - ℓ₀) + (ℓ₃ - ℓ₀) :=
      calc
        unionVl.toFinset.card
        _ = (Finset.univ.biUnion fun x ↦ (Vl x).toFinset).card := by
              rw [Set.toFinset_iUnion Vl]
        _ = ∑ i : Fin 3, (Vl i).toFinset.card := by
              apply Finset.card_biUnion
              intro i h_i j h_j h_neq
              simp only [Set.disjoint_toFinset]
              have := Set.PairwiseDisjoint.eq_or_disjoint h_Vl_disj_pairwise (Set.mem_univ i) (Set.mem_univ j)
              simp_all only [Set.toFinset_card, Finset.coe_univ, Set.mem_univ, ne_eq, false_or]
        _ = ∑ i : Fin 3, (Hl_size i - ℓ₀) := by
              apply Finset.sum_congr rfl
              intro i _
              exact h_Vl_card i
        _ = (ℓ₁ - ℓ₀) + (ℓ₂ - ℓ₀) + (ℓ₃ - ℓ₀) := by
              simp only [Fin.sum_univ_three, h_Hl_size₁, h_Hl_size₂, h_Hl_size₀]

    have h_V_other_card : V_other.toFinset.card = ℓ_other :=
      calc
        V_other.toFinset.card
        _ = (unionVl.toFinset ∪ G.type_verts.toFinset)ᶜ.card := by
                rw [h_V_other]; dsimp [unionVl]; simp only [Set.toFinset_compl, Set.toFinset_union]
        _ = ℓ - (unionVl.toFinset ∪ G.type_verts.toFinset).card := by
                rw [Finset.card_compl (unionVl.toFinset ∪ G.type_verts.toFinset)]
                rw [Fintype.card_fin]
        _ = ℓ - (unionVl.toFinset.card + G.type_verts.toFinset.card) := by
                have : Disjoint unionVl.toFinset G.type_verts.toFinset := by
                  suffices Disjoint unionVl G.type_verts by exact Set.disjoint_toFinset.mpr this
                  apply Set.disjoint_iff_inter_eq_empty.mpr h_unionVl_disj
                rw [Finset.card_union_of_disjoint this]
        _ = ℓ - ((ℓ₁ - ℓ₀) + (ℓ₂ - ℓ₀) + (ℓ₃ - ℓ₀) + ℓ₀) := by
                rw [h_unionVl_card]
                rw [Set.toFinset_card G.type_verts]
                rw [h_G_type_verts_card_eq_ℓ₀]
        _ = ℓ_other := by
                omega
    have h_V_other_disj_G_type_verts : V_other ∩ G.type_verts = ∅ := by
      rw [h_V_other]
      simp only [Set.compl_union]
      rw [Set.inter_assoc, Set.compl_inter_self]
      exact Set.inter_empty _
    have h_V_other_disj_Vl : ∀ (i : Fin 3), V_other ∩ Vl i = ∅ := by
      intro i
      rw [h_V_other]
      rw [Set.compl_union (⋃ i, Vl i) G.type_verts]
      rw [Set.inter_comm (⋃ i, Vl i)ᶜ G.type_vertsᶜ]
      rw [Set.inter_assoc]
      have : (⋃ i, Vl i)ᶜ ∩ (Vl i) = ∅ := by
        refine Set.subset_eq_empty ?_ rfl
        have h₀ : (⋃ i, Vl i)ᶜ ⊆ (Vl i)ᶜ := Set.compl_subset_compl.mpr (Set.subset_iUnion Vl i)
        calc
          (⋃ i, Vl i)ᶜ ∩ (Vl i) ⊆ (Vl i)ᶜ ∩ (Vl i) := Set.inter_subset_inter_left (Vl i) h₀
          _ = ∅ := Set.compl_inter_self (Vl i)
      rw [this]
      exact Set.inter_empty _
    exact ⟨h_V_other_card, h_V_other_disj_G_type_verts, h_V_other_disj_Vl⟩

  let f_LHS_RHS_fwd : LHS → RHS := by
    intro ⟨⟨X, Vl⟩, h_X_card, h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    let V_other := ((⋃ i, Vl i) ∪ G.type_verts)ᶜ
    have h_V_other := h_V_other_properties Vl V_other rfl h_Vl_card h_Vl_disj_G_type_verts h_Vl_disj_pairwise
    have h_V_other_card : V_other.toFinset.card = ℓ_other := by rw [←h_V_other.1]; congr!
    have h_V_other_disj_G_type_verts : V_other ∩ G.type_verts = ∅ := h_V_other.2.1
    have h_V_other_disj_Vl : ∀ (i : Fin 3), V_other ∩ Vl i = ∅ := h_V_other.2.2
    let f_V_other : Fin ℓ_other ≃ V_other := isoFromFinToFiniteSet V_other (by rw [←h_V_other_card]; congr!)

    let V : Set (Fin ℓ) := Subtype.val '' (f_V_other '' SetLike.coe X)
    have h_V_subset_V_other : V ⊆ V_other := by
      dsimp [V]
      simp only [Set.image_subset_iff, Subtype.coe_preimage_self, Set.subset_univ]
    have h_V_card : V.toFinset.card = ℓ'_other := by
      dsimp [V]
      rw [Set.toFinset_image, Set.toFinset_image]
      rw [Finset.card_image_of_injective _ (Subtype.val_injective)]
      rw [Finset.card_image_of_injective _ (Equiv.injective _)]
      rw [Finset.toFinset_coe]
      exact h_X_card
    have h_V_disj_Vl : ∀ (i : Fin 3), V ∩ Vl i = ∅ := by
      intro i
      suffices V ∩ Vl i ⊆ ∅ by exact Set.subset_eq_empty this rfl
      rw [←h_V_other_disj_Vl i]
      exact Set.inter_subset_inter_left (Vl i) h_V_subset_V_other
    have h_V_disj_G_type_verts : V ∩ G.type_verts = ∅ := by
      suffices V ∩ G.type_verts ⊆ ∅ by exact Set.subset_eq_empty this rfl
      rw [←h_V_other_disj_G_type_verts]
      exact Set.inter_subset_inter_left G.type_verts h_V_subset_V_other

    exact ⟨⟨V, Vl⟩,
      (by rw [←h_V_card]; congr!), h_V_disj_Vl, h_V_disj_G_type_verts,
      h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

  have h_f_LHS_RHS_inj : Function.Injective f_LHS_RHS_fwd := by
    intro ⟨⟨X₁, Vl₁⟩, h_X₁_card, h_Vl₁_card, h_Vl₁_iso, h_Vl₁_disj_G_type_verts, h_Vl₁_disj_pairwise⟩
      ⟨⟨X₂, Vl₂⟩, h_X₂_card, h_Vl₂_card, h_Vl₂_iso, h_Vl₂_disj_G_type_verts, h_Vl₂_disj_pairwise⟩
      h_eq
    simp only [Subtype.mk.injEq, Prod.mk.injEq, f_LHS_RHS_fwd] at h_eq
    have ⟨h_eq_X, h_eq_Vl⟩ := h_eq
    subst h_eq_Vl
    simp only [Set.image_val_inj, Equiv.image_eq_iff_eq, Finset.coe_inj] at h_eq_X
    subst h_eq_X
    rfl

  have h_f_LHS_RHS_surj : Function.Surjective f_LHS_RHS_fwd := by
    intro ⟨⟨V, Vl⟩,
      h_V_card, h_V_disj_Vl, h_V_disj_G_type_verts,
      h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    let V_other := (Set.iUnion Vl ∪ G.type_verts)ᶜ
    have h_V_other := h_V_other_properties Vl V_other rfl h_Vl_card h_Vl_disj_G_type_verts h_Vl_disj_pairwise
    have h_V_other_card : V_other.toFinset.card = ℓ_other := by rw [←h_V_other.1]; congr!
    have h_V_other_disj_G_type_verts : V_other ∩ G.type_verts = ∅ := h_V_other.2.1
    have h_V_other_disj_Vl : ∀ (i : Fin 3), V_other ∩ Vl i = ∅ := h_V_other.2.2
    have h_V_subseteq_V_other : V ⊆ V_other := by
      dsimp [V_other]
      rw [Set.subset_compl_iff_disjoint_right]
      rw [Set.disjoint_iff_inter_eq_empty]
      rw [Set.inter_union_distrib_left V (Set.iUnion Vl) G.type_verts]
      simp only [h_V_disj_G_type_verts, Set.union_empty]
      rw [Set.inter_iUnion]
      exact Set.iUnion_eq_empty.mpr h_V_disj_Vl
    let f_V_other : Fin ℓ_other ≃ V_other := isoFromFinToFiniteSet V_other (by rw [←h_V_other_card]; congr!)

    let X_set := f_V_other.symm '' {v : V_other | v.val ∈ V}
    let X : Finset (Fin ℓ_other) := X_set.toFinset
    have h_V_card' : V.toFinset.card = {v : V_other | v.val ∈ V}.toFinset.card :=
      calc
        V.toFinset.card = ((V_other ∩ V) : Set (Fin ℓ)).toFinset.card := by
              congr!; simp only [Set.right_eq_inter, h_V_subseteq_V_other]
        _ = {v : V_other | v.val ∈ V}.toFinset.card := by
              have : ((V_other ∩ V) : Set (Fin ℓ)) = {v : V_other | v.val ∈ V} := by
                ext x
                simp only [Set.mem_inter_iff, and_comm, Set.mem_image,
                  Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop, exists_eq_left]
              simp only [this, Set.toFinset_image, Set.toFinset_setOf]
              refine Finset.card_image_iff.mpr ?_
              simp only [Finset.coe_filter, Finset.mem_univ, true_and,
                Subtype.forall, Subtype.mk.injEq, implies_true, Set.injOn_of_eq_iff_eq]
    have h_X_card : X.card = ℓ'_other := by
      dsimp [X, X_set]
      rw [←h_V_card]
      simp only [h_V_card', Set.toFinset_setOf]
      rw [Set.toFinset_card]
      rw [Set.card_image_of_injective _ (Equiv.injective _)]
      rw [←Set.toFinset_card]
      simp only [Set.toFinset_setOf]
    use ⟨⟨X, Vl⟩, h_X_card, h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩
    dsimp [f_LHS_RHS_fwd, X, X_set, f_V_other]
    simp_all only [Set.toFinset_card, Fintype.card_ofFinset,
      Set.toFinset_setOf, Set.toFinset_image, Finset.coe_image, Finset.coe_filter,
      Finset.mem_univ, true_and, Subtype.mk.injEq, Prod.mk.injEq, and_true]
    simp only [Equiv.image_symm_image, V_other]
    exact Subtype.coe_image_of_subset h_V_subseteq_V_other

  Equiv.ofBijective f_LHS_RHS_fwd ⟨h_f_LHS_RHS_inj, h_f_LHS_RHS_surj⟩

/-- Chain-rule bijection, step 2: assemble the intermediate flag `G'` of size `ℓ'`
from the chosen vertices and re-split the data as vertex-set pairs in `G'` and `G`. -/
noncomputable def
  powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step2
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    (ℓ'_other : ℕ) (h_ℓ'_other : ℓ'_other = (ℓ' - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀))
    (Hl_size : Fin 3 → ℕ) (h_Hl_size : Hl_size 0 = ℓ₁ ∧ Hl_size 1 = ℓ₂ ∧ Hl_size 2 = ℓ₃)
    (Hl : (i : Fin 3) → LabeledGraph σ (Fin (Hl_size i))) (h_Hl : Hl 0 ≍ H₁ ∧ Hl 1 ≍ H₂ ∧ Hl 2 ≍ H₃)
    : { ⟨V, Vl⟩ : Set (Fin ℓ) × (Fin 3 → Set (Fin ℓ))
                | V.toFinset.card = ℓ'_other
                ∧ (∀ i : Fin 3, V ∩ (Vl i) = ∅)
                ∧ V ∩ G.type_verts = ∅
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }
      ≃
      { ⟨G', Vl', Vl''⟩ : Flag σ (Fin ℓ') × (Fin 2 → Set (Fin ℓ')) × (Fin 2 → Set (Fin ℓ))
                | (∀ i : Fin 2, (Vl' i) ∩ G'.out.type_verts = ∅)
                ∧ (∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl'
                ∧ Set.univ.PairwiseDisjoint Vl''
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i))
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [G'.out, H₃]ᵍ i)) }
  :=
  let LHS := { ⟨V, Vl⟩ : Set (Fin ℓ) × (Fin 3 → Set (Fin ℓ))
                | V.toFinset.card = ℓ'_other
                ∧ (∀ i : Fin 3, V ∩ (Vl i) = ∅)
                ∧ V ∩ G.type_verts = ∅
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }

  let RHS := { ⟨G', Vl', Vl''⟩ : Flag σ (Fin ℓ') × (Fin 2 → Set (Fin ℓ')) × (Fin 2 → Set (Fin ℓ))
                | (∀ i : Fin 2, (Vl' i) ∩ G'.out.type_verts = ∅)
                ∧ (∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl'
                ∧ Set.univ.PairwiseDisjoint Vl''
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i))
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [G'.out, H₃]ᵍ i)) }

  let ⟨h_Hl_size₀, h_Hl_size₁, h_Hl_size₂⟩ := h_Hl_size

  let ⟨h_Hl₀, h_Hl₁, h_Hl₂⟩ := h_Hl
  let iso_Hl₀ : Hl 0 ≃f H₁ := by
    subst h_Hl_size₀
    simp only [Fin.isValue, heq_eq_eq] at h_Hl₀
    rw [h_Hl₀]
  let iso_Hl₁ : Hl 1 ≃f H₂ := by
    subst h_Hl_size₁
    simp only [Fin.isValue, heq_eq_eq] at h_Hl₁
    rw [h_Hl₁]
  let iso_Hl₂ : Hl 2 ≃f H₃ := by
    subst h_Hl_size₂
    simp only [Fin.isValue, heq_eq_eq] at h_Hl₂
    rw [h_Hl₂]

  have h_G_type_verts_card_eq_ℓ₀ : Fintype.card ↑G.type_verts = ℓ₀ := by
    simp only [G.type_verts_card_eq]
    dsimp [FlagType.size]
    exact Fintype.card_fin ℓ₀

  have h_card_Vl_01_V_type_vert_eq_ℓ' :
      ∀ s : LHS, (s.1.2 0 ∪ s.1.2 1 ∪ s.1.1 ∪ G.type_verts).toFinset.card = ℓ'
    := by
    intro ⟨⟨V, Vl⟩,
      h_V_card, h_V_disj_Vl, h_V_disj_G_type_verts,
      h_Vl_card, _, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    calc
      (Vl 0 ∪ Vl 1 ∪ V ∪ G.type_verts).toFinset.card
      _ = ((Vl 0).toFinset ∪ (Vl 1).toFinset ∪ V.toFinset ∪ G.type_verts.toFinset).card := by
              repeat rw [Set.toFinset_union]
      _ = (Vl 0).toFinset.card + (Vl 1).toFinset.card + V.toFinset.card + G.type_verts.toFinset.card := by
              have h_disj_0_1 : Disjoint (Vl 0).toFinset (Vl 1).toFinset :=
                Set.disjoint_toFinset.mpr
                  (h_Vl_disj_pairwise (Set.mem_univ 0) (Set.mem_univ 1) (by omega))
              rw [←Finset.card_union_of_disjoint h_disj_0_1]
              have h_disj_01_V : Disjoint ((Vl 0).toFinset ∪ (Vl 1).toFinset) V.toFinset := by
                rw [Finset.disjoint_union_left]
                constructor <;> {
                  rw [Set.disjoint_toFinset, Set.disjoint_iff, Set.inter_comm]
                  simp only [Fin.isValue, h_V_disj_Vl, subset_refl] }
              rw [←Finset.card_union_of_disjoint h_disj_01_V]
              have h_disj_01V_G : Disjoint ((Vl 0).toFinset ∪ (Vl 1).toFinset ∪ V.toFinset) G.type_verts.toFinset := by
                repeat rw [Finset.disjoint_union_left]
                (repeat constructor) <;> {
                  rw [Set.disjoint_toFinset, Set.disjoint_iff]
                  simp only [Fin.isValue, h_Vl_disj_G_type_verts, h_V_disj_G_type_verts, subset_refl] }
              rw [←Finset.card_union_of_disjoint h_disj_01V_G]
      _ = (Hl_size 0 - ℓ₀) + (Hl_size 1 - ℓ₀) + ℓ'_other + ℓ₀ := by
              rw [h_V_card, h_Vl_card 0, h_Vl_card 1]
              simp only [Fin.isValue, Set.toFinset_card, Nat.add_left_cancel_iff]
              exact h_G_type_verts_card_eq_ℓ₀
      _ = ℓ' := by
              rw [h_Hl_size₀, h_Hl_size₁]; omega

  let f_LHS_RHS_fwd : LHS → RHS := by
    intro ⟨⟨V, Vl⟩,
      h_V_card, h_V_disj_Vl, h_V_disj_G_type_verts,
      h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    let V' := Vl 0 ∪ Vl 1 ∪ V
    let V'_type_verts := V' ∪ G.type_verts
    have h_V'_type_verts_card : V'_type_verts.toFinset.card = ℓ' :=
      h_card_Vl_01_V_type_vert_eq_ℓ' ⟨⟨V, Vl⟩,
        h_V_card, h_V_disj_Vl, h_V_disj_G_type_verts,
        h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    let G₀ := inducedLabeledSubgraph G V'_type_verts Set.subset_union_right
    let h_G₀_ind : G₀.IsInduced := inducedLabeledSubgraph_isInduced G V'_type_verts Set.subset_union_right
    have h_G₀_verts : G₀.subgraph.verts = V'_type_verts :=
      inducedLabeledSubgraph_verts G V'_type_verts Set.subset_union_right
    let ⟨F, iso⟩ : (F : Flag σ (Fin ℓ')) × (F.out ≃f G₀.coe) :=
      have : Fintype.card ↑G₀.subgraph.verts = ℓ' := by
        rw [←h_V'_type_verts_card]
        rw [inducedLabeledSubgraph_verts G V'_type_verts Set.subset_union_right]
        rw [Set.toFinset_card V'_type_verts]
        congr!
      ⟨getCanonicalFlag G₀.coe this, getCanonicalFlag_iso G₀.coe this⟩

    let Vl' (i : Fin 2) := iso.graph_iso.symm '' { v | v.val ∈ Vl ⟨i.val, by omega⟩ }
    let Vl'' (i : Fin 2) := match i with | 0 => V' | 1 => Vl 2

    have h_Vl'_disj_type_verts : ∀ i : Fin 2, (Vl' i) ∩ F.out.type_verts = ∅ := by
      intro i
      calc
        (Vl' i) ∩ F.out.type_verts
        _ = (iso.graph_iso.symm '' { v | v.val ∈ Vl ⟨i.val, by omega⟩ })
            ∩ F.out.type_verts := by rfl
        _ = (iso.graph_iso.symm '' { v | v.val ∈ Vl ⟨i.val, by omega⟩ })
            ∩ (iso.graph_iso.symm '' (iso.graph_iso '' F.out.type_verts)) := by
                have : iso.graph_iso.symm '' (iso.graph_iso '' F.out.type_verts) = F.out.type_verts := by
                  exact Equiv.symm_image_image _ F.out.type_verts
                rw [this]
        _ = iso.graph_iso.symm '' ({ v | v.val ∈ Vl ⟨i.val, by omega⟩ } ∩ (iso.graph_iso '' F.out.type_verts)) := by
                rw [Set.image_inter iso.graph_iso.symm.injective]
        _ = iso.graph_iso.symm '' ({ v | v.val ∈ Vl ⟨i.val, by omega⟩ } ∩ { v | v.val ∈ G.type_verts }) := by
                rw [←labeledGraphIso_preserve_type_verts_strict iso]
                have : G₀.coe.type_verts = {v : G₀.subgraph.verts | ↑v ∈ G.type_verts } := by
                  rw [←G₀.coe_type_verts_eq]
                  ext u
                  simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
                    Subtype.coe_eta, Subtype.coe_prop, exists_const, Set.setOf_mem_eq]
                rw [this]
        _ = iso.graph_iso.symm '' {v | v.val ∈ Vl ⟨i.val, by omega⟩ ∩ G.type_verts} :=
                rfl
        _ = iso.graph_iso.symm '' ∅ := by
                rw [h_Vl_disj_G_type_verts ⟨i.val, by omega⟩]
                simp only [coe_graph, Set.mem_empty_iff_false, Set.setOf_false, Set.image_empty]
        _ = ∅ := Set.image_empty _

    have h_Vl''_disj_type_verts : ∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅ := by
      intro i
      dsimp [Vl'']
      split
      · dsimp [V']
        rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right]
        rw [h_Vl_disj_G_type_verts 0, h_Vl_disj_G_type_verts 1, h_V_disj_G_type_verts]
        simp only [Set.union_empty]
      · exact h_Vl_disj_G_type_verts 2

    have h_Vl'_disj_pairwise : Set.univ.PairwiseDisjoint Vl' := by
      intro i _ j _ h_neq_ij
      simp only [Set.disjoint_iff_inter_eq_empty]
      dsimp [Vl']
      rw [←Set.image_inter iso.graph_iso.symm.injective]
      rw [Set.image_eq_empty]
      have h_Vl_ij : Vl ⟨i.val, by omega⟩ ∩ Vl ⟨j.val, by omega⟩ = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp
          (h_Vl_disj_pairwise
            (Set.mem_univ ⟨i.val, _⟩)
            (Set.mem_univ ⟨j.val, _⟩)
            (by simp only [ne_eq, Fin.mk.injEq]; omega))
      rw [←Set.subset_empty_iff]
      intro v h_v
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at h_v
      rw [←Set.mem_inter_iff _ _ _] at h_v
      rw [h_Vl_ij] at h_v
      simp_all only [Set.toFinset_card,
        Fintype.card_ofFinset, Fin.isValue, Set.mem_univ,
        ne_eq, Set.mem_empty_iff_false]

    have h_Vl''_disj_pairwise : Set.univ.PairwiseDisjoint Vl'' := by
      intro i _ j _ h_neq_ij
      simp only [Set.disjoint_iff_inter_eq_empty]
      dsimp [Vl'', V']
      have h_disj : (Vl 0 ∪ Vl 1 ∪ V) ∩ (Vl 2) = ∅ := by
        rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right]
        simp only [h_V_disj_Vl 2]
        simp only [Set.disjoint_iff_inter_eq_empty.mp
                      (h_Vl_disj_pairwise (Set.mem_univ 0) (Set.mem_univ 2) (by omega))]
        simp only [Set.disjoint_iff_inter_eq_empty.mp
                      (h_Vl_disj_pairwise (Set.mem_univ 1) (Set.mem_univ 2) (by omega))]
        simp only [Set.union_self]
      have h_disj_symm : (Vl 2) ∩ (Vl 0 ∪ Vl 1 ∪ V) = ∅ := by
        rw [Set.inter_comm]; exact h_disj
      split <;> split
            <;> simp_all only [Fin.isValue, Set.toFinset_union, Finset.union_assoc,
              Subtype.forall, Prod.forall, Set.toFinset_card, Fintype.card_ofFinset, Set.mem_univ,
              ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true]
    have h_Vl'_iso :
        ∀ i : Fin 2,
          Nonempty ((inducedLabeledSubgraph F.out (Vl' i ∪ F.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i)
      := by
      intro i
      let i' : Fin 3 := ⟨i.val, by omega⟩
      have h_Vl'_Vl_verts : ⇑iso.graph_iso '' (Vl' i) = Vl i' := by
        calc
          Subtype.val '' (⇑iso.graph_iso '' (Vl' i))
          _ = Subtype.val '' (⇑iso.graph_iso '' (iso.graph_iso.symm '' { v | v.val ∈ Vl i' })) := by rfl
          _ = Subtype.val '' { v : ↑G₀.subgraph.verts | v.val ∈ Vl i' } := by apply congrArg _ (Equiv.image_symm_image _ _)
          _ = Vl i' := by
                ext v
                simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, h_G₀_verts,
                  Fin.isValue, Set.mem_union, exists_and_left, exists_prop, exists_eq_right_right,
                  and_iff_left_iff_imp, V'_type_verts, V']
                dsimp [i']
                have : i = 0 ∨ i = 1 := by omega
                cases this with
                | inl h_i₀ =>
                    rw [h_i₀]
                    intro h_v
                    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta] at h_v
                    simp only [Fin.isValue, h_v, true_or]
                | inr h_i₁ =>
                    rw [h_i₁]
                    intro h_v
                    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Fin.mk_one] at h_v
                    simp only [Fin.isValue, h_v, or_true, true_or]
      let f_iso₁ : (inducedLabeledSubgraph F.out (Vl' i ∪ F.out.type_verts) Set.subset_union_right).coe
                    ≃f (inducedLabeledSubgraph G (Vl i' ∪ G.type_verts) Set.subset_union_right).coe
        := labeledGraphIso_inducedLabeledSubgraph_from_labeledGraphEmbedding h_G₀_ind iso (Vl' i) (Vl i') h_Vl'_Vl_verts
      let f_iso₂ : (inducedLabeledSubgraph G (Vl i' ∪ G.type_verts) Set.subset_union_right).coe
                    ≃f Hl i'
        := (h_Vl_iso i').some
      let f_iso₃ : Hl i' ≃f [H₁, H₂]ᵍ i := by
        dsimp [labeledGraphPairToList, i']
        split
        . simp only [Fin.isValue]; exact iso_Hl₀
        . simp only [Fin.isValue]; exact iso_Hl₁
      exact Nonempty.intro (f_iso₁.trans (f_iso₂.trans f_iso₃))

    have h_Vl''_iso :
        ∀ i : Fin 2,
          Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [F.out, H₃]ᵍ i)
      := by
      intro i
      match i with
      | 0 =>
        dsimp [Vl'',labeledGraphPairToList]
        exact Nonempty.intro iso.symm
      | 1 =>
        dsimp [Vl'', labeledGraphPairToList]
        apply Nonempty.intro
        exact (h_Vl_iso 2).some.trans iso_Hl₂

    exact ⟨⟨F, Vl', Vl''⟩,
      h_Vl'_disj_type_verts, h_Vl''_disj_type_verts,
      h_Vl'_disj_pairwise, h_Vl''_disj_pairwise,
      h_Vl'_iso, h_Vl''_iso⟩

  have h_f_LHS_RHS_inj : Function.Injective f_LHS_RHS_fwd := by
    intro ⟨⟨V₁, Vl₁⟩,
      h_V₁_card, h_V₁_disj_Vl₁, h_V₁_disj_G_type_verts,
      h_Vl₁_card, h_Vl₁_iso, h_Vl₁_disj_G_type_verts, h_Vl₁_disj_pairwise⟩
      ⟨⟨V₂, Vl₂⟩,
      h_V₂_card, h_V₂_disj_Vl₂, h_V₂_disj_G_type_verts,
      h_Vl₂_card, h_Vl₂_iso, h_Vl₂_disj_G_type_verts, h_Vl₂_disj_pairwise⟩
      h_eq
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    dsimp [f_LHS_RHS_fwd] at h_eq
    simp only [Fin.isValue, Subtype.mk.injEq, Prod.mk.injEq] at h_eq
    obtain ⟨h_eq_F, h_eq_Vl', h_eq_Vl''⟩ := h_eq

    have h_Vl_01_V_eq : Vl₁ 0 ∪ Vl₁ 1 ∪ V₁ = Vl₂ 0 ∪ Vl₂ 1 ∪ V₂ := congr_fun h_eq_Vl'' 0
    let H₁ := inducedLabeledSubgraph G (Vl₁ 0 ∪ Vl₁ 1 ∪ V₁ ∪ G.type_verts) Set.subset_union_right
    let H₂ := inducedLabeledSubgraph G (Vl₂ 0 ∪ Vl₂ 1 ∪ V₂ ∪ G.type_verts) Set.subset_union_right
    have h_H₁_size : Fintype.card ↑H₁.subgraph.verts = ℓ' := by
      rw [inducedLabeledSubgraph_verts G (Vl₁ 0 ∪ Vl₁ 1 ∪ V₁ ∪ G.type_verts) Set.subset_union_right]
      have := h_card_Vl_01_V_type_vert_eq_ℓ' ⟨⟨V₁, Vl₁⟩,
                h_V₁_card, h_V₁_disj_Vl₁, h_V₁_disj_G_type_verts,
                h_Vl₁_card, h_Vl₁_iso, h_Vl₁_disj_G_type_verts, h_Vl₁_disj_pairwise⟩
      rw [←this]
      simp only [Set.toFinset_union, Fintype.card_ofFinset, Set.filter_mem_univ_eq_toFinset]
    have h_H₂_size : Fintype.card ↑H₂.subgraph.verts = ℓ' := by
      rw [inducedLabeledSubgraph_verts G (Vl₂ 0 ∪ Vl₂ 1 ∪ V₂ ∪ G.type_verts) Set.subset_union_right]
      have := h_card_Vl_01_V_type_vert_eq_ℓ' ⟨⟨V₂, Vl₂⟩,
                h_V₂_card, h_V₂_disj_Vl₂, h_V₂_disj_G_type_verts,
                h_Vl₂_card, h_Vl₂_iso, h_Vl₂_disj_G_type_verts, h_Vl₂_disj_pairwise⟩
      rw [←this]
      simp only [Set.toFinset_union, Fintype.card_ofFinset, Set.filter_mem_univ_eq_toFinset]
    have h_H₁_eq_H₂ : H₁ = H₂ := by dsimp [H₁,H₂]; rw [h_Vl_01_V_eq]

    have h_Vl_0_eq : Vl₁ 0 = Vl₂ 0 := by
      have h₀ := congr_fun h_eq_Vl' 0
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta] at h₀
      have h_Vl₁_0 : Vl₁ 0 ⊆ H₁.subgraph.verts := by
        rw [inducedLabeledSubgraph_verts G (Vl₁ 0 ∪ Vl₁ 1 ∪ V₁ ∪ G.type_verts) Set.subset_union_right]
        exact subset_trans Set.subset_union_left (subset_trans Set.subset_union_left Set.subset_union_left)
      have h_Vl₂_0 : Vl₂ 0 ⊆ H₂.subgraph.verts := by
        rw [inducedLabeledSubgraph_verts G (Vl₂ 0 ∪ Vl₂ 1 ∪ V₂ ∪ G.type_verts) Set.subset_union_right]
        exact subset_trans Set.subset_union_left (subset_trans Set.subset_union_left Set.subset_union_left)
      exact cancel_getCanonicalFlag_iso H₁ H₂ (Vl₁ 0) (Vl₂ 0) h_H₁_size h_H₂_size h_Vl₁_0 h_Vl₂_0 h_H₁_eq_H₂ h₀
    have h_Vl_1_eq : Vl₁ 1 = Vl₂ 1 := by
      have h₁ := congr_fun h_eq_Vl' 1
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Fin.mk_one] at h₁
      have h_Vl₁_1 : Vl₁ 1 ⊆ H₁.subgraph.verts := by
        rw [inducedLabeledSubgraph_verts G (Vl₁ 0 ∪ Vl₁ 1 ∪ V₁ ∪ G.type_verts) Set.subset_union_right]
        exact subset_trans Set.subset_union_right (subset_trans Set.subset_union_left Set.subset_union_left)
      have h_Vl₂_1 : Vl₂ 1 ⊆ H₂.subgraph.verts := by
        rw [inducedLabeledSubgraph_verts G (Vl₂ 0 ∪ Vl₂ 1 ∪ V₂ ∪ G.type_verts) Set.subset_union_right]
        exact subset_trans Set.subset_union_right (subset_trans Set.subset_union_left Set.subset_union_left)
      exact cancel_getCanonicalFlag_iso H₁ H₂ (Vl₁ 1) (Vl₂ 1) h_H₁_size h_H₂_size h_Vl₁_1 h_Vl₂_1 h_H₁_eq_H₂ h₁
    have h_Vl_2_eq : Vl₁ 2 = Vl₂ 2 :=
      congr_fun h_eq_Vl'' 1
    have h_V_eq : V₁ = V₂ :=
      have h_V₁_disj_Vl₁_01 : V₁ ∩ (Vl₁ 0 ∪ Vl₁ 1) ⊆ ∅ := by
        suffices V₁ ∩ Vl₁ 0 = ∅ ∧ V₁ ∩ Vl₁ 1 = ∅ by {
          obtain ⟨h₀, h₁⟩ := this
          rw [Set.inter_union_distrib_left V₁ (Vl₁ 0) (Vl₁ 1), h₀, h₁]
          simp only [Set.union_self, subset_refl]
        }
        simp [h_V₁_disj_Vl₁ 0, h_V₁_disj_Vl₁ 1]
      have h_V₂_disj_Vl₂_01 : V₂ ∩ (Vl₂ 0 ∪ Vl₂ 1) ⊆ ∅ := by
        suffices V₂ ∩ Vl₂ 0 = ∅ ∧ V₂ ∩ Vl₂ 1 = ∅ by {
          obtain ⟨h₀, h₁⟩ := this
          rw [Set.inter_union_distrib_left V₂ (Vl₂ 0) (Vl₂ 1), h₀, h₁]
          simp only [Set.union_self, subset_refl]
        }
        simp [h_V₂_disj_Vl₂ 0, h_V₂_disj_Vl₂ 1]
      calc V₁ = (V₁ ∪ (Vl₁ 0 ∪ Vl₁ 1)) \ (Vl₁ 0 ∪ Vl₁ 1) := by
                rw [Set.union_diff_cancel_right h_V₁_disj_Vl₁_01]
            _ = ((Vl₁ 0 ∪ Vl₁ 1) ∪ V₁) \ (Vl₁ 0 ∪ Vl₁ 1) := by
                simp only [Set.union_comm]
            _ = ((Vl₂ 0 ∪ Vl₂ 1) ∪ V₂) \ (Vl₂ 0 ∪ Vl₂ 1) := by
                rw [h_Vl_01_V_eq]
                rw [h_Vl_0_eq, h_Vl_1_eq]
            _ = (V₂ ∪ (Vl₂ 0 ∪ Vl₂ 1)) \ (Vl₂ 0 ∪ Vl₂ 1) := by
                simp only [Set.union_comm]
            _ = V₂ := by
                rw [Set.union_diff_cancel_right h_V₂_disj_Vl₂_01]
    have h_Vl_eq : Vl₁ = Vl₂ := by
      ext i v
      match i with
      | 0 => rw [h_Vl_0_eq]
      | 1 => rw [h_Vl_1_eq]
      | 2 => rw [h_Vl_2_eq]
    exact ⟨h_V_eq, h_Vl_eq⟩

  have h_f_LHS_RHS_surj : Function.Surjective f_LHS_RHS_fwd := by
    intro ⟨⟨F, Vl', Vl''⟩,
      h_Vl'_disj_type_verts, h_Vl''_disj_type_verts,
      h_Vl'_disj_pairwise, h_Vl''_disj_pairwise,
      h_Vl'_iso, h_Vl''_iso⟩

    have h_Vl''_0_union_type_G_verts_card : Fintype.card ↑(Vl'' 0 ∪ G.type_verts) = ℓ' := by
      let K := inducedLabeledSubgraph G (Vl'' 0 ∪ G.type_verts) Set.subset_union_right
      have iso : K.coe ≃f F.out := (h_Vl''_iso 0).some
      have h_K_size_eq_F_out_size := labeledGraphIso_size_eq K.coe F.out iso
      dsimp [LabeledGraph.size] at h_K_size_eq_F_out_size
      rw [inducedLabeledSubgraph_verts G (Vl'' 0 ∪ G.type_verts) Set.subset_union_right] at h_K_size_eq_F_out_size
      rw [Fintype.card_fin ℓ'] at h_K_size_eq_F_out_size
      rw [←h_K_size_eq_F_out_size]
      congr!
    have h_Vl''_0_card : (Vl'' 0).toFinset.card = ℓ' - ℓ₀ := by
      rw [←h_Vl''_0_union_type_G_verts_card]
      rw [Fintype.card_ofFinset]
      have : Disjoint (Vl'' 0).toFinset G.type_verts.toFinset :=
        Set.disjoint_toFinset.mpr (disjoint_iff.mpr (h_Vl''_disj_type_verts 0))
      rw [Finset.card_union_of_disjoint this]
      simp only [Fin.isValue, Set.toFinset_card, Fintype.card_ofFinset,
        h_G_type_verts_card_eq_ℓ₀, add_tsub_cancel_right]

    let G₀ := inducedLabeledSubgraph G (Vl'' 0 ∪ G.type_verts) Set.subset_union_right
    have h_G₀_ind : G₀.IsInduced := inducedLabeledSubgraph_isInduced G (Vl'' 0 ∪ G.type_verts) Set.subset_union_right
    have h_G₀_card : Fintype.card ↑G₀.subgraph.verts = ℓ' := by
        rw [inducedLabeledSubgraph_verts G (Vl'' 0 ∪ G.type_verts) Set.subset_union_right]
        rw [←h_Vl''_0_union_type_G_verts_card]
        congr!
    let F₀ : Flag σ (Fin ℓ') := getCanonicalFlag G₀.coe h_G₀_card
    let iso₀ : F₀.out ≃f G₀.coe := getCanonicalFlag_iso G₀.coe h_G₀_card

    have h_F_eq_F₀ : F = F₀ := by
      have h_F : ⟦F.out⟧ = F := Quotient.out_eq F
      have h_F₀ : ⟦F₀.out⟧ = F₀ := Quotient.out_eq F₀
      rw [←h_F, ←h_F₀]
      let f_F₀_out_iso_F_out := iso₀.trans (h_Vl''_iso 0).some
      dsimp [labeledGraphPairToList] at f_F₀_out_iso_F_out
      exact Quotient.sound (Nonempty.intro f_F₀_out_iso_F_out.symm)
    subst h_F_eq_F₀

    have h_disj_implies_disj :
        ∀ W W' : Set (Fin ℓ'),
          W ∩ W' = ∅ → (Subtype.val '' (iso₀.graph_iso '' W)) ∩ (Subtype.val '' (iso₀.graph_iso '' W')) = ∅
      := by
      intro W W' h_W_W'_disj
      rw [←Set.image_inter Subtype.val_injective]
      rw [←Set.image_inter iso₀.graph_iso.injective]
      rw [h_W_W'_disj]
      rw [Set.image_empty iso₀.graph_iso]
      rw [Set.image_empty Subtype.val]

    have h_image_F₀_type_verts_eq_G_type_verts :
        Subtype.val '' (iso₀.graph_iso '' F₀.out.type_verts) = G.type_verts
      := by
      rw [←labeledGraphIso_preserve_type_verts_strict iso₀]
      rw [coe_type_verts_eq G₀]

    have h_disj_F₀_type_verts_implies_disj_G_type_verts :
        ∀ W : Set (Fin ℓ'),
          W ∩ F₀.out.type_verts = ∅ → (Subtype.val '' (iso₀.graph_iso '' W)) ∩ G.type_verts = ∅
      := by
      intro W h_W_disj_type_verts
      have := h_disj_implies_disj W F₀.out.type_verts h_W_disj_type_verts
      rw [←this]
      rw [h_image_F₀_type_verts_eq_G_type_verts]

    have h_disj_F₀_type_verts_implies_subseteq_Vl''_0 :
        ∀ W : Set (Fin ℓ'), W ∩ F₀.out.type_verts = ∅ → Subtype.val '' (iso₀.graph_iso '' W) ⊆ Vl'' 0
      := by
      intro W h_W_disj_type_verts
      suffices  Subtype.val '' (iso₀.graph_iso '' W) ⊆ Vl'' 0 ∪ G.type_verts by {
        calc
          Subtype.val '' (iso₀.graph_iso '' W)
          _ ⊆ (Subtype.val '' (iso₀.graph_iso '' W)) ∩ (Vl'' 0 ∪ G.type_verts) := by
                simp only [coe_graph, Fin.isValue, Set.subset_inter_iff, subset_refl, this, and_self]
          _ = ((Subtype.val '' (iso₀.graph_iso '' W)) ∩ Vl'' 0) ∪ ((Subtype.val '' (iso₀.graph_iso '' W)) ∩ G.type_verts) := by
                rw [Set.inter_union_distrib_left _ _ _]
          _ ⊆ Vl'' 0 := by
                rw [h_disj_F₀_type_verts_implies_disj_G_type_verts W h_W_disj_type_verts]
                simp only [coe_graph, Fin.isValue, Set.union_empty, Set.inter_subset_right]
      }
      intro u h_u
      simp only [coe_graph, Set.mem_image, exists_exists_and_eq_and] at h_u
      obtain ⟨w, h_w, h_w_u⟩ := h_u
      rw [←h_w_u]
      simp only [Fin.isValue, Subtype.coe_prop]

    have h_image_Vl'_01_subseteq_Vl''_0 :
        Subtype.val '' (iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (iso₀.graph_iso '' Vl' 1) ⊆ Vl'' 0
      := by
      rw [Set.union_subset_iff]
      constructor
      . exact h_disj_F₀_type_verts_implies_subseteq_Vl''_0 (Vl' 0) (h_Vl'_disj_type_verts 0)
      . exact h_disj_F₀_type_verts_implies_subseteq_Vl''_0 (Vl' 1) (h_Vl'_disj_type_verts 1)

    let U₀ := Subtype.val '' (iso₀.graph_iso '' Vl' 0)
              ∪ Subtype.val '' (iso₀.graph_iso '' Vl' 1)
              ∪ Vl'' 0 \ (Subtype.val '' (iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (iso₀.graph_iso '' Vl' 1))
    have h_U₀_eq_Vl''_0 : U₀ = Vl'' 0 := by
      dsimp [U₀]
      rw [Set.union_diff_self]
      exact Set.union_eq_right.mpr h_image_Vl'_01_subseteq_Vl''_0
    have h_ind_U₀_eq_G₀ : inducedLabeledSubgraph G (U₀ ∪ G.type_verts) Set.subset_union_right = G₀ := by
      rw [h_U₀_eq_Vl''_0]
    have h_iso₀_symm_comp_iso₀_eq_id :
        ∀ W : Set (Fin ℓ'),
          ⇑(getCanonicalFlag_iso G₀.coe h_G₀_card).graph_iso.symm '' {v : ↑G₀.subgraph.verts | ∃ a ∈ W, ↑(iso₀.graph_iso a) = ↑v} = W
        := by
        intro W
        have : getCanonicalFlag_iso G₀.coe h_G₀_card = iso₀ := by rfl
        rw [this]
        ext w
        simp_all only [Fin.isValue, Fintype.card_ofFinset, coe_graph, Set.union_subset_iff,
          Set.image_subset_iff, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and,
          RelIso.symm_apply_apply, exists_eq_right]
    let V := (Vl'' 0) \ (Subtype.val '' (iso₀.graph_iso '' (Vl' 0)) ∪ Subtype.val '' (iso₀.graph_iso '' (Vl' 1)))
    let Vl (i : Fin 3) : Set (Fin ℓ) :=
      match i with
      | 0 => Subtype.val '' (iso₀.graph_iso '' (Vl' 0))
      | 1 => Subtype.val '' (iso₀.graph_iso '' (Vl' 1))
      | 2 => Vl'' 1

    have h_image_Vl'_disj_Vl''_1 : ∀ i : Fin 2, Subtype.val '' (iso₀.graph_iso '' Vl' i) ∩ Vl'' 1 = ∅
      := by
      intro i
      apply Set.eq_empty_of_subset_empty
      calc
        (Subtype.val '' (iso₀.graph_iso '' Vl' i)) ∩ Vl'' 1
        _ ⊆ (Vl'' 0) ∩ Vl'' 1 := Set.inter_subset_inter_left _
                                    (Set.Subset.trans
                                      (match i with | 0 => Set.subset_union_left | 1 => Set.subset_union_right)
                                      h_image_Vl'_01_subseteq_Vl''_0)
        _ = ∅ := disjoint_iff.mp (h_Vl''_disj_pairwise (Set.mem_univ 0) (Set.mem_univ 1) (by omega))

    have h_V_disj_Vl : ∀ i : Fin 3, V ∩ (Vl i) = ∅ := by
      dsimp [V, Vl]
      intro i
      apply Set.eq_empty_of_subset_empty
      match i with
      | 0 =>
          simp only [Fin.isValue]
          calc
            (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1)))
                ∩ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0)
            _ ⊆
            (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1)))
                ∩ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1))
                  := Set.inter_subset_inter_right _ Set.subset_union_left
            _ = ∅
                  := Set.diff_inter_self
      | 1 =>
          simp only [Fin.isValue]
          calc
            (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1)))
                ∩ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1)
            _ ⊆
            (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1)))
                ∩ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1))
                  := Set.inter_subset_inter_right _ Set.subset_union_right
            _ = ∅
                  := Set.diff_inter_self
      | 2 =>
          simp only [Fin.isValue]
          calc
            (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1))) ∩ Vl'' 1
            _ ⊆ (Vl'' 0) ∩ (Vl'' 1) := Set.inter_subset_inter_left _ Set.diff_subset
            _ = ∅ := disjoint_iff.mp (h_Vl''_disj_pairwise (Set.mem_univ 0) (Set.mem_univ 1) (by omega))

    have h_V_disj_G_type_verts : V ∩ G.type_verts = ∅ := by
      dsimp [V]
      apply Set.eq_empty_of_subset_empty
      calc
        (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' Vl' 0) ∪ Subtype.val '' (⇑iso₀.graph_iso '' Vl' 1))) ∩ G.type_verts
        _ ⊆ Vl'' 0 ∩ G.type_verts := Set.inter_subset_inter_left G.type_verts Set.diff_subset
        _ = ∅ := h_Vl''_disj_type_verts 0

    have h_Vl_disj_G_type_verts : ∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅ := by
      intro i
      dsimp [Vl]
      match i with
      | 0 =>
          simp only [Fin.isValue]
          exact h_disj_F₀_type_verts_implies_disj_G_type_verts (Vl' 0) (h_Vl'_disj_type_verts 0)
      | 1 =>
          simp only [Fin.isValue]
          exact h_disj_F₀_type_verts_implies_disj_G_type_verts (Vl' 1) (h_Vl'_disj_type_verts 1)
      | 2 =>
          simp only [Fin.isValue]
          exact h_Vl''_disj_type_verts 1

    have h_Vl_disj_pairwise : Set.univ.PairwiseDisjoint Vl := by
      intro i _ j _ h_ij
      dsimp [Vl]
      apply disjoint_iff.mpr
      simp only [Fin.isValue, Set.inf_eq_inter, Set.bot_eq_empty]
      split <;> split <;> try contradiction
      . exact h_disj_implies_disj (Vl' 0) (Vl' 1)
                (disjoint_iff.mp (h_Vl'_disj_pairwise (Set.mem_univ 0) (Set.mem_univ 1) (by omega)))
      . exact (h_image_Vl'_disj_Vl''_1 0)
      . exact h_disj_implies_disj (Vl' 1) (Vl' 0)
                (disjoint_iff.mp (h_Vl'_disj_pairwise (Set.mem_univ 1) (Set.mem_univ 0) (by omega)))
      . exact (h_image_Vl'_disj_Vl''_1 1)
      . rw [Set.inter_comm _ _]; exact (h_image_Vl'_disj_Vl''_1 0)
      . rw [Set.inter_comm _ _]; exact (h_image_Vl'_disj_Vl''_1 1)

    have h_Vl_iso : ∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)) := by
      intro i
      dsimp [Vl]
      let K (i : Fin 2) := inducedLabeledSubgraph G
                              (Subtype.val '' (iso₀.graph_iso '' (Vl' i)) ∪ G.type_verts)
                              Set.subset_union_right
      have h_K_ind : ∀ i : Fin 2, (K i).IsInduced := by
        intro i
        exact inducedLabeledSubgraph_isInduced G
                (Subtype.val '' (iso₀.graph_iso '' (Vl' i)) ∪ G.type_verts)
                Set.subset_union_right
      let g (i : Fin 2) : (inducedLabeledSubgraph F₀.out (Vl' i ∪ F₀.out.type_verts) Set.subset_union_right).coe ≃f (K i).coe
        := labeledGraphIso_inducedLabeledSubgraph_from_labeledGraphEmbedding
              h_G₀_ind iso₀ (Vl' i) (Subtype.val '' (iso₀.graph_iso '' (Vl' i))) (by rfl)
      match i with
      | 0 => simp only [Fin.isValue]; exact Nonempty.intro ((g 0).symm.trans ((h_Vl'_iso 0).some.trans iso_Hl₀.symm))
      | 1 => simp only [Fin.isValue]; exact Nonempty.intro ((g 1).symm.trans ((h_Vl'_iso 1).some.trans iso_Hl₁.symm))
      | 2 => simp only [Fin.isValue]; exact Nonempty.intro ((h_Vl''_iso 1).some.trans iso_Hl₂.symm)

    have h_Vl_card : ∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀ := by
      intro i
      suffices (Vl i ∪ G.type_verts).toFinset.card = Hl_size i by {
          rw [Set.toFinset_union] at this
          rw [Finset.card_union_of_disjoint
                (Set.disjoint_toFinset.mpr (disjoint_iff.mpr (h_Vl_disj_G_type_verts i)))] at this
          rw [←this]
          simp only [Set.toFinset_card, Fintype.card_ofFinset, h_G_type_verts_card_eq_ℓ₀, add_tsub_cancel_right]
      }
      let K := inducedLabeledSubgraph G (Vl i ∪ G.type_verts) Set.subset_union_right
      have iso : K.coe ≃f Hl i := (h_Vl_iso i).some
      have h_K_size_eq_Hl_i_size := labeledGraphIso_size_eq K.coe (Hl i) iso
      dsimp [LabeledGraph.size] at h_K_size_eq_Hl_i_size
      rw [inducedLabeledSubgraph_verts G (Vl i ∪ G.type_verts) Set.subset_union_right] at h_K_size_eq_Hl_i_size
      rw [Fintype.card_fin (Hl_size i)] at h_K_size_eq_Hl_i_size
      rw [←h_K_size_eq_Hl_i_size]
      rw [Set.toFinset_card]
      congr!

    have h_V_card : V.toFinset.card = ℓ'_other := by
      dsimp [V]
      rw [h_ℓ'_other]
      calc
        (Vl'' 0 \ (Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 0)) ∪ Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 1)))).toFinset.card
        _ = ((Vl'' 0).toFinset \ (Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 0)) ∪ Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 1))).toFinset).card := by
                  rw [Set.toFinset_diff _ _]
        _ = (Vl'' 0).toFinset.card - (Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 0)) ∪ Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 1))).toFinset.card :=
                  Finset.card_sdiff_of_subset (Set.toFinset_mono h_image_Vl'_01_subseteq_Vl''_0)
        _ = (Vl'' 0).toFinset.card - ((Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 0))).toFinset.card
                                      + (Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 1))).toFinset.card) := by
                  rw [Set.toFinset_union _ _]
                  have h' := disjoint_iff.mpr
                                (h_disj_implies_disj (Vl' 0) (Vl' 1)
                                  (disjoint_iff.mp (h_Vl'_disj_pairwise (Set.mem_univ 0) (Set.mem_univ 1) (by omega))))
                  rw [Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h')]
        _ = ℓ' - ℓ₀ - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀) := by
                  rw [h_Vl''_0_card]
                  have h₀ : (Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 0))).toFinset.card = ℓ₁ - ℓ₀ := by
                    have h' := h_Vl_card 0
                    dsimp [Vl] at h'
                    rw [h_Hl_size₀] at h'
                    rw [←h']
                    congr!
                  have h₁ : (Subtype.val '' (⇑iso₀.graph_iso '' (Vl' 1))).toFinset.card = ℓ₂ - ℓ₀ := by
                    have h' := h_Vl_card 1
                    dsimp [Vl] at h'
                    rw [h_Hl_size₁] at h'
                    rw [←h']
                    congr!
                  rw [h₀,h₁]
                  omega

    use ⟨⟨V, Vl⟩,
      (by rw [←h_V_card]; congr!), h_V_disj_Vl, h_V_disj_G_type_verts,
      h_Vl_card, h_Vl_iso, h_Vl_disj_G_type_verts, h_Vl_disj_pairwise⟩

    dsimp [f_LHS_RHS_fwd, V, Vl]
    simp_all only [Fin.isValue, Fintype.card_ofFinset, coe_graph, Set.image_subset_iff,
      Set.union_subset_iff, and_self, Set.union_diff_self, Subtype.mk.injEq, Prod.mk.injEq]
    constructor
    . simp_all only [Fin.isValue]; dsimp [F₀,G₀]; congr!
    . constructor
      . funext i
        match i with
        | 0 =>
            simp_all only [Fin.isValue, Set.mem_image, exists_exists_and_eq_and]
            refine Eq.trans ?_ (h_iso₀_symm_comp_iso₀_eq_id (Vl' 0))
            congr!
            rename_i h_ty_eq u u' h_u_heq_u' v
            have : u.val = u'.val := by congr!
            rw [this]
            constructor
            . intro h'; exact SetCoe.ext h'
            . intro h'; rw [h']
        | 1 =>
            simp_all only [Fin.isValue, Set.mem_image, exists_exists_and_eq_and]
            refine Eq.trans ?_ (h_iso₀_symm_comp_iso₀_eq_id (Vl' 1))
            congr!
            rename_i h_ty_eq u u' h_u_heq_u' v
            have : u.val = u'.val := by congr!
            rw [this]
            constructor
            . intro h'; exact SetCoe.ext h'
            . intro h'; rw [h']
      . funext i
        match i with
        | 0 => simp_all only [Fin.isValue, coe_graph, Set.toFinset_card, Fintype.card_ofFinset,
                  Set.union_eq_right, Set.union_subset_iff, Set.image_subset_iff, and_self]
        | 1 => simp only [Fin.isValue]

  Equiv.ofBijective f_LHS_RHS_fwd ⟨h_f_LHS_RHS_inj, h_f_LHS_RHS_surj⟩

set_option linter.unusedVariables false in
/-- Chain-rule bijection, step 3: recognize the vertex-set pairs as genuine
realizing subgraph lists, yielding the Σ-type over the intermediate flag `G'`. -/
noncomputable def
  powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step3
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : { ⟨G', Vl', Vl''⟩ : Flag σ (Fin ℓ')
                                × (Fin 2 → Set (Fin ℓ'))
                                × (Fin 2 → Set (Fin ℓ))
                | (∀ i : Fin 2, (Vl' i) ∩ G'.out.type_verts = ∅)
                ∧ (∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl'
                ∧ Set.univ.PairwiseDisjoint Vl''
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i))
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [G'.out, H₃]ᵍ i)) }
      ≃
      (G' : Flag σ (Fin ℓ'))
        × (setOfLabeledSubgraphListIsoHl G'.out [H₁, H₂]ᵍ).toFinset
        × (setOfLabeledSubgraphListIsoHl G [G'.out, H₃]ᵍ).toFinset
  :=
  let T := (G' : Flag σ (Fin ℓ'))
            × (setOfLabeledSubgraphListIsoHl G'.out [H₁, H₂]ᵍ).toFinset
            × (setOfLabeledSubgraphListIsoHl G [G'.out, H₃]ᵍ).toFinset

  let T₀ := { ⟨G', Gl', Gl''⟩ : (G' : Flag σ (Fin ℓ'))
                                × LabeledSubgraphList σ 2 G'.out
                                × LabeledSubgraphList σ 2 G
                | Gl'.IsInduced
                ∧ predIsoLabeledHl G'.out [H₁, H₂]ᵍ Gl'
                ∧ Gl''.IsInduced
                ∧ predIsoLabeledHl G [G'.out, H₃]ᵍ Gl'' }

  let T₁ := { ⟨G', Vl', Vl''⟩ : Flag σ (Fin ℓ')
                                × (Fin 2 → Set (Fin ℓ'))
                                × (Fin 2 → Set (Fin ℓ))
                | (∀ i : Fin 2, (Vl' i) ∩ G'.out.type_verts = ∅)
                ∧ (∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl'
                ∧ Set.univ.PairwiseDisjoint Vl''
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i))
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [G'.out, H₃]ᵍ i)) }

  let f_T₀_T :=
    let f_T₀_T_fwd : T₀ → T := by
      intro ⟨⟨G', Gl', Gl''⟩, h_Gl'_ind, h_Gl'_other, h_Gl''_ind, h_Gl''_other⟩
      refine ⟨G', ⟨Gl', ?r_Gl'⟩, ⟨Gl'', ?r_Gl''⟩⟩
      dsimp [T]
      . dsimp [setOfLabeledSubgraphListIsoHl]
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h_Gl'_ind, h_Gl'_other⟩
      . dsimp [setOfLabeledSubgraphListIsoHl]
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h_Gl''_ind, h_Gl''_other⟩

    have h_f_T₀_T_inj : Function.Injective f_T₀_T_fwd := by
      intro ⟨⟨G'₁, Gl'₁, Gl''₁⟩, h₁⟩  ⟨⟨G'₂, Gl'₂, Gl''₂⟩, h₂⟩ h_eq
      dsimp [f_T₀_T_fwd, T] at h_eq

      split at h_eq
      rename_i _ _ G'₁_copy Gl'₁_copy Gl''₁_copy _ _ _ _ h_eq_lhs
      simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Sigma.mk.injEq] at h_eq_lhs
      obtain ⟨h_eq_lhs₀, h_eq_lhs₁⟩ := h_eq_lhs
      subst h_eq_lhs₀

      split at h_eq
      rename_i _ _ G'₂_copy Gl'₂_copy Gl''₂_copy _ _ _ _ h_eq_rhs
      simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Sigma.mk.injEq] at h_eq_rhs
      obtain ⟨h_eq_rhs₀, h_eq_rhs₁⟩ := h_eq_rhs
      subst h_eq_rhs₀

      simp only [Sigma.mk.injEq] at h_eq
      obtain ⟨h_eq₀, h_eq₁⟩ := h_eq
      subst h_eq₀

      simp_all only [heq_eq_eq, Prod.mk.injEq, Subtype.mk.injEq]

    have h_f_T₀_T_surj : Function.Surjective f_T₀_T_fwd := by
      intro ⟨G', ⟨Gl', h_Gl'⟩, ⟨Gl'', h_Gl''⟩⟩
      dsimp [setOfLabeledSubgraphListIsoHl] at h_Gl' h_Gl''
      simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at h_Gl' h_Gl''
      obtain ⟨h_Gl'_ind, h_Gl'_other⟩ := h_Gl'
      obtain ⟨h_Gl''_ind, h_Gl''_other⟩ := h_Gl''
      use ⟨⟨G', Gl', Gl''⟩, h_Gl'_ind, h_Gl'_other, h_Gl''_ind, h_Gl''_other⟩

    Equiv.ofBijective f_T₀_T_fwd ⟨h_f_T₀_T_inj, h_f_T₀_T_surj⟩

  let f_T₁_T₀ : T₁ ≃ T₀ :=
    let f_T₁_T₀_fwd : T₁ → T₀ := by
      intro ⟨⟨G', Vl', Vl''⟩,
        h_Vl'_disj_G'_type_verts, h_Vl''_disj_G_type_verts,
        h_Vl'_disj_pairwise, h_Vl''_disj_pairwise,
        h_Vl'_iso, h_Vl''_iso⟩
      let Gl' (i : Fin 2) := inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right
      let Gl'' (i : Fin 2) := inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right
      have h_Gl'_ind : ∀ i : Fin 2, (Gl' i).IsInduced := by
        intro i
        exact inducedLabeledSubgraph_isInduced G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right
      have h_Gl''_ind : ∀ i : Fin 2, (Gl'' i).IsInduced := by
        intro i
        exact inducedLabeledSubgraph_isInduced G (Vl'' i ∪ G.type_verts) Set.subset_union_right
      have h_Gl'_other : predIsoLabeledHl G'.out [H₁, H₂]ᵍ Gl' := by
        dsimp [predIsoLabeledHl]
        refine ⟨h_Vl'_iso, ?_⟩
        dsimp [predDisjointLabeledSubgraphList]
        intro i j h_neq
        rw [inducedLabeledSubgraph_verts G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right]
        rw [inducedLabeledSubgraph_verts G'.out (Vl' j ∪ G'.out.type_verts) Set.subset_union_right]
        simp only [Set.union_diff_right]
        rw [←Set.diff_inter_distrib_right G'.out.type_verts (Vl' i) (Vl' j)]
        have := Set.disjoint_iff_inter_eq_empty.mp
                  (h_Vl'_disj_pairwise (Set.mem_univ i) (Set.mem_univ j) h_neq)
        rw [this]
        exact Set.empty_diff G'.out.type_verts
      have h_Gl''_other : predIsoLabeledHl G [G'.out, H₃]ᵍ Gl'' := by
        dsimp [predIsoLabeledHl]
        refine ⟨h_Vl''_iso, ?_⟩
        dsimp [predDisjointLabeledSubgraphList]
        intro i j h_neq
        rw [inducedLabeledSubgraph_verts G (Vl'' i ∪ G.type_verts) Set.subset_union_right]
        rw [inducedLabeledSubgraph_verts G (Vl'' j ∪ G.type_verts) Set.subset_union_right]
        simp only [Set.union_diff_right]
        rw [←Set.diff_inter_distrib_right G.type_verts (Vl'' i) (Vl'' j)]
        have := Set.disjoint_iff_inter_eq_empty.mp
                  (h_Vl''_disj_pairwise (Set.mem_univ i) (Set.mem_univ j) h_neq)
        rw [this]
        exact Set.empty_diff G.type_verts
      exact ⟨⟨G', Gl', Gl''⟩, h_Gl'_ind, h_Gl'_other, h_Gl''_ind, h_Gl''_other⟩

    have h_f_T₁_T₀_inj : Function.Injective f_T₁_T₀_fwd := by
      intro ⟨⟨G'₁, Vl'₁, Vl''₁⟩, h_Vl'₁_disj_G'₁_type_verts, h_Vl''₁_disj_G_type_verts, _, _, _, _⟩
        ⟨⟨G'₂, Vl'₂, Vl''₂⟩, h_Vl'₂_disj_G'₂_type_verts, h_Vl''₂_disj_G_type_verts, _, _, _, _⟩
        h_eq
      dsimp [f_T₁_T₀_fwd] at h_eq
      simp only [Subtype.mk.injEq, Sigma.mk.injEq] at h_eq
      obtain ⟨h_eq_G', h_eq_other⟩ := h_eq
      subst h_eq_G'
      simp only [heq_eq_eq, Prod.mk.injEq] at h_eq_other
      obtain ⟨h_eq_Vl', h_eq_Vl''⟩ := h_eq_other
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      constructor
      . funext i
        calc
          Vl'₁ i
          _ = (Vl'₁ i ∪ G'₁.out.type_verts) \ G'₁.out.type_verts :=
                    Eq.symm (Set.union_diff_cancel_right (by simp only [h_Vl'₁_disj_G'₁_type_verts i, subset_refl]))
          _ = (inducedLabeledSubgraph G'₁.out (Vl'₁ i ∪ G'₁.out.type_verts) Set.subset_union_right).subgraph.verts
                \ G'₁.out.type_verts := by
                    rw [inducedLabeledSubgraph_verts G'₁.out (Vl'₁ i ∪ G'₁.out.type_verts) Set.subset_union_right]
          _ = (inducedLabeledSubgraph G'₁.out (Vl'₂ i ∪ G'₁.out.type_verts) Set.subset_union_right).subgraph.verts
                \ G'₁.out.type_verts := by
                    rw [funext_iff.mp h_eq_Vl' i]
          _ = (Vl'₂ i ∪ G'₁.out.type_verts) \ G'₁.out.type_verts := by
                    rw [inducedLabeledSubgraph_verts G'₁.out (Vl'₂ i ∪ G'₁.out.type_verts) Set.subset_union_right]
          _ = Vl'₂ i :=
                    Set.union_diff_cancel_right (by simp only [h_Vl'₂_disj_G'₂_type_verts i, subset_refl])
      . funext i
        calc
          Vl''₁ i
          _ = (Vl''₁ i ∪ G.type_verts) \ G.type_verts :=
                    Eq.symm (Set.union_diff_cancel_right (by simp only [h_Vl''₁_disj_G_type_verts i, subset_refl]))
          _ = (inducedLabeledSubgraph G (Vl''₁ i ∪ G.type_verts) Set.subset_union_right).subgraph.verts
                \ G.type_verts := by
                    rw [inducedLabeledSubgraph_verts G (Vl''₁ i ∪ G.type_verts) Set.subset_union_right]
          _ = (inducedLabeledSubgraph G (Vl''₂ i ∪ G.type_verts) Set.subset_union_right).subgraph.verts
                \ G.type_verts := by
                    rw [funext_iff.mp h_eq_Vl'' i]
          _ = (Vl''₂ i ∪ G.type_verts) \ G.type_verts := by
                    rw [inducedLabeledSubgraph_verts G (Vl''₂ i ∪ G.type_verts) Set.subset_union_right]
          _ = Vl''₂ i :=
                    Set.union_diff_cancel_right (by simp only [h_Vl''₂_disj_G_type_verts i, subset_refl])

    have h_f_T₁_T₀_surj : Function.Surjective f_T₁_T₀_fwd := by
      intro ⟨⟨G', Gl', Gl''⟩, h_Gl'_ind, h_Gl'_other, h_Gl''_ind, h_Gl''_other⟩
      dsimp [predIsoLabeledHl, predDisjointLabeledSubgraphList] at h_Gl'_other h_Gl''_other
      obtain ⟨h_Gl'_iso, h_Gl'_pairwise_disj⟩ := h_Gl'_other
      obtain ⟨h_Gl''_iso, h_Gl''_pairwise_disj⟩ := h_Gl''_other

      let Vl' : Fin 2 → Set (Fin ℓ') := fun i ↦ (Gl' i).subgraph.verts \ G'.out.type_verts
      let Vl'' : Fin 2 → Set (Fin ℓ) := fun i ↦ (Gl'' i).subgraph.verts \ G.type_verts

      have h_Vl'_Gl'_verts : ∀ i : Fin 2, (Vl' i) ∪ G'.out.type_verts = (Gl' i).subgraph.verts := by
        intro i
        exact Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G'.out (Gl' i))
      have h_Vl''_Gl''_verts : ∀ i : Fin 2, (Vl'' i) ∪ G.type_verts = (Gl'' i).subgraph.verts := by
        intro i
        exact Set.diff_union_of_subset (labeledSubgraph_contain_type_verts G (Gl'' i))
      have h_Vl'_disj_G'_type_verts : ∀ i : Fin 2, (Vl' i) ∩ G'.out.type_verts = ∅ := by
        intro i
        exact Set.diff_inter_self
      have h_Vl''_disj_G_type_verts : ∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅ := by
        intro i
        exact Set.diff_inter_self
      have h_Vl'_disj_pairwise : Set.univ.PairwiseDisjoint Vl' := by
        intro i _ j _ h_neq
        exact Set.disjoint_iff_inter_eq_empty.mpr (h_Gl'_pairwise_disj i j h_neq)
      have h_Vl''_disj_pairwise : Set.univ.PairwiseDisjoint Vl'' := by
        intro i _ j _ h_neq
        exact Set.disjoint_iff_inter_eq_empty.mpr (h_Gl''_pairwise_disj i j h_neq)
      have h_Vl'_iso : ∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i) := by
        intro i
        have h' : inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right
                  = inducedLabeledSubgraph G'.out (Gl' i).subgraph.verts (labeledSubgraph_contain_type_verts G'.out (Gl' i))  := by
          congr!
          exact h_Vl'_Gl'_verts i
        let g₁ : (inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe
                  ≃f (inducedLabeledSubgraph G'.out (Gl' i).subgraph.verts (labeledSubgraph_contain_type_verts G'.out (Gl' i))).coe := by
          rw [h']
        let g₂ : (inducedLabeledSubgraph G'.out (Gl' i).subgraph.verts (labeledSubgraph_contain_type_verts G'.out (Gl' i))).coe
                  ≃f [H₁, H₂]ᵍ i := by
          rw [←inducedLabeledSubgraph_eq (h_Gl'_ind i)]
          exact (h_Gl'_iso i).some
        exact Nonempty.intro (g₁.trans g₂)
      have h_Vl''_iso : ∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [G'.out, H₃]ᵍ i) := by
        intro i
        have h' : inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right
                  = inducedLabeledSubgraph G (Gl'' i).subgraph.verts (labeledSubgraph_contain_type_verts G (Gl'' i)) := by
          congr!
          exact h_Vl''_Gl''_verts i
        let g₁ : (inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe
                  ≃f (inducedLabeledSubgraph G (Gl'' i).subgraph.verts (labeledSubgraph_contain_type_verts G (Gl'' i))).coe := by
          rw [h']
        let g₂ : (inducedLabeledSubgraph G (Gl'' i).subgraph.verts (labeledSubgraph_contain_type_verts G (Gl'' i))).coe
                  ≃f [G'.out, H₃]ᵍ i := by
          rw [←inducedLabeledSubgraph_eq (h_Gl''_ind i)]
          exact (h_Gl''_iso i).some
        exact Nonempty.intro (g₁.trans g₂)

      use ⟨⟨G', Vl', Vl''⟩,
        h_Vl'_disj_G'_type_verts, h_Vl''_disj_G_type_verts,
        h_Vl'_disj_pairwise, h_Vl''_disj_pairwise, h_Vl'_iso, h_Vl''_iso⟩
      dsimp [f_T₁_T₀_fwd]
      simp_all only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and]
      constructor
      . funext i
        exact (inducedLabeledSubgraph_eq (h_Gl'_ind i)).symm
      . funext i
        exact (inducedLabeledSubgraph_eq (h_Gl''_ind i)).symm

    Equiv.ofBijective f_T₁_T₀_fwd ⟨h_f_T₁_T₀_inj, h_f_T₁_T₀_surj⟩

  f_T₁_T₀.trans f_T₀_T

/-- The composite chain-rule bijection (steps 0–3 chained): a powerset choice
together with a realizing triple list for `[H₁, H₂, H₃]` in `G` corresponds
bijectively to an intermediate flag `G'` with a realizing pair for `[H₁, H₂]` in
`G'` and a realizing pair for `[G', H₃]` in `G`. -/
noncomputable def
  powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : (Finset.univ : Finset (Fin ((ℓ - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀) - (ℓ₃ - ℓ₀)))).powersetCard ((ℓ' - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀))
        × (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset
      ≃
      (G' : Flag σ (Fin ℓ'))
        × (setOfLabeledSubgraphListIsoHl G'.out [H₁, H₂]ᵍ).toFinset
        × (setOfLabeledSubgraphListIsoHl G [G'.out, H₃]ᵍ).toFinset
  :=
  let ℓ_other := (ℓ - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀) - (ℓ₃ - ℓ₀)
  let ℓ'_other := (ℓ' - ℓ₀) - (ℓ₁ - ℓ₀) - (ℓ₂ - ℓ₀)

  let Hl_size (i : Fin 3) : ℕ :=
    match i with
    | 0 => ℓ₁
    | 1 => ℓ₂
    | 2 => ℓ₃
  let Hl (i : Fin 3) : LabeledGraph σ (Fin (Hl_size i)) :=
    match i with
    | 0 => H₁
    | 1 => H₂
    | 2 => H₃

  have h_G_type_verts_card_eq_ℓ₀ : Fintype.card ↑G.type_verts = ℓ₀ := by
    simp only [G.type_verts_card_eq]
    dsimp [FlagType.size]
    exact Fintype.card_fin ℓ₀

  let LHS := (Finset.univ : Finset (Fin ℓ_other)).powersetCard ℓ'_other
             × (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset

  let S₁ := { ⟨X, Vl⟩ : Finset (Fin ℓ_other) × (Fin 3 → Set (Fin ℓ))
                | X.card = ℓ'_other
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }

  let S₂ := { ⟨V, Vl⟩ : Set (Fin ℓ) × (Fin 3 → Set (Fin ℓ))
                | V.toFinset.card = ℓ'_other
                ∧ (∀ i : Fin 3, V ∩ (Vl i) = ∅)
                ∧ V ∩ G.type_verts = ∅
                ∧ (∀ i : Fin 3, (Vl i).toFinset.card = Hl_size i - ℓ₀)
                ∧ (∀ i : Fin 3, Nonempty ((inducedLabeledSubgraph G ((Vl i) ∪ G.type_verts) Set.subset_union_right).coe ≃f (Hl i)))
                ∧ (∀ i : Fin 3, (Vl i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl }

  let T₁ := { ⟨G', Vl', Vl''⟩ : Flag σ (Fin ℓ')
                                × (Fin 2 → Set (Fin ℓ'))
                                × (Fin 2 → Set (Fin ℓ))
                | (∀ i : Fin 2, (Vl' i) ∩ G'.out.type_verts = ∅)
                ∧ (∀ i : Fin 2, (Vl'' i) ∩ G.type_verts = ∅)
                ∧ Set.univ.PairwiseDisjoint Vl'
                ∧ Set.univ.PairwiseDisjoint Vl''
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G'.out (Vl' i ∪ G'.out.type_verts) Set.subset_union_right).coe ≃f [H₁, H₂]ᵍ i))
                ∧ (∀ i : Fin 2, Nonempty ((inducedLabeledSubgraph G (Vl'' i ∪ G.type_verts) Set.subset_union_right).coe ≃f [G'.out, H₃]ᵍ i)) }

  let RHS := (G' : Flag σ (Fin ℓ'))
             × (setOfLabeledSubgraphListIsoHl G'.out [H₁, H₂]ᵍ).toFinset
             × (setOfLabeledSubgraphListIsoHl G [G'.out, H₃]ᵍ).toFinset

  let f_LHS_S₁ : LHS ≃ S₁ := by
    dsimp [LHS, S₁]
    exact powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step0
            ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ
            ℓ_other  (by rfl)
            ℓ'_other (by rfl)
            Hl_size  (by dsimp [Hl_size]; simp only [and_self])
            Hl       (by dsimp [Hl, Hl_size]; simp only [heq_eq_eq, and_self])

  let f_S₁_S₂ : S₁ ≃ S₂ := by
    dsimp [S₁, S₂]
    exact powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step1
            ℓ' G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ
            ℓ_other  (by rfl)
            ℓ'_other
            Hl_size  (by dsimp [Hl_size]; simp only [and_self])
            Hl

  let f_S₂_T₁ : S₂ ≃ T₁ := by
    dsimp [S₂, T₁]
    exact powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step2
            ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ
            ℓ'_other (by rfl)
            Hl_size  (by dsimp [Hl_size]; simp only [and_self])
            Hl       (by dsimp [Hl, Hl_size]; simp only [heq_eq_eq, and_self])

  let f_T₁_RHS : T₁ ≃ RHS :=
    powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl_step3
       ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ

  (((f_LHS_S₁.trans f_S₁_S₂).trans f_S₂_T₁).trans f_T₁_RHS)

/-- Counting form of the chain rule: the binomial-weighted triple count equals the
sum over intermediate flags `G'` of (pair count in `G'`) · (pair count in `G`),
obtained by taking cardinalities through the composite bijection. -/
lemma labeledGraphTripleCount_eq_sum_density_prods'
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : (Nat.choose (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃) (ℓ' + ℓ₀ - ℓ₁ - ℓ₂))
        * labeledGraphListCount [H₁, H₂, H₃]ᵍ G
      = ∑ G' : Flag σ (Fin ℓ'),
          labeledGraphListCount [H₁, H₂]ᵍ G'.out * labeledGraphListCount [G'.out, H₃]ᵍ G
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
  let h_iso : S_LHS ≃ S_RHS :=
    powersetCard_prod_setOfLabeledSubgraphListIsoHl_iso_sigma_setOfLabeledSubgraphListIsoHl ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ
  calc
    (Nat.choose ℓ_other ℓ'_other) * (labeledGraphListCount [H₁, H₂, H₃]ᵍ G)
    _ = (Nat.choose ℓ_other ℓ'_other) * (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset.card := by
              dsimp [labeledGraphListCount]
              congr!
    _ = ((Finset.univ : Finset (Fin ℓ_other)).powersetCard ℓ'_other).card
        * (setOfLabeledSubgraphListIsoHl G [H₁, H₂, H₃]ᵍ).toFinset.card := by
              simp only [Set.toFinset_card, Fintype.card_ofFinset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ = (Fintype.card S_LHS) := by
              dsimp [S_LHS]
              simp only [Finset.card_powersetCard, Finset.card_univ,
                Fintype.card_fin, Set.toFinset_card, Fintype.card_ofFinset,
                Finset.mem_powersetCard, Finset.subset_univ, true_and,
                Set.mem_toFinset, Fintype.card_prod, Fintype.card_finset_len]
    _ = (Fintype.card S_RHS) :=
              Fintype.card_congr h_iso
    _ = ∑ G' : Flag σ (Fin ℓ'),
          (setOfLabeledSubgraphListIsoHl G'.out [H₁, H₂]ᵍ).toFinset.card
          * (setOfLabeledSubgraphListIsoHl G [G'.out, H₃]ᵍ).toFinset.card := by
              dsimp [S_RHS]
              simp only [Set.mem_toFinset, Fintype.card_sigma, Fintype.card_prod, Fintype.card_ofFinset, Set.toFinset_card]
    _ = ∑ G' : Flag σ (Fin ℓ'),
          labeledGraphListCount [H₁, H₂]ᵍ G'.out * labeledGraphListCount [G'.out, H₃]ᵍ G := by
              dsimp [labeledGraphListCount]
              congr!

set_option maxHeartbeats 400000 in
/-- Multinomial-coefficient form of the counting chain rule, repackaging
`labeledGraphTripleCount_eq_sum_density_prods'` with the normalizers that turn
counts into densities. -/
lemma labeledGraphTripleCount_eq_sum_density_prods
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    :     multinomialCoefficient
            (fun i : Fin 2 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀)
            (ℓ' - ℓ₀)
        * multinomialCoefficient
            (fun i : Fin 2 ↦ match i with | 0 => ℓ' - ℓ₀ | 1 => ℓ₃ - ℓ₀)
            (ℓ - ℓ₀)
        * labeledGraphListCount [H₁, H₂, H₃]ᵍ G
      =
          multinomialCoefficient
            (fun i : Fin 3 ↦ match i with | 0 => ℓ₁ - ℓ₀ | 1 => ℓ₂ - ℓ₀ | 2 => ℓ₃ - ℓ₀)
            (ℓ - ℓ₀)
        * ∑ G' : Flag σ (Fin ℓ'),
            labeledGraphListCount [H₁, H₂]ᵍ G'.out * labeledGraphListCount [G'.out, H₃]ᵍ G
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
           * (ℓ + 2 * ℓ₀ - ℓ₁ - ℓ₂ - ℓ₃).choose (ℓ' + ℓ₀ - ℓ₁ - ℓ₂)
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
        Nat.mul_dvd_mul h₀ dvd_rfl
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
        nth_rw 1 [mul_assoc]
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
      _ = ((ℓ' - ℓ₀).factorial * (ℓ - ℓ₀).factorial)
          / (((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial) *
             ((ℓ' - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) :=
                  Nat.div_mul_div_comm h_dvd₀ h_dvd₁
      _ = ((ℓ' - ℓ₀).factorial * (ℓ - ℓ₀).factorial)
          / ((ℓ' - ℓ₀).factorial *
             ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial)) := by
                  ring_nf
      _ = (ℓ - ℓ₀).factorial
          / ((ℓ₁ - ℓ₀).factorial * (ℓ₂ - ℓ₀).factorial * (ℓ₃ - ℓ₀).factorial * (ℓ' + ℓ₀ - ℓ₁ - ℓ₂).factorial * (ℓ - ℓ' + ℓ₀ - ℓ₃).factorial) :=
                  Nat.mul_div_mul_left _ _ (Nat.factorial_pos (ℓ' - ℓ₀))
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
/-- Density form of the chain rule on labeled-graph representatives: the triple
density equals the sum over intermediate flags `G'` of the product of the two pair
densities. The representative-level statement behind the public chain rules. -/
lemma labeledGraphTripleDensity_eq_sum_density_prods
    (ℓ' : ℕ) (H₁ : LabeledGraph σ (Fin ℓ₁)) (H₂ : LabeledGraph σ (Fin ℓ₂)) (H₃ : LabeledGraph σ (Fin ℓ₃)) (G : LabeledGraph σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : labeledGraphListDensity [H₁, H₂, H₃]ᵍ G
      =
      ∑ G' : Flag σ (Fin ℓ'), labeledGraphListDensity [H₁, H₂]ᵍ G'.out
                              * labeledGraphListDensity [G'.out, H₃]ᵍ G
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
  suffices C * labeledGraphListDensity [H₁, H₂, H₃]ᵍ G
           =
           C * ∑ G' : Flag σ (Fin ℓ'), labeledGraphListDensity [H₁, H₂]ᵍ G'.out
                                       * labeledGraphListDensity [G'.out, H₃]ᵍ G
  by exact (mul_right_inj' (by exact_mod_cast h_C_pos.ne')).mp this
  {
    have h_σ_size : σ.size = ℓ₀ := Fintype.card_fin ℓ₀
    have h_fintype_two₀ := fintype_card_match_comm_two ℓ₀ ℓ₁ ℓ₂
    have h_fintype_two₁ := fintype_card_match_comm_two ℓ₀ ℓ' ℓ₃
    have h_fintype_three := fintype_card_match_comm_three ℓ₀ ℓ₁ ℓ₂ ℓ₃
    have pair_density_eq_count_over_coeff :
        ∑ G' : Flag σ (Fin ℓ'),
          labeledGraphListDensity (labeledGraphPairToList H₁ H₂) G'.out *
          labeledGraphListDensity (labeledGraphPairToList G'.out H₃) G
        =
        ∑ G' : Flag σ (Fin ℓ'),
          @Nat.cast ℚ Rat.instNatCast ((labeledGraphListCount (labeledGraphPairToList H₁ H₂) G'.out)) / (C_rhs₀) *
          ((labeledGraphListCount (labeledGraphPairToList G'.out H₃) G) / C_rhs₁)
      := by
      apply Finset.sum_congr rfl
      intro G' _
      congr!
      · dsimp [labeledGraphListDensity]
        congr
        · dsimp [labeledGraphPairToList, LabeledGraph.size]
          rw [h_σ_size, ← h_fintype_two₀]
          rfl
        · dsimp [LabeledGraph.size]
          exact Fintype.card_fin ℓ'
      · dsimp [labeledGraphListDensity]
        congr
        · dsimp [labeledGraphPairToList, LabeledGraph.size]
          rw [h_σ_size, ← h_fintype_two₁]
          rfl
        · dsimp [LabeledGraph.size]
          exact Fintype.card_fin ℓ
    rw [pair_density_eq_count_over_coeff]
    have triple_density_eq_count_over_coeff :
        labeledGraphListDensity (labeledGraphTripleToList H₁ H₂ H₃) G
        =
        (labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) / C_lhs
      := by
      dsimp [labeledGraphListDensity]
      congr
      · rw [h_σ_size, ← h_fintype_three]
        rfl
      · exact Fintype.card_fin ℓ
    rw [triple_density_eq_count_over_coeff]
    calc
      (C : ℚ) * (↑(labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) / ↑C_lhs)
      _ = ((C : ℚ) / ↑C_lhs) * ↑(labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                ring
      _ = ((C_lhs : ℚ) * ↑C_rhs₀ * ↑C_rhs₁ / ↑C_lhs) *
          ↑(labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                rw [Nat.cast_mul, Nat.cast_mul]
      _ = ((C_lhs : ℚ) * ((↑C_rhs₀ * ↑C_rhs₁) / ↑C_lhs)) *
          ↑(labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                ring
      _ = (C_rhs₀ : ℚ) * ↑C_rhs₁ *
          ↑(labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                field_simp
      _ = ↑(C_rhs₀ * C_rhs₁ * labeledGraphListCount (labeledGraphTripleToList H₁ H₂ H₃) G) := by
                simp only [Nat.cast_mul]
      _ = ↑(C_lhs * ∑ G' : Flag σ (Fin ℓ'),
                      (labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
                      (labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)) := by
                rw [labeledGraphTripleCount_eq_sum_density_prods ℓ' H₁ H₂ H₃ G hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ]
      _ = ↑C_lhs * ∑ G' : Flag σ (Fin ℓ'),
                      ↑(labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
                      ↑(labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G) := by
                simp only [Nat.cast_mul, Nat.cast_sum]
      _ = ((C_lhs : ℚ) * (↑C_rhs₀ * ↑C_rhs₁) / (↑C_rhs₀ * ↑C_rhs₁))
          * ∑ G' : Flag σ (Fin ℓ'),
              ↑(labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
              (↑(labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)) := by
                field_simp
      _ = ((C : ℚ) / (↑C_rhs₀ * ↑C_rhs₁))
          * ∑ G' : Flag σ (Fin ℓ'),
              ↑(labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
              (↑(labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)) := by
                rw [Nat.cast_mul, Nat.cast_mul]
                ring
      _ = (C : ℚ)
          * ((∑ G' : Flag σ (Fin ℓ'),
                ↑(labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
                (↑(labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G)))
             / (↑C_rhs₀ * ↑C_rhs₁)) := by
                field_simp
      _ = (C : ℚ)
          * ∑ G' : Flag σ (Fin ℓ'),
              (↑(labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) *
               ↑(labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G))
              / (↑C_rhs₀ * ↑C_rhs₁) := by
                rw [Finset.sum_div]
      _ = (C : ℚ)
          * ∑ G' : Flag σ (Fin ℓ'),
            ↑(labeledGraphListCount (labeledGraphPairToList H₁ H₂) (Quotient.out G')) / ↑C_rhs₀ *
            (↑(labeledGraphListCount (labeledGraphPairToList (Quotient.out G') H₃) G) / ↑C_rhs₁) := by
                field_simp
  }

/-- Chain rule for triple densities (aliased `density_chain_rule₂₂`):
`d(F₁,F₂,F₃;G) = Σ_{G'} d(F₁,F₂;G') · d(G',F₃;G)` over intermediate flags of size `ℓ'`. -/
theorem flagTripleDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (F₂ : Flag σ (Fin ℓ₂)) (F₃ : Flag σ (Fin ℓ₃)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂) (hℓ₃ : ℓ₀ ≤ ℓ₃) (hℓ' : ℓ₁ + ℓ₂ ≤ ℓ' + ℓ₀) (hℓ : ℓ' + ℓ₃ ≤ ℓ + ℓ₀)
    : flagDensity₃ F₁ F₂ F₃ G = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ F₁ F₂ G' * flagDensity₂ G' F₃ G
  := by
  rw [←F₁.out_eq, ←F₂.out_eq, ←F₃.out_eq, ←G.out_eq]
  rw [←labeledGraphListDensity_eq_flagDensity₃ F₁.out F₂.out F₃.out G.out]
  have h : ∑ (G' : Flag σ (Fin ℓ')), flagDensity₂ ⟦F₁.out⟧ ⟦F₂.out⟧ G' * flagDensity₂ G' ⟦F₃.out⟧ ⟦G.out⟧
           = ∑ (G' : Flag σ (Fin ℓ')), labeledGraphListDensity [F₁.out, F₂.out]ᵍ G'.out * labeledGraphListDensity [G'.out, F₃.out]ᵍ G.out
    := by
    apply Finset.sum_congr (by rfl)
    intros G'
    rw [←G'.out_eq]
    rw [←labeledGraphListDensity_eq_flagDensity₂ F₁.out F₂.out G'.out]
    rw [←labeledGraphListDensity_eq_flagDensity₂ G'.out F₃.out G.out]
    simp only [Quotient.out_eq, Finset.mem_univ, imp_self]
  rw [h]
  exact labeledGraphTripleDensity_eq_sum_density_prods ℓ' F₁.out F₂.out F₃.out G.out hℓ₁ hℓ₂ hℓ₃ hℓ' hℓ

/-- Chain rule expanding a pair density over a final single flag (aliased
`density_chain_rule₂₁`): `d(F₁,F₂;G) = Σ_{G'} d(F₁,F₂;G') · d(G';G)`. -/
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

/-- Chain rule expanding a pair density over a leading single flag (aliased
`density_chain_rule₁₂`): `d(F₁,F₂;G) = Σ_{G'} d(F₁;G') · d(G',F₂;G)`. -/
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

/-- The basic flag-algebra chain rule (aliased `density_chain_rule₁₁`):
`d(F₁;G) = Σ_{G'} d(F₁;G') · d(G';G)` over intermediate flags of size `ℓ'`. -/
theorem flagDensity_eq_sum_density_prods
    (ℓ' : ℕ) (F₁ : Flag σ (Fin ℓ₁)) (G : Flag σ (Fin ℓ))
    (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ' : ℓ₁ ≤ ℓ') (hℓ : ℓ' ≤ ℓ)
    : flagDensity₁ F₁ G = ∑ (G' : Flag σ (Fin ℓ')), flagDensity₁ F₁ G' * flagDensity₁ G' G
  := by
  rw [← flagPairDensity_empty, flagPairDensity_eq_sum_density_prods ℓ'] <;> try linarith
  apply Finset.sum_congr (by rfl)
  intros
  rw [flagPairDensity_empty]

/-! ## Public chain-rule aliases

Short, uniformly named handles for the four chain rules above (subscripts =
arities of the two density factors), used by the `Forbid`/`Automation` tactic layer. -/

alias density_chain_rule₁₁ := flagDensity_eq_sum_density_prods
alias density_chain_rule₁₂ := flagPairDensity_eq_sum_density_prods'
alias density_chain_rule₂₁ := flagPairDensity_eq_sum_density_prods
alias density_chain_rule₂₂ := flagTripleDensity_eq_sum_density_prods

end FlagAlgebras
