import «LeanFlagAlgebras».FlagAlgebra.FlagOperators

/-! # Subset-parametrised subflag counting

Infrastructure for the counting identities of Razborov §4.3. The induced
labelled subgraphs of a host `X` are in bijection with the vertex subsets
containing all labelled vertices, so every `labeledGraphCount` can be recast
as a count of *vertex subsets* (`labeledGraphCount_eq_card_inducingSubsets`).
Sums of such counts over a family of pairwise distinct flags become a count
of a union of subset families (`sum_labeledGraphCount_filter`). This is the
form in which the total-probability computations of Lemmas 4.2/4.4 are
carried out: conditioning on whether the random vertex subset contains a
distinguished vertex (edge) is then literally a `Finset.filter` split.

Also provides the `getCanonicalFlag` equality lemmas used to move between
concrete labelled graphs on subtypes and flags on the canonical carriers. -/

namespace FlagAlgebras
namespace Differential

open Finset
open Classical
open LabeledSubgraph

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Canonical flags -/

theorem getCanonicalFlag_eq_iff {V : Type} [Fintype V] [DecidableEq V] {ℓ : ℕ}
    (G : LabeledGraph σ V) (h : Fintype.card V = ℓ) (F : Flag σ (Fin ℓ))
    : getCanonicalFlag G h = F ↔ Nonempty (F.out ≃f G)
  := by
  constructor
  · intro heq
    subst heq
    exact ⟨getCanonicalFlag_iso G h⟩
  · rintro ⟨φ⟩
    calc getCanonicalFlag G h
        = ⟦(getCanonicalFlag G h).out⟧ := (Quotient.out_eq _).symm
      _ = ⟦F.out⟧ := Quotient.sound ⟨(getCanonicalFlag_iso G h).trans φ.symm⟩
      _ = F := Quotient.out_eq _

/-- `getCanonicalFlag` identifies isomorphic labelled graphs (possibly on
different vertex types). -/
theorem getCanonicalFlag_eq_of_iso {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {ℓ : ℕ}
    {G : LabeledGraph σ V} {G' : LabeledGraph σ W}
    (φ : G ≃f G') (h : Fintype.card V = ℓ) (h' : Fintype.card W = ℓ)
    : getCanonicalFlag G h = getCanonicalFlag G' h'
  := by
  rw [getCanonicalFlag_eq_iff]
  exact ⟨(getCanonicalFlag_iso G' h').trans φ.symm⟩

/-- Two `∅ₜ`-labelled graphs with the same underlying graph are equal (the
empty type embedding is unique). -/
theorem emptyType_labeledGraph_ext {V : Type} {A B : LabeledGraph ∅ₜ V}
    (h : A.graph = B.graph)
    : A = B
  := by
  obtain ⟨g₁, e₁⟩ := A
  obtain ⟨g₂, e₂⟩ := B
  simp only at h
  subst h
  congr 1
  ext x
  exact x.elim0

/-! ## Subset-parametrised counting -/

/-- The vertex subsets of the host `X` that contain all labelled vertices and
induce a copy of `H₀`. -/
def inducingSubsets {U W : Type} (H₀ : LabeledGraph σ U) (X : LabeledGraph σ W)
    : Set (Set W)
  :=
  {S | ∃ (h : X.type_verts ⊆ S),
    Nonempty ((inducedLabeledSubgraph X S h).coe ≃f H₀)}

theorem mem_inducingSubsets {U W : Type} {H₀ : LabeledGraph σ U}
    {X : LabeledGraph σ W} {S : Set W}
    : S ∈ inducingSubsets H₀ X
      ↔ ∃ (h : X.type_verts ⊆ S),
          Nonempty ((inducedLabeledSubgraph X S h).coe ≃f H₀)
  := Iff.rfl

/-- **Subset form of subflag counting**: the number of induced labelled
subgraphs of `X` isomorphic to `H₀` equals the number of vertex subsets of
`X` inducing a copy of `H₀`. -/
theorem labeledGraphCount_eq_card_inducingSubsets
    {U W : Type} [Fintype U] [Fintype W] (H₀ : LabeledGraph σ U) (X : LabeledGraph σ W)
    : labeledGraphCount H₀ X = (inducingSubsets H₀ X).toFinset.card
  := by
  dsimp only [labeledGraphCount]
  apply Finset.card_bij (fun (H : LabeledSubgraph σ X) (_ : H ∈ _) => H.subgraph.verts)
  · intro H hH
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hH ⊢
    obtain ⟨h_ind, h_iso⟩ := hH
    rw [mem_inducingSubsets]
    exact ⟨labeledSubgraph_contain_type_verts X H,
      ⟨LabeledGraphIso.labeledSubgraphIso_cast (inducedLabeledSubgraph_eq h_ind) h_iso.some⟩⟩
  · intro H₁ h₁ H₂ h₂ heq
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at h₁ h₂
    apply labeledSubgraph_eq_from_subgraph_eq
    rw [← h₁.1.induce_top_verts, ← h₂.1.induce_top_verts]
    rw [heq]
  · intro S hS
    simp only [Set.mem_toFinset] at hS
    obtain ⟨h_sub, h_iso⟩ := hS
    refine ⟨inducedLabeledSubgraph X S h_sub, ?_, ?_⟩
    · simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨inducedLabeledSubgraph_isInduced X S h_sub, h_iso⟩
    · exact inducedLabeledSubgraph_verts X S h_sub

/-- Summing subflag counts over a family of pairwise distinct flags counts the
union of the corresponding subset families. -/
theorem sum_labeledGraphCount_filter {m : ℕ} {W : Type} [Fintype W]
    (𝒬 : FlagWithSize σ m → Prop) (X : LabeledGraph σ W)
    : ∑ F ∈ Finset.univ.filter 𝒬, labeledGraphCount F.out X
      = ((Finset.univ.filter 𝒬).biUnion
          (fun F => (inducingSubsets F.out X).toFinset)).card
  := by
  have hdisj : ∀ F₁ ∈ Finset.univ.filter 𝒬, ∀ F₂ ∈ Finset.univ.filter 𝒬, F₁ ≠ F₂ →
      Disjoint ((inducingSubsets F₁.out X).toFinset) ((inducingSubsets F₂.out X).toFinset) := by
    intro F₁ _ F₂ _ hne
    rw [Finset.disjoint_left]
    intro S hS₁ hS₂
    rw [Set.mem_toFinset, mem_inducingSubsets] at hS₁ hS₂
    obtain ⟨ha, ⟨ψ₁⟩⟩ := hS₁
    obtain ⟨hb, ⟨ψ₂⟩⟩ := hS₂
    apply hne
    calc F₁ = ⟦F₁.out⟧ := (Quotient.out_eq _).symm
      _ = ⟦F₂.out⟧ := Quotient.sound ⟨ψ₁.symm.trans ψ₂⟩
      _ = F₂ := Quotient.out_eq _
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro F _
  rw [labeledGraphCount_eq_card_inducingSubsets]

/-! ## Density as a subset count -/

theorem flagDensity₁_mk {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (H : LabeledGraph σ U) (X : LabeledGraph σ W)
    : flagDensity₁ (⟦H⟧ : Flag σ U) (⟦X⟧ : Flag σ W) = labeledGraphDensity H X
  := by
  dsimp only [flagDensity₁]
  rw [← subflagDensity_eq_flagListDensity]
  rfl

/-- The subflag density as a normalised subset count. -/
theorem labeledGraphDensity_eq_card_div {U W : Type}
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (H₀ : LabeledGraph σ U) (X : LabeledGraph σ W)
    : labeledGraphDensity H₀ X
      = ((inducingSubsets H₀ X).toFinset.card : ℚ)
        / ((Fintype.card W - n₀).choose (Fintype.card U - n₀))
  := by
  dsimp only [labeledGraphDensity]
  rw [labeledGraphCount_eq_card_inducingSubsets]
  congr 2 <;> simp [LabeledGraph.size, FlagType.size]

theorem flagDensity₁_out {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (H : Flag σ U) (X : Flag σ W)
    : flagDensity₁ H X = labeledGraphDensity H.out X.out
  := by
  conv_lhs => rw [← Quotient.out_eq H, ← Quotient.out_eq X]
  rw [flagDensity₁_mk]

end Differential
end FlagAlgebras
