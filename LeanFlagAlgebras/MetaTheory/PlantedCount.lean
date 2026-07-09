import LeanFlagAlgebras.MetaTheory.BlowupFlag
import LeanFlagAlgebras.MetaTheory.CloneCount

/-! # The good-event count for the planted estimate

The "good event" subsets of the blow-up (those containing the planted roots and meeting each
clone class at most once) that induce a copy of `F₀` are counted fiberwise over their
projection: each base subset `W` (containing the base roots) that induces `F₀` is hit by exactly
`∏_{v ∈ W ∖ roots} m v` good blow-up subsets (one clone choice per non-root vertex of `W`).  This
is the combinatorial heart of `lem:planted-estimate`, assembled from `clone_fiber_card`
(the clone multiplicity) and `good_event_induces_iff` (the projection preserves the induced flag).
-/

open Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras LabeledSubgraph

variable {n k : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}

/-! ## Root-projection helpers

Small facts relating the *planted* roots `θ̂ = ⟨θ ·, c ·⟩` of the blow-up to the base roots `θ`
under the projection `Sigma.fst`.  They are the bookkeeping that lets the fiberwise count below
split a good blow-up subset into its (forced) planted roots and a free clone choice over the
non-root base vertices. -/

/-- The induced labelled subgraph depends only on the *value* of its vertex set, not on the
particular proof of the root-containment side-condition: equal vertex sets give a definitionally
equal induced subgraph.  Used to transport an "induces `F₀`" hypothesis across an equality of
vertex sets. -/
private theorem indLab_congr {T : Type} [Fintype T] {σ : FlagType T} {V : Type}
    (G : LabeledGraph σ V) {S₁ S₂ : Set V} (hS : S₁ = S₂)
    (h₁ : G.type_verts ⊆ S₁) (h₂ : G.type_verts ⊆ S₂) :
    inducedLabeledSubgraph G S₁ h₁ = inducedLabeledSubgraph G S₂ h₂ := by
  subst hS; rfl

/-- On a good vertex set `S'` (injective projection, containing the planted roots), a vertex `x ∈ S'`
projects onto a *base root* iff `x` itself is a *planted root*.  In other words, within a transversal
the roots upstairs and downstairs correspond exactly, so removing the planted roots from `S'` removes
precisely the base roots from its projection. -/
private theorem mem_baseRoots_iff (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (S' : Finset (Σ v : Fin n, Fin (m v)))
    (hroot : (blowupLabeledGraph m θ c).type_verts.toFinset ⊆ S')
    (hinj : Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))))
    (x : Σ v : Fin n, Fin (m v)) (hxS : x ∈ S') :
    x.fst ∈ (baseLabeledGraph θ).type_verts.toFinset
      ↔ x ∈ (blowupLabeledGraph m θ c).type_verts.toFinset := by
  constructor
  · intro hx
    rw [Set.mem_toFinset, LabeledGraph.mem_type_verts] at hx
    obtain ⟨t, ht⟩ := hx
    have hpr : (⟨θ t, c t⟩ : Σ v, Fin (m v)) ∈ (blowupLabeledGraph m θ c).type_verts.toFinset := by
      rw [Set.mem_toFinset, LabeledGraph.mem_type_verts]; exact ⟨t, rfl⟩
    have hprS : (⟨θ t, c t⟩ : Σ v, Fin (m v)) ∈ S' := hroot hpr
    have hxeq : x = ⟨θ t, c t⟩ := by
      apply hinj hxS hprS
      rw [baseLabeledGraph_type_embed] at ht
      simp only [ht]
    rw [hxeq]; exact hpr
  · intro hx
    rw [Set.mem_toFinset, LabeledGraph.mem_type_verts] at hx
    obtain ⟨t, ht⟩ := hx
    rw [Set.mem_toFinset, LabeledGraph.mem_type_verts]
    refine ⟨t, ?_⟩
    rw [← ht]
    simp only [baseLabeledGraph_type_embed, blowupLabeledGraph_type_embed]

/-- The planted roots `{⟨θ i, c i⟩}` project `Sigma.fst`-injectively: distinct labels `i ≠ j` give
distinct base vertices `θ i ≠ θ j` (as `θ` is an embedding), so each root sits in its own clone
class. -/
private theorem plantedRoots_injOn (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    Set.InjOn Sigma.fst (↑((blowupLabeledGraph m θ c).type_verts.toFinset) : Set (Σ v : Fin n, Fin (m v))) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Set.mem_toFinset, LabeledGraph.mem_type_verts] at ha hb
  obtain ⟨ta, rfl⟩ := ha
  obtain ⟨tb, rfl⟩ := hb
  simp only [blowupLabeledGraph_type_embed] at hab ⊢
  have : θ ta = θ tb := hab
  have htab : ta = tb := θ.injective this
  subst htab; rfl

/-- The projection sends the planted roots exactly onto the base roots: `Sigma.fst` maps
`{⟨θ i, c i⟩ : i}` onto `{θ i : i}`. -/
private theorem plantedRoots_image (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    ((blowupLabeledGraph m θ c).type_verts.toFinset).image Sigma.fst
      = (baseLabeledGraph θ).type_verts.toFinset := by
  ext v
  simp only [Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LabeledGraph.mem_type_verts] at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t, rfl⟩
  · intro hv
    rw [LabeledGraph.mem_type_verts] at hv
    obtain ⟨t, rfl⟩ := hv
    refine ⟨⟨θ t, c t⟩, ?_, rfl⟩
    rw [LabeledGraph.mem_type_verts]
    exact ⟨t, rfl⟩

/-! ## The fiberwise count

The fiber over a base subset `W` is in bijection with the clone choices over the *non-root* vertices
`W ∖ roots` (the planted roots are forced), realised by the inverse pair `S' ↦ S' ∖ roots` and
`Q ↦ Q ∪ roots`.  This reduces the good-event count to `clone_fiber_card`. -/

/-- **Fiber cardinality**: for a base subset `W` (containing the base roots) that induces `F₀`, the
good blow-up subsets whose projection is exactly `W` number `∏_{v ∈ W ∖ roots} m v` — one free clone
choice per non-root vertex of `W`, with the planted roots forced.  Proved by the explicit bijection
`S' ↦ S' ∖ planted-roots` / `Q ↦ Q ∪ planted-roots` with the clone-fiber subsets counted by
`clone_fiber_card`; `good_event_induces_iff` transfers the "induces `F₀`" condition between the
blow-up subset and its projection. -/
private theorem fiber_card (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    {U : Type} [Fintype U] (F₀ : LabeledGraph H U)
    (W : Finset (Fin n))
    (hWroot : (baseLabeledGraph θ).type_verts ⊆ (↑W : Set (Fin n)))
    (hWind : Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑W) hWroot).coe ≃f F₀)) :
    ((Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (hroot : (blowupLabeledGraph m θ c).type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) ∧
        Nonempty ((inducedLabeledSubgraph (blowupLabeledGraph m θ c) (↑S') hroot).coe ≃f F₀))).filter
      (fun S' => S'.image Sigma.fst = W)).card
      = ∏ v ∈ (W \ (baseLabeledGraph θ).type_verts.toFinset), m v := by
  set pr := (blowupLabeledGraph m θ c).type_verts.toFinset with hpr
  set rf := (baseLabeledGraph θ).type_verts.toFinset with hrf
  -- Rewrite RHS as a clone-fiber card.
  rw [← clone_fiber_card (m := m) (W \ rf)]
  -- Now prove the two filtered finsets are equinumerous via card_nbij'.
  refine Finset.card_nbij' (i := fun S' => S' \ pr) (j := fun Q => Q ∪ pr) ?_ ?_ ?_ ?_
  · -- MapsTo (· \ pr) : fiber → clone-fiber
    intro S' hS'
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS'
    obtain ⟨⟨hroot, hinj, _⟩, himg⟩ := hS'
    have hrootF : (blowupLabeledGraph m θ c).type_verts.toFinset ⊆ S' :=
      Set.toFinset_subset.mpr hroot
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · -- InjOn on S' \ pr (mono from S')
      apply hinj.mono
      rw [Finset.coe_subset]
      exact Finset.sdiff_subset
    · -- image of S' \ pr = W \ rf
      rw [show pr = (blowupLabeledGraph m θ c).type_verts.toFinset from rfl,
          show rf = (baseLabeledGraph θ).type_verts.toFinset from rfl]
      -- use the Fact-2 derivation inline
      ext v
      simp only [Finset.mem_image, Finset.mem_sdiff]
      constructor
      · rintro ⟨x, ⟨hxS, hxnr⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [← himg]; exact Finset.mem_image_of_mem _ hxS
        · intro hcontra
          exact hxnr ((mem_baseRoots_iff m θ c S' hrootF hinj x hxS).mp hcontra)
      · rintro ⟨hvW, hvnr⟩
        rw [← himg, Finset.mem_image] at hvW
        obtain ⟨x, hxS, rfl⟩ := hvW
        refine ⟨x, ⟨hxS, ?_⟩, rfl⟩
        intro hcontra
        exact hvnr ((mem_baseRoots_iff m θ c S' hrootF hinj x hxS).mpr hcontra)
  · -- MapsTo (· ∪ pr) : clone-fiber → fiber
    intro Q hQ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hQ
    obtain ⟨hQinj, hQimg⟩ := hQ
    -- basic facts
    have hrf_sub : rf ⊆ W := by
      rw [show rf = (baseLabeledGraph θ).type_verts.toFinset from rfl, Set.toFinset_subset]
      exact hWroot
    have hpr_img : pr.image Sigma.fst = rf := plantedRoots_image m θ c
    have hpr_inj : Set.InjOn Sigma.fst (↑pr : Set (Σ v : Fin n, Fin (m v))) :=
      plantedRoots_injOn m θ c
    -- image of Q ∪ pr is W
    have himgU : (Q ∪ pr).image Sigma.fst = W := by
      rw [Finset.image_union, hQimg, hpr_img, Finset.sdiff_union_of_subset hrf_sub]
    -- disjointness of the two images
    have hdisj : Disjoint (Q.image Sigma.fst) (pr.image Sigma.fst) := by
      rw [hQimg, hpr_img]
      exact Finset.sdiff_disjoint
    -- InjOn on Q ∪ pr
    have hUinj : Set.InjOn Sigma.fst (↑(Q ∪ pr) : Set (Σ v : Fin n, Fin (m v))) := by
      intro a ha b hb hab
      rw [Finset.coe_union, Set.mem_union] at ha hb
      rw [Finset.disjoint_left] at hdisj
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hQinj ha hb hab
      · exact absurd (hab ▸ Finset.mem_image_of_mem _ hb) (hdisj (Finset.mem_image_of_mem _ ha))
      · exact absurd (hab ▸ Finset.mem_image_of_mem _ ha) (hdisj (Finset.mem_image_of_mem _ hb))
      · exact hpr_inj ha hb hab
    -- hroot: planted roots ⊆ Q ∪ pr  (as Set subset)
    have hUroot : (blowupLabeledGraph m θ c).type_verts ⊆ (↑(Q ∪ pr) : Set (Σ v : Fin n, Fin (m v))) := by
      apply Set.toFinset_subset.mp
      rw [show (blowupLabeledGraph m θ c).type_verts.toFinset = pr from rfl]
      exact Finset.subset_union_right
    -- the projection set equals ↑W
    have hπset : Sigma.fst '' (↑(Q ∪ pr) : Set (Σ v : Fin n, Fin (m v))) = (↑W : Set (Fin n)) := by
      rw [← Finset.coe_image, himgU]
    have hπ : (baseLabeledGraph θ).type_verts ⊆ Sigma.fst '' (↑(Q ∪ pr) : Set (Σ v : Fin n, Fin (m v))) := by
      rw [hπset]; exact hWroot
    -- membership in the fiber
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hUroot, hUinj, ?_⟩, himgU⟩
    -- the inducing condition via good_event_induces_iff
    rw [good_event_induces_iff m θ c hUinj hUroot hπ F₀]
    -- transport hWind across the set equality hπset
    rw [indLab_congr (baseLabeledGraph θ) hπset hπ hWroot]
    exact hWind
  · -- LeftInvOn : (S' \ pr) ∪ pr = S' on the fiber
    intro S' hS'
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS'
    obtain ⟨⟨hroot, _, _⟩, _⟩ := hS'
    have hrootF : pr ⊆ S' := by
      rw [show pr = (blowupLabeledGraph m θ c).type_verts.toFinset from rfl]
      exact Set.toFinset_subset.mpr hroot
    exact Finset.sdiff_union_of_subset hrootF
  · -- RightInvOn : (Q ∪ pr) \ pr = Q on the clone-fiber
    intro Q hQ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hQ
    obtain ⟨hQinj, hQimg⟩ := hQ
    have hdisj : Disjoint Q pr := by
      rw [Finset.disjoint_left]
      intro x hxQ hxpr
      have h1 : x.fst ∈ W \ rf := hQimg ▸ Finset.mem_image_of_mem _ hxQ
      have h2 : x.fst ∈ rf := by
        rw [show rf = (baseLabeledGraph θ).type_verts.toFinset from rfl,
            ← plantedRoots_image m θ c]
        exact Finset.mem_image_of_mem _ hxpr
      exact (Finset.mem_sdiff.mp h1).2 h2
    exact Finset.union_sdiff_cancel_right hdisj


/-! ## The good-event count -/

/-- **Good-event count** (`lem:planted-estimate`): the good blow-up subsets inducing `F₀` are
counted by `∑_W ∏_{v ∈ W ∖ roots} m v` over the base subsets `W` (containing the roots) inducing
`F₀`. -/
theorem good_event_count (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    {U : Type} [Fintype U] (F₀ : LabeledGraph H U) :
    (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (hroot : (blowupLabeledGraph m θ c).type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) ∧
        Nonempty ((inducedLabeledSubgraph (blowupLabeledGraph m θ c) (↑S') hroot).coe ≃f F₀))).card
      = ∑ W ∈ (Finset.univ.filter (fun W : Finset (Fin n) =>
          ∃ (hroot : (baseLabeledGraph θ).type_verts ⊆ (↑W : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑W) hroot).coe ≃f F₀))),
        ∏ v ∈ (W \ (baseLabeledGraph θ).type_verts.toFinset), m v := by
  -- Count fiberwise over the base-vertex projection `f S' = S'.image Sigma.fst`.
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ.filter (fun W : Finset (Fin n) =>
          ∃ (hroot : (baseLabeledGraph θ).type_verts ⊆ (↑W : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑W) hroot).coe ≃f F₀))))
        (f := fun S' => S'.image Sigma.fst) ?_]
  · -- each fiber equals the product, via fiber_card
    apply Finset.sum_congr rfl
    intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
    obtain ⟨hWroot, hWind⟩ := hW
    exact fiber_card m θ c F₀ W hWroot hWind
  · -- MapsTo: a good inducing S' projects to a base subset W ∈ t
    intro S' hS'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    obtain ⟨hroot, hinj, hind⟩ := hS'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    -- the projection contains the base roots
    have hπset : Sigma.fst '' (↑S' : Set (Σ v : Fin n, Fin (m v))) = (↑(S'.image Sigma.fst) : Set (Fin n)) := by
      rw [Finset.coe_image]
    have hπ : (baseLabeledGraph θ).type_verts ⊆ Sigma.fst '' (↑S' : Set (Σ v : Fin n, Fin (m v))) := by
      rw [← blowupLabeledGraph_type_verts_image m θ c]
      exact Set.image_mono hroot
    have hWroot : (baseLabeledGraph θ).type_verts ⊆ (↑(S'.image Sigma.fst) : Set (Fin n)) := by
      rw [← hπset]; exact hπ
    refine ⟨hWroot, ?_⟩
    -- the projection induces F₀
    rw [good_event_induces_iff m θ c hinj hroot hπ F₀] at hind
    rwa [indLab_congr (baseLabeledGraph θ) hπset hπ hWroot] at hind


end FlagAlgebras.MetaTheory
