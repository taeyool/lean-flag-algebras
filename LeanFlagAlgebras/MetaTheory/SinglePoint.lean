import LeanFlagAlgebras.MetaTheory.BooleanPoint
import LeanFlagAlgebras.MetaTheory.CertificateCones
import LeanFlagAlgebras.MetaTheory.DenseObstruction

/-! # Degenerate roots collapse to a point (paper §10, `prop:single-point`)

For an **edge-degenerate** hereditary class (every constrained limit has edge density
`0`) the root-planting set at the one-vertex type is a single point — the labelled
empty-graph limit `edgelessPoint` — and the ensemble certificate cone collapses to the
ray `ℝ≥0 · 1₀` of the quotient cone: at the one-vertex type the ensemble relaxation
certifies exactly the density bounds the quotient method does.  Dually for a
**co-edge-degenerate** class, with the labelled complete-graph limit.  So the §9
degeneracy counterexamples (`cor:c4-counterexample`, `cor:degenerate-family`,
`cor:codegenerate`) cost nothing for density bounds.

Layer structure:
* Every flag of an edge-containing (resp. non-complete) unlabelled graph has
  `φ₀`-density `0` under an (co-)edge-degenerate class: expand the two-vertex edge
  (resp. non-edge) flag to the flag's size (`basisVector_quot_eq_sum`) and use positivity
  of the two-vertex density (`flagDensity_unlabelledEdge_pos` /
  `flagDensity_unlabelledNonEdge_pos`).
* Hence, almost surely under every admissible random extension, all non-edgeless (resp.
  non-complete) `vtype`-flags vanish (`ae_nonEdgeless_zero_of_edgeDegenerate` /
  `ae_nonComplete_zero_of_coEdgeDegenerate`).
* `Sσ_eq_singleton_of_edgeDegenerate` / `Sσ_eq_singleton_of_coEdgeDegenerate` —
  `S_vtype = {edgelessPoint}` (resp. `{completePoint}`), given that some constrained
  limit exists (the paper's implicit non-vacuousness; every `φ₀` is admissible at
  `vtype` since `⟦1⟧₀ = 1`).
* `edgeDegenerate_cone_collapse` / `coEdgeDegenerate_cone_collapse`
  (**`prop:single-point`**) — every member of the ensemble cone agrees on all of `Q₀`
  with a non-negative multiple `c • 1₀` of the empty-type unit, which itself lies in the
  quotient cone (`smul_one_mem_quotCone_vtype`): both cones have evaluation image
  `ℝ≥0 · 1₀`.

Deviation from the paper: the paper derives the co-degenerate case by complementation
(`lem:complementation`); here it is proved by a direct symmetric argument, which is
shorter than transporting the cone identity through the complement homeomorphism.  As in
`prop:ideal-zero`, cone equalities are stated in evaluation form (values at every
`φ₀ ∈ Q₀`).
-/

open MeasureTheory SimpleGraph

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## Positivity of the two-vertex densities -/

/-- The unlabelled two-vertex non-edge flag (`⊥` on two vertices). -/
noncomputable def unlabelledNonEdgeFlag : Flag ∅ₜ (Fin 2) := graphFlag ⊥

/-- A graph that is not edgeless has an adjacent pair. -/
private lemma exists_adj_of_ne_bot {V : Type} {G : SimpleGraph V} (hG : G ≠ ⊥) :
    ∃ a b : V, G.Adj a b := by
  by_contra h
  push_neg at h
  refine hG ?_
  ext a b
  simp only [bot_adj, iff_false]
  exact h a b

/-- A graph that is not complete has a distinct non-adjacent pair. -/
private lemma exists_nonadj_of_ne_top {V : Type} {G : SimpleGraph V} (hG : G ≠ ⊤) :
    ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
  by_contra h
  push_neg at h
  refine hG ?_
  ext a b
  simp only [top_adj]
  exact ⟨fun hab => hab.ne, fun hab => h a b hab⟩

/-- Two distinct vertices of `Fin m` force `2 ≤ m`. -/
private lemma two_le_of_ne {m : ℕ} {a b : Fin m} (hab : a ≠ b) : 2 ≤ m := by
  have ha : (a : ℕ) < m := a.isLt
  have hb : (b : ℕ) < m := b.isLt
  have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.val_injective h)
  omega

/-- Every `∅ₜ`-flag is the `graphFlag` of its underlying graph (the type embedding from
`Fin 0` is unique). -/
lemma emptyType_flag_eq_graphFlag {m : ℕ} (L : LabeledGraph ∅ₜ (Fin m)) :
    (⟦L⟧ : Flag ∅ₜ (Fin m)) = graphFlag L.graph := by
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

/-- An edge-containing graph carries the two-vertex edge flag with positive density
(an edge gives an inducing two-vertex subset; via `flagDensity_unlabelledEdge_eq`). -/
lemma flagDensity_unlabelledEdge_pos {m : ℕ} {D : FlagWithSize ∅ₜ m}
    (hD : ¬ IsEdgelessFlag D) : 0 < flagDensity₁ unlabelledEdgeFlag D := by
  induction D using Quotient.inductionOn with
  | _ L =>
  rw [isEdgelessFlag_mk] at hD
  obtain ⟨a, b, hadj⟩ := exists_adj_of_ne_bot hD
  rw [emptyType_flag_eq_graphFlag L, flagDensity_unlabelledEdge_eq L.graph]
  apply div_pos
  · rw [Nat.cast_pos, Finset.card_pos]
    exact ⟨s(a, b), by rw [mem_edgeFinset, mem_edgeSet]; exact hadj⟩
  · rw [Nat.cast_pos]
    exact Nat.choose_pos (two_le_of_ne hadj.ne)

/-- The canonical representative of the unlabelled two-vertex non-edge flag. -/
private def botRep : LabeledGraph ∅ₜ (Fin 2) where
  graph := ⊥
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj (⊥ : SimpleGraph (Fin 2)).Adj

/-- A non-complete graph carries the two-vertex non-edge flag with positive density
(a non-adjacent pair gives an inducing two-vertex subset, via
`flagDensity₁_eq_subset_count_div`). -/
lemma flagDensity_unlabelledNonEdge_pos {m : ℕ} {D : FlagWithSize ∅ₜ m}
    (hD : ¬ IsCompleteFlag D) : 0 < flagDensity₁ unlabelledNonEdgeFlag D := by
  induction D using Quotient.inductionOn with
  | _ L =>
  rw [isCompleteFlag_mk] at hD
  obtain ⟨a, b, hab, hnadj⟩ := exists_nonadj_of_ne_top hD
  have h2m : 2 ≤ m := two_le_of_ne hab
  have hbotrep : unlabelledNonEdgeFlag = (⟦botRep⟧ : Flag ∅ₜ (Fin 2)) := rfl
  rw [hbotrep, flagDensity₁_eq_subset_count_div botRep L]
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero]
  apply div_pos
  · rw [Nat.cast_pos, Finset.card_pos]
    -- the pair `{a, b}` induces the non-edge
    have hsub : L.type_verts ⊆ (↑({a, b} : Finset (Fin m)) : Set (Fin m)) := by
      intro x hx
      obtain ⟨t, -⟩ := LabeledGraph.mem_type_verts.mp hx
      exact Fin.elim0 t
    refine ⟨({a, b} : Finset (Fin m)), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hsub, ?_⟩
    -- the induced graph on `{a, b}` has no edges
    have hbot : (LabeledSubgraph.inducedLabeledSubgraph L
          (↑({a, b} : Finset (Fin m)) : Set (Fin m)) hsub).coe.graph
        = (⊥ : SimpleGraph (↑(↑({a, b} : Finset (Fin m)) : Set (Fin m)))) := by
      ext u v
      simp only [bot_adj, iff_false]
      intro hadj
      have hadj' : u.val ∈ (↑({a, b} : Finset (Fin m)) : Set (Fin m))
          ∧ v.val ∈ (↑({a, b} : Finset (Fin m)) : Set (Fin m))
          ∧ L.graph.Adj u.val v.val := hadj
      obtain ⟨hu, hv, hLuv⟩ := hadj'
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · rw [hu, hv] at hLuv; exact L.graph.irrefl hLuv
      · rw [hu, hv] at hLuv; exact hnadj hLuv
      · rw [hu, hv] at hLuv; exact hnadj hLuv.symm
      · rw [hu, hv] at hLuv; exact L.graph.irrefl hLuv
    -- the pair has exactly two elements, giving the equivalence with `Fin 2`
    have hcard : Fintype.card
        (↑(LabeledSubgraph.inducedLabeledSubgraph L
          (↑({a, b} : Finset (Fin m)) : Set (Fin m)) hsub).subgraph.verts) = 2 := by
      rw [← Set.toFinset_card]
      have htofin : ((LabeledSubgraph.inducedLabeledSubgraph L
          (↑({a, b} : Finset (Fin m)) : Set (Fin m)) hsub).subgraph.verts).toFinset
          = ({a, b} : Finset (Fin m)) := by
        ext x
        rw [Set.mem_toFinset, LabeledSubgraph.inducedLabeledSubgraph_verts]
        simp
      rw [htofin]
      exact Finset.card_pair hab
    have hiso : Nonempty ((LabeledSubgraph.inducedLabeledSubgraph L
          (↑({a, b} : Finset (Fin m)) : Set (Fin m)) hsub).coe.graph ≃g botRep.graph) := by
      rw [hbot]
      exact ⟨{ toEquiv := Fintype.equivFinOfCardEq hcard,
               map_rel_iff' := by simp [botRep] }⟩
    obtain ⟨giso⟩ := hiso
    exact ⟨{ graph_iso := giso, type_preserve := funext fun t => Fin.elim0 t }⟩
  · rw [Nat.cast_pos]
    exact Nat.choose_pos h2m

/-! ## Edge-degeneracy kills every edge-containing unlabelled flag -/

/-- The one-root edge flag unlabels to the unlabelled edge flag. -/
lemma unlabel_edgeFF_eq : unlabel edgeFF.2 = unlabelledEdgeFlag := by
  -- `unlabel ⟦edgeLabeled⟧ = ⟦…⟧` with the same graph `edgeGraph`;
  -- conclude by the refl flag isomorphism (the empty type embeddings agree vacuously).
  show unlabeledGraphQuot edgeLabeled = graphFlag edgeGraph
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

/-- The unlabelled edge `ρ` is the two-vertex unlabelled edge flag on the nose
(`downward_basisVector` with `downwardNormalizingFactor_edge_eq_one`). -/
private lemma rho_eq_unlabelledEdge :
    ρ = (⟦basisVector ⟨2, unlabelledEdgeFlag⟩⟧ : FlagAlgebra ∅ₜ) := by
  show downward (⟦basisVector edgeFF⟧ : FlagAlgebra vtype) = _
  rw [downward_basisVector edgeFF, downwardNormalizingFactor_edge_eq_one, Rat.cast_one,
    one_smul]
  show (⟦basisVector ⟨2, unlabel edgeFF.2⟩⟧ : FlagAlgebra ∅ₜ) = _
  rw [unlabel_edgeFF_eq]

/-- Under an edge-degenerate class, every edge-containing unlabelled flag has density `0`
at every constrained limit.

Proof route: `φ₀ ρ = 0` gives `φ₀ ⟦basisVector ⟨2, unlabelledEdgeFlag⟩⟧ = 0`
(`downward_basisVector`, `unlabel_edgeFF_eq`, `downwardNormalizingFactor_edge_eq_one`).
Vanishing propagates to `D` along the positive density
`flagDensity_unlabelledEdge_pos` (`positiveHom_basisVector_eq_zero`, which performs the
level-`D.1` expansion of the two-vertex edge flag). -/
theorem eval_eq_zero_of_edgeDegenerate (hc : HeredClass) (hdeg : EdgeDegenerate hc)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0)
    {D : FinFlag ∅ₜ} (hD : ¬ IsEdgelessFlag D.2) :
    φ₀ (⟦basisVector D⟧ : FlagAlgebra ∅ₜ) = 0 := by
  have hρ0 : φ₀ ρ = 0 := hdeg φ₀ hφ₀
  have hedge : φ₀ (⟦basisVector ⟨2, unlabelledEdgeFlag⟩⟧ : FlagAlgebra ∅ₜ) = 0 := by
    rw [← rho_eq_unlabelledEdge]
    exact hρ0
  exact positiveHom_basisVector_eq_zero φ₀ (flagDensity_unlabelledEdge_pos hD) hedge

/-- The two-vertex `∅ₜ`-flags are the edge and the non-edge. -/
lemma flagWithSize_two_edgeless_or_complete (D : FlagWithSize ∅ₜ 2) :
    IsEdgelessFlag D ∨ IsCompleteFlag D := by
  -- a simple graph on `Fin 2` is `⊥` or `⊤` according to `Adj 0 1`.
  induction D using Quotient.inductionOn with
  | _ L =>
  by_cases h : L.graph.Adj 0 1
  · right
    rw [isCompleteFlag_mk]
    ext a b
    simp only [top_adj]
    constructor
    · exact fun hab => hab.ne
    · intro hab
      rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with ha | ha <;>
        rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;> rw [ha, hb]
      · exact absurd (ha.trans hb.symm) hab
      · exact h
      · exact h.symm
      · exact absurd (ha.trans hb.symm) hab
  · left
    rw [isEdgelessFlag_mk]
    ext a b
    simp only [bot_adj, iff_false]
    intro hab
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with ha | ha <;>
      rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;> rw [ha, hb] at hab
    · exact L.graph.irrefl hab
    · exact h hab
    · exact h hab.symm
    · exact L.graph.irrefl hab

/-- Under a co-edge-degenerate class, the two-vertex non-edge flag has density `0` at
every constrained limit: the two flags of size `2` sum to `1`
(`sum_positiveHom_basisVector_flagWithSize_eq_one`), and the edge flag alone already
accounts for `φ₀ ρ = 1` (`downwardNormalizingFactor_edge_eq_one`, `unlabel_edgeFF_eq`). -/
lemma nonEdge_eval_eq_zero_of_coEdgeDegenerate (hc : HeredClass)
    (hdeg : CoEdgeDegenerate hc)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0) :
    φ₀ (⟦basisVector ⟨2, unlabelledNonEdgeFlag⟩⟧ : FlagAlgebra ∅ₜ) = 0 := by
  have hρ1 : φ₀ ρ = 1 := hdeg φ₀ hφ₀
  have hedge : φ₀ (⟦basisVector ⟨2, unlabelledEdgeFlag⟩⟧ : FlagAlgebra ∅ₜ) = 1 := by
    rw [← rho_eq_unlabelledEdge]
    exact hρ1
  -- the two size-`2` flags are the edge and the non-edge, and they are distinct
  have hne : unlabelledEdgeFlag ≠ unlabelledNonEdgeFlag := by
    intro hEq
    have hbot : IsEdgelessFlag unlabelledEdgeFlag := by rw [hEq]; exact rfl
    have hbot' : edgeGraph = (⊥ : SimpleGraph (Fin 2)) := hbot
    have hadj : edgeGraph.Adj 0 1 := by
      simp only [edgeGraph, top_adj]
      decide
    rw [hbot'] at hadj
    simp only [bot_adj] at hadj
  have huniv : (Finset.univ : Finset (FlagWithSize ∅ₜ 2))
      = {unlabelledEdgeFlag, unlabelledNonEdgeFlag} := by
    symm
    rw [Finset.eq_univ_iff_forall]
    intro D
    rcases flagWithSize_two_edgeless_or_complete D with hD | hD
    · have hDeq : D = unlabelledNonEdgeFlag := edgelessFlag_unique_emptyType hD rfl
      rw [hDeq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have hDeq : D = unlabelledEdgeFlag := completeFlag_unique_emptyType hD rfl
      rw [hDeq]
      exact Finset.mem_insert_self _ _
  have hsum := sum_positiveHom_basisVector_flagWithSize_eq_one φ₀ 2 (Nat.zero_le 2)
  rw [huniv, Finset.sum_pair hne] at hsum
  linarith only [hsum, hedge]

/-- Under a co-edge-degenerate class, every non-complete unlabelled flag has density `0`
at every constrained limit: the symmetric counterpart of `eval_eq_zero_of_edgeDegenerate`,
propagating the vanishing of the two-vertex non-edge flag along its positive density. -/
theorem eval_eq_zero_of_coEdgeDegenerate (hc : HeredClass) (hdeg : CoEdgeDegenerate hc)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0)
    {D : FinFlag ∅ₜ} (hD : ¬ IsCompleteFlag D.2) :
    φ₀ (⟦basisVector D⟧ : FlagAlgebra ∅ₜ) = 0 :=
  positiveHom_basisVector_eq_zero φ₀ (flagDensity_unlabelledNonEdge_pos hD)
    (nonEdge_eval_eq_zero_of_coEdgeDegenerate hc hdeg hφ₀)

/-! ## Almost-sure vanishing of the non-boolean flags -/

/-- Under every admissible random extension of an edge-degenerate class, almost every
labelled limit vanishes on every non-edgeless flag.

Proof route: for each fixed `F` (`ae_all_iff` over the countable `FinFlag vtype`,
`by_cases` on the hypothesis), the mean of `χ ↦ χ ⟦basisVector F⟧` is
`φ₀ ⟦basisVector F⟧₀ / φ₀ ⟦1⟧₀` (`probMeasure_extend_emptyType_positiveHom_spec`), the
denominator is `1` (`one_downward_vtype`), and the numerator is
`dnf(F.2) · φ₀ ⟦basisVector ⟨F.1, unlabel F.2⟩⟧ = 0` (`downward_basisVector`,
`isEdgelessFlag_unlabel_iff`, `eval_eq_zero_of_edgeDegenerate`).  A non-negative
integrable function of zero mean vanishes a.e. (`integral_eq_zero_iff_of_nonneg`, as in
`forbidden_ae_zero`). -/
lemma ae_nonEdgeless_zero_of_edgeDegenerate (hc : HeredClass) (hdeg : EdgeDegenerate hc)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0)
    (hσ : φ₀ ⟨vtype⟩₀ > 0) :
    ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)),
      ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0 := by
  rw [ae_all_iff]
  intro F
  by_cases hF : IsEdgelessFlag F.2
  · filter_upwards with χ hcon
    exact absurd hF hcon
  · -- the underlying graph contains an edge, hence is killed at `φ₀`
    have hzero0 : φ₀ (⟦basisVector ⟨F.1, unlabel F.2⟩⟧ : FlagAlgebra ∅ₜ) = 0 :=
      eval_eq_zero_of_edgeDegenerate hc hdeg hφ₀ (D := ⟨F.1, unlabel F.2⟩)
        (fun h => hF ((isEdgelessFlag_unlabel_iff F.2).mp h))
    have hdown0 : φ₀ (downward (⟦basisVector F⟧ : FlagAlgebra vtype)) = 0 := by
      rw [downward_basisVector, PositiveHom.map_smul, hzero0, mul_zero]
    set g : PositiveHomSpace vtype → ℝ :=
      fun χ => (PositiveHomSpace.toPosHom χ) ⟦basisVector F⟧ with hg
    have fpos : ∀ χ, 0 ≤ g χ := fun χ => positiveHom_basisVector_ge_zero _ F
    have hint : Integrable g (ℙ[φ₀] : Measure (PositiveHomSpace vtype)) :=
      BoundedContinuousFunction.integrable _
        (BoundedContinuousFunction.mkOfCompact
          (evalContinuousMap (⟦basisVector F⟧ : FlagAlgebra vtype)))
    have hf0 : ∫ χ, g χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)) = 0 := by
      simp only [hg]
      rw [probMeasure_extend_emptyType_positiveHom_spec hσ
        (⟦basisVector F⟧ : FlagAlgebra vtype), hdown0, zero_div]
    have hae := (integral_eq_zero_iff_of_nonneg fpos hint).mp hf0
    filter_upwards [hae] with χ hχ _
    have hχ0 : g χ = 0 := hχ
    rw [← PositiveHomSpace.toPosHom_basisVector]
    exact hχ0

/-- The co-edge-degenerate counterpart of `ae_nonEdgeless_zero_of_edgeDegenerate`:
almost every labelled limit vanishes on every non-complete flag. -/
lemma ae_nonComplete_zero_of_coEdgeDegenerate (hc : HeredClass)
    (hdeg : CoEdgeDegenerate hc)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0)
    (hσ : φ₀ ⟨vtype⟩₀ > 0) :
    ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)),
      ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0 := by
  rw [ae_all_iff]
  intro F
  by_cases hF : IsCompleteFlag F.2
  · filter_upwards with χ hcon
    exact absurd hF hcon
  · -- the underlying graph misses an edge, hence is killed at `φ₀`
    have hzero0 : φ₀ (⟦basisVector ⟨F.1, unlabel F.2⟩⟧ : FlagAlgebra ∅ₜ) = 0 :=
      eval_eq_zero_of_coEdgeDegenerate hc hdeg hφ₀ (D := ⟨F.1, unlabel F.2⟩)
        (fun h => hF ((isCompleteFlag_unlabel_iff F.2).mp h))
    have hdown0 : φ₀ (downward (⟦basisVector F⟧ : FlagAlgebra vtype)) = 0 := by
      rw [downward_basisVector, PositiveHom.map_smul, hzero0, mul_zero]
    set g : PositiveHomSpace vtype → ℝ :=
      fun χ => (PositiveHomSpace.toPosHom χ) ⟦basisVector F⟧ with hg
    have fpos : ∀ χ, 0 ≤ g χ := fun χ => positiveHom_basisVector_ge_zero _ F
    have hint : Integrable g (ℙ[φ₀] : Measure (PositiveHomSpace vtype)) :=
      BoundedContinuousFunction.integrable _
        (BoundedContinuousFunction.mkOfCompact
          (evalContinuousMap (⟦basisVector F⟧ : FlagAlgebra vtype)))
    have hf0 : ∫ χ, g χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)) = 0 := by
      simp only [hg]
      rw [probMeasure_extend_emptyType_positiveHom_spec hσ
        (⟦basisVector F⟧ : FlagAlgebra vtype), hdown0, zero_div]
    have hae := (integral_eq_zero_iff_of_nonneg fpos hint).mp hf0
    filter_upwards [hae] with χ hχ _
    have hχ0 : g χ = 0 := hχ
    rw [← PositiveHomSpace.toPosHom_basisVector]
    exact hχ0

/-! ## The root-planting set is a single point -/

/-- Every base limit is admissible at the one-vertex type: `φ₀ ⟨vtype⟩₀ = 1 > 0`. -/
lemma posHom_vtype_flagType_pos (φ₀ : PositiveHom ∅ₜ) : φ₀ ⟨vtype⟩₀ > 0 := by
  rw [vtype_asEmptyTypeAlgebra_eq_one, PositiveHom.map_one]
  exact one_pos

/-- **`prop:single-point`, edge-degenerate half**: for an edge-degenerate class with at
least one constrained limit, the root-planting set at the one-vertex type is exactly the
labelled empty-graph limit.

Proof route: `⊆` — each admissible support lies in the closed set
`{χ | ∀ F, ¬IsEdgelessFlag F.2 → χ.val F = 0}` (`Measure.support_subset_of_isClosed`
with `ae_nonEdgeless_zero_of_edgeDegenerate`; closedness as in `Qσ_isClosed`), which is
`{edgelessPoint}` by `eq_edgelessPoint_of_nonEdgeless_zero`; pass to the closure.
`⊇` — the support of the extension of the given `φ₀` is non-empty
(`Measure.nonempty_support`, probability measure) and contained in `{edgelessPoint}`,
so `edgelessPoint` lies in one of the supports, hence in `S_vtype`. -/
theorem Sσ_eq_singleton_of_edgeDegenerate (hc : HeredClass) (hdeg : EdgeDegenerate hc)
    (hne : ∃ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0) :
    Sσ (hc.constraintOf vtype) = {edgelessPoint} := by
  have hPclosed : IsClosed {χ : PositiveHomSpace vtype |
      ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0} := by
    have hset : {χ : PositiveHomSpace vtype |
        ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0}
        = ⋂ (F : FinFlag vtype) (_ : ¬ IsEdgelessFlag F.2),
            {χ : PositiveHomSpace vtype | χ.val F = 0} := by
      ext χ
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    refine isClosed_iInter fun F => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((FinFlag.continuous F).comp continuous_subtype_val) continuous_const
  have hPsub : {χ : PositiveHomSpace vtype |
      ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0} ⊆ {edgelessPoint} :=
    fun χ hχ => eq_edgelessPoint_of_nonEdgeless_zero hχ
  have hsupp : ∀ (φ₀ : PositiveHom ∅ₜ),
      posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0 → ∀ (hσ : φ₀ ⟨vtype⟩₀ > 0),
      (ℙ[φ₀] : Measure (PositiveHomSpace vtype)).support
        ⊆ {χ : PositiveHomSpace vtype |
            ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0} :=
    fun φ₀ hφ₀ hσ => Measure.support_subset_of_isClosed hPclosed
      (ae_nonEdgeless_zero_of_edgeDegenerate hc hdeg hφ₀ hσ)
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ isClosed_singleton
    refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
    exact (hsupp φ₀ hφ₀ hσ).trans hPsub
  · rw [Set.singleton_subset_iff]
    obtain ⟨φ₀, hφ₀⟩ := hne
    have hσ : φ₀ ⟨vtype⟩₀ > 0 := posHom_vtype_flagType_pos φ₀
    have hμne : (ℙ[φ₀] : Measure (PositiveHomSpace vtype)) ≠ 0 :=
      IsProbabilityMeasure.ne_zero _
    obtain ⟨χ₀, hχ₀⟩ := Measure.nonempty_support hμne
    have hχeq : χ₀ = edgelessPoint := hPsub (hsupp φ₀ hφ₀ hσ hχ₀)
    rw [← hχeq]
    exact subset_closure (Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ₀,
      Set.mem_iUnion.mpr ⟨hσ, hχ₀⟩⟩⟩)

/-- **`prop:single-point`, co-edge-degenerate half**: for a co-edge-degenerate class with
at least one constrained limit, the root-planting set at the one-vertex type is exactly
the labelled complete-graph limit. -/
theorem Sσ_eq_singleton_of_coEdgeDegenerate (hc : HeredClass) (hdeg : CoEdgeDegenerate hc)
    (hne : ∃ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0) :
    Sσ (hc.constraintOf vtype) = {completePoint} := by
  have hPclosed : IsClosed {χ : PositiveHomSpace vtype |
      ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0} := by
    have hset : {χ : PositiveHomSpace vtype |
        ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0}
        = ⋂ (F : FinFlag vtype) (_ : ¬ IsCompleteFlag F.2),
            {χ : PositiveHomSpace vtype | χ.val F = 0} := by
      ext χ
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    refine isClosed_iInter fun F => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((FinFlag.continuous F).comp continuous_subtype_val) continuous_const
  have hPsub : {χ : PositiveHomSpace vtype |
      ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0} ⊆ {completePoint} :=
    fun χ hχ => eq_completePoint_of_nonComplete_zero hχ
  have hsupp : ∀ (φ₀ : PositiveHom ∅ₜ),
      posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0 → ∀ (hσ : φ₀ ⟨vtype⟩₀ > 0),
      (ℙ[φ₀] : Measure (PositiveHomSpace vtype)).support
        ⊆ {χ : PositiveHomSpace vtype |
            ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0} :=
    fun φ₀ hφ₀ hσ => Measure.support_subset_of_isClosed hPclosed
      (ae_nonComplete_zero_of_coEdgeDegenerate hc hdeg hφ₀ hσ)
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ isClosed_singleton
    refine Set.iUnion_subset fun φ₀ => Set.iUnion_subset fun hφ₀ => Set.iUnion_subset fun hσ => ?_
    exact (hsupp φ₀ hφ₀ hσ).trans hPsub
  · rw [Set.singleton_subset_iff]
    obtain ⟨φ₀, hφ₀⟩ := hne
    have hσ : φ₀ ⟨vtype⟩₀ > 0 := posHom_vtype_flagType_pos φ₀
    have hμne : (ℙ[φ₀] : Measure (PositiveHomSpace vtype)) ≠ 0 :=
      IsProbabilityMeasure.ne_zero _
    obtain ⟨χ₀, hχ₀⟩ := Measure.nonempty_support hμne
    have hχeq : χ₀ = completePoint := hPsub (hsupp φ₀ hφ₀ hσ hχ₀)
    rw [← hχeq]
    exact subset_closure (Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ₀,
      Set.mem_iUnion.mpr ⟨hσ, hχ₀⟩⟩⟩)

/-! ## The cones collapse to the ray `ℝ≥0 · 1₀` -/

/-- Non-negative multiples of the empty-type unit lie in the quotient cone at the
one-vertex type: `c • 1₀ = ⟦(√c • 1) * (√c • 1)⟧₀` (using `one_downward_vtype`). -/
lemma smul_one_mem_quotCone_vtype {c : ℝ} (hc : 0 ≤ c) :
    c • (1 : FlagAlgebra ∅ₜ) ∈ quotCone vtype := by
  refine ⟨(Real.sqrt c • (1 : FlagAlgebra vtype)) * (Real.sqrt c • (1 : FlagAlgebra vtype)),
    IsSumSq.mul_self _, ?_⟩
  have hsq : (Real.sqrt c • (1 : FlagAlgebra vtype)) * (Real.sqrt c • (1 : FlagAlgebra vtype))
      = c • (1 : FlagAlgebra vtype) := by
    rw [smul_mul_smul_comm, Real.mul_self_sqrt hc, mul_one]
  rw [hsq, downward_smul, one_downward_vtype]

/-- **`prop:single-point`, cone form (edge-degenerate)**: over an edge-degenerate class,
every member of the ensemble certificate cone at the one-vertex type agrees on all of
`Q₀` with a non-negative multiple `c • 1₀` of the empty-type unit — and `c • 1₀` lies in
the quotient cone.  At the one-vertex type the ensemble relaxation certifies exactly the
density bounds the quotient method does: both cones collapse to the ray `ℝ≥0 · 1₀`.

Proof route: write `u = ⟦s⟧₀` with `s ≥ 0` on `S_vtype`.  If no constrained limit
exists, take `c := 0` (the evaluation claim is vacuous).  Otherwise
`S_vtype = {edgelessPoint}` (`Sσ_eq_singleton_of_edgeDegenerate`), so
`c := (toPosHom edgelessPoint) s ≥ 0`, and `downward_eval_eq_of_Sσ_singleton` +
`one_downward_vtype` give `φ₀ u = 1 · c` for every `φ₀ ∈ Q₀`. -/
theorem edgeDegenerate_cone_collapse (hc : HeredClass) (hdeg : EdgeDegenerate hc)
    {u : FlagAlgebra ∅ₜ} (hu : u ∈ ensCone (hc.constraintOf vtype)) :
    ∃ c : ℝ, 0 ≤ c ∧ c • (1 : FlagAlgebra ∅ₜ) ∈ quotCone vtype ∧
      ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0 →
        φ₀ u = c := by
  obtain ⟨s, hs, rfl⟩ := hu
  by_cases hex : ∃ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0
  · have hS := Sσ_eq_singleton_of_edgeDegenerate hc hdeg hex
    have hmem : edgelessPoint ∈ Sσ (hc.constraintOf vtype) := by
      rw [hS]
      exact Set.mem_singleton _
    have hc0 : 0 ≤ (PositiveHomSpace.toPosHom edgelessPoint) s := hs edgelessPoint hmem
    refine ⟨(PositiveHomSpace.toPosHom edgelessPoint) s, hc0,
      smul_one_mem_quotCone_vtype hc0, fun φ₀ hφ₀ => ?_⟩
    rw [downward_eval_eq_of_Sσ_singleton (hc.constraintOf vtype) hS s hφ₀,
      one_downward_vtype, PositiveHom.map_one, one_mul]
  · exact ⟨0, le_rfl, smul_one_mem_quotCone_vtype le_rfl,
      fun φ₀ hφ₀ => absurd ⟨φ₀, hφ₀⟩ hex⟩

/-- **`prop:single-point`, cone form (co-edge-degenerate)**: the co-edge-degenerate
counterpart of `edgeDegenerate_cone_collapse`, with the complete-graph limit in place of
the empty-graph limit. -/
theorem coEdgeDegenerate_cone_collapse (hc : HeredClass) (hdeg : CoEdgeDegenerate hc)
    {u : FlagAlgebra ∅ₜ} (hu : u ∈ ensCone (hc.constraintOf vtype)) :
    ∃ c : ℝ, 0 ≤ c ∧ c • (1 : FlagAlgebra ∅ₜ) ∈ quotCone vtype ∧
      ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0 →
        φ₀ u = c := by
  obtain ⟨s, hs, rfl⟩ := hu
  by_cases hex : ∃ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0
  · have hS := Sσ_eq_singleton_of_coEdgeDegenerate hc hdeg hex
    have hmem : completePoint ∈ Sσ (hc.constraintOf vtype) := by
      rw [hS]
      exact Set.mem_singleton _
    have hc0 : 0 ≤ (PositiveHomSpace.toPosHom completePoint) s := hs completePoint hmem
    refine ⟨(PositiveHomSpace.toPosHom completePoint) s, hc0,
      smul_one_mem_quotCone_vtype hc0, fun φ₀ hφ₀ => ?_⟩
    rw [downward_eval_eq_of_Sσ_singleton (hc.constraintOf vtype) hS s hφ₀,
      one_downward_vtype, PositiveHom.map_one, one_mul]
  · exact ⟨0, le_rfl, smul_one_mem_quotCone_vtype le_rfl,
      fun φ₀ hφ₀ => absurd ⟨φ₀, hφ₀⟩ hex⟩

end FlagAlgebras.MetaTheory
