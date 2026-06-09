import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.Turan.GeneralizedTuran

/-! # From forbidden-subgraph bounds to Turán densities

This file bridges the `forbidLE` reasoning framework with classical extremal graph
theory. It converts a `SimpleGraph` into a flag (`toFinFlag`) and a flag-algebra element
(`toFlagAlgebra`), and proves `generalizedTuranDensity_le_of_forbidLE`: a forbidden
inequality `F.toFlagAlgebra ≤[H.toFinFlag] c • 1` yields the generalized Turán-density
bound `generalizedTuranDensity H F ≤ c`.
-/

open FlagAlgebras GraphAlgebras Filter Topology SimpleGraph

namespace Forbid

/-- The empty-type flag (`FinFlag ∅ₜ`) represented by a finite simple graph `G`,
obtained by labeling it with the empty type. -/
def _root_.SimpleGraph.toFinFlag
    {n : ℕ} (G : SimpleGraph (Fin n)) : FinFlag ∅ₜ
  :=
  let F : FlagWithSize ∅ₜ n := ⟦{
    graph := G,
    type_embed := RelEmbedding.ofIsEmpty _ _
  }⟧
  ⟨n, F⟩

/-- The flag-algebra element `⟦unitVector G.toFinFlag⟧` represented by a finite simple
graph `G`. -/
noncomputable def _root_.SimpleGraph.toFlagAlgebra
    {n : ℕ} (G : SimpleGraph (Fin n)) : FlagAlgebra ∅ₜ
  :=
  ⟦unitVector G.toFinFlag⟧

lemma exists_graphSeq_of_densityLowerBound
    {n m : ℕ} (H : SimpleGraph (Fin n)) (F : SimpleGraph (Fin m))
    {c : ℝ} (hc : 0 ≤ c)
    (a : ℕ → ℕ)
    (hm_le_a : ∀ k : ℕ, m ≤ a k)
    (ha_gt : ∀ k : ℕ, c < (generalizedExtremalNumber (a k) H F / (a k).choose m : ℝ)) :
    ∃ Gseq : (k : ℕ) → SimpleGraph (Fin (a k)),
      (∀ k : ℕ, H.Free (Gseq k)) ∧
      (∀ k : ℕ, c < GraphAlgebras.subgraphDensity F (Gseq k))
  := by
  have hden_pos : ∀ k, (0 : ℝ) < ((a k).choose m : ℝ) := by
    intro k
    exact_mod_cast Nat.choose_pos (hm_le_a k)
  have ha_gt_mul : ∀ k : ℕ,
      c * (a k).choose m < generalizedExtremalNumber (a k) H F := by
    intro k
    exact (lt_div_iff₀ (hden_pos k)).mp (ha_gt k)
  have hnonneg : ∀ k : ℕ, 0 ≤ c * ((a k).choose m : ℝ) := by
    intro k
    exact mul_nonneg hc (by exact_mod_cast Nat.zero_le ((a k).choose m))
  have hG : ∀ k : ℕ,
      ∃ G : SimpleGraph (Fin (a k)),
        H.Free G ∧
        c < GraphAlgebras.subgraphDensity F G := by
    intro k
    let x : ℝ := c * ((a k).choose m : ℝ)
    have hx_floor_lt : Nat.floor x < generalizedExtremalNumber (a k) H F := by
      exact (Nat.floor_lt (hnonneg k)).2 (by simpa [x] using ha_gt_mul k)
    rw [generalizedExtremalNumber] at hx_floor_lt
    rcases Finset.lt_sup_iff.mp hx_floor_lt with ⟨G, hG_mem, hG_lt⟩
    have hG_free : H.Free G := by
      simpa [Finset.mem_filter] using hG_mem
    refine ⟨G, hG_free, ?_⟩
    have hx_lt_floor_succ : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    have hfloor_succ_le_count :
        (Nat.floor x : ℝ) + 1 ≤ (GraphAlgebras.subgraphCount F G : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hG_lt
    simp [GraphAlgebras.subgraphDensity]
    rw [lt_div_iff₀ (hden_pos k)]
    simpa [x] using lt_of_lt_of_le hx_lt_floor_succ hfloor_succ_le_count
  choose Gseq hG_free hG_gt using hG
  exact ⟨Gseq, hG_free, hG_gt⟩

lemma flagDensitySeq_eq_zero_of_free
    {n : ℕ} (H : SimpleGraph (Fin n))
    {a : ℕ → ℕ} (Gseq : (k : ℕ) → SimpleGraph (Fin (a k)))
    (hG_free : ∀ k : ℕ, H.Free (Gseq k))
    (ϕ : ℕ → ℕ)
    : ∀ i, flagDensitySeq ((fun k ↦ (Gseq k).toFinFlag) ∘ ϕ) i H.toFinFlag = 0 := by
  intro i
  dsimp only [flagDensitySeq, toFinFlag, flagDensity₁]
  rw [← @subflagDensity_eq_flagListDensity]
  simp [subflagDensity, labeledGraphDensityLifted, labeledGraphDensity]
  left
  simp [labeledGraphCount]
  rw [@Fintype.card_eq_zero_iff]
  apply Subtype.isEmpty_of_false
  simp
  intro G' hG'_ind
  rw [← Set.univ_eq_empty_iff]
  ext ψ
  simp at ψ
  have hcontains : H ⊑ Gseq (ϕ i) :=
    IsContained.of_exists_iso_subgraph ⟨G'.subgraph, ⟨ψ.graph_iso.symm⟩⟩
  exact False.elim ((hG_free (ϕ i)) hcontains)

lemma flagDensitySpace_eval_toFinFlag_eq_positiveHom_eval_toFlagAlgebra
    {a : FlagDensitySpace ∅ₜ} {φ : PositiveHom ∅ₜ}
    (hφ : φ.coe = a) {n : ℕ} (G : SimpleGraph (Fin n))
    : a G.toFinFlag = φ G.toFlagAlgebra := by
  have hφ_eval : φ.coe G.toFinFlag = a G.toFinFlag := by
    simpa using congrFun (congrArg Subtype.val hφ) G.toFinFlag
  calc
    a G.toFinFlag = φ.coe G.toFinFlag := by simpa using hφ_eval.symm
    _ = φ ⟦unitVector G.toFinFlag⟧ := by simp [PositiveHom.coe_flag]
    _ = φ G.toFlagAlgebra := by rfl

lemma labeledGraphCount_emptyType_eq_subgraphCount
    {n m : ℕ} (F : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : labeledGraphCount
        { graph := F, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj F.Adj }
        { graph := G, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj }
      = subgraphCount F G := by
  classical
  let Flab : LabeledGraph ∅ₜ (Fin n) :=
    { graph := F, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj F.Adj }
  let Glab : LabeledGraph ∅ₜ (Fin m) :=
    { graph := G, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj }
  let e : LabeledSubgraph ∅ₜ Glab ≃ Subgraph G :=
    {
      toFun := fun H => H.subgraph
      invFun := fun H =>
        { subgraph := H
          type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj H.coe.Adj
          embed_eq := by
            intro t
            exact Fin.elim0 t }
      left_inv := by
        intro H
        exact labeledSubgraph_eq_from_subgraph_eq rfl
      right_inv := by
        intro H
        rfl }
  have hpred : ∀ H : LabeledSubgraph ∅ₜ Glab,
      (H.IsInduced ∧ Nonempty (H.coe ≃f Flab)) ↔
      ((e H).IsInduced ∧ Nonempty (Subgraph.coe (e H) ≃g F)) := by
    intro H
    constructor
    · rintro ⟨hInd, hIso⟩
      refine ⟨hInd, ?_⟩
      rcases hIso with ⟨φ⟩
      exact ⟨φ.graph_iso⟩
    · rintro ⟨hInd, hIso⟩
      refine ⟨hInd, ?_⟩
      rcases hIso with ⟨φ⟩
      refine ⟨{ graph_iso := φ, type_preserve := ?_ }⟩
      ext t
      exact Fin.elim0 t
  let S0 := {H : LabeledSubgraph ∅ₜ Glab | H.IsInduced ∧ Nonempty (H.coe ≃f Flab)}
  let S1 := {H : Subgraph G | H.IsInduced ∧ Nonempty (Subgraph.coe H ≃g F)}
  let eSet : S0 ≃ S1 :=
    {
      toFun := fun H => ⟨e H.1, (hpred H.1).1 H.2⟩
      invFun := by
        intro H
        rcases H with ⟨H, hH⟩
        refine ⟨e.symm H, (hpred (e.symm H)).2 ?_⟩
        simpa using hH
      left_inv := by
        intro H
        apply Subtype.ext
        simp
      right_inv := by
        intro H
        apply Subtype.ext
        simp }
  show S0.toFinset.card = S1.toFinset.card
  have card_eq : Fintype.card S0 = Fintype.card S1 := Fintype.card_congr eSet
  simp_all only [Set.toFinset_card]

lemma subgraphDensity_eq_flagDensity₁
    {n m : ℕ} (F : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphDensity F G = flagDensity₁ F.toFinFlag.2 G.toFinFlag.2
  := by
  dsimp [flagDensity₁]
  rw [← @subflagDensity_eq_flagListDensity]
  simp [toFinFlag]
  change subgraphDensity F G =
    labeledGraphDensity
      { graph := F, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj F.Adj }
      { graph := G, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj }
  simp [subgraphDensity, labeledGraphDensity, labeledGraphCount_emptyType_eq_subgraphCount,
    LabeledGraph.size]

/-- Turán-density bridge: a forbidden inequality `F.toFlagAlgebra ≤[H.toFinFlag] c • 1`
(with `0 ≤ c`) implies the generalized Turán-density bound
`generalizedTuranDensity H F ≤ c`. -/
theorem generalizedTuranDensity_le_of_forbidLE
    {n m : ℕ} {H : SimpleGraph (Fin n)} {F : SimpleGraph (Fin m)}
  {c : ℝ} (hc : 0 ≤ c) (h : F.toFlagAlgebra ≤[H.toFinFlag] c • 1)
    : generalizedTuranDensity H F ≤ c
  := by
  rw [← forbidLE_emptyType_iff_forbidLE] at h
  dsimp [forbidLE_emptyType] at h

  let f_den : ℕ → ℝ := fun k ↦ (generalizedExtremalNumber k H F / k.choose m : ℝ)
  suffices hε : ∀ ε > 0, ∀ᶠ k in atTop, f_den k ≤ c + ε by
    refine le_iff_forall_pos_le_add.mpr ?_
    intro ε hε_pos
    refine le_of_tendsto_of_tendsto ?_ (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c + ε) atTop (𝓝 (c + ε))) (hε ε hε_pos)
    simpa [f_den] using (tendsto_generalizedTuranDensity H F)

  contrapose h
  push_neg at h ⊢
  obtain ⟨ε, hε_pos, hε⟩ := h
  obtain ⟨a₀, ha₀_inc, ha_gt₀⟩ := extraction_of_frequently_atTop hε
  let a : ℕ → ℕ := fun k ↦ a₀ (k + m)
  have ha_inc : StrictMono a := by
    intro k l hkl
    exact ha₀_inc (Nat.add_lt_add_right hkl m)
  have ha_gt : ∀ k : ℕ, c + ε < f_den (a k) := by
    intro k
    simpa [a] using (ha_gt₀ (k + m))
  have hm_le_a : ∀ k : ℕ, m ≤ a k := by
    intro k
    exact le_trans (Nat.le_add_left m k) (ha₀_inc.id_le (k + m))
  clear hε ha₀_inc ha_gt₀

  have hcε : 0 ≤ c + ε := add_nonneg hc (le_of_lt hε_pos)
  obtain ⟨Gseq, hG_free, hG_den⟩ := exists_graphSeq_of_densityLowerBound H F hcε a hm_le_a ha_gt
  let gseq : FlagSeq ∅ₜ := fun k ↦ (Gseq k).toFinFlag
  have hgseq_inc : Increases gseq := by
    intro k l hkl
    simp [gseq, toFinFlag]
    exact Nat.lt_of_succ_le (ha_inc hkl)
  obtain ⟨x, ϕ, hϕ_mono, hϕ_conv'⟩ := increasing_flagSeq_contain_convergent_subseq gseq hgseq_inc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (gseq ∘ ϕ) hϕ_conv'
  obtain ⟨hϕ_inc, hϕ_conv⟩ := flagSeq_convergesTo_iff.mp hϕ_conv'
  clear hcε hgseq_inc hϕ_inc hϕ_conv'

  use φ
  constructor
  · apply @tendsto_nhds_unique _ _ _ _
      (fun n ↦ flagDensitySeq (gseq ∘ ϕ) n H.toFinFlag) atTop
    · simpa [flagDensitySpace_eval_toFinFlag_eq_positiveHom_eval_toFlagAlgebra hφ H]
        using (hϕ_conv H.toFinFlag)
    · have hH_den_zero : ∀ n, flagDensitySeq (gseq ∘ ϕ) n H.toFinFlag = 0 := by
        simpa [gseq] using flagDensitySeq_eq_zero_of_free H Gseq hG_free ϕ
      rw [tendsto_congr hH_den_zero, tendsto_const_nhds_iff]
  · simp [PositiveHom.map_smul]
    calc
      c < c + ε := lt_add_of_pos_right c hε_pos
      _ ≤ φ F.toFlagAlgebra := by
        have hF_tendsto :
            Tendsto (fun n ↦ flagDensitySeq (gseq ∘ ϕ) n F.toFinFlag)
              atTop (nhds (φ F.toFlagAlgebra)) := by
          simpa [flagDensitySpace_eval_toFinFlag_eq_positiveHom_eval_toFlagAlgebra hφ F]
            using (hϕ_conv F.toFinFlag)
        apply le_of_tendsto_of_tendsto'
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c + ε) atTop (𝓝 (c + ε))) hF_tendsto
        intro k
        specialize hG_den (ϕ k)
        dsimp [flagDensitySeq]
        rw [← subgraphDensity_eq_flagDensity₁]
        exact le_of_lt hG_den

end Forbid
