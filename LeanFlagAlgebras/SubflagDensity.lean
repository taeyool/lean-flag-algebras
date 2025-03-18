import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic

variable {T : Type} [Fintype T] {σ : FlagType T}

section

variable {V W T: Type}
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  [Fintype T] [DecidableEq T]

noncomputable def labeledSubgraphCount
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℕ
  :=
  let p (G' : LabeledSubgraph σ G) : Prop := G'.IsInduced ∧ Nonempty (G'.coe ≃f H)
  let S := { G' : LabeledSubgraph σ G | p G' }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card

noncomputable def labeledSubgraphDensity
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℚ
  :=
  let labeledSubgraph_cnt := labeledSubgraphCount H G
  let num_of_all_induced_subgraph := (G.size - σ.size).choose (H.size - σ.size)
  labeledSubgraph_cnt / num_of_all_induced_subgraph

noncomputable def isoSetOfInducedlabeledSubgraphIsoH
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ T)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
      ≃
      { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  := sorry

lemma labeledSubgraphDensity_respects_eqv_on_G
    (H : LabeledGraph σ T) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphDensity H G = labeledSubgraphDensity H G'
  := by
  dsimp [labeledSubgraphDensity]
  let S₀ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let S₁ := { G' : LabeledSubgraph σ G | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    dsimp [S₀, S₁]
    have := isoSetOfInducedlabeledSubgraphIsoH φ H
    rfl
  simp at h_iso_S₀_S₁
  have hS₀ : Fintype S₀ := sorry
  have hS₁ : Fintype S₁ := sorry
  have h_count : labeledSubgraphCount H G = labeledSubgraphCount H G' := by
    dsimp [labeledSubgraphCount]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp
    sorry
  rw [h_count]
  rfl

noncomputable def labeledSubgraphDensityLifted
    (H : LabeledGraph σ V) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ W => labeledSubgraphDensity H G)
  intro _ _ G_eqv
  exact labeledSubgraphDensity_respects_eqv_on_G H (Classical.choice G_eqv)

lemma labeledSubgraphDensityLifted_respects_eqv
    (H H' : LabeledGraph σ V) (φ : H ≃f H') (G : Flag σ W)
    : labeledSubgraphDensityLifted H G = labeledSubgraphDensityLifted H' G
  :=
  sorry

noncomputable def subflagDensity
    : Flag σ V → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphDensityLifted
  intro H H' H_eqv
  ext G
  exact labeledSubgraphDensityLifted_respects_eqv H H' (Classical.choice H_eqv) G

end

section

variable {t : ℕ} {V : Fin t → Type} [FintypeList V] [DecidableEqList V]
  {W : Type} [Fintype W] [DecidableEq W]
  {U : Type} [Fintype U] [DecidableEq U]

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ t V) (G : LabeledGraph σ W) : ℕ
  :=
  let p₁ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (Gl i).IsInduced ∧ Nonempty ((Gl i).coe ≃f Hl i)
  let p₂ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅
  let S := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | p₁ Gl ∧ p₂ Gl }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card

def multinomialCoefficient
    (r_list : Fin t → ℕ) (n : ℕ) : ℕ
  :=
  let r_sum := ∑ i : Fin t, r_list i
  if _ : n ≥ r_sum then
    Nat.factorial n / (∏ i : Fin t, Nat.factorial (r_list i)) / Nat.factorial (n - r_sum)
  else 0

noncomputable def labeledSubgraphListDensity
    (Hl : LabeledGraphList σ t V) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list := fun (i : Fin t) ↦ (Hl i).size - σ.size
  labeledSubgraphListCount Hl G / multinomialCoefficient r_list G.size

lemma labeledSubgraphListDensity_respects_eqv_on_G
    (Hl : LabeledGraphList σ t V) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphListDensity Hl G = labeledSubgraphListDensity Hl G'
  :=
  sorry

noncomputable def labeledSubgraphListDensityLifted
    (Hl : LabeledGraphList σ t V) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G => labeledSubgraphListDensity Hl G)
  intro _ _ h_eqv
  exact labeledSubgraphListDensity_respects_eqv_on_G Hl (Classical.choice h_eqv)

lemma labeledSubgraphListDensityLifted_respects_eqv
    (Hl Hl' : LabeledGraphList σ t V) (φ : ∀ (i : Fin t), Hl i ≃f Hl' i) (G : Flag σ W)
    : labeledSubgraphListDensityLifted Hl G = labeledSubgraphListDensityLifted Hl' G
  :=
  sorry

noncomputable def QuotLabeledSubgraphListDensity
    : QuotlabeledGraphList σ t V → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphListDensityLifted
  intro Hl Hl' Hl_eqv
  ext G
  have φ : ∀ (i : Fin t), Hl i ≃f Hl' i := by
    intro i
    exact Classical.choice (Hl_eqv i)
  exact labeledSubgraphListDensityLifted_respects_eqv Hl Hl' φ G

noncomputable def FlagListDensity
    : FlagList σ t V → Flag σ W → ℚ
  :=
  fun Fl ↦ QuotLabeledSubgraphListDensity Fl.coe

example (F : Flag σ U) (G : Flag σ W) : subflagDensity F G = FlagListDensity F.toSingletonList G := sorry

end
