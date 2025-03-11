import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic

variable {T : Type} [Fintype T] {σ : FlagType T}

variable {V W : Type}
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

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
  let σ_size := Fintype.card T
  let H_size := Fintype.card V
  let G_size := Fintype.card W
  let num_of_all_induced_subgraph := (G_size - σ_size).choose (H_size - σ_size)
  labeledSubgraph_cnt / num_of_all_induced_subgraph

lemma labeledSubgraphDensity_respects_eqv_on_G
    (H : LabeledGraph σ V) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphDensity H G = labeledSubgraphDensity H G'
  :=
  sorry

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

noncomputable def labeledSubgraphListCount
    {ι : Type} [Fintype ι] {V : ι → Type}
    (H_list : ∀ (i : ι), LabeledGraph σ (V i)) (G : LabeledGraph σ W) : ℕ
  :=
  let p₁ (G_list : ∀ (_ : ι), LabeledSubgraph σ G) : Prop
    := ∀ (i : ι), (G_list i).IsInduced ∧ Nonempty ((G_list i).coe ≃f H_list i)
  let p₂ (G_list : ∀ (_ : ι), LabeledSubgraph σ G) : Prop
    := ∀ (i j : ι), i ≠ j → (G_list i).subgraph.verts ∩ (G_list j).subgraph.verts = ∅
  let S := { G_list : ∀ (_ : ι), LabeledSubgraph σ G | p₁ G_list ∧ p₂ G_list }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card
