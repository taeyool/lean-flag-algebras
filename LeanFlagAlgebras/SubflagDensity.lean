import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic

variable {T : Type} [Fintype T] {σ : FlagType T}

section

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
  let num_of_all_induced_subgraph := (G.size - σ.size).choose (H.size - σ.size)
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

end

section

class FintypeList {t : ℕ} (V : Fin t → Type) where
  fintype_all : ∀ (i : Fin t), Fintype (V i)

class DecidableEqList {t : ℕ} (V : Fin t → Type) where
  decidable_eq_all : ∀ (i : Fin t), DecidableEq (V i)

instance fintype_V {t : ℕ} (V : Fin t → Type) [FintypeList V] (i : Fin t) : Fintype (V i)
  :=
  FintypeList.fintype_all i

instance decidable_eq_V {t : ℕ} (V : Fin t → Type) [DecidableEqList V] (i : Fin t) : DecidableEq (V i)
  :=
  DecidableEqList.decidable_eq_all i

variable {t : ℕ} {V : Fin t → Type} [FintypeList V] [DecidableEqList V]
  {W : Type} [Fintype W] [DecidableEq W]

noncomputable def labeledSubgraphListCount
    (H_list : ∀ (i : Fin t), LabeledGraph σ (V i)) (G : LabeledGraph σ W) : ℕ
  :=
  let p₁ (G_list : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (G_list i).IsInduced ∧ Nonempty ((G_list i).coe ≃f H_list i)
  let p₂ (G_list : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → (G_list i).subgraph.verts ∩ (G_list j).subgraph.verts = ∅
  let S := { G_list : ∀ (_ : Fin t), LabeledSubgraph σ G | p₁ G_list ∧ p₂ G_list }
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
    (H_list : ∀ (i : Fin t), LabeledGraph σ (V i)) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list := fun (i : Fin t) ↦ (H_list i).size - σ.size
  labeledSubgraphListCount H_list G / multinomialCoefficient r_list G.size

lemma labeledSubgraphListDensity_respects_eqv_on_G
    (H_list : ∀ (i : Fin t), LabeledGraph σ (V i)) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphListDensity H_list G = labeledSubgraphListDensity H_list G'
  :=
  sorry

noncomputable def labeledSubgraphListDensityLifted
    (H_list : ∀ (i : Fin t), LabeledGraph σ (V i)) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G => labeledSubgraphListDensity H_list G)
  intro _ _ h_eqv
  exact labeledSubgraphListDensity_respects_eqv_on_G H_list (Classical.choice h_eqv)

end
