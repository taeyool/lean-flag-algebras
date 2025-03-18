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

lemma labeledSubgraphListDensityLifted_respects_eqv
    (H_list H_list' : ∀ (i : Fin t), LabeledGraph σ (V i)) (φ : ∀ (i : Fin t), H_list i ≃f H_list' i) (G : Flag σ W)
    : labeledSubgraphListDensityLifted H_list G = labeledSubgraphListDensityLifted H_list' G
  :=
  sorry

namespace Fin

@[simps]
def coe {s t : ℕ} (hst : s ≤ t) (i : Fin s) : Fin t where
  val := i.val
  isLt := Nat.lt_of_lt_of_le i.is_lt hst

end Fin

noncomputable def subflagDensityList_partiallyLifted
    {s : ℕ} (hst : s ≤ t)
    (F_list : ∀ (i : Fin s), Flag σ (V (i.coe hst)))
    (H_list : ∀ (i : Fin (t - s)), Flag σ (V ⟨i.val + s, sorry⟩))
    : Flag σ W → ℚ
  :=
  sorry

noncomputable def subflagDensityList
    : (∀ (i : Fin t), Flag σ (V i)) → Flag σ W → ℚ
  := by
  induction t with
  | zero => exact fun _ _ ↦ 0
  | succ t ih =>
      sorry

end
