import «LeanFlagAlgebras».PositiveHom
import «LeanFlagAlgebras».MantelTheorem.Downward
import «LeanFlagAlgebras».MantelTheorem.FlagMuls

open FlagAlgebras

namespace MantelTheorem

/- proof of Mantel's theorem -/

def emptyTypeThreeVertexFlagSet : Finset (FlagWithSize ∅ₜ 3) where
  val := [O3_flag, E3_flag, P3_flag, K3_flag]
  nodup := by
    simp
    sorry

example {i : ℕ} (h : i < 0) : False := by
  exact Nat.not_succ_le_zero i h

lemma emptyTypeThreeVertexLabeledGraph_eqv
    (G : LabeledGraph ∅ₜ (Fin 3))
    : G ∼f O3_labeledGraph ∨ G ∼f E3_labeledGraph ∨ G ∼f P3_labeledGraph ∨ G ∼f K3_labeledGraph
  := by
  if h₀₁ : G.graph.Adj 0 1 then
    if h₀₂ : G.graph.Adj 0 2 then
      if h₁₂ : G.graph.Adj 1 2 then -- K3 case
        right; right; right
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [K3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro; split) <;> simp at *
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      else -- P3 case
        right; right; left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [P3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at *)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
    else
      if h₁₂ : G.graph.Adj 1 2 then -- P3 case
        right; right; left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
            invFun := fun i => match i with | 0 => 1 | 1 => 0 | 2 => 2
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [P3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at *)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      else -- E3 case
        right; left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [E3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at *)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
  else
    if h₀₂ : G.graph.Adj 0 2 then
      if h₁₂ : G.graph.Adj 1 2 then -- P3 case
        right; right; left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
            invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [P3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at *)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      else -- E3 case
        right; left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
            invFun := fun i => match i with | 0 => 0 | 1 => 2 | 2 => 1
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [E3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at *)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
    else
      if h₁₂ : G.graph.Adj 1 2 then -- E3 case
        right; left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
            invFun := fun i => match i with | 0 => 2 | 1 => 1 | 2 => 0
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [E3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;>
                (first | assumption | symm; assumption | simp at h)
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at *)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }
      else -- O3 case
        left
        apply Nonempty.intro
        exact {
          graph_iso := {
            toFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            invFun := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 2
            left_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            right_inv := by intro; simp; split <;> (rename_i h; split at h) <;> simp at *
            map_rel_iff' := by
              dsimp [O3_labeledGraph]
              intros; constructor
              · split <;> (intro h; split at h) <;> contradiction
              · split <;> (intro h; split) <;>
                (first | contradiction | symm at h; contradiction | simp at h)
          }
          type_preserve := by
            funext i
            exact False.elim (Nat.not_succ_le_zero i.1 i.2)
        }

lemma emptyTypeThreeVertexFlagSet_eq_univ
    : emptyTypeThreeVertexFlagSet = Finset.univ
  := by
  ext F; constructor
  · intro _
    simp only [Finset.mem_univ]
  · intro _
    simp [emptyTypeThreeVertexFlagSet]
    cases (emptyTypeThreeVertexLabeledGraph_eqv F.out) with
    | inl h₀ =>
      left
      rw [← F.out_eq]
      exact Quotient.sound h₀
    | inr h =>
      cases h with
      | inl h₁ =>
        right; left
        rw [← F.out_eq]
        exact Quotient.sound h₁
      | inr h =>
        cases h with
        | inl h₂ =>
          right; right; left
          rw [← F.out_eq]
          exact Quotient.sound h₂
        | inr h₃ =>
          right; right; right
          rw [← F.out_eq]
          exact Quotient.sound h₃

lemma expand_K2_on_3_vertex_graphs
    : K2 = (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3
  := by
  apply Quotient.sound
  apply flagVectorEqv.trans (unitVector_eqv_densityFlagSum ⟨2, K2_flag⟩ 3 (by simp))
  dsimp [densityFlagSum]
  rw [Finset.sum_eq_multiset_sum, ← emptyTypeThreeVertexFlagSet_eq_univ]
  simp only [emptyTypeThreeVertexFlagSet, Multiset.map_coe, List.map_cons, List.map_nil,
    Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  apply flagVector_eq_eqv
  calc
    _ = (0 : ℝ) • unitVector ⟨3, O3_flag⟩ + ((1 / 3 : ℝ) • unitVector ⟨3, E3_flag⟩ +
        ((2 / 3 : ℝ) • unitVector ⟨3, P3_flag⟩ + (1 : ℝ) • unitVector ⟨3, K3_flag⟩)) := by
      congr <;> simp
    _ = _ := by simp only [add_assoc, zero_smul, zero_add, one_smul]

lemma expand_1_on_3_vertex_graphs
    : 1 = O3 + E3 + P3 + K3
  := by
  apply Quotient.sound
  apply flagVectorEqv.trans (one_vector_eqv_densityFlagSum 3 (by simp))
  dsimp [densityFlagSum]
  calc
    _ ∼v (∑ F' : FlagWithSize ∅ₜ 3, unitVector ⟨3, F'⟩) := by
      apply flagVectorEqv_sum; intros
      rw [finFlag_one_snd, flagDensity_empty]
      simp only [Rat.cast_one, one_smul]
      rfl
    _ ∼v _ := by
      rw [Finset.sum_eq_multiset_sum, ← emptyTypeThreeVertexFlagSet_eq_univ]
      simp only [emptyTypeThreeVertexFlagSet, Multiset.map_coe, List.map_cons, List.map_nil,
        Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
      apply flagVector_eq_eqv
      simp only [add_assoc]

lemma O2₁_minus_K2₁_square_downward
    : ⟦(O2₁ - K2₁) * (O2₁ - K2₁)⟧₀ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3
  := by
  calc
    _ = ⟦O2₁ * O2₁ - (O2₁ * K2₁ + O2₁ * K2₁) + K2₁ * K2₁⟧₀ := by congr; ring
    _ = ⟦O2₁ * O2₁ - 2 • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := by congr; ring
    _ = ⟦O2₁ * O2₁ - (2 : ℝ) • (O2₁ * K2₁) + K2₁ * K2₁⟧₀ := rfl
    _ = ⟦O3₁ + E3₁' - E3₁ - P3₁' + P3₁ + K3₁⟧₀ := by
        congr 1
        simp [mul_O2₁_O2₁, mul_O2₁_K2₁, mul_K2₁_K2₁]
        ring
    _ = ⟦O3₁⟧₀ + ⟦E3₁'⟧₀ - ⟦E3₁⟧₀ - ⟦P3₁'⟧₀ + ⟦P3₁⟧₀ + ⟦K3₁⟧₀ := by simp only [downward_add, downward_sub]
    _ = O3 - ((2 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • E3) - ((2 / 3 : ℝ) • P3 - (1 / 3 : ℝ) • P3) + K3 := by
        simp only [downward_O3₁, downward_E3₁', downward_E3₁, downward_P3₁', downward_P3₁,
          downward_K3₁]
        ring
    _ = O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3 := by
        simp only [← sub_smul]
        norm_num

theorem mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  have h₁ : K2 ≤ (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3 := by rw [expand_K2_on_3_vertex_graphs]
  have h₂ : 0 ≤ (1 / 3 : ℝ) • E3 := by
    apply nonneg_smul_nonneg_geq_zero (by simp)
    apply flag_geq_zero
  have h₃ : 0 ≤ (1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3 := by
    calc
      0 ≤ (1 / 2 : ℝ) • (O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3) := by
          apply nonneg_smul_nonneg_geq_zero (by simp)
          rw [← O2₁_minus_K2₁_square_downward]
          apply square_downward_geq_zero
      _ = _ := by
          simp only [smul_add, smul_sub, smul_smul]
          norm_num
  calc
    _ = K2 + 0 + 0 := by simp only [add_zero]
    _ ≤ ((1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3)
        + (1 / 3 : ℝ) • E3
        + ((1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3) :=
        flag_add_le_add (flag_add_le_add h₁ h₂) h₃
    _ = (1 / 2 : ℝ) • O3
        + ((1 / 3 : ℝ) + (1 / 3 : ℝ) - (1 / 6 : ℝ)) • E3
        + ((2 / 3 : ℝ) - (1 / 6 : ℝ)) • P3
        + (1 / 2 : ℝ) • K3 + K3 := by simp only [add_smul, sub_smul]; ring
    _ = (1 / 2 : ℝ) • O3 + (1 / 2 : ℝ) • E3 + (1 / 2 : ℝ) • P3 + (1 / 2 : ℝ) • K3 + K3 := by norm_num
    _ = (1 / 2 : ℝ) • 1 + K3 := by
        rw [expand_1_on_3_vertex_graphs]
        norm_num

end MantelTheorem
