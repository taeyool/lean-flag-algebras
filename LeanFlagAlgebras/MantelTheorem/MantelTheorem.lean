import «LeanFlagAlgebras».FlagAlgebra.RandomHom
import «LeanFlagAlgebras».MantelTheorem.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

open FlagAlgebras Compute
open SimpleGraph
open Filter

namespace MantelTheorem

theorem Mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  have h₁ : K2 ≤ (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3 := by rw [expand_K2_on_three_vertex_graphs]
  have h₂ : 0 ≤ (1 / 3 : ℝ) • E3 :=
    nonneg_smul_nonneg_geq_zero (by linarith) (flag_geq_zero _)
  have h₃ : 0 ≤ (1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3 := by
    calc
      0 ≤ (1 / 2 : ℝ) • (O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3) := by
          apply nonneg_smul_nonneg_geq_zero (by simp)
          rw [← O2₁_minus_K2₁_square_downward]
          apply square_downward_nonneg
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
        rw [expand_1_on_three_vertex_graphs]
        norm_num

theorem Mantel_theorem'
    : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ K2 ≤ 1 / 2
  := by
  intro φ h
  simpa [φ.map_add, φ.map_sub, φ.map_smul, φ.map_one, h] using Mantel_theorem φ

example : Sym2Graph_3_0_0_3.toLabeledGraph.graph = completeGraph (Fin 3) := by
  ext v w
  simp [Sym2Graph.toLabeledGraph]
  fin_cases v <;> fin_cases w <;> decide

def SimpleGraph.blow_up
    {V : Type} (G : SimpleGraph V) (n : ℕ)
    : SimpleGraph (Fin n × V) where
  Adj x y := G.Adj x.2 y.2
  symm := by
    intro x y hxy
    exact hxy.symm
  loopless := by
    intro x hxx
    exact G.loopless x.2 hxx

lemma extremal_density_K3_ge
    (n : ℕ) (hn2 : n ≥ 2)
    : (extremalNumber n (completeGraph (Fin 3)) / n.choose 2 : ℝ) ≥ 1 / 2
  := by
  classical
  have h_even_case :
      ∀ m, Even m → m ≥ 2 →
        (extremalNumber m (completeGraph (Fin 3)) / m.choose 2 : ℝ) ≥ 1 / 2 := by
    rintro m ⟨k, rfl⟩ _
    have hk1 : k ≥ 1 := by linarith
    have hchoose_pos : (0 : ℝ) < (k + k).choose 2 := by
      exact_mod_cast Nat.choose_pos (by linarith)
    rw [ge_iff_le, le_div_iff₀ hchoose_pos, ← ge_iff_le, mul_comm]
    let K : SimpleGraph (Fin k ⊕ Fin k) := completeBipartiteGraph (Fin k) (Fin k)
    have hK_free : (completeGraph (Fin 3)).Free K := by
      haveI : Nonempty (Fin k) := ⟨⟨0, by linarith⟩⟩
      have hK_cliqueFree3 : K.CliqueFree 3 := by
        apply cliqueFree_of_chromaticNumber_lt
        have hχ : K.chromaticNumber = 2 := by
          simpa [K] using (CompleteBipartiteGraph.chromaticNumber (V := Fin k) (W := Fin k))
        rw [hχ]
        norm_num
      have hK_top_free : (⊤ : SimpleGraph (Fin 3)).Free K := by
        simpa using (cliqueFree_iff_top_free (G := K) (β := Fin 3)).1 hK_cliqueFree3
      simpa [completeGraph_eq_top] using hK_top_free
    have hK_le_nat : K.edgeFinset.card ≤ extremalNumber (k + k) (completeGraph (Fin 3)) := by
      simpa [K, Fintype.card_sum, Fintype.card_fin] using
        (card_edgeFinset_le_extremalNumber (V := Fin k ⊕ Fin k) (H := completeGraph (Fin 3))
          (G := K) hK_free)
    have hK_edges : K.edgeFinset.card = k * k := by
      let e : (Fin k ⊕ Fin k) ≃ (Fin 2 × Fin k) :=
        { toFun := fun x =>
            match x with
            | Sum.inl i => (0, i)
            | Sum.inr i => (1, i)
          invFun := fun x =>
            if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
          left_inv := by
            intro x
            cases x <;> simp
          right_inv := by
            intro x
            rcases x with ⟨i, j⟩
            fin_cases i <;> simp }
      have hIso : K ≃g completeEquipartiteGraph 2 k := by
        refine ⟨e, ?_⟩
        intro a b
        cases a <;> cases b <;> simp [K, e, completeEquipartiteGraph]
      have hEq : K.edgeFinset.card = (completeEquipartiteGraph 2 k).edgeFinset.card := by
        simpa using hIso.card_edgeFinset_eq
      rw [hEq, card_edgeFinset_completeEquipartiteGraph]
      simp [pow_two]
    have hK_edges' : (K.edgeFinset.card : ℝ) ≥ ((k + k).choose 2) / 2 := by
      rw [hK_edges]
      have hk_formula : (((k + k).choose 2 : ℕ) : ℝ) = (k + k : ℝ) * ((k + k : ℝ) - 1) / 2 := by
        simpa using (Nat.cast_choose_two (K := ℝ) (a := k + k))
      calc
        _ = (k : ℝ) * k := by norm_num
        _ ≥ ((k + k).choose 2) / 2 := by nlinarith [hk_formula]
    calc
      _ ≥ (K.edgeFinset.card : ℝ) := by simpa using hK_le_nat
      _ ≥ ((k + k).choose 2) * (1 / 2) := by simpa using hK_edges'
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · exact h_even_case n hn_even hn2
  · have hn2_succ : n + 1 ≥ 2 := le_trans hn2 (Nat.le_succ n)
    have h_next : (extremalNumber (n + 1) (completeGraph (Fin 3)) / (n + 1).choose 2 : ℝ) ≥ 1 / 2 :=
      h_even_case (n + 1) hn_odd.add_one hn2_succ
    apply le_trans h_next
    have hmono := antitoneOn_extremalNumber_div_choose_two (completeGraph (Fin 3))
    simpa using hmono hn2 hn2_succ

theorem Turan_density_K3
    : turanDensity (completeGraph (Fin 3)) = 1 / 2
  := by
  let f : ℕ → ℝ := fun n ↦ extremalNumber n (completeGraph (Fin 3)) / n.choose 2
  suffices h_target : Filter.Tendsto f Filter.atTop (nhds (1 / 2 : ℝ)) by
    exact tendsto_nhds_unique (tendsto_turanDensity (completeGraph (Fin 3))) h_target
  rw [Metric.tendsto_atTop']
  by_contra h
  push_neg at h
  obtain ⟨ε, hε, h⟩ := h
  classical
  choose g hg using h
  let n : ℕ → ℕ := Nat.rec (g 1) (fun _ m => g m)
  have hsucc : ∀ k : ℕ, n k < n (k + 1) := by
    intro k
    exact (hg (n k)).1
  have hn2 : ∀ k : ℕ, 2 ≤ n k := by
    intro k
    induction k with
    | zero =>
        exact Nat.succ_le_of_lt (by simpa [n] using (hg 1).1)
    | succ k ih =>
        exact le_trans ih (Nat.le_of_lt (hsucc k))
  have hdist : ∀ k : ℕ, ε ≤ dist (f (n k)) (1 / 2) := by
    intro k
    cases k with
    | zero => exact (by simpa [n] using (hg 1).2)
    | succ k => exact (hg (n k)).2
  have hf_ge : ∀ k : ℕ, f (n k) ≥ 1 / 2 + ε := by
    intro k
    have hlow : (1 / 2 : ℝ) ≤ f (n k) := by
      simpa [ge_iff_le] using extremal_density_K3_ge (n k) (hn2 k)
    have hε' : ε ≤ f (n k) - 1 / 2 := by
      calc
        ε ≤ dist (f (n k)) (1 / 2 : ℝ) := hdist k
        _ = |f (n k) - 1 / 2| := by rw [Real.dist_eq]
        _ = f (n k) - 1 / 2 := abs_of_nonneg (sub_nonneg.mpr hlow)
    linarith
  dsimp [f] at hf_ge

  choose G hG_dec hG_ext using
    (fun (k : ℕ) ↦ by
      exact exists_isExtremal_free (V := Fin (n k)) (H := completeGraph (Fin 3)) (by simp))
  have hG_free : ∀ (k : ℕ), (completeGraph (Fin 3)).Free (G k) := by
    intro k
    exact (hG_ext k).1
  letI (k : ℕ) : Fintype (G k).edgeSet :=
    @fintypeEdgeSet (Fin (n k)) (G k) (@Sym2.instFintype _ (Fin.fintype (n k))) (hG_dec k)
  have hG_edge_ge : ∀ (k : ℕ), ((G k).edgeFinset.card : ℝ) / (n k).choose 2 ≥ 1 / 2 + ε := by
    intro k
    specialize hf_ge k
    specialize hG_ext k
    refine ge_trans (ge_of_eq ?_) hf_ge
    congr
    rw [@isExtremal_free_iff] at hG_ext
    simp_all

  let lG (k : ℕ) : LabeledGraph ∅ₜ (Fin (n k)) := {
    graph := G k
    type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj (G k).Adj
  }
  let F (k : ℕ) : Flag ∅ₜ (Fin (n k)) := ⟦lG k⟧
  have hF_free : ∀ (k : ℕ),
      @flagDensity₁ _ _ _ (Fin.fintype (n k)) (instDecidableEqFin (n k)) _ _ _ _ K3_flag (F k) = 0 := by
    sorry
  have hF_edge : ∀ (k : ℕ),
      @flagDensity₁ _ _ _ (Fin.fintype (n k)) (instDecidableEqFin (n k)) _ _ _ _ K2_flag (F k) =
        ((G k).edgeFinset.card : ℝ) / (n k).choose 2 := by
    sorry
  have hF_edge_ge : ∀ (k : ℕ),
      @flagDensity₁ _ _ _ (Fin.fintype (n k)) (instDecidableEqFin (n k)) _ _ _ _ K2_flag (F k) ≥ 1 / 2 + ε := by
    intro k
    rw [hF_edge k]
    exact hG_edge_ge k

  sorry

end MantelTheorem
