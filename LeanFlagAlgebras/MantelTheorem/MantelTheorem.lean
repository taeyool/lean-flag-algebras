import LeanFlagAlgebras.MantelTheorem.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-! # Mantel's theorem (Turán density of `K₃`)

The headline file of the Mantel's theorem development. It proves, via the
flag-algebra square-positivity certificate from `Lemmas.lean`:

* `Mantel_theorem` / `Mantel_theorem'` — the flag-algebra density inequality
  `K2 ≤ (1/2)·1 + K3`, i.e. any triangle-free graph has edge density `≤ 1/2`;
* `Turan_density_K3 : turanDensity (completeGraph (Fin 3)) = 1 / 2` — the
  classical Turán-density statement, obtained by transferring the flag-algebra
  bound to extremal numbers and matching it with the complete-bipartite
  lower-bound construction (`extremal_density_K3_ge`). -/

open FlagAlgebras Compute
open SimpleGraph
open Filter

namespace MantelTheorem

/-- Mantel's theorem in flag-algebra form: the edge-density basis element `K2`
is bounded by `(1/2)·1 + K3`. Equivalently, the triangle density controls how
far the edge density can exceed `1/2`. -/
theorem Mantel_theorem
  : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  dsimp only [K2, K3]
  have h₁ : FlagAlgebra_2_0_0_1 ≤ (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
      + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3 := by
    rw [expand_K2_on_three_vertex_graphs]
  have h₂ : 0 ≤ (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 :=
    nonneg_smul_nonneg_geq_zero (by linarith) (flag_geq_zero _)
  have h₃ : 0 ≤ (1 / 2 : ℝ) • FlagAlgebra_3_0_0_0
      - (1 / 6 : ℝ) • FlagAlgebra_3_0_0_1 - (1 / 6 : ℝ) • FlagAlgebra_3_0_0_2
      + (1 / 2 : ℝ) • FlagAlgebra_3_0_0_3 := by
    calc
      0 ≤ (1 / 2 : ℝ) • (FlagAlgebra_3_0_0_0 - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
          - (1 / 3 : ℝ) • FlagAlgebra_3_0_0_2 + FlagAlgebra_3_0_0_3) := by
          apply nonneg_smul_nonneg_geq_zero (by simp)
          rw [← FlagAlgebra_2_1_0_0_minus_FlagAlgebra_2_1_0_1_square_downward]
          apply square_downward_nonneg
      _ = _ := by
          simp only [smul_add, smul_sub, smul_smul]
          norm_num
  calc
    _ = FlagAlgebra_2_0_0_1 + 0 + 0 := by simp only [add_zero]
    _ ≤ ((1 / 3 : ℝ) • FlagAlgebra_3_0_0_1 + (2 / 3 : ℝ) • FlagAlgebra_3_0_0_2
        + FlagAlgebra_3_0_0_3)
      + (1 / 3 : ℝ) • FlagAlgebra_3_0_0_1
      + ((1 / 2 : ℝ) • FlagAlgebra_3_0_0_0 - (1 / 6 : ℝ) • FlagAlgebra_3_0_0_1
        - (1 / 6 : ℝ) • FlagAlgebra_3_0_0_2 + (1 / 2 : ℝ) • FlagAlgebra_3_0_0_3) :=
        flag_add_le_add (flag_add_le_add h₁ h₂) h₃
    _ = (1 / 2 : ℝ) • FlagAlgebra_3_0_0_0
      + ((1 / 3 : ℝ) + (1 / 3 : ℝ) - (1 / 6 : ℝ)) • FlagAlgebra_3_0_0_1
      + ((2 / 3 : ℝ) - (1 / 6 : ℝ)) • FlagAlgebra_3_0_0_2
      + (1 / 2 : ℝ) • FlagAlgebra_3_0_0_3 + FlagAlgebra_3_0_0_3 := by
        simp only [add_smul, sub_smul]
        ring
    _ = (1 / 2 : ℝ) • FlagAlgebra_3_0_0_0 + (1 / 2 : ℝ) • FlagAlgebra_3_0_0_1
      + (1 / 2 : ℝ) • FlagAlgebra_3_0_0_2 + (1 / 2 : ℝ) • FlagAlgebra_3_0_0_3
      + FlagAlgebra_3_0_0_3 := by norm_num
    _ = (1 / 2 : ℝ) • 1 + FlagAlgebra_3_0_0_3 := by
        rw [expand_1_on_three_vertex_graphs]
        norm_num

/-- Pointwise form of Mantel's theorem: for any positive homomorphism `φ`
killing the triangle (`φ K3 = 0`), the edge density satisfies `φ K2 ≤ 1/2`. -/
theorem Mantel_theorem'
  : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ K2 ≤ 1 / 2
  := by
  intro φ h
  simpa [φ.map_add, φ.map_sub, φ.map_smul, φ.map_one, h] using Mantel_theorem φ

/-- The generated flag `Flag_3_0_0_3` is the triangle `K₃`: it equals the
empty-typed flag of `completeGraph (Fin 3)`. -/
lemma Flag_3_0_0_3_eq
    : Flag_3_0_0_3 = ⟦{ graph := completeGraph (Fin 3), type_embed := RelEmbedding.ofIsEmpty _ _}⟧ := by
  simp [Flag_3_0_0_3, Sym2EmptyTypedFlag.toFlag, Sym2Flag_3_0_0_3, Sym2Graph.toFlag]
  refine Quotient.sound (Nonempty.intro ?_)
  have hgraph : Sym2Graph_3_0_0_3.toLabeledGraph.graph = completeGraph (Fin 3) := by
    ext v w
    simp [Sym2Graph.toLabeledGraph]
    fin_cases v <;> fin_cases w <;> decide
  exact {
    graph_iso := by
      refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
      intro v w
      simp [hgraph]
    type_preserve := List.ofFn_inj.mp rfl
  }

/-- The generated flag `Flag_2_0_0_1` is the single edge `K₂`: it equals the
empty-typed flag of `completeGraph (Fin 2)`. -/
lemma Flag_2_0_0_1_eq
    : Flag_2_0_0_1 = ⟦{ graph := completeGraph (Fin 2), type_embed := RelEmbedding.ofIsEmpty _ _}⟧ := by
  simp [Flag_2_0_0_1, Sym2EmptyTypedFlag.toFlag, Sym2Flag_2_0_0_1, Sym2Graph.toFlag]
  refine Quotient.sound (Nonempty.intro ?_)
  have hgraph : Sym2Graph_2_0_0_1.toLabeledGraph.graph = completeGraph (Fin 2) := by
    ext v w
    simp [Sym2Graph.toLabeledGraph]
    fin_cases v <;> fin_cases w <;> decide
  exact {
    graph_iso := by
      refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
      intro v w
      simp [hgraph]
    type_preserve := List.ofFn_inj.mp rfl
  }

/-- Lower bound matching Mantel's theorem: for `n ≥ 2` the maximal edge density
of a triangle-free graph on `n` vertices is at least `1/2`, witnessed by the
balanced complete bipartite graph. -/
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

/-- **Mantel's theorem (Turán density form).** The Turán density of the
triangle `K₃` is `1/2`: the flag-algebra upper bound (`Mantel_theorem'`) meets
the complete-bipartite lower bound (`extremal_density_K3_ge`). -/
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
      @flagDensity₁ _ _ _ (Fin.fintype (n k)) (instDecidableEqFin (n k)) _ _ _ _ Flag_3_0_0_3 (F k) = 0 := by
    intro k
    dsimp only [flagDensity₁]
    rw [← @subflagDensity_eq_flagListDensity, Flag_3_0_0_3_eq]
    simp [subflagDensity, labeledGraphDensityLifted, labeledGraphDensity, F, lG]
    left
    simp [labeledGraphCount]
    rw [@Fintype.card_eq_zero_iff]
    apply Subtype.isEmpty_of_false
    simp
    intro G' hG'_ind
    rw [← Set.univ_eq_empty_iff]
    ext φ
    simp at φ
    have hcontains : (completeGraph (Fin 3)) ⊑ G k :=
      IsContained.of_exists_iso_subgraph ⟨G'.subgraph, ⟨φ.graph_iso.symm⟩⟩
    exact False.elim ((hG_free k) hcontains)
  have hF_edge : ∀ (k : ℕ),
      @flagDensity₁ _ _ _ (Fin.fintype (n k)) (instDecidableEqFin (n k)) _ _ _ _ Flag_2_0_0_1 (F k) =
        ((G k).edgeFinset.card : ℝ) / (n k).choose 2 := by
    intro k
    dsimp only [flagDensity₁]
    rw [← @subflagDensity_eq_flagListDensity, Flag_2_0_0_1_eq]
    simp [subflagDensity, labeledGraphDensityLifted, labeledGraphDensity, F, lG]
    congr!
    · simp [labeledGraphCount]
      refine Eq.symm (Finset.card_bij ?_ ?_ ?_ ?_)
      · intro e he
        simp [edgeFinset] at he
        refine ⟨?_, ?_, ?_⟩
        · exact LabeledSubgraph.inducedLabeledSubgraph (lG k) e (by simp [LabeledGraph.type_verts])
        · simpa using (LabeledSubgraph.inducedLabeledSubgraph_isInduced (lG k) e
            (by simp [LabeledGraph.type_verts]))
        · exact Nonempty.intro {
            graph_iso := by
              classical
              let H := (LabeledSubgraph.inducedLabeledSubgraph (lG k) e
                (by simp [LabeledGraph.type_verts])).subgraph
              have hnotdiag : ¬ e.IsDiag := not_isDiag_of_mem_edgeSet _ he
              have hverts : H.verts = (e : Set (Fin (n k))) := by
                simp [H, LabeledSubgraph.inducedLabeledSubgraph_verts]
              have hcard_H : Fintype.card H.verts = 2 := by
                rw [hverts]
                rw [← Set.toFinset_card (s := (e : Set (Fin (n k))))]
                have htoFinset : Set.toFinset (e : Set (Fin (n k))) = e.toFinset := by
                  ext x
                  simp [Sym2.mem_toFinset]
                rw [htoFinset]
                simpa using (Sym2.card_toFinset_of_not_isDiag e hnotdiag)
              let f : H.verts ≃ Fin 2 := by
                exact Fintype.equivFinOfCardEq hcard_H
              refine { toEquiv := f, map_rel_iff' := ?_ }
              intro u v
              constructor
              · intro huv
                have hne : f u ≠ f v := by simpa using huv
                have huv_ne : u ≠ v := fun h => hne (congrArg f h)
                have hu : u.1 ∈ e := by
                  exact u.2
                have hv : v.1 ∈ e := by
                  exact v.2
                have huv_val_ne : u.1 ≠ v.1 := by
                  intro huv
                  apply huv_ne
                  exact Subtype.ext huv
                have hs : e = s(u.1, v.1) := by
                  exact (Sym2.mem_and_mem_iff huv_val_ne).1 ⟨hu, hv⟩
                have hs' : s(u.1, v.1) ∈ (G k).edgeSet := by simpa [hs] using he
                have hAdjG : (G k).Adj u.1 v.1 := by
                  simpa [SimpleGraph.mem_edgeSet] using hs'
                change H.Adj u.1 v.1
                exact ⟨hu, hv, hAdjG⟩
              · intro huv
                have hne' : f u ≠ f v := by
                  intro hEq
                  have : u = v := f.injective hEq
                  cases this
                  exact H.loopless u huv
                simpa using hne'
            type_preserve := List.ofFn_inj.mp rfl
          }
      · intros; simp_all
      · intro e he e' he' heq
        simp [LabeledSubgraph.inducedLabeledSubgraph, Subgraph.induce] at heq
        simp_all
      · intro ⟨G', hG'_ind, hG'_eqv⟩ _
        have φ := hG'_eqv.some.graph_iso
        let a : Sym2 (Fin (n k)) := s((φ.symm 0).1, (φ.symm 1).1)
        have ha_sub : a ∈ G'.subgraph.edgeSet := by
          change G'.subgraph.Adj (φ.symm 0).1 (φ.symm 1).1
          exact (φ.map_adj_iff).1 (by simp)
        have ha : a ∈ (G k).edgeSet := G'.subgraph.edgeSet_subset ha_sub
        have ha_finset : a ∈ (G k).edgeFinset := by
          simpa [edgeFinset] using ha
        refine ⟨a, ha_finset, ?_⟩
        have hverts : (a : Set (Fin (n k))) = G'.subgraph.verts := by
          ext x
          constructor
          · intro hx
            rcases (Sym2.mem_iff.mp hx) with hx | hx
            · rw [hx]
              exact (φ.symm 0).2
            · rw [hx]
              exact (φ.symm 1).2
          · intro hx
            let y : Fin 2 := φ ⟨x, hx⟩
            have hxy : (φ.symm y).1 = x := by
              have hy' : φ.symm y = ⟨x, hx⟩ := by
                dsimp [y]
                exact φ.symm_apply_apply ⟨x, hx⟩
              exact congrArg Subtype.val hy'
            have hy : y = 0 ∨ y = 1 := by
              have hy' : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by omega
              rcases hy' with hy' | hy'
              · exact Or.inl (Fin.eq_of_val_eq hy')
              · exact Or.inr (Fin.eq_of_val_eq hy')
            rcases hy with hy | hy
            · have hx0 : x = (φ.symm 0).1 := by simpa [hy] using hxy.symm
              exact (Sym2.mem_iff.mpr (Or.inl hx0))
            · have hx1 : x = (φ.symm 1).1 := by simpa [hy] using hxy.symm
              exact (Sym2.mem_iff.mpr (Or.inr hx1))
        have h_induced :
            LabeledSubgraph.inducedLabeledSubgraph (lG k) G'.subgraph.verts
              (LabeledSubgraph.labeledSubgraph_contain_type_verts (lG k) G') = G' :=
          (LabeledSubgraph.inducedLabeledSubgraph_eq (G := lG k) (H := G') hG'_ind).symm
        simpa [a, hverts] using h_induced
    · simp only [LabeledGraph.size, Fintype.card_fin]
  have hF_edge_ge : ∀ (k : ℕ),
      @flagDensity₁ _ _ _ (Fin.fintype (n k)) (instDecidableEqFin (n k)) _ _ _ _ Flag_2_0_0_1 (F k) ≥ 1 / 2 + ε := by
    intro k
    rw [hF_edge k]
    exact hG_edge_ge k

  let s : FlagSeq ∅ₜ := fun k ↦ ⟨n k, F k⟩
  have hs_inc : Increases s := by
    apply increases_of_consecutive_lt
    intro k
    simp only [hsucc, s]
  obtain ⟨a, ϕ, hϕ_mono, hϕ_conv⟩ := increasing_flagSeq_contain_convergent_subseq s hs_inc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (s ∘ ϕ) hϕ_conv
  obtain ⟨_, hϕ_conv⟩ := flagSeq_convergesTo_iff.mp hϕ_conv

  have hφ_K3 : φ FlagAlgebra_3_0_0_3 = 0 := by
    have h_eval_K3 : a ⟨3, Flag_3_0_0_3⟩ = φ ⟦basisVector ⟨3, Flag_3_0_0_3⟩⟧ := by
      have hφ_val : (φ.coe : FinFlag ∅ₜ → ℝ) = (a : FinFlag ∅ₜ → ℝ) := congrArg Subtype.val hφ
      have hφ_eval : φ.coe ⟨3, Flag_3_0_0_3⟩ = a ⟨3, Flag_3_0_0_3⟩ := by
        simpa using congrFun hφ_val ⟨3, Flag_3_0_0_3⟩
      calc
        a ⟨3, Flag_3_0_0_3⟩ = φ.coe ⟨3, Flag_3_0_0_3⟩ := by simpa using hφ_eval.symm
        _ = φ ⟦basisVector ⟨3, Flag_3_0_0_3⟩⟧ := by
              simpa using (PositiveHom.coe_flag φ ⟨3, Flag_3_0_0_3⟩)
    apply @tendsto_nhds_unique _ _ _ _ (fun n ↦ flagDensitySeq (s ∘ ϕ) n ⟨3, Flag_3_0_0_3⟩) atTop
    · simpa [h_eval_K3] using (hϕ_conv ⟨3, Flag_3_0_0_3⟩)
    · have hK3_zero : ∀ n, flagDensitySeq (s ∘ ϕ) n ⟨3, Flag_3_0_0_3⟩ = 0 := by
        intro n
        simpa [flagDensitySeq, s] using congrArg (fun x : ℚ ↦ (x : ℝ)) (hF_free (ϕ n))
      rw [tendsto_congr hK3_zero, tendsto_const_nhds_iff]

  have hφ_K2_le : φ FlagAlgebra_2_0_0_1 ≤ 1 / 2 := Mantel_theorem' φ hφ_K3
  have hφ_K2_tendsto :
      Tendsto (fun n ↦ flagDensitySeq (s ∘ ϕ) n ⟨2, Flag_2_0_0_1⟩) atTop (nhds (φ FlagAlgebra_2_0_0_1)) := by
    have h_eval_K2 : a ⟨2, Flag_2_0_0_1⟩ = φ ⟦basisVector ⟨2, Flag_2_0_0_1⟩⟧ := by
      have hφ_val : (φ.coe : FinFlag ∅ₜ → ℝ) = (a : FinFlag ∅ₜ → ℝ) := by
        exact congrArg Subtype.val hφ
      have hφ_eval : φ.coe ⟨2, Flag_2_0_0_1⟩ = a ⟨2, Flag_2_0_0_1⟩ := by
        simpa using congrFun hφ_val (⟨2, Flag_2_0_0_1⟩ : FinFlag ∅ₜ)
      calc
        a ⟨2, Flag_2_0_0_1⟩ = φ.coe ⟨2, Flag_2_0_0_1⟩ := by simpa using hφ_eval.symm
        _ = φ ⟦basisVector ⟨2, Flag_2_0_0_1⟩⟧ := by
              simpa using (PositiveHom.coe_flag φ ⟨2, Flag_2_0_0_1⟩)
    simpa [h_eval_K2] using (hϕ_conv ⟨2, Flag_2_0_0_1⟩)
  rw [Metric.tendsto_atTop'] at hφ_K2_tendsto
  obtain ⟨N, hN⟩ := hφ_K2_tendsto (ε / 2) (by linarith [hε])
  let x : ℝ := flagDensitySeq (s ∘ ϕ) (N + 1) ⟨2, Flag_2_0_0_1⟩
  have hx_ge : x ≥ 1 / 2 + ε := by
    dsimp [x]
    simpa [flagDensitySeq, s] using hF_edge_ge (ϕ (N + 1))
  have hdist_lt : dist x (φ FlagAlgebra_2_0_0_1) < ε / 2 := by
    simpa [x] using hN (N + 1) (Nat.lt_add_one N)
  have hdist_ge : dist x (φ FlagAlgebra_2_0_0_1) ≥ ε := by
    have hxφ_nonneg : 0 ≤ x - φ FlagAlgebra_2_0_0_1 := by linarith
    rw [Real.dist_eq, abs_of_nonneg hxφ_nonneg]
    linarith
  linarith

end MantelTheorem
