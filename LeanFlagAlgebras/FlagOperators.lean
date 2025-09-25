import «LeanFlagAlgebras».FlagAlgebra

open FlagAlgebras
open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/- Downward operator from σ-type to the empty type -/

def emptyType : FlagType (Fin 0) := SimpleGraph.emptyGraph (Fin 0)

notation "∅ₜ" => emptyType

@[simp]
theorem emptyType_size : ∅ₜ.size = 0 := by
  dsimp [emptyType, FlagType.size]
  simp only [Fintype.card_eq_zero]

def isoLabeledGraphSetWithSameGraph
    (G : LabeledGraph σ (Fin n)) : Set (LabeledGraph σ (Fin n))
  :=
  { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H }

noncomputable instance (G : LabeledGraph σ (Fin n)) : Fintype (isoLabeledGraphSetWithSameGraph G)
  :=
  Fintype.ofFinite (isoLabeledGraphSetWithSameGraph G)

noncomputable def isomorphismCount
    (G : LabeledGraph σ (Fin n)) : ℕ
  :=
  (isoLabeledGraphSetWithSameGraph G).toFinset.card

noncomputable def downwardNormalizingFactor_labeledGraph
    (G : LabeledGraph σ (Fin n)) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - n₀).factorial
  isomorphismCount G / num_of_all_injections

def funBetweenIsoLabeledGraphSetWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (φ : G ≃f G')
    : isoLabeledGraphSetWithSameGraph G → isoLabeledGraphSetWithSameGraph G'
  := by
  intro ⟨H, ⟨hGH_graph, hGH_iso⟩⟩
  let H' : LabeledGraph σ (Fin n) := {
    graph := G'.graph
    type_embed := {
      toFun := φ.graph_iso ∘ H.type_embed
      inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
      map_rel_iff' := by
        intro a b
        simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
        constructor
        · intro h
          rw [type_embed_Adj_iff H]
          nth_rw 1 [← hGH_graph]
          exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h
        · intro h
          rw [SimpleGraph.Iso.map_adj_iff φ.graph_iso, hGH_graph, ← type_embed_Adj_iff H]
          exact h
    }
  }
  have hG'H'_graph : G'.graph = H'.graph := rfl
  let φH : H.graph ≃g H'.graph := by
    rw [← hGH_graph, ← hG'H'_graph]
    exact φ.graph_iso
  let ψ : G ≃f H := hGH_iso.some
  have hH' : G'.graph = H'.graph ∧ G' ∼f H' := by
    constructor
    · rfl
    · apply Nonempty.intro
      exact {
        graph_iso := (φ.graph_iso.symm.trans ψ.graph_iso).trans φH
        type_preserve := by
          simp only [SimpleGraph.Iso.coe_comp]
          rw [← φ.type_preserve]
          calc
            _ = ⇑φH ∘ ⇑ψ.graph_iso ∘ (⇑φ.graph_iso.symm ∘ ⇑φ.graph_iso) ∘ ⇑G.type_embed := rfl
            _ = ⇑φH ∘ ⇑ψ.graph_iso ∘ ⇑G.type_embed := by ext; simp
            _ = ⇑φ.graph_iso ∘ ⇑ψ.graph_iso ∘ ⇑G.type_embed := by
              congr! 1
              show φH.toFun = φ.graph_iso
              dsimp [φH]
              funext x
              congr
              · rw [hGH_graph]
              · rw [hGH_graph]
              · simp only [cast_heq]
            _ = ⇑H'.type_embed := by
              rw [ψ.type_preserve]
              rfl
      }
  exact ⟨H', hH'⟩

lemma comp_funBetweenIsoLabeledGraphSetWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (φ : G ≃f G')
    : ∀ H, (funBetweenIsoLabeledGraphSetWithSameGraph φ.symm) ((funBetweenIsoLabeledGraphSetWithSameGraph φ) H) = H
  := by
  intro ⟨H, ⟨hGH_graph, hGH_iso⟩⟩
  unfold funBetweenIsoLabeledGraphSetWithSameGraph
  split
  rename_i h H_1 hGH_graph_1 hGH_iso_1 heq
  simp_all only [Subtype.mk.injEq]
  subst heq
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  congr!
  calc
    _ = (⇑φ.graph_iso.symm ∘ ⇑φ.graph_iso) ∘ ⇑H.type_embed := rfl
    _ = ⇑H.type_embed := by ext; simp only [Function.comp_apply, RelIso.symm_apply_apply]
    _ = H.2.1.toFun := rfl

def isoSetOfIsoLabeledGraphWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (φ : G ≃f G')
    : isoLabeledGraphSetWithSameGraph G ≃ isoLabeledGraphSetWithSameGraph G' where
  toFun := funBetweenIsoLabeledGraphSetWithSameGraph φ
  invFun := funBetweenIsoLabeledGraphSetWithSameGraph φ.symm
  left_inv := comp_funBetweenIsoLabeledGraphSetWithSameGraph φ
  right_inv := comp_funBetweenIsoLabeledGraphSetWithSameGraph φ.symm

lemma isomorphismCount_respect_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : isomorphismCount G = isomorphismCount G'
  := by
  dsimp [isomorphismCount]
  simp only [Set.toFinset_card, Fintype.card_congr (isoSetOfIsoLabeledGraphWithSameGraph h.some)]

lemma downwardNormalizingFactor_labeledGraph_respect_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : downwardNormalizingFactor_labeledGraph G = downwardNormalizingFactor_labeledGraph G'
  := by
  dsimp [downwardNormalizingFactor_labeledGraph]
  rw [isomorphismCount_respect_eqv h]

noncomputable def downwardNormalizingFactor
    : Flag σ (Fin n) → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ (Fin n) => downwardNormalizingFactor_labeledGraph G)
  intro G G' G_eqv
  exact downwardNormalizingFactor_labeledGraph_respect_eqv G_eqv

theorem downwardNormalizingFactor_pos
    (F : Flag σ (Fin n))
    : downwardNormalizingFactor F > 0
  := by
  rw [← Quotient.out_eq F]
  dsimp only [downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph, Quotient.lift_mk]
  apply div_pos
  · simp only [Nat.cast_pos]
    dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
    rw [Finset.card_pos]
    use F.out
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
    apply flagEqv.refl
  · simp only [Nat.cast_pos, Nat.div_pos_iff]
    constructor
    · exact Nat.factorial_pos (n - n₀)
    · apply Nat.factorial_le
      exact Nat.sub_le n n₀

theorem downwardNormalizingFactor_nonneg
    (F : Flag σ (Fin n))
    : downwardNormalizingFactor F ≥ 0
  :=
  le_of_lt (downwardNormalizingFactor_pos F)

theorem downwardNormalizingFactor_emptyFlag_pos
    : downwardNormalizingFactor (emptyFlag σ) > 0
  := by
  dsimp only [emptyFlag, downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph, Quotient.lift_mk]
  simp only [tsub_self, Nat.factorial_zero, Nat.div_one]
  apply div_pos <;> simp only [Nat.cast_pos]
  · dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
    rw [Set.toFinset_setOf, Finset.card_pos]
    use emptyLabeledGraph σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply flagEqv.refl
  · exact Nat.factorial_pos n₀

def unlabeledGraph {V : Type} (G : LabeledGraph σ V) : LabeledGraph ∅ₜ V where
  graph := G.graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.graph.Adj

theorem unlabeledGraph_iso
    (G G' : LabeledGraph σ V) (h : G ∼f G')
    : unlabeledGraph G ∼f unlabeledGraph G'
  := by
  let φ : G ≃f G' := h.some
  apply Nonempty.intro
  exact {
    graph_iso := φ.graph_iso
    type_preserve := List.ofFn_inj.mp rfl
  }

def unlabeledGraphQuot {V : Type} (G : LabeledGraph σ V) : Flag ∅ₜ V :=
  ⟦unlabeledGraph G⟧

theorem unlabeledGraphQuot_respect_eqv
    {G G' : LabeledGraph σ V} (h : G ∼f G')
    : unlabeledGraphQuot G = unlabeledGraphQuot G'
  :=
  Quotient.sound (unlabeledGraph_iso G G' h)

noncomputable def unlabel {V : Type}
    : Flag σ V → Flag ∅ₜ V
  := by
  apply Quot.lift (fun G : LabeledGraph σ V => unlabeledGraphQuot G)
  intro G G' G_eqv
  exact unlabeledGraphQuot_respect_eqv G_eqv

noncomputable def downwardFlag (F : Flag σ (Fin n)) : FlagVector ∅ₜ :=
  downwardNormalizingFactor F • unitVector ⟨n, unlabel F⟩

noncomputable def downwardFlagVector : FlagVector σ → FlagVector ∅ₜ :=
  linearExtension (fun F : FinFlag σ => downwardFlag F.2)

noncomputable def downwardFlagVectorQuot (f : FlagVector σ) : FlagAlgebra ∅ₜ :=
  ⟦downwardFlagVector f⟧

lemma downwardFlagVector_zero
    : downwardFlagVector (0 : FlagVector σ) = 0
  := by
  simp only [downwardFlagVector, linearExtension_zero]

lemma downwardFlagVector_unitVector
    (F : FinFlag σ)
    : downwardFlagVector (unitVector F) = downwardFlag F.2
  := by
  simp only [downwardFlagVector, linearExtension_unitVector]

lemma downwardFlagVector_add
    (f f' : FlagVector σ)
    : downwardFlagVector (f + f') = downwardFlagVector f + downwardFlagVector f'
  := by
  simp only [downwardFlagVector, linearExtension_add]

lemma downwardFlagVector_sum
    (s : Finset ι) (c : ι → FlagVector σ)
    : downwardFlagVector (∑ i ∈ s, c i) = ∑ i ∈ s, downwardFlagVector (c i)
  := by
  simp only [downwardFlagVector, linearExtension_sum]

lemma downwardFlagVector_neg
    (f : FlagVector σ)
    : downwardFlagVector (-f) = -downwardFlagVector f
  := by
  simp only [downwardFlagVector, linearExtension_neg]

lemma downwardFlagVector_sub
    (f f' : FlagVector σ)
    : downwardFlagVector (f - f') = downwardFlagVector f - downwardFlagVector f'
  := by
  simp only [downwardFlagVector, linearExtension_sub]

lemma downwardFlagVector_smul
    (f : FlagVector σ) (r : ℝ)
    : downwardFlagVector (r • f) = r • downwardFlagVector f
  := by
  simp only [downwardFlagVector, linearExtension_smul]

noncomputable def labelExtensions
    {ℓ : ℕ} (F : FlagWithSize ∅ₜ ℓ) (σ : FlagType (Fin n₀))
    : Finset (FlagWithSize σ ℓ)
  :=
  { G : FlagWithSize σ ℓ | unlabel G = F }

set_option maxHeartbeats 200000 in
lemma flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions
    {ℓ ℓ' : ℕ} (F : FlagWithSize σ ℓ) (F' : FlagWithSize ∅ₜ ℓ') (hℓ : ℓ ≤ ℓ')
    : flagDensity₁ (unlabel F) F' * downwardNormalizingFactor F =
      ∑ G ∈ labelExtensions F' σ, flagDensity₁ F G * downwardNormalizingFactor G
  := by
  let ⟨Frep, hFrep⟩ := Quotient.exists_rep F
  have hFrep_size : Frep.size = ℓ := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  let ⟨Furep, hFurep⟩ := Quotient.exists_rep (unlabel F)
  have hFurep_size : Furep.size = ℓ := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  let ⟨F'rep, hF'rep⟩ := Quotient.exists_rep F'
  have hF'rep_size : F'rep.size = ℓ' := by
    simp only [LabeledGraph.size, Fintype.card_fin]
  have h_Fu_F := hFurep
  rw [← hFrep] at h_Fu_F
  simp only [unlabel, unlabeledGraphQuot, Quotient.lift_mk, unlabeledGraph, Quotient.eq] at h_Fu_F
  obtain ⟨iso_Fu_F, type_embed_Fu_F⟩ := h_Fu_F
  simp only at iso_Fu_F type_embed_Fu_F

  let Ω := { (w, θ) : (Set (Fin ℓ')) × (Fin n₀ → Fin ℓ') | Function.Injective θ ∧ w.toFinset.card = ℓ ∧ (Set.image θ Set.univ) ⊆ w }
  let A : Finset Ω := { w | by
    obtain ⟨⟨w, θ⟩, hw⟩ := w
    let G' := (F'rep.graph.induce w)
    let θ' : Fin n₀ → w := fun i ↦ ⟨θ i, by
      have : θ i ∈ Set.image θ Set.univ := ⟨i, Set.mem_univ i, rfl⟩
      exact hw.2.2 this⟩
    have hθ_inj : Function.Injective θ' := by
      intro a b h_eq
      simp only [Subtype.mk.injEq, θ'] at h_eq
      exact hw.1 (by rw [h_eq])
    exact if hθ_model : ∀ {a b : Fin n₀}, G'.Adj (θ' a) (θ' b) ↔ σ.Adj a b
          then Nonempty (⟨G', by exact { toEmbedding := ⟨θ', hθ_inj⟩, map_rel_iff' := hθ_model }⟩ ≃f Frep)
          else false
    -- let G : SimpleGraph (Fin ℓ') := {
    --     Adj := fun a b => a ∈ w ∧ b ∈ w ∧ F'rep.graph.Adj a b
    --     symm := fun a b ⟨ha, hb, hab⟩ => ⟨hb, ha, hab.symm⟩
    --   }
    -- exact if hθ_model : ∀ {a b : Fin n₀}, G.Adj (θ a) (θ b) ↔ σ.Adj a b
    --       then Nonempty (⟨G, by exact { toEmbedding := ⟨θ, hw.1⟩, map_rel_iff' := hθ_model }⟩ ≃f Frep)
    --       else false
          }
  dsimp only [flagDensity₁, downwardNormalizingFactor]
  rw [← subflagDensity_eq_flagListDensity (unlabel F) F']
  nth_rw 1 [← hFurep, ← hFrep, ← hF'rep]
  dsimp only [subflagDensity, Quotient.lift_mk, labeledSubgraphDensityLifted]
  have P₁ : labeledSubgraphDensity Furep F'rep * downwardNormalizingFactor_labeledGraph Frep = A.card / Ω.toFinset.card := by
    dsimp [labeledSubgraphDensity, downwardNormalizingFactor_labeledGraph]
    rw [div_mul_div_comm]
    have this_is_wrong_statement : labeledSubgraphCount Furep F'rep = A.card := by
      dsimp only [labeledSubgraphCount]
      apply Finset.card_eq_of_equiv
      refine Equiv.ofBijective ?_ ?_
      · intro ⟨G, hG⟩
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hG
        let iso_Fu_G := (Classical.choice hG.2).symm
        let θ : Fin n₀ → Fin ℓ' := fun i ↦ iso_Fu_G.graph_iso.toFun (iso_Fu_F.symm (Frep.type_embed i))
        use ⟨(G.subgraph.verts, θ), by
          simp only [Set.toFinset_card, Fintype.card_ofFinset, Set.image_univ,
            LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Set.mem_setOf_eq,
            Ω, θ]
          constructor <;> try constructor
          · intro u v h_eq
            simp only at h_eq
            apply Subtype.ext at h_eq
            simp only [EmbeddingLike.apply_eq_iff_eq] at h_eq
            exact h_eq
          · have : G.size = ℓ := by
              rw [← hFurep_size, Eq.comm]
              exact labeledGraphIso_size_eq _ _ iso_Fu_G
            simp_all only [Fintype.card_ofFinset, LabeledSubgraph.size]
          · intro w hw
            obtain ⟨w', hw'⟩ := hw
            subst hw'
            simp only [Subtype.coe_prop]⟩
        simp only [Bool.false_eq_true, dite_else_false, LabeledSubgraph.coe_graph,
          Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Finset.mem_filter, Finset.mem_univ,
          true_and, A, θ]
        have hθ_model : ∀ {a b : Fin n₀}, F'rep.graph.Adj (θ a) (θ b) ↔ σ.Adj a b := by
          intro a b
          rw [type_embed_Adj_iff Frep, ← iso_Fu_F.symm.map_adj_iff, ← iso_Fu_G.graph_iso.map_adj_iff]
          have ha : θ a ∈ G.subgraph.verts := by
            simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
              Subtype.coe_prop, θ]
          have hb : θ b ∈ G.subgraph.verts := by
            simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
              Subtype.coe_prop, θ]
          constructor
          · exact fun h ↦ hG.1 ha hb h
          · exact fun h ↦
              SimpleGraph.Subgraph.Adj.adj_sub' G.subgraph
                (iso_Fu_G.graph_iso.toFun (iso_Fu_F.symm (Frep.type_embed a)))
                (iso_Fu_G.graph_iso.toFun (iso_Fu_F.symm (Frep.type_embed b))) h
        use hθ_model
        apply Nonempty.intro
        refine { graph_iso := ?_ , type_preserve := ?_ }
        · simp only
          refine { toEquiv := ?_, map_rel_iff' := ?_ }
          · exact iso_Fu_G.graph_iso.symm.toEquiv.trans iso_Fu_F.toEquiv
          · intro ⟨u, hu⟩ ⟨v, hv⟩
            simp only [LabeledSubgraph.coe_graph, Equiv.trans_apply, RelIso.coe_fn_toEquiv,
              SimpleGraph.comap_adj, Function.Embedding.subtype_apply]
            rw [iso_Fu_F.map_adj_iff, iso_Fu_G.graph_iso.symm.map_adj_iff]
            simp only [LabeledSubgraph.coe_graph, SimpleGraph.Subgraph.coe_adj]
            constructor
            · exact fun a ↦ SimpleGraph.Subgraph.Adj.adj_sub a
            · exact fun h ↦ hG.1 hu hv h
        · ext _
          simp only [LabeledSubgraph.coe_graph, id_eq, RelIso.coe_fn_mk, Equiv.coe_trans,
            RelIso.coe_fn_toEquiv, Subtype.coe_eta, RelEmbedding.coe_mk,
            Function.Embedding.coeFn_mk, Function.comp_apply, RelIso.symm_apply_apply,
            RelIso.apply_symm_apply]
      · constructor
        · intro ⟨G, hG⟩ ⟨G', hG'⟩ h_eq
          simp only [Subtype.mk.injEq]
          simp only [Subtype.mk.injEq, Prod.mk.injEq] at h_eq
          simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hG hG'
          apply labeledSubgraph_eq_from_subgraph_eq
          exact inducedSubgraph_eq_verts hG.1 hG'.1 h_eq.1
        · intro ⟨⟨⟨w, θ⟩, hΩ⟩, hA⟩
          simp only [Set.image_univ, Set.mem_setOf_eq, Ω] at hΩ
          obtain ⟨hθ_inj, hw_card, hw⟩ := hΩ
          simp only [Bool.false_eq_true, dite_else_false, Finset.mem_filter, Finset.mem_univ,
            true_and, A] at hA
          obtain ⟨hθ, iso_G_F⟩ := hA
          let G := LabeledSubgraph.inducedLabeledSubgraph F'rep w (by
            intro x hx
            simp only [LabeledGraph.type_verts, Set.image_univ, Matrix.range_empty, Set.mem_empty_iff_false] at hx)
          have hG_ind : G.IsInduced := by simp only [LabeledSubgraph.inducedLabeledSubgraph_isInduced, G]
          let iso_G_Fu : G.coe ≃f Furep := by
            refine { graph_iso := ?_, type_preserve := ?_ }
            · simp only [LabeledSubgraph.coe_graph, G]
              have : G.coe.graph ≃g (labeledGraphIso_extract_graph (Classical.choice iso_G_F)).graph := by
                dsimp only [LabeledSubgraph.inducedLabeledSubgraph, LabeledSubgraph.coe_graph,
                  labeledGraphIso_extract_graph, G]
                have G_rfl : (inducedSubgraph F'rep.graph w).coe = SimpleGraph.induce w F'rep.graph := by
                  ext u v
                  simp only [SimpleGraph.Subgraph.coe_adj, inducedSubgraph_isInduced,
                    SimpleGraph.Subgraph.IsInduced.adj, SimpleGraph.comap_adj,
                    Function.Embedding.subtype_apply]
                rw [G_rfl]
              exact (this.trans (Classical.choice iso_G_F).graph_iso).trans iso_Fu_F.symm
            · ext k
              exact Fin.elim0 k
          use ⟨G, by
            simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hG_ind, Nonempty.intro iso_G_Fu⟩⟩
          simp only [LabeledSubgraph.coe_graph, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv,
            Subtype.mk.injEq, Prod.mk.injEq]
          constructor
          · simp only [LabeledSubgraph.inducedLabeledSubgraph_verts, G]
          · ext k
            apply Fin.val_eq_of_eq
            have := congrFun (Classical.choice iso_G_F).symm.type_preserve k
            sorry
    congr
    · sorry
    · simp only [emptyType_size, tsub_zero]
      suffices (@Nat.cast ℚ _ (ℓ'.choose ℓ)) * ↑(ℓ.factorial / (ℓ - n₀).factorial) = ↑Ω.toFinset.card by rw [← this]; congr
      let inj_map := {θ : Fin n₀ → Fin ℓ' | Function.Injective θ}
      have inj_map_card : inj_map.toFinset.card = ℓ'.factorial / (ℓ - n₀).factorial := by
        sorry
      let lest_vtx (θ : Fin n₀ → Fin ℓ') : Finset (Finset (Fin ℓ')) := by
        let left := (Finset.univ : Finset (Fin ℓ')) \ (Set.image θ Set.univ).toFinset
        exact combinations left (ℓ - n₀)
      -- have card_eq : Ω.toFinset.card = inj_map.toFinset.card * lest_vtx.card := by sorry

      sorry

    -- suffices (@Nat.cast ℚ _ (labeledSubgraphCount Furep F'rep)) * ↑(isomorphismCount Frep) / (ℓ'.factorial / ((ℓ - n₀).factorial * (ℓ'- ℓ).factorial)) = A.card / Ω.toFinset.card by
    --   rw [← this]
    --   refine congrArg (HDiv.hDiv _) ?_
    --   simp only [emptyType_size, tsub_zero]
    --   calc
    --     (@Nat.cast ℚ _ (F'rep.size.choose Furep.size)) * ↑(ℓ.factorial / (ℓ - n₀).factorial) = ℓ'.choose ℓ * ↑(ℓ.factorial / (ℓ - n₀).factorial) := by congr
    --     _ = ℓ'.factorial / ((ℓ - n₀).factorial * (ℓ'- ℓ).factorial) := by
    --       rw [Nat.choose_eq_factorial_div_factorial hℓ, ← Nat.cast_mul]
    --       nth_rw 2 [mul_comm]
    --       rw [← Nat.mul_div_assoc ]
    --       rw [← Nat.div_div_eq_div_mul]
    --       · rw [Nat.div_mul_cancel (by
    --           apply Nat.dvd_div_of_mul_dvd; rw [mul_comm]
    --           apply Nat.factorial_mul_factorial_dvd_factorial; omega)]
    --         rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.cast_mul]
    --         refine Rat.natCast_div ℓ'.factorial ((ℓ - n₀).factorial * (ℓ' - ℓ).factorial) ?_
    --         sorry
    --       · apply Nat.factorial_dvd_factorial; omega

  rw [P₁]

  sorry

example (A B C D : ℚ) (h : B = C) : A / B = A / C := by
  -- exact congrArg (HDiv.hDiv A) h
  sorry

example (A B C D : ℕ) (h : B = C) : (A / B) * C = A / (B / C) := by

  -- refine Eq.symm (Nat.mul_div_assoc (A / B) ?_)
  -- refine div_mul_div_cancel₀ ?_
  -- rw [h]
  -- exact congrArg (HDiv.hDiv A) h
  sorry

lemma downwardFlag_eqv_sum_flagDensity_smul_downwardFlag
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : downwardFlag F.2 ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardFlag G
  := by
  calc
    _ = (downwardNormalizingFactor F.2) • unitVector ⟨F.1, unlabel F.2⟩ := rfl
    _ ∼v (downwardNormalizingFactor F.2) • densityFlagSum ⟨F.1, unlabel F.2⟩ ℓ := by
      apply flagVectorEqv_smul
      exact unitVector_eqv_densityFlagSum _ ℓ hℓ
    _ ∼v (downwardNormalizingFactor F.2) • (∑ G : FlagWithSize ∅ₜ ℓ, flagDensity₁ (unlabel F.2) G • unitVector ⟨ℓ, G⟩) := by
      apply flagVectorEqv_smul
      rfl
    _ ∼v ∑ G : FlagWithSize ∅ₜ ℓ, ∑ G' ∈ labelExtensions G σ,
          flagDensity₁ F.2 G' • downwardNormalizingFactor G' • unitVector ⟨ℓ, G⟩ := by
      rw [Finset.smul_sum]
      apply flagVectorEqv_sum
      intro G _
      rw [smul_smul, mul_comm, flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions _ _ hℓ]
      simp only [rat_smul_eq_real_smul, Rat.cast_sum, Rat.cast_mul]
      rw [sum_smul]
      apply flagVectorEqv_sum
      intro G' _
      rw [smul_smul]
    _ ∼v ∑ G : FlagWithSize ∅ₜ ℓ, ∑ G' ∈ Finset.filter (fun G' ↦ unlabel G' = G) Finset.univ,
          flagDensity₁ F.2 G' • downwardNormalizingFactor G' • unitVector ⟨ℓ, unlabel G'⟩ := by
      apply flagVectorEqv_sum
      intro G _
      apply flagVectorEqv_sum
      intro G' hG'
      iterate 2 (apply flagVectorEqv_smul)
      dsimp [labelExtensions] at hG'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG'
      rw [hG']
    _ ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardNormalizingFactor G • unitVector ⟨ℓ, unlabel G⟩ := by
      rw [Finset.sum_fiberwise _ (fun G => unlabel G)]
    _ ∼v ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • downwardFlag G := by
      apply flagVectorEqv_sum
      intro G _
      rfl

lemma downwardFlagVector_zeroElement_zeroSpace
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : downwardFlagVector (zeroElement F ℓ) ∈ ZeroSpace ∅ₜ
  := by
  dsimp [downwardFlagVector]
  let S : Finset (FinFlag σ) := (Finset.univ : Finset (FlagWithSize σ ℓ)).map {
    toFun := fun F' => ⟨ℓ, F'⟩
    inj' := fun F₁' F₂' h => by injection h
  }
  have h_supp : (zeroElement F ℓ).support ⊆ S ∪ {F} := by
    dsimp [zeroElement]
    calc
      _ ⊆ (unitVector F).support ∪ (densityFlagSum F ℓ).support := Finsupp.support_sub
      _ ⊆ S ∪ {F} := by
        rw [Finset.union_comm]
        apply Finset.union_subset_union
        · dsimp [densityFlagSum]
          apply Finset.Subset.trans Finsupp.support_finset_sum
          apply Finset.biUnion_subset.mpr
          intro G _
          apply Finset.Subset.trans Finsupp.support_smul
          simp only [unitVector_support, Finset.singleton_subset_iff, Finset.mem_map,
            Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, exists_apply_eq_apply, S]
        · simp only [unitVector_support, subset_refl]
  have h_supp_outside : ∀ G ∈ S ∪ {F},
    G ∉ (zeroElement F ℓ).support → (zeroElement F ℓ) G • downwardFlag G.2 = 0 := by
    intro G _ hG
    simp only [smul_eq_zero]; left
    exact Finsupp.notMem_support_iff.mp hG
  rw [linearExtension, Finset.sum_subset h_supp h_supp_outside]
  have hF_iff : F ∈ S ↔ F.1 = ℓ := by
    constructor
    · intro hF
      simp_all only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, S]
      obtain ⟨G, hG⟩ := hF
      subst hG
      simp_all only
    · intro hF
      subst hF
      simp only [Finset.mem_map, Finset.mem_univ, true_and, S]
      exact exists_apply_eq_apply _ F.2
  have h₁ : ∀ G ∈ S, G ≠ F → (zeroElement F ℓ) G = -(flagDensity₁ F.2 G.2) := by
    intro G hG h_G_neq_F
    simp only [zeroElement, densityFlagSum]
    rw [Finsupp.sub_apply, Finset.sum_apply', unitVector_apply_other F G h_G_neq_F.symm]
    simp only [zero_sub, neg_inj]
    have h_Gℓ : G.1 = ℓ := by
      simp_all only [Finset.mem_map, Finset.mem_univ, true_and, S]
      obtain ⟨w, h⟩ := hG
      subst h
      simp only [Function.Embedding.coeFn_mk]
    subst h_Gℓ
    rw [Finset.sum_eq_single_of_mem G.2]
    · simp only [Sigma.eta, rat_smul_eq_real_smul, Finsupp.coe_smul, Pi.smul_apply,
        unitVector_apply_self, smul_eq_mul, mul_one]
    · simp only [Finset.mem_univ]
    · intro G' _ hG'
      rw [Finsupp.smul_apply, unitVector_apply_other, smul_zero]
      contrapose! hG'
      simp only [ne_eq] at *
      rw [Sigma.ext_iff] at hG'
      simp only [heq_eq_eq, true_and] at hG'
      exact hG'
  have h₂ : (zeroElement F ℓ) F = if F ∈ S then 0 else 1 := by
    dsimp [zeroElement, densityFlagSum]
    simp only [unitVector_apply_self]
    rw [Finset.sum_apply']
    split
    next h =>
      rw [hF_iff] at h
      subst h
      rw [Finset.sum_eq_single_of_mem F.2]
      · simp only [flagDensity_self, Rat.cast_one, Sigma.eta, one_smul, unitVector_apply_self, sub_self]
      · simp only [Finset.mem_univ]
      · intro G _ hG
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero, Rat.cast_eq_zero]
        left
        exact flagDensity_other hG.symm
    next h =>
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, sub_eq_self]
      apply Finset.sum_eq_zero
      intro G _
      simp only [mul_eq_zero]
      right
      apply unitVector_apply_other_size
      symm; simp only
      rw [ne_eq, ← hF_iff]
      exact h
  have h₃ : ∑ G ∈ S ∪ {F}, (zeroElement F ℓ) G • downwardFlag G.2 =
      downwardFlag F.2 - ∑ G ∈ S, (flagDensity₁ F.snd G.snd) • downwardFlag G.2 := by
    by_cases hF : F ∈ S
    · have hF_S : S ∪ {F} = (S \ {F}) ∪ {F} := Eq.symm Finset.sdiff_union_self_eq_union
      have hF_S' : S = (S \ {F}) ∪ {F} := by
        rw [← hF_S, Finset.left_eq_union]
        simp only [Finset.singleton_subset_iff, hF]
      have h_disjoint : Disjoint (S \ {F}) {F} := Finset.sdiff_disjoint
      have h₂' : (zeroElement F ℓ) F = 1 - flagDensity₁ F.2 F.2 := by
        rw [h₂]
        simp only [hF, reduceIte, flagDensity_self, Rat.cast_one, sub_self]
      rw [hF_S, Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm, h₂', sub_smul, one_smul, sub_add]
      congr
      nth_rw 2 [hF_S']
      rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro G hG
      have h_G_S : G ∈ S := by
        have : S \ {F} ⊆ S := Finset.sdiff_subset
        exact this hG
      have h_G_neq_F : G ≠ F := by
        intro h; subst h
        revert hG
        simp only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, imp_self]
      rw [h₁ G h_G_S h_G_neq_F]
      simp only [neg_smul, neg_neg, rat_smul_eq_real_smul]
    · have h_disjoint : Disjoint S {F} := Finset.disjoint_singleton_right.mpr hF
      have h₁' : ∀ G ∈ S, (zeroElement F ℓ) G = -(flagDensity₁ F.2 G.2) := by
        intro G hG
        have h_G_neq_F : G ≠ F := ne_of_mem_of_not_mem hG hF
        exact h₁ G hG h_G_neq_F
      have h₂' : (zeroElement F ℓ) F = 1 := by
        rw [h₂]
        exact if_neg hF
      rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm, h₂', one_smul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro G hG
      rw [h₁' G hG]
      simp only [neg_smul, rat_smul_eq_real_smul]
  have h₄ : ∑ G ∈ S, (flagDensity₁ F.snd G.snd) • downwardFlag G.2 =
    ∑ G' : FlagWithSize σ ℓ, flagDensity₁ F.2 G' • downwardFlag G' := by
    simp only [Function.Embedding.coeFn_mk, Finset.sum_map, S]
  rw [h₃, h₄]
  exact downwardFlag_eqv_sum_flagDensity_smul_downwardFlag F ℓ hℓ

lemma downwardFlagVector_zeroSpace
    (f : FlagVector σ) (f_zero : f ∈ ZeroSpace σ)
    : downwardFlagVector f ∈ ZeroSpace ∅ₜ
  := by
  have ⟨I, hI, c, v, hv_zero, hf⟩ := zeroSpace_eq_sum_spanElement f f_zero
  rw [hf, downwardFlagVector_sum]
  apply zeroSpace_closed_under_sum
  intro i _
  rw [downwardFlagVector_smul]
  apply zeroSpace_closed_under_smul
  have ⟨F, ℓ, hℓ, hvi⟩ := hv_zero i
  rw [hvi]
  exact downwardFlagVector_zeroElement_zeroSpace F ℓ hℓ

lemma downwardFlagVectorQuot_zero
    : downwardFlagVectorQuot (0 : FlagVector σ) = 0
  := by
  apply Quotient.sound
  show downwardFlagVector (0 : FlagVector σ) - 0 ∈ ZeroSpace ∅ₜ
  rw [downwardFlagVector_zero, sub_self]
  simp only [Submodule.zero_mem]

lemma downwardFlagVectorQuot_add
    (f f' : FlagVector σ)
    : downwardFlagVectorQuot (f + f') = downwardFlagVectorQuot f + downwardFlagVectorQuot f'
  := by
  apply Quotient.sound
  show downwardFlagVector (f + f') - (downwardFlagVector f + downwardFlagVector f') ∈ ZeroSpace ∅ₜ
  rw [← downwardFlagVector_add, sub_self]
  simp only [Submodule.zero_mem]

lemma downwardFlagVectorQuot_neg
    (f : FlagVector σ)
    : downwardFlagVectorQuot (-f) = -(downwardFlagVectorQuot f)
  := by
  apply Quotient.sound
  simp only [neg_smul, one_smul]
  rw [downwardFlagVector_neg]

lemma downwardFlagVectorQuot_smul
    (f : FlagVector σ) (r : ℝ)
    : downwardFlagVectorQuot (r • f) = r • downwardFlagVectorQuot f
  := by
  apply Quotient.sound
  rw [downwardFlagVector_smul]

lemma downwardFlagVectorQuot_respect_eqv
    {f f' : FlagVector σ} (h : f ∼v f')
    : downwardFlagVectorQuot f = downwardFlagVectorQuot f'
  := by
  apply Quotient.sound
  show downwardFlagVector f - downwardFlagVector f' ∈ ZeroSpace ∅ₜ
  rw [← downwardFlagVector_sub]
  exact downwardFlagVector_zeroSpace (f - f') h

noncomputable def downward
    : FlagAlgebra σ → FlagAlgebra ∅ₜ
  := by
  apply Quot.lift (fun g : FlagVector σ => downwardFlagVectorQuot g)
  intro f f' f_eqv
  exact downwardFlagVectorQuot_respect_eqv f_eqv

notation "⟦" f "⟧₀" => (downward f)

theorem downward_zero
    : ⟦(0 : FlagAlgebra σ)⟧₀ = 0
  := by
  exact downwardFlagVectorQuot_zero

theorem downward_add
    (f f' : FlagAlgebra σ)
    : ⟦f + f'⟧₀ = ⟦f⟧₀ + ⟦f'⟧₀
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq f']
  apply downwardFlagVectorQuot_add

theorem downward_sum
    {ι : Type*} (s : Finset ι) (c : ι → FlagAlgebra σ)
    : ⟦∑ i ∈ s, c i⟧₀ = ∑ i ∈ s, ⟦c i⟧₀
  := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, downward_zero]
  · intro r R hr ih
    simp only [Finset.sum_insert hr, downward_add, ih]

theorem downward_neg
    (f : FlagAlgebra σ)
    : ⟦-f⟧₀ = -⟦f⟧₀
  := by
  rw [← Quotient.out_eq f, ← neg_quot]
  apply downwardFlagVectorQuot_neg

theorem downward_sub
    (f f' : FlagAlgebra σ)
    : ⟦f - f'⟧₀ = ⟦f⟧₀ - ⟦f'⟧₀
  := by
  simp only [sub_eq_add_neg, downward_add, downward_neg]

theorem downward_smul
    (f : FlagAlgebra σ) (r : ℝ)
    : ⟦r • f⟧₀ = r • ⟦f⟧₀
  := by
  rw [← Quotient.out_eq f, ← smul_quot]
  apply downwardFlagVectorQuot_smul
