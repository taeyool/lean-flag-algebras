import «LeanFlagAlgebras».FlagAlgebra.Compute.Basic

namespace FlagAlgebras.Compute

open SimpleGraph

abbrev LabeledSym2GraphList
    {k : ℕ} (σ : Sym2FlagType k) (t : ℕ) (Vl : Fin t → ℕ)
  := ∀ (i : Fin t), LabeledSym2Graph σ (Vl i)

def labeledSym2GraphToList
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : LabeledSym2Graph σ n)
    : LabeledSym2GraphList σ 1 (fun _ ↦ n)
  :=
  fun _ ↦ G

def labeledSym2GraphPairToList
    {k : ℕ} {σ : Sym2FlagType k} {n₀ n₁ : ℕ} (G₀ : LabeledSym2Graph σ n₀) (G₁ : LabeledSym2Graph σ n₁)
    : LabeledSym2GraphList σ 2 (fun i ↦ match i with | 0 => n₀ | 1 => n₁)
  :=
  fun i ↦ match i with | 0 => G₀ | 1 => G₁

def LabeledSym2GraphList.toLabeledGraphList
    {k : ℕ} {σ : Sym2FlagType k} {t : ℕ} {Vl : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) : LabeledGraphList σ.toFlagType t (fun i ↦ Fin (Vl i))
  :=
  fun i ↦ (Hl i).toLabeledGraph

@[ext]
structure LabeledSym2InducedSubgraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : LabeledSym2Graph σ n) where
  verts : Finset (Fin n)
  verts_subset : G.type_verts ⊆ verts

instance
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    Fintype (LabeledSym2InducedSubgraph G) where
  elems := (@Finset.univ (Finset (Fin n))).filterMap (fun V ↦
    if hV : G.type_verts ⊆ V
    then .some ⟨V, hV⟩
    else .none) (by grind)
  complete H := by
    simp
    use H.verts
    simp only [exists_prop, and_true]
    exact H.verts_subset

def LabeledSym2InducedSubgraph.edges
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) : Finset (Sym2 (Fin n))
  :=
  G.edges.filter (fun e ↦ ∀ v ∈ e, v ∈ H.verts)

theorem LabeledSym2InducedSubgraph.edges_valid
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) :
    ∀ e ∈ H.edges, ¬e.IsDiag
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact G.edges_valid e he.1

theorem LabeledSym2InducedSubgraph.edges_subset
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) :
    H.edges ⊆ G.edges
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact he.1

def LabeledSym2InducedSubgraph.toLabeledSubraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) : LabeledSubgraph σ.toFlagType G.toLabeledGraph where
  subgraph := {
    verts := H.verts
    Adj := fun u v ↦ Sym2.mk (u, v) ∈ H.edges
    adj_sub := by
      intro u v huv
      simp [LabeledSym2Graph.toLabeledGraph]
      constructor
      · exact H.edges_subset huv
      · exact G.edges_valid (Sym2.mk (u, v)) (H.edges_subset huv)
    edge_vert := by
      intro u v huv
      simp [edges] at huv
      exact huv.2.1
    symm := by
      intro u v huv
      rw [Sym2.eq_swap]
      exact huv
  }
  type_embed := {
    toFun := by
      simp only [Finset.coe_sort_coe]
      intro i
      exact ⟨G.type_embed i, H.verts_subset (G.mem_type_verts i)⟩
    inj' := by
      intro a b hab
      simp at hab
      exact hab
    map_rel_iff' := by
      intro a b
      simp [edges]
      constructor
      · intro ⟨h, _, _⟩
        rw [Sym2FlagType.toFlagType]
        rw [← G.type_embed.map_rel_iff]
        simp
        refine ⟨h, ?_⟩
        intro hab
        apply G.edges_valid (Sym2.mk (G.type_embed a, G.type_embed b)) h
        exact Sym2.mk_isDiag_iff.mpr (congrArg (G.type_embed) hab)
      · intro h
        have h' : (fromEdgeSet (SetLike.coe σ.edges)).Adj a b := by
          simpa [Sym2FlagType.toFlagType] using h
        rw [← G.type_embed.map_rel_iff] at h'
        constructor
        · simp at h'
          exact h'.1
        · exact ⟨H.verts_subset (G.mem_type_verts a), H.verts_subset (G.mem_type_verts b)⟩
  }
  embed_eq := by simp [LabeledSym2Graph.toLabeledGraph]

theorem LabeledSym2InducedSubgraph.toLabeledSubraph_isInduced
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} (H : LabeledSym2InducedSubgraph G) :
    H.toLabeledSubraph.IsInduced
  := by
  intro u hu v hv h_adj
  simp [toLabeledSubraph, edges, LabeledSym2Graph.toLabeledGraph] at *
  exact ⟨h_adj.1, hu, hv⟩

abbrev LabeledSym2InducedSubgraphList
    (t : ℕ) {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n)
  := Fin t → LabeledSym2InducedSubgraph G

def predDisjointLabeledSym2InducedSubgraphList
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} (Hl : LabeledSym2InducedSubgraphList t G) : Prop
  :=
  ∀ (i j : Fin t), i ≠ j → ((Hl i).verts \ G.type_verts) ∩ ((Hl j).verts \ G.type_verts) = ∅

def predIsoLabeledSym2Hl
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} {Vl  : Fin t → ℕ} (Hl : LabeledSym2GraphList σ t Vl)
    : LabeledSym2InducedSubgraphList t G → Prop
  := fun Gl ↦
      (∀ (i : Fin t), Nonempty ((Gl i).toLabeledSubraph.coe ≃f (Hl i).toLabeledGraph))
      ∧ predDisjointLabeledSym2InducedSubgraphList Gl

instance
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : LabeledSym2Graph σ n} {Vl  : Fin t → ℕ} (Hl : LabeledSym2GraphList σ t Vl) :
    DecidablePred (fun (Gl : LabeledSym2InducedSubgraphList t G) ↦ predIsoLabeledSym2Hl Hl Gl)
  := fun Gl ↦ by
  refine @instDecidableAnd _ _ ?_ ?_
  · refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    simp only
    have : Fintype (Gl i).toLabeledSubraph.subgraph.verts := by
      simp [LabeledSym2InducedSubgraph.toLabeledSubraph]
      exact (Gl i).verts.fintypeCoeSort
    have : DecidableRel (Gl i).toLabeledSubraph.coe.graph.Adj := by
      simp [LabeledSym2InducedSubgraph.toLabeledSubraph, Subgraph.coe]
      intro ⟨a, ha⟩ ⟨b, hb⟩
      exact Finset.decidableMem s(a, b) (Gl i).edges
    have : DecidableRel (Hl i).toLabeledGraph.graph.Adj := by
      intro a b
      simp [LabeledSym2Graph.toLabeledGraph]
      exact instDecidableAnd
    infer_instance
  · simp [predDisjointLabeledSym2InducedSubgraphList]
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro j
    exact instDecidableForall

def finsetOfLabeledSym2InducedSubgraphListIsoHl
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) {Vl  : Fin t → ℕ} (Hl : LabeledSym2GraphList σ t Vl)
    : Finset (LabeledSym2InducedSubgraphList t G)
  :=
  { Gl | predIsoLabeledSym2Hl Hl Gl }

def labeledSym2InducedSubgraphListCount
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) : ℕ
  :=
  (finsetOfLabeledSym2InducedSubgraphListIsoHl G Hl).card

lemma induced_subgraph_adj_iff
    {V : Type} {G : SimpleGraph V} {H : Subgraph G} (h_ind : H.IsInduced)
    {u v : V} (hu : u ∈ H.verts) (hv : v ∈ H.verts) :
    H.Adj u v ↔ G.Adj u v
  := by
  constructor <;> intro h
  · exact Subgraph.Adj.adj_sub h
  · exact h_ind hu hv h

lemma subgraph_not_adj
    {V : Type} {G : SimpleGraph V} {H : Subgraph G}
    {u v : V} (hu : u ∉ H.verts) :
    ¬H.Adj u v
  := by
  intro h_adj
  apply H.edge_vert at h_adj
  exact hu h_adj

theorem labeledSubgraphListCount_eq
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) :
    labeledSubgraphListCount Hl.toLabeledGraphList G.toLabeledGraph =
    labeledSym2InducedSubgraphListCount Hl G
  := by
  dsimp [labeledSubgraphListCount, labeledSym2InducedSubgraphListCount,
    setOfLabeledSubgraphListIsoHl, finsetOfLabeledSym2InducedSubgraphListIsoHl]
  apply Finset.card_nbij (fun Hl i ↦ {
    verts := @Set.toFinset _ (Hl i).subgraph.verts (Fintype.ofFinite _)
    verts_subset := by
      have h := LabeledSubgraph.labeledSubgraph_contain_type_verts G.toLabeledGraph (Hl i)
      rw [G.toLabeledGraph_type_verts_eq] at h
      simp only [Set.subset_toFinset]
      exact h
  })
  · intro Gl hGl
    simp [predIsoLabeledHl] at hGl
    obtain ⟨h_ind, h_iso, h_disj⟩:= hGl
    simp [predIsoLabeledSym2Hl]
    constructor
    · intro i
      let φ := (h_iso i).some.graph_iso
      have hφ : φ ∘ (Gl i).coe.type_embed = (Hl.toLabeledGraphList i).type_embed :=
        (h_iso i).some.type_preserve
      simp [LabeledSubgraph.coe] at φ
      exact Nonempty.intro {
        graph_iso := {
          toFun := by
            intro v
            simp [LabeledSym2InducedSubgraph.toLabeledSubraph, Subgraph.coe] at v
            exact φ v
          invFun := by
            intro w
            simp [LabeledSym2InducedSubgraph.toLabeledSubraph, Subgraph.coe]
            exact φ.symm w
          left_inv := by
            intro ⟨v, hv⟩
            simp
            rw [cast_eq_iff_heq]
            congr
            · funext w
              simp [LabeledSym2InducedSubgraph.toLabeledSubraph]
            · exact proof_irrel_heq _ _
          right_inv := by
            intro w
            simp
          map_rel_iff' := by
            intro ⟨v, hv⟩ ⟨v', hv'⟩
            simp [LabeledSym2InducedSubgraph.toLabeledSubraph] at hv hv'
            simp [LabeledSym2InducedSubgraph.toLabeledSubraph, LabeledSym2InducedSubgraph.edges, LabeledSym2Graph.toLabeledGraph]
            rw [← LabeledSym2Graph.toLabeledGraph_adj_iff, ← LabeledSym2Graph.toLabeledGraph_adj_iff]
            simp_all
            constructor
            · intro ⟨h_adj, hvv'_ne⟩
              have h : (Hl.toLabeledGraphList i).graph.Adj (φ ⟨v, hv⟩) (φ ⟨v', hv'⟩) := by
                simp [LabeledSym2GraphList.toLabeledGraphList]
                convert h_adj
                · have : v = (Subtype.mk v hv).val := rfl
                  nth_rw 1 [this]
                  congr 1; symm
                  rw [cast_eq_iff_heq]
                  congr
                  · funext w
                    simp
                  · exact proof_irrel_heq _ _
                · have : v' = (Subtype.mk v' hv').val := rfl
                  nth_rw 1 [this]
                  congr 1; symm
                  rw [cast_eq_iff_heq]
                  congr
                  · funext w
                    simp
                  · exact proof_irrel_heq _ _
              rw [φ.map_rel_iff] at h
              exact Subgraph.Adj.adj_sub h
            · intro h_adj
              constructor
              · have h : (Hl.toLabeledGraphList i).graph.Adj (φ ⟨v, hv⟩) (φ ⟨v', hv'⟩) := by
                  rw [φ.map_rel_iff]
                  exact h_ind i hv hv' h_adj
                simp [LabeledSym2GraphList.toLabeledGraphList] at h
                convert h
                · have : v = (Subtype.mk v hv).val := rfl
                  nth_rw 2 [this]
                  congr 1
                  rw [cast_eq_iff_heq]
                  congr
                  · funext w
                    simp
                  · exact proof_irrel_heq _ _
                · have : v' = (Subtype.mk v' hv').val := rfl
                  nth_rw 2 [this]
                  congr 1
                  rw [cast_eq_iff_heq]
                  congr
                  · funext w
                    simp
                  · exact proof_irrel_heq _ _
              · exact Adj.ne' (adj_symm G.toLabeledGraph.graph h_adj)
        }
        type_preserve := by
          funext u
          simp [LabeledSym2InducedSubgraph.toLabeledSubraph]
          have hu := congrFun hφ u
          simp [LabeledSym2GraphList.toLabeledGraphList] at hu
          rw [← hu]
          congr
          rw [cast_eq_iff_heq]
          congr
          · funext w
            simp
          · rw [← G.toLabeledGraph_type_embed_eq, ← (Gl i).embed_eq u]
            rfl
          · exact proof_irrel_heq _ _
      }
    · intro i j hij_ne
      simp only
      specialize h_disj i j hij_ne
      rw [G.toLabeledGraph_type_verts_eq] at h_disj
      rw [← Finset.coe_inj]
      simp [h_disj]
  · intro Gl hGl Gl' hGl' h_eq
    simp [predIsoLabeledHl] at hGl hGl'
    obtain ⟨hGl_ind, hGl_iso, hGl_disj⟩ := hGl
    obtain ⟨hGl'_ind, hGl'_iso, hGl'_disj⟩ := hGl'
    have h_iso : ∀ (i : Fin t), Nonempty ((Gl i).coe ≃f (Gl' i).coe) :=
      fun i ↦ Nonempty.intro ((hGl_iso i).some.trans (hGl'_iso i).some.symm)
    clear hGl_iso hGl'_iso
    have h_verts_eq : ∀ (i : Fin t), (Gl i).subgraph.verts = (Gl' i).subgraph.verts := by
      intro i
      have h := congrFun h_eq i
      simp at h
      rw [h]
    have h_adj_iff : ∀ (i : Fin t) (v w : Fin n),
      (Gl i).subgraph.Adj v w ↔ (Gl' i).subgraph.Adj v w := by
      intro i v w
      specialize hGl_ind i
      specialize hGl'_ind i
      specialize h_verts_eq i
      by_cases h : v ∈ (Gl i).subgraph.verts ∧ w ∈ (Gl i).subgraph.verts
      · obtain ⟨hv, hw⟩ := h
        rw [induced_subgraph_adj_iff hGl_ind hv hw]
        rw [h_verts_eq] at hv hw
        rw [induced_subgraph_adj_iff hGl'_ind hv hw]
      · have h' : v ∉ (Gl i).subgraph.verts ∨ w ∉ (Gl i).subgraph.verts :=
          Classical.not_and_iff_not_or_not.mp h
        rcases h' with hv | hw
        · simp [subgraph_not_adj hv]
          rw [h_verts_eq] at hv
          exact subgraph_not_adj hv
        · rw [Subgraph.adj_comm _ v w, Subgraph.adj_comm _ v w]
          simp [subgraph_not_adj hw]
          rw [h_verts_eq] at hw
          exact subgraph_not_adj hw
    ext u v w
    · rw [h_verts_eq]
    · exact h_adj_iff u v w
    · apply type_embed_heq_of_subgraph_eq
      ext v w
      · rw [h_verts_eq]
      · exact h_adj_iff u v w
  · intro Gl hGl
    simp [predIsoLabeledSym2Hl] at hGl
    obtain ⟨h_iso, h_disj⟩ := hGl
    simp only [Set.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
    use fun i ↦ (Gl i).toLabeledSubraph
    repeat' constructor
    · intro i
      exact (Gl i).toLabeledSubraph_isInduced
    · exact h_iso
    · intro i j hij_ne
      specialize h_disj i j hij_ne
      simp [LabeledSym2InducedSubgraph.toLabeledSubraph]
      rw [G.toLabeledGraph_type_verts_eq, ← Finset.coe_empty, ← h_disj]
      simp only [Finset.coe_inter, Finset.coe_sdiff]
    · funext i
      ext v
      simp [LabeledSym2InducedSubgraph.toLabeledSubraph]

def labeledSym2InducedSubgraphListDensity
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) : ℚ
  :=
  let r_list (i : Fin t) := Vl i - k
  labeledSym2InducedSubgraphListCount Hl G / multinomialCoefficient r_list (n - k)

instance
    {t : ℕ} {Vl : Fin t → ℕ} :
    FintypeList fun i ↦ Fin (Vl i)
  := by
  refine { fintype_all := ?_ }
  intro i
  exact Fin.fintype (Vl i)

instance
    {t : ℕ} {Vl  : Fin t → ℕ} :
    DecidableEqList fun i ↦ Fin (Vl i)
  := by
  refine { decidable_eq_all := ?_ }
  intro i
  exact instDecidableEqFin (Vl i)

theorem labeledSubgraphListDensity_eq
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : LabeledSym2GraphList σ t Vl) (G : LabeledSym2Graph σ n) :
    labeledSubgraphListDensity Hl.toLabeledGraphList G.toLabeledGraph =
    labeledSym2InducedSubgraphListDensity Hl G
  := by
  dsimp [labeledSubgraphListDensity, labeledSym2InducedSubgraphListDensity]
  have hk : σ.toFlagType.size = k := by
    change Fintype.card (Fin k) = k
    exact Fintype.card_fin k
  congr
  · exact labeledSubgraphListCount_eq Hl G
  · funext i
    simp [LabeledGraph.size, hk]
  · change Fintype.card (Fin n) = n
    exact Fintype.card_fin n

theorem labeledSubgraphListDensity_labeledGraphToList_eq
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (H : LabeledSym2Graph σ m) (G : LabeledSym2Graph σ n) :
    labeledSubgraphListDensity (labeledGraphToList H.toLabeledGraph) G.toLabeledGraph =
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphToList H) G
  :=
  labeledSubgraphListDensity_eq (labeledSym2GraphToList H) G

theorem labeledSubgraphListDensity_labeledGraphPairToList_eq
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (H₀ : LabeledSym2Graph σ m₀) (H₁ : LabeledSym2Graph σ m₁) (G : LabeledSym2Graph σ n) :
    labeledSubgraphListDensity (labeledGraphPairToList H₀.toLabeledGraph H₁.toLabeledGraph) G.toLabeledGraph =
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphPairToList H₀ H₁) G
  := by
  rw [← labeledSubgraphListDensity_eq]
  simp only [labeledSubgraphListDensity]
  congr!
  · grind
  · refine Function.hfunext rfl ?_
    intro a b hab
    simp only [heq_eq_eq] at hab
    match a, b with
    | 0, 0 => simp [labeledGraphPairToList, labeledSym2GraphPairToList, LabeledSym2GraphList.toLabeledGraphList]
    | 1, 1 => simp [labeledGraphPairToList, labeledSym2GraphPairToList, LabeledSym2GraphList.toLabeledGraphList]
  · simp [LabeledGraph.size]
    split
    · exact Fintype.card_fin m₀
    · exact Fintype.card_fin m₁

theorem labeledSym2InducedSubgraphListDensity_labeledSym2GraphToList_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    {F F' : LabeledSym2Graph σ m} (hF_eqv : F ∼sf F')
    {G G' : LabeledSym2Graph σ n} (hG_eqv : G ∼sf G') :
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphToList F) G =
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphToList F') G'
  := by
  rw [← labeledSubgraphListDensity_eq, ← labeledSubgraphListDensity_eq]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF_eqv.some
  · exact hG_eqv.some

def labeledSym2InducedSubgraphListDensityLifted₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : LabeledSym2Graph σ m) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ labeledSym2InducedSubgraphListDensity (labeledSym2GraphToList F) H) ?_ G
  intro _ _ h_eqv
  exact labeledSym2InducedSubgraphListDensity_labeledSym2GraphToList_respect_eqv (labeledSym2GraphEqv.refl F) h_eqv

theorem labeledSym2InducedSubgraphListDensityLifted₁_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    {F F' : LabeledSym2Graph σ m} (hF_eqv : F ∼sf F')
    (G : Sym2Flag σ n) :
    labeledSym2InducedSubgraphListDensityLifted₁ F G =
    labeledSym2InducedSubgraphListDensityLifted₁ F' G
  := by
  dsimp [labeledSym2InducedSubgraphListDensityLifted₁]
  congr
  funext H
  exact labeledSym2InducedSubgraphListDensity_labeledSym2GraphToList_respect_eqv hF_eqv (labeledSym2GraphEqv.refl H)

def sym2FlagDensity₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : Sym2Flag σ m) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ labeledSym2InducedSubgraphListDensityLifted₁ H G) ?_ F
  intro _ _ h_eqv
  exact labeledSym2InducedSubgraphListDensityLifted₁_respect_eqv h_eqv G

theorem labeledSym2InducedSubgraphListDensity_eq_sym2FlagDensity₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : LabeledSym2Graph σ m) (G : LabeledSym2Graph σ n) :
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphToList F) G = sym2FlagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  dsimp [sym2FlagDensity₁, labeledSym2InducedSubgraphListDensityLifted₁]

theorem flagDensity₁_eq
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : Sym2Flag σ m) (G : Sym2Flag σ n) :
    flagDensity₁ F.toFlag G.toFlag = sym2FlagDensity₁ F G
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  rcases Quotient.exists_rep G with ⟨G, rfl⟩
  dsimp [Sym2Flag.toFlag, LabeledSym2Graph.toFlag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁,
    ← labeledSym2InducedSubgraphListDensity_eq_sym2FlagDensity₁]
  exact labeledSubgraphListDensity_labeledGraphToList_eq F G

theorem labeledSym2InducedSubgraphListDensity_labeledSym2GraphPairToList_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    {F₀ F₀' : LabeledSym2Graph σ m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : LabeledSym2Graph σ m₁} (hF₁_eqv : F₁ ∼sf F₁')
    {G G' : LabeledSym2Graph σ n} (hG_eqv : G ∼sf G') :
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphPairToList F₀ F₁) G =
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphPairToList F₀' F₁') G'
  := by
  rw [← labeledSubgraphListDensity_eq, ← labeledSubgraphListDensity_eq]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF₀_eqv.some
    | 1 => exact hF₁_eqv.some
  · exact hG_eqv.some

def labeledSym2InducedSubgraphListDensityLifted₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : LabeledSym2Graph σ m₀) (F₁ : LabeledSym2Graph σ m₁) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ labeledSym2InducedSubgraphListDensity (labeledSym2GraphPairToList F₀ F₁) H) ?_ G
  intro _ _ h_eqv
  exact labeledSym2InducedSubgraphListDensity_labeledSym2GraphPairToList_respect_eqv
    (labeledSym2GraphEqv.refl F₀) (labeledSym2GraphEqv.refl F₁) h_eqv

theorem labeledSym2InducedSubgraphListDensityLifted₂_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    {F₀ F₀' : LabeledSym2Graph σ m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : LabeledSym2Graph σ m₁} (hF₁_eqv : F₁ ∼sf F₁')
    (G : Sym2Flag σ n) :
    labeledSym2InducedSubgraphListDensityLifted₂ F₀ F₁ G =
    labeledSym2InducedSubgraphListDensityLifted₂ F₀' F₁' G
  := by
  dsimp [labeledSym2InducedSubgraphListDensityLifted₂]
  congr
  funext H
  exact labeledSym2InducedSubgraphListDensity_labeledSym2GraphPairToList_respect_eqv
    hF₀_eqv hF₁_eqv (labeledSym2GraphEqv.refl H)

def sym2FlagDensity₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : Sym2Flag σ m₀) (F₁ : Sym2Flag σ m₁) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift₂ (fun H₀ H₁ ↦ labeledSym2InducedSubgraphListDensityLifted₂ H₀ H₁ G) ?_ F₀ F₁
  intro _ _ _ _ h_eqv h_eqv'
  exact labeledSym2InducedSubgraphListDensityLifted₂_respect_eqv h_eqv h_eqv' G

theorem labeledSym2InducedSubgraphListDensity_eq_sym2FlagDensity₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : LabeledSym2Graph σ m₀) (F₁ : LabeledSym2Graph σ m₁) (G : LabeledSym2Graph σ n) :
    labeledSym2InducedSubgraphListDensity (labeledSym2GraphPairToList F₀ F₁) G =
    sym2FlagDensity₂ ⟦F₀⟧ ⟦F₁⟧ ⟦G⟧
  := by
  dsimp [sym2FlagDensity₂, labeledSym2InducedSubgraphListDensityLifted₂]

theorem flagDensity₂_eq
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : Sym2Flag σ m₀) (F₁ : Sym2Flag σ m₁) (G : Sym2Flag σ n) :
    flagDensity₂ F₀.toFlag F₁.toFlag G.toFlag = sym2FlagDensity₂ F₀ F₁ G
  := by
  rcases Quotient.exists_rep F₀ with ⟨F₀, rfl⟩
  rcases Quotient.exists_rep F₁ with ⟨F₁, rfl⟩
  rcases Quotient.exists_rep G with ⟨G, rfl⟩
  dsimp [Sym2Flag.toFlag, LabeledSym2Graph.toFlag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂,
    ← labeledSym2InducedSubgraphListDensity_eq_sym2FlagDensity₂]
  exact labeledSubgraphListDensity_labeledGraphPairToList_eq F₀ F₁ G

end FlagAlgebras.Compute
