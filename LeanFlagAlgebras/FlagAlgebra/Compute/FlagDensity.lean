import «LeanFlagAlgebras».FlagAlgebra.Compute.Basic

namespace FlagAlgebras.Compute

open SimpleGraph

/- Empty-typed flags --/

abbrev Sym2GraphList
    (t : ℕ) (Vl : Fin t → ℕ)
  := ∀ (i : Fin t), Sym2Graph (Vl i)

def sym2GraphToList
    {n : ℕ} (G : Sym2Graph n) : Sym2GraphList 1 (fun _ ↦ n)
  :=
  fun _ ↦ G

def sym2GraphPairToList
    {n₀ n₁ : ℕ} (G₀ : Sym2Graph n₀) (G₁ : Sym2Graph n₁) :
    Sym2GraphList 2 (fun i ↦ match i with | 0 => n₀ | 1 => n₁)
  :=
  fun i ↦ match i with | 0 => G₀ | 1 => G₁

def Sym2GraphList.toLabeledGraphList
    {t : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2GraphList t Vl) : LabeledGraphList ∅ₜ t (fun i ↦ Fin (Vl i))
  :=
  fun i ↦ (Hl i).toLabeledGraph

@[ext]
structure Sym2InducedSubgraph
    {n : ℕ} (G : Sym2Graph n) where
  verts : Finset (Fin n)

instance
    {n : ℕ} (G : Sym2Graph n) :
    Fintype (Sym2InducedSubgraph G) where
  elems := Finset.map
    { toFun := fun V ↦ (⟨V⟩ : Sym2InducedSubgraph G)
      inj' := by
        intro A B h
        exact congrArg Sym2InducedSubgraph.verts h }
    (@Finset.univ (Finset (Fin n)) (inferInstance))
  complete H := by
    refine Finset.mem_map.mpr ?_
    refine ⟨H.verts, ?_, rfl⟩
    exact Finset.mem_univ H.verts

def Sym2InducedSubgraph.edges
    {n : ℕ} {G : Sym2Graph n} (H : Sym2InducedSubgraph G) : Finset (Sym2 (Fin n))
  :=
  G.edges.filter (fun e ↦ ∀ v ∈ e, v ∈ H.verts)

theorem Sym2InducedSubgraph.edges_valid
    {n : ℕ} {G : Sym2Graph n} (H : Sym2InducedSubgraph G) :
    ∀ e ∈ H.edges, ¬e.IsDiag
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact G.edges_valid e he.1

theorem Sym2InducedSubgraph.edges_subset
    {n : ℕ} {G : Sym2Graph n} (H : Sym2InducedSubgraph G) :
    H.edges ⊆ G.edges
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact he.1

def Sym2InducedSubgraph.toLabeledSubraph
    {n : ℕ} {G : Sym2Graph n} (H : Sym2InducedSubgraph G) : LabeledSubgraph ∅ₜ G.toLabeledGraph where
  subgraph := {
    verts := H.verts
    Adj := fun u v ↦ Sym2.mk (u, v) ∈ H.edges
    adj_sub := by
      intro u v huv
      simp [Sym2Graph.toLabeledGraph]
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
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj _
  embed_eq := by simp only [SetLike.coe_sort_coe, IsEmpty.forall_iff]

theorem Sym2InducedSubgraph.toLabeledSubraph_isInduced
    {n : ℕ} {G : Sym2Graph n} (H : Sym2InducedSubgraph G) :
    H.toLabeledSubraph.IsInduced
  := by
  intro u hu v hv h_adj
  simp [toLabeledSubraph, edges, Sym2Graph.toLabeledGraph] at *
  exact ⟨h_adj.1, hu, hv⟩

abbrev Sym2InducedSubgraphList
    (t : ℕ) {n : ℕ} (G : Sym2Graph n)
  := Fin t → Sym2InducedSubgraph G

def predDisjointSym2InducedSubgraphList
    {t : ℕ} {n : ℕ} {G : Sym2Graph n} (Hl : Sym2InducedSubgraphList t G) : Prop
  :=
  ∀ (i j : Fin t), i ≠ j → (Hl i).verts ∩ (Hl j).verts = ∅

def predIsoSym2Hl
    {t : ℕ} {n : ℕ} {G : Sym2Graph n} {Vl : Fin t → ℕ} (Hl : Sym2GraphList t Vl)
    : Sym2InducedSubgraphList t G → Prop
  :=
  fun Gl ↦
    (∀ (i : Fin t), Nonempty ((Gl i).toLabeledSubraph.coe ≃f (Hl i).toLabeledGraph))
    ∧ predDisjointSym2InducedSubgraphList Gl

instance
    {t : ℕ} {n : ℕ} {G : Sym2Graph n} {Vl : Fin t → ℕ} (Hl : Sym2GraphList t Vl) :
    DecidablePred (fun (Gl : Sym2InducedSubgraphList t G) ↦ predIsoSym2Hl Hl Gl)
  := fun Gl ↦ by
  refine @instDecidableAnd _ _ ?_ ?_
  · refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    simp only
    have : Fintype (Gl i).toLabeledSubraph.subgraph.verts := by
      simp [Sym2InducedSubgraph.toLabeledSubraph]
      exact (Gl i).verts.fintypeCoeSort
    have : DecidableRel (Gl i).toLabeledSubraph.coe.graph.Adj := by
      simp [Sym2InducedSubgraph.toLabeledSubraph, Subgraph.coe]
      intro ⟨a, ha⟩ ⟨b, hb⟩
      exact Finset.decidableMem s(a, b) (Gl i).edges
    have : DecidableRel (Hl i).toLabeledGraph.graph.Adj := by
      intro a b
      simp [Sym2Graph.toLabeledGraph]
      exact instDecidableAnd
    infer_instance
  · simp [predDisjointSym2InducedSubgraphList]
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro j
    exact instDecidableForall

def finsetOfSym2InducedSubgraphListIsoHl
    {t : ℕ} {n : ℕ} (G : Sym2Graph n) {Vl : Fin t → ℕ} (Hl : Sym2GraphList t Vl)
    : Finset (Sym2InducedSubgraphList t G)
  :=
  { Gl | predIsoSym2Hl Hl Gl }

def sym2InducedSubgraphListCount
    {t : ℕ} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2GraphList t Vl) (G : Sym2Graph n) : ℕ
  :=
  (finsetOfSym2InducedSubgraphListIsoHl G Hl).card

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

theorem labeledSubgraphListCount_eq_sym2InducedSubgraphListCount
    {t : ℕ} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2GraphList t Vl) (G : Sym2Graph n) :
    labeledSubgraphListCount Hl.toLabeledGraphList G.toLabeledGraph =
    sym2InducedSubgraphListCount Hl G
  := by
  dsimp [labeledSubgraphListCount, sym2InducedSubgraphListCount,
    setOfLabeledSubgraphListIsoHl, finsetOfSym2InducedSubgraphListIsoHl]
  apply Finset.card_nbij (fun Hl i ↦ {
    verts := @Set.toFinset _ (Hl i).subgraph.verts (Fintype.ofFinite _)
  })
  · intro Gl hGl
    simp [predIsoLabeledHl] at hGl
    obtain ⟨h_ind, h_iso, h_disj⟩ := hGl
    simp [predIsoSym2Hl]
    constructor
    · intro i
      let φ := (h_iso i).some.graph_iso
      simp [LabeledSubgraph.coe] at φ
      exact Nonempty.intro {
        graph_iso := {
          toFun := by
            intro v
            simp [Sym2InducedSubgraph.toLabeledSubraph, Subgraph.coe] at v
            exact φ v
          invFun := by
            intro w
            simp [Sym2InducedSubgraph.toLabeledSubraph, Subgraph.coe]
            exact φ.symm w
          left_inv := by
            intro ⟨v, hv⟩
            simp
            rw [cast_eq_iff_heq]
            congr
            · funext w
              simp [Sym2InducedSubgraph.toLabeledSubraph]
            · exact proof_irrel_heq _ _
          right_inv := by
            intro w
            simp
          map_rel_iff' := by
            intro ⟨v, hv⟩ ⟨v', hv'⟩
            simp [Sym2InducedSubgraph.toLabeledSubraph] at hv hv'
            simp [Sym2InducedSubgraph.toLabeledSubraph, Sym2InducedSubgraph.edges, Sym2Graph.toLabeledGraph]
            rw [← Sym2Graph.toLabeledGraph_adj_iff, ← Sym2Graph.toLabeledGraph_adj_iff]
            simp_all
            constructor
            · intro ⟨h_adj, hvv'_ne⟩
              have h : (Hl.toLabeledGraphList i).graph.Adj (φ ⟨v, hv⟩) (φ ⟨v', hv'⟩) := by
                simp [Sym2GraphList.toLabeledGraphList]
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
                simp [Sym2GraphList.toLabeledGraphList] at h
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
          exact Fin.elim0 u
      }
    · intro i j hij_ne
      simp only
      specialize h_disj i j hij_ne
      simp [Sym2Graph.toLabeledGraph, LabeledGraph.type_verts] at h_disj
      rw [← Finset.coe_inj]
      simpa using h_disj
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
    simp [predIsoSym2Hl] at hGl
    obtain ⟨h_iso, h_disj⟩ := hGl
    simp only [Set.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
    use fun i ↦ (Gl i).toLabeledSubraph
    repeat' constructor
    · intro i
      exact (Gl i).toLabeledSubraph_isInduced
    · exact h_iso
    · intro i j hij_ne
      specialize h_disj i j hij_ne
      simp [Sym2InducedSubgraph.toLabeledSubraph, Sym2Graph.toLabeledGraph, LabeledGraph.type_verts]
      rw [← Finset.coe_empty, ← h_disj]
      simp only [Finset.coe_inter]
    · funext i
      ext v
      simp [Sym2InducedSubgraph.toLabeledSubraph]

def sym2InducedSubgraphListDensity
    {t : ℕ} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2GraphList t Vl) (G : Sym2Graph n) : ℚ
  :=
  sym2InducedSubgraphListCount Hl G / multinomialCoefficient Vl n

instance {t : ℕ} {Vl : Fin t → ℕ} :
    FintypeList fun i ↦ Fin (Vl i)
  := by
  refine { fintype_all := ?_ }
  intro i
  exact Fin.fintype (Vl i)

instance {t : ℕ} {Vl : Fin t → ℕ} :
    DecidableEqList (fun i ↦ Fin (Vl i))
  := by
  refine { decidable_eq_all := ?_ }
  intro i
  exact instDecidableEqFin (Vl i)

theorem labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity
    {t : ℕ} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2GraphList t Vl) (G : Sym2Graph n) :
    labeledSubgraphListDensity Hl.toLabeledGraphList G.toLabeledGraph =
    sym2InducedSubgraphListDensity Hl G
  := by
  dsimp [labeledSubgraphListDensity, sym2InducedSubgraphListDensity]
  congr
  · exact labeledSubgraphListCount_eq_sym2InducedSubgraphListCount Hl G
  · funext i
    simp [LabeledGraph.size]
  · change Fintype.card (Fin n) = n
    exact Fintype.card_fin n

theorem labeledSubgraphListDensity_sym2GraphToList_eq
    {m n : ℕ}
    (H : Sym2Graph m) (G : Sym2Graph n) :
    labeledSubgraphListDensity (labeledGraphToList H.toLabeledGraph) G.toLabeledGraph =
    sym2InducedSubgraphListDensity (sym2GraphToList H) G
  :=
  labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity (sym2GraphToList H) G

theorem labeledSubgraphListDensity_sym2GraphPairToList_eq
    {m₀ m₁ n : ℕ}
    (H₀ : Sym2Graph m₀) (H₁ : Sym2Graph m₁) (G : Sym2Graph n) :
    labeledSubgraphListDensity (labeledGraphPairToList H₀.toLabeledGraph H₁.toLabeledGraph) G.toLabeledGraph =
    sym2InducedSubgraphListDensity (sym2GraphPairToList H₀ H₁) G
  := by
  rw [← labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity]
  simp only [labeledSubgraphListDensity]
  congr!
  · grind
  · refine Function.hfunext rfl ?_
    intro a b hab
    simp only [heq_eq_eq] at hab
    match a, b with
    | 0, 0 => simp [labeledGraphPairToList, sym2GraphPairToList, Sym2GraphList.toLabeledGraphList]
    | 1, 1 => simp [labeledGraphPairToList, sym2GraphPairToList, Sym2GraphList.toLabeledGraphList]
  · simp [LabeledGraph.size]
    split
    · exact Fintype.card_fin m₀
    · exact Fintype.card_fin m₁

theorem sym2InducedSubgraphListDensity_sym2GraphToList_respect_eqv
    {m n : ℕ}
    {F F' : Sym2Graph m} (hF_eqv : F ∼sf F')
    {G G' : Sym2Graph n} (hG_eqv : G ∼sf G') :
    sym2InducedSubgraphListDensity (sym2GraphToList F) G =
    sym2InducedSubgraphListDensity (sym2GraphToList F') G'
  := by
  rw [← labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity,
      ← labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF_eqv.some
  · exact hG_eqv.some

def sym2InducedSubgraphListDensityLifted₁
    {m n : ℕ}
    (F : Sym2Graph m) (G : Sym2EmptyTypedFlag n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedSubgraphListDensity (sym2GraphToList F) H) ?_ G
  intro _ _ h_eqv
  exact sym2InducedSubgraphListDensity_sym2GraphToList_respect_eqv (Sym2GraphEqv.refl F) h_eqv

theorem sym2InducedSubgraphListDensityLifted₁_respect_eqv
    {m n : ℕ}
    {F F' : Sym2Graph m} (hF_eqv : F ∼sf F')
    (G : Sym2EmptyTypedFlag n) :
    sym2InducedSubgraphListDensityLifted₁ F G =
    sym2InducedSubgraphListDensityLifted₁ F' G
  := by
  dsimp [sym2InducedSubgraphListDensityLifted₁]
  congr
  funext H
  exact sym2InducedSubgraphListDensity_sym2GraphToList_respect_eqv hF_eqv (Sym2GraphEqv.refl H)

def sym2EmptyTypeFlagDensity₁
    {m n : ℕ}
    (F : Sym2EmptyTypedFlag m) (G : Sym2EmptyTypedFlag n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedSubgraphListDensityLifted₁ H G) ?_ F
  intro _ _ h_eqv
  exact sym2InducedSubgraphListDensityLifted₁_respect_eqv h_eqv G

theorem sym2InducedSubgraphListDensity_eq_sym2EmptyTypeFlagDensity₁
    {m n : ℕ}
    (F : Sym2Graph m) (G : Sym2Graph n) :
    sym2InducedSubgraphListDensity (sym2GraphToList F) G =
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  dsimp [sym2EmptyTypeFlagDensity₁, sym2InducedSubgraphListDensityLifted₁]

theorem flagDensity₁_eq_sym2EmptyTypeFlagDensity₁
    {m n : ℕ}
    (F : Sym2EmptyTypedFlag m) (G : Sym2EmptyTypedFlag n) :
    flagDensity₁ F.toFlag G.toFlag = sym2EmptyTypeFlagDensity₁ F G
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  rcases Quotient.exists_rep G with ⟨G, rfl⟩
  dsimp [Sym2EmptyTypedFlag.toFlag, Sym2Graph.toFlag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁,
    ← sym2InducedSubgraphListDensity_eq_sym2EmptyTypeFlagDensity₁]
  exact labeledSubgraphListDensity_sym2GraphToList_eq F G

theorem sym2InducedSubgraphListDensity_sym2GraphPairToList_respect_eqv
    {m₀ m₁ n : ℕ}
    {F₀ F₀' : Sym2Graph m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : Sym2Graph m₁} (hF₁_eqv : F₁ ∼sf F₁')
    {G G' : Sym2Graph n} (hG_eqv : G ∼sf G') :
    sym2InducedSubgraphListDensity (sym2GraphPairToList F₀ F₁) G =
    sym2InducedSubgraphListDensity (sym2GraphPairToList F₀' F₁') G'
  := by
  rw [← labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity,
      ← labeledSubgraphListDensity_eq_sym2InducedSubgraphListDensity]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF₀_eqv.some
    | 1 => exact hF₁_eqv.some
  · exact hG_eqv.some

def sym2InducedSubgraphListDensityLifted₂
    {m₀ m₁ n : ℕ}
    (F₀ : Sym2Graph m₀) (F₁ : Sym2Graph m₁) (G : Sym2EmptyTypedFlag n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedSubgraphListDensity (sym2GraphPairToList F₀ F₁) H) ?_ G
  intro _ _ h_eqv
  exact sym2InducedSubgraphListDensity_sym2GraphPairToList_respect_eqv
    (Sym2GraphEqv.refl F₀) (Sym2GraphEqv.refl F₁) h_eqv

theorem sym2InducedSubgraphListDensityLifted₂_respect_eqv
    {m₀ m₁ n : ℕ}
    {F₀ F₀' : Sym2Graph m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : Sym2Graph m₁} (hF₁_eqv : F₁ ∼sf F₁')
    (G : Sym2EmptyTypedFlag n) :
    sym2InducedSubgraphListDensityLifted₂ F₀ F₁ G =
    sym2InducedSubgraphListDensityLifted₂ F₀' F₁' G
  := by
  dsimp [sym2InducedSubgraphListDensityLifted₂]
  congr
  funext H
  exact sym2InducedSubgraphListDensity_sym2GraphPairToList_respect_eqv
    hF₀_eqv hF₁_eqv (Sym2GraphEqv.refl H)

def sym2EmptyTypeFlagDensity₂
    {m₀ m₁ n : ℕ}
    (F₀ : Sym2EmptyTypedFlag m₀) (F₁ : Sym2EmptyTypedFlag m₁) (G : Sym2EmptyTypedFlag n) : ℚ
  := by
  refine Quotient.lift₂ (fun H₀ H₁ ↦ sym2InducedSubgraphListDensityLifted₂ H₀ H₁ G) ?_ F₀ F₁
  intro _ _ _ _ h_eqv h_eqv'
  exact sym2InducedSubgraphListDensityLifted₂_respect_eqv h_eqv h_eqv' G

theorem sym2InducedSubgraphListDensity_eq_sym2EmptyTypeFlagDensity₂
    {m₀ m₁ n : ℕ}
    (F₀ : Sym2Graph m₀) (F₁ : Sym2Graph m₁) (G : Sym2Graph n) :
    sym2InducedSubgraphListDensity (sym2GraphPairToList F₀ F₁) G =
    sym2EmptyTypeFlagDensity₂ ⟦F₀⟧ ⟦F₁⟧ ⟦G⟧
  := by
  dsimp [sym2EmptyTypeFlagDensity₂, sym2InducedSubgraphListDensityLifted₂]

theorem flagDensity₂_eq_sym2EmptyTypeFlagDensity₂
    {m₀ m₁ n : ℕ}
    (F₀ : Sym2EmptyTypedFlag m₀) (F₁ : Sym2EmptyTypedFlag m₁) (G : Sym2EmptyTypedFlag n) :
    flagDensity₂ F₀.toFlag F₁.toFlag G.toFlag = sym2EmptyTypeFlagDensity₂ F₀ F₁ G
  := by
  rcases Quotient.exists_rep F₀ with ⟨F₀, rfl⟩
  rcases Quotient.exists_rep F₁ with ⟨F₁, rfl⟩
  rcases Quotient.exists_rep G with ⟨G, rfl⟩
  dsimp [Sym2EmptyTypedFlag.toFlag, Sym2Graph.toFlag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂,
    ← sym2InducedSubgraphListDensity_eq_sym2EmptyTypeFlagDensity₂]
  exact labeledSubgraphListDensity_sym2GraphPairToList_eq F₀ F₁ G

/- Non-empty-typed flags --/

abbrev Sym2LabeledGraphList
    {k : ℕ} (σ : Sym2FlagType k) (t : ℕ) (Vl : Fin t → ℕ)
  := ∀ (i : Fin t), Sym2LabeledGraph σ (Vl i)

def sym2LabeledGraphToList
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : Sym2LabeledGraph σ n) :
    Sym2LabeledGraphList σ 1 (fun _ ↦ n)
  :=
  fun _ ↦ G

def sym2LabeledGraphPairToList
    {k : ℕ} {σ : Sym2FlagType k} {n₀ n₁ : ℕ} (G₀ : Sym2LabeledGraph σ n₀) (G₁ : Sym2LabeledGraph σ n₁) : Sym2LabeledGraphList σ 2 (fun i ↦ match i with | 0 => n₀ | 1 => n₁)
  :=
  fun i ↦ match i with | 0 => G₀ | 1 => G₁

def Sym2LabeledGraphList.toLabeledGraphList
    {k : ℕ} {σ : Sym2FlagType k} {t : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) : LabeledGraphList σ.toFlagType t (fun i ↦ Fin (Vl i))
  :=
  fun i ↦ (Hl i).toLabeledGraph

@[ext]
structure Sym2InducedLabeledSubgraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (G : Sym2LabeledGraph σ n) where
  verts : Finset (Fin n)
  verts_subset : G.type_verts ⊆ verts

instance
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    Fintype (Sym2InducedLabeledSubgraph G) where
  elems := (@Finset.univ (Finset (Fin n))).filterMap (fun V ↦
    if hV : G.type_verts ⊆ V
    then .some ⟨V, hV⟩
    else .none) (by grind)
  complete H := by
    simp
    use H.verts
    simp only [exists_prop, and_true]
    exact H.verts_subset

def Sym2InducedLabeledSubgraph.edges
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) : Finset (Sym2 (Fin n))
  :=
  G.edges.filter (fun e ↦ ∀ v ∈ e, v ∈ H.verts)

theorem Sym2InducedLabeledSubgraph.edges_valid
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) :
    ∀ e ∈ H.edges, ¬e.IsDiag
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact G.edges_valid e he.1

theorem Sym2InducedLabeledSubgraph.edges_subset
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) :
    H.edges ⊆ G.edges
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact he.1

def Sym2InducedLabeledSubgraph.toLabeledSubraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) : LabeledSubgraph σ.toFlagType G.toLabeledGraph where
  subgraph := {
    verts := H.verts
    Adj := fun u v ↦ Sym2.mk (u, v) ∈ H.edges
    adj_sub := by
      intro u v huv
      simp [Sym2LabeledGraph.toLabeledGraph]
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
  embed_eq := by simp [Sym2LabeledGraph.toLabeledGraph]

theorem Sym2InducedLabeledSubgraph.toLabeledSubraph_isInduced
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) :
    H.toLabeledSubraph.IsInduced
  := by
  intro u hu v hv h_adj
  simp [toLabeledSubraph, edges, Sym2LabeledGraph.toLabeledGraph] at *
  exact ⟨h_adj.1, hu, hv⟩

abbrev Sym2InducedLabeledSubgraphList
    (t : ℕ) {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n)
  := Fin t → Sym2InducedLabeledSubgraph G

def predDisjointSym2InducedLabeledSubgraphList
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} (Hl : Sym2InducedLabeledSubgraphList t G) : Prop
  :=
  ∀ (i j : Fin t), i ≠ j → ((Hl i).verts \ G.type_verts) ∩ ((Hl j).verts \ G.type_verts) = ∅

def predIsoSym2LabeledHl
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} {Vl : Fin t → ℕ} (Hl : Sym2LabeledGraphList σ t Vl)
    : Sym2InducedLabeledSubgraphList t G → Prop
  :=
  fun Gl ↦
    (∀ (i : Fin t), Nonempty ((Gl i).toLabeledSubraph.coe ≃f (Hl i).toLabeledGraph))
    ∧ predDisjointSym2InducedLabeledSubgraphList Gl

instance
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G : Sym2LabeledGraph σ n} {Vl : Fin t → ℕ} (Hl : Sym2LabeledGraphList σ t Vl) :
    DecidablePred (fun (Gl : Sym2InducedLabeledSubgraphList t G) ↦ predIsoSym2LabeledHl Hl Gl)
  := fun Gl ↦ by
  refine @instDecidableAnd _ _ ?_ ?_
  · refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    simp only
    have : Fintype (Gl i).toLabeledSubraph.subgraph.verts := by
      simp [Sym2InducedLabeledSubgraph.toLabeledSubraph]
      exact (Gl i).verts.fintypeCoeSort
    have : DecidableRel (Gl i).toLabeledSubraph.coe.graph.Adj := by
      simp [Sym2InducedLabeledSubgraph.toLabeledSubraph, Subgraph.coe]
      intro ⟨a, ha⟩ ⟨b, hb⟩
      exact Finset.decidableMem s(a, b) (Gl i).edges
    have : DecidableRel (Hl i).toLabeledGraph.graph.Adj := by
      intro a b
      simp [Sym2LabeledGraph.toLabeledGraph]
      exact instDecidableAnd
    infer_instance
  · simp [predDisjointSym2InducedLabeledSubgraphList]
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro i
    refine @Fintype.decidableForallFintype (Fin t) _ ?_ _
    intro j
    exact instDecidableForall

def finsetOfSym2InducedLabeledSubgraphListIsoHl
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) {Vl : Fin t → ℕ} (Hl : Sym2LabeledGraphList σ t Vl)
    : Finset (Sym2InducedLabeledSubgraphList t G)
  :=
  { Gl | predIsoSym2LabeledHl Hl Gl }

def sym2InducedLabeledSubgraphListCount
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) : ℕ
  :=
  (finsetOfSym2InducedLabeledSubgraphListIsoHl G Hl).card

theorem labeledSubgraphListCount_eq_sym2InducedLabeledSubgraphListCount
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListCount Hl.toLabeledGraphList G.toLabeledGraph =
    sym2InducedLabeledSubgraphListCount Hl G
  := by
  dsimp [labeledSubgraphListCount, sym2InducedLabeledSubgraphListCount,
    setOfLabeledSubgraphListIsoHl, finsetOfSym2InducedLabeledSubgraphListIsoHl]
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
    simp [predIsoSym2LabeledHl]
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
            simp [Sym2InducedLabeledSubgraph.toLabeledSubraph, Subgraph.coe] at v
            exact φ v
          invFun := by
            intro w
            simp [Sym2InducedLabeledSubgraph.toLabeledSubraph, Subgraph.coe]
            exact φ.symm w
          left_inv := by
            intro ⟨v, hv⟩
            simp
            rw [cast_eq_iff_heq]
            congr
            · funext w
              simp [Sym2InducedLabeledSubgraph.toLabeledSubraph]
            · exact proof_irrel_heq _ _
          right_inv := by
            intro w
            simp
          map_rel_iff' := by
            intro ⟨v, hv⟩ ⟨v', hv'⟩
            simp [Sym2InducedLabeledSubgraph.toLabeledSubraph] at hv hv'
            simp [Sym2InducedLabeledSubgraph.toLabeledSubraph, Sym2InducedLabeledSubgraph.edges, Sym2LabeledGraph.toLabeledGraph]
            rw [← Sym2LabeledGraph.toLabeledGraph_adj_iff, ← Sym2LabeledGraph.toLabeledGraph_adj_iff]
            simp_all
            constructor
            · intro ⟨h_adj, hvv'_ne⟩
              have h : (Hl.toLabeledGraphList i).graph.Adj (φ ⟨v, hv⟩) (φ ⟨v', hv'⟩) := by
                simp [Sym2LabeledGraphList.toLabeledGraphList]
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
                simp [Sym2LabeledGraphList.toLabeledGraphList] at h
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
          simp [Sym2InducedLabeledSubgraph.toLabeledSubraph]
          have hu := congrFun hφ u
          simp [Sym2LabeledGraphList.toLabeledGraphList] at hu
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
    simp [predIsoSym2LabeledHl] at hGl
    obtain ⟨h_iso, h_disj⟩ := hGl
    simp only [Set.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
    use fun i ↦ (Gl i).toLabeledSubraph
    repeat' constructor
    · intro i
      exact (Gl i).toLabeledSubraph_isInduced
    · exact h_iso
    · intro i j hij_ne
      specialize h_disj i j hij_ne
      simp [Sym2InducedLabeledSubgraph.toLabeledSubraph]
      rw [G.toLabeledGraph_type_verts_eq, ← Finset.coe_empty, ← h_disj]
      simp only [Finset.coe_inter, Finset.coe_sdiff]
    · funext i
      ext v
      simp [Sym2InducedLabeledSubgraph.toLabeledSubraph]

def sym2InducedLabeledSubgraphListDensity
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) : ℚ
  :=
  let r_list (i : Fin t) := Vl i - k
  sym2InducedLabeledSubgraphListCount Hl G / multinomialCoefficient r_list (n - k)

instance
    {t : ℕ} {Vl : Fin t → ℕ} :
    FintypeList fun i ↦ Fin (Vl i)
  := by
  refine { fintype_all := ?_ }
  intro i
  exact Fin.fintype (Vl i)

instance
    {t : ℕ} {Vl : Fin t → ℕ} :
    DecidableEqList fun i ↦ Fin (Vl i)
  := by
  refine { decidable_eq_all := ?_ }
  intro i
  exact instDecidableEqFin (Vl i)

theorem labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity
    {t : ℕ} {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListDensity Hl.toLabeledGraphList G.toLabeledGraph =
    sym2InducedLabeledSubgraphListDensity Hl G
  := by
  dsimp [labeledSubgraphListDensity, sym2InducedLabeledSubgraphListDensity]
  have hk : σ.toFlagType.size = k := by
    change Fintype.card (Fin k) = k
    exact Fintype.card_fin k
  congr
  · exact labeledSubgraphListCount_eq_sym2InducedLabeledSubgraphListCount Hl G
  · funext i
    simp [LabeledGraph.size, hk]
  · change Fintype.card (Fin n) = n
    exact Fintype.card_fin n

theorem labeledSubgraphListDensity_labeledGraphToList_eq
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (H : Sym2LabeledGraph σ m) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListDensity (labeledGraphToList H.toLabeledGraph) G.toLabeledGraph =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList H) G
  :=
  labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList H) G

theorem labeledSubgraphListDensity_labeledGraphPairToList_eq
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (H₀ : Sym2LabeledGraph σ m₀) (H₁ : Sym2LabeledGraph σ m₁) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListDensity (labeledGraphPairToList H₀.toLabeledGraph H₁.toLabeledGraph) G.toLabeledGraph =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList H₀ H₁) G
  := by
  rw [← labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity]
  simp only [labeledSubgraphListDensity]
  congr!
  · grind
  · refine Function.hfunext rfl ?_
    intro a b hab
    simp only [heq_eq_eq] at hab
    match a, b with
    | 0, 0 => simp [labeledGraphPairToList, sym2LabeledGraphPairToList, Sym2LabeledGraphList.toLabeledGraphList]
    | 1, 1 => simp [labeledGraphPairToList, sym2LabeledGraphPairToList, Sym2LabeledGraphList.toLabeledGraphList]
  · simp [LabeledGraph.size]
    split
    · exact Fintype.card_fin m₀
    · exact Fintype.card_fin m₁

theorem sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphToList_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    {F F' : Sym2LabeledGraph σ m} (hF_eqv : F ∼sf F')
    {G G' : Sym2LabeledGraph σ n} (hG_eqv : G ∼sf G') :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) G =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F') G'
  := by
  rw [← labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity,
      ← labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF_eqv.some
  · exact hG_eqv.some

def sym2InducedLabeledSubgraphListDensityLifted₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : Sym2LabeledGraph σ m) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) H) ?_ G
  intro _ _ h_eqv
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphToList_respect_eqv (sym2LabeledGraphEqv.refl F) h_eqv

theorem sym2InducedLabeledSubgraphListDensityLifted₁_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    {F F' : Sym2LabeledGraph σ m} (hF_eqv : F ∼sf F')
    (G : Sym2Flag σ n) :
    sym2InducedLabeledSubgraphListDensityLifted₁ F G =
    sym2InducedLabeledSubgraphListDensityLifted₁ F' G
  := by
  dsimp [sym2InducedLabeledSubgraphListDensityLifted₁]
  congr
  funext H
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphToList_respect_eqv hF_eqv (sym2LabeledGraphEqv.refl H)

def sym2FlagDensity₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : Sym2Flag σ m) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedLabeledSubgraphListDensityLifted₁ H G) ?_ F
  intro _ _ h_eqv
  exact sym2InducedLabeledSubgraphListDensityLifted₁_respect_eqv h_eqv G

theorem sym2InducedLabeledSubgraphListDensity_eq_sym2FlagDensity₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : Sym2LabeledGraph σ m) (G : Sym2LabeledGraph σ n) :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) G = sym2FlagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  dsimp [sym2FlagDensity₁, sym2InducedLabeledSubgraphListDensityLifted₁]

theorem flagDensity₁_eq_sym2FlagDensity₁
    {k : ℕ} {σ : Sym2FlagType k} {m n : ℕ}
    (F : Sym2Flag σ m) (G : Sym2Flag σ n) :
    flagDensity₁ F.toFlag G.toFlag = sym2FlagDensity₁ F G
  := by
  rcases Quotient.exists_rep F with ⟨F, rfl⟩
  rcases Quotient.exists_rep G with ⟨G, rfl⟩
  dsimp [Sym2Flag.toFlag, Sym2LabeledGraph.toFlag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₁,
    ← sym2InducedLabeledSubgraphListDensity_eq_sym2FlagDensity₁]
  exact labeledSubgraphListDensity_labeledGraphToList_eq F G

theorem sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphPairToList_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    {F₀ F₀' : Sym2LabeledGraph σ m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : Sym2LabeledGraph σ m₁} (hF₁_eqv : F₁ ∼sf F₁')
    {G G' : Sym2LabeledGraph σ n} (hG_eqv : G ∼sf G') :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀ F₁) G =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀' F₁') G'
  := by
  rw [← labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity,
      ← labeledSubgraphListDensity_eq_sym2InducedLabeledSubgraphListDensity]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF₀_eqv.some
    | 1 => exact hF₁_eqv.some
  · exact hG_eqv.some

def sym2InducedLabeledSubgraphListDensityLifted₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : Sym2LabeledGraph σ m₀) (F₁ : Sym2LabeledGraph σ m₁) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀ F₁) H) ?_ G
  intro _ _ h_eqv
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphPairToList_respect_eqv
    (sym2LabeledGraphEqv.refl F₀) (sym2LabeledGraphEqv.refl F₁) h_eqv

theorem sym2InducedLabeledSubgraphListDensityLifted₂_respect_eqv
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    {F₀ F₀' : Sym2LabeledGraph σ m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : Sym2LabeledGraph σ m₁} (hF₁_eqv : F₁ ∼sf F₁')
    (G : Sym2Flag σ n) :
    sym2InducedLabeledSubgraphListDensityLifted₂ F₀ F₁ G =
    sym2InducedLabeledSubgraphListDensityLifted₂ F₀' F₁' G
  := by
  dsimp [sym2InducedLabeledSubgraphListDensityLifted₂]
  congr
  funext H
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphPairToList_respect_eqv
    hF₀_eqv hF₁_eqv (sym2LabeledGraphEqv.refl H)

def sym2FlagDensity₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : Sym2Flag σ m₀) (F₁ : Sym2Flag σ m₁) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift₂ (fun H₀ H₁ ↦ sym2InducedLabeledSubgraphListDensityLifted₂ H₀ H₁ G) ?_ F₀ F₁
  intro _ _ _ _ h_eqv h_eqv'
  exact sym2InducedLabeledSubgraphListDensityLifted₂_respect_eqv h_eqv h_eqv' G

theorem sym2InducedLabeledSubgraphListDensity_eq_sym2FlagDensity₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : Sym2LabeledGraph σ m₀) (F₁ : Sym2LabeledGraph σ m₁) (G : Sym2LabeledGraph σ n) :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀ F₁) G =
    sym2FlagDensity₂ ⟦F₀⟧ ⟦F₁⟧ ⟦G⟧
  := by
  dsimp [sym2FlagDensity₂, sym2InducedLabeledSubgraphListDensityLifted₂]

theorem flagDensity₂_eq_sym2FlagDensity₂
    {k : ℕ} {σ : Sym2FlagType k} {m₀ m₁ n : ℕ}
    (F₀ : Sym2Flag σ m₀) (F₁ : Sym2Flag σ m₁) (G : Sym2Flag σ n) :
    flagDensity₂ F₀.toFlag F₁.toFlag G.toFlag = sym2FlagDensity₂ F₀ F₁ G
  := by
  rcases Quotient.exists_rep F₀ with ⟨F₀, rfl⟩
  rcases Quotient.exists_rep F₁ with ⟨F₁, rfl⟩
  rcases Quotient.exists_rep G with ⟨G, rfl⟩
  dsimp [Sym2Flag.toFlag, Sym2LabeledGraph.toFlag]
  rw [← labeledSubgraphListDensity_eq_flagDensity₂,
    ← sym2InducedLabeledSubgraphListDensity_eq_sym2FlagDensity₂]
  exact labeledSubgraphListDensity_labeledGraphPairToList_eq F₀ F₁ G

end FlagAlgebras.Compute
