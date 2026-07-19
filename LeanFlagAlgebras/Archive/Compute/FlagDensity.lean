module

public import «LeanFlagAlgebras».Archive.Compute.Basic

@[export] public section

/-!
# (Archived) Computable flag density for `Sym2`-encoded flags

ARCHIVED / SUPERSEDED — this file is **not** part of the build (its import is
commented out in `LeanFlagAlgebras.lean`). It is an early computable
implementation of induced-labeled-subgraph counting and the single/pair flag
densities (`sym2FlagDensity₁`, `sym2FlagDensity₂`) for the `Sym2`-encoded flags,
together with lemmas matching them to the abstract `flagDensity₁/₂`. The active
version lives in `LeanFlagAlgebras/FlagAlgebra/Compute/FlagDensity.lean`.
-/

namespace Archive.Compute

open FlagAlgebras
open SimpleGraph

abbrev Sym2LabeledGraphList
    {T : Type} (σ : FlagType T) (t : ℕ) (Vl : Fin t → ℕ)
  := ∀ (i : Fin t), Sym2LabeledGraph σ (Vl i)

def sym2LabeledGraphToList
    {T : Type} {σ : FlagType T} {n : ℕ} (G : Sym2LabeledGraph σ n)
    : Sym2LabeledGraphList σ 1 (fun _ ↦ n)
  :=
  fun _ ↦ G

def sym2LabeledGraphPairToList
    {T : Type} {σ : FlagType T} {n₀ n₁ : ℕ} (G₀ : Sym2LabeledGraph σ n₀) (G₁ : Sym2LabeledGraph σ n₁)
    : Sym2LabeledGraphList σ 2 (fun i ↦ match i with | 0 => n₀ | 1 => n₁)
  :=
  fun i ↦ match i with | 0 => G₀ | 1 => G₁

def Sym2LabeledGraphList.toLabeledGraphList
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {t : ℕ} {Vl : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) : LabeledGraphList σ t (fun i ↦ Fin (Vl i))
  :=
  fun i ↦ (Hl i).toLabeledGraph

@[ext]
structure Sym2InducedLabeledSubgraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} (G : Sym2LabeledGraph σ n) where
  verts : Finset (Fin n)
  verts_subset : G.type_verts ⊆ verts

instance
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
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
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) : Finset (Sym2 (Fin n))
  :=
  G.edges.filter (fun e ↦ ∀ v ∈ e, v ∈ H.verts)

theorem Sym2InducedLabeledSubgraph.edges_valid
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) :
    ∀ e ∈ H.edges, ¬e.IsDiag
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact G.edges_valid e he.1

theorem Sym2InducedLabeledSubgraph.edges_subset
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) :
    H.edges ⊆ G.edges
  := by
  intro e he
  simp only [edges, Finset.mem_filter] at he
  exact he.1

def Sym2InducedLabeledSubgraph.toLabeledSubraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) : LabeledSubgraph σ G.toLabeledGraph where
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
        rw [← G.type_embed.map_rel_iff]
        simp
        refine ⟨h, ?_⟩
        intro hab
        apply G.edges_valid (Sym2.mk (G.type_embed a, G.type_embed b)) h
        exact Sym2.mk_isDiag_iff.mpr (congrArg (G.type_embed) hab)
      · intro h
        constructor
        · rw [← G.type_embed.map_rel_iff] at h
          simp at h
          exact h.1
        · exact ⟨H.verts_subset (G.mem_type_verts a), H.verts_subset (G.mem_type_verts b)⟩
  }
  embed_eq := by simp [Sym2LabeledGraph.toLabeledGraph]

theorem Sym2InducedLabeledSubgraph.toLabeledSubraph_isInduced
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} (H : Sym2InducedLabeledSubgraph G) :
    H.toLabeledSubraph.IsInduced
  := by
  intro u hu v hv h_adj
  simp [toLabeledSubraph, edges, Sym2LabeledGraph.toLabeledGraph] at *
  exact ⟨h_adj.1, hu, hv⟩

abbrev Sym2InducedLabeledSubgraphList
    (t : ℕ) {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n)
  := Fin t → Sym2InducedLabeledSubgraph G

def predDisjointSym2InducedLabeledSubgraphList
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} (Hl : Sym2InducedLabeledSubgraphList t G) : Prop
  :=
  ∀ (i j : Fin t), i ≠ j → ((Hl i).verts \ G.type_verts) ∩ ((Hl j).verts \ G.type_verts) = ∅

def predIsoSym2LabeledHl
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} {Vl  : Fin t → ℕ} (Hl : Sym2LabeledGraphList σ t Vl)
    : Sym2InducedLabeledSubgraphList t G → Prop
  := fun Gl ↦
      (∀ (i : Fin t), Nonempty ((Gl i).toLabeledSubraph.coe ≃f (Hl i).toLabeledGraph))
      ∧ predDisjointSym2InducedLabeledSubgraphList Gl

instance
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    {G : Sym2LabeledGraph σ n} {Vl  : Fin t → ℕ} (Hl : Sym2LabeledGraphList σ t Vl) :
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
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ}
    (G : Sym2LabeledGraph σ n) {Vl  : Fin t → ℕ} (Hl : Sym2LabeledGraphList σ t Vl)
    : Finset (Sym2InducedLabeledSubgraphList t G)
  :=
  { Gl | predIsoSym2LabeledHl Hl Gl }

def sym2InducedLabeledSubgraphListCount
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) : ℕ
  :=
  (finsetOfSym2InducedLabeledSubgraphListIsoHl G Hl).card

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
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
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
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) : ℚ
  :=
  let r_list (i : Fin t) := Vl i - Fintype.card T
  sym2InducedLabeledSubgraphListCount Hl G / multinomialCoefficient r_list (n - Fintype.card T)

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
    {t : ℕ} {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {n : ℕ} {Vl  : Fin t → ℕ}
    (Hl : Sym2LabeledGraphList σ t Vl) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListDensity Hl.toLabeledGraphList G.toLabeledGraph =
    sym2InducedLabeledSubgraphListDensity Hl G
  := by
  dsimp only [labeledSubgraphListDensity, sym2InducedLabeledSubgraphListDensity]
  congr!
  · exact labeledSubgraphListCount_eq Hl G
  · simp only [LabeledGraph.size, Fintype.card_fin]
  · simp only [LabeledGraph.size, Fintype.card_fin]

theorem labeledSubgraphListDensity_labeledGraphToList_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
    (H : Sym2LabeledGraph σ m) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListDensity (labeledGraphToList H.toLabeledGraph) G.toLabeledGraph =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList H) G
  :=
  labeledSubgraphListDensity_eq (sym2LabeledGraphToList H) G

theorem labeledSubgraphListDensity_labeledGraphPairToList_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
    (H₀ : Sym2LabeledGraph σ m₀) (H₁ : Sym2LabeledGraph σ m₁) (G : Sym2LabeledGraph σ n) :
    labeledSubgraphListDensity (labeledGraphPairToList H₀.toLabeledGraph H₁.toLabeledGraph) G.toLabeledGraph =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList H₀ H₁) G
  := by
  rw [← labeledSubgraphListDensity_eq]
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
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
    {F F' : Sym2LabeledGraph σ m} (hF_eqv : F ∼sf F')
    {G G' : Sym2LabeledGraph σ n} (hG_eqv : G ∼sf G') :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) G =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F') G'
  := by
  rw [← labeledSubgraphListDensity_eq, ← labeledSubgraphListDensity_eq]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF_eqv.some
  · exact hG_eqv.some

def sym2InducedLabeledSubgraphListDensityLifted₁
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
    (F : Sym2LabeledGraph σ m) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) H) ?_ G
  intro _ _ h_eqv
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphToList_respect_eqv (sym2LabeledGraphEqv.refl F) h_eqv

theorem sym2InducedLabeledSubgraphListDensityLifted₁_respect_eqv
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
    {F F' : Sym2LabeledGraph σ m} (hF_eqv : F ∼sf F')
    (G : Sym2Flag σ n) :
    sym2InducedLabeledSubgraphListDensityLifted₁ F G =
    sym2InducedLabeledSubgraphListDensityLifted₁ F' G
  := by
  dsimp [sym2InducedLabeledSubgraphListDensityLifted₁]
  congr
  funext H
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphToList_respect_eqv hF_eqv (sym2LabeledGraphEqv.refl H)

/-- Single-flag density: density of `Sym2Flag` `F` (size `m`) inside `G` (size
`n`). Computable counterpart of the abstract `flagDensity₁`. -/
def sym2FlagDensity₁
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
    (F : Sym2Flag σ m) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedLabeledSubgraphListDensityLifted₁ H G) ?_ F
  intro _ _ h_eqv
  exact sym2InducedLabeledSubgraphListDensityLifted₁_respect_eqv h_eqv G

theorem sym2InducedLabeledSubgraphListDensity_eq_sym2FlagDensity₁
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
    (F : Sym2LabeledGraph σ m) (G : Sym2LabeledGraph σ n) :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphToList F) G = sym2FlagDensity₁ ⟦F⟧ ⟦G⟧
  := by
  dsimp [sym2FlagDensity₁, sym2InducedLabeledSubgraphListDensityLifted₁]

theorem flagDensity₁_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m n : ℕ}
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
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
    {F₀ F₀' : Sym2LabeledGraph σ m₀} (hF₀_eqv : F₀ ∼sf F₀')
    {F₁ F₁' : Sym2LabeledGraph σ m₁} (hF₁_eqv : F₁ ∼sf F₁')
    {G G' : Sym2LabeledGraph σ n} (hG_eqv : G ∼sf G') :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀ F₁) G =
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀' F₁') G'
  := by
  rw [← labeledSubgraphListDensity_eq, ← labeledSubgraphListDensity_eq]
  apply labeledSubgraphListDensity_respect_eqv
  · intro i
    match i with
    | 0 => exact hF₀_eqv.some
    | 1 => exact hF₁_eqv.some
  · exact hG_eqv.some

def sym2InducedLabeledSubgraphListDensityLifted₂
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
    (F₀ : Sym2LabeledGraph σ m₀) (F₁ : Sym2LabeledGraph σ m₁) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun H ↦ sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀ F₁) H) ?_ G
  intro _ _ h_eqv
  exact sym2InducedLabeledSubgraphListDensity_sym2LabeledGraphPairToList_respect_eqv
    (sym2LabeledGraphEqv.refl F₀) (sym2LabeledGraphEqv.refl F₁) h_eqv

theorem sym2InducedLabeledSubgraphListDensityLifted₂_respect_eqv
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
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

/-- Flag-pair density: joint density of `F₀, F₁` inside `G`. Computable
counterpart of the abstract `flagDensity₂`. -/
def sym2FlagDensity₂
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
    (F₀ : Sym2Flag σ m₀) (F₁ : Sym2Flag σ m₁) (G : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift₂ (fun H₀ H₁ ↦ sym2InducedLabeledSubgraphListDensityLifted₂ H₀ H₁ G) ?_ F₀ F₁
  intro _ _ _ _ h_eqv h_eqv'
  exact sym2InducedLabeledSubgraphListDensityLifted₂_respect_eqv h_eqv h_eqv' G

theorem sym2InducedLabeledSubgraphListDensity_eq_sym2FlagDensity₂
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
    (F₀ : Sym2LabeledGraph σ m₀) (F₁ : Sym2LabeledGraph σ m₁) (G : Sym2LabeledGraph σ n) :
    sym2InducedLabeledSubgraphListDensity (sym2LabeledGraphPairToList F₀ F₁) G =
    sym2FlagDensity₂ ⟦F₀⟧ ⟦F₁⟧ ⟦G⟧
  := by
  dsimp [sym2FlagDensity₂, sym2InducedLabeledSubgraphListDensityLifted₂]

theorem flagDensity₂_eq
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] {m₀ m₁ n : ℕ}
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

end Archive.Compute
