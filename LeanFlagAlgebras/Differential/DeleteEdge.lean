import «LeanFlagAlgebras».Differential.DeleteVertex

/-! # The edge-deletion operator `∂_E` (Razborov §4.3, Lemma 4.4)

Razborov's second variation principle corresponds to edge deletion, formulated
for undirected graphs only. There are exactly two types of size two: `E`
(an edge between the two labelled vertices) and `Ē` (a non-edge). This file
defines:

* `edgeType`/`nonEdgeType` — the types `E` and `Ē`;
* `edgeRootedAt G v₁ v₂ h` — the `E`-flag `(G, v₁, v₂)` for an edge
  `(v₁, v₂) ∈ E(G)`;
* `deleteEdge G e` — the graph `G` with the edge `e` removed;
* `fillGraph`/`fillFlag`/`fillVec` — the natural isomorphism
  `Fill : A^Ē → A^E` adding an edge between the two labelled vertices;
* `partialEdgeVec` — Razborov's edge-deletion operator
  `∂_E G = (ℓ(ℓ−1)/2) (Fill(μ_ℓ^Ē(G)) − μ_ℓ^E(G))`, extended linearly;
* `partialEdge` — the induced linear map `A⁰ → A^E` (Lemma 4.4 b)).

The main results are Razborov's Lemma 4.4:

* a) `edge_deletion_density` : for a model `H` on `ℓ` vertices, a graph `G` on
  `L ≥ ℓ` vertices and an edge `(v₁, v₂) ∈ E(G)`,
  `p(H, G − (v₁,v₂)) = p(H, G) + (2/(L(L−1))) · p^{(G,v₁,v₂)}(∂_E H)`;
* b) `partialEdgeVec_zeroSpace` : `∂_E(K⁰) ⊆ K^E`, so `∂_E` descends to a
  linear map `partialEdge : A⁰ → A^E`.

Unlike the vertex case there is no analogue of Lemma 4.2 c): averaging does
not kill the image of `∂_E`; instead extremality gives the *inequality* of
Theorem 4.5 (see `Grad.lean`).

The combinatorial input to a) is the single counting identity
`edge_deletion_counting` (Razborov's pair of total-probability computations
with the `{v₁,v₂} ⊄ V` terms cancelled): conditioning a uniformly random
`ℓ`-subset `V ⊆ V(G)` on `{v₁, v₂} ⊆ V`, and using that `G|_V = (G−e)|_V`
whenever `V` misses one of `v₁, v₂`. -/

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

/-! ## The two types of size two -/

/-- The type `E` of size two: an edge between the two labelled vertices. -/
abbrev edgeType : FlagType (Fin 2) := ⊤

/-- The type `Ē` of size two: a non-edge between the two labelled vertices. -/
abbrev nonEdgeType : FlagType (Fin 2) := ⊥

theorem fin_two_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  have hx := x.isLt
  have : x.val = 0 ∨ x.val = 1 := by omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem fin_two_ne_iff {a b : Fin 2} : a ≠ b ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have hv : a.val ≠ b.val := fun hh => h (Fin.ext hh)
    have ha := a.isLt
    have hb := b.isLt
    have : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) := by omega
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
    · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-! ## Edge-rooted flags and edge deletion -/

/-- The `E`-flag `(G, v₁, v₂)`: the graph `G` with the two labels placed on
the endpoints of the edge `(v₁, v₂)`. -/
def edgeRootedAt {V : Type} (G : LabeledGraph ∅ₜ V) (v₁ v₂ : V)
    (h_adj : G.graph.Adj v₁ v₂) : LabeledGraph edgeType V where
  graph := G.graph
  type_embed := {
    toFun := ![v₁, v₂]
    inj' := by
      intro a b hab
      by_contra hne
      rcases fin_two_ne_iff.mp hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h_adj.ne (by simpa using hab)
      · exact h_adj.ne (by simpa using hab.symm)
    map_rel_iff' := by
      intro a b
      rw [SimpleGraph.top_adj]
      constructor
      · intro h
        intro hab
        subst hab
        exact G.graph.irrefl h
      · intro hab
        rcases fin_two_ne_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa using h_adj
        · simpa using h_adj.symm
  }

@[simp]
theorem edgeRootedAt_graph {V : Type} (G : LabeledGraph ∅ₜ V) (v₁ v₂ : V)
    (h : G.graph.Adj v₁ v₂)
    : (edgeRootedAt G v₁ v₂ h).graph = G.graph
  := rfl

theorem edgeType_adj_zero_one : edgeType.Adj 0 1 :=
  (SimpleGraph.top_adj 0 1).mpr (by decide)

/-- The two labelled vertices of an `E`-flag are adjacent. -/
theorem edgeFlag_roots_adj {V : Type} (R : LabeledGraph edgeType V)
    : R.graph.Adj (R.type_embed 0) (R.type_embed 1)
  :=
  (type_embed_Adj_iff R 0 1).mp edgeType_adj_zero_one

/-- Every `E`-flag is of the form `edgeRootedAt G v₁ v₂`: rooting the
underlying unlabelled graph at the two labelled vertices recovers the flag. -/
theorem edgeRootedAt_unlabeledGraph_self {V : Type} (R : LabeledGraph edgeType V)
    : edgeRootedAt (unlabeledGraph R) (R.type_embed 0) (R.type_embed 1)
        (edgeFlag_roots_adj R) = R
  := by
  obtain ⟨graph, emb⟩ := R
  dsimp only [edgeRootedAt, unlabeledGraph]
  congr 1
  ext x
  rcases fin_two_eq_zero_or_one x with rfl | rfl
  · rfl
  · rfl

/-- The graph `G` with the edge `e` removed. -/
def deleteEdge {V : Type} (G : LabeledGraph ∅ₜ V) (e : Sym2 V)
    : LabeledGraph ∅ₜ V where
  graph := G.graph \ SimpleGraph.fromEdgeSet {e}
  type_embed := RelEmbedding.ofIsEmpty _ _

@[simp]
theorem deleteEdge_adj {V : Type} (G : LabeledGraph ∅ₜ V) (e : Sym2 V) (u w : V)
    : (deleteEdge G e).graph.Adj u w ↔ G.graph.Adj u w ∧ ¬(s(u, w) = e)
  := by
  dsimp only [deleteEdge]
  rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hmem => h2 ⟨hmem, h1.ne⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hmem => h2 hmem.1⟩

/-! ## The `Fill` isomorphism `A^Ē → A^E` -/

/-- Add an edge between the two labelled vertices of an `Ē`-flag, making it an
`E`-flag on the same vertex set. -/
def fillGraph {V : Type} (G : LabeledGraph nonEdgeType V) : LabeledGraph edgeType V where
  graph := G.graph ⊔ SimpleGraph.fromEdgeSet {s(G.type_embed 0, G.type_embed 1)}
  type_embed := {
    toFun := G.type_embed
    inj' := G.type_embed.injective
    map_rel_iff' := by
      intro a b
      rw [SimpleGraph.top_adj, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro (h | ⟨heq, hne⟩)
        · intro hab
          subst hab
          exact G.graph.irrefl h
        · intro hab
          subst hab
          exact hne rfl
      · intro hab
        right
        constructor
        · rcases fin_two_ne_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        · intro heq
          exact hab (G.type_embed.injective heq)
  }

@[simp]
theorem fillGraph_type_embed {V : Type} (G : LabeledGraph nonEdgeType V) (i : Fin 2)
    : (fillGraph G).type_embed i = G.type_embed i
  := rfl

/-- `Fill` respects labelled-graph isomorphism. -/
def fillGraph_iso {V W : Type} {G : LabeledGraph nonEdgeType V}
    {G' : LabeledGraph nonEdgeType W} (φ : G ≃f G')
    : fillGraph G ≃f fillGraph G' where
  graph_iso := {
    toEquiv := φ.graph_iso.toEquiv
    map_rel_iff' := by
      intro u v
      have h0 : φ.graph_iso (G.type_embed 0) = G'.type_embed 0 := congrFun φ.type_preserve 0
      have h1 : φ.graph_iso (G.type_embed 1) = G'.type_embed 1 := congrFun φ.type_preserve 1
      have hedge : s(φ.graph_iso u, φ.graph_iso v) = s(G'.type_embed 0, G'.type_embed 1)
          ↔ s(u, v) = s(G.type_embed 0, G.type_embed 1) := by
        rw [← h0, ← h1, ← Sym2.map_pair_eq, ← Sym2.map_pair_eq]
        exact ⟨fun h => Sym2.map.injective φ.graph_iso.injective h, fun h => congrArg _ h⟩
      have hne : φ.graph_iso u ≠ φ.graph_iso v ↔ u ≠ v :=
        not_congr ⟨fun h => φ.graph_iso.injective h, fun h => congrArg _ h⟩
      dsimp only [fillGraph, RelIso.coe_fn_toEquiv]
      rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
        SimpleGraph.fromEdgeSet_adj]
      simp only [Set.mem_singleton_iff]
      rw [φ.graph_iso.map_adj_iff, hedge, hne]
  }
  type_preserve := by
    ext t
    exact congrFun φ.type_preserve t

/-- `Fill` on flags: the natural isomorphism `ℱ^Ē → ℱ^E` (adding the edge
between the labelled vertices), lifted through the quotient. -/
noncomputable def fillFlag {V : Type} : Flag nonEdgeType V → Flag edgeType V :=
  Quotient.map fillGraph (fun _ _ h => Nonempty.intro (fillGraph_iso h.some))

theorem fillFlag_mk {V : Type} (G : LabeledGraph nonEdgeType V)
    : fillFlag ⟦G⟧ = ⟦fillGraph G⟧
  := rfl

/-- `Fill : ℝℱ^Ē → ℝℱ^E` as a linear map on flag vectors. -/
noncomputable def fillVec : FlagVector nonEdgeType → FlagVector edgeType :=
  linearExtension (fun F : FinFlag nonEdgeType => basisVector ⟨F.1, fillFlag F.2⟩)

/-! ## The edge-deletion operator `∂_E` -/

/-- Razborov's edge-deletion operator on formal combinations of models:
`∂_E H = (ℓ(ℓ−1)/2) (Fill(μ_ℓ^Ē(H)) − μ_ℓ^E(H))` for a model `H` on `ℓ`
vertices, extended linearly to `ℝℱ⁰`. -/
noncomputable def partialEdgeVec : FlagVector ∅ₜ → FlagVector edgeType :=
  linearExtension (fun H : FinFlag ∅ₜ =>
    ((H.1 : ℝ) * ((H.1 : ℝ) - 1) / 2) • (fillVec (muVec nonEdgeType H) - muVec edgeType H))

@[simp]
theorem partialEdgeVec_basisVector (H : FinFlag ∅ₜ)
    : partialEdgeVec (basisVector H)
      = ((H.1 : ℝ) * ((H.1 : ℝ) - 1) / 2) • (fillVec (muVec nonEdgeType H) - muVec edgeType H)
  := by
  dsimp only [partialEdgeVec]
  rw [linearExtension_basisVector]

theorem partialEdgeVec_sub (f f' : FlagVector ∅ₜ)
    : partialEdgeVec (f - f') = partialEdgeVec f - partialEdgeVec f'
  := by
  dsimp only [partialEdgeVec]
  rw [linearExtension_sub]

theorem partialEdgeVec_eq_sum (f : FlagVector ∅ₜ)
    : partialEdgeVec f = ∑ M ∈ f.support, f M • partialEdgeVec (basisVector M)
  := by
  simp_rw [partialEdgeVec_basisVector]
  rfl

/-! ## Density evaluations of the two halves of `∂_E` -/

theorem densityEval_fillVec_muVec (M : FinFlag ∅ₜ) (R : FinFlag edgeType)
    : densityEval (fillVec (muVec nonEdgeType M)) R
      = ∑ F ∈ labelExtensions M.2 nonEdgeType, (flagDensity₁ (fillFlag F) R.2 : ℝ)
  := by
  dsimp only [muVec, fillVec]
  rw [linearExtension_sum, densityEval_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [linearExtension_basisVector, densityEval_basisVector]

/-! ## Glue lemmas for the counting identity -/

theorem edgeRootedAt_type_verts_subset {V : Type} (G : LabeledGraph ∅ₜ V) {v₁ v₂ : V}
    (h : G.graph.Adj v₁ v₂) {S : Set V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S)
    : (edgeRootedAt G v₁ v₂ h).type_verts ⊆ S
  := by
  intro u hu
  rw [LabeledGraph.mem_type_verts] at hu
  obtain ⟨t, rfl⟩ := hu
  rcases fin_two_eq_zero_or_one t with rfl | rfl
  · exact h₁
  · exact h₂

theorem mem_of_edgeRootedAt_subset₁ {V : Type} {G : LabeledGraph ∅ₜ V} {v₁ v₂ : V}
    {h : G.graph.Adj v₁ v₂} {S : Set V}
    (hsub : (edgeRootedAt G v₁ v₂ h).type_verts ⊆ S)
    : v₁ ∈ S
  :=
  hsub ((edgeRootedAt G v₁ v₂ h).type_verts_contain 0)

theorem mem_of_edgeRootedAt_subset₂ {V : Type} {G : LabeledGraph ∅ₜ V} {v₁ v₂ : V}
    {h : G.graph.Adj v₁ v₂} {S : Set V}
    (hsub : (edgeRootedAt G v₁ v₂ h).type_verts ⊆ S)
    : v₂ ∈ S
  :=
  hsub ((edgeRootedAt G v₁ v₂ h).type_verts_contain 1)

theorem unlabeledGraph_induced_edgeRootedAt {V : Type} (G : LabeledGraph ∅ₜ V) {v₁ v₂ : V}
    (h : G.graph.Adj v₁ v₂) (S : Set V)
    (hsub : (edgeRootedAt G v₁ v₂ h).type_verts ⊆ S)
    : unlabeledGraph ((LabeledSubgraph.inducedLabeledSubgraph (edgeRootedAt G v₁ v₂ h) S hsub).coe)
      = (LabeledSubgraph.inducedLabeledSubgraph G S (emptyType_type_verts_subset G S)).coe
  :=
  emptyType_labeledGraph_ext rfl

/-- Induced subgraphs of `G` and of `G − (v₁,v₂)` on a vertex set missing one
of `v₁, v₂` coincide. -/
noncomputable def deleteEdge_induce_iso_of_not_both {L : ℕ} (G : LabeledGraph ∅ₜ (Fin L))
    (v₁ v₂ : Fin L) (S : Set (Fin L)) (h : ¬(v₁ ∈ S ∧ v₂ ∈ S))
    : (LabeledSubgraph.inducedLabeledSubgraph G S (emptyType_type_verts_subset _ _)).coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph (deleteEdge G s(v₁, v₂)) S
          (emptyType_type_verts_subset _ _)).coe where
  graph_iso := {
    toEquiv := Equiv.refl _
    map_rel_iff' := by
      intro a b
      constructor
      · rintro ⟨ha, hb, hadj⟩
        exact ⟨a.property, b.property, ((deleteEdge_adj G _ _ _).mp hadj).1⟩
      · rintro ⟨ha, hb, hadj⟩
        refine ⟨a.property, b.property, (deleteEdge_adj G _ _ _).mpr ⟨hadj, ?_⟩⟩
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h ⟨h1 ▸ a.property, h2 ▸ b.property⟩
        · exact h ⟨h2 ▸ b.property, h1 ▸ a.property⟩
  }
  type_preserve := by
    ext x
    exact x.elim0

/-- The `Ē`-flag `(X, v₁, v₂)` for a *non*-edge `(v₁, v₂)` of `X`. -/
def nonEdgeRootedAt {V : Type} (X : LabeledGraph ∅ₜ V) (v₁ v₂ : V)
    (hne : v₁ ≠ v₂) (h_nadj : ¬X.graph.Adj v₁ v₂) : LabeledGraph nonEdgeType V where
  graph := X.graph
  type_embed := {
    toFun := ![v₁, v₂]
    inj' := by
      intro a b hab
      by_contra hcon
      rcases fin_two_ne_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h12 : v₁ = v₂ := by simpa using hab
        exact hne h12
      · have h21 : v₂ = v₁ := by simpa using hab
        exact hne h21.symm
    map_rel_iff' := by
      intro a b
      rw [SimpleGraph.bot_adj]
      constructor
      · intro h
        rcases fin_two_eq_zero_or_one a with rfl | rfl <;>
          rcases fin_two_eq_zero_or_one b with rfl | rfl
        · have h' : X.graph.Adj v₁ v₁ := by simpa using h
          exact X.graph.irrefl h'
        · have h' : X.graph.Adj v₁ v₂ := by simpa using h
          exact h_nadj h'
        · have h' : X.graph.Adj v₂ v₁ := by simpa using h
          exact h_nadj h'.symm
        · have h' : X.graph.Adj v₂ v₂ := by simpa using h
          exact X.graph.irrefl h'
      · intro h
        exact h.elim
  }

theorem deleteEdge_not_adj {V : Type} (G : LabeledGraph ∅ₜ V) (v₁ v₂ : V)
    : ¬(deleteEdge G s(v₁, v₂)).graph.Adj v₁ v₂
  :=
  fun hc => ((deleteEdge_adj G _ _ _).mp hc).2 rfl

theorem nonEdgeRootedAt_type_verts_subset {V : Type} (X : LabeledGraph ∅ₜ V) {v₁ v₂ : V}
    (hne : v₁ ≠ v₂) (h_nadj : ¬X.graph.Adj v₁ v₂) {S : Set V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S)
    : (nonEdgeRootedAt X v₁ v₂ hne h_nadj).type_verts ⊆ S
  := by
  intro u hu
  rw [LabeledGraph.mem_type_verts] at hu
  obtain ⟨t, rfl⟩ := hu
  rcases fin_two_eq_zero_or_one t with rfl | rfl
  · exact h₁
  · exact h₂

theorem unlabeledGraph_induced_nonEdgeRootedAt {V : Type} (X : LabeledGraph ∅ₜ V) {v₁ v₂ : V}
    (hne : v₁ ≠ v₂) (h_nadj : ¬X.graph.Adj v₁ v₂) (S : Set V)
    (hsub : (nonEdgeRootedAt X v₁ v₂ hne h_nadj).type_verts ⊆ S)
    : unlabeledGraph
        ((LabeledSubgraph.inducedLabeledSubgraph (nonEdgeRootedAt X v₁ v₂ hne h_nadj) S hsub).coe)
      = (LabeledSubgraph.inducedLabeledSubgraph X S (emptyType_type_verts_subset X S)).coe
  :=
  emptyType_labeledGraph_ext rfl

/-- Filling the `Ē`-rooted induced subgraph of `G − (v₁,v₂)` on `S ⊇ {v₁,v₂}`
recovers the `E`-rooted induced subgraph of `G`: the only edge removed inside
`S` is the rooted one, which `Fill` restores. -/
noncomputable def fill_induced_deleteEdge_iso {L : ℕ} (G : LabeledGraph ∅ₜ (Fin L))
    {v₁ v₂ : Fin L} (h_adj : G.graph.Adj v₁ v₂) (S : Set (Fin L)) (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S)
    : fillGraph ((LabeledSubgraph.inducedLabeledSubgraph
        (nonEdgeRootedAt (deleteEdge G s(v₁, v₂)) v₁ v₂ h_adj.ne (deleteEdge_not_adj G v₁ v₂))
        S (nonEdgeRootedAt_type_verts_subset _ _ _ h₁ h₂)).coe)
      ≃f (LabeledSubgraph.inducedLabeledSubgraph (edgeRootedAt G v₁ v₂ h_adj) S
          (edgeRootedAt_type_verts_subset G h_adj h₁ h₂)).coe where
  graph_iso := {
    toEquiv := Equiv.refl _
    map_rel_iff' := by
      intro a b
      have hval0 : (((LabeledSubgraph.inducedLabeledSubgraph
          (nonEdgeRootedAt (deleteEdge G s(v₁, v₂)) v₁ v₂ h_adj.ne (deleteEdge_not_adj G v₁ v₂))
          S (nonEdgeRootedAt_type_verts_subset _ _ _ h₁ h₂)).coe.type_embed 0) : Fin L) = v₁ :=
        (LabeledSubgraph.inducedLabeledSubgraph
          (nonEdgeRootedAt (deleteEdge G s(v₁, v₂)) v₁ v₂ h_adj.ne (deleteEdge_not_adj G v₁ v₂))
          S (nonEdgeRootedAt_type_verts_subset _ _ _ h₁ h₂)).embed_eq 0
      have hval1 : (((LabeledSubgraph.inducedLabeledSubgraph
          (nonEdgeRootedAt (deleteEdge G s(v₁, v₂)) v₁ v₂ h_adj.ne (deleteEdge_not_adj G v₁ v₂))
          S (nonEdgeRootedAt_type_verts_subset _ _ _ h₁ h₂)).coe.type_embed 1) : Fin L) = v₂ :=
        (LabeledSubgraph.inducedLabeledSubgraph
          (nonEdgeRootedAt (deleteEdge G s(v₁, v₂)) v₁ v₂ h_adj.ne (deleteEdge_not_adj G v₁ v₂))
          S (nonEdgeRootedAt_type_verts_subset _ _ _ h₁ h₂)).embed_eq 1
      constructor
      · -- an edge of `G[S]` is an edge of `(G−e)[S]` or the restored root edge
        rintro ⟨ha, hb, hadj⟩
        by_cases heq : s(a.val, b.val) = s(v₁, v₂)
        · right
          rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          refine ⟨?_, ?_⟩
          · apply Sym2.map.injective Subtype.val_injective
            rw [Sym2.map_pair_eq, Sym2.map_pair_eq, hval0, hval1]
            exact heq
          · intro hab
            exact G.graph.irrefl (hab ▸ hadj)
        · left
          exact ⟨a.property, b.property, (deleteEdge_adj G _ _ _).mpr ⟨hadj, heq⟩⟩
      · rintro (⟨ha, hb, hadj⟩ | hroot)
        · exact ⟨a.property, b.property, ((deleteEdge_adj G _ _ _).mp hadj).1⟩
        · rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff] at hroot
          obtain ⟨heq, -⟩ := hroot
          have hvals : s(a.val, b.val) = s(v₁, v₂) := by
            have h3 := congrArg (Sym2.map Subtype.val) heq
            rw [Sym2.map_pair_eq, Sym2.map_pair_eq, hval0, hval1] at h3
            exact h3
          refine ⟨a.property, b.property, ?_⟩
          rcases Sym2.eq_iff.mp hvals with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
          · show G.graph.Adj a.val b.val
            rw [ha1, hb1]
            exact h_adj
          · show G.graph.Adj a.val b.val
            rw [ha1, hb1]
            exact h_adj.symm
  }
  type_preserve := by
    ext t
    rcases fin_two_eq_zero_or_one t with rfl | rfl
    · rfl
    · rfl

/-! ## The counting identity behind Lemma 4.4 a) -/

/-- The combined total-probability computation of Razborov's Lemma 4.4 a):
conditioning a uniformly random `ℓ`-subset `V ⊆ V(G)` on `{v₁, v₂} ⊆ V` in
both `G` and `G − (v₁,v₂)` and cancelling the (equal) `{v₁,v₂} ⊄ V`
contributions,

`p(H, G−e) − p(H, G)
   = (ℓ(ℓ−1)/(L(L−1))) · (p^{(G,v₁,v₂)}(Fill(μ_ℓ^Ē H)) − p^{(G,v₁,v₂)}(μ_ℓ^E H))`.

Here `P[G|_V ≅ H ∣ {v₁,v₂} ⊆ V] = p^{(G,v₁,v₂)}(μ_ℓ^E(H))` and
`P[(G−e)|_V ≅ H ∣ {v₁,v₂} ⊆ V] = p^{(G,v₁,v₂)}(Fill(μ_ℓ^Ē(H)))` (removing the
rooted edge turns an induced `E`-rooted copy into an `Ē`-rooted one), while
`G|_V = (G−e)|_V` whenever `V` misses one of `v₁, v₂`. -/
theorem edge_deletion_counting {ℓ L : ℕ} (H : FlagWithSize ∅ₜ ℓ) (hL : ℓ ≤ L)
    (G : LabeledGraph ∅ₜ (Fin L)) (v₁ v₂ : Fin L) (h_adj : G.graph.Adj v₁ v₂)
    : (flagDensity₁ H ⟦deleteEdge G s(v₁, v₂)⟧ : ℚ) - flagDensity₁ H ⟦G⟧
      = ((ℓ : ℚ) * ((ℓ : ℚ) - 1) / ((L : ℚ) * ((L : ℚ) - 1)))
          * ((∑ F ∈ labelExtensions H nonEdgeType,
                flagDensity₁ (fillFlag F) ⟦edgeRootedAt G v₁ v₂ h_adj⟧)
             - ∑ F ∈ labelExtensions H edgeType,
                flagDensity₁ F ⟦edgeRootedAt G v₁ v₂ h_adj⟧)
  := by
  sorry

/-! ## Lemma 4.4 a) -/

/-- **Razborov, Lemma 4.4 a)**: for a model `H` on `ℓ` vertices, a graph `G`
on `L ≥ ℓ` vertices (`L ≥ 2`) and an edge `(v₁, v₂) ∈ E(G)`,

`p(H, G − (v₁,v₂)) = p(H, G) + (2/(L(L−1))) · p^{(G,v₁,v₂)}(∂_E H)`. -/
theorem edge_deletion_density (H : FinFlag ∅ₜ) {L : ℕ} (hL : H.1 ≤ L) (hL2 : 2 ≤ L)
    (G : LabeledGraph ∅ₜ (Fin L)) (v₁ v₂ : Fin L) (h_adj : G.graph.Adj v₁ v₂)
    : (flagDensity₁ H.2 ⟦deleteEdge G s(v₁, v₂)⟧ : ℝ)
      = (flagDensity₁ H.2 ⟦G⟧ : ℝ)
        + (2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * densityEval (partialEdgeVec (basisVector H)) ⟨L, ⟦edgeRootedAt G v₁ v₂ h_adj⟧⟩
  := by
  have hcount := edge_deletion_counting H.2 hL G v₁ v₂ h_adj
  rw [partialEdgeVec_basisVector, densityEval_smul, densityEval_sub,
    densityEval_fillVec_muVec, densityEval_muVec]
  rw [← Rat.cast_sum, ← Rat.cast_sum]
  set P : ℚ := flagDensity₁ H.2 ⟦deleteEdge G s(v₁, v₂)⟧ with hP
  set p : ℚ := flagDensity₁ H.2 ⟦G⟧ with hp
  set SĒ : ℚ := ∑ F ∈ labelExtensions H.2 nonEdgeType,
      flagDensity₁ (fillFlag F) ⟦edgeRootedAt G v₁ v₂ h_adj⟧ with hSĒ
  set SE : ℚ := ∑ F ∈ labelExtensions H.2 edgeType,
      flagDensity₁ F ⟦edgeRootedAt G v₁ v₂ h_adj⟧ with hSE
  have hL2' : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hLpos : (0 : ℝ) < (L : ℝ) * ((L : ℝ) - 1) := by nlinarith
  have key : (P : ℝ) - (p : ℝ)
      = ((H.1 : ℝ) * ((H.1 : ℝ) - 1) / ((L : ℝ) * ((L : ℝ) - 1))) * ((SĒ : ℝ) - (SE : ℝ)) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hcount
    push_cast at this
    convert this using 2
  rw [sub_eq_iff_eq_add'] at key
  rw [key]
  have hLne : (L : ℝ) * ((L : ℝ) - 1) ≠ 0 := ne_of_gt hLpos
  field_simp

/-- Linear extension of Lemma 4.4 a) to arbitrary formal combinations of
models supported on sizes `≤ L`. -/
theorem edge_deletion_density_vec (f : FlagVector ∅ₜ) {L : ℕ}
    (h_supp : ∀ M ∈ f.support, M.1 ≤ L) (hL2 : 2 ≤ L)
    (G : LabeledGraph ∅ₜ (Fin L)) (v₁ v₂ : Fin L) (h_adj : G.graph.Adj v₁ v₂)
    : densityEval f ⟨L, ⟦deleteEdge G s(v₁, v₂)⟧⟩
      = densityEval f ⟨L, ⟦G⟧⟩
        + (2 / ((L : ℝ) * ((L : ℝ) - 1)))
            * densityEval (partialEdgeVec f) ⟨L, ⟦edgeRootedAt G v₁ v₂ h_adj⟧⟩
  := by
  have hexp : ∀ (X : FinFlag ∅ₜ), densityEval f X
      = ∑ M ∈ f.support, f M * (flagDensity₁ M.2 X.2 : ℝ) := by
    intro X
    dsimp only [densityEval, linearExtension]
    apply Finset.sum_congr rfl
    intro M _
    rw [smul_eq_mul]
  have hpart : densityEval (partialEdgeVec f) ⟨L, ⟦edgeRootedAt G v₁ v₂ h_adj⟧⟩
      = ∑ M ∈ f.support,
          f M * densityEval (partialEdgeVec (basisVector M)) ⟨L, ⟦edgeRootedAt G v₁ v₂ h_adj⟧⟩ := by
    rw [partialEdgeVec_eq_sum, densityEval_sum]
    apply Finset.sum_congr rfl
    intro M _
    rw [densityEval_smul]
  rw [hexp, hexp, hpart, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro M hM
  rw [edge_deletion_density M (h_supp M hM) hL2 G v₁ v₂ h_adj]
  ring

/-! ## Lemma 4.4 b): `∂_E` respects the zero spaces -/

theorem partialEdgeVec_support_le {f : FlagVector ∅ₜ} {B : ℕ}
    (h : ∀ M ∈ f.support, M.1 ≤ B)
    : ∀ F ∈ (partialEdgeVec f).support, F.1 ≤ B
  := by
  intro F hF
  dsimp only [partialEdgeVec, linearExtension] at hF
  have h1 : F ∈ f.support.biUnion
      (fun M => (f M • (((M.1 : ℝ) * ((M.1 : ℝ) - 1) / 2)
        • (fillVec (muVec nonEdgeType M) - muVec edgeType M))).support) :=
    Finsupp.support_finset_sum hF
  rw [Finset.mem_biUnion] at h1
  obtain ⟨M, hM, hFM⟩ := h1
  have h2 : F ∈ (fillVec (muVec nonEdgeType M) - muVec edgeType M).support :=
    Finsupp.support_smul (Finsupp.support_smul hFM)
  have h3 : F ∈ (fillVec (muVec nonEdgeType M)).support ∪ (muVec edgeType M).support :=
    Finsupp.support_sub h2
  have hsize : F.1 = M.1 := by
    rw [Finset.mem_union] at h3
    rcases h3 with h4 | h4
    · dsimp only [muVec, fillVec] at h4
      rw [linearExtension_sum] at h4
      have h5 := Finsupp.support_finset_sum h4
      rw [Finset.mem_biUnion] at h5
      obtain ⟨G, _, hFG⟩ := h5
      rw [linearExtension_basisVector, basisVector_support, Finset.mem_singleton] at hFG
      rw [hFG]
    · dsimp only [muVec] at h4
      have h5 := Finsupp.support_finset_sum h4
      rw [Finset.mem_biUnion] at h5
      obtain ⟨G, _, hFG⟩ := h5
      rw [basisVector_support, Finset.mem_singleton] at hFG
      rw [hFG]
  rw [hsize]
  exact h M hM

/-- **Razborov, Lemma 4.4 b)**: `∂_E(K⁰) ⊆ K^E`. Consequently `∂_E` defines a
linear mapping from `A⁰` to `A^E` (see `partialEdge`). Proved exactly as
Lemma 4.2 b): evaluate `∂_E k` at an arbitrary large edge-rooted host
`(G, v₁, v₂)` via Lemma 4.4 a). -/
theorem partialEdgeVec_zeroSpace {k : FlagVector ∅ₜ} (hk : k ∈ ZeroSpace ∅ₜ)
    : partialEdgeVec k ∈ ZeroSpace edgeType
  := by
  obtain ⟨L₀, hL₀⟩ := zeroSpace_densityEval_eventually_zero hk
  set B : ℕ := max 2 (max L₀ (k.support.sup (fun M => M.1))) with hB
  have hB2 : 2 ≤ B := le_max_left _ _
  have hBL₀ : L₀ ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have h_supp : ∀ M ∈ k.support, M.1 ≤ B :=
    fun M hM => le_trans (le_trans (Finset.le_sup hM) (le_max_right _ _)) (le_max_right _ _)
  apply mem_zeroSpace_of_densityEval_zero (L := B)
  · exact partialEdgeVec_support_le h_supp
  · intro R
    set G : LabeledGraph ∅ₜ (Fin B) := unlabeledGraph R.out with hG
    set v₁ : Fin B := R.out.type_embed 0 with hv₁
    set v₂ : Fin B := R.out.type_embed 1 with hv₂
    have h_adj : G.graph.Adj v₁ v₂ := edgeFlag_roots_adj R.out
    have hR : (⟦edgeRootedAt G v₁ v₂ h_adj⟧ : FlagWithSize edgeType B) = R := by
      have h1 : edgeRootedAt G v₁ v₂ h_adj = R.out := edgeRootedAt_unlabeledGraph_self R.out
      rw [h1, Quotient.out_eq]
    have hkey := edge_deletion_density_vec k h_supp hB2 G v₁ v₂ h_adj
    rw [hL₀ B hBL₀ ⟦deleteEdge G s(v₁, v₂)⟧, hL₀ B hBL₀ ⟦G⟧] at hkey
    have hB2' : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    have hBpos : (0 : ℝ) < (B : ℝ) * ((B : ℝ) - 1) := by nlinarith
    have hmul : (2 / ((B : ℝ) * ((B : ℝ) - 1)))
        * densityEval (partialEdgeVec k) ⟨B, ⟦edgeRootedAt G v₁ v₂ h_adj⟧⟩ = 0 := by
      linarith [hkey]
    have hpos : (2 / ((B : ℝ) * ((B : ℝ) - 1))) ≠ 0 := by positivity
    have := (mul_eq_zero.mp hmul).resolve_left hpos
    rwa [hR] at this

/-- The edge-deletion operator `∂_E : A⁰ → A^E`, descended to the flag
algebras via Lemma 4.4 b). -/
noncomputable def partialEdge : FlagAlgebra ∅ₜ → FlagAlgebra edgeType :=
  Quotient.lift (fun f : FlagVector ∅ₜ => (⟦partialEdgeVec f⟧ : FlagAlgebra edgeType))
    (by
      intro f g hfg
      apply Quotient.sound
      show partialEdgeVec f ∼v partialEdgeVec g
      dsimp only [flagVectorEqv]
      rw [← partialEdgeVec_sub]
      exact partialEdgeVec_zeroSpace hfg)

theorem partialEdge_quot (f : FlagVector ∅ₜ)
    : partialEdge ⟦f⟧ = ⟦partialEdgeVec f⟧
  := rfl

/-- `∂_E` is additive on the flag algebra. -/
theorem partialEdge_add (f g : FlagAlgebra ∅ₜ)
    : partialEdge (f + g) = partialEdge f + partialEdge g
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← add_quot, partialEdge_quot,
    partialEdge_quot, partialEdge_quot, ← add_quot]
  apply congrArg
  dsimp only [partialEdgeVec]
  rw [linearExtension_add]

/-- `∂_E` commutes with scalars on the flag algebra. -/
theorem partialEdge_smul (r : ℝ) (f : FlagAlgebra ∅ₜ)
    : partialEdge (r • f) = r • partialEdge f
  := by
  rw [← Quotient.out_eq f, ← smul_quot, partialEdge_quot, partialEdge_quot, ← smul_quot]
  apply congrArg
  dsimp only [partialEdgeVec]
  rw [linearExtension_smul]

end Differential
end FlagAlgebras
