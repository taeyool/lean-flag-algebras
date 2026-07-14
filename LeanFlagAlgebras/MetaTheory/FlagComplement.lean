import LeanFlagAlgebras.MetaTheory.LabeledCount
import LeanFlagAlgebras.FlagAlgebra.FlagOperators

/-! # Graph complement on flags and complement-invariance of flag densities

Infrastructure for `lem:complementation` of `MetaTheory/paper.tex`: *root-plantability is
invariant under complementation*.  The semantic heart of that statement is the fact that
labelled flag densities are unchanged when every graph in sight is replaced by its complement
and the type `σ` by `σᶜ`.

This file builds the complementation functor on the flag tower and proves its key density
identities.

* **Complement infrastructure.** `complEmbedding` / `graphIsoCompl` complement a graph
  embedding / isomorphism; `LabeledGraph.compl`, `LabeledGraphIso.compl`, `Flag.compl`,
  `FinFlag.compl` lift this through the labelled-graph and flag quotients.  `Flag.compl` is an
  involution (`Flag.compl_compl`, modulo the propositional `σᶜᶜ = σ`).
* **Commutation.** Taking an induced labelled subgraph commutes with complementing
  (`inducedLabeledSubgraph_coe_compl_graph`), so the subset-count filter sets of a flag and of
  its complement coincide.
* **The headline identities.**  `flagDensity₁_compl` and `flagDensity₂_compl`: complementing
  both arguments (and the type) leaves single- and pair-flag densities unchanged.  The auxiliary
  `unlabel_compl` and `downwardNormalizingFactor_compl` carry complementation through the
  unlabelling layer used by `downward`.

The single most important result is `flagDensity₁_compl`; everything else supports the eventual
flag-algebra-level complementation isomorphism. -/

open Classical

namespace FlagAlgebras

variable {T : Type} [Fintype T] {σ : FlagType T}

/-! ## Complementing graph embeddings and isomorphisms -/

/-- An induced embedding `f : H ↪g G` complements to an induced embedding `Hᶜ ↪g Gᶜ`: same
underlying (injective) map, with adjacency negated on both sides. -/
def complEmbedding {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W} (f : H ↪g G) :
    Hᶜ ↪g Gᶜ where
  toFun := f
  inj' := f.injective
  map_rel_iff' := by
    intro a b
    show Gᶜ.Adj (f a) (f b) ↔ Hᶜ.Adj a b
    simp only [SimpleGraph.compl_adj]
    rw [f.injective.ne_iff, f.map_rel_iff]

/-- A graph isomorphism `φ : G ≃g H` complements to `Gᶜ ≃g Hᶜ`: same underlying equivalence,
with adjacency negated on both sides. -/
def graphIsoCompl {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    Gᶜ ≃g Hᶜ where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    show Hᶜ.Adj (φ a) (φ b) ↔ Gᶜ.Adj a b
    simp only [SimpleGraph.compl_adj]
    rw [φ.injective.ne_iff, φ.map_rel_iff]

@[simp]
theorem graphIsoCompl_apply {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (v : V) : graphIsoCompl φ v = φ v := rfl

/-! ## Complementing labelled graphs, isomorphisms, and flags -/

/-- The complement of a labelled graph: complement the underlying graph and the type. -/
def LabeledGraph.compl {V : Type} (G : LabeledGraph σ V) : LabeledGraph σᶜ V where
  graph := G.graphᶜ
  type_embed := complEmbedding G.type_embed

omit [Fintype T] in
@[simp]
theorem LabeledGraph.compl_graph {V : Type} (G : LabeledGraph σ V) :
    G.compl.graph = G.graphᶜ := rfl

omit [Fintype T] in
@[simp]
theorem LabeledGraph.compl_type_embed_apply {V : Type} (G : LabeledGraph σ V) (t : T) :
    G.compl.type_embed t = G.type_embed t := rfl

omit [Fintype T] in
@[simp]
theorem LabeledGraph.compl_type_verts {V : Type} (G : LabeledGraph σ V) :
    G.compl.type_verts = G.type_verts := rfl

/-- A labelled-graph isomorphism `φ : G ≃f G'` complements to `G.compl ≃f G'.compl`: the
underlying maps are unchanged, only adjacency is negated. -/
def LabeledGraphIso.compl {V W : Type} {G : LabeledGraph σ V} {G' : LabeledGraph σ W}
    (φ : G ≃f G') : G.compl ≃f G'.compl where
  graph_iso := graphIsoCompl φ.graph_iso
  type_preserve := by
    have h := φ.type_preserve
    funext t
    show graphIsoCompl φ.graph_iso (G.type_embed t) = G'.type_embed t
    rw [graphIsoCompl_apply]
    exact congrFun h t

omit [Fintype T] in
/-- Complementation respects labelled-graph isomorphism, hence descends to flags. -/
theorem flagEqv_compl {V : Type} {G G' : LabeledGraph σ V} (h : G ∼f G') :
    G.compl ∼f G'.compl :=
  ⟨LabeledGraphIso.compl h.some⟩

/-- The complement of a flag: lift `LabeledGraph.compl` through the flag quotient. -/
noncomputable def Flag.compl {V : Type} : Flag σ V → Flag σᶜ V :=
  Quotient.lift (fun G : LabeledGraph σ V => (⟦G.compl⟧ : Flag σᶜ V))
    fun _ _ h => Quotient.sound (flagEqv_compl h)

omit [Fintype T] in
@[simp]
theorem Flag.compl_mk {V : Type} (G : LabeledGraph σ V) :
    Flag.compl (⟦G⟧ : Flag σ V) = (⟦G.compl⟧ : Flag σᶜ V) := rfl

omit [Fintype T] in
/-- A general HEq for graph embeddings: equal source types and target graphs together with equal
underlying functions give heterogeneously equal embeddings. -/
theorem graphEmbedding_heq_of {V : Type} {σ₁ σ₂ : FlagType T} (hσ : σ₁ = σ₂)
    {g₁ g₂ : SimpleGraph V} (hg : g₁ = g₂) {e₁ : σ₁ ↪g g₁} {e₂ : σ₂ ↪g g₂}
    (he : ∀ t : T, (e₁ t : V) = e₂ t) : HEq e₁ e₂ := by
  subst hσ hg
  apply heq_of_eq
  apply RelEmbedding.ext
  intro t
  exact he t

omit [Fintype T] in
/-- The doubly-complemented graph embedding is heterogeneously equal to the original (its
underlying map is unchanged), modulo `σᶜᶜ = σ` and `gᶜᶜ = g`. -/
theorem complEmbedding_complEmbedding_heq {V : Type} {g : SimpleGraph V} (e : σ ↪g g) :
    HEq (complEmbedding (complEmbedding e)) e :=
  graphEmbedding_heq_of (_root_.compl_compl σ) (_root_.compl_compl g) (fun _ => rfl)

omit [Fintype T] in
/-- A heterogeneous congruence for labelled graphs: equal types, equal graphs, and
heterogeneously equal embeddings give heterogeneously equal labelled graphs. -/
theorem LabeledGraph.heq_of {V : Type} {σ₁ σ₂ : FlagType T} (hσ : σ₁ = σ₂)
    {g₁ g₂ : SimpleGraph V} (hg : g₁ = g₂) {e₁ : σ₁ ↪g g₁} {e₂ : σ₂ ↪g g₂}
    (he : HEq e₁ e₂) :
    HEq (⟨g₁, e₁⟩ : LabeledGraph σ₁ V) (⟨g₂, e₂⟩ : LabeledGraph σ₂ V) := by
  subst hσ hg
  rw [eq_of_heq he]

omit [Fintype T] in
/-- `LabeledGraph.compl` is a (heterogeneous) involution: `G.compl.compl = G` modulo the
propositional `σᶜᶜ = σ` and `Gᶜᶜ = G`. -/
theorem LabeledGraph.compl_compl {V : Type} (G : LabeledGraph σ V) :
    HEq (LabeledGraph.compl (LabeledGraph.compl G)) G :=
  LabeledGraph.heq_of (_root_.compl_compl σ) (_root_.compl_compl G.graph)
    (complEmbedding_complEmbedding_heq G.type_embed)

/-- The complement of a sized flag, as a sized flag of complementary type. -/
noncomputable def FinFlag.compl {n₀ : ℕ} {σ : FlagType (Fin n₀)} (F : FinFlag σ) :
    FinFlag σᶜ :=
  ⟨F.1, F.2.compl⟩

omit [Fintype T] in
/-- Two labelled graphs are isomorphic if and only if their complements are: complementation of
the underlying graph isomorphism is an involution (via `compl_compl`).  This is the workhorse
that transports isomorphism witnesses across complementation in both directions. -/
theorem nonempty_flagEqv_compl_iff {V W : Type} (G : LabeledGraph σ V) (G' : LabeledGraph σ W) :
    Nonempty (G ≃f G') ↔ Nonempty (G.compl ≃f G'.compl) := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨LabeledGraphIso.compl φ⟩
  · rintro ⟨φ⟩
    -- `φ.graph_iso : G.graphᶜ ≃g G'.graphᶜ` shares its underlying equiv `V ≃ W` with the desired
    -- `G.graph ≃g G'.graph`; only the relation-preservation clause differs, recovered via `compl_adj`.
    let ψ : G.graph ≃g G'.graph :=
      { toEquiv := φ.graph_iso.toEquiv
        map_rel_iff' := by
          intro a b
          show G'.graph.Adj (φ.graph_iso a) (φ.graph_iso b) ↔ G.graph.Adj a b
          -- Decide adjacency in `G`/`G'` by complementing the `Gᶜ`/`G'ᶜ` characterization.
          by_cases hab : a = b
          · subst hab
            simp only [SimpleGraph.irrefl]
          · have key : G'.graphᶜ.Adj (φ.graph_iso a) (φ.graph_iso b) ↔ G.graphᶜ.Adj a b :=
              φ.graph_iso.map_rel_iff (a := a) (b := b)
            rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at key
            have hne' : φ.graph_iso a ≠ φ.graph_iso b := by
              simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact hab
            constructor
            · intro hadj
              by_contra hcon
              have := key.mpr ⟨hab, hcon⟩
              exact this.2 hadj
            · intro hadj
              by_contra hcon
              have := key.mp ⟨hne', hcon⟩
              exact this.2 hadj }
    refine ⟨{ graph_iso := ψ, type_preserve := ?_ }⟩
    funext t
    show ψ (G.type_embed t) = G'.type_embed t
    show φ.graph_iso (G.compl.type_embed t) = G'.compl.type_embed t
    exact congrFun φ.type_preserve t

/-- The reverse of `complEmbedding`, keeping `σ` honest: an embedding `e : σᶜ ↪g g` yields an
embedding `σ ↪g gᶜ` with the same underlying map (no `σᶜᶜ` clutter). -/
def uncomplEmbedding {V : Type} {g : SimpleGraph V} (e : σᶜ ↪g g) : σ ↪g gᶜ where
  toFun := e
  inj' := e.injective
  map_rel_iff' := by
    intro a b
    show gᶜ.Adj (e a) (e b) ↔ σ.Adj a b
    by_cases hab : a = b
    · subst hab; simp only [SimpleGraph.irrefl]
    · have key : g.Adj (e a) (e b) ↔ σᶜ.Adj a b := e.map_rel_iff (a := a) (b := b)
      rw [SimpleGraph.compl_adj] at key
      rw [SimpleGraph.compl_adj]
      have hne' : e a ≠ e b := by simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact hab
      constructor
      · rintro ⟨_, hcon⟩
        by_contra hadj
        exact hcon (key.mpr ⟨hab, hadj⟩)
      · intro hadj
        refine ⟨hne', ?_⟩
        intro hgadj
        exact (key.mp hgadj).2 hadj

/-- The reverse complement of a labelled graph of type `σᶜ`, landing honestly in type `σ`:
`graph := G.graphᶜ`, with the σ-embedding repackaged via `uncomplEmbedding`. -/
def LabeledGraph.uncompl {V : Type} (G : LabeledGraph σᶜ V) : LabeledGraph σ V where
  graph := G.graphᶜ
  type_embed := uncomplEmbedding G.type_embed

omit [Fintype T] in
@[simp]
theorem LabeledGraph.uncompl_graph {V : Type} (G : LabeledGraph σᶜ V) :
    G.uncompl.graph = G.graphᶜ := rfl

omit [Fintype T] in
/-- `compl` then `uncompl` is the identity on `LabeledGraph σ V`. -/
theorem LabeledGraph.uncompl_compl {V : Type} (G : LabeledGraph σ V) :
    G.compl.uncompl = G := by
  apply LabeledGraph.ext
  · show G.graphᶜᶜ = G.graph
    exact _root_.compl_compl G.graph
  · apply HEq.symm
    apply graphEmbedding_heq_of rfl (_root_.compl_compl G.graph).symm
    intro t; rfl

omit [Fintype T] in
/-- `uncompl` then `compl` is the identity on `LabeledGraph σᶜ V`. -/
theorem LabeledGraph.compl_uncompl {V : Type} (G : LabeledGraph σᶜ V) :
    G.uncompl.compl = G := by
  apply LabeledGraph.ext
  · show G.graphᶜᶜ = G.graph
    exact _root_.compl_compl G.graph
  · apply HEq.symm
    apply graphEmbedding_heq_of rfl (_root_.compl_compl G.graph).symm
    intro t; rfl

namespace MetaTheory

variable {V : Type}

/-! ## Complement commutes with taking induced subgraphs -/

omit [Fintype T] in
/-- Complementing commutes with cutting out an induced labelled subgraph: the underlying graph of
the induced subgraph of `Gᶜ` on `S` is the complement of the underlying graph of the induced
subgraph of `G` on `S` (both live on the subtype `↑S`). -/
theorem inducedLabeledSubgraph_coe_compl_graph (G : LabeledGraph σ V)
    (S : Set V) (h : G.type_verts ⊆ S) (h' : G.compl.type_verts ⊆ S) :
    (LabeledSubgraph.inducedLabeledSubgraph G.compl S h').coe.graph
      = ((LabeledSubgraph.inducedLabeledSubgraph G S h).coe.graph)ᶜ := by
  ext u v
  rw [SimpleGraph.compl_adj]
  rw [LabeledSubgraph.coe_adj_iff, LabeledSubgraph.coe_adj_iff]
  show (LabeledSubgraph.inducedLabeledSubgraph G.compl S h').subgraph.Adj u.val v.val
    ↔ u ≠ v ∧ ¬ (LabeledSubgraph.inducedLabeledSubgraph G S h).subgraph.Adj u.val v.val
  simp only [LabeledSubgraph.inducedLabeledSubgraph, SimpleGraph.Subgraph.induce, LabeledGraph.compl_graph]
  constructor
  · rintro ⟨_, _, hne, hadj⟩
    refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
    rintro ⟨_, _, h2⟩
    exact hadj h2
  · rintro ⟨hne, hadj⟩
    have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
    refine ⟨u.property, v.property, hne', ?_⟩
    intro hadjG
    exact hadj ⟨u.property, v.property, hadjG⟩

omit [Fintype T] in
/-- The complement-of-induced-subgraph iso transfer: an induced copy of `H` in `G` on `S`
corresponds to an induced copy of `Hᶜ` in `Gᶜ` on the same `S`. -/
theorem nonempty_inducedLabeledSubgraph_iso_compl {U : Type}
    (G : LabeledGraph σ V) (H : LabeledGraph σ U)
    (S : Set V) (h : G.type_verts ⊆ S) (h' : G.compl.type_verts ⊆ S) :
    Nonempty ((LabeledSubgraph.inducedLabeledSubgraph G S h).coe ≃f H)
      ↔ Nonempty ((LabeledSubgraph.inducedLabeledSubgraph G.compl S h').coe ≃f H.compl) := by
  have hgeq := inducedLabeledSubgraph_coe_compl_graph G S h h'
  -- A labelled-graph iso `(induced Gᶜ S).coe ≃f (induced G S).coe.compl`, from the graph equality.
  -- Both sides live on `↑S`; their graphs agree (`hgeq`) and their type embeddings have the same
  -- underlying map, so the identity-on-`↑S` map (transported across `hgeq`) is an iso.
  have key : (LabeledSubgraph.inducedLabeledSubgraph G.compl S h').coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph G S h).coe.compl :=
    { graph_iso :=
        { toEquiv := Equiv.refl _
          map_rel_iff' := by
            intro a b
            show ((LabeledSubgraph.inducedLabeledSubgraph G S h).coe.compl.graph).Adj a b
              ↔ ((LabeledSubgraph.inducedLabeledSubgraph G.compl S h').coe.graph).Adj a b
            rw [LabeledGraph.compl_graph, hgeq] }
      type_preserve := by
        funext t
        apply Subtype.ext
        rfl }
  rw [nonempty_flagEqv_compl_iff]
  constructor
  · rintro ⟨φ⟩
    exact ⟨key.trans φ⟩
  · rintro ⟨φ⟩
    exact ⟨key.symm.trans φ⟩

/-- `σᶜ` has the same size as `σ` (the carrier `T` is unchanged). -/
theorem flagType_compl_size : (σᶜ).size = σ.size := rfl

omit [Fintype T] in
/-- Complementing leaves the number of vertices unchanged (same vertex carrier). -/
theorem labeledGraph_compl_size [Fintype V] [DecidableEq V] (G : LabeledGraph σ V) :
    G.compl.size = G.size := rfl

omit [Fintype T] in
/-- The subset-count filter sets for a flag and for its complement coincide as `Finset`s: the
*same* subset `S` qualifies for `(H, G)` and for `(Hᶜ, Gᶜ)`, since induce/compl commute and the
isomorphism witnesses transfer (`nonempty_inducedLabeledSubgraph_iso_compl`). -/
theorem subset_count_filter_compl {U : Type} [Fintype V] [DecidableEq V]
    (G : LabeledGraph σ V) (H : LabeledGraph σ U) :
    (Finset.univ.filter (fun S : Finset V =>
        ∃ (h : G.type_verts ⊆ (↑S : Set V)),
          Nonempty ((LabeledSubgraph.inducedLabeledSubgraph G (↑S) h).coe ≃f H)))
      = (Finset.univ.filter (fun S : Finset V =>
        ∃ (h : G.compl.type_verts ⊆ (↑S : Set V)),
          Nonempty ((LabeledSubgraph.inducedLabeledSubgraph G.compl (↑S) h).coe ≃f H.compl))) := by
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨h, hiso⟩
    have h' : G.compl.type_verts ⊆ (↑S : Set V) := h
    exact ⟨h', (nonempty_inducedLabeledSubgraph_iso_compl G H (↑S) h h').mp hiso⟩
  · rintro ⟨h', hiso⟩
    have h : G.type_verts ⊆ (↑S : Set V) := h'
    exact ⟨h, (nonempty_inducedLabeledSubgraph_iso_compl G H (↑S) h h').mpr hiso⟩

/-! ## The headline density identity -/

/-- **Single-flag density is complement-invariant.**  Complementing both arguments (and the type
`σ`) leaves the labelled single-flag density unchanged.  This is the density-level content of
`lem:complementation`.

The binomial denominators agree (complementing changes neither vertex counts nor `σ.size`), and the
numerator filter sets are literally equal (`subset_count_filter_compl`): the same vertex subset `S`
witnesses a copy of `H` in `G` and of `Hᶜ` in `Gᶜ`. -/
theorem flagDensity₁_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (F : Flag σ U) (G : Flag σ W) :
    flagDensity₁ F.compl G.compl = flagDensity₁ F G := by
  rcases Quotient.exists_rep F with ⟨Frep, rfl⟩
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  rw [Flag.compl_mk, Flag.compl_mk]
  rw [flagDensity₁_eq_subset_count_div, flagDensity₁_eq_subset_count_div]
  -- Denominators are definitionally equal; the numerator filter sets are literally equal.
  rw [subset_count_filter_compl Grep Frep]
  rfl

/-! ## Pair-flag density is complement-invariant -/

omit [Fintype T] in
/-- The complement-induced subgraph of a list member: replace `Gl i` by the induced subgraph of
`G.compl` on the same vertex set.  When `Gl` is induced, this is the componentwise complement. -/
private def complSubgraphList {n₀ : ℕ} {σ : FlagType (Fin n₀)} {t : ℕ}
    {G : LabeledGraph σ V} (Gl : LabeledSubgraphList σ t G) :
    LabeledSubgraphList σᶜ t G.compl :=
  fun i => LabeledSubgraph.inducedLabeledSubgraph G.compl (Gl i).subgraph.verts
    (by
      have := LabeledSubgraph.labeledSubgraph_contain_type_verts G (Gl i)
      exact this)

omit [Fintype T] in
/-- `complSubgraphList` preserves the verts of each member. -/
private theorem complSubgraphList_verts {n₀ : ℕ} {σ : FlagType (Fin n₀)} {t : ℕ}
    {G : LabeledGraph σ V} (Gl : LabeledSubgraphList σ t G) (i : Fin t) :
    (complSubgraphList Gl i).subgraph.verts = (Gl i).subgraph.verts := by
  simp only [complSubgraphList, LabeledSubgraph.inducedLabeledSubgraph_verts]

omit [Fintype T] in
/-- The induced labelled subgraph depends only on its vertex set, not on the containment proof. -/
private theorem inducedLabeledSubgraph_verts_congr {G : LabeledGraph σ V}
    {S₁ S₂ : Set V} (hS : S₁ = S₂)
    (h₁ : G.type_verts ⊆ S₁) (h₂ : G.type_verts ⊆ S₂) :
    LabeledSubgraph.inducedLabeledSubgraph G S₁ h₁ = LabeledSubgraph.inducedLabeledSubgraph G S₂ h₂ := by
  subst hS; rfl

/-- **List-count is complement-invariant.**  Complementing the host, the type, and each flag in the
list leaves the number of realizing induced subgraph lists unchanged: the componentwise
complement-induced map (`complSubgraphList`, restricted to induced subgraph lists) is a bijection
of the realizing sets, preserving `IsInduced`, disjointness (same vertex sets), and the per-member
isomorphism conditions (`nonempty_inducedLabeledSubgraph_iso_compl`). -/
theorem labeledGraphListCount_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)} {t : ℕ}
    {Vl : Fin t → Type} [Fintype V] [DecidableEq V]
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V) :
    labeledGraphListCount (fun i => (Hl i).compl) G.compl = labeledGraphListCount Hl G := by
  classical
  dsimp only [labeledGraphListCount]
  rw [Set.toFinset_card, Set.toFinset_card]
  -- It suffices to give an equivalence of the two realizing sets; `complSubgraphList` provides it.
  -- The forward map: complement each (induced) member, keeping its vertex set.
  have e : setOfLabeledSubgraphListIsoHl G Hl
      ≃ setOfLabeledSubgraphListIsoHl G.compl (fun i => (Hl i).compl) := Equiv.ofBijective
    (fun (Gl : setOfLabeledSubgraphListIsoHl G Hl) =>
      (⟨complSubgraphList Gl.1, ?_⟩ : setOfLabeledSubgraphListIsoHl G.compl (fun i => (Hl i).compl)))
    ⟨?_, ?_⟩
  · exact (@Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _) e).symm
  · -- `complSubgraphList Gl.1` lies in the complement realizing set.
    obtain ⟨Gl, hind, hiso, hdisj⟩ := Gl
    refine ⟨fun i => LabeledSubgraph.inducedLabeledSubgraph_isInduced _ _ _, ?_, ?_⟩
    · intro i
      have hHi := hiso i
      have heq : Gl i = LabeledSubgraph.inducedLabeledSubgraph G (Gl i).subgraph.verts
          (LabeledSubgraph.labeledSubgraph_contain_type_verts G (Gl i)) :=
        LabeledSubgraph.inducedLabeledSubgraph_eq (hind i)
      rw [heq] at hHi
      exact (nonempty_inducedLabeledSubgraph_iso_compl G (Hl i)
        (Gl i).subgraph.verts (LabeledSubgraph.labeledSubgraph_contain_type_verts G (Gl i))
        (LabeledSubgraph.labeledSubgraph_contain_type_verts G (Gl i))).mp hHi
    · intro i j hij
      rw [complSubgraphList_verts, complSubgraphList_verts]
      exact hdisj i j hij
  · -- injective
    rintro ⟨Gl₁, h₁⟩ ⟨Gl₂, h₂⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    funext i
    have hv : (Gl₁ i).subgraph.verts = (Gl₂ i).subgraph.verts := by
      have := congrFun heq i
      rw [← complSubgraphList_verts Gl₁ i, ← complSubgraphList_verts Gl₂ i, this]
    rw [LabeledSubgraph.inducedLabeledSubgraph_eq (h₁.1 i),
      LabeledSubgraph.inducedLabeledSubgraph_eq (h₂.1 i)]
    exact inducedLabeledSubgraph_verts_congr hv _ _
  · -- surjective
    rintro ⟨Gl', hind', hiso', hdisj'⟩
    refine ⟨⟨fun i => LabeledSubgraph.inducedLabeledSubgraph G (Gl' i).subgraph.verts
      (LabeledSubgraph.labeledSubgraph_contain_type_verts G.compl (Gl' i)), ?_, ?_, ?_⟩, ?_⟩
    · intro i
      exact LabeledSubgraph.inducedLabeledSubgraph_isInduced _ _ _
    · intro i
      have hHi := hiso' i
      have heq : Gl' i = LabeledSubgraph.inducedLabeledSubgraph G.compl (Gl' i).subgraph.verts
          (LabeledSubgraph.labeledSubgraph_contain_type_verts G.compl (Gl' i)) :=
        LabeledSubgraph.inducedLabeledSubgraph_eq (hind' i)
      rw [heq] at hHi
      exact (nonempty_inducedLabeledSubgraph_iso_compl G (Hl i)
        (Gl' i).subgraph.verts
        (LabeledSubgraph.labeledSubgraph_contain_type_verts G.compl (Gl' i))
        (LabeledSubgraph.labeledSubgraph_contain_type_verts G.compl (Gl' i))).mpr hHi
    · intro i j hij
      rw [LabeledSubgraph.inducedLabeledSubgraph_verts, LabeledSubgraph.inducedLabeledSubgraph_verts]
      exact hdisj' i j hij
    · -- the complement of this preimage is `Gl'`
      simp only [Subtype.mk.injEq]
      funext i
      rw [LabeledSubgraph.inducedLabeledSubgraph_eq (hind' i)]
      apply inducedLabeledSubgraph_verts_congr
      rw [LabeledSubgraph.inducedLabeledSubgraph_verts]

/-- **List-density is complement-invariant.**  Complementing the host, the type, and every flag in
the list leaves the list density unchanged: the counts agree (`labeledGraphListCount_compl`) and the
normalizing multinomial coefficients agree (complementing changes no vertex count nor `σ.size`). -/
theorem labeledGraphListDensity_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)} {t : ℕ}
    {Vl : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl] [Fintype V] [DecidableEq V]
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ V) :
    labeledGraphListDensity (fun i => (Hl i).compl) G.compl = labeledGraphListDensity Hl G := by
  dsimp only [labeledGraphListDensity]
  rw [labeledGraphListCount_compl]
  rfl

/-- **Pair-flag density is complement-invariant.**  Complementing both flags, the host, and the
type leaves the joint two-flag density unchanged — the pair analogue of `flagDensity₁_compl`,
obtained from `labeledGraphListDensity_compl` for the two-element list `[F₁, F₂]`. -/
theorem flagDensity₂_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {U₁ U₂ W : Type} [Fintype U₁] [Fintype U₂] [Fintype W]
    [DecidableEq U₁] [DecidableEq U₂] [DecidableEq W]
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W) :
    flagDensity₂ F₁.compl F₂.compl G.compl = flagDensity₂ F₁ F₂ G := by
  rcases Quotient.exists_rep F₁ with ⟨F₁rep, rfl⟩
  rcases Quotient.exists_rep F₂ with ⟨F₂rep, rfl⟩
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  rw [Flag.compl_mk, Flag.compl_mk, Flag.compl_mk]
  rw [← labeledGraphListDensity_eq_flagDensity₂, ← labeledGraphListDensity_eq_flagDensity₂]
  -- Both sides are `labeledGraphListDensity` of the two-element list; apply the list-density fact.
  -- The complemented list `[F₁.compl, F₂.compl]ᵍ` equals `fun i => ([F₁,F₂]ᵍ i).compl`.
  have hlist : ([F₁rep.compl, F₂rep.compl]ᵍ : LabeledGraphList σᶜ 2 _)
      = (fun i => ([F₁rep, F₂rep]ᵍ i).compl) := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
  rw [hlist]
  exact labeledGraphListDensity_compl [F₁rep, F₂rep]ᵍ Grep

/-! ## Carrying complementation through the unlabelling layer -/

/-- The empty type is its own complement: `Fin 0` has no vertices, so `∅ₜᶜ = ∅ₜ`. -/
theorem emptyType_compl : (∅ₜ : FlagType (Fin 0))ᶜ = ∅ₜ := by
  ext u v
  exact Fin.elim0 u

omit [Fintype T] in
/-- Transporting a flag's quotient class along a type equality `h : τ = τ'` is the quotient of the
transported labelled graph. -/
theorem flag_eqRec_mk {τ τ' : FlagType T} (h : τ = τ') (G : LabeledGraph τ V) :
    (h ▸ (⟦G⟧ : Flag τ V) : Flag τ' V) = ⟦h ▸ G⟧ := by
  subst h; rfl

omit [Fintype T] in
/-- Transporting a labelled graph along a type-index equality leaves its underlying graph
unchanged. -/
theorem labeledGraph_eqRec_graph {τ τ' : FlagType T} (h : τ = τ') (G : LabeledGraph τ V) :
    (h ▸ G : LabeledGraph τ' V).graph = G.graph := by
  subst h; rfl

/-- **Unlabelling commutes with complementing.**  Forgetting the `σ`-labelling and then
complementing the (now unlabelled) flag gives the same underlying graph as complementing first and
then unlabelling — the only difference is the type index `∅ₜᶜ` vs `∅ₜ`, bridged by
`emptyType_compl`. -/
theorem unlabel_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)} {V : Type} (F : Flag σ V) :
    unlabel F.compl = emptyType_compl ▸ (unlabel F).compl := by
  rcases Quotient.exists_rep F with ⟨Grep, rfl⟩
  -- Both sides are `⟦·⟧` of a `∅ₜ`-labelled graph on the same underlying graph `Grep.graphᶜ`.
  rw [Flag.compl_mk]
  show unlabel (⟦Grep.compl⟧ : Flag σᶜ V) = emptyType_compl ▸ (Flag.compl (unlabel ⟦Grep⟧))
  -- Reduce `unlabel ⟦·⟧` to `⟦unlabeledGraph ·⟧`.
  show (⟦unlabeledGraph Grep.compl⟧ : Flag ∅ₜ V)
    = emptyType_compl ▸ (Flag.compl (⟦unlabeledGraph Grep⟧ : Flag ∅ₜ V))
  rw [Flag.compl_mk, flag_eqRec_mk]
  -- Both sides are `⟦·⟧` of a `∅ₜ`-labelled graph on the same underlying graph `Grep.graphᶜ`.
  apply Quotient.sound
  -- `unlabeledGraph Grep.compl ∼f emptyType_compl ▸ (unlabeledGraph Grep).compl` (same graph).
  refine ⟨{ graph_iso := ?_, type_preserve := by funext z; exact Fin.elim0 z }⟩
  -- The two underlying graphs are equal (`Grep.graphᶜ`); the transport does not change it.
  show (unlabeledGraph Grep.compl).graph ≃g (emptyType_compl ▸ (unlabeledGraph Grep).compl).graph
  have hg : (unlabeledGraph Grep.compl).graph
      = (emptyType_compl ▸ (unlabeledGraph Grep).compl).graph := by
    rw [labeledGraph_eqRec_graph]; rfl
  rw [hg]

/-! ## The unlabelling weight is complement-invariant -/

/-- **The number of label placements is complement-invariant.**  `isomorphismCount G.compl =
isomorphismCount G`: complement is an involution on labelled graphs (`compl`/`uncompl`) preserving
both the same-underlying-graph condition and flag-isomorphism, so it bijects the two iso-sets. -/
theorem isomorphismCount_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)} {n : ℕ}
    (G : LabeledGraph σ (Fin n)) :
    isomorphismCount G.compl = isomorphismCount G := by
  classical
  dsimp only [isomorphismCount]
  rw [Set.toFinset_card, Set.toFinset_card]
  -- Bijection `K ↦ K.compl`, inverse `H ↦ H.uncompl`, between the two iso-sets.
  refine (@Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _) ?_)
  refine Equiv.symm
    { toFun := fun K => ⟨K.1.compl, ?_⟩
      invFun := fun H => ⟨H.1.uncompl, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- `K.compl` lies in `isoLabeledGraphSetWithSameGraph G.compl`.
    obtain ⟨K, hgr, hiso⟩ := K
    refine ⟨?_, flagEqv_compl hiso⟩
    show G.compl.graph = K.compl.graph
    rw [LabeledGraph.compl_graph, LabeledGraph.compl_graph]
    exact congrArg (·ᶜ) hgr
  · -- `H.uncompl` lies in `isoLabeledGraphSetWithSameGraph G`.
    obtain ⟨H, hgr, hiso⟩ := H
    refine ⟨?_, ?_⟩
    · show G.graph = H.uncompl.graph
      rw [LabeledGraph.uncompl_graph]
      -- `G.graph = H.graphᶜ` from `G.compl.graph = H.graph`, i.e. `G.graphᶜ = H.graph`.
      have hgr' : G.graphᶜ = H.graph := hgr
      rw [← hgr', _root_.compl_compl]
    · -- `G ∼f H.uncompl` from `G.compl ∼f H`.
      refine (nonempty_flagEqv_compl_iff G H.uncompl).mpr ?_
      -- `G.compl ∼f H.uncompl.compl`; and `H.uncompl.compl = H`.
      rw [LabeledGraph.compl_uncompl]
      exact hiso
  · rintro ⟨K, hK⟩
    simp only [Subtype.mk.injEq]
    exact LabeledGraph.uncompl_compl K
  · rintro ⟨H, hH⟩
    simp only [Subtype.mk.injEq]
    exact LabeledGraph.compl_uncompl H

/-- **The unlabelling weight is complement-invariant.**  `downwardNormalizingFactor F.compl =
downwardNormalizingFactor F`: the descending-factorial normaliser `n!/(n - n₀)!` is unchanged
(complementing alters neither `n` nor `σ.size = n₀`), and the placement count
`isomorphismCount` is complement-invariant (`isomorphismCount_compl`). -/
theorem downwardNormalizingFactor_compl {n₀ : ℕ} {σ : FlagType (Fin n₀)} {n : ℕ}
    (F : Flag σ (Fin n)) :
    downwardNormalizingFactor F.compl = downwardNormalizingFactor F := by
  rcases Quotient.exists_rep F with ⟨Grep, rfl⟩
  rw [Flag.compl_mk]
  show downwardNormalizingFactor_labeledGraph Grep.compl = downwardNormalizingFactor_labeledGraph Grep
  dsimp only [downwardNormalizingFactor_labeledGraph]
  rw [isomorphismCount_compl]

end MetaTheory

end FlagAlgebras
