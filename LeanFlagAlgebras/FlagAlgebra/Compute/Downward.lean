import «LeanFlagAlgebras».FlagAlgebra.Compute.FastIso

/-! # Computable downward / averaging coefficients

Computable counterpart of the abstract downward (unlabeling/averaging) machinery, used by the
loader macros. It defines effective isomorphism counts on `Sym2LabeledGraph`s and the
`downwardNormalizingFactor` for `Sym2LabeledGraph`/`Sym2Flag`, then proves these agree with the
abstract `isomorphismCount` / `downwardNormalizingFactor` under the `toLabeledGraph` / `toFlag`
decoding, so data computed in the `Sym2` representation is provably correct.
-/

namespace FlagAlgebras.Compute

open SimpleGraph

/-- The flag-equivalent relabelings of `G` that keep the same underlying edge set; their count
gives the computable isomorphism count. -/
def isoSym2LabeledGraphSetWithSameGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Finset (Sym2LabeledGraph σ n)
  :=
  { H : Sym2LabeledGraph σ n | G.edges = H.edges ∧ G ∼sf H }

/-- The type embeddings into `G`'s graph that make it flag-equivalent to `G`; equinumerous
with `isoSym2LabeledGraphSetWithSameGraph G`. -/
def isoSym2TypeEmbeddingSetWithSameGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n)
    : Finset ((fromEdgeSet (SetLike.coe σ.edges)) ↪g (fromEdgeSet (SetLike.coe G.edges)))
  :=
  { θ | let H : Sym2LabeledGraph σ n := {
          edges := G.edges,
          edges_valid := G.edges_valid,
          type_embed := θ
        };
        G ∼sf H }

/-- Computable isomorphism count of `G` (number of same-graph flag-equivalent relabelings). -/
def isomorphismCount_sym2LabeledGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : ℕ
  :=
  (isoSym2LabeledGraphSetWithSameGraph G).card

/-- Computable count of type embeddings making `G` flag-equivalent to itself. -/
def isoEmbeddingCount_sym2LabeledGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : ℕ
  :=
  (isoSym2TypeEmbeddingSetWithSameGraph G).card

/-- The two computable counts agree (relabelings ↔ type embeddings). -/
theorem isomorphismCount_sym2LabeledGraph_eq_isoEmbeddingCount_sym2LabeledGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    isomorphismCount_sym2LabeledGraph G = isoEmbeddingCount_sym2LabeledGraph G
  := by
  dsimp only [isomorphismCount_sym2LabeledGraph, isoEmbeddingCount_sym2LabeledGraph]
  apply Finset.card_bij (fun H hH => cast (by
    have h_mem : G.edges = H.edges ∧ G ∼sf H := by
      simpa [isoSym2LabeledGraphSetWithSameGraph] using hH
    have h_edges : G.edges = H.edges := h_mem.1
    rw [h_edges]) H.type_embed)
  · intro H hH
    have h_mem : G.edges = H.edges ∧ G ∼sf H := by
      simpa [isoSym2LabeledGraphSetWithSameGraph] using hH
    have h_edges : G.edges = H.edges := h_mem.1
    have h_iso : G ∼sf H := h_mem.2
    rcases H with ⟨edges, edges_valid, type_embed⟩
    dsimp at h_edges h_iso ⊢
    subst h_edges
    simpa [isoSym2TypeEmbeddingSetWithSameGraph] using h_iso
  · intro H1 hH1 H2 hH2 hEq
    have h_mem1 : G.edges = H1.edges ∧ G ∼sf H1 := by
      simpa [isoSym2LabeledGraphSetWithSameGraph] using hH1
    have h_mem2 : G.edges = H2.edges ∧ G ∼sf H2 := by
      simpa [isoSym2LabeledGraphSetWithSameGraph] using hH2
    have h1 : G.edges = H1.edges := h_mem1.1
    have h2 : G.edges = H2.edges := h_mem2.1
    rcases H1 with ⟨edges1, edges_valid1, type_embed1⟩
    rcases H2 with ⟨edges2, edges_valid2, type_embed2⟩
    dsimp at h1 h2 hEq ⊢
    subst h1 h2
    simp at hEq
    ext e
    · rfl
    · simpa using hEq
  · intro θ hθ
    refine ⟨⟨G.edges, G.edges_valid, θ⟩, ?_, rfl⟩
    simpa [isoSym2LabeledGraphSetWithSameGraph, isoSym2TypeEmbeddingSetWithSameGraph] using hθ

/-- Computable downward normalizing factor of `G`: its isomorphism-embedding count divided by
the number of all injections `Fin k ↪ Fin n` (`n! / (n-k)!`). -/
def downwardNormalizingFactor_sym2LabeledGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - k).factorial
  isoEmbeddingCount_sym2LabeledGraph G / num_of_all_injections

/-- The computable count matches the abstract `isomorphismCount` of the decoded graph. -/
theorem isomorphismCount_eq_isomorphismCount_sym2LabeledGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    isomorphismCount G.toLabeledGraph = isomorphismCount_sym2LabeledGraph G
  := by
  dsimp only [isomorphismCount, isomorphismCount_sym2LabeledGraph]
  symm
  apply Finset.card_nbij Sym2LabeledGraph.toLabeledGraph
  · intro G' hG'
    simp [isoSym2LabeledGraphSetWithSameGraph] at hG'
    obtain ⟨h_edges, h_iso⟩ := hG'
    simp only [isoLabeledGraphSetWithSameGraph, Set.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · simp only [Sym2LabeledGraph.toLabeledGraph, h_edges]
    · exact h_iso
  · intro G₁ _ G₂ _ h_eq
    exact Sym2LabeledGraph.toLabeledGraph_injective G₁ G₂ h_eq
  · intro G' hG'
    simp only [isoLabeledGraphSetWithSameGraph, Set.coe_toFinset, Set.mem_setOf_eq] at hG'
    obtain ⟨h_graph, h_iso⟩ := hG'
    simp [isoSym2LabeledGraphSetWithSameGraph, sym2LabeledGraphEqv]
    use G'.toSym2LabeledGraph
    rw [LabeledGraph.toSym2LabeledGraph_toLabeledGraph_eq G']
    simp only [and_true, h_iso]
    simp only [LabeledGraph.toSym2LabeledGraph, Lean.Elab.WF.paramLet, eq_mpr_eq_cast]
    simp [Sym2LabeledGraph.toLabeledGraph] at h_graph
    ext e
    simp only [Set.mem_toFinset]
    rw [← h_graph]
    simp
    exact fun h ↦ G.edges_valid e h

theorem isomorphismCount_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    isomorphismCount G.toLabeledGraph = isoEmbeddingCount_sym2LabeledGraph G
  := by
  rw [isomorphismCount_eq_isomorphismCount_sym2LabeledGraph, isomorphismCount_sym2LabeledGraph_eq_isoEmbeddingCount_sym2LabeledGraph]

/-- The computable normalizing factor matches the abstract one on the decoded labeled graph. -/
theorem downwardNormalizingFactor_labeledGraph_eq
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    downwardNormalizingFactor_labeledGraph G.toLabeledGraph = downwardNormalizingFactor_sym2LabeledGraph G
  := by
  dsimp only [downwardNormalizingFactor_labeledGraph, downwardNormalizingFactor_sym2LabeledGraph]
  congr
  exact isomorphismCount_eq G

theorem downwardNormalizingFactor_sym2LabeledGraph_respect_eqv
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G G' : Sym2LabeledGraph σ n} (h_eqv : G ∼sf G') :
    downwardNormalizingFactor_sym2LabeledGraph G = downwardNormalizingFactor_sym2LabeledGraph G'
  := by
  rw [← downwardNormalizingFactor_labeledGraph_eq, ← downwardNormalizingFactor_labeledGraph_eq]
  exact downwardNormalizingFactor_labeledGraph_respect_eqv h_eqv

/-- Computable downward normalizing factor of a `Sym2Flag`, lifted from representatives since
the factor respects flag-equivalence. -/
def downwardNormalizingFactor_Sym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (F : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun (G : Sym2LabeledGraph σ n) ↦ downwardNormalizingFactor_sym2LabeledGraph G) ?_ F
  intro G G' h_eqv
  exact downwardNormalizingFactor_sym2LabeledGraph_respect_eqv h_eqv

/-- The computable `Sym2Flag` factor matches the abstract `downwardNormalizingFactor` on the
decoded flag; this is the correctness guarantee the loader relies on. -/
theorem downwardNormalizingFactor_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (F : Sym2Flag σ n) :
    downwardNormalizingFactor F.toFlag = downwardNormalizingFactor_Sym2Flag F
  := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  dsimp [downwardNormalizingFactor, downwardNormalizingFactor_Sym2Flag, Sym2Flag.toFlag, Sym2LabeledGraph.toFlag]
  exact downwardNormalizingFactor_labeledGraph_eq G

end FlagAlgebras.Compute
