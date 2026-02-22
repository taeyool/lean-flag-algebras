import «LeanFlagAlgebras».FlagAlgebra.Compute.Basic

namespace FlagAlgebras.Compute

open SimpleGraph

def isoLabeledSym2GraphSetWithSameGraph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) : Finset (LabeledSym2Graph σ n)
  :=
  { H : LabeledSym2Graph σ n | G.edges = H.edges ∧ G.toLabeledGraph ∼f H.toLabeledGraph }

def isomorphismCount_labeledSym2Graph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) : ℕ
  :=
  (isoLabeledSym2GraphSetWithSameGraph G).card

def downwardNormalizingFactor_labeledSym2Graph
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - k).factorial
  isomorphismCount_labeledSym2Graph G / num_of_all_injections

theorem isomorphismCount_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    isomorphismCount G.toLabeledGraph = isomorphismCount_labeledSym2Graph G
  := by
  dsimp only [isomorphismCount, isomorphismCount_labeledSym2Graph]
  symm
  apply Finset.card_nbij LabeledSym2Graph.toLabeledGraph
  · intro G' hG'
    simp [isoLabeledSym2GraphSetWithSameGraph] at hG'
    obtain ⟨h_edges, h_iso⟩ := hG'
    simp only [isoLabeledGraphSetWithSameGraph, Set.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · simp only [LabeledSym2Graph.toLabeledGraph, h_edges]
    · exact h_iso
  · intro G₁ _ G₂ _ h_eq
    exact LabeledSym2Graph.toLabeledGraph_injective G₁ G₂ h_eq
  · intro G' hG'
    simp only [isoLabeledGraphSetWithSameGraph, Set.coe_toFinset, Set.mem_setOf_eq] at hG'
    obtain ⟨h_graph, h_iso⟩ := hG'
    simp [isoLabeledSym2GraphSetWithSameGraph]
    use G'.toLabeledSym2Graph
    rw [LabeledGraph.toLabeledSym2Graph_toLabeledGraph_eq G']
    simp only [and_true, h_iso]
    simp only [LabeledGraph.toLabeledSym2Graph, Lean.Elab.WF.paramLet, eq_mpr_eq_cast]
    simp [LabeledSym2Graph.toLabeledGraph] at h_graph
    ext e
    simp only [Set.mem_toFinset]
    rw [← h_graph]
    simp
    exact fun h ↦ G.edges_valid e h

theorem downwardNormalizingFactor_labeledGraph_eq
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : LabeledSym2Graph σ n) :
    downwardNormalizingFactor_labeledGraph G.toLabeledGraph = downwardNormalizingFactor_labeledSym2Graph G
  := by
  dsimp only [downwardNormalizingFactor_labeledGraph, downwardNormalizingFactor_labeledSym2Graph]
  congr
  exact isomorphismCount_eq G

theorem downwardNormalizingFactor_labeledSym2Graph_respect_eqv
  {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G G' : LabeledSym2Graph σ n} (h_eqv : G ∼sf G') :
    downwardNormalizingFactor_labeledSym2Graph G = downwardNormalizingFactor_labeledSym2Graph G'
  := by
  rw [← downwardNormalizingFactor_labeledGraph_eq, ← downwardNormalizingFactor_labeledGraph_eq]
  exact downwardNormalizingFactor_labeledGraph_respect_eqv h_eqv

def downwardNormalizingFactor_Sym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} (F : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun (G : LabeledSym2Graph σ n) ↦ downwardNormalizingFactor_labeledSym2Graph G) ?_ F
  intro G G' h_eqv
  exact downwardNormalizingFactor_labeledSym2Graph_respect_eqv h_eqv

theorem downwardNormalizingFactor_eq
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (F : Sym2Flag σ n) :
    downwardNormalizingFactor F.toFlag = downwardNormalizingFactor_Sym2Flag F
  := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  dsimp [downwardNormalizingFactor, downwardNormalizingFactor_Sym2Flag, Sym2Flag.toFlag, LabeledSym2Graph.toFlag]
  exact downwardNormalizingFactor_labeledGraph_eq G

end FlagAlgebras.Compute
