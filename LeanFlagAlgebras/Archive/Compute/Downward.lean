import «LeanFlagAlgebras».Archive.Compute.Basic

/-!
# (Archived) Computable downward (unlabeling) normalizing factor

ARCHIVED / SUPERSEDED — this file is **not** part of the build (its import is
commented out in `LeanFlagAlgebras.lean`). It is an early computable account of
the downward / unlabeling normalizing factor for the `Sym2`-encoded flags from
`Archive/Compute/Basic.lean`, with lemmas certifying it agrees with the
abstract `downwardNormalizingFactor`. The active version lives in
`LeanFlagAlgebras/FlagAlgebra/Compute/Downward.lean`.
-/

namespace Archive.Compute

open FlagAlgebras
open SimpleGraph

def isoSym2LabeledGraphSetWithSameGraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G : Sym2LabeledGraph σ n) : Finset (Sym2LabeledGraph σ n)
  :=
  { H : Sym2LabeledGraph σ n | G.edges = H.edges ∧ G.toLabeledGraph ∼f H.toLabeledGraph }

def isomorphismCount_sym2LabeledGraph
    {T : Type} {σ : FlagType T} [Fintype T] [DecidableEq T] [DecidableRel σ.Adj] {n : ℕ}
    (G : Sym2LabeledGraph σ n) : ℕ
  :=
  (isoSym2LabeledGraphSetWithSameGraph G).card

def downwardNormalizingFactor_sym2LabeledGraph
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (G : Sym2LabeledGraph σ n) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - n₀).factorial
  isomorphismCount_sym2LabeledGraph G / num_of_all_injections

theorem isomorphismCount_eq
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
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
    simp [isoSym2LabeledGraphSetWithSameGraph]
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

theorem downwardNormalizingFactor_labeledGraph_eq
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (G : Sym2LabeledGraph σ n) :
    downwardNormalizingFactor_labeledGraph G.toLabeledGraph = downwardNormalizingFactor_sym2LabeledGraph G
  := by
  dsimp only [downwardNormalizingFactor_labeledGraph, downwardNormalizingFactor_sym2LabeledGraph]
  congr
  exact isomorphismCount_eq G

theorem downwardNormalizingFactor_sym2LabeledGraph_respect_eqv
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    {G G' : Sym2LabeledGraph σ n} (h_eqv : G ∼sf G') :
    downwardNormalizingFactor_sym2LabeledGraph G = downwardNormalizingFactor_sym2LabeledGraph G'
  := by
  rw [← downwardNormalizingFactor_labeledGraph_eq, ← downwardNormalizingFactor_labeledGraph_eq]
  exact downwardNormalizingFactor_labeledGraph_respect_eqv h_eqv

def downwardNormalizingFactor_Sym2Flag
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ} (F : Sym2Flag σ n) : ℚ
  := by
  refine Quotient.lift (fun (G : Sym2LabeledGraph σ n) ↦ downwardNormalizingFactor_sym2LabeledGraph G) ?_ F
  intro G G' h_eqv
  exact downwardNormalizingFactor_sym2LabeledGraph_respect_eqv h_eqv

theorem downwardNormalizingFactor_eq
    {n₀ : ℕ} {σ : FlagType (Fin n₀)} [DecidableRel σ.Adj] {n : ℕ}
    (F : Sym2Flag σ n) :
    downwardNormalizingFactor F.toFlag = downwardNormalizingFactor_Sym2Flag F
  := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  dsimp [downwardNormalizingFactor, downwardNormalizingFactor_Sym2Flag, Sym2Flag.toFlag, Sym2LabeledGraph.toFlag]
  exact downwardNormalizingFactor_labeledGraph_eq G

end Archive.Compute
