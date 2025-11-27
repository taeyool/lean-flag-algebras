import LeanFlagAlgebras.Compute.Basic
import LeanFlagAlgebras.SubflagListDensity
/-!
# ImportantFunction

TODO : Naming.
-/

namespace Compute

/-- This function computes `labeledSubgraphListCount` if I understood correctly.
    However, the function is slightly different from `labeledSubgraphListCount`. -/
def labeledGraphListCount
    {T U V ι : Type*} [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    {σ : SimpleGraph T} [DecidableRel σ.Adj]
    (l : ι → (LabeledGraph σ U)) [∀ i, DecidableRel (l i).graph.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ :=
  -- A set of every embedding from `σ` to `G`.
  let embeddings : Finset (σ ↪g G) := .univ
  -- For each embedding `e`, add up:
  embeddings.fold (· + ·) 0 fun e ↦
    -- Let `s` be the image of `e`.
    let s := Finset.univ.image e.toFun
    -- From the set containing every function `f` from `ι` to `Finset V`,
    -- choose only those whose image is disjoint from `s`.
    let maps₁ : Finset (ι → Finset V) := Finset.univ.filter fun f ↦ ∀ i, Disjoint (f i) s
    have hmaps₁ : ∀ f ∈ maps₁, ∀ i, Disjoint (f i) s := by grind
    -- Among those, choose only those which `f i` and `f j` are disjoint whenever `i ≠ j`.
    let maps₂ : Finset (ι → Finset V) := maps₁.filter fun f ↦ ∀ {i j}, i ≠ j → Disjoint (f i) (f j)
    have hmaps₂ : ∀ f ∈ maps₂, ∀ i, Disjoint (f i) s := by grind
    -- Among those, choose 
    let maps₃ : Finset (ι → Finset V) := maps₂.filter fun f ↦ ∀ i, ∃ emb : (l i).graph ↪g G,
      (∀ x, emb ((l i).type_embed x) = e x) ∧ Finset.univ.image emb = s ∪ f i
    maps₃.card

end Compute
