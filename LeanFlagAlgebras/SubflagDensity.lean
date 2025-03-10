import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic

variable {T : Type} [Fintype T] {σ : FlagType T}

variable {V W : Type}
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

noncomputable def labeledSubgraphCount
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℕ
  :=
  let p (G' : LabeledSubgraph σ G) : Prop := G'.IsInduced ∧ Nonempty (LabeledSubgraph.coe G' ≃f H)
  let S := { G' : LabeledSubgraph σ G | p G' }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card

noncomputable def labeledSubgraphDensity
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℚ
  :=
  let labeledSubgraph_cnt := labeledSubgraphCount H G
  let σ_size := Fintype.card T
  let H_size := Fintype.card V
  let G_size := Fintype.card W
  let num_of_all_induced_subgraph := (G_size - σ_size).choose (H_size - σ_size)
  labeledSubgraph_cnt / num_of_all_induced_subgraph
