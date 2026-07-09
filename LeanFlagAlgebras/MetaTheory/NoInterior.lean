import LeanFlagAlgebras.MetaTheory.HeredClass

/-! # Edge-deletion-closed classes (paper §9.4)

The low-level predicate for §9.4 (`thm:no-interior`): a hereditary class that is additionally closed
under deleting edges.  Equivalent (with heredity) to being cut out by forbidding a family of graphs
as *ordinary* (not necessarily induced) subgraphs, and automatic for the usual `H`-subgraph-free
classes.  It is exactly what the edge-thinning argument of `EdgeThinning`/`EdgeThinningLimit` needs:
every spanning subgraph of an in-class graph stays in the class.

The headline `thm:no-interior` (no interior pinning) is proved in
[`NoInteriorThinning`](./NoInteriorThinning.lean), which sits above the thinning construction.
-/

namespace FlagAlgebras.MetaTheory

/-- **Edge-deletion closure.**  Every spanning subgraph of an in-class graph is again in the class. -/
def EdgeDeletionClosed (hc : HeredClass) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {G H : SimpleGraph V},
    H ≤ G → hc.Mem G → hc.Mem H

end FlagAlgebras.MetaTheory
