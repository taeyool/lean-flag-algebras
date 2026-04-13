import LeanFlagAlgebras.ErdosPentagon.ErdosPentagon
import LeanFlagAlgebras.Forbid.TuranDensityBound

open FlagAlgebras GraphAlgebras SimpleGraph Compute

namespace ErdosPentagon

def K₃ : SimpleGraph (Fin 3) := completeGraph (Fin 3)
def C₅ : SimpleGraph (Fin 5) := {
  Adj i j := match i, j with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => true
    | _, _ => false
}

lemma K₃_toFinFlag_eq
    : K₃.toFinFlag = K3
  := by
  simp [toFinFlag, K₃, K3]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_3_0_0_3, mkEdgeFinset]
  }

lemma C₅_toFinFlag_eq
    : C₅.toFlagAlgebra = C5
  := by
  simp [toFlagAlgebra, C₅, C5, toFinFlag]
  congr 3
  apply Quotient.sound
  refine Nonempty.intro { graph_iso := ?_, type_preserve := List.ofFn_inj.mp rfl }
  exact {
    toFun i := match i with
      | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2
    invFun i := match i with
      | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3
    left_inv i := by fin_cases i <;> simp
    right_inv i := by fin_cases i <;> simp
    map_rel_iff' := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Sym2Graph_5_0_0_19, mkEdgeFinset, Sym2Graph.toLabeledGraph]
  }

end ErdosPentagon
