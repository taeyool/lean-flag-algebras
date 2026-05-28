import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.Forbid.TuranDensity

/-! # Common forbidden graphs

Concrete `SimpleGraph (Fin n)` definitions for graphs frequently used as forbidden or
target subgraphs (e.g. the complete graphs `K3`, `K4`), together with lemmas computing
their `toFinFlag` representations as explicit empty-type flags.
-/

open FlagAlgebras SimpleGraph Compute

/-- The complete graph on 3 vertices, `K₃` (a triangle). -/
def K3 : SimpleGraph (Fin 3) := completeGraph (Fin 3)

/-- `K3.toFinFlag` equals the explicit empty-type flag `⟨3, Flag_3_0_0_3⟩`. -/
lemma K3_toFinFlag_eq
    : K3.toFinFlag = ⟨3, Flag_3_0_0_3⟩
  := by
  simp [toFinFlag, K3]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_3_0_0_3, mkEdgeFinset]
  }

/-- The complete graph on 4 vertices, `K₄`. -/
def K4 : SimpleGraph (Fin 4) := completeGraph (Fin 4)

/-- `K4.toFinFlag` equals the explicit empty-type flag `⟨4, Flag_4_0_0_10⟩`. -/
lemma K4_toFinFlag_eq
    : K4.toFinFlag = ⟨4, Flag_4_0_0_10⟩
  := by
  simp [toFinFlag, K4]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_4_0_0_10, mkEdgeFinset]
  }

set_option maxHeartbeats 0

/-- The complete graph on 4 vertices, `K₅`. -/
def K5 : SimpleGraph (Fin 5) := completeGraph (Fin 5)

/-- `K5.toFinFlag` equals the explicit empty-type flag `⟨5, Flag_5_0_0_33⟩`. -/
lemma K5_toFinFlag_eq
    : K5.toFinFlag = ⟨5, Flag_5_0_0_33⟩
  := by
  simp [toFinFlag, K5]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_5_0_0_33, mkEdgeFinset]
  }
