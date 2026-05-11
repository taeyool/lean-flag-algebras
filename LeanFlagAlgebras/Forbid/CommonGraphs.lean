import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.Forbid.TuranDensity

open FlagAlgebras SimpleGraph Compute

def K3 : SimpleGraph (Fin 3) := completeGraph (Fin 3)

lemma K3_toFinFlag_eq
    : K3.toFinFlag = ⟨3, Flag_3_0_0_3⟩
  := by
  simp [toFinFlag, K3]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_3_0_0_3, mkEdgeFinset]
  }

def K4 : SimpleGraph (Fin 4) := completeGraph (Fin 4)

lemma K4_toFinFlag_eq
    : K4.toFinFlag = ⟨4, Flag_4_0_0_10⟩
  := by
  simp [toFinFlag, K4]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_4_0_0_10, mkEdgeFinset]
  }
