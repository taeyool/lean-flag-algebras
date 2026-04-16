import LeanFlagAlgebras.Flags.FlagDef
import LeanFlagAlgebras.Forbid.TuranDensity
import LeanFlagAlgebras.ErdosPentagon.Matrix.PosSemiDef

open FlagAlgebras SimpleGraph Compute

namespace ErdosPentagon

def K3 : SimpleGraph (Fin 3) := completeGraph (Fin 3)
def C5 : SimpleGraph (Fin 5) := {
  Adj i j := match i, j with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => true
    | _, _ => false
}

lemma K3_toFinFlag_eq
    : K3.toFinFlag = ⟨3, Flag_3_0_0_3⟩
  := by
  simp [toFinFlag, K3]
  congr
  all_goals {
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Sym2Graph_3_0_0_3, mkEdgeFinset]
  }

lemma C5_toFlagAlgebra_eq
    : C5.toFlagAlgebra = FlagAlgebra_5_0_0_19
  := by
  simp [toFlagAlgebra, C5, toFinFlag]
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

#print Sym2Graph_5_0_0_19 -- s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 4)

def σ₀ : FlagType (Fin 3) := FlagType_3_0
def σ₁ : FlagType (Fin 3) := FlagType_3_1
def σ₂ : FlagType (Fin 3) := FlagType_3_2

noncomputable def v₀ : FlagAlgebraVec σ₀ 8 := ![
  FlagAlgebra_4_3_0_0, FlagAlgebra_4_3_0_1, FlagAlgebra_4_3_0_2, FlagAlgebra_4_3_0_4, FlagAlgebra_4_3_0_3, FlagAlgebra_4_3_0_5, FlagAlgebra_4_3_0_6, FlagAlgebra_4_3_0_7
]

noncomputable def v₁ : FlagAlgebraVec σ₁ 6 := ![
  FlagAlgebra_4_3_1_0, FlagAlgebra_4_3_1_1, FlagAlgebra_4_3_1_2, FlagAlgebra_4_3_1_3, FlagAlgebra_4_3_1_5, FlagAlgebra_4_3_1_6
]

noncomputable def v₂ : FlagAlgebraVec σ₂ 5 := ![
  FlagAlgebra_4_3_2_0, FlagAlgebra_4_3_2_2, FlagAlgebra_4_3_2_1, FlagAlgebra_4_3_2_3, FlagAlgebra_4_3_2_6
]

end ErdosPentagon
