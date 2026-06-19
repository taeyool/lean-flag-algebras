import LeanFlagAlgebras.Flags.FlagGenerator
import LeanFlagAlgebras.Forbid.TuranDensity
import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.ErdosPentagon.MatrixDef

/-! # Erdős pentagon problem: flags and certificate vectors

Sets up the combinatorial data for the Erdős pentagon problem (maximum density
of the 5-cycle in triangle-free graphs). Defines the pentagon graph `C5`, the
three labelled types `σ₀`/`σ₁`/`σ₂` (the 3-vertex types `K3_*`) used for the
sum-of-squares certificate, and the flag-algebra vectors `v₀`/`v₁`/`v₂` of
4-vertex flags that are paired with the PSD matrices `P`/`Q`/`R` from
`MatrixDef.lean`. -/

open FlagAlgebras SimpleGraph Compute

namespace ErdosPentagonAPI

-- Locally generate the flags this development uses (formerly from the global
-- `Flags/FlagDef.lean`): empty-typed underlying flags (n = 3 for the forbidden `K3`,
-- n = 4/5 for the pattern/host and the pentagon `C5`), the forbidden graph `K3`, and the
-- σ-typed (3-labelled) pattern/host flags. These `ErdosPentagonAPI.*` constants are
-- shared by `FlagMul` / `Lemmas` / `ErdosPentagon` (which all import this file).
generate_empty_typed_flags 3
generate_empty_typed_flags 4
generate_empty_typed_flags 5
generate_complete_graph 3 3
generate_flags 4 3 0
generate_flags 4 3 1
generate_flags 4 3 2
generate_flags 5 3 0
generate_flags 5 3 1
generate_flags 5 3 2

/-- The 5-cycle `C₅` on `Fin 5` (edges `01,12,23,34,40`); the target subgraph
whose triangle-free density is being maximised. -/
def C5 : SimpleGraph (Fin 5) := {
  Adj i j := match i, j with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => true
    | _, _ => false
}

/-- Identifies the pentagon's flag-algebra element with the generated 5-vertex
basis element `FlagAlgebra_5_0_0_19`. -/
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

/-- First 3-vertex labelled type used by the SOS certificate. -/
def σ₀ : FlagType (Fin 3) := FlagType_3_0
/-- Second 3-vertex labelled type used by the SOS certificate. -/
def σ₁ : FlagType (Fin 3) := FlagType_3_1
/-- Third 3-vertex labelled type used by the SOS certificate. -/
def σ₂ : FlagType (Fin 3) := FlagType_3_2

/-- Vector of eight 4-vertex flags over type `σ₀`, paired with the PSD matrix
`P` to form one square term of the certificate. -/
noncomputable def v₀ : FlagAlgebraVec σ₀ 8 := ![
  FlagAlgebra_4_3_0_0, FlagAlgebra_4_3_0_1, FlagAlgebra_4_3_0_2, FlagAlgebra_4_3_0_4, FlagAlgebra_4_3_0_3, FlagAlgebra_4_3_0_5, FlagAlgebra_4_3_0_6, FlagAlgebra_4_3_0_7
]

/-- Vector of six 4-vertex flags over type `σ₁`, paired with the PSD matrix
`Q` to form one square term of the certificate. -/
noncomputable def v₁ : FlagAlgebraVec σ₁ 6 := ![
  FlagAlgebra_4_3_1_0, FlagAlgebra_4_3_1_1, FlagAlgebra_4_3_1_2, FlagAlgebra_4_3_1_3, FlagAlgebra_4_3_1_5, FlagAlgebra_4_3_1_6
]

/-- Vector of five 4-vertex flags over type `σ₂`, paired with the PSD matrix
`R` to form one square term of the certificate. -/
noncomputable def v₂ : FlagAlgebraVec σ₂ 5 := ![
  FlagAlgebra_4_3_2_0, FlagAlgebra_4_3_2_2, FlagAlgebra_4_3_2_1, FlagAlgebra_4_3_2_3, FlagAlgebra_4_3_2_6
]

end ErdosPentagonAPI
