import LeanFlagAlgebras.Forbid.CommonGraphs
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import Mathlib.Tactic

open FlagAlgebras FlagAlgebras.Compute

/-! Prototype: H-free completeness for n=4, K3-forbidden (empty-typed), in the
exact form the forbid-mul bridge consumes:
`flagSetHfree = univ.filter (fun F' => flagDensity₁ K3.toFinFlag.2 (unlabel F') = 0)`. -/

/-- Computable forbid-free test via the ℚ-valued `Sym2` density (K3 = `Sym2Flag_3_0_0_3`). -/
def isK3free4 (S : Sym2EmptyTypedFlag 4) : Bool :=
  decide (sym2EmptyTypeFlagDensity₁ Sym2Flag_3_0_0_3 S = 0)

def sym2FlagSetHfree_4 : Finset (Sym2EmptyTypedFlag 4) :=
  ([Sym2Flag_4_0_0_0, Sym2Flag_4_0_0_1, Sym2Flag_4_0_0_2, Sym2Flag_4_0_0_3,
    Sym2Flag_4_0_0_4, Sym2Flag_4_0_0_6, Sym2Flag_4_0_0_8]).toFinset

theorem hfree_list_eq :
    (genEmptyTypedFlags 4).filter (fun S => isK3free4 S)
      = [Sym2Flag_4_0_0_0, Sym2Flag_4_0_0_1, Sym2Flag_4_0_0_2, Sym2Flag_4_0_0_3,
         Sym2Flag_4_0_0_4, Sym2Flag_4_0_0_6, Sym2Flag_4_0_0_8] := by
  native_decide

theorem sym2FlagSetHfree_4_eq :
    sym2FlagSetHfree_4 = Finset.univ.filter (fun S => isK3free4 S = true) := by
  rw [← genEmptyTypedFlagSet_eq_univ 4]
  show _ = ((genEmptyTypedFlags 4).toFinset).filter (fun S => isK3free4 S = true)
  rw [← List.toFinset_filter]
  rw [hfree_list_eq]
  rfl

/-- FlagWithSize-level forbid-free set: the image under `toFlag` of the `Sym2` set. -/
noncomputable def flagSetHfree_4 : Finset (FlagWithSize ∅ₜ 4) :=
  sym2FlagSetHfree_4.map ⟨Sym2EmptyTypedFlag.toFlag,
    fun a b h => Sym2EmptyTypedFlag.toFlag_injective a b h⟩

/-- The deliverable completeness lemma, in the bridge's exact predicate form. -/
theorem flagSetHfree_4_eq :
    flagSetHfree_4
      = Finset.univ.filter (fun F' => flagDensity₁ K3.toFinFlag.2 (unlabel F') = 0) := by
  rw [flagSetHfree_4, sym2FlagSetHfree_4_eq]
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨S, hS, rfl⟩
    rw [unlabel_emptyType, K3_toFinFlag_eq]
    show flagDensity₁ (Sym2Flag_3_0_0_3).toFlag S.toFlag = 0
    rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]
    exact of_decide_eq_true hS
  · intro hx
    refine ⟨x.toSym2EmptyTypedFlag, ?_, x.toSym2EmptyTypedFlag_toFlag_eq⟩
    rw [unlabel_emptyType, K3_toFinFlag_eq] at hx
    show isK3free4 _ = true
    rw [isK3free4, decide_eq_true_eq]
    rw [← flagDensity₁_eq_sym2EmptyTypeFlagDensity₁, x.toSym2EmptyTypedFlag_toFlag_eq]
    exact hx
