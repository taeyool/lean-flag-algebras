import «LeanFlagAlgebras».MantelTheorem.FlagDefs
import Mathlib.Tactic.FinCases


open FlagAlgebras
open Compute

namespace MantelTheorem

def emptyTypeOneVertexSym2FlagSet : Finset (Sym2Flag ∅ₜ 1) where
  val := [K1_Sym2Flag]
  nodup := by native_decide

theorem emptyTypeOneVertexSym2FlagSet_eq_univ : emptyTypeOneVertexSym2FlagSet = Finset.univ
  := by
  native_decide

def emptyTypeOneVertexFlagSet : Finset (FlagWithSize ∅ₜ 1) :=
  Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } emptyTypeOneVertexSym2FlagSet

theorem emptyTypeOneVertexFlagSet_val_eq :
    emptyTypeOneVertexFlagSet.val = [K1_flag]
  := by
  simp [emptyTypeOneVertexFlagSet, emptyTypeOneVertexSym2FlagSet]
  rw [K1_eq]

theorem emptyTypeOneVertexFlagSet_eq_univ : emptyTypeOneVertexFlagSet = Finset.univ
  := by
  dsimp only [emptyTypeOneVertexFlagSet]
  rw [emptyTypeOneVertexSym2FlagSet_eq_univ]
  ext F
  simp
  exact ⟨F.toSym2Flag, Flag.toSym2Flag_toFlag_eq F⟩


def emptyTypeThreeVertexSym2FlagSet : Finset (Sym2Flag ∅ₜ 3) where
  val := [O3_Sym2Flag, E3_Sym2Flag, P3_Sym2Flag, K3_Sym2Flag]
  nodup := by native_decide

theorem emptyTypeThreeVertexSym2FlagSet_eq_univ : emptyTypeThreeVertexSym2FlagSet = Finset.univ
  := by
  native_decide

def emptyTypeThreeVertexFlagSet : Finset (FlagWithSize ∅ₜ 3) :=
  Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } emptyTypeThreeVertexSym2FlagSet

theorem emptyTypeThreeVertexFlagSet_val_eq :
    emptyTypeThreeVertexFlagSet.val = [O3_flag, E3_flag, P3_flag, K3_flag]
  := by
  simp [emptyTypeThreeVertexFlagSet, emptyTypeThreeVertexSym2FlagSet]
  rw [O3_eq, E3_eq, P3_eq, K3_eq]

theorem emptyTypeThreeVertexFlagSet_eq_univ : emptyTypeThreeVertexFlagSet = Finset.univ
  := by
  dsimp only [emptyTypeThreeVertexFlagSet]
  rw [emptyTypeThreeVertexSym2FlagSet_eq_univ]
  ext F
  simp
  exact ⟨F.toSym2Flag, Flag.toSym2Flag_toFlag_eq F⟩

/- labeledGraphs with singleton type -/

def singletonTypeThreeVertexSym2FlagSet : Finset (Sym2Flag Sₜ 3) where
  val := [O3₁_Sym2Flag, E3₁_Sym2Flag, E3₁'_Sym2Flag, P3₁_Sym2Flag, P3₁'_Sym2Flag, K3₁_Sym2Flag]
  nodup := by native_decide

theorem singletonTypeThreeVertexSym2FlagSet_eq_univ : singletonTypeThreeVertexSym2FlagSet = Finset.univ
  := by
  native_decide

def singletonTypeThreeVertexFlagSet : Finset (FlagWithSize Sₜ 3) :=
  Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective } singletonTypeThreeVertexSym2FlagSet

theorem singletonTypeThreeVertexFlagSet_val_eq :
    singletonTypeThreeVertexFlagSet.val =
      [O3₁_flag, E3₁_flag, E3₁'_flag, P3₁_flag, P3₁'_flag, K3₁_flag]
  := by
  simp [singletonTypeThreeVertexFlagSet, singletonTypeThreeVertexSym2FlagSet]
  rw [O3₁_eq, E3₁_eq, E3₁'_eq, P3₁_eq, P3₁'_eq, K3₁_eq]

theorem singletonTypeThreeVertexFlagSet_eq_univ : singletonTypeThreeVertexFlagSet = Finset.univ
  := by
  dsimp only [singletonTypeThreeVertexFlagSet]
  rw [singletonTypeThreeVertexSym2FlagSet_eq_univ]
  ext F
  simp
  exact ⟨F.toSym2Flag, Flag.toSym2Flag_toFlag_eq F⟩

end MantelTheorem
