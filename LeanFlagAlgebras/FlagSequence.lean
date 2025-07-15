import «LeanFlagAlgebras».PositiveHom
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Sequences

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open Filter
open scoped Topology

abbrev FlagSeq (σ : FlagType (Fin n₀))
  :=
  ℕ → FinFlag σ

def Increases (s : FlagSeq σ) : Prop
  :=
  StrictMono (fun n => (s n).1)

def ConvergesTo (s : FlagSeq σ) (a : FinFlag σ → ℝ) : Prop
  :=
  Increases s ∧
  ∀ (F : FinFlag σ), Tendsto (fun n => (flagDensity₁ F.2 (s n).2 : ℝ)) atTop (𝓝 (a F))

#check CompactSpace.tendsto_subseq

theorem increasing_seq_contain_convergent_subseq
    (s : FlagSeq σ) (hs_inc : Increases s)
    : ∃ (a : FinFlag σ → ℝ) (ϕ : ℕ → ℕ), StrictMono ϕ ∧ ConvergesTo (s ∘ ϕ) a
  := by
  sorry

namespace PositiveHom

noncomputable def coe (φ : PositiveHom σ) : FinFlag σ → ℝ
  :=
  fun F => φ ⟦unitVector F⟧

end PositiveHom
