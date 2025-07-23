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

noncomputable def flagDensitySeq (F : FinFlag σ) (s : FlagSeq σ) : ℕ → ℝ
  :=
  fun n => (flagDensity₁ F.2 (s n).2 : ℝ)

def Increases (s : FlagSeq σ) : Prop
  :=
  StrictMono (fun n => (s n).1)

def ConvergesTo (s : FlagSeq σ) (a : FinFlag σ → ℝ) : Prop
  :=
  Increases s ∧
  ∀ (F : FinFlag σ), Tendsto (flagDensitySeq F s) atTop (𝓝 (a F))

def flagDensitySpace (σ : FlagType (Fin n₀))
  :=
  Set.pi (Set.univ : Set (FinFlag σ)) (fun _ => (Set.Icc 0 1 : Set ℝ))

instance : Countable (FinFlag σ)
  := by
  sorry

theorem flagDensitySpace_compact
    : IsCompact (flagDensitySpace σ)
  := by
  dsimp [flagDensitySpace, Set.pi]
  simp only [Set.mem_univ, forall_true_left]
  apply isCompact_pi_infinite
  intro _
  exact isCompact_Icc

instance : CompactSpace (flagDensitySpace σ)
  :=
  isCompact_iff_compactSpace.mp flagDensitySpace_compact

#check isCompact_pi_infinite
#check @CompactSpace.tendsto_subseq (flagDensitySpace σ) _ _ _

theorem increasing_flagSeq_contain_convergent_subseq
    (s : FlagSeq σ) (hs_inc : Increases s)
    : ∃ (a : FinFlag σ → ℝ) (ϕ : ℕ → ℕ), StrictMono ϕ ∧ ConvergesTo (s ∘ ϕ) a
  := by
  sorry

namespace PositiveHom

noncomputable def coe (φ : PositiveHom σ) : FinFlag σ → ℝ
  :=
  fun F => φ ⟦unitVector F⟧

end PositiveHom

theorem flagSeq_limit_mem_positiveHom
    (s : FlagSeq σ) {a : FinFlag σ → ℝ} (hs_conv : ConvergesTo s a)
    : ∃ (φ : PositiveHom σ), φ.coe = a
  := by
  sorry

theorem positiveHom_as_flagSeq_limit
    (φ : PositiveHom σ)
    : ∃ (s : FlagSeq σ), ConvergesTo s φ.coe
  := by
  sorry
