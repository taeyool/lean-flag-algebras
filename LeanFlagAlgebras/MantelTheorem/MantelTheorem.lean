import «LeanFlagAlgebras».FlagAlgebra.RandomHom
import «LeanFlagAlgebras».MantelTheorem.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity

open FlagAlgebras Compute
open SimpleGraph

namespace MantelTheorem

theorem Mantel_theorem
    : K2 ≤ (1 / 2 : ℝ) • 1 + K3
  := by
  have h₁ : K2 ≤ (1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3 := by rw [expand_K2_on_three_vertex_graphs]
  have h₂ : 0 ≤ (1 / 3 : ℝ) • E3 :=
    nonneg_smul_nonneg_geq_zero (by linarith) (flag_geq_zero _)
  have h₃ : 0 ≤ (1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3 := by
    calc
      0 ≤ (1 / 2 : ℝ) • (O3 - (1 / 3 : ℝ) • E3 - (1 / 3 : ℝ) • P3 + K3) := by
          apply nonneg_smul_nonneg_geq_zero (by simp)
          rw [← O2₁_minus_K2₁_square_downward]
          apply square_downward_nonneg
      _ = _ := by
          simp only [smul_add, smul_sub, smul_smul]
          norm_num
  calc
    _ = K2 + 0 + 0 := by simp only [add_zero]
    _ ≤ ((1 / 3 : ℝ) • E3 + (2 / 3 : ℝ) • P3 + K3)
        + (1 / 3 : ℝ) • E3
        + ((1 / 2 : ℝ) • O3 - (1 / 6 : ℝ) • E3 - (1 / 6 : ℝ) • P3 + (1 / 2 : ℝ) • K3) :=
        flag_add_le_add (flag_add_le_add h₁ h₂) h₃
    _ = (1 / 2 : ℝ) • O3
        + ((1 / 3 : ℝ) + (1 / 3 : ℝ) - (1 / 6 : ℝ)) • E3
        + ((2 / 3 : ℝ) - (1 / 6 : ℝ)) • P3
        + (1 / 2 : ℝ) • K3 + K3 := by simp only [add_smul, sub_smul]; ring
    _ = (1 / 2 : ℝ) • O3 + (1 / 2 : ℝ) • E3 + (1 / 2 : ℝ) • P3 + (1 / 2 : ℝ) • K3 + K3 := by norm_num
    _ = (1 / 2 : ℝ) • 1 + K3 := by
        rw [expand_1_on_three_vertex_graphs]
        norm_num

theorem Mantel_theorem'
    : ∀ (φ : PositiveHom ∅ₜ), φ K3 = 0 → φ K2 ≤ 1 / 2
  := by
  intro φ h
  simpa [φ.map_add, φ.map_sub, φ.map_smul, φ.map_one, h] using Mantel_theorem φ

example : Sym2Graph_3_0_0_3.toLabeledGraph.graph = completeGraph (Fin 3) := by
  ext v w
  simp [Sym2Graph.toLabeledGraph]
  fin_cases v <;> fin_cases w <;> decide

def SimpleGraph.blow_up
    {V : Type} (G : SimpleGraph V) (n : ℕ)
    : SimpleGraph (Fin n × V) where
  Adj x y := G.Adj x.2 y.2
  symm := by
    intro x y hxy
    exact hxy.symm
  loopless := by
    intro x hxx
    exact G.loopless x.2 hxx

theorem Turan_density_K3
    : turanDensity (completeGraph (Fin 3)) = 1 / 2
  := by
  dsimp [turanDensity]
  sorry

end MantelTheorem
