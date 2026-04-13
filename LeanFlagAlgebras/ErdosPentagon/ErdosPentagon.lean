import LeanFlagAlgebras.ErdosPentagon.Lemmas

open FlagAlgebras Forbid Filter Topology

namespace ErdosPentagon

theorem ErdosPentagon_Turan_upperBound
    : generalizedTuranDensity K3 C5 ≤ 24 / 625
  :=
  generalizedTuranDensity_le_of_forbidLE (by norm_num) ErdosPentagon_flagAlgebra

theorem generalizedExtremalNumber_K3_C5_ge
    (n : ℕ)
    : generalizedExtremalNumber (5 * n) K3 C5 ≥ n ^ 5
  := by
  suffices hWit : ∃ G : SimpleGraph (Fin (5 * n)), K3.Free G ∧ n ^ 5 ≤ GraphAlgebras.subgraphCount C5 G by
    rcases hWit with ⟨G, hGfree, hGcount⟩
    refine le_trans hGcount (Finset.le_sup ?_)
    simpa [Finset.mem_filter] using hGfree

  sorry

theorem generalizedExtremalNumber_K3_C5_div_choose_ge
    (n : ℕ) (hn : 0 < n)
    : (generalizedExtremalNumber (5 * n) K3 C5 / (5 * n).choose 5 : ℝ) ≥ 24 / 625
  := by
  have hchoose_pos : (0 : ℝ) < (5 * n).choose 5 :=
    Nat.cast_pos'.mpr (Nat.choose_pos (by nlinarith [hn]))
  calc
    generalizedExtremalNumber (5 * n) K3 C5 / (5 * n).choose 5
        ≥ (n : ℝ) ^ 5 / (5 * n).choose 5 := by
      field_simp
      exact_mod_cast (generalizedExtremalNumber_K3_C5_ge n)
    _ ≥ (n : ℝ) ^ 5 / (((5 * n) ^ 5) / Nat.factorial 5 : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hchoose_pos
      apply le_trans (Nat.choose_le_pow_div (α := ℝ) 5 (5 * n))
      simp only [Nat.cast_mul, Nat.cast_ofNat, le_refl]
    _ = (24 / 625 : ℝ) := by
      field_simp
      norm_num

theorem ErdosPentagon_Turan_lowerBound
    : generalizedTuranDensity K3 C5 ≥ 24 / 625
  := by
  let f : ℕ → ℝ := fun n ↦ (generalizedExtremalNumber n K3 C5 / n.choose 5 : ℝ)
  let g : ℕ → ℝ := fun n ↦ f (5 * (n + 1))
  have hf : Tendsto f atTop (𝓝 (generalizedTuranDensity K3 C5)) := by
    simpa [f] using (tendsto_generalizedTuranDensity K3 C5)
  have hmul_mono : StrictMono (fun n : ℕ ↦ 5 * (n + 1)) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hab 1) (by decide : 0 < 5)
  have hg : Tendsto g atTop (𝓝 (generalizedTuranDensity K3 C5)) :=
    hf.comp (StrictMono.tendsto_atTop hmul_mono)
  refine le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (24 / 625 : ℝ)) atTop (𝓝 (24 / 625 : ℝ)))
    hg ?_
  intro n
  simpa [g, f, ge_iff_le] using
    (generalizedExtremalNumber_K3_C5_div_choose_ge (n + 1) (Nat.succ_pos n))

theorem ErdosPentagon_Turan
    : generalizedTuranDensity K3 C5 = 24 / 625
  := by
  apply le_antisymm
  · exact ErdosPentagon_Turan_upperBound
  · exact ErdosPentagon_Turan_lowerBound

end ErdosPentagon
