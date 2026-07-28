import «LeanFlagAlgebras».FlagAlgebra.FlagOperators

/-! # Density evaluation of flag vectors (Razborov §4.3 preliminaries)

This file provides the *density evaluation* `p^G(f)` of a formal flag vector
`f ∈ ℝF^σ` at a host flag `G` — the linear extension of `F ↦ p(F, G)` — and the
resulting membership criterion for the zero space `K^σ`:

* `densityEval_zeroElement` : every generating relation of `ZeroSpace σ`
  evaluates to `0` on all hosts of size at least the relation's expansion size
  (this is the chain rule);
* `zeroSpace_densityEval_eventually_zero` : hence every element of
  `ZeroSpace σ` evaluates to `0` on all sufficiently large hosts;
* `mem_zeroSpace_of_densityEval_zero` : conversely, a vector supported on sizes
  `≤ L` whose evaluations vanish at every size-`L` host lies in `ZeroSpace σ`.

Together these give the standard tool (used by Razborov to prove his
Lemma 4.2 b) and Lemma 4.4 b)) for showing that a linear operator defined on
models descends to the flag algebra: it suffices to control the operator's
density evaluations at large hosts. -/

namespace FlagAlgebras
namespace Differential

open Finset

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- Razborov's `p^G(f)`: the density evaluation of a formal flag vector `f` at
the host flag `G`, i.e. the linear extension of `F ↦ p(F, G)` applied to `f`. -/
noncomputable def densityEval (f : FlagVector σ) (G : FinFlag σ) : ℝ :=
  linearExtension (fun F : FinFlag σ => (flagDensity₁ F.2 G.2 : ℝ)) f

@[simp]
theorem densityEval_basisVector (F G : FinFlag σ)
    : densityEval (basisVector F) G = (flagDensity₁ F.2 G.2 : ℝ)
  := by
  dsimp only [densityEval]
  rw [linearExtension_basisVector]

@[simp]
theorem densityEval_zero (G : FinFlag σ)
    : densityEval (0 : FlagVector σ) G = 0
  := by
  dsimp only [densityEval]
  rw [linearExtension_zero]

theorem densityEval_add (f f' : FlagVector σ) (G : FinFlag σ)
    : densityEval (f + f') G = densityEval f G + densityEval f' G
  := by
  dsimp only [densityEval]
  rw [linearExtension_add]

theorem densityEval_neg (f : FlagVector σ) (G : FinFlag σ)
    : densityEval (-f) G = -densityEval f G
  := by
  dsimp only [densityEval]
  rw [linearExtension_neg]

theorem densityEval_sub (f f' : FlagVector σ) (G : FinFlag σ)
    : densityEval (f - f') G = densityEval f G - densityEval f' G
  := by
  dsimp only [densityEval]
  rw [linearExtension_sub]

theorem densityEval_smul (r : ℝ) (f : FlagVector σ) (G : FinFlag σ)
    : densityEval (r • f) G = r * densityEval f G
  := by
  dsimp only [densityEval]
  rw [linearExtension_smul]
  rfl

theorem densityEval_sum {ι : Type*} (s : Finset ι) (c : ι → FlagVector σ) (G : FinFlag σ)
    : densityEval (∑ i ∈ s, c i) G = ∑ i ∈ s, densityEval (c i) G
  := by
  dsimp only [densityEval]
  rw [linearExtension_sum]

/-- Density evaluations are bounded in absolute value by the ℓ¹-norm of the
coefficient vector (each single-flag density lies in `[0, 1]`). -/
theorem abs_densityEval_le (f : FlagVector σ) (G : FinFlag σ)
    : |densityEval f G| ≤ ∑ F ∈ f.support, |f F|
  := by
  dsimp only [densityEval, linearExtension]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro F _
  rw [smul_eq_mul, abs_mul]
  have h₀ : (0 : ℚ) ≤ flagDensity₁ F.2 G.2 := flagListDensity_ge_zero _ _
  have h₁ : flagDensity₁ F.2 G.2 ≤ 1 := flagListDensity_le_one _ _
  have : |(flagDensity₁ F.2 G.2 : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · calc (-1 : ℝ) ≤ 0 := by norm_num
        _ ≤ (flagDensity₁ F.2 G.2 : ℝ) := by exact_mod_cast h₀
    · exact_mod_cast h₁
  calc |f F| * |(flagDensity₁ F.2 G.2 : ℝ)| ≤ |f F| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |f F| := mul_one _

/-- The size-`L` expansion of a flag vector: the formal combination of all
size-`L` flags weighted by the vector's density evaluations. -/
noncomputable def expandAt (L : ℕ) (f : FlagVector σ) : FlagVector σ :=
  ∑ G : FlagWithSize σ L, densityEval f ⟨L, G⟩ • basisVector ⟨L, G⟩

theorem expandAt_basisVector (F : FinFlag σ) (L : ℕ)
    : expandAt L (basisVector F) = flagExpansion F L
  := by
  dsimp only [expandAt, flagExpansion]
  apply Finset.sum_congr rfl
  intro G _
  rw [densityEval_basisVector]
  simp only [rat_smul_eq_real_smul]

/-- A flag vector supported on sizes `≤ L` is flag-equal (`∼v`) to its size-`L`
expansion. This is the linear extension of Razborov's averaging relation. -/
theorem flagVector_eqv_expandAt {f : FlagVector σ} {L : ℕ}
    (h_supp : ∀ F ∈ f.support, F.1 ≤ L)
    : f ∼v expandAt L f
  := by
  have h1 : f ∼v ∑ F ∈ f.support, f F • flagExpansion F L := by
    nth_rw 1 [flagVector_eq_sum_basisVector f]
    apply flagVectorEqv_sum
    intro F hF
    exact flagVectorEqv_smul _ (basisVector_eqv_flagExpansion F L (h_supp F hF))
  have h2 : (∑ F ∈ f.support, f F • flagExpansion F L) = expandAt L f := by
    dsimp only [flagExpansion, expandAt, densityEval, linearExtension]
    simp_rw [rat_smul_eq_real_smul, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro G _
    rw [← sum_smul]
  exact h1.trans (flagVector_eq_eqv h2)

theorem expandAt_eq_zero_of_eval_zero {f : FlagVector σ} {L : ℕ}
    (h : ∀ G : FlagWithSize σ L, densityEval f ⟨L, G⟩ = 0)
    : expandAt L f = 0
  := by
  apply Finset.sum_eq_zero
  intro G _
  rw [h G, zero_smul]

/-- **Zero-space membership criterion.** A vector supported on sizes `≤ L`
whose density evaluations vanish at every size-`L` host lies in `ZeroSpace σ`.
This is the tool behind Razborov's Lemma 4.2 b) / 4.4 b). -/
theorem mem_zeroSpace_of_densityEval_zero {f : FlagVector σ} {L : ℕ}
    (h_supp : ∀ F ∈ f.support, F.1 ≤ L)
    (h_eval : ∀ G : FlagWithSize σ L, densityEval f ⟨L, G⟩ = 0)
    : f ∈ ZeroSpace σ
  := by
  have h := flagVector_eqv_expandAt h_supp
  dsimp only [flagVectorEqv] at h
  rwa [expandAt_eq_zero_of_eval_zero h_eval, sub_zero] at h

/-- The density evaluations of a generating relation `zeroElement F ℓ` vanish
at every host of size `L ≥ ℓ`; this is exactly the chain rule
`p(F; G) = ∑_{F'} p(F; F') · p(F'; G)`. -/
theorem densityEval_zeroElement (F : FinFlag σ) {ℓ L : ℕ} (hℓ : F.1 ≤ ℓ) (hL : ℓ ≤ L)
    (G : FlagWithSize σ L)
    : densityEval (zeroElement F ℓ) ⟨L, G⟩ = 0
  := by
  dsimp only [zeroElement]
  rw [densityEval_sub, sub_eq_zero, densityEval_basisVector]
  dsimp only [flagExpansion]
  rw [densityEval_sum]
  simp_rw [rat_smul_eq_real_smul, densityEval_smul, densityEval_basisVector]
  rw [density_chain_rule₁₁ ℓ F.2 G (finFlag_size_ge_n₀ F) hℓ hL]
  push_cast
  rfl

/-- Every element of the zero space has vanishing density evaluations at all
sufficiently large host sizes. -/
theorem zeroSpace_densityEval_eventually_zero {k : FlagVector σ} (hk : k ∈ ZeroSpace σ)
    : ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ G : FlagWithSize σ L, densityEval k ⟨L, G⟩ = 0
  := by
  obtain ⟨I, hI, c, v, hv, hk_sum⟩ := zeroSpace_eq_sum_spanElement k hk
  simp only [mem_zeroSet] at hv
  choose F ℓ hFℓ hveq using hv
  refine ⟨Finset.univ.sup ℓ, fun L hL G => ?_⟩
  rw [hk_sum, densityEval_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [densityEval_smul, hveq i,
    densityEval_zeroElement (F i) (hFℓ i) (le_trans (Finset.le_sup (mem_univ i)) hL) G,
    mul_zero]

end Differential
end FlagAlgebras
