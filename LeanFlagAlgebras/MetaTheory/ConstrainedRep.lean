import LeanFlagAlgebras.FlagAlgebra.FlagSequence
import LeanFlagAlgebras.FlagAlgebra.RandomHom

/-! # The constrained representation theorem

This is the constrained refinement of Razborov's Theorem 3.3(b)
(`positiveHom_as_flagSeq_limit`): a positive homomorphism `ψ` that vanishes on
every `forb`-forbidden flag arises as the density limit of a flag sequence whose
flags are *themselves* forbidden-free (zero density of every forbidden flag).

The proof mirrors `positiveHom_as_flagSeq_limit`: it works over the product
probability space `μ{ψ}` of flag sequences of sizes `n² + n₀`, intersecting the
full-measure convergence event with a full-measure "forbidden-free" event, and
reads off a point of the intersection.
-/

open MeasureTheory Filter Topology

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- For a fixed coordinate `n` and a `forb`-forbidden flag `F`, almost every flag
sequence assigns `F` zero density in its `n`-th component. -/
private theorem ae_flagDensity_forbidden_zero
    (ψ : PositiveHom σ) {forb : FinFlag σ → Prop}
    (hψ : ∀ F : FinFlag σ, forb F → ψ.coe F = 0)
    (n : ℕ) (F : FinFlag σ) (hF : forb F) :
    ∀ᵐ s' ∂μ{ψ}, (flagDensity₁ F.2 (s' n) : ℝ) = 0 := by
  -- The "bad" event is a single-coordinate cylinder.
  -- Its measure equals the marginal probability of the bad flags at size `n² + n₀`.
  have hmarg : μ{ψ} { s' | (flagDensity₁ F.2 (s' n) : ℝ) ≠ 0 } =
      (ψ.toMeasure (Nat.le_add_left n₀ (n ^ 2)))
        { G : FlagWithSize σ (n ^ 2 + n₀) | (flagDensity₁ F.2 G : ℝ) ≠ 0 } := by
    have hpi : { s' : ∀ m, FlagWithSize σ (m ^ 2 + n₀) | (flagDensity₁ F.2 (s' n) : ℝ) ≠ 0 }
        = Set.pi ({n} : Finset ℕ)
          (fun m ↦ { G : FlagWithSize σ (m ^ 2 + n₀) | (flagDensity₁ F.2 G : ℝ) ≠ 0 }) := by
      simp only [Finset.coe_singleton, Set.singleton_pi, Set.preimage_setOf_eq, Function.eval]
    rw [hpi]
    dsimp only [flagSeqMeasure]
    rw [Measure.infinitePi_pi _ (by measurability)]
    simp only [Finset.prod_singleton]
  -- The marginal of the bad flags is zero.
  have hzero : (ψ.toMeasure (Nat.le_add_left n₀ (n ^ 2)))
      { G : FlagWithSize σ (n ^ 2 + n₀) | (flagDensity₁ F.2 G : ℝ) ≠ 0 } = 0 := by
    by_cases hsize : n ^ 2 + n₀ < F.1
    · -- The pattern is larger than the host, so density is deterministically zero.
      have hempty : { G : FlagWithSize σ (n ^ 2 + n₀) | (flagDensity₁ F.2 G : ℝ) ≠ 0 } = ∅ := by
        ext G
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
        have hcard : Fintype.card (Fin F.1) > Fintype.card (Fin (n ^ 2 + n₀)) := by
          simpa only [Fintype.card_fin] using hsize
        rw [flagDensity_le_card_contra hcard]
        norm_num
      rw [hempty, measure_empty]
    · -- Otherwise the host is at least as large as the pattern, and the expected
      -- density is `ψ.coe F = 0`; with non-negativity this forces a.e. zero.
      push_neg at hsize
      set μF := ψ.toMeasure (Nat.le_add_left n₀ (n ^ 2)) with hμF
      have hL2 : MemLp (randomDensity F (n ^ 2 + n₀)) 2 μF :=
        randomDensity_L2 ψ F (Nat.le_add_left n₀ (n ^ 2))
      have hint : Integrable (randomDensity F (n ^ 2 + n₀)) μF :=
        hL2.integrable (by norm_num)
      have hnonneg : 0 ≤ randomDensity F (n ^ 2 + n₀) := by
        intro G
        show (0 : ℝ) ≤ (flagDensity₁ F.2 G : ℝ)
        exact_mod_cast flagListDensity₁_ge_zero F.2 G
      have hintegral : ∫ G, randomDensity F (n ^ 2 + n₀) G ∂μF = 0 := by
        have := randomDensity_expectation ψ F hsize
        -- the measure proofs are propositionally irrelevant, so this rewrites.
        rw [hμF, this, hψ F hF]
      have hae := (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hintegral
      -- The bad flags form a null set for the marginal: `randomDensity F ℓ G =
      -- (flagDensity₁ F.2 G : ℝ)` definitionally, so the two `setOf`s coincide.
      rw [hμF]
      have hnull : μF { G | randomDensity F (n ^ 2 + n₀) G ≠ 0 } = 0 := ae_iff.mp hae
      apply measure_mono_null _ hnull
      intro G hG
      simp only [Set.mem_setOf_eq] at hG ⊢
      exact hG
  rw [ae_iff]
  show μ{ψ} { s' | (flagDensity₁ F.2 (s' n) : ℝ) ≠ 0 } = 0
  rw [hmarg, hzero]

/-- **Constrained representation theorem.** If a positive homomorphism `ψ` vanishes on every
`forb`-forbidden flag, then `ψ` is the limit of a flag sequence whose every flag is itself
forbidden-free (zero density of every forbidden flag). -/
theorem exists_constrained_flagSeq_limit (ψ : PositiveHom σ) (forb : FinFlag σ → Prop)
    (hψ : ∀ F : FinFlag σ, forb F → ψ.coe F = 0) :
    ∃ s : FlagSeq σ, ConvergesTo s ψ.coe ∧
      ∀ (t : ℕ) (F : FinFlag σ), forb F → flagDensity₁ F.2 (s t).2 = 0 := by
  -- Step 1: almost surely the densities converge to `ψ.coe`.
  have h_conv : ∀ᵐ s' ∂μ{ψ},
      ∀ (F : FinFlag σ), Tendsto (fun n ↦ (flagDensity₁ F.2 (s' n) : ℝ)) atTop (𝓝 (ψ.coe F)) := by
    rw [ae_all_iff]
    intro F
    rw [ae_iff]
    simp_rw [atTop_basis.tendsto_iff (nhds_basis_Ioo_Nat_pos (ψ.coe F))]
    push_neg
    apply MeasureTheory.measure_exists_zero
    intro n
    simp_rw [real_mem_Ioo_iff_abs_sub_lt]
    simp only [Set.mem_Ici, forall_const]
    simp_rw [← forall_and_left]
    by_cases hn : n = 0
    · subst hn
      simp only [lt_self_iff_false, CharP.cast_eq_zero, div_zero, false_and, forall_const,
        Set.setOf_false, measure_empty]
    · apply Nat.zero_lt_of_ne_zero at hn
      simp only [hn, true_and, not_lt]
      have hn_recip_pos : 0 < (1 / n : ℝ) := by
        rw [one_div, inv_pos]
        exact Nat.cast_pos.mpr hn
      exact flagSeqMeasure_error_prob_zero ψ F hn_recip_pos
  -- Step 2: almost surely every forbidden flag has zero density in every component.
  have h_ff : ∀ᵐ s' ∂μ{ψ},
      ∀ (n : ℕ) (F : FinFlag σ), forb F → (flagDensity₁ F.2 (s' n) : ℝ) = 0 := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro F
    by_cases hF : forb F
    · filter_upwards [ae_flagDensity_forbidden_zero ψ hψ n F hF] with s' hs' _ using hs'
    · filter_upwards with s' hcon using absurd hcon hF
  -- Step 3: intersect and obtain a single good sequence.
  obtain ⟨s', hconv, hff⟩ := (h_conv.and h_ff).exists
  -- Step 4: build the flag sequence of sizes `n² + n₀`.
  refine ⟨fun n ↦ ⟨n ^ 2 + n₀, s' n⟩, ?_, ?_⟩
  · rw [flagSeq_convergesTo_iff]
    refine ⟨?_, hconv⟩
    intro n m hnm
    simp only [add_lt_add_iff_right]
    exact Nat.pow_lt_pow_left hnm (by norm_num)
  · intro t F hForb
    have h := hff t F hForb
    exact_mod_cast h

end FlagAlgebras.MetaTheory
