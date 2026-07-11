import Mathlib

/-! # Limits of the planted-estimate ratio under uniform clone sizes

Analytic core (§5 of `MetaTheory/paper.tex`) of the uniform-clone specialisation of
`lem:planted-estimate`: it shows the "good" probability `ρ` of `PlantedEstimate.planted_estimate`
tends to `1` in the iterated `M → ∞`, `n → ∞` limit, so the planted blow-up density matches the
base density in the limit.  (`E1`/`E2` below are this file's own mnemonics for the two limit
lemmas, not paper labels.)

Two analytic limit lemmas about the planted-estimate ratio when every clone of the blow-up has the
*same* size `M`, so an `n`-vertex base blows up to a graph on `n · M` vertices.  Writing `k` for the
type size and `ℓ` for the test-flag size, set `r := ℓ − k`.

The relevant ratio is
`ρ_M(n) = (Mʳ · C(n−k, r)) / C(n·M−k, r)`,
the probability that a uniform `r`-subset of the non-root blow-up vertices meets each clone class at
most once (cf. `lem:planted-estimate`).

* `rho_tendsto_atTop`: for fixed `n, k, r`, `ρ_M(n) → ρ_∞(n) := descFactorial(n−k, r) / nʳ` as
  `M → ∞`.  Each blow-up factor `M / (n·M − k − i)` tends to `1/n`, so the `r`-fold product tends to
  `1/nʳ`, and `Mʳ · C(n−k, r) / C(n·M−k, r) = descFactorial(n−k, r) · ∏_{i<r} M/(n·M−k−i)`.
* `rho_inf_tendsto_one`: `ρ_∞(n) = descFactorial(n−k, r) / nʳ → 1` as `n → ∞` (fixed `k, r`), since
  `descFactorial(n−k, r) / nʳ = ∏_{i<r} (n−k−i)/n` and each factor `1 − (k+i)/n → 1`.

Everything is stated over `ℚ`; the meaning is the limit value of the rational ratio in each case. -/

open Filter Topology

namespace FlagAlgebras.MetaTheory

/-- A single blow-up factor `M / (n·M − c)` tends to `1/n` as `M → ∞`, for `n > 0` and any
constant `c` (dividing numerator and denominator by `M`, `n·M/M = n` and `c/M → 0`). -/
private theorem factor_tendsto (n c : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => (M : ℚ) / ((n : ℚ) * M - c)) atTop (𝓝 (1 / (n : ℚ))) := by
  have hcM : Tendsto (fun M : ℕ => (c : ℚ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℚ) (c : ℚ)
  have hden : Tendsto (fun M : ℕ => (n : ℚ) - (c : ℚ) / M) atTop (𝓝 (n : ℚ)) := by
    have := (tendsto_const_nhds (x := (n : ℚ)) (f := atTop (α := ℕ))).sub hcM
    simpa using this
  have hnne : (n : ℚ) ≠ 0 := by positivity
  have hinv : Tendsto (fun M : ℕ => 1 / ((n : ℚ) - (c : ℚ) / M)) atTop (𝓝 (1 / (n : ℚ))) :=
    Tendsto.div tendsto_const_nhds hden hnne
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMpos : (0 : ℚ) < M := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM
  field_simp

/-- The blow-up factor in the form occurring in the ratio, `M / (n·M − k − i)`, tends to `1/n`. -/
private theorem factor_tendsto' (n k i : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => (M : ℚ) / ((n * M - k - i : ℕ) : ℚ)) atTop (𝓝 (1 / (n : ℚ))) := by
  refine (factor_tendsto n (k + i) hn).congr' ?_
  filter_upwards [eventually_ge_atTop (k + i)] with M hM
  have h1 : k + i ≤ n * M := le_trans hM (Nat.le_mul_of_pos_left M hn)
  rw [Nat.sub_sub]
  push_cast [Nat.cast_sub h1]
  ring

/-- **E1.**  For fixed `n, k, r` (with `1 ≤ r` and `0 < n`), the uniform-clone planted-estimate ratio
`Mʳ · C(n−k, r) / C(n·M−k, r)` tends, as `M → ∞`, to `ρ_∞(n) = descFactorial(n−k, r) / nʳ`. -/
theorem rho_tendsto_atTop (n k r : ℕ) (_hr : 1 ≤ r) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M : ℚ) ^ r * ((n - k).choose r : ℚ)) / (((n * M - k).choose r : ℚ)))
      atTop (𝓝 (((n - k).descFactorial r : ℚ) / ((n : ℚ) ^ r))) := by
  -- The `r`-fold product of blow-up factors tends to `∏ (1/n) = 1/nʳ`.
  have hprod : Tendsto
      (fun M : ℕ => ∏ i ∈ Finset.range r, ((M : ℚ) / ((n * M - k - i : ℕ) : ℚ)))
      atTop (𝓝 (∏ _i ∈ Finset.range r, (1 / (n : ℚ)))) := by
    apply tendsto_finset_prod
    intro i _
    exact factor_tendsto' n k i hn
  -- Multiply by the constant `descFactorial (n−k) r`.
  have hmul : Tendsto
      (fun M : ℕ => ((n - k).descFactorial r : ℚ) *
        ∏ i ∈ Finset.range r, ((M : ℚ) / ((n * M - k - i : ℕ) : ℚ)))
      atTop (𝓝 (((n - k).descFactorial r : ℚ) * ∏ _i ∈ Finset.range r, (1 / (n : ℚ)))) :=
    tendsto_const_nhds.mul hprod
  -- Identify the limit value `descFactorial(n−k, r) · (1/n)ʳ = descFactorial(n−k, r) / nʳ`.
  have hlim : ((n - k).descFactorial r : ℚ) * ∏ _i ∈ Finset.range r, (1 / (n : ℚ))
      = ((n - k).descFactorial r : ℚ) / ((n : ℚ) ^ r) := by
    rw [Finset.prod_const, Finset.card_range, one_div, inv_pow, ← div_eq_mul_inv]
  rw [← hlim]
  -- The ratio equals the constant times the product, eventually (`M ≥ k + r`).
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (k + r)] with M hM
  symm
  have hfact : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have e1 : ((n - k).choose r : ℚ) = ((n - k).descFactorial r : ℚ) / (r.factorial : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; field_simp
  have e2 : ((n * M - k).choose r : ℚ) = ((n * M - k).descFactorial r : ℚ) / (r.factorial : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; field_simp
  rw [e1, e2]
  have e3 : ((n * M - k).descFactorial r : ℚ)
      = ∏ i ∈ Finset.range r, ((n * M - k - i : ℕ) : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range]; push_cast; rfl
  rw [e3]
  have hprodne : ∏ i ∈ Finset.range r, ((n * M - k - i : ℕ) : ℚ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [Finset.mem_range] at hi
    have : n * M - k - i ≠ 0 := by
      have hkr : k + r ≤ n * M := le_trans hM (Nat.le_mul_of_pos_left M hn)
      omega
    exact_mod_cast this
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  field_simp

/-- A single factor of `ρ_∞(n)`, namely `(n−k−i)/n = 1 − (k+i)/n`, tends to `1` as `n → ∞`. -/
private theorem factor_one_tendsto (k i : ℕ) :
    Tendsto (fun n : ℕ => ((n - k - i : ℕ) : ℚ) / (n : ℚ)) atTop (𝓝 1) := by
  have hci : Tendsto (fun n : ℕ => (((k + i) : ℕ) : ℚ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℚ) (((k + i) : ℕ) : ℚ)
  have hbase : Tendsto (fun n : ℕ => (1 : ℚ) - (((k + i) : ℕ) : ℚ) / n) atTop (𝓝 (1 : ℚ)) := by
    have := (tendsto_const_nhds (x := (1 : ℚ)) (f := atTop (α := ℕ))).sub hci
    simpa using this
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (k + i + 1)] with n hn
  have h1 : k + i ≤ n := by omega
  rw [Nat.sub_sub]
  push_cast [Nat.cast_sub h1]
  have hnpos : (0 : ℚ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  field_simp

/-- **E2.**  `ρ_∞(n) = descFactorial(n−k, r) / nʳ` tends to `1` as `n → ∞` (fixed `k, r`):
it equals `∏_{i<r} (n−k−i)/n`, a product of `r` factors each tending to `1`. -/
theorem rho_inf_tendsto_one (k r : ℕ) :
    Tendsto (fun n : ℕ => ((n - k).descFactorial r : ℚ) / ((n : ℚ) ^ r)) atTop (𝓝 1) := by
  have hprod : Tendsto
      (fun n : ℕ => ∏ i ∈ Finset.range r, ((n - k - i : ℕ) : ℚ) / (n : ℚ))
      atTop (𝓝 (∏ _i ∈ Finset.range r, (1 : ℚ))) := by
    apply tendsto_finset_prod
    intro i _
    exact factor_one_tendsto k i
  rw [Finset.prod_const_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (k + r)] with n hn
  symm
  have e3 : ((n - k).descFactorial r : ℚ) = ∏ i ∈ Finset.range r, ((n - k - i : ℕ) : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    rfl
  rw [e3, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]

end FlagAlgebras.MetaTheory
