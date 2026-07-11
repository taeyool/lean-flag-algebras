import Mathlib.Tactic

/-! # A total-variation bound for product distributions

The analytic heart of the planted blow-up estimate (paper §5, `eq:good-unnormalized-weight-bound`):
for two probability vectors `μ, ν` on a finite set, the product distributions on `q`-tuples are
close in `ℓ¹` to within `q · ‖μ − ν‖₁`.  This is a self-contained finite-sum inequality, proved
by peeling one coordinate at a time and telescoping.

It feeds the comparison between the clone-weighted sampling distribution on a blow-up and the
uniform distribution on the base graph.

## Relation to the clone-root-plantability proof

This module formalises `eq:good-unnormalized-weight-bound` (`prod_tv_bound`) and the accompanying
`ℓ¹`-normalisation estimate (`l1_normalization_bound`) for general (non-uniform) product
distributions. The clone-root-plantability proof (`CloneClosed`) uses the **uniform**
`(M+1)`-blow-up (every clone class the same size), where the planted-estimate gap is controlled
directly by the explicit binomial ratio (`PlantedEstimate`, `BinomialRatio`), with no need to
compare two distinct product distributions in TV. This file therefore stands as a self-contained
record of the general bound, imported only by the `MetaTheory` aggregator.
-/

namespace FlagAlgebras.MetaTheory

open Finset

variable {α : Type*} [Fintype α]

/-- Non-dependent "append at the end" (`Fin.snoc` specialised to a constant motive, so the
elaborator doesn't have to guess the dependent type). -/
def snocLast {q : ℕ} (w : Fin q → α) (a : α) : Fin (q + 1) → α := Fin.snoc w a

omit [Fintype α] in
@[simp] lemma snocLast_castSucc {q : ℕ} (w : Fin q → α) (a : α) (i : Fin q) :
    snocLast w a i.castSucc = w i := Fin.snoc_castSucc ..

omit [Fintype α] in
@[simp] lemma snocLast_last {q : ℕ} (w : Fin q → α) (a : α) :
    snocLast w a (Fin.last q) = a := Fin.snoc_last ..

omit [Fintype α] in
lemma snocLast_init_self {q : ℕ} (v : Fin (q + 1) → α) :
    snocLast (Fin.init v) (v (Fin.last q)) = v := Fin.snoc_init_self v

omit [Fintype α] in
/-- The bijection `(Fin q → α) × α ≃ (Fin (q+1) → α)` given by appending the last coordinate. -/
lemma snocPair_bijective (q : ℕ) :
    Function.Bijective (fun p : (Fin q → α) × α => snocLast p.1 p.2) := by
  constructor
  · rintro ⟨w, a⟩ ⟨w', a'⟩ h
    simp only at h
    have h1 : w = w' := by funext i; have := congrFun h i.castSucc; simpa using this
    have h2 : a = a' := by have := congrFun h (Fin.last q); simpa using this
    simp [h1, h2]
  · intro v
    exact ⟨(Fin.init v, v (Fin.last q)), snocLast_init_self v⟩

/-- Peeling the last coordinate of a sum over `Fin (q+1)`-tuples. -/
lemma sum_fin_succ_eq {β : Type*} [AddCommMonoid β] (q : ℕ) (G : (Fin (q + 1) → α) → β) :
    ∑ v : Fin (q + 1) → α, G v = ∑ w : Fin q → α, ∑ a : α, G (snocLast w a) := by
  rw [← Fintype.sum_bijective (fun p : (Fin q → α) × α => snocLast p.1 p.2)
        (snocPair_bijective q) (fun p => G (snocLast p.1 p.2)) G (fun _ => rfl),
    Fintype.sum_prod_type]

/-- Summing a product over all `q`-tuples factors as a power of the coordinate sum. -/
lemma sum_prod_eq_pow (ν : α → ℝ) (q : ℕ) :
    ∑ v : Fin q → α, ∏ j, ν (v j) = (∑ a, ν a) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_fin_succ_eq]
    simp_rw [Fin.prod_univ_castSucc, snocLast_castSucc, snocLast_last, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ih, ← pow_succ]

/-- **Total-variation bound for product distributions** (`eq:good-unnormalized-weight-bound`):
for probability vectors `μ, ν` on a finite set, the `q`-fold product distributions differ in
`ℓ¹` by at most `q · ‖μ − ν‖₁`. -/
theorem prod_tv_bound (μ ν : α → ℝ) (hμ : ∑ a, μ a = 1) (hν : ∑ a, ν a = 1)
    (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ a, 0 ≤ ν a) (q : ℕ) :
    ∑ v : Fin q → α, |∏ j, μ (v j) - ∏ j, ν (v j)| ≤ q * ∑ a, |μ a - ν a| := by
  induction q with
  | zero => simp
  | succ q ih =>
    have key : ∀ (w : Fin q → α) (a : α),
        |∏ j, μ (snocLast w a j) - ∏ j, ν (snocLast w a j)|
          ≤ μ a * |∏ j, μ (w j) - ∏ j, ν (w j)| + |μ a - ν a| * ∏ j, ν (w j) := by
      intro w a
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      simp only [snocLast_castSucc, snocLast_last]
      have e : (∏ j, μ (w j)) * μ a - (∏ j, ν (w j)) * ν a
          = μ a * ((∏ j, μ (w j)) - ∏ j, ν (w j)) + (μ a - ν a) * ∏ j, ν (w j) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hμ0 a),
        abs_of_nonneg (Finset.prod_nonneg fun j _ => hν0 (w j))]
    calc ∑ v : Fin (q + 1) → α, |∏ j, μ (v j) - ∏ j, ν (v j)|
        = ∑ w : Fin q → α, ∑ a : α,
            |∏ j, μ (snocLast w a j) - ∏ j, ν (snocLast w a j)| := sum_fin_succ_eq q _
      _ ≤ ∑ w : Fin q → α, ∑ a : α,
            (μ a * |∏ j, μ (w j) - ∏ j, ν (w j)| + |μ a - ν a| * ∏ j, ν (w j)) :=
          Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun a _ => key w a
      _ = ∑ w : Fin q → α,
            (|∏ j, μ (w j) - ∏ j, ν (w j)| + (∑ a, |μ a - ν a|) * ∏ j, ν (w j)) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul, hμ, one_mul]
          · rw [← Finset.sum_mul]
      _ = (∑ w : Fin q → α, |∏ j, μ (w j) - ∏ j, ν (w j)|)
            + (∑ a, |μ a - ν a|) * ∑ w : Fin q → α, ∏ j, ν (w j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ w : Fin q → α, |∏ j, μ (w j) - ∏ j, ν (w j)|) + (∑ a, |μ a - ν a|) := by
          rw [sum_prod_eq_pow, hν, one_pow, mul_one]
      _ ≤ (↑(q + 1)) * ∑ a, |μ a - ν a| := by
          have hexp : (↑(q + 1) : ℝ) * ∑ a, |μ a - ν a|
              = ↑q * (∑ a, |μ a - ν a|) + ∑ a, |μ a - ν a| := by push_cast; ring
          rw [hexp]; linarith [ih]

/-- **The `ℓ¹` normalization estimate** (paper §5, lines 877–901): the clone-weighted
probability vector `v ↦ a v / A` (with `A = ∑ a`) is within `4·err` in `ℓ¹` of the "uniform"
vector `v ↦ c / β` (with `β = ∑ c = |U|·c`), provided the unnormalized weights `a v` are within
`err` (summed) of the constant `c` and `β ≥ 1/2`.  Composed with `prod_tv_bound`, this gives the
total-variation target for the planted blow-up estimate. -/
theorem l1_normalization_bound {U : Type*} [Fintype U] (a : U → ℝ) (c err : ℝ)
    (ha : ∀ v, 0 ≤ a v) (herr : ∑ v, |a v - c| ≤ err)
    (hβ : (1 : ℝ) / 2 ≤ ∑ _v : U, c) (hA : 0 < ∑ v, a v) :
    ∑ v, |a v / (∑ u, a u) - c / (∑ _u : U, c)| ≤ 4 * err := by
  set A := ∑ u, a u with hAdef
  set β := ∑ _u : U, c with hβdef
  have hβpos : (0 : ℝ) < β := by linarith
  have herr0 : 0 ≤ err := le_trans (Finset.sum_nonneg fun v _ => abs_nonneg _) herr
  have hAβ : |A - β| ≤ err := by
    have hsub : A - β = ∑ v, (a v - c) := by rw [hAdef, hβdef, Finset.sum_sub_distrib]
    rw [hsub]; exact (Finset.abs_sum_le_sum_abs _ _).trans herr
  have htwo : ∀ x : ℝ, 0 ≤ x → x / β ≤ 2 * x := fun x hx => by
    rw [div_le_iff₀ hβpos]; nlinarith [hβ, hx]
  calc ∑ v, |a v / A - c / β|
      ≤ ∑ v, (|a v / A - a v / β| + |a v / β - c / β|) :=
        Finset.sum_le_sum fun v _ => abs_sub_le _ _ _
    _ = (∑ v, |a v / A - a v / β|) + (∑ v, |a v / β - c / β|) := Finset.sum_add_distrib
    _ ≤ 2 * err + 2 * err := by
        gcongr ?_ + ?_
        · have hid : ∀ v, |a v / A - a v / β| = a v * |1 / A - 1 / β| := fun v => by
            rw [div_eq_mul_inv (a v), div_eq_mul_inv (a v), ← mul_sub, abs_mul,
              abs_of_nonneg (ha v), one_div, one_div]
          simp_rw [hid]
          rw [← Finset.sum_mul, ← hAdef]
          have hcompute : A * |1 / A - 1 / β| = |A - β| / β := by
            have hstep : (1 : ℝ) / A - 1 / β = (β - A) / (A * β) := by
              rw [div_sub_div _ _ (ne_of_gt hA) (ne_of_gt hβpos), one_mul, mul_one]
            rw [hstep, abs_div, abs_of_pos (mul_pos hA hβpos), abs_sub_comm β A]
            field_simp
          rw [hcompute]
          calc |A - β| / β ≤ err / β := by gcongr
            _ ≤ 2 * err := htwo err herr0
        · have hid : ∀ v, |a v / β - c / β| = |a v - c| / β := fun v => by
            rw [div_sub_div_same, abs_div, abs_of_pos hβpos]
          simp_rw [hid]
          rw [← Finset.sum_div]
          calc (∑ v, |a v - c|) / β ≤ err / β := by gcongr
            _ ≤ 2 * err := htwo err herr0
    _ = 4 * err := by ring

end FlagAlgebras.MetaTheory
