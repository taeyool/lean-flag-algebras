import Mathlib.Tactic

/-! # A total-variation bound for product distributions

The analytic heart of the planted blow-up estimate (paper §5, `eq:good-unnormalized-weight-bound`):
for two probability vectors `μ, ν` on a finite set, the product distributions on `q`-tuples are
close in `ℓ¹` to within `q · ‖μ − ν‖₁`.  This is a self-contained finite-sum inequality, proved
by peeling one coordinate at a time and telescoping.

It feeds the comparison between the clone-weighted sampling distribution on a blow-up and the
uniform distribution on the base graph.
-/

namespace FlagAlgebras.MetaTheory

open Finset

variable {α : Type*} [Fintype α]

/-- Non-dependent "append at the end" (`Fin.snoc` specialised to a constant motive, so the
elaborator doesn't have to guess the dependent type). -/
def snocLast {q : ℕ} (w : Fin q → α) (a : α) : Fin (q + 1) → α := Fin.snoc w a

@[simp] lemma snocLast_castSucc {q : ℕ} (w : Fin q → α) (a : α) (i : Fin q) :
    snocLast w a i.castSucc = w i := Fin.snoc_castSucc ..

@[simp] lemma snocLast_last {q : ℕ} (w : Fin q → α) (a : α) :
    snocLast w a (Fin.last q) = a := Fin.snoc_last ..

lemma snocLast_init_self {q : ℕ} (v : Fin (q + 1) → α) :
    snocLast (Fin.init v) (v (Fin.last q)) = v := Fin.snoc_init_self v

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

end FlagAlgebras.MetaTheory
