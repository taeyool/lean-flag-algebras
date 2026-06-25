import Mathlib.Algebra.BigOperators.Fin

/-! # `Fin.sum_univ_*` for block sizes above eight

Mathlib provides the explicit finite-sum unfoldings `Fin.sum_univ_two` …
`Fin.sum_univ_eight` (generated from the multiplicative versions by
`@[to_additive]`). The flag-algebra SDP proof templates expand
`flagQuadraticForm M v = ∑ i, ∑ j, …` over `Fin n` with these lemmas, so a
certificate whose SDP blocks have more than eight flags needs the same
unfoldings at larger `n`.

These continue the mathlib sequence verbatim — each is proved exactly the way
mathlib proves `Fin.sum_univ_eight` (`rw [Fin.sum_univ_castSucc,
Fin.sum_univ_<prev>]; rfl`), so the resulting right-hand side is the
left-associated explicit sum the templates expect. Sizes nine through sixteen
cover the larger certificates (e.g. `K3forbidC6`, whose blocks are 15 and 10).
-/

namespace Fin

variable {M : Type*} [AddCommMonoid M]

theorem sum_univ_nine (f : Fin 9 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]; rfl

theorem sum_univ_ten (f : Fin 10 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_nine]; rfl

theorem sum_univ_eleven (f : Fin 11 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_ten]; rfl

theorem sum_univ_twelve (f : Fin 12 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eleven]; rfl

theorem sum_univ_thirteen (f : Fin 13 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_twelve]; rfl

theorem sum_univ_fourteen (f : Fin 14 → M) :
    ∑ i, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_thirteen]; rfl

theorem sum_univ_fifteen (f : Fin 15 → M) :
    ∑ i, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13
        + f 14 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_fourteen]; rfl

theorem sum_univ_sixteen (f : Fin 16 → M) :
    ∑ i, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13
        + f 14 + f 15 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_fifteen]; rfl

end Fin
