import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# (Archived) Boolean functions and multilinear polynomial collapse

ARCHIVED / SUPERSEDED — this file is **not** part of the build (its import is
commented out in `LeanFlagAlgebras.lean`). It is an early, self-contained
experiment with `{±1}`-valued Boolean functions, their Fourier (multilinear
polynomial) representations, and the "quadratic collapse" reducing polynomials
modulo `xᵢ² = 1` on the Boolean cube. It was an exploratory side track and is
unrelated to the active flag-algebra machinery; no direct replacement exists.
-/

namespace Archive.BoolAlgebra

inductive pmone : Type where
| p1 : pmone -- False
| m1 : pmone -- True

def pmone.to_rat : pmone → ℚ :=
  fun v => match v with
  | pmone.p1 => 1
  | pmone.m1 => -1

def pmone.to_bool : pmone → Bool :=
  fun v => match v with
  | pmone.p1 => false
  | pmone.m1 => true

abbrev BoolVector (n : ℕ) := Fin n → pmone


abbrev RealVector (n : ℕ) := Fin n → ℚ
abbrev BoolFunction (n : ℕ) := BoolVector n → pmone

-- TODO : Define Hamming Distance

def max2 : BoolFunction 2 :=
  fun v =>
    match v 0, v 1 with
    | pmone.p1, pmone.p1 => pmone.p1
    | pmone.p1, pmone.m1 => pmone.p1
    | pmone.m1, pmone.p1 => pmone.p1
    | pmone.m1, pmone.m1 => pmone.m1

noncomputable def max2_fourier : (RealVector 2) → ℚ :=
  fun v =>
    1/2 + (v 0) / 2 + (v 1) / 2 - (v 0) * (v 1) / 2

instance :
  ∀ bv : BoolVector 2,
    pmone.to_rat (max2 bv) = max2_fourier (fun i => pmone.to_rat (bv i)) := by
    intro bv
    unfold max2 max2_fourier
    simp
    cases bv 0
    all_goals cases bv 1
    all_goals simp [pmone.to_rat]
    all_goals field_simp
    all_goals ring

def maj3 : BoolFunction 3 :=
  fun v =>
    match v 0, v 1, v 2 with
    | pmone.p1, pmone.p1, pmone.p1 => pmone.p1
    | pmone.p1, pmone.p1, pmone.m1 => pmone.p1
    | pmone.p1, pmone.m1, pmone.p1 => pmone.p1
    | pmone.m1, pmone.p1, pmone.p1 => pmone.p1
    | pmone.p1, pmone.m1, pmone.m1 => pmone.m1
    | pmone.m1, pmone.p1, pmone.m1 => pmone.m1
    | pmone.m1, pmone.m1, pmone.p1 => pmone.m1
    | pmone.m1, pmone.m1, pmone.m1 => pmone.m1

noncomputable def maj3_fourier : (RealVector 3) → ℚ :=
  fun v =>
    (v 0) / 2 + (v 1) / 2 + (v 2) / 2 - (v 0) * (v 1) * (v 2) / 2

instance :
  ∀ bv : BoolVector 3,
    pmone.to_rat (maj3 bv) = maj3_fourier (fun i => pmone.to_rat (bv i)) := by
    intro bv
    unfold maj3 maj3_fourier
    simp
    cases bv 0
    all_goals cases bv 1
    all_goals cases bv 2
    all_goals simp [pmone.to_rat]
    all_goals field_simp
    all_goals ring

open MvPolynomial

variable {n : ℕ}

abbrev BoolPolyBase (n) := MvPolynomial (Fin n) ℚ

def bool_eq (p q : BoolPolyBase n) :=
  ∀ (g : Fin n → ℚ),
    (∀ (i : Fin n),
      g i = 1 ∨ g i = -1) →
      eval g p = eval g q

lemma deg_quad_collapse_ :
  (fun i => i % 2) 0 = 0 := rfl

noncomputable def deg_quad_collapse (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapRange (fun i => i % 2) deg_quad_collapse_

-- This function is actually computable, but it looks like
/-- Reduce a polynomial modulo `xᵢ² = 1` (replace each variable's exponent by its
parity), giving the multilinear polynomial agreeing with `p` on the Boolean cube. -/
noncomputable def quad_collapse (p : BoolPolyBase n) : BoolPolyBase n :=
  -- Sum over the monomials
  -- Given monomial m, take the monomial's degree by mod 2
  -- Ex : 1->1, x -> x, x^2 -> 1, x^3 -> x, ..., etc.
  -- Fold over p.support.toList with add, init as zero
  p.support.sum (fun m => monomial (deg_quad_collapse m) (p.coeff m))

noncomputable def quad_eq (p q : BoolPolyBase n) :=
  quad_collapse p = quad_collapse q

theorem quad_collapse_eq_on_pmone (p : BoolPolyBase n) (g : Fin n → ℚ) :
  (∀ (i : Fin n), g i = 1 ∨ g i = -1) →
  eval g (quad_collapse p) = eval g p :=
  by
    intro h
    unfold quad_collapse
    rw [eval_sum]
    rw [eval_eq']
    have h' :
      ∀ i : (Fin n →₀ ℕ), (eval g) ((monomial (deg_quad_collapse i)) (coeff i p)) = coeff i p * ∏ j : Fin n, g j ^ i j := by
      intro i
      rw [eval_monomial]
      simp
      have h'' :
        ∀ a : Fin n, g a ^ deg_quad_collapse i a = g a ^ i a := by
          intro a
          unfold deg_quad_collapse
          simp
          have hga := h a
          rcases hga with hga | hga
          ·
            rw [hga]
            simp
          ·
            rw [hga]
            -- i a = (i a / 2) * 2 + i a % 2
            rw [<- Nat.div_add_mod (i a) 2]
            rw [pow_add]
            simp [pow_mul]
      have h''f :
        (fun a => g a ^ deg_quad_collapse i a) = (fun a => g a ^ i a) := by
          ext
          apply h''
      rw [h''f]
      simp
    have h'f :
      (fun i => eval g (monomial (deg_quad_collapse i) (coeff i p))) = (fun i => coeff i p * ∏ j : Fin n, g j ^ i j) := by
        ext
        apply h'
    rw [h'f]

lemma deg_quad_collapse_le_one (m : Fin n →₀ ℕ) (i : Fin n) :
  deg_quad_collapse m i ≤ 1 := by
  unfold deg_quad_collapse
  simp
  exact Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide : 0 < 2))

lemma degreeOf_quad_collapse_le_one (p : BoolPolyBase n) (i : Fin n) :
  degreeOf i (quad_collapse p) ≤ 1 := by
  unfold quad_collapse
  refine le_trans (degreeOf_sum_le i p.support (fun m => monomial (deg_quad_collapse m) (p.coeff m))) ?_
  refine Finset.sup_le ?_
  intro m hm
  by_cases hcoeff : p.coeff m = 0
  · simp [hcoeff]
  · rw [degreeOf_monomial_eq (deg_quad_collapse m) i hcoeff]
    exact deg_quad_collapse_le_one m i

private theorem multilinear_eq_zero_of_eval_pmone_eq_zero :
    ∀ {n : ℕ} (p : BoolPolyBase n),
      (∀ i, degreeOf i p ≤ 1) →
      (∀ g : Fin n → ℚ, (∀ i : Fin n, g i = 1 ∨ g i = -1) → eval g p = 0) →
      p = 0
  | 0, p, _hdeg, heval => by
      apply (MvPolynomial.isEmptyRingEquiv ℚ (Fin 0)).injective
      rw [map_zero]
      have h0 := heval (fun i : Fin 0 => Fin.elim0 i) (by intro i; exact Fin.elim0 i)
      simpa using h0
  | n + 1, p, hdeg, heval => by
      let p' : Polynomial (BoolPolyBase n) := finSuccEquiv ℚ n p
      have hpdeg : p'.natDegree ≤ 1 := by
        simpa [p', natDegree_finSuccEquiv] using hdeg 0
      let sA : Finset (BoolPolyBase n) := {MvPolynomial.C (-1 : ℚ), MvPolynomial.C (1 : ℚ)}
      have h_eval_at_roots : ∀ b ∈ sA, Polynomial.eval b p' = 0 := by
        intro b hb
        apply multilinear_eq_zero_of_eval_pmone_eq_zero (n := n) (Polynomial.eval b p')
        · intro j
          have hcoeff0 : degreeOf j (Polynomial.coeff p' 0) ≤ 1 := by
            exact le_trans (degreeOf_coeff_finSuccEquiv p j 0) (hdeg j.succ)
          have hcoeff1 : degreeOf j (Polynomial.coeff p' 1) ≤ 1 := by
            exact le_trans (degreeOf_coeff_finSuccEquiv p j 1) (hdeg j.succ)
          have hbdeg : degreeOf j b = 0 := by
            rcases Finset.mem_insert.mp hb with hb | hb
            · subst hb
              simp
            · have hb' : b = MvPolynomial.C (1 : ℚ) := by simpa using hb
              subst hb'
              simp
          have h_eval_expand : Polynomial.eval b p' = (Polynomial.coeff p' 1) * b + Polynomial.coeff p' 0 := by
            rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg]
            simp [Polynomial.eval_add, Polynomial.eval_mul]
          rw [h_eval_expand]
          refine le_trans (degreeOf_add_le j _ _) ?_
          refine max_le ?_ hcoeff0
          refine le_trans (degreeOf_mul_le j _ _) ?_
          simpa [hbdeg] using add_le_add hcoeff1 (le_refl 0)
        · intro x hx
          have hx0 : eval x b = 1 ∨ eval x b = -1 := by
            rcases Finset.mem_insert.mp hb with hb | hb
            · subst hb
              right
              simp
            · have hb' : b = MvPolynomial.C (1 : ℚ) := by simpa using hb
              subst hb'
              left
              simp
          let g : Fin (n + 1) → ℚ := fun i => Fin.cases (eval x b) x i
          have hxall : ∀ i : Fin (n + 1), g i = 1 ∨ g i = -1 := by
            intro i
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
            · simpa [g] using hx0
            · simpa [g] using hx j
          have h_main := heval g hxall
          have h_rewrite : eval x (Polynomial.eval b p') = eval (Fin.cases (eval x b) x) p := by
            simpa [p'] using (eval_polynomial_eval_finSuccEquiv (R := ℚ) (n := n) (f := p) (x := x) (q := b))
          exact h_rewrite.trans h_main
      have hp'zero : p' = 0 := by
        have hne : (MvPolynomial.C (-1 : ℚ) : BoolPolyBase n) ≠ MvPolynomial.C (1 : ℚ) := by
          intro h
          have : (-1 : ℚ) = 1 := by
            simpa using congrArg MvPolynomial.constantCoeff h
          norm_num at this
        have hs_card : sA.card = 2 := by
          simpa [sA] using (Finset.card_pair hne)
        apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p := p') (s := sA)
        · intro b hb
          exact h_eval_at_roots b hb
        · calc
            p'.natDegree ≤ 1 := hpdeg
            _ < 2 := by decide
            _ = sA.card := by simp [hs_card]
      exact (finSuccEquiv ℚ n).injective (by simpa [p'] using hp'zero)

/-- Two polynomials agree on all `{±1}` points iff they have the same quadratic
collapse, i.e. agreement on the Boolean cube is decided by the multilinear form. -/
theorem bool_eq_quad_eq (p q : BoolPolyBase n) :
  bool_eq p q ↔ quad_eq p q
  := by
    constructor
    · -- bool_eq then quad_eq
      intro h_bool_eq
      unfold quad_eq
      apply eq_of_sub_eq_zero
      apply multilinear_eq_zero_of_eval_pmone_eq_zero (n := n) (quad_collapse p - quad_collapse q)
      · intro i
        refine le_trans (degreeOf_sub_le i (quad_collapse p) (quad_collapse q)) ?_
        exact max_le (degreeOf_quad_collapse_le_one p i) (degreeOf_quad_collapse_le_one q i)
      · intro g hgi
        rw [eval_sub]
        rw [quad_collapse_eq_on_pmone p g hgi]
        rw [quad_collapse_eq_on_pmone q g hgi]
        exact sub_eq_zero.mpr (h_bool_eq g hgi)
    · -- quad_eq then bool_eq
      intro h
      unfold quad_eq at h
      unfold bool_eq
      intro g hgi
      rw [<- quad_collapse_eq_on_pmone p g hgi]
      rw [<- quad_collapse_eq_on_pmone q g hgi]
      rw [h]

end Archive.BoolAlgebra
