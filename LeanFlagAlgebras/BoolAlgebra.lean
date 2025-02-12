import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import MathLib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Quotient

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
    ring

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
    ∀ (i : Fin n),
      g i = 1 ∨ g i = -1 →
      eval g p = eval g q

lemma deg_quad_collapse_ :
  (fun i => i % 2) 0 = 0 := rfl

noncomputable def deg_quad_collapse (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapRange (fun i => i % 2) deg_quad_collapse_

-- This function is actually computable, but it looks like
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
      ∀ i ∈ support p, (eval g) ((monomial (deg_quad_collapse i)) (coeff i p)) = coeff i p * ∏ j : Fin n, g j ^ i j := by

      sorry
    sorry


theorem bool_eq_quad_eq (p q : BoolPolyBase n) :
  bool_eq p q ↔ quad_eq p q
  := by
    constructor
    · -- bool_eq then quad_eq
      intro h_bool_eq
      unfold quad_eq
      unfold quad_collapse
      unfold bool_eq at h_bool_eq
      apply ext
      intro m
      rw [coeff_sum, coeff_sum]
      simp


      sorry
    · -- quad_eq then bool_eq
      sorry
