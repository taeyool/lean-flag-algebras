import Mathlib.Data.Nat.Factorial.BigOperators

variable {t : ℕ}

def multinomialCoefficient
    (r_list : Fin t → ℕ) (n : ℕ) : ℕ
  :=
  let r_sum := ∑ i : Fin t, r_list i
  if _ : n ≥ r_sum then
    Nat.factorial n / ((∏ i : Fin t, Nat.factorial (r_list i)) * Nat.factorial (n - r_sum))
  else 0

lemma multinomialCoefficient_eq
    {r_list₁ r_list₂ : Fin t → ℕ} (n : ℕ) (heq : r_list₁ = r_list₂)
    : multinomialCoefficient r_list₁ n = multinomialCoefficient r_list₂ n
  := by subst heq; rfl

lemma multinomialCoefficient_eq_of_perm
    {r_list₁ r_list₂ : Fin t → ℕ} (n : ℕ) {π : Equiv.Perm (Fin t)} (heq_perm : r_list₁ = r_list₂ ∘ π)
    : multinomialCoefficient r_list₁ n = multinomialCoefficient r_list₂ n
  := by
  rw [heq_perm]
  simp [multinomialCoefficient, Equiv.Perm.sum_comp]
  congr 3
  exact Fintype.prod_equiv π _ _ (congrFun rfl)

lemma multinomialCoefficient_pos
    (r_list : Fin t → ℕ) (n : ℕ) (h_n : n ≥ ∑ i : Fin t, r_list i) :
    multinomialCoefficient r_list n > 0
  := by
  dsimp [multinomialCoefficient]
  simp only [h_n]
  let r_sum := ∑ i : Fin t, r_list i
  let C₀ := ∏ i : Fin t, (r_list i).factorial
  let C₁ := (n - r_sum).factorial
  let C := C₀ * C₁
  show n.factorial / C > 0
  have h_n_factorial_pos : n.factorial > 0 := Nat.factorial_pos n
  have h_dvd : C ∣ n.factorial := by
    have h₀ : C₀ ∣ r_sum.factorial :=
      Nat.prod_factorial_dvd_factorial_sum Finset.univ r_list
    have h₁ : C ∣ r_sum.factorial * C₁ := Nat.mul_dvd_mul_right h₀ C₁
    have h₂ : r_sum.factorial * C₁ ∣ n.factorial :=
      Nat.factorial_mul_factorial_dvd_factorial h_n
    exact dvd_trans h₁ h₂
  exact (Nat.lt_div_iff_mul_lt' h_dvd 0).mpr h_n_factorial_pos

lemma multinomialCoefficient_zero
    (r_list : Fin t → ℕ) (n : ℕ)
    : multinomialCoefficient r_list n = 0 → n < ∑ i : Fin t, r_list i
  := by
  contrapose!
  exact fun h ↦ Nat.ne_zero_of_lt (multinomialCoefficient_pos r_list n h)
