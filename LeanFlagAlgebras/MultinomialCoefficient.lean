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
    {r_list : Fin t → ℕ} (n : ℕ) {π : Equiv.Perm (Fin t)}
    : multinomialCoefficient (r_list ∘ π) n = multinomialCoefficient r_list n
  := by
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

@[simp]
lemma multinomialCoefficient_fin_zero
    {r_list : Fin 0 → ℕ} (n : ℕ)
    : multinomialCoefficient r_list n = 1 := by
  simp [multinomialCoefficient]; exact Nat.div_self n.factorial_pos

lemma multinomialCoefficient_fin_one_of_le
    {r_list : Fin 1 → ℕ} {n : ℕ} (h : r_list 0 ≤ n)
    : multinomialCoefficient r_list n =
      n.factorial / ((r_list 0).factorial * (n - r_list 0).factorial)
  := by
  simp [multinomialCoefficient, h]

lemma multinomialCoefficient_fin_one_of_lt
    {r_list : Fin 1 → ℕ} {n : ℕ} (h : n < r_list 0)
    : multinomialCoefficient r_list n = 0
  := by
  simp [multinomialCoefficient, h]

@[simp]
lemma multinomialCoefficient_fin_one
    {r_list : Fin 1 → ℕ} {n : ℕ}
    : multinomialCoefficient r_list n = n.choose (r_list 0) := by
  by_cases h : r_list 0 ≤ n
  · simp only [multinomialCoefficient_fin_one_of_le h, Nat.choose_eq_factorial_div_factorial h]
  · rw [not_le] at h
    simp only [multinomialCoefficient_fin_one_of_lt h, Nat.choose_eq_zero_of_lt h]
