import LeanFlagAlgebras.MetaTheory.DownwardAverage

/-! # The vanishing ideal unlabels to zero (paper §10, `prop:ideal-zero`)

Elements of `A^σ` that vanish on the root-planting set `S_σ` — in particular every
pinning witness `F - c·1_σ` exposed by the §9 obstructions, and all its flag-multiples —
have unlabelled average `0` on every constrained unlabelled limit.  So the witnesses of
the quotient/ensemble gap contribute *nothing* to empty-type density certificates, even
before taking closures.

Formalisation choice (documented in `README.md`): the paper's conclusion "`⟨a⟩_σ = 0` in
`A⁰[T₁]`" is stated in its evaluation form — `φ₀ ⟦a⟧₀ = 0` for every `φ₀ ∈ Q₀` — which is
what the paper's proof establishes and what all downstream uses consume.  (Equality in
the quotient algebra itself would additionally require a separation theorem for
`A⁰[T₁]`, which this development does not formalise.)

All results are `δ = 0` instances of the master bound
`abs_downward_eval_le_of_abs_le_on_Sσ`.
-/

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- **`prop:ideal-zero`, core form**: an element vanishing on `S_σ` has unlabelled
average `0` at every constrained unlabelled limit. -/
theorem downward_eval_eq_zero_of_zero_on_Sσ (T : Constraint σ) {a : FlagAlgebra σ}
    (ha : ∀ χ ∈ Sσ T, (PositiveHomSpace.toPosHom χ) a = 0)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) :
    φ₀ (⟦a⟧₀ : FlagAlgebra ∅ₜ) = 0 := by
  -- `abs_downward_eval_le_of_abs_le_on_Sσ` with `δ := 0`, then `abs_nonpos_iff`.
  have habs : |φ₀ (⟦a⟧₀ : FlagAlgebra ∅ₜ)| ≤ 0 :=
    abs_downward_eval_le_of_abs_le_on_Sσ T (δ := 0) le_rfl
      (fun χ hχ => by rw [ha χ hχ, abs_zero]) hφ₀
  exact abs_nonpos_iff.mp habs

/-- The vanishing locus is an ideal: multiples of an element vanishing on `S_σ` also
unlabel to zero (evaluations are multiplicative). -/
theorem downward_mul_eval_eq_zero_of_zero_on_Sσ (T : Constraint σ) {a : FlagAlgebra σ}
    (ha : ∀ χ ∈ Sσ T, (PositiveHomSpace.toPosHom χ) a = 0) (h : FlagAlgebra σ)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) :
    φ₀ (⟦a * h⟧₀ : FlagAlgebra ∅ₜ) = 0 := by
  -- `χ (a * h) = χ a * χ h = 0` by `PositiveHom.map_mul`; apply the core form.
  refine downward_eval_eq_zero_of_zero_on_Sσ T (fun χ hχ => ?_) hφ₀
  rw [PositiveHom.map_mul, ha χ hχ, zero_mul]

/-- **`prop:ideal-zero` for pinning witnesses**: if `g` is pinned to the value `c` on
`S_σ`, then the pinning witness `g - c·1_σ` and each of its flag-multiples unlabel to
zero on `Q₀`. -/
theorem pinned_witness_downward_eq_zero (T : Constraint σ) {g : FlagAlgebra σ} {c : ℝ}
    (hpin : ∀ χ ∈ Sσ T, (PositiveHomSpace.toPosHom χ) g = c) (h : FlagAlgebra σ)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) :
    φ₀ (⟦(g - c • (1 : FlagAlgebra σ)) * h⟧₀ : FlagAlgebra ∅ₜ) = 0 := by
  -- the witness vanishes on `S_σ`: `χ (g - c•1) = χ g - c = 0`
  -- (`PositiveHom.map_sub`, `map_smul`, `map_one`); apply the multiple form.
  refine downward_mul_eval_eq_zero_of_zero_on_Sσ T (fun χ hχ => ?_) h hφ₀
  rw [PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one, hpin χ hχ, mul_one,
    sub_self]

/-- **`prop:ideal-zero`, congruence form**: two labelled elements with the same
evaluation on `S_σ` have the same unlabelled average on `Q₀`. -/
theorem downward_eval_congr_of_eqOn_Sσ (T : Constraint σ) {s s' : FlagAlgebra σ}
    (h : ∀ χ ∈ Sσ T, (PositiveHomSpace.toPosHom χ) s = (PositiveHomSpace.toPosHom χ) s')
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) :
    φ₀ (⟦s⟧₀ : FlagAlgebra ∅ₜ) = φ₀ (⟦s'⟧₀ : FlagAlgebra ∅ₜ) := by
  -- apply the core form to `s - s'` (`downward_sub`, `PositiveHom.map_sub`, `sub_eq_zero`).
  have h0 : φ₀ (⟦s - s'⟧₀ : FlagAlgebra ∅ₜ) = 0 := by
    refine downward_eval_eq_zero_of_zero_on_Sσ T (fun χ hχ => ?_) hφ₀
    rw [PositiveHom.map_sub, h χ hχ, sub_self]
  rw [downward_sub, PositiveHom.map_sub] at h0
  exact sub_eq_zero.mp h0

end FlagAlgebras.MetaTheory
