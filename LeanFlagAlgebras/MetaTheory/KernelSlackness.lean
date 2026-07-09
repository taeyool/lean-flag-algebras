import LeanFlagAlgebras.MetaTheory.RelativeSlackness
import LeanFlagAlgebras.FlagAlgebra.QuadraticForm

/-! # Kernel form of complementary slackness (paper §11.3, `thm:kernel-slackness`)

An SDP certificate ships, per type, a positive semidefinite matrix `Q` over a vector `v`
of labelled flags — not an explicit list of squares.  This module consumes `Q` directly
(no eigendecomposition, so exact/rational arithmetic survives): with certificate terms
`⟨Q⁽ⁱ⁾v⁽ⁱ⁾, v⁽ⁱ⁾⟩ = flagQuadraticForm (Qs i) (vs i)`,

* `kernel_slackness_soundness` — `φ₀ h ≤ c` on `Y`;
* `kernel_slackness_approx` — for every weight vector `w`,
  `φ₀ ⟦(wᵀQv)²⟧₀ ≤ ⟨Qw, w⟩·Δ` (`kernelCombo` is `wᵀQv`);
* `kernel_slackness_exact_slack` / `_exact_ae` — on the equality slice `φ₀ h = c` the
  slack vanishes and the labelled moment vector `ψ(v)` falls a.s. into `ker Q`;
* `kernel_slackness_global` — if every `φ₀ ∈ Y` attains the bound, `χ(v) ∈ ker Q` for
  every `χ ∈ S_σ(Y)` (each row of `Q` yields a labelled equation on the slice).

Supporting lemmas: the evaluation identity `eval_flagQuadraticForm`
(`φ (flagQuadraticForm Q v) = x ⬝ᵥ Q *ᵥ x` for the moment vector `x = φ ∘ v`), its
non-negativity under `Q.PosSemidef`, and two elementary real-PSD facts proved via the
quadratic discriminant (`posSemidef_dotProduct_mulVec_sq_le`,
`posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero`).

`flagQuadraticForm` and its cone non-negativity come from
`LeanFlagAlgebras/FlagAlgebra/QuadraticForm.lean`.
-/

open MeasureTheory Matrix

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Evaluation of a PSD quadratic form -/

/-- Evaluating a quadratic form at a positive homomorphism gives the quadratic form of
the moment vector: `φ (⟨Qv,v⟩) = x ⬝ᵥ Q *ᵥ x` where `x = fun a => φ (v a)`. -/
lemma eval_flagQuadraticForm {kq : ℕ} (Q : Matrix (Fin kq) (Fin kq) ℝ)
    (v : Fin kq → FlagAlgebra σ) (φ : PositiveHom σ) :
    φ (flagQuadraticForm Q v)
      = (fun a => φ (v a)) ⬝ᵥ (Q *ᵥ (fun a => φ (v a))) := by
  -- `flagQuadraticForm` is `∑ i, ∑ j, Q i j • (v i * v j)`; push `PositiveHom.map_sum`,
  -- `map_smul`, `map_mul` through and compare with `dotProduct`/`mulVec` unfolded
  -- (`Finset.mul_sum`, `mul_comm`/`mul_left_comm` — cf. the computation inside
  -- `flagQuadraticForm_nonneg`, `FlagAlgebra/QuadraticForm.lean`).
  simp only [flagQuadraticForm, PositiveHom.map_sum, PositiveHom.map_smul,
    PositiveHom.map_mul, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Evaluations of a PSD quadratic form are non-negative — at EVERY positive
homomorphism (paper `rem:cs-shape`: hypothesis (i) of the slackness theorem is automatic
for matrix-certificate terms). -/
lemma eval_flagQuadraticForm_nonneg {kq : ℕ} {Q : Matrix (Fin kq) (Fin kq) ℝ}
    (hQ : Q.PosSemidef) (v : Fin kq → FlagAlgebra σ) (φ : PositiveHom σ) :
    0 ≤ φ (flagQuadraticForm Q v) := by
  -- Pointwise instance of the base cone-nonnegativity lemma
  -- (`flagQuadraticForm_nonneg`, `FlagAlgebra/QuadraticForm.lean`).
  have h := flagQuadraticForm_nonneg Q hQ v
  rw [ge_iff_le, le_def, sub_zero] at h
  exact h φ

/-! ## Two elementary facts about real PSD matrices -/

/-- Symmetry of the bilinear form of a real Hermitian (= symmetric) matrix:
`y ⬝ᵥ Q *ᵥ z = z ⬝ᵥ Q *ᵥ y`. -/
private lemma isHermitian_dotProduct_mulVec_comm {kq : ℕ}
    {Q : Matrix (Fin kq) (Fin kq) ℝ} (hQ : Q.IsHermitian) (y z : Fin kq → ℝ) :
    y ⬝ᵥ (Q *ᵥ z) = z ⬝ᵥ (Q *ᵥ y) := by
  have hQt : Qᵀ = Q := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hQ.eq
  have hvm : y ᵥ* Q = Q *ᵥ y := by
    rw [← Matrix.vecMul_transpose, hQt]
  rw [Matrix.dotProduct_mulVec, hvm, dotProduct_comm]

/-- Cauchy–Schwarz for the bilinear form of a real PSD matrix:
`(w ⬝ᵥ Q *ᵥ x)² ≤ (w ⬝ᵥ Q *ᵥ w) · (x ⬝ᵥ Q *ᵥ x)`. -/
lemma posSemidef_dotProduct_mulVec_sq_le {kq : ℕ} {Q : Matrix (Fin kq) (Fin kq) ℝ}
    (hQ : Q.PosSemidef) (x w : Fin kq → ℝ) :
    (w ⬝ᵥ (Q *ᵥ x)) ^ 2 ≤ (w ⬝ᵥ (Q *ᵥ w)) * (x ⬝ᵥ (Q *ᵥ x)) := by
  -- Discriminant route: `t ↦ (x + t • w) ⬝ᵥ Q *ᵥ (x + t • w) ≥ 0`
  -- (`hQ.dotProduct_mulVec_nonneg`, `star_trivial`); expand by bilinearity
  -- (`Matrix.mulVec_add`, `Matrix.mulVec_smul`, `Matrix.add_dotProduct`,
  -- `Matrix.smul_dotProduct`, `Matrix.dotProduct_add`, `Matrix.dotProduct_smul`), use
  -- symmetry `w ⬝ᵥ Q *ᵥ x = x ⬝ᵥ Q *ᵥ w` (from `hQ.1 : Q.IsHermitian`, i.e. `Qᵀ = Q`
  -- over ℝ; e.g. via `Matrix.dotProduct_mulVec` + `Matrix.vecMul_transpose` +
  -- `Matrix.dotProduct_comm`), then `discrim_le_zero` and `nlinarith`/`linarith`.
  have hsym := isHermitian_dotProduct_mulVec_comm hQ.1 x w
  have key : ∀ t : ℝ,
      0 ≤ (w ⬝ᵥ (Q *ᵥ w)) * (t * t) + 2 * (w ⬝ᵥ (Q *ᵥ x)) * t + x ⬝ᵥ (Q *ᵥ x) := by
    intro t
    have h0 := hQ.dotProduct_mulVec_nonneg (x + t • w)
    rw [star_trivial] at h0
    have hexp : (x + t • w) ⬝ᵥ (Q *ᵥ (x + t • w))
        = (w ⬝ᵥ (Q *ᵥ w)) * (t * t) + 2 * (w ⬝ᵥ (Q *ᵥ x)) * t + x ⬝ᵥ (Q *ᵥ x) := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hsym]
      ring
    rwa [hexp] at h0
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

/-- For a real PSD matrix, a vector with vanishing quadratic value lies in the kernel:
`x ⬝ᵥ Q *ᵥ x = 0 → Q *ᵥ x = 0`. -/
lemma posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero {kq : ℕ}
    {Q : Matrix (Fin kq) (Fin kq) ℝ} (hQ : Q.PosSemidef) {x : Fin kq → ℝ}
    (hx : x ⬝ᵥ (Q *ᵥ x) = 0) :
    Q *ᵥ x = 0 := by
  -- `funext a`; apply `posSemidef_dotProduct_mulVec_sq_le` with `w := Pi.single a 1`:
  -- `(Pi.single a 1 ⬝ᵥ Q *ᵥ x)² ≤ (…) * 0 = 0`, and
  -- `Pi.single a 1 ⬝ᵥ y = y a` (`Matrix.single_dotProduct`/`Matrix.dotProduct_single`
  -- + `one_mul`; names vary — `Finset.sum_eq_single` as fallback).  `pow_eq_zero_iff`.
  funext a
  have h := posSemidef_dotProduct_mulVec_sq_le hQ x (Pi.single a 1)
  rw [hx, mul_zero, single_dotProduct, one_mul] at h
  have h2 : (Q *ᵥ x) a ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  simpa using sq_eq_zero_iff.mp h2

/-! ## The kernel slackness theorem -/

/-- The row combination `wᵀQv = ∑ a, (Q *ᵥ w) a • v a` of the flag vector `v` (for
symmetric `Q`, `(wᵀQ)ₐ = (Q *ᵥ w)ₐ`).  Its vanishing on the slice is the labelled
equation the certificate row `wᵀQ` yields. -/
noncomputable def kernelCombo {kq : ℕ} (Q : Matrix (Fin kq) (Fin kq) ℝ)
    (v : Fin kq → FlagAlgebra σ) (w : Fin kq → ℝ) : FlagAlgebra σ :=
  ∑ a, (Q *ᵥ w) a • v a

section Kernel

variable {Y : Set (PositiveHomSpace ∅ₜ)}
  {m : ℕ} {k : Fin m → ℕ} {σs : ∀ i, FlagType (Fin (k i))}
  {kq : Fin m → ℕ} {Qs : ∀ i, Matrix (Fin (kq i)) (Fin (kq i)) ℝ}
  {vs : ∀ i, Fin (kq i) → FlagAlgebra (σs i)}
  {h n : FlagAlgebra ∅ₜ} {c : ℝ}

/-- **Kernel slackness, soundness** (`thm:kernel-slackness` (1)): a matrix certificate
bounds the objective, `φ₀ h ≤ c` on `Y`. -/
theorem kernel_slackness_soundness
    (hQ : ∀ i, (Qs i).PosSemidef)
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) :
    φ₀ h ≤ c := by
  -- Instance of `relative_slackness_soundness` with `lam := fun _ => 1`,
  -- `fs i := flagQuadraticForm (Qs i) (vs i)`: hypothesis (i) is
  -- `eval_flagQuadraticForm_nonneg` (at every `χ`, a fortiori on `relSσ`), and `one_mul`
  -- reconciles the certificate shapes (`Finset.sum_congr`).
  exact relative_slackness_soundness (lam := fun _ => 1)
    (fs := fun i => flagQuadraticForm (Qs i) (vs i))
    (fun _ => one_pos)
    (fun i χ _ => eval_flagQuadraticForm_nonneg (hQ i) (vs i) _)
    hn (fun φ₀' hφ₀' => by simpa using hcert φ₀' hφ₀') hφ₀

/-- **Kernel slackness, approximate form** (`thm:kernel-slackness` (2)): for every weight
vector `w`, the square of the row combination is controlled by the slack:
`φ₀ ⟦(wᵀQv)·(wᵀQv)⟧₀ ≤ (w ⬝ᵥ Q *ᵥ w) · (c - φ₀ h)`. -/
theorem kernel_slackness_approx
    (hQ : ∀ i, (Qs i).PosSemidef)
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (i : Fin m)
    (w : Fin (kq i) → ℝ) :
    φ₀ (⟦kernelCombo (Qs i) (vs i) w * kernelCombo (Qs i) (vs i) w⟧₀ : FlagAlgebra ∅ₜ)
      ≤ (w ⬝ᵥ ((Qs i) *ᵥ w)) * (c - φ₀ h) := by
  -- Two steps.
  -- (A) SEMANTIC-CONE COMPARISON, no measure theory: at EVERY `ψ : PositiveHom (σs i)`,
  --     `ψ (kernelCombo …) = (Qs i *ᵥ w) ⬝ᵥ xψ = w ⬝ᵥ (Qs i *ᵥ xψ)` for the moment
  --     vector `xψ = fun a => ψ (vs i a)` (`map_sum`/`map_smul`; symmetry from
  --     `(hQ i).1`), so by `posSemidef_dotProduct_mulVec_sq_le` and
  --     `eval_flagQuadraticForm`,
  --     `ψ (kernelCombo·kernelCombo) ≤ (w ⬝ᵥ Qs i *ᵥ w) · ψ (flagQuadraticForm …)`.
  --     Hence `(w ⬝ᵥ Qs i *ᵥ w) • flagQuadraticForm … - kernelCombo·kernelCombo` is in
  --     the semantic cone; `downward_preserve_semanticCone` (cf.
  --     `flagQuadraticForm_downward_nonneg`) gives
  --     `φ₀ ⟦kernelCombo²⟧₀ ≤ (w ⬝ᵥ Qs i *ᵥ w) · φ₀ ⟦flagQuadraticForm …⟧₀`
  --     (`downward_sub`/`downward_smul`, `PositiveHom.map_sub`/`map_smul`, `le_def`).
  -- (B) `relative_slackness_term` with `lam = 1` (`div_one`) bounds
  --     `φ₀ ⟦flagQuadraticForm …⟧₀ ≤ c - φ₀ h`; multiply by `w ⬝ᵥ Qs i *ᵥ w ≥ 0`
  --     (`(hQ i).dotProduct_mulVec_nonneg` + `star_trivial`).
  -- (A) pointwise comparison at every labelled positive homomorphism
  have hpoint : ∀ ψ : PositiveHom (σs i),
      ψ (kernelCombo (Qs i) (vs i) w * kernelCombo (Qs i) (vs i) w)
        ≤ (w ⬝ᵥ ((Qs i) *ᵥ w)) * ψ (flagQuadraticForm (Qs i) (vs i)) := by
    intro ψ
    have hkc : ψ (kernelCombo (Qs i) (vs i) w)
        = w ⬝ᵥ ((Qs i) *ᵥ (fun a => ψ (vs i a))) := by
      have h1 : ψ (kernelCombo (Qs i) (vs i) w)
          = ((Qs i) *ᵥ w) ⬝ᵥ (fun a => ψ (vs i a)) := by
        simp only [kernelCombo, PositiveHom.map_sum, PositiveHom.map_smul]
        rfl
      rw [h1, dotProduct_comm,
        isHermitian_dotProduct_mulVec_comm (hQ i).1]
    have hcs := posSemidef_dotProduct_mulVec_sq_le (hQ i) (fun a => ψ (vs i a)) w
    rw [← eval_flagQuadraticForm (Qs i) (vs i) ψ] at hcs
    calc ψ (kernelCombo (Qs i) (vs i) w * kernelCombo (Qs i) (vs i) w)
        = ψ (kernelCombo (Qs i) (vs i) w) ^ 2 := by
          rw [PositiveHom.map_mul, sq]
      _ = (w ⬝ᵥ ((Qs i) *ᵥ (fun a => ψ (vs i a)))) ^ 2 := by rw [hkc]
      _ ≤ (w ⬝ᵥ ((Qs i) *ᵥ w)) * ψ (flagQuadraticForm (Qs i) (vs i)) := hcs
  -- package as membership of the difference in the semantic cone and unlabel
  have hcone : ((w ⬝ᵥ ((Qs i) *ᵥ w)) • flagQuadraticForm (Qs i) (vs i)
      - kernelCombo (Qs i) (vs i) w * kernelCombo (Qs i) (vs i) w)
        ∈ semanticCone (σs i) := by
    intro ψ
    rw [PositiveHom.map_sub, PositiveHom.map_smul]
    have := hpoint ψ
    linarith
  have hdown : 0 ≤ φ₀ (⟦(w ⬝ᵥ ((Qs i) *ᵥ w)) • flagQuadraticForm (Qs i) (vs i)
      - kernelCombo (Qs i) (vs i) w * kernelCombo (Qs i) (vs i) w⟧₀ : FlagAlgebra ∅ₜ) :=
    downward_preserve_semanticCone _ hcone φ₀
  rw [downward_sub, downward_smul, PositiveHom.map_sub, PositiveHom.map_smul] at hdown
  -- (B) the certificate bounds the averaged quadratic form by the slack
  have hterm : φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ) ≤ c - φ₀ h := by
    have := relative_slackness_term (lam := fun _ => 1)
      (fs := fun j => flagQuadraticForm (Qs j) (vs j))
      (fun _ => one_pos)
      (fun j χ _ => eval_flagQuadraticForm_nonneg (hQ j) (vs j) _)
      hn (fun φ₀' hφ₀' => by simpa using hcert φ₀' hφ₀') hφ₀ i
    simpa using this
  have hwQw : 0 ≤ w ⬝ᵥ ((Qs i) *ᵥ w) := by
    have h := (hQ i).dotProduct_mulVec_nonneg w
    rwa [star_trivial] at h
  calc φ₀ (⟦kernelCombo (Qs i) (vs i) w * kernelCombo (Qs i) (vs i) w⟧₀ : FlagAlgebra ∅ₜ)
      ≤ (w ⬝ᵥ ((Qs i) *ᵥ w))
          * φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ) := by linarith
    _ ≤ (w ⬝ᵥ ((Qs i) *ᵥ w)) * (c - φ₀ h) :=
        mul_le_mul_of_nonneg_left hterm hwQw

/-- **Kernel slackness, exact slack** (`thm:kernel-slackness` (3), slack part): on the
equality slice the unlabelled slack vanishes. -/
theorem kernel_slackness_exact_slack
    (hQ : ∀ i, (Qs i).PosSemidef)
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hattain : φ₀ h = c) :
    φ₀ n = 0 := by
  -- Instance of `relative_slackness_exact_slack` (`lam := 1`, hf from
  -- `eval_flagQuadraticForm_nonneg`).
  exact relative_slackness_exact_slack (lam := fun _ => 1)
    (fs := fun i => flagQuadraticForm (Qs i) (vs i))
    (fun _ => one_pos)
    (fun i χ _ => eval_flagQuadraticForm_nonneg (hQ i) (vs i) _)
    hn (fun φ₀' hφ₀' => by simpa using hcert φ₀' hφ₀') hφ₀ hattain

/-- **Kernel slackness, almost-sure kernel membership** (`thm:kernel-slackness` (3)): on
the equality slice, for every type with positive density the labelled moment vector
falls into `ker Q` almost surely under the random extension. -/
theorem kernel_slackness_exact_ae
    (hQ : ∀ i, (Qs i).PosSemidef)
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Y) (hattain : φ₀ h = c) (i : Fin m)
    (hσi : φ₀ ⟨σs i⟩₀ > 0) :
    ∀ᵐ ψ ∂(ℙ[φ₀] : Measure (PositiveHomSpace (σs i))),
      (Qs i) *ᵥ (fun a => (PositiveHomSpace.toPosHom ψ) (vs i a)) = 0 := by
  -- `relative_slackness_exact_ae` (`lam := 1`) gives
  -- `ψ (flagQuadraticForm (Qs i) (vs i)) = 0` a.e.; rewrite by
  -- `eval_flagQuadraticForm` and finish each `ψ` with
  -- `posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero (hQ i)` (`filter_upwards`).
  have hae := relative_slackness_exact_ae (lam := fun _ => 1)
    (fs := fun j => flagQuadraticForm (Qs j) (vs j))
    (fun _ => one_pos)
    (fun j χ _ => eval_flagQuadraticForm_nonneg (hQ j) (vs j) _)
    hn (fun φ₀' hφ₀' => by simpa using hcert φ₀' hφ₀') hφ₀ hattain i hσi
  filter_upwards [hae] with ψ hψ
  simp only [eval_flagQuadraticForm] at hψ
  exact posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero (hQ i) hψ

/-- **Kernel slackness, global form** (`thm:kernel-slackness` (4)): if every `φ₀ ∈ Y`
attains the bound, the moment vector of EVERY point of the relative support lies in
`ker Q` — each row of `Q` yields a labelled equation valid on all of `S_σ(Y)`. -/
theorem kernel_slackness_global
    (hQ : ∀ i, (Qs i).PosSemidef)
    (hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → 0 ≤ φ₀ n)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y →
      φ₀ h + (∑ i, φ₀ (⟦flagQuadraticForm (Qs i) (vs i)⟧₀ : FlagAlgebra ∅ₜ)) + φ₀ n ≤ c)
    (hall : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Y → φ₀ h = c) (i : Fin m) :
    ∀ χ ∈ relSσ Y (σs i),
      (Qs i) *ᵥ (fun a => (PositiveHomSpace.toPosHom χ) (vs i a)) = 0 := by
  -- `relative_slackness_global` (`lam := 1`, hf from `eval_flagQuadraticForm_nonneg`)
  -- gives `χ (flagQuadraticForm (Qs i) (vs i)) = 0` on `relSσ Y (σs i)`; rewrite by
  -- `eval_flagQuadraticForm`, finish with
  -- `posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero (hQ i)`.
  intro χ hχ
  have hzero := relative_slackness_global (lam := fun _ => 1)
    (fs := fun j => flagQuadraticForm (Qs j) (vs j))
    (fun _ => one_pos)
    (fun j χ' _ => eval_flagQuadraticForm_nonneg (hQ j) (vs j) _)
    hn (fun φ₀' hφ₀' => by simpa using hcert φ₀' hφ₀') hall i χ hχ
  simp only [eval_flagQuadraticForm] at hzero
  exact posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero (hQ i) hzero

end Kernel

end FlagAlgebras.MetaTheory
