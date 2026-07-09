import LeanFlagAlgebras.MetaTheory.CertificateSliceVanishing
import LeanFlagAlgebras.MetaTheory.GraphClassConstraint
import LeanFlagAlgebras.Automation.CompleteGraphFreeP4
import LeanFlagAlgebras.Automation.K4freeP4

/-! # The parametric `K_{r+1}`-free `P₄` equality slice (paper §11.6,
`thm:parametric-p4-equality-slice`; the `r = 3` instance is
`thm:k4free-p4-equality-slice`)

The verified parametric certificate `CompleteGraphFreeP4.gap_identity`
(`P4_density + p₁·f₁ + p₂·f₂ + p₃·f₃ + p₀·f₀ + leftover = 12((r-1)/r)³·1₀`) is consumed
through the relative-slackness machinery on the extremal slice

  `Y_r = {φ₀ ∈ Q₀^{(r)} : φ₀(P4_density) = 12((r-1)/r)³}`,

yielding the mined labelled equations on the relative supports at the generated non-edge
type `FlagType_2_0` (= `η`) and edge type `FlagType_2_1` (= `τ`):

* `(r-1)·z_η = g_η` on `S_η(Y_r)` (`parametricP4_eta_equation`);
* `a_τ = b_τ` and `(r-2)·(a_τ + b_τ) = 2·g_τ` on `S_τ(Y_r)`
  (`parametricP4_tau_symm`, `parametricP4_tau_equation`);
* every `φ₀ ∈ Y_r` has extremal `K₄` density `(r-1)(r-2)(r-3)/r³`
  (`parametricP4_K4_density`).

**The Zykov input is a hypothesis, not an axiom.**  The non-negativity of the `κ₄` term
`f₀ r` on the class is Zykov's classical `K₄`-density bound; the `Automation` layer records
it as `axiom Zykov_K4_density_bound`, but — following this development's practice for
classical inputs (cf. `cor:degenerate-family`) — the theorems below take the bound as an
explicit hypothesis `hZykov`, keeping `MetaTheory` on the standard axioms.  At `r = 3` the
`κ₄` coefficient `(r-1)(r-2)(r-3)/r³` vanishes and `f₀ 3 = 0•1₀ - K₄`, so the `r = 3`
theorems (`k4freeP4_*` below) need **no Zykov input at all** — the slice equations of
`thm:k4free-p4-equality-slice` are unconditional.

The `r = 3` slice is stated, as in the paper, with the `API.K4freeP4` density expression
(`K4freeP4.P4_density`, the four-atom form omitting the `K₄` atom); on the `K₄`-free class
the two expressions agree (`P4_density_eval_eq_of_K4free`).
-/

open scoped Topology
open CompleteGraphFreeP4 SimpleGraph Forbid

namespace FlagAlgebras.MetaTheory

/-! ## The class and the atom-vanishing bridge -/

/-- The forbidden-graph predicate of the `K_{r+1}`-free class at the empty type. -/
noncomputable abbrev krFreeForb0 (r : ℕ) : FinFlag ∅ₜ → Prop :=
  (constraintOf (cliqueFreeClass (r + 1)) ∅ₜ).forb0

/-- A constrained limit of the `K_{r+1}`-free class kills the `K_{r+1}` basis flag
(the single-forbidden-flag form consumed by the `Automation` certificates). -/
lemma krFree_completeGraph_flag_eq_zero {r : ℕ} {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r)) :
    φ₀ (⟦basisVector (completeGraph (Fin (r + 1))).toFinFlag⟧ : FlagAlgebra ∅ₜ) = 0 := by
  -- The flag `(completeGraph (Fin (r+1))).toFinFlag` is forbidden: its underlying graph
  -- is `completeGraph (Fin (r+1)) = ⊤`, which is not `CliqueFree (r+1)` (the membership
  -- predicate of `cliqueFreeClass (r+1)` is definitionally exposed on the flag);
  -- `mem_Qσ_iff` + `posHomPoint_val_apply` then kill its density.
  have hforb : krFreeForb0 r ((completeGraph (Fin (r + 1))).toFinFlag) := fun hmem =>
    SimpleGraph.not_cliqueFree_of_top_embedding
      (SimpleGraph.Embedding.refl
        : (⊤ : SimpleGraph (Fin (r + 1))) ↪g (⊤ : SimpleGraph (Fin (r + 1)))) hmem
  have hmem := (mem_Qσ_iff (krFreeForb0 r) (posHomPoint φ₀)).mp hφ₀
    ((completeGraph (Fin (r + 1))).toFinFlag) hforb
  rwa [posHomPoint_val_apply] at hmem

/-- A constrained limit of the `K₄`-free class (`r = 3`) kills the `K₄` atom
`FlagAlgebra_4_0_0_10`.  (Stated at `r = 3` only: for `r ≥ 4` the class forbids
`K_{r+1}`, not `K₄`, and the corresponding statement is false; every downstream use
is at `r = 3`.) -/
lemma k4free_K4_atom_eq_zero {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 3)) :
    φ₀ FlagAlgebra_4_0_0_10 = 0 := by
  -- `K4freeP4.K4_toFinFlag_eq` identifies the atom's flag with
  -- `(completeGraph (Fin 4)).toFinFlag`; then `krFree_completeGraph_flag_eq_zero` at `r = 3`.
  have h := krFree_completeGraph_flag_eq_zero (r := 3) hφ₀
  rw [show (completeGraph (Fin (3 + 1))).toFinFlag
      = (⟨4, CompleteGraphFreeP4.Flag_4_0_0_10⟩ : FinFlag ∅ₜ) from K4freeP4.K4_toFinFlag_eq]
    at h
  exact h

/-! ## The parametric slice and its mined equations -/

/-- The parametric extremal slice `Y_r` (paper `thm:parametric-p4-equality-slice`). -/
noncomputable def parametricP4Slice (r : ℕ) : Set (PositiveHomSpace ∅ₜ) :=
  eqSlice (krFreeForb0 r) CompleteGraphFreeP4.P4_density (12 * (((r : ℝ) - 1) / r) ^ 3)

/-! ### Private helpers: evaluation positivity and strict multiplier positivity -/

/-- Evaluating a semantic-cone element at any positive homomorphism is non-negative. -/
private lemma eval_nonneg_of_nonneg {x : FlagAlgebra ∅ₜ} (hx : 0 ≤ x)
    (φ : PositiveHom ∅ₜ) : 0 ≤ φ x := by
  rw [le_def, sub_zero] at hx
  exact hx φ

/-- Strict positivity of `p₁` for `r ≥ 3` (the API exports only `p₁_nonneg`). -/
private lemma p₁_pos (r : ℕ) (hr : 3 ≤ r) : 0 < p₁ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₁
  apply div_pos
  · nlinarith
  · nlinarith

/-- Strict positivity of `p₂` for `r ≥ 3`. -/
private lemma p₂_pos (r : ℕ) (hr : 3 ≤ r) : 0 < p₂ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₂
  apply div_pos
  · nlinarith [sq_nonneg ((r : ℝ) - 3)]
  · linarith

/-- Strict positivity of `p₃` for `r ≥ 3`. -/
private lemma p₃_pos (r : ℕ) (hr : 3 ≤ r) : 0 < p₃ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₃
  apply div_pos
  · nlinarith [sq_nonneg ((r : ℝ) - 3)]
  · nlinarith

/-- Strict positivity of `p₀` for `r ≥ 3`. -/
private lemma p₀_pos (r : ℕ) (hr : 3 ≤ r) : 0 < p₀ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₀
  apply div_pos
  · nlinarith
  · linarith

/-- The Zykov hypothesis makes the `κ₄` correction term non-negative on the class:
unfolding `f₀`, `φ₀ (p₀ r • f₀ r) = p₀ r · ((r³-6r²+11r-6)/r³ - φ₀(K₄)) ≥ 0`. -/
private lemma zykov_term_nonneg (r : ℕ) (hr : 3 ≤ r)
    (hZykov : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3)
    {φ₀ : PositiveHom ∅ₜ} (hQ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r)) :
    0 ≤ φ₀ (p₀ r • f₀ r) := by
  rw [PositiveHom.map_smul]
  refine mul_nonneg (p₀_nonneg r hr) ?_
  rw [f₀, PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one, mul_one]
  have := hZykov φ₀ hQ
  linarith

section Parametric

variable {r : ℕ} (hr : 3 ≤ r)
  (hZykov : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
    φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3)

include hr in
/-- The certificate hypothesis in un-summed slackness form, extracted from
`CompleteGraphFreeP4.gap_identity`: for every constrained limit,
`φ₀(P4) + p₁·φ₀⟦l₁²⟧₀ + p₂·φ₀⟦l₂²⟧₀ + p₃·φ₀⟦l₃²⟧₀ + φ₀(p₀•f₀ + leftover) = 12((r-1)/r)³`,
hence `≤`. -/
lemma parametricP4_cert (φ₀ : PositiveHom ∅ₜ) (_hφ₀ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r)) :
    φ₀ CompleteGraphFreeP4.P4_density
      + (p₁ r * φ₀ (f₁ r) + p₂ r * φ₀ f₂ + p₃ r * φ₀ (f₃ r))
      + φ₀ (p₀ r • f₀ r + leftover r)
      = 12 * (((r : ℝ) - 1) / r) ^ 3 := by
  -- Apply `φ₀` to `gap_identity r hr` and push through `PositiveHom.map_add`/`map_smul`/
  -- `map_one` (`φ₀ (c • 1) = c`).  Pure evaluation algebra.
  have h := congrArg (fun x => φ₀ x) (gap_identity r hr)
  simp only [PositiveHom.map_add, PositiveHom.map_smul, PositiveHom.map_one, mul_one] at h
  rw [PositiveHom.map_add, PositiveHom.map_smul]
  linarith

include hr hZykov in
/-- The full certificate bound `φ₀(P4) + λᵢ·φ₀⟦lᵢ²⟧₀ ≤ 12((r-1)/r)³` on the class, for
a single square term: all other certificate terms are dropped, each being non-negative
on `Q₀` (`hZykov` + `leftover_nonneg` for the unlabelled slack, squares for the rest). -/
private lemma parametricP4_single_bound (φ₀ : PositiveHom ∅ₜ)
    (hQ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r)) :
    φ₀ CompleteGraphFreeP4.P4_density + p₁ r * φ₀ (f₁ r) ≤ 12 * (((r : ℝ) - 1) / r) ^ 3
    ∧ φ₀ CompleteGraphFreeP4.P4_density + p₂ r * φ₀ f₂ ≤ 12 * (((r : ℝ) - 1) / r) ^ 3
    ∧ φ₀ CompleteGraphFreeP4.P4_density + p₃ r * φ₀ (f₃ r)
        ≤ 12 * (((r : ℝ) - 1) / r) ^ 3 := by
  have hc := parametricP4_cert hr φ₀ hQ
  have h1 : 0 ≤ p₁ r * φ₀ (f₁ r) :=
    mul_nonneg (p₁_nonneg r hr) (eval_nonneg_of_nonneg (f₁_nonneg r) φ₀)
  have h2 : 0 ≤ p₂ r * φ₀ f₂ :=
    mul_nonneg (p₂_nonneg r hr) (eval_nonneg_of_nonneg f₂_nonneg φ₀)
  have h3 : 0 ≤ p₃ r * φ₀ (f₃ r) :=
    mul_nonneg (p₃_nonneg r hr) (eval_nonneg_of_nonneg (f₃_nonneg r) φ₀)
  have h0 : 0 ≤ φ₀ (p₀ r • f₀ r + leftover r) := by
    rw [PositiveHom.map_add]
    exact add_nonneg (zykov_term_nonneg r hr hZykov hQ)
      (eval_nonneg_of_nonneg (leftover_nonneg r hr) φ₀)
  exact ⟨by linarith, by linarith, by linarith⟩

include hr hZykov in
/-- **Near equality controls the squares** (`prop:k4free-p4-certificate-stability` and
`thm:parametric-quant-stability` (i), hom level): writing
`Δ = 12((r-1)/r)³ − φ₀(π_{P4}^{(r)})`, each weighted certificate square is at most `Δ`:
`p₁(r)·φ₀⟦l_η²⟧₀ ≤ Δ`, `p₂(r)·φ₀⟦l_τ⁻²⟧₀ ≤ Δ`, `p₃(r)·φ₀⟦l_τ⁺²⟧₀ ≤ Δ`.
(The paper's kernel-level `R_η(W)/R_τ^±(W)` forms follow through the graphon
representation dictionary — the standing unformalised bridge; at `r = 3`, dividing by the
coefficients gives the `9/8, 1/5, 9/35` pattern of
`prop:k4free-p4-certificate-stability`.) -/
theorem parametricP4_sq_bounds (φ₀ : PositiveHom ∅ₜ)
    (hQ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r)) :
    p₁ r * φ₀ (f₁ r)
        ≤ 12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density
    ∧ p₂ r * φ₀ f₂
        ≤ 12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density
    ∧ p₃ r * φ₀ (f₃ r)
        ≤ 12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density := by
  obtain ⟨h1, h2, h3⟩ := parametricP4_single_bound hr hZykov φ₀ hQ
  exact ⟨by linarith, by linarith, by linarith⟩

include hr in
/-- **The `K₄` density is nearly extremal** (`thm:parametric-quant-stability` (ii), hom
level): `φ₀(K₄) ≥ (r-1)(r-2)(r-3)/r³ − Δ/p₀(r)` with `Δ = 12((r-1)/r)³ − φ₀(π)`.
Notably this needs NO Zykov input — only the certificate squares and the leftover are
dropped, and those are unconditionally non-negative.  (On the equality slice, where
`Δ = 0`, this is the `≥` half of `parametricP4_K4_density`.) -/
theorem parametricP4_K4_density_approx (φ₀ : PositiveHom ∅ₜ)
    (hQ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r)) :
    ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3
        - (12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density) / p₀ r
      ≤ φ₀ FlagAlgebra_4_0_0_10 := by
  have hc := parametricP4_cert hr φ₀ hQ
  have h1 : 0 ≤ p₁ r * φ₀ (f₁ r) :=
    mul_nonneg (p₁_nonneg r hr) (eval_nonneg_of_nonneg (f₁_nonneg r) φ₀)
  have h2 : 0 ≤ p₂ r * φ₀ f₂ :=
    mul_nonneg (p₂_nonneg r hr) (eval_nonneg_of_nonneg f₂_nonneg φ₀)
  have h3 : 0 ≤ p₃ r * φ₀ (f₃ r) :=
    mul_nonneg (p₃_nonneg r hr) (eval_nonneg_of_nonneg (f₃_nonneg r) φ₀)
  have hL : 0 ≤ φ₀ (leftover r) := eval_nonneg_of_nonneg (leftover_nonneg r hr) φ₀
  have hp₀ := p₀_pos r hr
  -- unfold the folded slack term
  have hf₀ : φ₀ (f₀ r)
      = ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3
          - φ₀ FlagAlgebra_4_0_0_10 := by
    rw [f₀, PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one, mul_one]
  have hsplit : φ₀ (p₀ r • f₀ r + leftover r)
      = p₀ r * φ₀ (f₀ r) + φ₀ (leftover r) := by
    rw [PositiveHom.map_add, PositiveHom.map_smul]
  -- the certificate bounds the Zykov term linearly in `Δ`
  have hbound : p₀ r * φ₀ (f₀ r)
      ≤ 12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density := by
    rw [hsplit] at hc
    linarith
  -- the cubic factorisation `(r³-6r²+11r-6) = (r-1)(r-2)(r-3)`
  have hfact : ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3
      = ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 := by
    congr 1
    ring
  rw [hf₀, hfact] at hbound
  -- divide by `p₀ r > 0` and rearrange
  have hdiv : ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3
      - φ₀ FlagAlgebra_4_0_0_10
      ≤ (12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density) / p₀ r := by
    rw [le_div_iff₀ hp₀, mul_comm]
    exact hbound
  linarith

include hr hZykov in
/-- **The mined `η`-equation** (`thm:parametric-p4-equality-slice`): on
`S_η(Y_r)` (with `η = FlagType_2_0`, the ordered non-edge type),
`(r-1)·z_η = g_η` — in evaluation form for the generated flags
`z_η = FlagAlgebra_3_2_0_0`, `g_η = FlagAlgebra_3_2_0_3`. -/
theorem parametricP4_eta_equation :
    ∀ χ ∈ relSσ (parametricP4Slice r) FlagType_2_0,
      ((r : ℝ) - 1) * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0
        = (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 := by
  -- `equality_slice_vanishing` (a `relative_slackness_global_sq` instance) with the
  -- single square `f₁ r = ⟦l₁²⟧₀`, the remaining certificate terms dropped on `Q₀` via
  -- `parametricP4_single_bound`.
  have hsq : f₁ r
      = ⟦(((r : ℝ) - 1) • FlagAlgebra_3_2_0_0 - (1 : ℝ) • FlagAlgebra_3_2_0_3)
          * (((r : ℝ) - 1) • FlagAlgebra_3_2_0_0 - (1 : ℝ) • FlagAlgebra_3_2_0_3)⟧₀ := by
    rw [f₁, pow_two]
  have key := equality_slice_vanishing (krFreeForb0 r)
    (fun _ : Fin 1 => ((r : ℝ) - 1) • FlagAlgebra_3_2_0_0 - (1 : ℝ) • FlagAlgebra_3_2_0_3)
    (fun _ => p₁ r) (fun _ => p₁_pos r hr) CompleteGraphFreeP4.P4_density
    (12 * (((r : ℝ) - 1) / r) ^ 3)
    (fun φ₀ hQ => by
      simp only [Fin.sum_univ_one]
      rw [← hsq]
      exact (parametricP4_single_bound hr hZykov φ₀ hQ).1) 0
  intro χ hχ
  have h := key χ hχ
  simp only [PositiveHom.map_sub, PositiveHom.map_smul, one_mul] at h
  linarith

include hr hZykov in
/-- **The mined `τ`-symmetry** (`thm:parametric-p4-equality-slice`): on `S_τ(Y_r)`,
`a_τ = b_τ` (with `a_τ = FlagAlgebra_3_2_1_1`, `b_τ = FlagAlgebra_3_2_1_2`). -/
theorem parametricP4_tau_symm :
    ∀ χ ∈ relSσ (parametricP4Slice r) FlagType_2_1,
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1
        = (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2 := by
  -- Same slackness instance with the square `f₂ = ⟦l₂²⟧₀`.
  have hsq : f₂
      = ⟦((1 : ℝ) • FlagAlgebra_3_2_1_1 - (1 : ℝ) • FlagAlgebra_3_2_1_2)
          * ((1 : ℝ) • FlagAlgebra_3_2_1_1 - (1 : ℝ) • FlagAlgebra_3_2_1_2)⟧₀ := by
    rw [f₂, pow_two]
  have key := equality_slice_vanishing (krFreeForb0 r)
    (fun _ : Fin 1 => (1 : ℝ) • FlagAlgebra_3_2_1_1 - (1 : ℝ) • FlagAlgebra_3_2_1_2)
    (fun _ => p₂ r) (fun _ => p₂_pos r hr) CompleteGraphFreeP4.P4_density
    (12 * (((r : ℝ) - 1) / r) ^ 3)
    (fun φ₀ hQ => by
      simp only [Fin.sum_univ_one]
      rw [← hsq]
      exact (parametricP4_single_bound hr hZykov φ₀ hQ).2.1) 0
  intro χ hχ
  have h := key χ hχ
  simp only [PositiveHom.map_sub, PositiveHom.map_smul, one_mul] at h
  linarith

include hr hZykov in
/-- **The mined `τ`-equation** (`thm:parametric-p4-equality-slice`): on `S_τ(Y_r)`,
`(r-2)·(a_τ + b_τ) = 2·g_τ` (with `g_τ = FlagAlgebra_3_2_1_3`). -/
theorem parametricP4_tau_equation :
    ∀ χ ∈ relSσ (parametricP4Slice r) FlagType_2_1,
      ((r : ℝ) - 2) * ((PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1
          + (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2)
        = 2 * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 := by
  -- Same slackness instance with the square `f₃ r = ⟦l₃²⟧₀`.
  have hsq : f₃ r
      = ⟦(((r : ℝ) - 2) • FlagAlgebra_3_2_1_1 + ((r : ℝ) - 2) • FlagAlgebra_3_2_1_2
            - (2 : ℝ) • FlagAlgebra_3_2_1_3)
          * (((r : ℝ) - 2) • FlagAlgebra_3_2_1_1 + ((r : ℝ) - 2) • FlagAlgebra_3_2_1_2
            - (2 : ℝ) • FlagAlgebra_3_2_1_3)⟧₀ := by
    rw [f₃, pow_two]
  have key := equality_slice_vanishing (krFreeForb0 r)
    (fun _ : Fin 1 => ((r : ℝ) - 2) • FlagAlgebra_3_2_1_1
      + ((r : ℝ) - 2) • FlagAlgebra_3_2_1_2 - (2 : ℝ) • FlagAlgebra_3_2_1_3)
    (fun _ => p₃ r) (fun _ => p₃_pos r hr) CompleteGraphFreeP4.P4_density
    (12 * (((r : ℝ) - 1) / r) ^ 3)
    (fun φ₀ hQ => by
      simp only [Fin.sum_univ_one]
      rw [← hsq]
      exact (parametricP4_single_bound hr hZykov φ₀ hQ).2.2) 0
  intro χ hχ
  have h := key χ hχ
  simp only [PositiveHom.map_sub, PositiveHom.map_add, PositiveHom.map_smul] at h
  rw [mul_add]
  linarith

include hr hZykov in
/-- **Extremal `K₄` density on the slice** (`thm:parametric-p4-equality-slice`, final
clause): every `φ₀ ∈ Y_r` has `φ₀(K₄) = (r-1)(r-2)(r-3)/r³`. -/
theorem parametricP4_K4_density {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ parametricP4Slice r) :
    φ₀ FlagAlgebra_4_0_0_10 = ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 := by
  -- Exact slackness on the slice: attainment kills the sum of the non-negative
  -- certificate terms, so `φ₀ (p₀ r • f₀ r) = 0`; `p₀ r > 0` gives `φ₀ (f₀ r) = 0`,
  -- i.e. `φ₀ K₄ = (r³-6r²+11r-6)/r³ = (r-1)(r-2)(r-3)/r³` (`field_simp`/`ring`).
  obtain ⟨hQ, hattain⟩ := posHomPoint_mem_eqSlice.mp hφ₀
  have hc := parametricP4_cert hr φ₀ hQ
  have h1 : 0 ≤ p₁ r * φ₀ (f₁ r) :=
    mul_nonneg (p₁_nonneg r hr) (eval_nonneg_of_nonneg (f₁_nonneg r) φ₀)
  have h2 : 0 ≤ p₂ r * φ₀ f₂ :=
    mul_nonneg (p₂_nonneg r hr) (eval_nonneg_of_nonneg f₂_nonneg φ₀)
  have h3 : 0 ≤ p₃ r * φ₀ (f₃ r) :=
    mul_nonneg (p₃_nonneg r hr) (eval_nonneg_of_nonneg (f₃_nonneg r) φ₀)
  have h0 := zykov_term_nonneg r hr hZykov hQ
  have hleft := eval_nonneg_of_nonneg (leftover_nonneg r hr) φ₀
  rw [PositiveHom.map_add] at hc
  have hzero : φ₀ (p₀ r • f₀ r) = 0 := by linarith
  rw [PositiveHom.map_smul] at hzero
  have hf₀ : φ₀ (f₀ r) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (p₀_pos r hr))
  rw [f₀, PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one, mul_one] at hf₀
  have hr0 : (r : ℝ) ≠ 0 := by
    have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hval : φ₀ FlagAlgebra_4_0_0_10
      = ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3 := by linarith
  rw [hval]
  field_simp
  ring

end Parametric

/-! ## The `r = 3` instance: `thm:k4free-p4-equality-slice` (unconditional) -/

/-- The `K₄`-free `P₄` extremal slice `Y_{P₄}`, stated as in the paper with the
`API.K4freeP4` density expression (`K4freeP4.P4_density`, the four-atom form). -/
noncomputable def k4freeP4Slice : Set (PositiveHomSpace ∅ₜ) :=
  eqSlice (krFreeForb0 3) K4freeP4.P4_density (32 / 9)

/-- At `r = 3` the Zykov bound reads `φ₀(K₄) ≤ 0/27 = 0`, which holds with equality by
the atom-vanishing lemma — so the `r = 3` instances need no classical input. -/
private lemma zykov_at_three :
    ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 3) →
      φ₀ FlagAlgebra_4_0_0_10
        ≤ (((3 : ℕ) : ℝ) ^ 3 - 6 * ((3 : ℕ) : ℝ) ^ 2 + 11 * ((3 : ℕ) : ℝ) - 6)
            / ((3 : ℕ) : ℝ) ^ 3 := by
  intro φ₀ hQ
  rw [k4free_K4_atom_eq_zero hQ]
  norm_num

/-- On the `K₄`-free class the parametric and `K4freeP4` `P₄`-density expressions agree
(they differ by `12•K₄`, which vanishes), so the two slice descriptions coincide. -/
lemma k4freeP4Slice_eq_parametric : k4freeP4Slice = parametricP4Slice 3 := by
  -- On `Qσ (krFreeForb0 3)`: `φ₀ CGF.P4_density = φ₀ K4freeP4.P4_density + 12·φ₀ K₄`,
  -- the atom vanishing by `k4free_K4_atom_eq_zero`; and `12·((3-1)/3)³ = 32/9`.
  have hsplit : CompleteGraphFreeP4.P4_density
      = K4freeP4.P4_density + 12 • CompleteGraphFreeP4.FlagAlgebra_4_0_0_10 := rfl
  ext χ
  simp only [k4freeP4Slice, parametricP4Slice, eqSlice, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hQ, hval⟩
    refine ⟨hQ, ?_⟩
    have hatom : (PositiveHomSpace.toPosHom χ) FlagAlgebra_4_0_0_10 = 0 := by
      apply k4free_K4_atom_eq_zero
      rw [posHomPoint_toPosHom]
      exact hQ
    rw [hsplit, PositiveHom.map_add, hval, ← Nat.cast_smul_eq_nsmul ℝ,
      PositiveHom.map_smul, hatom]
    norm_num
  · rintro ⟨hQ, hval⟩
    refine ⟨hQ, ?_⟩
    have hatom : (PositiveHomSpace.toPosHom χ) FlagAlgebra_4_0_0_10 = 0 := by
      apply k4free_K4_atom_eq_zero
      rw [posHomPoint_toPosHom]
      exact hQ
    rw [hsplit, PositiveHom.map_add, ← Nat.cast_smul_eq_nsmul ℝ,
      PositiveHom.map_smul, hatom] at hval
    norm_num at hval
    exact hval

/-- **The `K₄`-free `P₄` equality slice, `η`-equation** (`thm:k4free-p4-equality-slice`):
`2·z_η = g_η` on `S_η(Y_{P₄})` — unconditional (no Zykov input at `r = 3`). -/
theorem k4freeP4_eta_equation :
    ∀ χ ∈ relSσ k4freeP4Slice FlagType_2_0,
      2 * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0
        = (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 := by
  intro χ hχ
  rw [k4freeP4Slice_eq_parametric] at hχ
  have h := parametricP4_eta_equation (r := 3) (by norm_num) zykov_at_three χ hχ
  norm_num at h
  exact h

/-- **The `K₄`-free `P₄` equality slice, `τ`-symmetry**: `a_τ = b_τ` on `S_τ(Y_{P₄})`. -/
theorem k4freeP4_tau_symm :
    ∀ χ ∈ relSσ k4freeP4Slice FlagType_2_1,
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1
        = (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2 := by
  intro χ hχ
  rw [k4freeP4Slice_eq_parametric] at hχ
  exact parametricP4_tau_symm (r := 3) (by norm_num) zykov_at_three χ hχ

/-- **The `K₄`-free `P₄` equality slice, `τ`-equation**: `a_τ + b_τ = 2·g_τ` on
`S_τ(Y_{P₄})`. -/
theorem k4freeP4_tau_equation :
    ∀ χ ∈ relSσ k4freeP4Slice FlagType_2_1,
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1
          + (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2
        = 2 * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 := by
  -- `parametricP4_tau_equation` at `r = 3`: `(3-2)·(a+b) = 2g` with `(3:ℝ)-2 = 1`.
  intro χ hχ
  rw [k4freeP4Slice_eq_parametric] at hχ
  have h := parametricP4_tau_equation (r := 3) (by norm_num) zykov_at_three χ hχ
  norm_num at h
  linarith

end FlagAlgebras.MetaTheory
