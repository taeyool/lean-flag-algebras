import LeanFlagAlgebras.Forbid.Basic

open FlagAlgebras Forbid
open SimpleGraph Matrix
open Lean Elab Command

namespace FlagAlgebras.API

noncomputable def one_expand
    (F_forbid : FinFlag ∅ₜ) (expandSize : ℕ)
    : FlagAlgebra ∅ₜ :=
  ∑ F' : FlagWithSize ∅ₜ expandSize with flagDensity₁ F_forbid.2 (unlabel F') = 0,
    (flagDensity₁ ((⟨0, default⟩ : FinFlag ∅ₜ).2) F' : ℝ) • ⟦unitVector ⟨expandSize, F'⟩⟧

theorem one_forbidEq_expand
    (F_forbid : FinFlag ∅ₜ) (expandSize : ℕ)
    : (1 : FlagAlgebra ∅ₜ) =[F_forbid] one_expand F_forbid expandSize := by
  simpa [one_expand] using
    (unitVector_quot_forbidEq_sum (σ := ∅ₜ) F_forbid (⟨0, default⟩ : FinFlag ∅ₜ) expandSize (by simp))

lemma forbidLE_trans_add_nonneg
    {F_forbid : FinFlag ∅ₜ} {f g c : FlagAlgebra ∅ₜ}
    (hfg : f ≤[F_forbid] g) (hc : 0 ≤[F_forbid] c)
    : f ≤[F_forbid] (g + c) := by
  rw [← add_zero f]
  exact forbidLE_add hfg hc

theorem flagQuadraticForm_downward_forbidLE_nonneg
    {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    (F_forbid : FinFlag ∅ₜ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : 0 ≤[F_forbid] ⟦flagQuadraticForm M v⟧₀
  := by
  apply downward_forbidLE_nonneg
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg M hM v

theorem forbidLE_add_QuadraticForm
    {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (v : FlagAlgebraVec σ n)
    : (f ≤[F_forbid] g) → f ≤[F_forbid] g + ⟦flagQuadraticForm M v⟧₀
  := by
  intro hfg
  rw [← add_zero f]
  apply forbidLE_add hfg
  apply downward_forbidLE_nonneg
  apply forbidLE_of_le
  exact flagQuadraticForm_nonneg M hM v

/-
Generates a batch of `simp` lemmas of the form

  ⟦unitVector ⟨n, Flag_n_0_0_i⟩⟧ = FlagAlgebra_n_0_0_i

for `i = 0, 1, ..., count - 1`.  The names follow the convention
`unitVector_FlagAlgebra_<n>_0_0_<i>`.

Example:

  generate_unitVector_lemmas 5 34
  -- creates `unitVector_FlagAlgebra_5_0_0_0`, ..., `unitVector_FlagAlgebra_5_0_0_33`
-/

syntax (name := generateUnitVectorLemmasCmd)
  "generate_unitVector_lemmas" num num : command

private def generateUnitVectorLemmas (n count : Nat) : CommandElabM Unit := do
  for idx in [:count] do
    let lemmaName := mkIdent (Name.mkSimple s!"unitVector_FlagAlgebra_{n}_0_0_{idx}")
    let flagName := mkIdent (Name.mkSimple s!"Flag_{n}_0_0_{idx}")
    let algebraName := mkIdent (Name.mkSimple s!"FlagAlgebra_{n}_0_0_{idx}")
    elabCommand (← `(
      @[simp]
      theorem $lemmaName
          : ⟦unitVector ⟨$(Syntax.mkNumLit (toString n)), $flagName⟩⟧ = $algebraName := Quotient.out_inj.mp rfl
    ))

elab_rules : command
  | `(command| generate_unitVector_lemmas $n:num $count:num) => do
      generateUnitVectorLemmas n.getNat count.getNat

end FlagAlgebras.API
