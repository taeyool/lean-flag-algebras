import LeanFlagAlgebras.MetaTheory.RelativeSlackness

/-! # Equality slices force certificate terms to vanish (paper §11.6,
`prop:equality-slice-vanishing`)

The generic mining principle: if a certificate
`h + ∑ λᵢ ⟦ℓᵢ²⟧₀ ≤ c·1₀` (`λᵢ > 0`) is proved on the whole constrained class `Q₀`, then on
the equality slice `Y = {φ₀ ∈ Q₀ : φ₀ h = c}` every linear certificate term vanishes
identically on the corresponding relative support: `ψ(ℓᵢ) = 0` for every
`ψ ∈ S_{σᵢ}(Y)`.

This is `thm:relative-slackness` (via `relative_slackness_global_sq`) with `fᵢ := ℓᵢ²` and
`n := 0`; hypothesis (i) is automatic for squares, and every `φ₀ ∈ Y` attains the bound by
the definition of the slice.
-/

open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ}

/-- The equality slice of a density expression `h` at level `c`, inside the constrained
space cut out by `forb0`. -/
def eqSlice (forb0 : FinFlag ∅ₜ → Prop) (h : FlagAlgebra ∅ₜ) (c : ℝ) :
    Set (PositiveHomSpace ∅ₜ) :=
  {χ | χ ∈ Qσ forb0 ∧ (PositiveHomSpace.toPosHom χ) h = c}

/-- Membership of a base limit in an equality slice, unfolded. -/
lemma posHomPoint_mem_eqSlice {forb0 : FinFlag ∅ₜ → Prop} {h : FlagAlgebra ∅ₜ} {c : ℝ}
    {φ₀ : PositiveHom ∅ₜ} :
    posHomPoint φ₀ ∈ eqSlice forb0 h c ↔ posHomPoint φ₀ ∈ Qσ forb0 ∧ φ₀ h = c := by
  -- Unfold; the evaluation glue is `toPosHom_posHomPoint`.
  simp only [eqSlice, Set.mem_setOf_eq, toPosHom_posHomPoint]

/-- **Equality slices force certificate terms to vanish**
(`prop:equality-slice-vanishing`): a certificate `h + ∑ λᵢ ⟦ℓᵢ²⟧₀ ≤ c·1₀` on `Q₀` makes
every linear term `ℓᵢ` vanish identically on the relative support `S_{σᵢ}(Y)` of the
equality slice `Y = eqSlice forb0 h c`. -/
theorem equality_slice_vanishing (forb0 : FinFlag ∅ₜ → Prop)
    {m : ℕ} {k : Fin m → ℕ} {σs : ∀ i, FlagType (Fin (k i))}
    (ls : ∀ i, FlagAlgebra (σs i)) (lam : Fin m → ℝ) (hlam : ∀ i, 0 < lam i)
    (h : FlagAlgebra ∅ₜ) (c : ℝ)
    (hcert : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ forb0 →
      φ₀ h + (∑ i, lam i * φ₀ (⟦ls i * ls i⟧₀ : FlagAlgebra ∅ₜ)) ≤ c)
    (i : Fin m) :
    ∀ χ ∈ relSσ (eqSlice forb0 h c) (σs i),
      (PositiveHomSpace.toPosHom χ) (ls i) = 0 := by
  -- Instance of `relative_slackness_global_sq` with `Y := eqSlice forb0 h c`,
  -- `fs j := ls j * ls j`, `n := (0 : FlagAlgebra ∅ₜ)`:
  -- * `hf`: squares evaluate non-negatively at EVERY hom (`PositiveHom.map_mul`,
  --   `mul_self_nonneg`), a fortiori on the relative supports;
  -- * `hn`: `φ₀ 0 = 0` (`map_zero`);
  -- * `hcert`: the given bound restricted along `eqSlice ⊆ Qσ` (use
  --   `posHomPoint_mem_eqSlice`), with the `φ₀ 0` term rewritten away (`add_zero`);
  -- * `hall`: every slice member attains `φ₀ h = c` (`posHomPoint_mem_eqSlice`);
  -- * `hfi : fs i = ls i * ls i` is `rfl`.
  have hf : ∀ j, ∀ χ ∈ relSσ (eqSlice forb0 h c) (σs j),
      0 ≤ (PositiveHomSpace.toPosHom χ) (ls j * ls j) := by
    intro j χ _
    rw [PositiveHom.map_mul]
    exact mul_self_nonneg _
  have hn : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ eqSlice forb0 h c →
      0 ≤ φ₀ (0 : FlagAlgebra ∅ₜ) :=
    fun φ₀ _ => (PositiveHom.map_zero φ₀).ge
  have hcert' : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ eqSlice forb0 h c →
      φ₀ h + (∑ j, lam j * φ₀ (⟦ls j * ls j⟧₀ : FlagAlgebra ∅ₜ))
        + φ₀ (0 : FlagAlgebra ∅ₜ) ≤ c := by
    intro φ₀ hφ₀
    rw [PositiveHom.map_zero, add_zero]
    exact hcert φ₀ ((posHomPoint_mem_eqSlice.mp hφ₀).1)
  have hall : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ eqSlice forb0 h c → φ₀ h = c :=
    fun φ₀ hφ₀ => (posHomPoint_mem_eqSlice.mp hφ₀).2
  exact relative_slackness_global_sq (fs := fun j => ls j * ls j) hlam hf hn hcert' hall
    i rfl

end FlagAlgebras.MetaTheory
