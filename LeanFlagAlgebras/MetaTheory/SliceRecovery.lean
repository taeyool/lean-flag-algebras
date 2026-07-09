import LeanFlagAlgebras.MetaTheory.ParametricP4Slice

/-! # Recovery of the extremiser and qualitative stability (paper §11.7,
`cor:parametric-p4-turan-recovery`, `cor:k4free-p4-qualitative-stability`,
`cor:parametric-qualitative-stability`)

The certificate slices collapse to a single point once a classical equality case
identifies the extremiser, and a singleton slice upgrades to qualitative stability by
compactness (`unique_slice_stability`, §11.3).

Classical inputs are explicit hypotheses (this development's standing practice):

* `hZykov` — Zykov's `K₄`-density bound on the `K_{r+1}`-free class (as in
  `ParametricP4Slice`);
* `hZykEq` — the **equality case** of Zykov's theorem: a constrained limit attaining the
  extremal `K₄` density is THE balanced `r`-partite limit (`cor:parametric-p4-turan-recovery`
  assumes exactly this);
* `huniq` — at `r = 3`, the singleton identification of the `P₄` slice.  Its mathematical
  content is `thm:k4free-p4-tripartite` = the graphon rigidity theorem (FORMALISED at the
  kernel level: `Graphon.r3_rigidity`, `GraphonRigidity.lean`) transported through the
  graphon representation of unlabelled limits, which is outside this development
  (README deviation).
-/

open Filter CompleteGraphFreeP4
open scoped Topology

namespace FlagAlgebras.MetaTheory

/-! ## Recovery modulo Zykov equality (`cor:parametric-p4-turan-recovery`) -/

/-- **Recovery modulo Zykov equality**: if every constrained limit attaining the extremal
`K₄` density is the balanced `r`-partite limit `χ★`, then the whole parametric `P₄`
equality slice is `{χ★}` (given the slice is nonempty; the inclusion needs no
nonemptiness). -/
theorem parametric_recovery {r : ℕ} (hr : 3 ≤ r)
    (hZykov : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3)
    {χstar : PositiveHomSpace ∅ₜ}
    (hZykEq : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 = ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 →
      posHomPoint φ₀ = χstar) :
    parametricP4Slice r ⊆ {χstar} := by
  -- Fix `χ` in the slice; set `φ₀ := PositiveHomSpace.toPosHom χ`, so
  -- `posHomPoint φ₀ = χ` (`posHomPoint_toPosHom`).  Slice membership gives
  -- `posHomPoint φ₀ ∈ parametricP4Slice r`; `parametricP4_K4_density hr hZykov` pins the
  -- `K₄` density; `hZykEq` identifies `χ = χstar`.  Also note slice ⊆ `Qσ` via
  -- `posHomPoint_mem_eqSlice`.
  intro χ hχ
  have hpoint : posHomPoint (PositiveHomSpace.toPosHom χ) = χ := posHomPoint_toPosHom χ
  have hmem : posHomPoint (PositiveHomSpace.toPosHom χ) ∈ parametricP4Slice r := by
    rw [hpoint]; exact hχ
  have hQ : posHomPoint (PositiveHomSpace.toPosHom χ) ∈ Qσ (krFreeForb0 r) :=
    (posHomPoint_mem_eqSlice.mp hmem).1
  have hK4 : (PositiveHomSpace.toPosHom χ) FlagAlgebra_4_0_0_10
      = ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 := by
    exact parametricP4_K4_density hr hZykov hmem
  have hstar : posHomPoint (PositiveHomSpace.toPosHom χ) = χstar :=
    hZykEq (PositiveHomSpace.toPosHom χ) hQ hK4
  rw [hpoint] at hstar
  exact Set.mem_singleton_iff.mpr hstar

/-! ## Qualitative stability (`cor:parametric-qualitative-stability`,
`cor:k4free-p4-qualitative-stability`) -/

/-- **Parametric qualitative stability**: under the Zykov hypotheses and nonemptiness of
the slice, every constrained sequence whose `P₄` density tends to the extremal value
converges to the balanced `r`-partite limit. -/
theorem parametric_qualitative_stability {r : ℕ} (hr : 3 ≤ r)
    (hZykov : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3)
    {χstar : PositiveHomSpace ∅ₜ}
    (hZykEq : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 = ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 →
      posHomPoint φ₀ = χstar)
    (hne : (parametricP4Slice r).Nonempty)
    {seq : ℕ → PositiveHomSpace ∅ₜ} (hseq : ∀ k, seq k ∈ Qσ (krFreeForb0 r))
    (hconv : Tendsto
      (fun k => (PositiveHomSpace.toPosHom (seq k)) CompleteGraphFreeP4.P4_density)
      atTop (𝓝 (12 * (((r : ℝ) - 1) / r) ^ 3))) :
    Tendsto seq atTop (𝓝 χstar) := by
  -- `parametric_recovery` + `hne` make the slice exactly `{χstar}`
  -- (`Set.Subset.antisymm`-style / `Set.eq_singleton_iff_nonempty_unique_mem`).  Then apply
  -- `unique_slice_stability` (RelativeSlackness) with `Z := Qσ (krFreeForb0 r)`
  -- (`Qσ_isClosed`), a single equation (`J := PUnit`, `hs _ := P4_density`,
  -- `cs _ := 12((r-1)/r)³`): its slice `{φ ∈ Z | ∀ j, eval = c}` coincides with
  -- `parametricP4Slice r = eqSlice … = {χ | χ ∈ Qσ … ∧ eval = c}` (`Set.ext`,
  -- `posHomPoint`-free — both are sets of `PositiveHomSpace ∅ₜ` defined by the same
  -- conditions; unfold `eqSlice` and massage the `∀ (_ : PUnit)` quantifier).
  have heq : parametricP4Slice r = {χstar} :=
    Set.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hne, fun χ hχ =>
        Set.mem_singleton_iff.mp (parametric_recovery hr hZykov hZykEq hχ)⟩
  refine unique_slice_stability (Qσ_isClosed (krFreeForb0 r))
    (fun _ : Unit => CompleteGraphFreeP4.P4_density)
    (fun _ => 12 * (((r : ℝ) - 1) / r) ^ 3) ?_ hseq fun _ => hconv
  rw [← heq]
  ext φ
  simp [parametricP4Slice, eqSlice]

/-- **Qualitative stability for the `K₄`-free `P₄` problem**
(`cor:k4free-p4-qualitative-stability`): given the singleton identification of the slice
(whose content is the FORMALISED kernel-level rigidity `Graphon.r3_rigidity` plus the
unformalised graphon representation — see the module docstring), every `K₄`-free sequence
whose `P₄` density tends to `32/9` converges to the balanced tripartite limit. -/
theorem k4free_qualitative_stability {χstar : PositiveHomSpace ∅ₜ}
    (huniq : k4freeP4Slice = {χstar})
    {seq : ℕ → PositiveHomSpace ∅ₜ} (hseq : ∀ k, seq k ∈ Qσ (krFreeForb0 3))
    (hconv : Tendsto (fun k => (PositiveHomSpace.toPosHom (seq k)) K4freeP4.P4_density)
      atTop (𝓝 (32 / 9))) :
    Tendsto seq atTop (𝓝 χstar) := by
  -- `unique_slice_stability` with `Z := Qσ (krFreeForb0 3)`, the single equation
  -- `K4freeP4.P4_density = 32/9`, and `huniq` (unfold `k4freeP4Slice`/`eqSlice` to match
  -- the sep-set of `unique_slice_stability`).
  refine unique_slice_stability (Qσ_isClosed (krFreeForb0 3))
    (fun _ : Unit => K4freeP4.P4_density) (fun _ => 32 / 9) ?_ hseq fun _ => hconv
  rw [← huniq]
  ext φ
  simp [k4freeP4Slice, eqSlice]

end FlagAlgebras.MetaTheory
