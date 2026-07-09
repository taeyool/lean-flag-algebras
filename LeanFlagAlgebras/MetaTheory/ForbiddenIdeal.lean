import LeanFlagAlgebras.MetaTheory.ConstrainedClass

/-! # The forbidden ideal as an ℝ-span (paper §3)

When the product of a forbidden flag with any algebra element stays in the ℝ-span of the
forbidden flags — the algebraic content of *heredity* — the forbidden ideal coincides with that
ℝ-span.  The ℝ-span is automatically a submodule; the heredity hypothesis upgrades it to an ideal,
and the two-way inclusion of carriers gives the equality of underlying sets.
-/

open Classical
namespace FlagAlgebras.MetaTheory
variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- The set of forbidden basis flags. -/
def forbiddenGens (forb : FinFlag σ → Prop) : Set (FlagAlgebra σ) :=
  {x | ∃ F, forb F ∧ x = ⟦basisVector F⟧}

/-- **Heredity ⟹ the forbidden flags span an ideal** (paper §3): when the product of a forbidden
flag with any algebra element stays in the ℝ-span of the forbidden flags (the algebraic content of
heredity), the forbidden ideal coincides with that ℝ-span. -/
theorem forbiddenIdeal_eq_span (forb : FinFlag σ → Prop)
    (hered : ∀ (F : FinFlag σ) (g : FlagAlgebra σ), forb F →
      (⟦basisVector F⟧ : FlagAlgebra σ) * g ∈ Submodule.span ℝ (forbiddenGens forb)) :
    (forbiddenIdeal forb : Set (FlagAlgebra σ)) = (Submodule.span ℝ (forbiddenGens forb) : Set (FlagAlgebra σ)) := by
  set S := forbiddenGens forb
  -- Multiplicative closure of the ℝ-span: `g * x ∈ span ℝ S` for every `g` and `x ∈ span ℝ S`.
  have hmul : ∀ (g : FlagAlgebra σ) (x : FlagAlgebra σ),
      x ∈ Submodule.span ℝ S → g * x ∈ Submodule.span ℝ S := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨F, hF, rfl⟩ := hy
        rw [mul_comm]
        exact hered F g hF
    | zero => simp
    | add a b _ _ ha hb =>
        rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
        rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  -- Package the ℝ-span as an ideal `I` with the same carrier.
  let I : Ideal (FlagAlgebra σ) :=
    { Submodule.span ℝ S with
      smul_mem' := fun g x hx => hmul g x hx }
  have hIcoe : (I : Set (FlagAlgebra σ)) = (Submodule.span ℝ S : Set (FlagAlgebra σ)) := rfl
  apply Set.Subset.antisymm
  · -- `Ideal.span S ⊆ span ℝ S`, via the ideal `I`.
    have hSI : S ⊆ (I : Set (FlagAlgebra σ)) := by
      intro x hx
      rw [hIcoe]
      exact Submodule.subset_span hx
    have hle : forbiddenIdeal forb ≤ I := Ideal.span_le.mpr hSI
    intro x hx
    have hxI : x ∈ I := hle hx
    rw [← SetLike.mem_coe, hIcoe] at hxI
    exact hxI
  · -- `span ℝ S ⊆ Ideal.span S`.
    have hsub : (Submodule.span ℝ S) ≤ (forbiddenIdeal forb).restrictScalars ℝ := by
      refine Submodule.span_le.mpr ?_
      intro x hx
      simp only [Submodule.restrictScalars_mem, SetLike.mem_coe]
      exact Ideal.subset_span hx
    intro x hx
    have hxI : x ∈ (forbiddenIdeal forb).restrictScalars ℝ := hsub hx
    rwa [Submodule.restrictScalars_mem] at hxI

end FlagAlgebras.MetaTheory
