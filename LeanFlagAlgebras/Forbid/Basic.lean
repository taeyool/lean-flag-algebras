import LeanFlagAlgebras.FlagAlgebra.QuadraticForm

open FlagAlgebras
open MeasureTheory

namespace Forbid

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

def forbidEq
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra σ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), (hσ : φ₀ ⟨σ⟩₀ > 0)
    → φ₀ ⟦unitVector F_forbid⟧ > 0
    → ℙ[φ₀] {φ | φ f = φ g} = 1

def forbidLE
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra σ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), (hσ : φ₀ ⟨σ⟩₀ > 0)
    → φ₀ ⟦unitVector F_forbid⟧ > 0
    → ℙ[φ₀] {φ | φ f ≤ φ g} = 1

notation f "=[" F_forbid "]" g => forbidEq F_forbid f g
notation f "≤[" F_forbid "]" g => forbidLE F_forbid f g

lemma positiveHomSpace_eval_eq_sum
    (k : FlagAlgebra σ)
    : (fun ψ : PositiveHomSpace σ => ψ k)
      = (fun ψ => ∑ F ∈ k.out.support, k.out F * ψ.val F)
  := by
  funext ψ
  conv_lhs =>
    rw [← Quotient.out_eq k, flagVector_eq_sum_unitVector k.out]
    rw [sum_quot, PositiveHom.map_sum]
    simp only [smul_quot, PositiveHom.map_smul, PositiveHomSpace.toPosHom_unitVector]

lemma positiveHomSpace_toPosHom_continuous
    : Continuous (fun (ψ : PositiveHomSpace σ) => (PositiveHomSpace.toPosHom ψ : FlagAlgebra σ → ℝ))
  := by
  apply continuous_pi
  intro k
  have h_cont_sum : Continuous (fun ψ : PositiveHomSpace σ => ∑ F ∈ k.out.support, k.out F * ψ.val F) := by
    apply continuous_finset_sum
    intro F hF
    exact Continuous.mul continuous_const ((FinFlag.continuous F).comp continuous_subtype_val)
  simpa [positiveHomSpace_eval_eq_sum (σ := σ) k] using h_cont_sum

lemma positiveHomSpace_eval_continuous
    (f : FlagAlgebra σ)
    : Continuous (fun ψ : PositiveHomSpace σ => ψ f)
  :=
  (continuous_apply f).comp positiveHomSpace_toPosHom_continuous

lemma forbidEq_set_measurable
    (f g : FlagAlgebra σ)
    : MeasurableSet {φ : PositiveHomSpace σ | φ f = φ g}
  :=
  (isClosed_eq (positiveHomSpace_eval_continuous (σ := σ) f)
    (positiveHomSpace_eval_continuous (σ := σ) g)).measurableSet

lemma forbidLE_set_measurable
    (f g : FlagAlgebra σ)
    : MeasurableSet {φ : PositiveHomSpace σ | φ f ≤ φ g}
  :=
  (isClosed_le (positiveHomSpace_eval_continuous (σ := σ) f)
    (positiveHomSpace_eval_continuous (σ := σ) g)).measurableSet

theorem forbidEq_refl
    (F_forbid : FinFlag ∅ₜ) (f : FlagAlgebra σ)
    : f =[F_forbid] f
  := by
  intro φ₀ hσ hF_forbid
  simp

theorem forbidLE_refl
    (F_forbid : FinFlag ∅ₜ) (f : FlagAlgebra σ)
    : f ≤[F_forbid] f
  := by
  intro φ₀ hσ hF_forbid
  simp

theorem forbidEq_symm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f =[F_forbid] g)
    : g =[F_forbid] f
  := by
  intro φ₀ hσ hF_forbid
  simpa [eq_comm] using hfg φ₀ hσ hF_forbid

theorem forbidEq_implies_forbidLE
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f =[F_forbid] g)
    : f ≤[F_forbid] g
  := by
  intro φ₀ hσ hF_forbid
  have hEq : ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ g} = 1 := hfg φ₀ hσ hF_forbid
  have hmono :
      {φ : PositiveHomSpace σ | φ f = φ g} ⊆ {φ : PositiveHomSpace σ | φ f ≤ φ g} := by
    intro φ hφ
    exact le_of_eq (by simpa using hφ)
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ g} := by
        simpa using hEq.symm
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hmono

theorem forbidEq_trans
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =[F_forbid] g) (hgh : g =[F_forbid] h)
    : f =[F_forbid] h
  := by
  intro φ₀ hσ hF_forbid
  let A : Set (PositiveHomSpace σ) := {φ | φ f = φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ g = φ h}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
  have hB : ℙ[φ₀] B = 1 := hgh φ₀ hσ hF_forbid
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidEq_set_measurable (σ := σ) f g)
      (forbidEq_set_measurable (σ := σ) g h) hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ f = φ h} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hgh'⟩
    exact Eq.trans (by simpa [A] using hfg') (by simpa [B] using hgh')
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ h} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

theorem forbidLE_trans
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤[F_forbid] g) (hgh : g ≤[F_forbid] h)
    : f ≤[F_forbid] h
  := by
  intro φ₀ hσ hF_forbid
  let A : Set (PositiveHomSpace σ) := {φ | φ f ≤ φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ g ≤ φ h}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
  have hB : ℙ[φ₀] B = 1 := hgh φ₀ hσ hF_forbid
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidLE_set_measurable (σ := σ) f g)
      (forbidLE_set_measurable (σ := σ) g h) hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ f ≤ φ h} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hgh'⟩
    exact le_trans (by simpa [A] using hfg') (by simpa [B] using hgh')
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ h} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

theorem forbidEq_add
    {F_forbid : FinFlag ∅ₜ} {f g f' g' : FlagAlgebra σ}
    (hfg : f =[F_forbid] g) (hf'g' : f' =[F_forbid] g')
    : (f + f') =[F_forbid] (g + g')
  := by
  intro φ₀ hσ hF_forbid
  let A : Set (PositiveHomSpace σ) := {φ | φ f = φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ f' = φ g'}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
  have hB : ℙ[φ₀] B = 1 := hf'g' φ₀ hσ hF_forbid
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidEq_set_measurable (σ := σ) f g)
      (forbidEq_set_measurable (σ := σ) f' g') hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ (f + f') = φ (g + g')} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hf'g''⟩
    have h₁ : φ f = φ g := by simpa [A] using hfg'
    have h₂ : φ f' = φ g' := by simpa [B] using hf'g''
    calc
      φ (f + f') = φ f + φ f' := by simp [PositiveHom.map_add]
      _ = φ g + φ g' := by simp [h₁, h₂]
      _ = φ (g + g') := by simp [PositiveHom.map_add]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (f + f') = φ (g + g')} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

theorem forbidEq_add_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =[F_forbid] g)
    : (h + f) =[F_forbid] (h + g)
  :=
  forbidEq_add (forbidEq_refl F_forbid h) hfg

theorem forbidEq_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f =[F_forbid] g)
    : (f + h) =[F_forbid] (g + h)
  :=
  forbidEq_add hfg (forbidEq_refl F_forbid h)

theorem forbitEq_smul
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ} {c : ℝ}
    (hfg : f =[F_forbid] g)
    : (c • f) =[F_forbid] (c • g)
  := by
  intro φ₀ hσ hF_forbid
  let A : Set (PositiveHomSpace σ) := {φ | φ f = φ g}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
  have hsubset :
      A ⊆ {φ : PositiveHomSpace σ | φ (c • f) = φ (c • g)} := by
    intro φ hφ
    have hfg' : φ f = φ g := by simpa using hφ
    calc
      φ (c • f) = c * φ f := by simp [PositiveHom.map_smul]
      _ = c * φ g := by simp [hfg']
      _ = φ (c • g) := by simp [PositiveHom.map_smul]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] A := by simpa using hA.symm
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (c • f) = φ (c • g)} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

theorem forbidLE_add
    {F_forbid : FinFlag ∅ₜ} {f g f' g' : FlagAlgebra σ}
    (hfg : f ≤[F_forbid] g) (hf'g' : f' ≤[F_forbid] g')
    : (f + f') ≤[F_forbid] (g + g')
  := by
  intro φ₀ hσ hF_forbid
  let A : Set (PositiveHomSpace σ) := {φ | φ f ≤ φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ f' ≤ φ g'}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
  have hB : ℙ[φ₀] B = 1 := hf'g' φ₀ hσ hF_forbid
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidLE_set_measurable (σ := σ) f g)
      (forbidLE_set_measurable (σ := σ) f' g') hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ (f + f') ≤ φ (g + g')} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hf'g''⟩
    have h₁ : φ f ≤ φ g := by simpa [A] using hfg'
    have h₂ : φ f' ≤ φ g' := by simpa [B] using hf'g''
    calc
      φ (f + f') = φ f + φ f' := by simp [PositiveHom.map_add]
      _ ≤ φ g + φ g' := add_le_add h₁ h₂
      _ = φ (g + g') := by simp [PositiveHom.map_add]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (f + f') ≤ φ (g + g')} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

theorem forbidLE_add_left
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤[F_forbid] g)
    : (h + f) ≤[F_forbid] (h + g)
  :=
  forbidLE_add (forbidLE_refl F_forbid h) hfg

theorem forbidLE_add_right
    {F_forbid : FinFlag ∅ₜ} {f g h : FlagAlgebra σ}
    (hfg : f ≤[F_forbid] g)
    : (f + h) ≤[F_forbid] (g + h)
  :=
  forbidLE_add hfg (forbidLE_refl F_forbid h)

theorem forbidLE_smul_nonneg
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ} {c : ℝ}
    (hc : 0 ≤ c) (hfg : f ≤[F_forbid] g)
    : (c • f) ≤[F_forbid] (c • g)
  := by
  intro φ₀ hσ hF_forbid
  have hA : ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} = 1 := hfg φ₀ hσ hF_forbid
  have hsubset :
      {φ : PositiveHomSpace σ | φ f ≤ φ g} ⊆
      {φ : PositiveHomSpace σ | φ (c • f) ≤ φ (c • g)} := by
    intro φ hφ
    have hfg' : φ f ≤ φ g := by simpa using hφ
    calc
      φ (c • f) = c * φ f := by simp [PositiveHom.map_smul]
      _ ≤ c * φ g := mul_le_mul_of_nonneg_left hfg' hc
      _ = φ (c • g) := by simp [PositiveHom.map_smul]
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] {φ : PositiveHomSpace σ | φ f ≤ φ g} := by simpa using hA.symm
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ (c • f) ≤ φ (c • g)} :=
        ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset

example (F_forbid : FinFlag ∅ₜ) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦unitVector F⟧ =[F_forbid] ∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') > 0, (flagDensity₁ F.2 F' : ℝ) • ⟦unitVector ⟨ℓ, F'⟩⟧
  := by
  sorry

end Forbid
