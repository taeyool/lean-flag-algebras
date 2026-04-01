import LeanFlagAlgebras.FlagAlgebra.QuadraticForm

open FlagAlgebras
open MeasureTheory

namespace Forbid

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

def forbidEq
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra σ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), (hσ : φ₀ ⟨σ⟩₀ > 0)
    → φ₀ ⟦unitVector F_forbid⟧ = 0
    → ℙ[φ₀] {φ | φ f = φ g} = 1

def forbidLE
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra σ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), (hσ : φ₀ ⟨σ⟩₀ > 0)
    → φ₀ ⟦unitVector F_forbid⟧ = 0
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

theorem forbidEq_sum_eq_zero
    {F_forbid : FinFlag ∅ₜ} {α : Type*}
    (s : Finset α) (f : α → FlagAlgebra σ)
    (hzero : ∀ a ∈ s, f a =[F_forbid] 0)
    : (Finset.sum s f) =[F_forbid] 0
  := by
  classical
  revert hzero
  refine Finset.induction_on s ?base ?step
  · intro _
    simpa using (forbidEq_refl F_forbid (0 : FlagAlgebra σ))
  · intro a s ha ih hzero
    have ha0 : f a =[F_forbid] 0 := hzero a (by simp)
    have hs : ∀ x ∈ s, f x =[F_forbid] 0 := by
      intro x hx
      exact hzero x (by simp [hx])
    have hs0 : (Finset.sum s f) =[F_forbid] 0 := ih hs
    simpa [Finset.sum_insert, ha] using (forbidEq_add ha0 hs0)

theorem forbidEq_sum_filter_eq_zero
    {F_forbid : FinFlag ∅ₜ} {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → FlagAlgebra σ)
    (hzero : ∀ a ∈ s, p a → f a =[F_forbid] 0)
  : (Finset.sum (s.filter p) f) =[F_forbid] 0
  := by
  apply forbidEq_sum_eq_zero (F_forbid := F_forbid) (s := s.filter p) (f := f)
  intro a ha
  exact hzero a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2

theorem forbidEq_smul
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

theorem forbidEq_smul_zero
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} {c : ℝ}
    (hfg : f =[F_forbid] 0)
    : (c • f) =[F_forbid] 0
  := by
  have := forbidEq_smul (c := c) hfg
  simpa using this

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

theorem unitVector_forbidEq_zero
    (F_forbid : FinFlag ∅ₜ) (F : FinFlag σ) (hF : flagDensity₁ F_forbid.2 (unlabel F.2) > 0)
    : ⟦unitVector F⟧ =[F_forbid] 0
  := by
  intro φ₀ hσ hF_forbid
  have h_nonneg : ∀ φ : PositiveHomSpace σ, 0 ≤ (PositiveHomSpace.toPosHom φ) ⟦unitVector F⟧ := by
    intro φ
    exact positiveHom_unitVector_ge_zero (PositiveHomSpace.toPosHom φ) F
  have h_measurable :
      Measurable (fun φ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom φ) ⟦unitVector F⟧) := by
    simpa using
      (positiveHomSpace_eval_continuous (σ := σ) (⟦unitVector F⟧ : FlagAlgebra σ)).measurable
  have h_integrable :
      Integrable
        (fun φ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom φ) ⟦unitVector F⟧)
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))) := by
    apply Integrable.of_bound
    · exact Measurable.aestronglyMeasurable h_measurable
    · exact Filter.Eventually.of_forall (fun φ => by
        simp only [Real.norm_eq_abs]
        simpa [PositiveHomSpace.toPosHom_unitVector] using flagDensitySpace_abs_le_one φ F)
  have h_integral_zero :
      ∫ φ : PositiveHomSpace σ, (PositiveHomSpace.toPosHom φ) ⟦unitVector F⟧ ∂(ℙ[φ₀]) = 0 := by
    rw [probMeasure_extend_emptyType_positiveHom_spec]
    simp; left
    simp [downward, downwardFlagVectorQuot, downwardFlagVector_unitVector, downwardFlag]
    simp [smul_quot, PositiveHom.map_smul]
    right
    exact positiveHom_unitVector_eq_zero φ₀ hF hF_forbid
  have h_prob_zero :
      ℙ[φ₀] {φ : PositiveHomSpace σ | (PositiveHomSpace.toPosHom φ) ⟦unitVector F⟧ = 0} = 1 :=
    ae_zero_of_integral_eq_zero h_nonneg h_measurable (by simpa using h_integrable) h_integral_zero
  simpa [PositiveHomSpace.toPosHom_unitVector] using h_prob_zero

theorem unitVector_quot_forbidEq_sum
    (F_forbid : FinFlag ∅ₜ) (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    : ⟦unitVector F⟧ =[F_forbid]
      ∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') = 0,
        (flagDensity₁ F.2 F' : ℝ) • ⟦unitVector ⟨ℓ, F'⟩⟧
  := by
  rw [unitVector_quot_eq_sum F ℓ hℓ]
  let p : FlagWithSize σ ℓ → Prop :=
    fun x => 0 < flagDensity₁ F_forbid.2 (unlabel x)
  have hpred : ∀ x : FlagWithSize σ ℓ,
      (¬ p x) ↔ (flagDensity₁ F_forbid.2 (unlabel x) = 0) := by
    intro x
    constructor
    · intro hx
      exact le_antisymm
        (le_of_not_gt (by simpa [p] using hx))
        (flagListDensity₁_ge_zero F_forbid.2 (unlabel x))
    · intro hx
      simp [p, hx]
  have hsplit :
      (∑ x : FlagWithSize σ ℓ,
        (flagDensity₁ F.2 x : ℝ) • (⟦unitVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        =
      (∑ x : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel x) > 0,
        (flagDensity₁ F.2 x : ℝ) • (⟦unitVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        +
      (∑ x : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel x) = 0,
        (flagDensity₁ F.2 x : ℝ) • (⟦unitVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun x => p x)]
    simp_rw [hpred]
    rfl
  rw [hsplit]
  nth_rw 2 [← zero_add (∑ F' with flagDensity₁ F_forbid.2 (unlabel F') = 0, _)]
  apply forbidEq_add
  · apply forbidEq_sum_filter_eq_zero
    intro x _ hx
    apply forbidEq_smul_zero
    exact unitVector_forbidEq_zero F_forbid ⟨ℓ, x⟩ hx
  · apply forbidEq_refl

theorem unitVector_quot_mul_forbidEq_sum
    (F_forbid : FinFlag ∅ₜ) (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    : (⟦unitVector F₁⟧ * ⟦unitVector F₂⟧ : FlagAlgebra σ) =[F_forbid]
      ∑ F' : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel F') = 0,
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) • ⟦unitVector ⟨ℓ, F'⟩⟧
  := by
  rw [unitVector_quot_mul_eq_flagMulWithSize_quot F₁ F₂ ℓ hℓ]
  simp [flagMulWithSize, sum_quot, smul_quot]
  let p : FlagWithSize σ ℓ → Prop :=
    fun x => 0 < flagDensity₁ F_forbid.2 (unlabel x)
  have hpred : ∀ x : FlagWithSize σ ℓ,
      (¬ p x) ↔ (flagDensity₁ F_forbid.2 (unlabel x) = 0) := by
    intro x
    constructor
    · intro hx
      exact le_antisymm
        (le_of_not_gt (by simpa [p] using hx))
        (flagListDensity₁_ge_zero F_forbid.2 (unlabel x))
    · intro hx
      simp [p, hx]
  have hsplit :
      (∑ x : FlagWithSize σ ℓ,
        (flagDensity₂ F₁.2 F₂.2 x : ℝ) • (⟦unitVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        =
      (∑ x : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel x) > 0,
        (flagDensity₂ F₁.2 F₂.2 x : ℝ) • (⟦unitVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ))
        +
      (∑ x : FlagWithSize σ ℓ with flagDensity₁ F_forbid.2 (unlabel x) = 0,
        (flagDensity₂ F₁.2 F₂.2 x : ℝ) • (⟦unitVector ⟨ℓ, x⟩⟧ : FlagAlgebra σ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun x => p x)]
    simp_rw [hpred]
    rfl
  rw [hsplit]
  nth_rw 2 [← zero_add (∑ F' with flagDensity₁ F_forbid.2 (unlabel F') = 0, _)]
  apply forbidEq_add
  · apply forbidEq_sum_filter_eq_zero
    intro x _ hx
    apply forbidEq_smul_zero
    exact unitVector_forbidEq_zero F_forbid ⟨ℓ, x⟩ hx
  · apply forbidEq_refl

theorem downward_forbidLE_nonneg
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : 0 ≤[F_forbid] f)
    : 0 ≤[F_forbid] ⟦f⟧₀
  := by
  sorry

theorem positiveHom_emptyType_eval_one
    (φ₀ : PositiveHom ∅ₜ)
    : φ₀ ⟨∅ₜ⟩₀ = 1
  := by
  sorry

lemma probMeasure_extend_emptyType_positiveHom_singleton_eq_one
    (φ₀ : PositiveHom ∅ₜ)
    : probMeasure_extend_emptyType_positiveHom (σ := ∅ₜ) φ₀
        (by
          have h1 : φ₀ ⟨∅ₜ⟩₀ = 1 := positiveHom_emptyType_eval_one φ₀
          nlinarith)
        {φ : PositiveHomSpace ∅ₜ | φ = (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)} = 1
  := by
  sorry

def forbidEq_emptyType
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), φ₀ ⟦unitVector F_forbid⟧ = 0 → φ₀ f = φ₀ g

def forbidLE_emptyType
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ) : Prop
  :=
  ∀ (φ₀ : PositiveHom ∅ₜ), φ₀ ⟦unitVector F_forbid⟧ = 0 → φ₀ f ≤ φ₀ g

notation f "=[" F_forbid "]₀" g => forbidEq_emptyType F_forbid f g
notation f "≤[" F_forbid "]₀" g => forbidLE_emptyType F_forbid f g

theorem forbidEq_emptyType_iff_forbidEq
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ)
    : (f =[F_forbid]₀ g) ↔ (f =[F_forbid] g)
  := by
  sorry

theorem forbidLE_emptyType_iff_forbidLE
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ)
    : (f ≤[F_forbid]₀ g) ↔ (f ≤[F_forbid] g)
  := by
  constructor
  · intro hfg φ₀ hσ hF_forbid
    specialize hfg φ₀ hF_forbid
    sorry
  · sorry

end Forbid
