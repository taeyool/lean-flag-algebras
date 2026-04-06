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

theorem forbidLE_antisymm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra σ}
    (hfg : f ≤[F_forbid] g) (hgf : g ≤[F_forbid] f)
    : f =[F_forbid] g
  := by
  intro φ₀ hσ hF_forbid
  let A : Set (PositiveHomSpace σ) := {φ | φ f ≤ φ g}
  let B : Set (PositiveHomSpace σ) := {φ | φ g ≤ φ f}
  have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
  have hB : ℙ[φ₀] B = 1 := hgf φ₀ hσ hF_forbid
  have hAB : ℙ[φ₀] (A ∩ B) = 1 :=
    prob_inter_eq_one_of_prob_eq_one (forbidLE_set_measurable (σ := σ) f g)
      (forbidLE_set_measurable (σ := σ) g f) hA hB
  have hsubset : A ∩ B ⊆ {φ : PositiveHomSpace σ | φ f = φ g} := by
    intro φ hφ
    rcases hφ with ⟨hfg', hgf'⟩
    exact le_antisymm (by simpa [A] using hfg') (by simpa [B] using hgf')
  apply le_antisymm
  · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) _
  · calc
      1 = ℙ[φ₀] (A ∩ B) := by simp [hAB]
      _ ≤ ℙ[φ₀] {φ : PositiveHomSpace σ | φ f = φ g} :=
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
  have h_nonneg : ∀ φ : PositiveHomSpace σ, 0 ≤ φ ⟦unitVector F⟧ := by
    intro φ
    exact positiveHom_unitVector_ge_zero (PositiveHomSpace.toPosHom φ) F
  have h_measurable :
      Measurable (fun φ : PositiveHomSpace σ => φ ⟦unitVector F⟧) := by
    simpa using
      (positiveHomSpace_eval_continuous (σ := σ) (⟦unitVector F⟧ : FlagAlgebra σ)).measurable
  have h_integrable :
      Integrable
        (fun φ : PositiveHomSpace σ => φ ⟦unitVector F⟧)
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))) := by
    apply Integrable.of_bound
    · exact Measurable.aestronglyMeasurable h_measurable
    · exact Filter.Eventually.of_forall (fun φ => by
        simp only [Real.norm_eq_abs]
        simpa [PositiveHomSpace.toPosHom_unitVector] using flagDensitySpace_abs_le_one φ F)
  have h_integral_zero :
      ∫ φ : PositiveHomSpace σ, φ ⟦unitVector F⟧ ∂(ℙ[φ₀]) = 0 := by
    rw [probMeasure_extend_emptyType_positiveHom_spec]
    simp; left
    simp [downward, downwardFlagVectorQuot, downwardFlagVector_unitVector, downwardFlag]
    simp [smul_quot, PositiveHom.map_smul]
    right
    exact positiveHom_unitVector_eq_zero φ₀ hF hF_forbid
  have h_prob_zero :
      ℙ[φ₀] {φ | φ ⟦unitVector F⟧ = 0} = 1 :=
    ae_zero_of_integral_eq_zero h_nonneg h_measurable (by simpa using h_integrable) h_integral_zero
  simpa [PositiveHomSpace.toPosHom_unitVector] using h_prob_zero

-- theorem flagDensity₁_pos_of_unitVector_forbidEq_zero
--     {F_forbid : FinFlag ∅ₜ} {F : FinFlag σ} (hF_forbid : ⟦unitVector F⟧ =[F_forbid] 0)
--     : flagDensity₁ F_forbid.2 (unlabel F.2) > 0
--   := by
--   contrapose! hF_forbid
--   simp [forbidEq]
--   sorry

-- theorem forbidEq_zero_iff
--     {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : f =[F_forbid] 0)
--     : ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (v : I → FinFlag σ),
--       f = ∑ i, c i • ⟦unitVector (v i)⟧ ∧ (∀ i, flagDensity₁ F_forbid.2 (unlabel (v i).2) > 0)
--   := by
--   dsimp [forbidEq] at hf
--   sorry

-- theorem all_unitVector_forbidEq_zero_of_sum_forbidEq_zero
--     {I : Type} [Fintype I]
--     {c : I → ℝ} (hc : ∀ i, c i ≠ 0) {v : I → FinFlag σ} (hv : ∀ i j, i ≠ j → v i ≠ v j)
--     {F_forbid : FinFlag ∅ₜ} (hf : (∑ i, c i • ⟦unitVector (v i)⟧) =[F_forbid] 0)
--     : ∀ i, ⟦unitVector (v i)⟧ =[F_forbid] 0
--   := by
--   intro i
--   apply unitVector_forbidEq_zero
--   sorry

-- theorem flagAlgebra_eq_sum_unitVector_quot
--     (f : FlagAlgebra σ)
--     : ∃ (I : Type) (_ : Fintype I)
--          (c : I → ℝ) (_ : ∀ i, c i ≠ 0) (v : I → FinFlag σ) (_ : ∀ i j, i ≠ j → v i ≠ v j),
--       f = ∑ i, c i • ⟦unitVector (v i)⟧
--   := by
--   rcases Quot.exists_rep f with ⟨f, rfl⟩
--   rw [flagVector_eq_sum_unitVector f]
--   use (↑f.support : Type), inferInstance, (fun i => f i), ?_, (fun i => (i : FinFlag σ)), ?_
--   · simp_rw [← smul_quot, ← sum_quot]
--     apply Quotient.sound
--     apply flagVector_eq_eqv
--     simpa using
--       (Finset.sum_attach (s := f.support)
--         (f := fun F : FinFlag σ => f F • unitVector F)).symm
--   · intro ⟨i, hi⟩
--     simp only [ne_eq]
--     simp_all only [Finsupp.mem_support_iff, ne_eq, not_false_eq_true]
--   · simp only [ne_eq, SetLike.coe_eq_coe, imp_self, implies_true]

-- theorem unlabel_unlabel
--     {V : Type} (F : Flag σ V)
--     : unlabel (unlabel F) = unlabel F
--   := by
--   refine Quot.inductionOn F ?_
--   intro G
--   simp [unlabel, unlabeledGraphQuot, unlabeledGraph]

-- theorem downward_forbidEq_zero
--     {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : f =[F_forbid] 0)
--     : ⟦f⟧₀ =[F_forbid] 0
--   := by
--   obtain ⟨I, _, c, hc, v, hv, hf⟩ := flagAlgebra_eq_sum_unitVector_quot f
--   subst hf
--   apply all_unitVector_forbidEq_zero_of_sum_forbidEq_zero hc hv at hf
--   simp_rw [downward_sum, downward_smul]
--   apply forbidEq_sum_eq_zero
--   intro i _
--   apply forbidEq_smul_zero
--   simp [downward, downwardFlagVectorQuot, downwardFlagVector_unitVector, downwardFlag, smul_quot]
--   apply forbidEq_smul_zero
--   apply unitVector_forbidEq_zero
--   simp [unlabel_unlabel]
--   apply flagDensity₁_pos_of_unitVector_forbidEq_zero
--   exact hf i

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

lemma flagType_asEmptyTypeAlgebra_emptyType_eq_one
    : ⟨∅ₜ⟩₀ = 1
  := by
  show _ = ⟦unitVector ⟨0, default⟩⟧
  simp [flagType_asEmptyTypeAlgebra]
  congr
  apply Quotient.sound
  exact Nonempty.intro {
    graph_iso := SimpleGraph.Iso.refl
    type_preserve := List.ofFn_inj.mp rfl
  }

lemma probMeasure_extend_emptyType_positiveHom_singleton_eq_one
    (φ₀ : PositiveHom ∅ₜ)
    : probMeasure_extend_emptyType_positiveHom (σ := ∅ₜ) φ₀
        (by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one])
        {⟨φ₀.coe, ⟨φ₀, rfl⟩⟩} = 1
  := by
  have hσ : φ₀ ⟨∅ₜ⟩₀ > 0 := by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one]
  let a₀ : PositiveHomSpace ∅ₜ := ⟨φ₀.coe, ⟨φ₀, rfl⟩⟩
  have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ
  have hspec' : ∀ f : FlagAlgebra ∅ₜ, ∫ φ : PositiveHomSpace ∅ₜ, φ f ∂ℙ[φ₀] = φ₀ f := by
    intro f
    have h := hspec f
    simpa [downward_emptyType, div_one] using h
  have h_int_var : ∀ f : FlagAlgebra ∅ₜ,
      ∫ φ : PositiveHomSpace ∅ₜ, ((φ f) - (φ₀ f))^2 ∂ℙ[φ₀] = 0 := by
    intro f
    let q : FlagAlgebra ∅ₜ :=
      (f - (φ₀ f) • (1 : FlagAlgebra ∅ₜ)) * (f - (φ₀ f) • (1 : FlagAlgebra ∅ₜ))
    have hq : ∫ φ : PositiveHomSpace ∅ₜ, φ q ∂ℙ[φ₀] = φ₀ q := hspec' q
    calc
      ∫ φ : PositiveHomSpace ∅ₜ, ((φ f) - (φ₀ f))^2 ∂ℙ[φ₀]
          = ∫ φ : PositiveHomSpace ∅ₜ, φ q ∂ℙ[φ₀] := by
              apply integral_congr_ae
              filter_upwards with φ
              rw [pow_two]
              simp [q, PositiveHom.map_mul, PositiveHom.map_sub,
                PositiveHom.map_smul, PositiveHom.map_one]
      _ = φ₀ q := hq
      _ = 0 := by
            simp [q, PositiveHom.map_mul, PositiveHom.map_sub,
              PositiveHom.map_smul, PositiveHom.map_one]
  have h_unit_ae : ∀ F : FinFlag ∅ₜ,
      ℙ[φ₀] {φ : PositiveHomSpace ∅ₜ | φ ⟦unitVector F⟧ = φ₀ ⟦unitVector F⟧} = 1 := by
    intro F
    let g : PositiveHomSpace ∅ₜ → ℝ :=
      fun φ => ((φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧))^2
    have hg_nonneg : ∀ φ : PositiveHomSpace ∅ₜ, 0 ≤ g φ := by
      intro φ
      positivity
    have hg_measurable : Measurable g := by
      dsimp [g]
      have hsub : Measurable (fun φ : PositiveHomSpace ∅ₜ =>
          (φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧)) :=
        Measurable.sub
          ((positiveHomSpace_eval_continuous (σ := ∅ₜ)
            (⟦unitVector F⟧ : FlagAlgebra ∅ₜ)).measurable)
          measurable_const
      simpa [pow_two] using Measurable.mul hsub hsub
    have hg_integrable : Integrable g ℙ[φ₀] := by
      apply Integrable.of_bound
      · exact Measurable.aestronglyMeasurable hg_measurable
      · exact Filter.Eventually.of_forall (fun φ => by
          dsimp [g]
          have hφ_abs : |φ ⟦unitVector F⟧| ≤ 1 := by
            simpa [PositiveHomSpace.toPosHom_unitVector] using flagDensitySpace_abs_le_one φ F
          have hφ₀_abs : |φ₀ ⟦unitVector F⟧| ≤ 1 := by
            rw [abs_le]
            constructor
            · linarith [positiveHom_unitVector_ge_zero φ₀ F]
            · exact positiveHom_unitVector_le_one φ₀ F
          have hsub_abs : |(φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧)| ≤ 2 := by
            calc
              |(φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧)|
                  ≤ |φ ⟦unitVector F⟧| + |φ₀ ⟦unitVector F⟧| := abs_sub _ _
              _ ≤ 1 + 1 := add_le_add hφ_abs hφ₀_abs
              _ = 2 := by norm_num
          have hsub_nonneg : 0 ≤ |(φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧)| := abs_nonneg _
          have hsq_le : |(φ ⟦unitVector F⟧ - φ₀ ⟦unitVector F⟧)| ^ 2 ≤ 4 := by
            nlinarith [hsub_abs, hsub_nonneg]
          have hnorm_eq : ‖((φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧))^2‖
              = |(φ ⟦unitVector F⟧ - φ₀ ⟦unitVector F⟧)| ^ 2 := by
            simp [Real.norm_eq_abs, pow_two]
          simpa [hnorm_eq] using hsq_le)
    have hg_int_zero : ∫ φ : PositiveHomSpace ∅ₜ, g φ ∂ℙ[φ₀] = 0 := by
      simpa [g] using h_int_var (⟦unitVector F⟧ : FlagAlgebra ∅ₜ)
    have h_sq_zero :
        ℙ[φ₀] {φ : PositiveHomSpace ∅ₜ |
          ((φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧))^2 = 0} = 1 := by
      exact ae_zero_of_integral_eq_zero hg_nonneg hg_measurable hg_integrable hg_int_zero
    have h_sub_eq :
        {φ : PositiveHomSpace ∅ₜ |
          (φ ⟦unitVector F⟧) - (φ₀ ⟦unitVector F⟧) = 0}
        = {φ : PositiveHomSpace ∅ₜ | φ ⟦unitVector F⟧ = φ₀ ⟦unitVector F⟧} := by
      ext φ
      constructor
      · intro hφ
        exact sub_eq_zero.mp hφ
      · intro hφ
        exact sub_eq_zero.mpr hφ
    simpa [h_sub_eq] using h_sq_zero
  have h_all_unit_ae :
      ℙ[φ₀] (⋂ F : FinFlag ∅ₜ,
        {φ : PositiveHomSpace ∅ₜ | φ ⟦unitVector F⟧ = φ₀ ⟦unitVector F⟧}) = 1 := by
    refine prob_iInter_eq_one_of_all_prob_eq_one ?_ h_unit_ae
    intro F
    simpa [PositiveHom.map_smul, PositiveHom.map_one] using
      (forbidEq_set_measurable (σ := ∅ₜ)
        (⟦unitVector F⟧ : FlagAlgebra ∅ₜ)
        ((φ₀ ⟦unitVector F⟧) • (1 : FlagAlgebra ∅ₜ)))
  have hsubset_singleton :
      (⋂ F : FinFlag ∅ₜ,
        {φ : PositiveHomSpace ∅ₜ | φ ⟦unitVector F⟧ = φ₀ ⟦unitVector F⟧}) ⊆ {a₀}
    := by
    intro φ hφ
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have hval_eq : φ.val = a₀.val := by
      ext F
      have hF : φ ⟦unitVector F⟧ = φ₀ ⟦unitVector F⟧ := (Set.mem_iInter.mp hφ) F
      calc
        φ.val F = φ ⟦unitVector F⟧ := by
          symm
          simpa using (PositiveHomSpace.toPosHom_unitVector φ F)
        _ = φ₀ ⟦unitVector F⟧ := hF
        _ = (PositiveHomSpace.toPosHom a₀) ⟦unitVector F⟧ := by simp [ha₀_toPosHom]
        _ = a₀.val F := by simpa using (PositiveHomSpace.toPosHom_unitVector a₀ F)
    have hφa₀ : φ = a₀ := SetCoe.ext hval_eq
    simpa [Set.mem_singleton_iff] using hφa₀
  have hsingle' : ℙ[φ₀] ({a₀} : Set (PositiveHomSpace ∅ₜ)) = 1 := by
    apply le_antisymm
    · exact ProbabilityMeasure.apply_le_one ℙ[φ₀] _
    · calc
        1 = ℙ[φ₀] (⋂ F : FinFlag ∅ₜ,
              {a : PositiveHomSpace ∅ₜ | a ⟦unitVector F⟧ = φ₀ ⟦unitVector F⟧}) := by
                simpa using h_all_unit_ae.symm
        _ ≤ ℙ[φ₀] {a₀} := ProbabilityMeasure.apply_mono ℙ[φ₀] hsubset_singleton
  simpa [a₀, Set.setOf_eq_eq_singleton] using hsingle'

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

theorem forbidEq_emptyType_symm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (hf_eq_g : f =[F_forbid]₀ g)
    : g =[F_forbid]₀ f
  := by
  intro φ₀ hF_forbid
  exact (hf_eq_g φ₀ hF_forbid).symm

theorem forbidEq_emptyType_implies_forbidLE_emptyType
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (hf_eq_g : f =[F_forbid]₀ g)
    : f ≤[F_forbid]₀ g
  := by
  intro φ₀ hF_forbid
  exact le_of_eq (hf_eq_g φ₀ hF_forbid)

theorem forbidLE_emptyType_antisymm
    {F_forbid : FinFlag ∅ₜ} {f g : FlagAlgebra ∅ₜ}
    (hfg : f ≤[F_forbid]₀ g) (hgf : g ≤[F_forbid]₀ f)
    : f =[F_forbid]₀ g
  := by
  intro φ₀ hF_forbid
  exact le_antisymm (hfg φ₀ hF_forbid) (hgf φ₀ hF_forbid)

theorem forbidLE_emptyType_iff_forbidLE
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ)
    : (f ≤[F_forbid]₀ g) ↔ (f ≤[F_forbid] g)
  := by
  constructor
  · intro hfg φ₀ hσ hF_forbid
    let a₀ : PositiveHomSpace ∅ₜ := (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)
    let S : Set (PositiveHomSpace ∅ₜ) := ({a₀} : Set (PositiveHomSpace ∅ₜ))
    let A : Set (PositiveHomSpace ∅ₜ) := {φ | φ f ≤ φ g}
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have ha₀A : a₀ ∈ A := by
      have ha₀A' : a₀ f ≤ a₀ g := by
        simpa [ha₀_toPosHom] using (hfg φ₀ hF_forbid)
      simpa [A] using ha₀A'
    have hsubset : S ⊆ A := by
      intro φ hφ
      have hEq : φ = a₀ := by simpa [S] using hφ
      subst hEq
      exact ha₀A
    have hsingle : ℙ[φ₀] S = 1 := by
      simpa [S, a₀, Set.setOf_eq_eq_singleton] using
        probMeasure_extend_emptyType_positiveHom_singleton_eq_one φ₀
    apply le_antisymm
    · exact ProbabilityMeasure.apply_le_one (ℙ[φ₀]) A
    · calc
        1 = ℙ[φ₀] S := by simpa using hsingle.symm
        _ ≤ ℙ[φ₀] A := ProbabilityMeasure.apply_mono (ℙ[φ₀]) hsubset
  · intro hfg φ₀ hF_forbid
    have hσ : φ₀ ⟨∅ₜ⟩₀ > 0 := by simp [flagType_asEmptyTypeAlgebra_emptyType_eq_one]
    let a₀ : PositiveHomSpace ∅ₜ := (⟨φ₀.coe, ⟨φ₀, rfl⟩⟩ : PositiveHomSpace ∅ₜ)
    let S : Set (PositiveHomSpace ∅ₜ) := ({a₀} : Set (PositiveHomSpace ∅ₜ))
    let A : Set (PositiveHomSpace ∅ₜ) := {φ | φ f ≤ φ g}
    have ha₀_toPosHom : PositiveHomSpace.toPosHom a₀ = φ₀ := by
      apply PositiveHom.coe_injective
      calc
        PositiveHom.coe (PositiveHomSpace.toPosHom a₀) = a₀ := Classical.choose_spec a₀.property
        _ = PositiveHom.coe φ₀ := by rfl
    have hA : ℙ[φ₀] A = 1 := hfg φ₀ hσ hF_forbid
    have hsingle : ℙ[φ₀] S = 1 := by
      simpa [S, a₀, Set.setOf_eq_eq_singleton] using
        probMeasure_extend_emptyType_positiveHom_singleton_eq_one φ₀
    have hinter : ℙ[φ₀] (S ∩ A) = 1 := by
      apply prob_inter_eq_one_of_prob_eq_one
      · simp [S]
      · exact (forbidLE_set_measurable (σ := ∅ₜ) f g)
      · exact hsingle
      · exact hA
    have ha₀A : a₀ ∈ A := by
      by_contra ha₀A
      have hempty : (S ∩ A : Set (PositiveHomSpace ∅ₜ)) = ∅ := by
        ext φ
        constructor
        · intro hφ
          rcases hφ with ⟨hS, hAφ⟩
          have hEq : φ = a₀ := by simpa [S] using hS
          subst hEq
          exact (ha₀A hAφ).elim
        · intro hφ
          exact False.elim hφ
      have hzero : ℙ[φ₀] (S ∩ A) = 0 := by
        simp [hempty]
      have : (1 : NNReal) = 0 := by
        calc
          (1 : NNReal) = ℙ[φ₀] (S ∩ A) := by simpa using hinter.symm
          _ = 0 := hzero
      exact one_ne_zero this
    have ha₀A' : a₀ f ≤ a₀ g := by
      simpa [A] using ha₀A
    simpa [ha₀_toPosHom] using ha₀A'

theorem forbidEq_emptyType_iff_forbidEq
    (F_forbid : FinFlag ∅ₜ) (f g : FlagAlgebra ∅ₜ)
    : (f =[F_forbid]₀ g) ↔ (f =[F_forbid] g)
  := by
  constructor
  · intro hfg
    apply forbidLE_antisymm <;> rw [← forbidLE_emptyType_iff_forbidLE]
    · exact forbidEq_emptyType_implies_forbidLE_emptyType hfg
    · exact forbidEq_emptyType_implies_forbidLE_emptyType (forbidEq_emptyType_symm hfg)
  · intro hfg
    apply forbidLE_emptyType_antisymm <;> rw [forbidLE_emptyType_iff_forbidLE]
    · exact forbidEq_implies_forbidLE hfg
    · exact forbidEq_implies_forbidLE (forbidEq_symm hfg)

theorem downward_forbidLE_nonneg_emptyType
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : 0 ≤[F_forbid] f)
    : (0 : FlagAlgebra ∅ₜ) ≤[F_forbid]₀ ⟦f⟧₀
  := by
  intro φ₀ hF_forbid
  simp only [PositiveHom.map_zero]
  have hσ_nonneg : 0 ≤ φ₀ ⟨σ⟩₀ := positiveHom_unitVector_ge_zero φ₀ _
  rcases eq_or_lt_of_le hσ_nonneg with hσ_zero | hσ_pos
  · have hzero : φ₀ ⟦f⟧₀ = 0 := downward_zero_at_hom (σ := σ) φ₀ hσ_zero.symm f
    simp only [hzero, le_refl]
  · have hprob : ℙ[φ₀] {φ : PositiveHomSpace σ | 0 ≤ φ f} = 1 := by
      simpa using (hf φ₀ hσ_pos hF_forbid)
    have hprob_zero :
        ℙ[φ₀] {φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f} = 1 := by
      simpa [PositiveHom.map_zero] using hprob
    have hprob_zero_measure :
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))
          {φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f}) = 1 := by
      have hprob_zero_toNNReal :
          (((ℙ[φ₀] : Measure (PositiveHomSpace σ))
            {φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f}).toNNReal) = 1 := by
        simpa [ProbabilityMeasure.mk_apply] using hprob_zero
      rw [ENNReal.toNNReal_eq_one_iff] at hprob_zero_toNNReal
      exact hprob_zero_toNNReal
    have hcompl_zero :
        ((ℙ[φ₀] : Measure (PositiveHomSpace σ))
          ({φ : PositiveHomSpace σ | φ (0 : FlagAlgebra σ) ≤ φ f}ᶜ)) = 0 := by
      exact (prob_compl_eq_zero_iff
        (μ := (ℙ[φ₀] : Measure (PositiveHomSpace σ)))
        (forbidLE_set_measurable (σ := σ) (0 : FlagAlgebra σ) f)).mpr hprob_zero_measure
    have h_ae_zero :
        ∀ᵐ φ : PositiveHomSpace σ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
          φ (0 : FlagAlgebra σ) ≤ φ f := by
      exact (mem_ae_iff).2 hcompl_zero
    have h_ae : ∀ᵐ φ : PositiveHomSpace σ ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)), 0 ≤ φ f := by
      filter_upwards [h_ae_zero] with φ hφ
      simpa [PositiveHom.map_zero] using hφ
    have hint_nonneg : 0 ≤ ∫ φ : PositiveHomSpace σ, φ f ∂(ℙ[φ₀]) := by
      exact integral_nonneg_of_ae h_ae
    have hspec := probMeasure_extend_emptyType_positiveHom_spec (σ := σ) (φ₀ := φ₀) hσ_pos f
    have hden_pos : 0 < φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ := positiveHom_one_downward_pos hσ_pos
    have hfrac_nonneg : 0 ≤ (φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) := by
      simpa [hspec] using hint_nonneg
    have hmul_nonneg :
        0 ≤ ((φ₀ ⟦f⟧₀) / (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀)) * (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) := by
      exact mul_nonneg hfrac_nonneg (le_of_lt hden_pos)
    have : 0 ≤ φ₀ ⟦f⟧₀ := by
      have hden_ne : (φ₀ ⟦(1 : FlagAlgebra σ)⟧₀) ≠ 0 := ne_of_gt hden_pos
      simpa [hden_ne] using hmul_nonneg
    exact this

theorem downward_forbidLE_nonneg
    {F_forbid : FinFlag ∅ₜ} {f : FlagAlgebra σ} (hf : 0 ≤[F_forbid] f)
    : 0 ≤[F_forbid] ⟦f⟧₀
  := by
  have h0 : (0 : FlagAlgebra ∅ₜ) ≤[F_forbid]₀ ⟦f⟧₀ :=
    downward_forbidLE_nonneg_emptyType (σ := σ) hf
  exact (forbidLE_emptyType_iff_forbidLE F_forbid (0 : FlagAlgebra ∅ₜ) ⟦f⟧₀).1 h0

end Forbid
