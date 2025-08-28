import «LeanFlagAlgebras».PositiveHom
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.NumberTheory.ZetaValues

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open Filter
open scoped Topology
open MeasureTheory
open scoped ENNReal
open scoped ProbabilityTheory

abbrev FlagSeq (σ : FlagType (Fin n₀))
  :=
  ℕ → FinFlag σ

noncomputable def flagDensitySeq (s : FlagSeq σ) : ℕ → FinFlag σ → ℝ
  :=
  fun n F => (flagDensity₁ F.2 (s n).2 : ℝ)

theorem flagDensitySeq_comp_assoc
    (s : FlagSeq σ) (ϕ : ℕ → ℕ)
    : flagDensitySeq (s ∘ ϕ) = flagDensitySeq s ∘ ϕ
  :=
  rfl

def Increases (s : FlagSeq σ) : Prop
  :=
  StrictMono (fun n => (s n).1)

theorem Increases.eventually_gt
    {s : FlagSeq σ} (h_inc : Increases s) (ℓ : ℕ)
    : ∃ N, ∀ n ≥ N, (s n).1 > ℓ
  := by
  use ℓ + 1
  intro n hn
  calc
    (s n).1 ≥ n := h_inc.id_le n
    _ > ℓ := hn

theorem Increases.eventually_ge
    {s : FlagSeq σ} (h_inc : Increases s) (ℓ : ℕ)
    : ∃ N, ∀ n ≥ N, (s n).1 ≥ ℓ
  := by
  obtain ⟨N, hN⟩ := h_inc.eventually_gt ℓ
  use N
  exact fun n hn ↦ Nat.le_of_succ_le (hN n hn)

def ConvergesTo (s : FlagSeq σ) (a : FinFlag σ → ℝ) : Prop
  :=
  Increases s ∧
  Tendsto (flagDensitySeq s) atTop (𝓝 a)

theorem flagSeq_convergesTo_iff
    {s : FlagSeq σ} {a : FinFlag σ → ℝ}
    : ConvergesTo s a ↔
      Increases s ∧ ∀ (F : FinFlag σ), Tendsto (fun n => flagDensitySeq s n F) atTop (𝓝 (a F))
  := by
  constructor
  · intro ⟨h_inc, h_lim⟩
    constructor; exact h_inc
    intro F
    rw [nhds_pi, tendsto_pi] at h_lim
    exact h_lim F
  · intro ⟨h_inc, h_lim⟩
    constructor; exact h_inc
    rw [nhds_pi, tendsto_pi]
    exact h_lim

def FlagDensitySpace (σ : FlagType (Fin n₀)) : Set (FinFlag σ → ℝ)
  :=
  (Set.univ : Set (FinFlag σ)).pi (fun _ => (Set.Icc 0 1 : Set ℝ))

instance : FunLike (FlagDensitySpace σ) (FinFlag σ) ℝ where
  coe := fun a => a.val
  coe_injective' := by
    intro a b h
    ext F
    exact congrFun h F

instance : TopologicalSpace (PositiveHom σ) :=
  TopologicalSpace.induced (fun a ↦ ⟨fun F ↦ a ⟦unitVector F⟧, (by
    intro f _; simp; constructor
    · exact positiveHom_unitVector_ge_zero a f
    · exact positiveHom_unitVector_le_one a f
    : (fun F ↦ a ⟦unitVector F⟧) ∈ FlagDensitySpace σ)⟩)
    instTopologicalSpaceSubtype

theorem flagDensitySpace_mem_Icc_zero_one
    (a : FlagDensitySpace σ) (F : FinFlag σ)
    : a F ∈ Set.Icc 0 1 := by
  simp only [Set.mem_Icc]
  obtain ⟨val, property⟩ := a
  simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc] at property
  exact ⟨property.1 F, property.2 F⟩

theorem flagDensitySpace_compact
    : IsCompact (FlagDensitySpace σ)
  := by
  dsimp [FlagDensitySpace, Set.pi]
  simp only [Set.mem_univ, forall_true_left]
  apply isCompact_pi_infinite
  intro _
  exact isCompact_Icc

instance : CompactSpace (FlagDensitySpace σ)
  :=
  isCompact_iff_compactSpace.mp flagDensitySpace_compact

noncomputable instance : MetricSpace (FlagDensitySpace σ)
  :=
  TopologicalSpace.metrizableSpaceMetric (FlagDensitySpace σ)

noncomputable def flagDensitySeq' (s : FlagSeq σ) : ℕ → FlagDensitySpace σ
  :=
  fun n => {
    val := flagDensitySeq s n
    property := by
      simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
      constructor
      · intro F
        rw [flagDensitySeq, Rat.cast_nonneg]
        apply flagListDensity₁_ge_zero
      · intro F
        rw [flagDensitySeq, ← Rat.cast_one, Rat.cast_le]
        apply flagListDensity₁_le_one
  }

lemma flagDensitySpace_mem_nhds
    {a : FlagDensitySpace σ} {A : Set (FinFlag σ → ℝ)} (hA : A ∈ 𝓝 (a : FinFlag σ → ℝ))
    : { a' : FlagDensitySpace σ | a'.val ∈ A } ∈ 𝓝 a
  := by
  rw [mem_nhds_subtype]
  use A
  constructor
  · exact hA
  · rfl

theorem increasing_flagSeq_contain_convergent_subseq
    (s : FlagSeq σ) (hs_inc : Increases s)
    : ∃ (a : FlagDensitySpace σ) (ϕ : ℕ → ℕ), StrictMono ϕ ∧ ConvergesTo (s ∘ ϕ) a
  := by
  obtain ⟨a, ϕ, h_stmono, h_lim⟩ := CompactSpace.tendsto_subseq (flagDensitySeq' s)
  use a, ϕ
  constructor; exact h_stmono
  constructor
  · exact hs_inc.comp h_stmono
  · rw [flagDensitySeq_comp_assoc]
    intro A hA
    specialize h_lim (flagDensitySpace_mem_nhds hA)
    exact h_lim

namespace PositiveHom

@[coe]
protected noncomputable def coe (φ : PositiveHom σ) : FlagDensitySpace σ
  := {
    val := fun F => φ ⟦unitVector F⟧
    property := by
      simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
      constructor <;> intro F
      · exact positiveHom_unitVector_ge_zero φ F
      · exact positiveHom_unitVector_le_one φ F
  }

theorem coe_flag
    (φ : PositiveHom σ) (F : FinFlag σ)
    : φ.coe F = φ ⟦unitVector F⟧
  :=
  rfl

@[ext]
theorem coe_injective
    : Function.Injective (@PositiveHom.coe _ σ)
  := by
  intro φ φ' h
  simp only [PositiveHom.coe, Subtype.mk.injEq] at h
  apply congrFun at h
  ext f
  rcases Quotient.exists_rep f with ⟨frep, rfl⟩
  rw [flagVector_eq_sum_unitVector frep]
  simp_rw [sum_quot, smul_quot, map_sum, map_smul]
  apply Finset.sum_congr rfl
  rintro F -
  rw [h F]

end PositiveHom

def PositiveHomSpace (σ : FlagType (Fin n₀))
  :=
  Set.range (@PositiveHom.coe _ σ)

noncomputable def PositiveHomSpace.toPosHom
    (φ : PositiveHomSpace σ)
    : PositiveHom σ
  :=
  Classical.choose φ.property

instance : Nonempty (FlagDensitySpace σ) :=
  .intro ⟨fun _ ↦ 0, by simp [FlagDensitySpace]; exact fun _ ↦ zero_le_one⟩

theorem PositiveHom.isClosedMap_coe : IsClosedMap (@PositiveHom.coe _ σ) := by
  intro s h₁
  simp only [PositiveHom.coe, isClosed_induced_iff]
  sorry

theorem positiveHomSpace_isClosed
    : IsClosed (PositiveHomSpace σ)
  := by
  rw [isClosed_induced_iff]
  use PositiveHomSpace σ
  simp only [Subtype.val_injective, Set.preimage_image_eq, and_true]
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp
    <| IsClosedMap.isClosed_range PositiveHom.isClosedMap_coe
  simp only [FlagDensitySpace, Topology.isClosedEmbedding_iff, Topology.IsEmbedding.subtypeVal,
    Subtype.range_coe_subtype, Set.pi_univ_Icc, true_and]
  exact isClosed_Icc

instance : CompactSpace (PositiveHomSpace σ)
  :=
  isCompact_iff_compactSpace.mp (positiveHomSpace_isClosed.isCompact)

lemma tendsto_sum
    {ι : Type} [Fintype ι] (s : ι → ℕ → ℝ) (a : ι → ℝ)
    (h : ∀ i, Tendsto (s i) atTop (𝓝 (a i)))
    : Tendsto (fun n ↦ ∑ i, s i n) atTop (𝓝 (∑ i, a i))
  := by
  classical
  have : ∀ (I : Finset ι), Tendsto (fun n ↦ ∑ i ∈ I, s i n) atTop (𝓝 (∑ i ∈ I, a i)) := by
    intro I
    induction I using Finset.induction with
    | empty =>
      simp only [Finset.sum_empty]
      exact tendsto_const_nhds
    | @insert j I hj ih =>
      simp only [Finset.sum_insert hj]
      exact (h j).add ih
  exact this Finset.univ

theorem flagSeq_limit_chain_rule
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    {F : FinFlag σ} {ℓ : ℕ} (hℓ : ℓ ≥ F.1)
    : a F = ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G * a ⟨ℓ, G⟩
  := by
  rw [flagSeq_convergesTo_iff] at hs_conv
  obtain ⟨h_inc, h_lim⟩ := hs_conv
  apply @tendsto_nhds_unique _ _ _ _ (fun n ↦ flagDensitySeq s n F) atTop
  · exact h_lim F
  · dsimp [flagDensitySeq]
    have h_eventually_sum : ∀ᶠ (n : ℕ) in atTop, (flagDensity₁ F.2 (s n).2 : ℝ)
      = ∑ G : FlagWithSize σ ℓ, (flagDensity₁ F.2 G : ℝ) * flagDensity₁ G (s n).2 := by
      rw [eventually_atTop]
      obtain ⟨N, hN⟩ := h_inc.eventually_ge ℓ
      use N
      intro n hn
      simp_rw [← Rat.cast_mul, ← Rat.cast_sum, Rat.cast_inj]
      apply density_chain_rule₁₁
      · exact finFlag_size_ge_n₀ F
      · exact hℓ
      · exact hN n hn
    rw [tendsto_congr' h_eventually_sum]
    apply tendsto_sum
    intro G
    exact (h_lim ⟨ℓ, G⟩).const_smul (flagDensity₁ F.2 G)

theorem flagSeq_limit_linearExtension_respect_eqv
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    {f f' : FlagVector σ} (h : f ∼v f')
    : linearExtension a f = linearExtension a f'
  := by
  rw [← sub_eq_zero, ← linearExtension_sub]
  apply zeroSpace_eq_sum_spanElement _ at h
  rcases h with ⟨I, hI, c, v, hv, hk_sum⟩
  rw [hk_sum, linearExtension_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [linearExtension_smul]
  simp only [smul_eq_mul, mul_eq_zero]; right
  rcases hv i with ⟨F, ℓ, hℓ, hvi⟩
  dsimp [zeroElement, densityFlagSum] at hvi
  rw [hvi, linearExtension_sub, linearExtension_sum, sub_eq_zero]
  simp_rw [linearExtension_smul, linearExtension_unitVector]
  exact flagSeq_limit_chain_rule hs_conv hℓ

noncomputable def homFunFromFlagSeqLimit
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : FlagAlgebra σ → ℝ
  := by
  apply Quot.lift (linearExtension a)
  intro f f' f_eqv
  exact flagSeq_limit_linearExtension_respect_eqv hs_conv f_eqv

theorem homFunFromFlagSeqLimit_map_zero
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : homFunFromFlagSeqLimit hs_conv 0 = 0
  :=
  rfl

theorem homFunFromFlagSeqLimit_map_one
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : homFunFromFlagSeqLimit hs_conv 1 = 1
  := by
  show linearExtension a (unitVector 1) = 1
  simp only [linearExtension, unitVector_support, Finset.sum_singleton, unitVector_apply_self, one_smul]
  rw [flagSeq_convergesTo_iff] at hs_conv
  obtain ⟨_, h_lim⟩ := hs_conv
  apply @tendsto_nhds_unique _ _ _ _ (fun n ↦ flagDensitySeq s n 1) atTop
  · exact h_lim 1
  · have h_den_one : ∀ n, flagDensitySeq s n 1 = 1 := by
      intro n
      simp only [flagDensitySeq]
      rw [flagDensity_one, Rat.cast_one]
    rw [tendsto_congr h_den_one, tendsto_const_nhds_iff]

theorem homFunFromFlagSeqLimit_map_add
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a) (f g : FlagAlgebra σ)
    : homFunFromFlagSeqLimit hs_conv (f + g) = homFunFromFlagSeqLimit hs_conv f + homFunFromFlagSeqLimit hs_conv g
  := by
  rcases Quotient.exists_rep f with ⟨F, hF⟩
  rcases Quotient.exists_rep g with ⟨G, hG⟩
  rw [← hF, ← hG, ← add_quot]
  simp only [homFunFromFlagSeqLimit, Quotient.lift_mk]
  exact linearExtension_add a F G

theorem flagPairDensity_tendsto_flagDensity_mul
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a) (F G : FinFlag σ)
    : Tendsto (fun n ↦ (flagDensity₂ F.2 G.2 (s n).2 : ℝ)) atTop (𝓝 (a F * a G))
  := by
  rw [flagSeq_convergesTo_iff] at hs_conv
  obtain ⟨h_inc, h_lim⟩ := hs_conv
  have h_seq_mul : Tendsto (fun n ↦ flagDensitySeq s n F * flagDensitySeq s n G) atTop (𝓝 (a F * a G)) :=
    Tendsto.mul (h_lim F) (h_lim G)
  apply Tendsto.congr_dist h_seq_mul
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨c, _, hc⟩ := flagListDensity₂_prod_approx F.2 G.2
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, c / (s n).1 < ε := by
    obtain ⟨N, hN⟩ := h_inc.eventually_gt ⌈c / ε⌉₊
    use N
    intro n hn
    specialize hN n hn
    have hsn_pos : 0 < (s n).1 := by
      calc
        0 ≤ ⌈c / ε⌉₊ := Nat.zero_le _
        _ < (s n).1 := hN
    apply Nat.lt_of_ceil_lt at hN
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hsn_pos)]
    rw [div_lt_iff₀ hε, mul_comm] at hN
    exact hN
  use N
  intro n hn
  specialize hc (s n).2
  specialize hN n hn
  simp only [LabeledGraph.size, Fintype.card_fin] at hc
  rw [← @Rat.cast_le _ _ ℝ] at hc
  simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_div] at hc
  simp only [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_abs]
  calc
    _ ≤ c / ((s n).1 : ℝ) := by
      rw [abs_sub_comm]
      exact hc
    _ < ε := hN

theorem flagSeq_limit_linearExtension_flagMul
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a) (F G : FinFlag σ)
    : linearExtension a (flagMul F G) = a F * a G
  := by
  dsimp [flagMul, flagMulWithSize]
  simp_rw [linearExtension_sum, linearExtension_smul, linearExtension_unitVector]
  obtain ⟨h_inc, h_lim⟩ := flagSeq_convergesTo_iff.mp hs_conv
  apply @tendsto_nhds_unique _ _ _ _ (fun n ↦ (flagDensity₂ F.2 G.2 (s n).2 : ℝ)) atTop
  · have h_eventually_sum : ∀ᶠ (n : ℕ) in atTop, (flagDensity₂ F.2 G.2 (s n).2 : ℝ)
      = ∑ H : FlagWithSize σ (F.1 + G.1 - n₀), (flagDensity₂ F.2 G.2 H : ℝ) * flagDensity₁ H (s n).2 := by
      rw [eventually_atTop]
      obtain ⟨N, hN⟩ := h_inc.eventually_ge (F.1 + G.1 - n₀)
      use N
      intro n hn
      simp_rw [← Rat.cast_mul, ← Rat.cast_sum, Rat.cast_inj]
      apply density_chain_rule₂₁
      · exact finFlag_size_ge_n₀ F
      · exact finFlag_size_ge_n₀ G
      · exact le_tsub_add
      · exact hN n hn
    rw [tendsto_congr' h_eventually_sum]
    apply tendsto_sum
    intro H
    apply Tendsto.const_smul
    exact h_lim ⟨F.1 + G.1 - n₀, H⟩
  · exact flagPairDensity_tendsto_flagDensity_mul hs_conv F G

theorem homFunFromFlagSeqLimit_map_mul
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a) (f g : FlagAlgebra σ)
    : homFunFromFlagSeqLimit hs_conv (f * g) = homFunFromFlagSeqLimit hs_conv f * homFunFromFlagSeqLimit hs_conv g
  := by
  rcases Quotient.exists_rep f with ⟨frep, h_frep⟩
  rcases Quotient.exists_rep g with ⟨grep, h_grep⟩
  rw [← h_frep, ← h_grep, ← mul_quot]
  simp only [homFunFromFlagSeqLimit, Quotient.lift_mk]
  rw [flagVector_mul_eq_nested_sum]
  nth_rw 3 [flagVector_eq_sum_unitVector frep, flagVector_eq_sum_unitVector grep]
  simp_rw [linearExtension_sum]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  apply Finset.sum_congr rfl
  intro G _
  simp_rw [linearExtension_smul]
  rw [smul_mul_smul_comm]
  congr
  simp only [linearExtension_unitVector]
  exact flagSeq_limit_linearExtension_flagMul hs_conv F G

theorem homFunFromFlagSeqLimit_map_smul
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a) (r : ℝ) (f : FlagAlgebra σ)
    : homFunFromFlagSeqLimit hs_conv (r • f) = r * homFunFromFlagSeqLimit hs_conv f
  := by
  rcases Quotient.exists_rep f with ⟨F, hF⟩
  rw [← hF, ← smul_quot]
  simp only [homFunFromFlagSeqLimit, Quotient.lift_mk]
  exact linearExtension_smul a r F

theorem homFunFromFlagSeqLimit_commutes
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a) (r : ℝ)
    : homFunFromFlagSeqLimit hs_conv (Algebra.cast r) = r
  := by
  show homFunFromFlagSeqLimit hs_conv (r • 1) = r
  rw [homFunFromFlagSeqLimit_map_smul, homFunFromFlagSeqLimit_map_one, mul_one]

noncomputable def homFromFlagSeqLimit
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : Hom σ
  := {
    toFun := homFunFromFlagSeqLimit hs_conv
    map_zero' := homFunFromFlagSeqLimit_map_zero hs_conv
    map_one' := homFunFromFlagSeqLimit_map_one hs_conv
    map_add' := homFunFromFlagSeqLimit_map_add hs_conv
    map_mul' := homFunFromFlagSeqLimit_map_mul hs_conv
    commutes' := homFunFromFlagSeqLimit_commutes hs_conv
  }

noncomputable def positiveHomFromFlagSeqLimit
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : PositiveHom σ
  := {
    val := homFromFlagSeqLimit hs_conv
    property := by
      intro F
      simp only [homFromFlagSeqLimit, homFunFromFlagSeqLimit, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk, linearExtension, unitVector_support,
        Finset.sum_singleton, unitVector_apply_self, one_smul, ge_iff_le]
      rw [flagSeq_convergesTo_iff] at hs_conv
      obtain ⟨_, h_lim⟩ := hs_conv
      have h_den_nonneg : ∀ n, 0 ≤ flagDensitySeq s n F := by
        intro n
        simp only [flagDensitySeq, Rat.cast_nonneg]
        exact flagListDensity₁_ge_zero F.2 (s n).2
      exact ge_of_tendsto' (h_lim F) h_den_nonneg
  }

/- Theorem 3.3 (a) -/
theorem flagSeq_limit_mem_positiveHom
    (s : FlagSeq σ) {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : ∃ (φ : PositiveHom σ), φ.coe = a
  := by
  use positiveHomFromFlagSeqLimit hs_conv
  ext F
  show linearExtension a (unitVector F) = a F
  simp only [linearExtension, unitVector_support, Finset.sum_singleton, unitVector_apply_self, one_smul]

instance {ℓ : ℕ} : MeasurableSpace (FlagWithSize σ ℓ) := ⊤

noncomputable def PositiveHom.toPMF
    (φ : PositiveHom σ) {ℓ : ℕ} (hℓ : ℓ ≥ n₀)
    : PMF (FlagWithSize σ ℓ)
  := {
    val := fun (F : FlagWithSize σ ℓ) ↦ ENNReal.ofReal (φ ⟦unitVector ⟨ℓ, F⟩⟧)
    property := by
      have h := hasSum_fintype (fun F ↦ ENNReal.ofReal (φ ⟦unitVector ⟨ℓ, F⟩⟧))
      have h_sum : ∑ F : FlagWithSize σ ℓ, ENNReal.ofReal (φ ⟦unitVector ⟨ℓ, F⟩⟧) = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ ↦ positiveHom_unitVector_ge_zero φ ⟨ℓ, F⟩), ← ENNReal.ofReal_one]
        congr
        exact sum_positiveHom_unitVector_flagWithSize_eq_one φ ℓ hℓ
      rw [h_sum] at h
      exact h
  }

noncomputable def PositiveHom.toMeasure
    (φ : PositiveHom σ) {ℓ : ℕ} (hℓ : ℓ ≥ n₀)
    : Measure (FlagWithSize σ ℓ)
  :=
  (φ.toPMF hℓ).toMeasure

instance PositiveHom.toMeasure_isProbabilityMeasure
    (φ : PositiveHom σ) {ℓ : ℕ} (hℓ : ℓ ≥ n₀)
    : IsProbabilityMeasure (φ.toMeasure hℓ)
  :=
  PMF.toMeasure.isProbabilityMeasure (φ.toPMF hℓ)

noncomputable def randomDensity
    (F : FinFlag σ) (ℓ : ℕ)
    : FlagWithSize σ ℓ → ℝ
  :=
  fun G ↦ (flagDensity₁ F.2 G : ℝ)

theorem randomDensity_L2
    (φ : PositiveHom σ) (F : FinFlag σ) {ℓ : ℕ} (hℓ : ℓ ≥ n₀)
    : MemLp (randomDensity F ℓ) 2 (φ.toMeasure hℓ)
  :=
  MemLp.of_discrete

theorem randomDensity_expectation
    (φ : PositiveHom σ) (F : FinFlag σ) {ℓ : ℕ} (hℓ : ℓ ≥ F.1)
    : (φ.toMeasure (le_trans (finFlag_size_ge_n₀ F) hℓ))[randomDensity F ℓ] = φ.coe F
  := by
  dsimp [PositiveHom.toMeasure, PositiveHom.toPMF, randomDensity]
  rw [PMF.integral_eq_sum, PositiveHom.coe_flag]
  rw [unitVector_quot_eq_sum_density_mul_flagWithSize F ℓ hℓ, PositiveHom.map_sum]
  apply Finset.sum_congr rfl
  intro G _
  rw [PositiveHom.map_smul, mul_comm]
  have : φ ⟦unitVector ⟨ℓ, G⟩⟧ ≥ 0 := positiveHom_unitVector_ge_zero φ ⟨ℓ, G⟩
  rw [← ENNReal.toReal_ofReal this]
  congr

theorem randomDensity_second_moment
    (φ : PositiveHom σ) (F : FinFlag σ) {ℓ : ℕ} (hℓ : ℓ ≥ F.1)
    : ∫ G, (randomDensity F ℓ G) ^ 2 ∂(φ.toMeasure (le_trans (finFlag_size_ge_n₀ F) hℓ)) =
      ∑ G : FlagWithSize σ ℓ, (flagDensity₁ F.2 G) ^ 2 * φ.coe ⟨ℓ, G⟩
  := by
  dsimp [PositiveHom.toMeasure, PositiveHom.toPMF, randomDensity]
  simp_rw [PMF.integral_eq_sum, PositiveHom.coe_flag]
  apply Finset.sum_congr rfl
  intro G _
  rw [mul_comm]
  congr
  have : φ ⟦unitVector ⟨ℓ, G⟩⟧ ≥ 0 := positiveHom_unitVector_ge_zero φ ⟨ℓ, G⟩
  rw [← ENNReal.toReal_ofReal this]
  congr

theorem randomDensity_variance_bounded
    (φ : PositiveHom σ) (F : FinFlag σ)
    : ∃ (c : ℝ), c ≥ 0 ∧
      ∀ {ℓ : ℕ} (hℓ : ℓ ≥ 2 * F.1), Var[randomDensity F ℓ; φ.toMeasure (by linarith [finFlag_size_ge_n₀ F])] ≤ c / ℓ
  := by
  obtain ⟨c, cpos, hc⟩ := flagListDensity₂_prod_approx F.2 F.2
  use c
  constructor; exact Rat.cast_nonneg.mpr cpos
  intro ℓ hℓ
  rw [ProbabilityTheory.variance_eq_sub (randomDensity_L2 φ F _)]
  simp only [Pi.pow_apply]
  have hℓ' : ℓ ≥ F.1 := by linarith
  rw [randomDensity_expectation φ F hℓ', randomDensity_second_moment φ F hℓ']
  simp_rw [PositiveHom.coe_flag]
  calc
    _ = ∑ G : FlagWithSize σ ℓ,
        ((flagDensity₁ F.2 G) ^ 2 - flagDensity₂ F.2 F.2 G) * φ ⟦unitVector ⟨ℓ, G⟩⟧ := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      congr
      rw [pow_two, ← PositiveHom.map_mul, ← mul_quot, flagVector_mul_eq_nested_sum]
      simp_rw [← PositiveHom.map_smul, ← PositiveHom.map_sum]
      congr
      simp only [unitVector_support, Finset.sum_singleton, unitVector_apply_self, mul_one, one_smul]
      simp_rw [← smul_quot, ← sum_quot]
      apply Quotient.sound
      calc
        _ ∼v flagMulWithSize F F ℓ := by
          apply flagMul_indep_on_size
          linarith
        _ = ∑ G : FlagWithSize σ ℓ, flagDensity₂ F.2 F.2 G • unitVector ⟨ℓ, G⟩ := rfl
    _ ≤ ∑ G : FlagWithSize σ ℓ, (c / ℓ) * φ ⟦unitVector ⟨ℓ, G⟩⟧ := by
      apply Finset.sum_le_sum
      intro G _
      apply mul_le_mul_of_nonneg_right
      · calc
          _ ≤ (|flagDensity₂ F.2 F.2 G - (flagDensity₁ F.2 G) ^ 2| : ℝ) := by
            rw [abs_sub_comm]
            apply le_abs_self
          _ ≤ (c / ℓ : ℝ) := by
            specialize hc G
            have hG_size : G.out.size = ℓ := by
              simp only [LabeledGraph.size, Fintype.card_fin]
            rw [hG_size, ← @Rat.cast_le _ _ ℝ] at hc
            simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
              Rat.cast_natCast] at hc
            rw [pow_two]
            exact hc
      · exact positiveHom_unitVector_ge_zero φ ⟨ℓ, G⟩
    _ = c / ℓ := by
      rw [← Finset.mul_sum, ← PositiveHom.map_sum]
      have hℓ_ge_n₀ : ℓ ≥ n₀ := by linarith [finFlag_size_ge_n₀ F]
      rw [sum_flagWithSize_eq_one ℓ hℓ_ge_n₀, PositiveHom.map_one, mul_one]

example (a b : ℚ) (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  simp_all only [Rat.cast_le]

noncomputable def flagSeqMeasure
    (φ : PositiveHom σ)
    : Measure ((n : ℕ) → FlagWithSize σ (n ^ 2 + n₀))
  :=
  have : ∀ n, n ^ 2 + n₀ ≥ n₀ := fun n ↦ Nat.le_add_left n₀ (n ^ 2)
  Measure.infinitePi (fun n ↦ φ.toMeasure (this n))

instance flagSeqMeasure_isProbabilityMeasure
    (φ : PositiveHom σ)
    : IsProbabilityMeasure (flagSeqMeasure φ)
  := by
  dsimp [flagSeqMeasure]
  infer_instance

notation "μ{" φ "}" => (flagSeqMeasure φ)

def flagDensityErrorSet
    (φ : PositiveHom σ) (F : FinFlag σ) (ε : ℝ) (n : ℕ)
    : Set (∀ n, FlagWithSize σ (n ^ 2 + n₀))
  :=
  { s | |flagDensity₁ F.2 (s n) - φ.coe F| ≥ ε }

theorem flagDensityErrorSet_flagSeqMeasure
    (φ : PositiveHom σ) (F : FinFlag σ) (ε : ℝ) (n : ℕ)
    : μ{φ} (flagDensityErrorSet φ F ε n) = (φ.toMeasure (Nat.le_add_left n₀ (n ^ 2))) { G | |randomDensity F (n ^ 2 + n₀) G - φ.coe F| ≥ ε }
  := by
  have : flagDensityErrorSet φ F ε n = Set.pi ({n} : Finset ℕ) (
      fun m ↦ { G | |randomDensity F (m ^ 2 + n₀) G - φ.coe F| ≥ ε }
    ) := by
    simp only [Finset.coe_singleton, Set.singleton_pi, Set.preimage_setOf_eq, Function.eval]
    rfl
  rw [this]
  dsimp [flagSeqMeasure]
  rw [Measure.infinitePi_pi _ (by measurability)]
  simp only [Finset.prod_singleton]

theorem measure_flagDensityErrorSet_bounded
    (φ : PositiveHom σ) (F : FinFlag σ) {ε : ℝ} (hε : 0 < ε)
    : ∃ (c : ℝ), c ≥ 0 ∧
      ∀ n, (n > 0 ∧ n ^ 2 + n₀ ≥ 2 * F.1) → μ{φ} (flagDensityErrorSet φ F ε n) ≤ ENNReal.ofReal (c / (n ^ 2))
  := by
  choose c' c'pos hc' using randomDensity_variance_bounded φ F
  use c' / (ε ^ 2)
  constructor
  · exact div_nonneg c'pos (sq_nonneg ε)
  · intro n ⟨hn₁, hn₂⟩
    have hn₂' : n ^ 2 + n₀ ≥ F.1 := by linarith
    rw [flagDensityErrorSet_flagSeqMeasure φ F ε n, ← randomDensity_expectation φ F hn₂']
    have n_sq_add_n₀_ge_n₀ : n ^ 2 + n₀ ≥ n₀ := Nat.le_add_left n₀ (n ^ 2)
    let μ_n := φ.toMeasure n_sq_add_n₀_ge_n₀
    let rand_F := randomDensity F (n ^ 2 + n₀)
    have rand_F_L2 : MemLp rand_F 2 μ_n := randomDensity_L2 φ F n_sq_add_n₀_ge_n₀
    have chebyshev := @ProbabilityTheory.meas_ge_le_variance_div_sq _ _ μ_n _ rand_F rand_F_L2 ε hε
    apply le_trans chebyshev
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (c' / (n ^ 2 + n₀ : ℕ)) / (ε ^ 2) := by
        rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hε)]
        exact hc' hn₂
      _ = (c' / (ε ^ 2)) / (n ^ 2 + n₀ : ℕ) := div_right_comm c' _ _
      _ ≤ (c' / (ε ^ 2)) / (n ^ 2) := by
        apply div_le_div_of_nonneg_left
        · exact div_nonneg c'pos (sq_nonneg ε)
        · exact sq_pos_of_pos (Nat.cast_pos'.mpr hn₁)
        · simp only [Nat.cast_add, Nat.cast_pow, le_add_iff_nonneg_right, Nat.cast_nonneg]

lemma limsup_eq_forall_exists
    {α : Type} (s : ℕ → Set α)
    : limsup s atTop = { a | ∀ N, ∃ n ≥ N, a ∈ s n } := by
  rw [limsup_eq_iInf_iSup_of_nat, Set.setOf_forall]
  apply Set.iInter_congr
  intro N
  rw [Set.setOf_exists]
  apply Set.iUnion_congr
  intro n
  ext a
  simp only [ge_iff_le, Set.iSup_eq_iUnion, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]

lemma tsum_ENNReal_ne_infty_congr
    (f g : ℕ → ℝ) (hg_nonneg : ∀ n, g n ≥ 0)
    (hg : ∑' n, ENNReal.ofReal (g n) ≠ ∞) (h : ∀ᶠ n in atTop, f n = g n)
    : ∑' n, ENNReal.ofReal (f n) ≠ ∞
  := by
  have hg_summable : Summable g := by
    rw [← NNReal.summable_mk hg_nonneg]
    have : (fun n ↦ (⟨g n, hg_nonneg n⟩ : NNReal)) = ENNReal.toNNReal ∘ (fun n ↦ ENNReal.ofReal (g n)) := by
      funext n
      congr
      exact left_eq_sup.mpr (hg_nonneg n)
    rw [this]
    exact ENNReal.summable_toNNReal_of_tsum_ne_top hg
  rw [← summable_congr_atTop h] at hg_summable
  exact Summable.tsum_ofReal_ne_top hg_summable

lemma tsum_ENNReal_le_tsum_ne_infty
    (f : ℕ → ENNReal) (g : ℕ → ℝ) (hf_ne_top : ∀ n, f n ≠ ∞) (hg_nonneg : ∀ n, g n ≥ 0)
    (hg : ∑' n, ENNReal.ofReal (g n) ≠ ∞) (h : ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal (g n))
    : ∑' n, f n ≠ ∞
  := by
  have : ∑' n, f n = ∑' n, ENNReal.ofReal (ENNReal.toReal (f n)) := by
    apply tsum_congr
    intro n
    rw [ENNReal.ofReal_toReal (hf_ne_top n)]
  rw [this]
  let g' : ℕ → ENNReal := fun n ↦ ENNReal.ofReal (max (ENNReal.toReal (f n)) (g n))
  have h_fsum_le_g'sum : ∑' n, ENNReal.ofReal (ENNReal.toReal (f n)) ≤ ∑' n, g' n := by
    apply ENNReal.tsum_le_tsum
    intro n
    exact ENNReal.ofReal_le_ofReal (le_max_left (f n).toReal (g n))
  refine ne_top_of_le_ne_top ?_ h_fsum_le_g'sum
  apply tsum_ENNReal_ne_infty_congr (fun n ↦ max (ENNReal.toReal (f n)) (g n)) g hg_nonneg hg
  simp_rw [max_eq_right_iff]
  rw [eventually_atTop] at *
  obtain ⟨M, hM⟩ := h
  use M
  intro m hm
  exact ENNReal.toReal_le_of_le_ofReal (hg_nonneg m) (hM m hm)

theorem flagSeqMeasure_error_prob_zero
    (φ : PositiveHom σ) (F : FinFlag σ) {ε : ℝ} (hε : 0 < ε)
    : μ{φ} { s | ∀ N, ∃ n ≥ N, |flagDensity₁ F.2 (s n) - φ.coe F| ≥ ε } = 0
  := by
  let E : ℕ → Set (∀ n, FlagWithSize σ (n ^ 2 + n₀)) := flagDensityErrorSet φ F ε
  show μ{φ} { s | ∀ N, ∃ n ≥ N, s ∈ E n } = 0
  rw [← limsup_eq_forall_exists]
  apply measure_limsup_atTop_eq_zero
  obtain ⟨c, hc, hE⟩ := measure_flagDensityErrorSet_bounded φ F hε
  apply tsum_ENNReal_le_tsum_ne_infty _ (fun n ↦ c / (n ^ 2))
  · exact fun n ↦ measure_ne_top (flagSeqMeasure φ) (E n)
  · exact fun n ↦ div_nonneg hc (sq_nonneg _)
  · simp_rw [div_eq_mul_one_div c, ENNReal.ofReal_mul hc]
    rw [ENNReal.tsum_mul_left]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply Summable.tsum_ofReal_ne_top
    exact ⟨_, hasSum_zeta_two⟩
  · rw [eventually_atTop]
    use max (2 * F.1) 1
    intro n hn
    have hn₁ : n > 0 := le_of_max_le_right hn
    have hn₂ : n ^ 2 + n₀ ≥ 2 * F.1 := by
      calc
        _ ≥ n ^ 2 := Nat.le_add_right (n ^ 2) n₀
        _ ≥ n := Nat.le_pow (by norm_num)
        _ ≥ 2 * F.1 := le_of_max_le_left hn
    exact hE n ⟨hn₁, hn₂⟩

lemma prop_set_cases (P : Set Prop) : P = ∅ ∨ P = {True} ∨ P = {False} ∨ P = {True, False} := by
  rw [← Set.subset_pair_iff_eq, Set.subset_pair_iff]
  intro p hp
  exact Classical.propComplete p

lemma Set.forall_compl
    {α β : Type} (p : α → β → Prop)
    : { b | ∀ a, p a b }ᶜ = { b | ∃ a, ¬p a b }
  := by
  ext b
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]

lemma MeasureTheory.measure_exists_zero
    {α β : Type} [Countable α] [MeasurableSpace β] {μ : Measure β} {p : α → β → Prop}
    (hμ : ∀ a, μ { b | p a b } = 0)
    : μ { b | ∃ a, p a b } = 0 := by
  rw [Set.setOf_exists, ← nonpos_iff_eq_zero]
  apply le_trans (measure_iUnion_le _)
  apply tsum_nonpos
  intro a
  simp_all only [le_refl]

lemma nhds_basis_Ioo_Nat_pos
    (a : ℝ)
    : (𝓝 a).HasBasis (fun (n : ℕ) ↦ 0 < n) fun n ↦ Set.Ioo (a - 1 / n) (a + 1 / n)
  := by
  have h_ε_basis := nhds_basis_Ioo_pos a
  rw [hasBasis_iff] at *
  intro S
  rw [h_ε_basis S]
  constructor
  · intro ⟨ε, εpos, hε⟩
    obtain ⟨n, npos, hn⟩ : ∃ (n : ℕ), 0 < n ∧ 1 / n ≤ ε := by
      use ⌈1 / ε⌉₊
      have : 0 < ⌈1 / ε⌉₊ := by
        rw [Nat.ceil_pos]
        exact one_div_pos.mpr εpos
      constructor
      · exact this
      · rw [← one_div_le εpos (Nat.cast_pos'.mpr this)]
        exact Nat.le_ceil (1 / ε)
    use n
    constructor
    · exact npos
    · calc
        _ ⊆ Set.Ioo (a - ε) (a + ε) := by
          apply Set.Ioo_subset_Ioo <;> linarith
        _ ⊆ S := hε
  · intro ⟨n, npos, hn⟩
    use 1 / n
    constructor
    · simp only [one_div, inv_pos, Nat.cast_pos, npos]
    · exact hn

lemma real_mem_Ioo_iff_abs_sub_lt
    {a b x : ℝ}
    : x ∈ Set.Ioo (a - b) (a + b) ↔ |x - a| < b
  := by
  rw [Set.mem_Ioo, abs_sub_lt_iff]
  constructor <;> (intro; constructor) <;> linarith

/- Theorem 3.3 (b) -/
theorem positiveHom_as_flagSeq_limit
    (φ : PositiveHom σ)
    : ∃ (s : FlagSeq σ), ConvergesTo s φ.coe
  := by
  let S : Set (∀ n, FlagWithSize σ (n ^ 2 + n₀)) :=
    { s | ∀ (F : FinFlag σ), Tendsto (fun n ↦ (flagDensity₁ F.2 (s n) : ℝ)) atTop (𝓝 (φ.coe F)) }
  have hS_measurable : MeasurableSet S := by
    rw [measurableSet_setOf]
    apply Measurable.forall
    intro F
    have : Measurable fun (s : ∀ n, FlagWithSize σ (n ^ 2 + n₀)) ↦ Tendsto (fun n ↦ (flagDensity₁ F.2 (s n) : ℝ)) atTop (𝓝 (φ.coe F)) := by
      rw [← measurableSet_setOf]
      apply measurableSet_tendsto (𝓝 (φ.coe F))
      measurability
    intro P hP
    rcases prop_set_cases P with hP | hP | hP | hP <;> rw [hP]
    · exact MeasurableSet.empty
    · simp only [Set.preimage_singleton_true, measurableSet_setOf]
      exact this
    · simp only [Set.preimage_singleton_false, measurableSet_setOf]
      apply Measurable.not
      exact this
    · rw [← Set.univ_eq_true_false]
      simp only [Set.preimage_univ, MeasurableSet.univ]
  have hS_measure : μ{φ} S = 1 := by
    dsimp [flagSeqMeasure]
    rw [← prob_compl_eq_zero_iff hS_measurable, Set.forall_compl]
    apply MeasureTheory.measure_exists_zero
    intro F
    simp_rw [atTop_basis.tendsto_iff (nhds_basis_Ioo_Nat_pos (φ.coe F))]
    push_neg
    apply MeasureTheory.measure_exists_zero
    intro n
    simp_rw [real_mem_Ioo_iff_abs_sub_lt]
    simp only [Set.mem_Ici, forall_const]
    simp_rw [← forall_and_left]
    by_cases hn : n = 0
    · subst hn
      simp only [lt_self_iff_false, CharP.cast_eq_zero, div_zero, false_and, forall_const, Set.setOf_false, measure_empty]
    · apply Nat.zero_lt_of_ne_zero at hn
      simp only [hn, true_and, not_lt]
      have hn_recip_pos : 0 < (1 / n : ℝ) := by
        rw [one_div, inv_pos]
        exact Nat.cast_pos.mpr hn
      exact flagSeqMeasure_error_prob_zero φ F hn_recip_pos
  obtain ⟨s, hs⟩ : ∃ s, s ∈ S := by
    rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
    contrapose hS_measure
    simp only [ne_eq, not_not] at hS_measure
    rw [hS_measure]
    simp only [measure_empty, zero_ne_one, not_false_eq_true]
  dsimp [S] at hs
  use fun n ↦ ⟨n ^ 2 + n₀, s n⟩
  rw [flagSeq_convergesTo_iff]
  constructor
  · intro n m hnm
    simp only [add_lt_add_iff_right]
    exact Nat.pow_lt_pow_left hnm (by norm_num)
  · exact hs
