import «LeanFlagAlgebras».SubflagListDensityProp
import «LeanFlagAlgebras».PositiveHom
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProductMeasure

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open Filter
open scoped Topology
open MeasureTheory

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
  Set.pi (Set.univ : Set (FinFlag σ)) (fun _ => (Set.Icc 0 1 : Set ℝ))

instance : FunLike (FlagDensitySpace σ) (FinFlag σ) ℝ where
  coe := fun a => a.val
  coe_injective' := by
    intro a b h
    ext F
    exact congrFun h F

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
noncomputable def coe (φ : PositiveHom σ) : FlagDensitySpace σ
  := {
    val := fun F => φ ⟦unitVector F⟧
    property := by
      simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
      constructor <;> (intro F; simp only)
      · exact positiveHom_unitVector_ge_zero φ F
      · exact positiveHom_unitVector_le_one φ F
  }

end PositiveHom

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
  obtain ⟨k, hk⟩ := flagListDensity₂_prod_approx F.2 G.2
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (F.1 + G.1) ^ k / (s n).1 < ε := by
    obtain ⟨N, hN⟩ := h_inc.eventually_gt ⌈(F.1 + G.1) ^ k / ε⌉₊
    use N
    intro n hn
    specialize hN n hn
    have hsn_pos : 0 < (s n).1 := by
      calc
        0 ≤ ⌈(↑F.fst + ↑G.fst) ^ k / ε⌉₊ := Nat.zero_le _
        _ < (s n).1 := hN
    apply Nat.lt_of_ceil_lt at hN
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hsn_pos)]
    rw [div_lt_iff₀ hε, mul_comm] at hN
    exact hN
  use N
  intro n hn
  specialize hk (s n).2
  specialize hN n hn
  simp only [LabeledGraph.size, Fintype.card_fin] at hk
  rw [← @Rat.cast_le _ _ ℝ] at hk
  simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_add] at hk
  simp only [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_abs]
  calc
    _ ≤ ((F.1 : ℝ) + (G.1 : ℝ)) ^ k / ((s n).1 : ℝ) := by
      rw [abs_sub_comm]
      exact hk
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

noncomputable def flagSeqMeasure
    (φ : PositiveHom σ)
    : Measure ((n : ℕ) → FlagWithSize σ (n ^ 2 + n₀))
  :=
  have : ∀ n, n ^ 2 + n₀ ≥ n₀ := fun n ↦ Nat.le_add_left n₀ (n ^ 2)
  Measure.infinitePi (fun n ↦ φ.toMeasure (this n))

notation "μ[" φ "]" => (flagSeqMeasure φ)

theorem flagSeqMeasure_converge_prob_one
    (φ : PositiveHom σ) (F : FinFlag σ) {ε : ℝ} (hε : 0 < ε)
    : μ[φ] { s | ∃ n₀, ∀ n ≥ n₀, |flagDensity₁ F.2 (s n) - φ.coe F| ≤ ε } = 1
  := by
  sorry

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

lemma nhds_basis_Icc_Nat_pos
    (a : ℝ)
    : (𝓝 a).HasBasis (fun (n : ℕ) ↦ 0 < n) fun n ↦ Set.Icc (a - 1 / n) (a + 1 / n)
  := by
  have h_ε_basis := nhds_basis_Icc_pos a
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
        _ ⊆ Set.Icc (a - ε) (a + ε) := by
          apply Set.Icc_subset_Icc <;> linarith
        _ ⊆ S := hε
  · intro ⟨n, npos, hn⟩
    use 1 / n
    constructor
    · simp only [one_div, inv_pos, Nat.cast_pos, npos]
    · exact hn

lemma real_mem_Icc_iff_abs_sub_le
    {a b x : ℝ}
    : x ∈ Set.Icc (a - b) (a + b) ↔ |x - a| ≤ b := by
  rw [abs_sub_le_iff, Set.mem_Icc]
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
    -- simp_rw [atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (φ.coe F))]
    -- measurability
    -- repeat apply Measurable.eval
    sorry
  have hS_measure : μ[φ] S = 1 := by
    dsimp [flagSeqMeasure]
    rw [← prob_compl_eq_zero_iff hS_measurable, Set.forall_compl]
    apply MeasureTheory.measure_exists_zero
    intro F
    simp_rw [atTop_basis.tendsto_iff (nhds_basis_Icc_Nat_pos (φ.coe F))]
    push_neg
    apply MeasureTheory.measure_exists_zero
    intro n
    simp_rw [real_mem_Icc_iff_abs_sub_le]
    rw [← prob_compl_eq_one_iff sorry]
    simp_rw [← forall_and_left, Set.forall_compl]
    push_neg
    by_cases hn : n = 0
    · subst hn
      simp only [lt_self_iff_false, Set.mem_Ici, CharP.cast_eq_zero, div_zero, abs_nonpos_iff,
        IsEmpty.forall_iff, and_self, exists_const, Set.setOf_true, measure_univ]
    · apply Nat.zero_lt_of_ne_zero at hn
      simp only [hn, Set.mem_Ici, forall_const, true_and]
      have hn_recip_pos : 0 < (1 / n : ℝ) := by
        rw [one_div, inv_pos]
        exact Nat.cast_pos.mpr hn
      exact flagSeqMeasure_converge_prob_one φ F hn_recip_pos
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
