import «LeanFlagAlgebras».SubflagListDensityProp
import «LeanFlagAlgebras».PositiveHom
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Sequences

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

open Filter
open scoped Topology

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

theorem Increases.eventually_ge
    {s : FlagSeq σ} (h_inc : Increases s) (ℓ : ℕ)
    : ∃ N, ∀ n ≥ N, (s n).1 ≥ ℓ
  := by
  use ℓ
  intro n hn
  calc
    (s n).1 ≥ n := h_inc.id_le n
    _ ≥ ℓ := hn

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

example (a b : ℚ) (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  rw [Rat.cast_le]
  exact h

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
    sorry
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

theorem flagSeq_limit_mem_positiveHom
    (s : FlagSeq σ) {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : ∃ (φ : PositiveHom σ), φ.coe = a
  := by
  use positiveHomFromFlagSeqLimit hs_conv
  ext F
  show linearExtension a (unitVector F) = a F
  simp only [linearExtension, unitVector_support, Finset.sum_singleton, unitVector_apply_self, one_smul]

theorem positiveHom_as_flagSeq_limit
    (φ : PositiveHom σ)
    : ∃ (s : FlagSeq σ), ConvergesTo s φ.coe
  := by
  sorry
