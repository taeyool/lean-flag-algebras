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

def ConvergesTo (s : FlagSeq σ) (a : FinFlag σ → ℝ) : Prop
  :=
  Increases s ∧
  Tendsto (flagDensitySeq s) atTop (𝓝 a)

theorem flagSeq_convergesTo_iff
    (s : FlagSeq σ) (a : FinFlag σ → ℝ)
    : ConvergesTo s a ↔
      Increases s ∧ ∀ (F : FinFlag σ), Tendsto (fun n => flagDensitySeq s n F) atTop (𝓝 (a F))
  := by
  constructor
  · intro ⟨h_inc, h_lim⟩
    constructor; exact h_inc
    intro F
    rw [nhds_pi, Filter.tendsto_pi] at h_lim
    exact h_lim F
  · intro ⟨h_inc, h_lim⟩
    constructor; exact h_inc
    rw [nhds_pi, Filter.tendsto_pi]
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

theorem flagSeq_limit_chain_rule
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    {F : FinFlag σ} {ℓ : ℕ} (hℓ : ℓ ≥ F.1)
    : a F = ∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G • a ⟨ℓ, G⟩
  := by
  sorry

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
  nth_rw 1 [unitVector]
  rw [linearExtension_single_one]
  simp_rw [linearExtension_smul, unitVector, linearExtension_single_one]
  exact flagSeq_limit_chain_rule hs_conv hℓ

noncomputable def homFunFromFlagSeqLimit
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : FlagAlgebra σ → ℝ
  := by
  apply Quot.lift (linearExtension a)
  intro f f' f_eqv
  exact flagSeq_limit_linearExtension_respect_eqv hs_conv f_eqv

noncomputable def homFromFlagSeqLimit
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : Hom σ
  := {
    toFun := homFunFromFlagSeqLimit hs_conv
    map_zero' := sorry
    map_one' := sorry
    map_add' := sorry
    map_mul' := sorry
    commutes' := sorry
  }

noncomputable def positiveHomFromFlagSeqLimit
    {s : FlagSeq σ} {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : PositiveHom σ
  := {
    val := homFromFlagSeqLimit hs_conv
    property := sorry
  }

theorem flagSeq_limit_mem_positiveHom
    (s : FlagSeq σ) {a : FlagDensitySpace σ} (hs_conv : ConvergesTo s a)
    : ∃ (φ : PositiveHom σ), φ.coe = a
  := by
  use positiveHomFromFlagSeqLimit hs_conv
  sorry

theorem positiveHom_as_flagSeq_limit
    (φ : PositiveHom σ)
    : ∃ (s : FlagSeq σ), ConvergesTo s φ.coe
  := by
  sorry
