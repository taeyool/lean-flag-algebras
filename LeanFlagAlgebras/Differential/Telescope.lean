import LeanFlagAlgebras.Differential.DeleteFinset
import LeanFlagAlgebras.Differential.Hitting
import LeanFlagAlgebras.Differential.Ensemble

/-! # Telescoping deletion estimates (Razborov's (29)–(33), finite part)

The finite machinery for `bad_vertex_negPart_tendsto_zero`:

* `integral_toMeasure_eq_root_average` — the empirical integral of any
  function of the rooted evaluation against `G.toMeasure` is the *uniform*
  average over the `ℓ` roots of `G` (the label-extension weights
  `q(F') = |Iso(F')|/ℓ` regroup into root counts);
* `card_bad_ge_of_average_ge` — Markov: if the average of a `[0,B]`-valued
  root statistic is at least `ε`, roots with value `≥ ε/2` have density
  `≥ ε/(2B)`;
* `pdensityVec_deleteFinset_stability` — deleting `|W|` vertices moves any
  model combination's density by at most `|W|·‖∂₁g‖₁/(n−|W|)`;
* `pdensityVec_deleteFinset_descent` — deleting `|W|` *uniformly bad* roots
  (each `p^{(N,v)}(∂₁g) ≤ −ε` in the original host) drives the density down
  by `|W|·(ε−corr)/n`, the hitting estimate (`Hitting.lean`) supplying the
  correction `corr` for evaluating badness in the partially deleted host. -/

open MeasureTheory Filter
open scoped Topology

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

/-! ## The empirical integral as a root average -/

/-- Every label extension of an `(ℓ+1)`-vertex model at the one-vertex type is
realised by rooting the model at one of its vertices. -/
theorem exists_realising_root {ℓ : ℕ} (M : FlagWithSize ∅ₜ (ℓ + 1))
    (F' : FlagWithSize vertexType (ℓ + 1)) (hF' : F' ∈ labelExtensions M vertexType)
    : ∃ r₀ : Fin (ℓ + 1), (⟦rootedAt M.out r₀⟧ : FlagWithSize vertexType (ℓ + 1)) = F'
  := by
  rw [labelExtensions_eq_filter, Finset.mem_filter] at hF'
  have h2 : (⟦unlabeledGraph F'.out⟧ : FlagWithSize ∅ₜ (ℓ + 1)) = M := by
    rw [← unlabel_out F']
    exact hF'.2
  have hψ : unlabeledGraph F'.out ∼f M.out := Quotient.mk_eq_iff_out.mp h2
  obtain ⟨ψ⟩ := hψ
  refine ⟨ψ.graph_iso (F'.out.type_embed 0), ?_⟩
  have hiso : F'.out ∼f rootedAt M.out (ψ.graph_iso (F'.out.type_embed 0)) := by
    refine ⟨{ graph_iso := ψ.graph_iso, type_preserve := ?_ }⟩
    funext x
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    rfl
  calc (⟦rootedAt M.out (ψ.graph_iso (F'.out.type_embed 0))⟧
        : FlagWithSize vertexType (ℓ + 1))
      = ⟦F'.out⟧ := Quotient.sound (flagEqv.symm hiso)
    _ = F' := Quotient.out_eq F'

/-- Every rooting of an `(ℓ+1)`-vertex model is a label extension of it. -/
theorem rootedAt_mem_labelExtensions {ℓ : ℕ} (M : FlagWithSize ∅ₜ (ℓ + 1))
    (r : Fin (ℓ + 1))
    : (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1))
        ∈ labelExtensions M vertexType
  := by
  rw [labelExtensions_eq_filter, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show (⟦unlabeledGraph (rootedAt M.out r)⟧ : FlagWithSize ∅ₜ (ℓ + 1)) = M
  rw [unlabeledGraph_rootedAt]
  exact Quotient.out_eq M

/-- **The root-average identity**: the empirical integral of any bounded
measurable function of the rooted evaluation of `g` against the
random-labelling measure of an `(ℓ+1)`-vertex model is the uniform average
over its `ℓ+1` roots. -/
theorem integral_toMeasure_eq_root_average {ℓ : ℕ}
    (M : FlagWithSize ∅ₜ (ℓ + 1))
    (hM : flagDensity₁ vertexType.toEmptyTypeFlag M > 0)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) {c : ℝ} (hΨb : ∀ x, |Ψ x| ≤ c)
    (g : FlagVector vertexType)
    : ∫ a, Ψ (densityEvalFun g a)
        ∂(FinFlag.toMeasure (⟨ℓ + 1, M⟩ : FinFlag ∅ₜ) hM)
      = (1 / ((ℓ : ℝ) + 1)) * ∑ r : Fin (ℓ + 1), Ψ (pEval g M.out r)
  := by
  have hmeas : Measurable (fun a : FlagDensitySpace vertexType => Ψ (densityEvalFun g a)) :=
    hΨm.comp (measurable_densityEvalFun g)
  have hint : Integrable (fun a : FlagDensitySpace vertexType => Ψ (densityEvalFun g a))
      (FinFlag.toMeasure (⟨ℓ + 1, M⟩ : FinFlag ∅ₜ) hM) :=
    integrable_of_bounded hmeas c (fun a => hΨb _)
  rw [FinFlag.integral_toMeasure_eq_sum (⟨ℓ + 1, M⟩ : FinFlag ∅ₜ) hM _ hint]
  have hsum1 : ∑ F'' ∈ labelExtensions M vertexType,
      ((downwardNormalizingFactor F'' : ℚ) : ℝ) = 1 := by
    rw [← Rat.cast_sum,
      sum_downwardNormalizingFactor_labelExtensions_vertexType M (by omega), Rat.cast_one]
  -- the root fibres partition the vertex set
  have hpart : (Finset.univ : Finset (Fin (ℓ + 1)))
      = (labelExtensions M vertexType).biUnion (fun F' =>
          Finset.univ.filter (fun r =>
            (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F')) := by
    apply Finset.ext
    intro r
    constructor
    · intro _
      rw [Finset.mem_biUnion]
      refine ⟨⟦rootedAt M.out r⟧, rootedAt_mem_labelExtensions M r, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ r, rfl⟩
    · intro _
      exact Finset.mem_univ r
  have hdisj : ∀ F₁ ∈ labelExtensions M vertexType,
      ∀ F₂ ∈ labelExtensions M vertexType, F₁ ≠ F₂ →
      Disjoint
        (Finset.univ.filter (fun r =>
          (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F₁))
        (Finset.univ.filter (fun r =>
          (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F₂)) := by
    intro F₁ _ F₂ _ hne
    rw [Finset.disjoint_left]
    intro r h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact hne (h₁.2 ▸ h₂.2)
  calc ∑ F' ∈ labelExtensions M vertexType,
        ((downwardNormalizingFactor F' : ℝ)
          / ∑ F'' ∈ labelExtensions M vertexType, (downwardNormalizingFactor F'' : ℝ))
        * Ψ (densityEvalFun g
            (funFromFlagWithSizeToFlagDensitySpace vertexType (ℓ + 1) F'))
      = ∑ F' ∈ labelExtensions M vertexType, (1 / ((ℓ : ℝ) + 1))
          * (((Finset.univ.filter (fun r =>
              (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F')).card : ℝ)
            * Ψ (densityEvalFun g
                (funFromFlagWithSizeToFlagDensitySpace vertexType (ℓ + 1) F'))) := by
        apply Finset.sum_congr rfl
        intro F' hF'
        rw [hsum1, div_one]
        obtain ⟨r₀, hr₀⟩ := exists_realising_root M F' hF'
        rw [downwardNormalizingFactor_vertexType F',
          isomorphismCount_eq_card_roots M.out F' r₀ hr₀]
        push_cast
        ring
    _ = (1 / ((ℓ : ℝ) + 1)) * ∑ F' ∈ labelExtensions M vertexType,
          ∑ r ∈ Finset.univ.filter (fun r =>
              (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F'),
            Ψ (pEval g M.out r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro F' _
        congr 1
        have hconst : ∀ r ∈ Finset.univ.filter (fun r =>
            (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F'),
            Ψ (pEval g M.out r)
              = Ψ (densityEvalFun g
                  (funFromFlagWithSizeToFlagDensitySpace vertexType (ℓ + 1) F')) := by
          intro r hr
          rw [Finset.mem_filter] at hr
          rw [pEval_fin, ← densityEvalFun_emp, hr.2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    _ = (1 / ((ℓ : ℝ) + 1)) * ∑ r : Fin (ℓ + 1), Ψ (pEval g M.out r) := by
        congr 1
        have hpd : Set.PairwiseDisjoint
            ((↑(labelExtensions M vertexType) : Set (FlagWithSize vertexType (ℓ + 1))))
            (fun F' => Finset.univ.filter (fun r =>
              (⟦rootedAt M.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F')) := by
          intro F₁ h₁ F₂ h₂ hne
          exact hdisj F₁ h₁ F₂ h₂ hne
        conv_rhs => rw [hpart]
        rw [Finset.sum_biUnion hpd]

/-- Sigma-generic wrapper of the root-average identity. -/
theorem integral_toMeasure_eq_root_average' (G : FinFlag ∅ₜ) (h1 : 1 ≤ G.1)
    (hG : flagDensity₁ vertexType.toEmptyTypeFlag G.2 > 0)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) {c : ℝ} (hΨb : ∀ x, |Ψ x| ≤ c)
    (g : FlagVector vertexType)
    : ∫ a, Ψ (densityEvalFun g a) ∂(G.toMeasure hG)
      = (1 / (G.1 : ℝ)) * ∑ r : Fin G.1, Ψ (pEval g G.2.out r)
  := by
  obtain ⟨L, M⟩ := G
  dsimp only at h1 hG ⊢
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, L = ℓ + 1 := ⟨L - 1, by omega⟩
  have h := integral_toMeasure_eq_root_average M hG Ψ hΨm hΨb g
  rw [h]
  push_cast
  ring

/-! ## Markov: extracting a positive density of bad roots -/

/-- If the average of a `[0,B]`-valued root statistic is at least `ε`, the
roots with value at least `ε/2` have density at least `ε/(2B)`. -/
theorem card_bad_ge_of_average_ge {n : ℕ} (x : Fin n → ℝ) {ε B : ℝ}
    (hB : 0 < B) (hb : ∀ r, x r ≤ B) (hnn : ∀ r, 0 ≤ x r)
    (havg : ε ≤ (1 / (n : ℝ)) * ∑ r, x r)
    : ε / (2 * B) * n ≤ ((Finset.univ.filter (fun r => ε / 2 ≤ x r)).card : ℝ)
  := by
  by_cases hε : ε ≤ 0
  · have h1 : ε / (2 * B) * n ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact div_nonpos_of_nonpos_of_nonneg hε (by linarith)
      · positivity
    exact le_trans h1 (Nat.cast_nonneg _)
  push_neg at hε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- empty index type: the average is `0`, contradicting `ε > 0`
    exfalso
    simp only [Nat.cast_zero, div_zero, zero_mul] at havg
    linarith
  have hncast : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set Bad := Finset.univ.filter (fun r : Fin n => ε / 2 ≤ x r) with hBad
  have hsum_ub : ∑ r, x r ≤ (Bad.card : ℝ) * B + (n : ℝ) * (ε / 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => ε / 2 ≤ x r)]
    apply add_le_add
    · calc ∑ r ∈ Bad, x r ≤ ∑ _r ∈ Bad, B := Finset.sum_le_sum (fun r _ => hb r)
        _ = (Bad.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    · calc ∑ r ∈ Finset.univ.filter (fun r => ¬ε / 2 ≤ x r), x r
          ≤ ∑ _r ∈ Finset.univ.filter (fun r => ¬ε / 2 ≤ x r), (ε / 2) :=
            Finset.sum_le_sum (fun r hr =>
              le_of_lt (not_le.mp (Finset.mem_filter.mp hr).2))
        _ = ((Finset.univ.filter (fun r => ¬ε / 2 ≤ x r)).card : ℝ) * (ε / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (ε / 2) := by
            apply mul_le_mul_of_nonneg_right ?_ (by linarith)
            have hcle : (Finset.univ.filter (fun r : Fin n => ¬ε / 2 ≤ x r)).card ≤ n := by
              calc (Finset.univ.filter (fun r : Fin n => ¬ε / 2 ≤ x r)).card
                  ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
                _ = n := by rw [Finset.card_univ, Fintype.card_fin]
            exact_mod_cast hcle
  have hsum_lb : ε * n ≤ ∑ r, x r := by
    have h2 := mul_le_mul_of_nonneg_right havg (le_of_lt hncast)
    calc ε * n ≤ (1 / (n : ℝ)) * (∑ r, x r) * n := h2
      _ = ∑ r, x r := by field_simp
  have hkey : ε * n / 2 ≤ (Bad.card : ℝ) * B := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * B)]
  calc ε * n ≤ 2 * ((Bad.card : ℝ) * B) := by linarith
    _ = (Bad.card : ℝ) * (2 * B) := by ring

/-! ## Telescoping stability: deletion barely moves model densities -/

/-- **(S)** Deleting `|W|` vertices moves the density of any model
combination by at most `|W| · ‖∂₁g‖₁ / (n − |W|)`. -/
theorem pdensityVec_deleteFinset_stability {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector ∅ₜ) (N : LabeledGraph ∅ₜ V) (W : Finset V)
    (hW : W.card < Fintype.card V)
    (hfit : ∀ M ∈ g.support, M.1 + W.card + 1 ≤ Fintype.card V)
    : |pdensityVec g (deleteFinset N W) - pdensityVec g N|
      ≤ (W.card : ℝ)
          * (∑ F ∈ (partialVertexVec g).support, |partialVertexVec g F|)
          / ((Fintype.card V : ℝ) - W.card)
  := by
  set B : ℝ := ∑ F ∈ (partialVertexVec g).support, |partialVertexVec g F| with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun F _ => abs_nonneg _)
  induction W using Finset.induction_on with
  | empty =>
    have h1 : pdensityVec g (deleteFinset N ∅) = pdensityVec g N :=
      pdensityVec_congr g (deleteFinsetEmptyIso N)
    rw [h1, sub_self, abs_zero]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]
  | insert w W' hw ih =>
    have hcardins : (insert w W').card = W'.card + 1 := Finset.card_insert_of_notMem hw
    have hW' : W'.card < Fintype.card V := by omega
    have hfit' : ∀ M ∈ g.support, M.1 + W'.card + 1 ≤ Fintype.card V := by
      intro M hM
      have := hfit M hM
      omega
    have hih := ih hW' hfit'
    -- one more deletion step
    have hstep : pdensityVec g (deleteFinset N (insert w W'))
        = pdensityVec g (deleteFinset N W')
          + (1 / (((Fintype.card V - W'.card - 1 : ℕ) : ℝ) + 1))
            * pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩ := by
      have hV' : Fintype.card {u : V // u ∉ W'} = (Fintype.card V - W'.card - 1) + 1 := by
        rw [card_deleteFinset]
        omega
      have hsupp' : ∀ M ∈ g.support, M.1 ≤ Fintype.card V - W'.card - 1 := by
        intro M hM
        have := hfit M hM
        omega
      exact Eq.trans (pdensityVec_congr g (deleteFinsetInsertIso N W' w hw)).symm
        (vertex_deletion_pdensity g hV' hsupp' (deleteFinset N W') ⟨w, hw⟩)
    have hpe : |pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩| ≤ B :=
      abs_pEval_le _ _ _
    have hden : ((Fintype.card V - W'.card - 1 : ℕ) : ℝ) + 1
        = (Fintype.card V : ℝ) - W'.card := by
      have h9 : (Fintype.card V - W'.card - 1 : ℕ) = Fintype.card V - (W'.card + 1) := by
        omega
      rw [h9, Nat.cast_sub (by omega : W'.card + 1 ≤ Fintype.card V)]
      push_cast
      ring
    have hdpos : (0 : ℝ) < (Fintype.card V : ℝ) - W'.card := by
      have h9 : (W'.card : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hW'
      linarith
    have hdpos' : (0 : ℝ) < (Fintype.card V : ℝ) - (insert w W').card := by
      have h9 : ((insert w W').card : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hW
      linarith
    calc |pdensityVec g (deleteFinset N (insert w W')) - pdensityVec g N|
        = |(pdensityVec g (deleteFinset N W') - pdensityVec g N)
            + (1 / (((Fintype.card V - W'.card - 1 : ℕ) : ℝ) + 1))
              * pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩| := by
          rw [hstep]
          ring_nf
      _ ≤ |pdensityVec g (deleteFinset N W') - pdensityVec g N|
            + |(1 / (((Fintype.card V - W'.card - 1 : ℕ) : ℝ) + 1))
              * pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩| := abs_add_le _ _
      _ ≤ (W'.card : ℝ) * B / ((Fintype.card V : ℝ) - W'.card)
            + (1 / ((Fintype.card V : ℝ) - W'.card)) * B := by
          apply add_le_add hih
          rw [abs_mul, hden]
          have h9 : |1 / ((Fintype.card V : ℝ) - W'.card)|
              = 1 / ((Fintype.card V : ℝ) - W'.card) := abs_of_pos (by positivity)
          rw [h9]
          exact mul_le_mul_of_nonneg_left hpe (by positivity)
      _ = ((W'.card : ℝ) + 1) * B / ((Fintype.card V : ℝ) - W'.card) := by
          field_simp
      _ ≤ ((insert w W').card : ℝ) * B / ((Fintype.card V : ℝ) - (insert w W').card) := by
          rw [hcardins]
          push_cast
          rw [div_le_div_iff₀ hdpos (by rw [hcardins] at hdpos'; push_cast at hdpos'; exact hdpos')]
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith

/-! ## Telescoping descent: deleting uniformly bad roots -/

/-- **(T)** Deleting a set `W` of roots that are all `ε`-bad *in the original
host* (`p^{(N,r)}(∂₁g) ≤ −ε`) drives the density of `g` down by
`|W|·(ε−corr)/n`, where `corr` dominates the hitting correction
`‖∂₁g‖₁·K·|W|/(n−1)` for evaluating badness in the partially deleted hosts. -/
theorem pdensityVec_deleteFinset_descent {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector ∅ₜ) (N : LabeledGraph ∅ₜ V) {ε corr : ℝ} {K : ℕ}
    (hK : ∀ F ∈ (partialVertexVec g).support, F.1 ≤ K + 1)
    (hεcorr : 0 ≤ ε - corr)
    (W : Finset V)
    (hgfit : ∀ M ∈ g.support, M.1 + W.card + 1 ≤ Fintype.card V)
    (hKfit : K + 1 + W.card ≤ Fintype.card V)
    (hV2 : 2 ≤ Fintype.card V)
    (hbad : ∀ r ∈ W, pEval (partialVertexVec g) N r ≤ -ε)
    (hcorr : (∑ F ∈ (partialVertexVec g).support, |partialVertexVec g F|)
        * K * W.card / ((Fintype.card V : ℝ) - 1) ≤ corr)
    : pdensityVec g (deleteFinset N W)
      ≤ pdensityVec g N - (W.card : ℝ) * (ε - corr) / (Fintype.card V : ℝ)
  := by
  set B : ℝ := ∑ F ∈ (partialVertexVec g).support, |partialVertexVec g F| with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun F _ => abs_nonneg _)
  have hcpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV2
    linarith
  induction W using Finset.induction_on with
  | empty =>
    have h1 : pdensityVec g (deleteFinset N ∅) = pdensityVec g N :=
      pdensityVec_congr g (deleteFinsetEmptyIso N)
    rw [h1]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div, sub_zero, le_refl]
  | insert w W' hw ih =>
    have hcardins : (insert w W').card = W'.card + 1 := Finset.card_insert_of_notMem hw
    have hWins : (insert w W').card ≤ Fintype.card V := by omega
    have hgfit' : ∀ M ∈ g.support, M.1 + W'.card + 1 ≤ Fintype.card V := by
      intro M hM
      have := hgfit M hM
      omega
    have hKfit' : K + 1 + W'.card ≤ Fintype.card V := by omega
    have hbad' : ∀ r ∈ W', pEval (partialVertexVec g) N r ≤ -ε :=
      fun r hr => hbad r (Finset.mem_insert_of_mem hr)
    have hcorr' : B * K * W'.card / ((Fintype.card V : ℝ) - 1) ≤ corr := by
      refine le_trans ?_ hcorr
      have h2r : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV2
      have hd1 : (0 : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by linarith
      apply div_le_div_of_nonneg_right ?_ hd1
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hcardins]
      push_cast
      linarith
    have hih := ih hgfit' hKfit' hbad' hcorr'
    -- one more deletion step
    have hstep : pdensityVec g (deleteFinset N (insert w W'))
        = pdensityVec g (deleteFinset N W')
          + (1 / (((Fintype.card V - W'.card - 1 : ℕ) : ℝ) + 1))
            * pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩ := by
      have hV' : Fintype.card {u : V // u ∉ W'} = (Fintype.card V - W'.card - 1) + 1 := by
        rw [card_deleteFinset]
        omega
      have hsupp' : ∀ M ∈ g.support, M.1 ≤ Fintype.card V - W'.card - 1 := by
        intro M hM
        have := hgfit M hM
        omega
      exact Eq.trans (pdensityVec_congr g (deleteFinsetInsertIso N W' w hw)).symm
        (vertex_deletion_pdensity g hV' hsupp' (deleteFinset N W') ⟨w, hw⟩)
    -- badness survives the partial deletion, up to the hitting correction
    have hpe : pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩ ≤ -(ε - corr) := by
      have hhit := hitting_pEval N w W' hw (partialVertexVec g) hK hKfit' hV2
      have h1 := hbad w (Finset.mem_insert_self w W')
      have h2 : pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩
          ≤ pEval (partialVertexVec g) N w
            + B * K * W'.card / ((Fintype.card V : ℝ) - 1) := by
        have h3 := abs_le.mp hhit
        linarith [h3.1]
      linarith
    have hden : ((Fintype.card V - W'.card - 1 : ℕ) : ℝ) + 1
        = (Fintype.card V : ℝ) - W'.card := by
      have h9 : (Fintype.card V - W'.card - 1 : ℕ) = Fintype.card V - (W'.card + 1) := by
        omega
      rw [h9, Nat.cast_sub (by omega : W'.card + 1 ≤ Fintype.card V)]
      push_cast
      ring
    have hdpos : (0 : ℝ) < (Fintype.card V : ℝ) - W'.card := by
      have h9 : (W'.card : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast (by omega : W'.card + 1 ≤ Fintype.card V)
      linarith
    -- the step decreases the density by at least (ε−corr)/n
    have hstep_le : pdensityVec g (deleteFinset N (insert w W'))
        ≤ pdensityVec g (deleteFinset N W') - (ε - corr) / (Fintype.card V : ℝ) := by
      rw [hstep, hden]
      have h4 : (1 / ((Fintype.card V : ℝ) - W'.card))
          * pEval (partialVertexVec g) (deleteFinset N W') ⟨w, hw⟩
          ≤ (1 / ((Fintype.card V : ℝ) - W'.card)) * (-(ε - corr)) :=
        mul_le_mul_of_nonneg_left hpe (by positivity)
      have h5 : (1 / ((Fintype.card V : ℝ) - W'.card)) * (-(ε - corr))
          ≤ -((ε - corr) / (Fintype.card V : ℝ)) := by
        rw [one_div, mul_neg, neg_le_neg_iff, div_eq_mul_inv, mul_comm]
        apply mul_le_mul_of_nonneg_right ?_ hεcorr
        rw [inv_le_inv₀ hcpos hdpos]
        have h9 : (0 : ℝ) ≤ (W'.card : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    calc pdensityVec g (deleteFinset N (insert w W'))
        ≤ pdensityVec g (deleteFinset N W') - (ε - corr) / (Fintype.card V : ℝ) := hstep_le
      _ ≤ (pdensityVec g N - (W'.card : ℝ) * (ε - corr) / (Fintype.card V : ℝ))
            - (ε - corr) / (Fintype.card V : ℝ) := by linarith
      _ = pdensityVec g N
            - ((insert w W').card : ℝ) * (ε - corr) / (Fintype.card V : ℝ) := by
          rw [hcardins]
          push_cast
          ring

end Differential
end FlagAlgebras
