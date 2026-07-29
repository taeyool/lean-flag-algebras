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
    (g : FlagVector vertexType)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) {c : ℝ}
    (hΨb : ∀ a : FlagDensitySpace vertexType, |Ψ (densityEvalFun g a)| ≤ c)
    : ∫ a, Ψ (densityEvalFun g a)
        ∂(FinFlag.toMeasure (⟨ℓ + 1, M⟩ : FinFlag ∅ₜ) hM)
      = (1 / ((ℓ : ℝ) + 1)) * ∑ r : Fin (ℓ + 1), Ψ (pEval g M.out r)
  := by
  have hmeas : Measurable (fun a : FlagDensitySpace vertexType => Ψ (densityEvalFun g a)) :=
    hΨm.comp (measurable_densityEvalFun g)
  have hint : Integrable (fun a : FlagDensitySpace vertexType => Ψ (densityEvalFun g a))
      (FinFlag.toMeasure (⟨ℓ + 1, M⟩ : FinFlag ∅ₜ) hM) :=
    integrable_of_bounded hmeas c hΨb
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
    (g : FlagVector vertexType)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) {c : ℝ}
    (hΨb : ∀ a : FlagDensitySpace vertexType, |Ψ (densityEvalFun g a)| ≤ c)
    : ∫ a, Ψ (densityEvalFun g a) ∂(G.toMeasure hG)
      = (1 / (G.1 : ℝ)) * ∑ r : Fin G.1, Ψ (pEval g G.2.out r)
  := by
  obtain ⟨L, M⟩ := G
  dsimp only at h1 hG ⊢
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, L = ℓ + 1 := ⟨L - 1, by omega⟩
  have h := integral_toMeasure_eq_root_average M hG g Ψ hΨm hΨb
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

/-! ## Odds and ends for the endgame -/

/-- Densities are preserved by canonicalisation, at the level of `densityEval`. -/
theorem densityEval_getCanonicalFlag {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector ∅ₜ) (X : LabeledGraph ∅ₜ V) {L : ℕ} (h : Fintype.card V = L)
    : densityEval g ⟨L, getCanonicalFlag X h⟩ = pdensityVec g X
  := by
  dsimp only [densityEval, pdensityVec, linearExtension]
  apply Finset.sum_congr rfl
  intro M _
  congr 1
  rw [Rat.cast_inj]
  exact flagDensity₁_getCanonicalFlag M.2 X h

/-- Evaluating a basis vector on an arbitrary carrier is the plain density. -/
theorem pdensityVec_basisVector {V : Type} [Fintype V] [DecidableEq V]
    (M : FinFlag ∅ₜ) (X : LabeledGraph ∅ₜ V)
    : pdensityVec (basisVector M) X = (flagDensity₁ M.2 (⟦X⟧ : Flag ∅ₜ V) : ℝ)
  := by
  dsimp only [pdensityVec]
  simp only [linearExtension, basisVector_support, Finset.sum_singleton,
    basisVector_apply_self, one_smul]

/-- `pdensityVec` on the representative of a finite flag is `densityEval`. -/
theorem pdensityVec_out (g : FlagVector ∅ₜ) (G : FinFlag ∅ₜ)
    : pdensityVec g G.2.out = densityEval g G
  := by
  rw [pdensityVec_fin g G.2.out, Quotient.out_eq]
  rfl

/-- **One deletion round** (Razborov (29)–(33) for a single host): if the
average of `max(−p^{(N,r)}(∂₁g), 0)` over the roots of an `L`-vertex host is
at least `ε₀`, then deleting the `⌊δL⌋` worst roots produces a host on which
the density of `g` has dropped by at least `ε₀δ/8`, while only a `δ`-fraction
of the vertices was removed. -/
theorem exists_deleted_host {L : ℕ} (N : LabeledGraph ∅ₜ (Fin L))
    (g : FlagVector ∅ₜ) {ε₀ δ B' : ℝ} {K Kg : ℕ}
    (hε₀ : 0 < ε₀) (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hB'pos : 0 < B')
    (hBb : ∑ F ∈ (partialVertexVec g).support, |partialVertexVec g F| ≤ B')
    (hK : ∀ F ∈ (partialVertexVec g).support, F.1 ≤ K + 1)
    (hKg : ∀ M ∈ g.support, M.1 ≤ Kg)
    (hδbad : δ ≤ ε₀ / (2 * B')) (hδcorr : 2 * B' * K * δ ≤ ε₀ / 4)
    (hLg : 2 * Kg + 2 ≤ L) (hLK : 2 * K + 4 ≤ L) (hδL : 2 ≤ δ * L)
    (havg : ε₀ ≤ (1 / (L : ℝ))
        * ∑ r, max (-(pEval (partialVertexVec g) N r)) 0)
    : ∃ W : Finset (Fin L),
        2 * W.card ≤ L ∧ (W.card : ℝ) ≤ δ * L ∧
        pdensityVec g (deleteFinset N W)
          ≤ pdensityVec g N - ε₀ * δ / 8
  := by
  set B : ℝ := ∑ F ∈ (partialVertexVec g).support, |partialVertexVec g F| with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun F _ => abs_nonneg _)
  have hLr : (4 : ℝ) ≤ (L : ℝ) := by
    have h1 : δ * L ≤ (1 / 2) * L :=
      mul_le_mul_of_nonneg_right hδhalf (Nat.cast_nonneg _)
    linarith
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  -- Markov: many roots are `ε₀/2`-bad
  have hxb : ∀ r : Fin L, max (-(pEval (partialVertexVec g) N r)) 0 ≤ B' := by
    intro r
    calc max (-(pEval (partialVertexVec g) N r)) 0
        ≤ |pEval (partialVertexVec g) N r| :=
          max_le (neg_le_abs _) (abs_nonneg _)
      _ ≤ B := abs_pEval_le _ _ _
      _ ≤ B' := hBb
  have hmark := card_bad_ge_of_average_ge
    (fun r : Fin L => max (-(pEval (partialVertexVec g) N r)) 0)
    hB'pos hxb (fun r => le_max_right _ _) havg
  -- the deleted set: `⌊δL⌋` bad roots
  set w : ℕ := ⌊δ * (L : ℝ)⌋₊ with hw
  have hwle : (w : ℝ) ≤ δ * L := Nat.floor_le (by positivity)
  have hwge : δ * L - 1 ≤ (w : ℝ) := by
    have h1 := Nat.lt_floor_add_one (δ * (L : ℝ))
    push_cast at h1 ⊢
    linarith
  have hwBad : w ≤ (Finset.univ.filter (fun r : Fin L =>
      ε₀ / 2 ≤ max (-(pEval (partialVertexVec g) N r)) 0)).card := by
    have h1 : (w : ℝ) ≤ ((Finset.univ.filter (fun r : Fin L =>
        ε₀ / 2 ≤ max (-(pEval (partialVertexVec g) N r)) 0)).card : ℝ) := by
      calc (w : ℝ) ≤ δ * L := hwle
        _ ≤ ε₀ / (2 * B') * L :=
            mul_le_mul_of_nonneg_right hδbad (Nat.cast_nonneg _)
        _ ≤ _ := hmark
    exact_mod_cast h1
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hwBad
  -- W is uniformly bad in the original host
  have hbadW : ∀ r ∈ W, pEval (partialVertexVec g) N r ≤ -(ε₀ / 2) := by
    intro r hr
    have h1 := hWsub hr
    rw [Finset.mem_filter] at h1
    by_contra hc
    push_neg at hc
    have h2 : max (-(pEval (partialVertexVec g) N r)) 0 < ε₀ / 2 :=
      max_lt (by linarith) (by linarith)
    linarith [h1.2]
  -- basic size facts
  have hw2 : 2 * w ≤ L := by
    have h1 : (2 : ℝ) * w ≤ (L : ℝ) := by
      calc (2 : ℝ) * w ≤ 2 * (δ * L) := by linarith
        _ ≤ 2 * ((1 / 2) * L) := by
            have := mul_le_mul_of_nonneg_right hδhalf (Nat.cast_nonneg (α := ℝ) L)
            linarith
        _ = (L : ℝ) := by ring
    exact_mod_cast h1
  have hWc2 : 2 * W.card ≤ L := by rw [hWcard]; exact hw2
  have hWcr : (W.card : ℝ) ≤ δ * L := by rw [hWcard]; exact hwle
  refine ⟨W, hWc2, hWcr, ?_⟩
  -- the descent estimate
  have hdesc := pdensityVec_deleteFinset_descent g N
    (ε := ε₀ / 2) (corr := ε₀ / 4) (K := K) hK (by linarith) W ?gfit ?Kfit ?V2
    hbadW ?corr
  case gfit =>
    intro M hM
    have h1 := hKg M hM
    rw [Fintype.card_fin, hWcard]
    omega
  case Kfit =>
    rw [Fintype.card_fin, hWcard]
    omega
  case V2 =>
    rw [Fintype.card_fin]
    have : (4 : ℕ) ≤ L := by exact_mod_cast hLr
    omega
  case corr =>
    rw [Fintype.card_fin, hWcard]
    have hLhalf : (L : ℝ) / 2 ≤ (L : ℝ) - 1 := by linarith
    have hd2 : (0 : ℝ) < (L : ℝ) / 2 := by linarith
    have hd1 : (0 : ℝ) < (L : ℝ) - 1 := by linarith
    have hnum : B * K * w ≤ B' * K * (δ * L) := by
      have h1 : B * K ≤ B' * K :=
        mul_le_mul_of_nonneg_right hBb (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ B * K := by positivity
      nlinarith [hwle, Nat.cast_nonneg (α := ℝ) w]
    calc B * K * w / ((L : ℝ) - 1)
        ≤ B' * K * (δ * L) / ((L : ℝ) / 2) := by
          apply div_le_div₀ (by positivity) hnum hd2 hLhalf
      _ = 2 * B' * K * δ := by
          field_simp
      _ ≤ ε₀ / 4 := hδcorr
  -- convert the drop `w(ε₀/4)/L` into `ε₀δ/8`
  rw [Fintype.card_fin, hWcard] at hdesc
  have hdrop : ε₀ * δ / 8 ≤ (w : ℝ) * (ε₀ / 2 - ε₀ / 4) / (L : ℝ) := by
    have h1 : δ * (L : ℝ) / 2 ≤ (w : ℝ) := by linarith
    have h2 : ε₀ / 2 - ε₀ / 4 = ε₀ / 4 := by ring
    rw [h2, div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) hLpos]
    nlinarith [mul_nonneg hε₀.le (by linarith : (0:ℝ) ≤ (w : ℝ) - δ * L / 2)]
  linarith [hdesc, hdrop]

/-- From any `ℕ`-sequence tending to infinity one can extract a subsequence
along which it is strictly monotone. -/
theorem exists_strictMono_comp_strictMono (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (m ∘ ψ)
  := by
  have h : ∀ a b : ℕ, ∃ n, a < n ∧ b < m n := by
    intro a b
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hm.eventually_gt_atTop b)
    refine ⟨max (a + 1) N, ?_, hN _ (le_max_right _ _)⟩
    have := le_max_left (a + 1) N
    omega
  choose nxt h1 h2 using h
  refine ⟨fun k => Nat.rec (nxt 0 0) (fun _ prev => nxt prev (m prev)) k,
    strictMono_nat_of_lt_succ (fun k => ?_),
    strictMono_nat_of_lt_succ (fun k => ?_)⟩
  · exact h1 _ _
  · exact h2 _ _

end Differential
end FlagAlgebras
