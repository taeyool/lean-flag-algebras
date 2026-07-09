import LeanFlagAlgebras.MetaTheory.SupportClosure
import Mathlib.Data.Fintype.CardEmbedding

/-! # Evaluating unlabelled averages through the ensemble (paper §10 groundwork)

Paper §10 ("The gap is invisible to density bounds") repeatedly evaluates an unlabelled
average `φ₀ ⟦s⟧₀` of a labelled element `s ∈ A^σ` at a constrained unlabelled limit
`φ₀ ∈ Q₀`, through the random-extension identity `eq:extension-expectation`
(`probMeasure_extend_emptyType_positiveHom_spec`).  This module collects the generic
evaluation facts every §10 result rests on:

* `toPosHom_posHomPoint` / `posHomPoint_toPosHom` — the two roundtrips between
  `PositiveHom σ` and its point in the homomorphism space `X_σ`.
* `downwardNormalizingFactor_le_one` — the unlabelling weight is a probability, so
  `φ₀ ⟦1⟧₀ ∈ [0,1]` (`posHom_one_downward_nonneg` / `posHom_one_downward_le_one`).
* `downward_eval_eq_zero_of_degenerate` — a **degenerate** base limit (`φ₀ ⟨σ⟩₀ = 0`)
  kills every unlabelled average: `φ₀ ⟦g⟧₀ = 0` for all `g ∈ A^σ`.  This is the paper's
  "every unlabelled graph appearing in `⟨g⟩_σ` contains an embedding of `σ`, so its
  `φ₀`-density is zero by monotonicity", proved here by pushing the level-`ℓ` expansion of
  `1 ∈ A^σ` (`sum_flagWithSize_eq_one`) through the unlabelling operator.
* `support_subset_Sσ` — the support of every admissible random extension lies in the
  root-planting set `S_σ`.
* `abs_downward_eval_le_of_abs_le_on_Sσ` — the **master evaluation bound**: if
  `|s| ≤ δ` pointwise on `S_σ`, then `|φ₀ ⟦s⟧₀| ≤ δ` for every `φ₀ ∈ Q₀`.  This single
  estimate drives `thm:no-closed-certificate-gap` (with `δ = ε`) and `prop:ideal-zero`
  (with `δ = 0`).
* `downward_eval_eq_of_Sσ_singleton` — when `S_σ` is a single point `χ₀`, every
  unlabelled average collapses: `φ₀ ⟦s⟧₀ = φ₀ ⟦1⟧₀ · χ₀(s)` (used by
  `prop:single-point`).
-/

open MeasureTheory

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Roundtrips between `PositiveHom σ` and points of `X_σ` -/

/-- Recovering the homomorphism from the point of `X_σ` it defines gives back the same
homomorphism (`toPosHom` is a section of `posHomPoint`). -/
lemma toPosHom_posHomPoint (φ : PositiveHom σ) :
    PositiveHomSpace.toPosHom (posHomPoint φ) = φ := by
  -- `Classical.choose_spec (posHomPoint φ).property : (toPosHom (posHomPoint φ)).coe = φ.coe`,
  -- then `PositiveHom.coe_injective`.
  apply PositiveHom.coe_injective
  exact Classical.choose_spec (posHomPoint φ).property

/-- The point of `X_σ` defined by the homomorphism recovered from `χ` is `χ` itself. -/
lemma posHomPoint_toPosHom (χ : PositiveHomSpace σ) :
    posHomPoint (PositiveHomSpace.toPosHom χ) = χ := by
  -- `Subtype.ext`; values agree by `Classical.choose_spec χ.property : (toPosHom χ).coe = χ.val`.
  apply Subtype.ext
  exact Classical.choose_spec χ.property

/-! ## The unlabelling weight is a probability -/

/-- A labelled graph is determined by its underlying graph and the underlying embedding of
its type embedding. -/
private lemma labeled_graph_eq_of_type_embed_eq {V : Type} {G H : LabeledGraph σ V}
    (hgraph : G.graph = H.graph)
    (hembed : G.type_embed.toEmbedding = H.type_embed.toEmbedding) : G = H := by
  cases G with
  | mk g₁ t₁ =>
    cases H with
    | mk g₂ t₂ =>
      obtain rfl : g₁ = g₂ := hgraph
      obtain rfl : t₁ = t₂ := RelEmbedding.toEmbedding_injective hembed
      rfl

/-- The unlabelling weight of a flag is at most `1`: the label placements realising the
flag (`isomorphismCount`) inject into all `n!/(n-n₀)!` injections of the labels.

Proof route: a member `H` of `isoLabeledGraphSetWithSameGraph G` is determined by its
`type_embed` (its graph is pinned to `G.graph`), so the set injects into
`Fin n₀ ↪ Fin n`, whose card is `n.descFactorial n₀ = n! / (n-n₀)!`
(`Fintype.card_embedding_eq`, `Nat.descFactorial_eq_div`; `n₀ ≤ n` comes from the type
embedding of any representative). -/
theorem downwardNormalizingFactor_le_one {n : ℕ} (F : Flag σ (Fin n)) :
    downwardNormalizingFactor F ≤ 1 := by
  rw [← Quotient.out_eq F]
  dsimp only [downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph,
    Quotient.lift_mk]
  have hn : n₀ ≤ n := by
    have h := Fintype.card_le_of_embedding F.out.type_embed.toEmbedding
    simpa using h
  have hcount : isomorphismCount F.out ≤ n.factorial / (n - n₀).factorial := by
    have hinj : Function.Injective
        (fun H : isoLabeledGraphSetWithSameGraph F.out => H.val.type_embed.toEmbedding) := by
      intro H₁ H₂ h
      obtain ⟨hg₁, -⟩ := H₁.2
      obtain ⟨hg₂, -⟩ := H₂.2
      apply Subtype.ext
      exact labeled_graph_eq_of_type_embed_eq (hg₁.symm.trans hg₂) h
    have hle := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
      Nat.descFactorial_eq_div hn] at hle
    dsimp only [isomorphismCount]
    rw [Set.toFinset_card]
    exact hle
  have hden : (0 : ℚ) < ((n.factorial / (n - n₀).factorial : ℕ) : ℚ) := by
    simp only [Nat.cast_pos, Nat.div_pos_iff]
    exact ⟨Nat.factorial_pos (n - n₀), Nat.factorial_le (Nat.sub_le n n₀)⟩
  rw [div_le_one hden]
  exact_mod_cast hcount

/-- `φ₀ ⟨σ⟩₀ ≥ 0`: the type flag is a single basis flag, so its value is non-negative. -/
private lemma type_eval_nonneg (φ₀ : PositiveHom ∅ₜ) : 0 ≤ φ₀ ⟨σ⟩₀ :=
  positiveHom_basisVector_ge_zero φ₀ ⟨n₀, σ.toEmptyTypeFlag⟩

/-- `φ₀ ⟨σ⟩₀ ≤ 1`: the type flag is a single basis flag, so its value is at most one. -/
private lemma type_eval_le_one (φ₀ : PositiveHom ∅ₜ) : φ₀ ⟨σ⟩₀ ≤ 1 :=
  positiveHom_basisVector_le_one φ₀ ⟨n₀, σ.toEmptyTypeFlag⟩

/-- `φ₀ ⟦1⟧₀ ≥ 0`: the unlabelled density of the type is non-negative. -/
lemma posHom_one_downward_nonneg (φ₀ : PositiveHom ∅ₜ) :
    0 ≤ φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) := by
  -- `one_downward_eq`, `PositiveHom.map_smul`, `downwardNormalizingFactor_nonneg`,
  -- `positiveHom_basisVector_ge_zero` applied to `⟨σ⟩₀ = ⟦basisVector ⟨n₀, σ.toEmptyTypeFlag⟩⟧`.
  rw [one_downward_eq, PositiveHom.map_smul]
  exact mul_nonneg (by exact_mod_cast downwardNormalizingFactor_nonneg (emptyFlag σ))
    (type_eval_nonneg φ₀)

/-- `φ₀ ⟦1⟧₀ ≤ 1`: the unlabelled density of the type is a probability. -/
lemma posHom_one_downward_le_one (φ₀ : PositiveHom ∅ₜ) :
    φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) ≤ 1 := by
  -- `one_downward_eq` + `downwardNormalizingFactor_le_one` (on `emptyFlag σ`) +
  -- `positiveHom_basisVector_le_one`.
  rw [one_downward_eq, PositiveHom.map_smul]
  have h₁ : ((downwardNormalizingFactor (emptyFlag σ) : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast downwardNormalizingFactor_le_one (emptyFlag σ)
  have h₂ : ((downwardNormalizingFactor (emptyFlag σ) : ℚ) : ℝ) ≥ 0 := by
    exact_mod_cast downwardNormalizingFactor_nonneg (emptyFlag σ)
  calc ((downwardNormalizingFactor (emptyFlag σ) : ℚ) : ℝ) * φ₀ ⟨σ⟩₀
      ≤ 1 * 1 := mul_le_mul h₁ (type_eval_le_one φ₀) (type_eval_nonneg φ₀) zero_le_one
    _ = 1 := one_mul 1

/-! ## Degenerate base limits kill all unlabelled averages -/

/-- **Degenerate types are invisible**: if `φ₀ ⟨σ⟩₀ = 0` then `φ₀ ⟦g⟧₀ = 0` for every
`g ∈ A^σ`.  (Every unlabelled graph appearing in an unlabelled average contains an
embedding of `σ`, whose density at `φ₀` is zero.)

Proof route: this is exactly `downward_zero_at_hom` (FlagAlgebra/RandomHom.lean), which
reduces to single flags by linearity (`flagVector_eq_sum_basisVector`, `downward_sum`,
`downward_smul`, `PositiveHom.map_sum`/`map_smul`) and kills each flag term by density
monotonicity (`positiveHom_basisVector_eq_zero` with
`flagDensity₁_flagType_asEmptyType_pos`). -/
theorem downward_eval_eq_zero_of_degenerate {φ₀ : PositiveHom ∅ₜ}
    (hdeg : φ₀ ⟨σ⟩₀ = 0) (g : FlagAlgebra σ) :
    φ₀ (⟦g⟧₀ : FlagAlgebra ∅ₜ) = 0 :=
  downward_zero_at_hom φ₀ hdeg g

/-! ## The support of an admissible extension lies in `S_σ` -/

/-- The support of an admissible random extension is contained in the root-planting set
`S_σ` (immediately from the definition of `Sσ` as a closure of the union of supports). -/
lemma support_subset_Sσ (T : Constraint σ) {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) (hσ : φ₀ ⟨σ⟩₀ > 0) :
    (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support ⊆ Sσ T := by
  -- `subset_closure` composed with `Set.subset_iUnion` three times.
  intro χ hχ
  exact subset_closure (Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ₀,
    Set.mem_iUnion.mpr ⟨hσ, hχ⟩⟩⟩)

/-! ## The master evaluation bound -/

/-- **Master evaluation bound** (the engine of paper §10): if the evaluation of
`s ∈ A^σ` is bounded by `δ` in absolute value on the root-planting set `S_σ`, then the
unlabelled average `⟦s⟧₀` is bounded by `δ` in absolute value at every constrained
unlabelled limit `φ₀ ∈ Q₀`.

Proof route: split on `φ₀ ⟨σ⟩₀`.
* Degenerate (`= 0`): `φ₀ ⟦s⟧₀ = 0` by `downward_eval_eq_zero_of_degenerate`.
* Non-degenerate (`> 0`): by `probMeasure_extend_emptyType_positiveHom_spec`,
  `φ₀ ⟦s⟧₀ = φ₀ ⟦1⟧₀ · ∫ χ, χ s ∂ℙ[φ₀]` (the denominator `φ₀ ⟦1⟧₀` is positive by
  `one_downward_eq`, `downwardNormalizingFactor_pos`).  Almost every `χ` lies in the
  support (`Measure.support_mem_ae`; the space is compact metrizable, hence hereditarily
  Lindelöf), which is inside `S_σ` (`support_subset_Sσ`), so the integrand is a.e. bounded
  by `δ`; `norm_integral_le_of_norm_le_const` bounds the integral by `δ` (probability
  measure), and `0 ≤ φ₀ ⟦1⟧₀ ≤ 1` (`posHom_one_downward_nonneg`/`_le_one`) finishes. -/
theorem abs_downward_eval_le_of_abs_le_on_Sσ (T : Constraint σ) {s : FlagAlgebra σ}
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ χ ∈ Sσ T, |(PositiveHomSpace.toPosHom χ) s| ≤ δ)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) :
    |φ₀ (⟦s⟧₀ : FlagAlgebra ∅ₜ)| ≤ δ := by
  rcases eq_or_lt_of_le (type_eval_nonneg (σ := σ) φ₀) with hσ0 | hσpos
  · -- degenerate base limit: the average vanishes
    rw [downward_eval_eq_zero_of_degenerate hσ0.symm s, abs_zero]
    exact hδ
  · -- non-degenerate: evaluate through the random extension
    have hσ : φ₀ ⟨σ⟩₀ > 0 := hσpos
    have h1pos : φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) > 0 :=
      positiveHom_one_downward_pos hσ
    have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ s
    rw [eq_div_iff (ne_of_gt h1pos)] at hspec
    have hint : |∫ (χ : PositiveHomSpace σ), (PositiveHomSpace.toPosHom χ) s
        ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ))| ≤ δ := by
      have hae : ∀ᵐ (χ : PositiveHomSpace σ) ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
          ‖(PositiveHomSpace.toPosHom χ) s‖ ≤ δ := by
        filter_upwards [Measure.support_mem_ae] with χ hχ
        rw [Real.norm_eq_abs]
        exact hs χ (support_subset_Sσ T hφ₀ hσ hχ)
      have h := norm_integral_le_of_norm_le_const hae
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
      exact h
    have habs1 : |φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ)| ≤ 1 := by
      rw [abs_of_nonneg (posHom_one_downward_nonneg φ₀)]
      exact posHom_one_downward_le_one φ₀
    rw [← hspec, abs_mul]
    have hfin := mul_le_mul hint habs1 (abs_nonneg _) hδ
    rw [mul_one] at hfin
    exact hfin

/-! ## Collapse at a singleton root-planting set -/

/-- If the root-planting set is a single point `S_σ = {χ₀}`, then every unlabelled
average evaluates at every `φ₀ ∈ Q₀` to `φ₀ ⟦1⟧₀ · χ₀(s)`.

Proof route: degenerate `φ₀` — both sides vanish (`downward_eval_eq_zero_of_degenerate`;
for the right side `φ₀ ⟦1⟧₀ = 0` by the same or by `one_downward_eq`).  Non-degenerate —
almost every `χ` lies in the support (`Measure.support_mem_ae`) hence equals `χ₀`
(`support_subset_Sσ` + `hS`), so `∫ χ, χ s ∂ℙ[φ₀] = χ₀ s` (`integral_congr_ae`,
`integral_const`, probability measure), and the spec rearranges to the claim. -/
theorem downward_eval_eq_of_Sσ_singleton (T : Constraint σ) {χ₀ : PositiveHomSpace σ}
    (hS : Sσ T = {χ₀}) (s : FlagAlgebra σ)
    {φ₀ : PositiveHom ∅ₜ} (hφ₀ : posHomPoint φ₀ ∈ Qσ T.forb0) :
    φ₀ (⟦s⟧₀ : FlagAlgebra ∅ₜ)
      = φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) * (PositiveHomSpace.toPosHom χ₀) s := by
  rcases eq_or_lt_of_le (type_eval_nonneg (σ := σ) φ₀) with hσ0 | hσpos
  · -- degenerate base limit: both sides vanish
    rw [downward_eval_eq_zero_of_degenerate hσ0.symm s,
      downward_eval_eq_zero_of_degenerate hσ0.symm (1 : FlagAlgebra σ), zero_mul]
  · -- non-degenerate: almost every extension point equals `χ₀`
    have hσ : φ₀ ⟨σ⟩₀ > 0 := hσpos
    have h1pos : φ₀ (⟦(1 : FlagAlgebra σ)⟧₀ : FlagAlgebra ∅ₜ) > 0 :=
      positiveHom_one_downward_pos hσ
    have hspec := probMeasure_extend_emptyType_positiveHom_spec hσ s
    rw [eq_div_iff (ne_of_gt h1pos)] at hspec
    have hae : ∀ᵐ (χ : PositiveHomSpace σ) ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)),
        (PositiveHomSpace.toPosHom χ) s = (PositiveHomSpace.toPosHom χ₀) s := by
      filter_upwards [Measure.support_mem_ae] with χ hχ
      have hmem : χ ∈ Sσ T := support_subset_Sσ T hφ₀ hσ hχ
      rw [hS] at hmem
      rw [Set.mem_singleton_iff.mp hmem]
    have hint : ∫ (χ : PositiveHomSpace σ), (PositiveHomSpace.toPosHom χ) s
        ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ)) = (PositiveHomSpace.toPosHom χ₀) s :=
      integral_eq_const hae
    rw [← hspec, hint]
    exact mul_comm _ _

end FlagAlgebras.MetaTheory
