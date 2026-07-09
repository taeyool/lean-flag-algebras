import LeanFlagAlgebras.MetaTheory.Pinning
import LeanFlagAlgebras.MetaTheory.HeredClass

/-! # The one-root edge flag and the endpoint pinning obstructions (paper §9 / §9.2)

This module sets up the concrete ingredients of paper §9's degeneracy obstruction and its dense
(co-degenerate) counterpart from §9.2, on top of the *abstract* `pinning_obstruction` of
[`Pinning`](./Pinning.lean).

The one mechanism behind both is **boundary pinning** at the one-vertex type `vtype`: the one-root
edge flag `e` has its density pinned almost surely to a boundary value of `[0,1]` (`0` for a
degenerate class, `1` for a co-degenerate one) across every admissible random extension, while the
constrained quotient still contains a labelled limit attaining the opposite boundary.  The paper's
"Endpoints are automatic" remark (after `thm:pinning`) is what makes this work from a mere
*expectation* condition: a `[0,1]`-valued random variable with mean `0` (resp. `1`) is almost surely
`0` (resp. `1`).

Contents:

* `vtype` — the one-vertex type; `e : A^vtype` the one-root edge flag; `ρ := ⟦e⟧₀ : A^0` the
  unlabelled edge (`⟨e⟩_vtype = ρ`).
* `e_eval_nonneg` / `e_eval_le_one` — `e` evaluates in `[0,1]` at every positive homomorphism (`e`
  is a single basis flag).
* `one_downward_vtype` — `⟦1⟧₀ = 1` at the one-vertex type, so the random-extension denominator is
  `1` and the expectation of `e` is `φ₀ ρ` (`expectation_e`).
* `ae_e_eq_zero_of_pinned` / `ae_e_eq_one_of_pinned` — the two endpoint a.s.-pinning facts.
* `EdgeDegenerate` (`def:edge-degenerate`) / `CoEdgeDegenerate`.
* `edgeDegenerate_not_rootPlantable_of_witness` / `coEdgeDegenerate_not_rootPlantable_of_witness` —
  the abstract obstruction: edge-(co-)degeneracy plus a quotient witness at the opposite boundary
  obstructs root-plantability.  The concrete star / co-star witnesses are built in
  [`StarWitness`](./StarWitness.lean).
-/

open MeasureTheory SimpleGraph

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The one-vertex type and the one-root edge flag -/

/-- The **one-vertex type** `vtype` (paper §9's `\vtype`): a single labelled vertex with no edge.
Definitionally the same `FlagType (Fin 1)` as §8's `oneVertexType`, redeclared here so §9 does not
depend on the §8 `C₅`/sparse-repair stack. -/
abbrev vtype : FlagType (Fin 1) := ⊥

/-- The edge `0–1` on `Fin 2`.  Since `Fin 2` admits exactly one edge this is the complete graph
`⊤`. -/
abbrev edgeGraph : SimpleGraph (Fin 2) := ⊤

/-- The one-root edge as a labelled graph over the one-vertex type: vertex `0` is the root, the edge
joins the root to the single unlabelled vertex `1`. -/
def edgeLabeled : LabeledGraph vtype (Fin 2) where
  graph := edgeGraph
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [edgeGraph, top_adj, ne_eq]
        constructor
        · intro h; exact absurd rfl h
        · intro h; exact (h.ne (Subsingleton.elim a b)).elim }

/-- The one-root edge as a size-tagged flag. -/
noncomputable def edgeFF : FinFlag vtype := ⟨2, (⟦edgeLabeled⟧ : Flag vtype (Fin 2))⟩

/-- **The one-root edge flag** `e ∈ A^vtype` (paper's `e`): the two-vertex flag in which the root is
adjacent to the one unlabelled vertex. -/
noncomputable def e : FlagAlgebra vtype := ⟦basisVector edgeFF⟧

/-- **The unlabelled edge** `ρ = ⟨e⟩_vtype ∈ A^0` (paper's `ρ`), the unlabelling of `e`. -/
noncomputable def ρ : FlagAlgebra ∅ₜ := ⟦e⟧₀

/-- `e` is nonnegative at every positive homomorphism (it is a single basis flag). -/
lemma e_eval_nonneg (φ : PositiveHom vtype) : 0 ≤ φ e :=
  positiveHom_basisVector_ge_zero φ edgeFF

/-- `e` is at most `1` at every positive homomorphism (it is a single basis flag). -/
lemma e_eval_le_one (φ : PositiveHom vtype) : φ e ≤ 1 :=
  positiveHom_basisVector_le_one φ edgeFF

/-! ## The denominator collapses at the one-vertex type -/

/-- On the empty type there is exactly one size-`1` flag (the single unlabelled vertex): two
`∅ₜ`-labelled graphs on `Fin 1` are flag-isomorphic via the (unique) graph isomorphism, since
`Fin 1` carries only the edgeless graph and there are no labels to preserve. -/
private instance : Subsingleton (FlagWithSize ∅ₜ 1) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | _ A =>
  induction b using Quotient.inductionOn with
  | _ B =>
  apply Quotient.sound
  have hgraph : A.graph = B.graph := Subsingleton.elim _ _
  refine ⟨{ graph_iso := hgraph ▸ SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
  funext t
  exact Fin.elim0 t

/-- The fully-labelled one-vertex type is rigid: its only label placement is the identity, so the
isomorphism count of `emptyLabeledGraph vtype` is `1` (the type embedding `Fin 1 ↪ Fin 1` is forced
to be the identity). -/
private theorem isomorphismCount_emptyLabeledGraph_vtype :
    isomorphismCount (emptyLabeledGraph vtype) = 1 := by
  dsimp only [isomorphismCount]
  simp only [Set.toFinset_card]
  refine Fintype.card_eq_one_iff.mpr ?_
  refine ⟨⟨emptyLabeledGraph vtype, ⟨rfl, ⟨LabeledGraphIso.refl⟩⟩⟩, ?_⟩
  rintro ⟨H, hH⟩
  rcases hH with ⟨hGraph, _⟩
  congr
  rcases H with ⟨Hgraph, Hembed⟩
  simp only at hGraph ⊢
  subst hGraph
  congr 1
  apply RelEmbedding.ext
  intro t
  exact Subsingleton.elim _ _

/-- The unlabeling weight of the empty flag at the rigid one-vertex type is `1`
(`isomorphismCount = 1` over the single label injection `1!/0! = 1`). -/
private theorem downwardNormalizingFactor_emptyFlag_vtype :
    downwardNormalizingFactor (emptyFlag vtype) = 1 := by
  dsimp only [emptyFlag, downwardNormalizingFactor, downwardNormalizingFactor_labeledGraph,
    Quotient.lift_mk]
  rw [isomorphismCount_emptyLabeledGraph_vtype]
  norm_num

/-- The type-density `⟨vtype⟩₀` is the unit of `A^0`. -/
lemma vtype_asEmptyTypeAlgebra_eq_one : (⟨vtype⟩₀ : FlagAlgebra ∅ₜ) = 1 := by
  -- `1` expands to the density-weighted sum of size-`1` `∅ₜ`-flags; there is exactly one,
  -- namely `vtype.toEmptyTypeFlag`, so the sum collapses to `⟨vtype⟩₀`.
  rw [← sum_flagWithSize_eq_one (σ := ∅ₜ) 1 (Nat.zero_le 1),
    Finset.sum_eq_single vtype.toEmptyTypeFlag]
  · rfl
  · intro F _ hF; exact absurd (Subsingleton.elim _ _) hF
  · intro h; exact absurd (Finset.mem_univ _) h

/-- At the one-vertex type, unlabelling the unit gives the unit: `⟦1⟧₀ = 1` in `A^0`.

`one_downward_eq` gives `⟦1⟧₀ = dnf(emptyFlag vtype) • ⟨vtype⟩₀`; the normalizing factor of the
rigid one-vertex type is `1`, and the single-vertex unlabelled flag `⟨vtype⟩₀` equals the unit of
`A^0` by the one-vertex averaging relation. -/
lemma one_downward_vtype : (⟦(1 : FlagAlgebra vtype)⟧₀ : FlagAlgebra ∅ₜ) = 1 := by
  rw [one_downward_eq, downwardNormalizingFactor_emptyFlag_vtype, vtype_asEmptyTypeAlgebra_eq_one]
  simp

/-! ## The expectation of the edge flag -/

/-- **Specialised expectation formula.**  Under any admissible random extension at the one-vertex
type, the mean of the one-root edge flag is the base edge density:
`E[χ ↦ χ e] = φ₀ ρ` (the denominator `φ₀ ⟦1⟧₀` is `1` by `one_downward_vtype`). -/
lemma expectation_e {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨vtype⟩₀ > 0) :
    ∫ χ : PositiveHomSpace vtype, (PositiveHomSpace.toPosHom χ) e ∂(ℙ[φ₀]) = φ₀ ρ := by
  rw [probMeasure_extend_emptyType_positiveHom_spec hσ e, one_downward_vtype,
    PositiveHom.map_one, div_one]
  rfl

/-- The integrand `χ ↦ χ e` is integrable against the (finite) random-extension measure: it is a
continuous function on the compact homomorphism space. -/
private lemma integrable_e {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨vtype⟩₀ > 0) :
    Integrable (fun χ : PositiveHomSpace vtype => (PositiveHomSpace.toPosHom χ) e)
      (ℙ[φ₀] : Measure (PositiveHomSpace vtype)) :=
  (continuous_eval e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## The two endpoint a.s.-pinning facts -/

/-- **Endpoint `c = 0`.**  If the unlabelled edge has base value `0`, then `e` is almost surely `0`
under the random extension: a `[0,1]`-valued variable of mean `0` vanishes a.s. -/
lemma ae_e_eq_zero_of_pinned {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨vtype⟩₀ > 0) (h0 : φ₀ ρ = 0) :
    ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)),
      (PositiveHomSpace.toPosHom χ) e = 0 := by
  have hint : ∫ χ : PositiveHomSpace vtype, (PositiveHomSpace.toPosHom χ) e
      ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)) = 0 := by rw [expectation_e hσ, h0]
  have hnonneg : 0 ≤ (fun χ : PositiveHomSpace vtype => (PositiveHomSpace.toPosHom χ) e) :=
    fun χ => e_eval_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnonneg (integrable_e hσ)).mp hint] with χ hχ
  exact hχ

/-- **Endpoint `c = 1`.**  If the unlabelled edge has base value `1`, then `e` is almost surely `1`
under the random extension: a `[0,1]`-valued variable of mean `1` equals `1` a.s. -/
lemma ae_e_eq_one_of_pinned {φ₀ : PositiveHom ∅ₜ} (hσ : φ₀ ⟨vtype⟩₀ > 0) (h1 : φ₀ ρ = 1) :
    ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)),
      (PositiveHomSpace.toPosHom χ) e = 1 := by
  set g : PositiveHomSpace vtype → ℝ := fun χ => (PositiveHomSpace.toPosHom χ) e with hg
  have hgintval : ∫ χ, g χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)) = 1 := by
    rw [expectation_e hσ, h1]
  -- The slack `1 - g` is non-negative (`e ≤ 1`), integrable, and has integral `0`.
  have hhnonneg : 0 ≤ (fun χ => 1 - g χ) := fun χ => by
    simp only [Pi.zero_apply, sub_nonneg]; exact e_eval_le_one _
  have hhint : Integrable (fun χ => 1 - g χ) (ℙ[φ₀] : Measure (PositiveHomSpace vtype)) :=
    (integrable_const 1).sub (integrable_e hσ)
  have hhintval : ∫ χ, (1 - g χ) ∂(ℙ[φ₀] : Measure (PositiveHomSpace vtype)) = 0 := by
    rw [integral_sub (integrable_const 1) (integrable_e hσ), hgintval]; simp
  filter_upwards [(integral_eq_zero_iff_of_nonneg hhnonneg hhint).mp hhintval] with χ hχ
  have hχ' : (1 : ℝ) - g χ = 0 := hχ
  linarith

/-! ## Edge-degeneracy and the abstract obstruction -/

/-- **`def:edge-degenerate`.**  A hereditary class is *edge-degenerate* if every constrained
unlabelled limit has edge density zero: `φ₀(ρ) = 0` for all `φ₀ ∈ Q₀`. -/
def EdgeDegenerate (hc : HeredClass) : Prop :=
  ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0 → φ₀ ρ = 0

/-- The dual: a class is *co-edge-degenerate* if every constrained unlabelled limit has edge density
one (`§9.2`): `φ₀(ρ) = 1` for all `φ₀ ∈ Q₀`. -/
def CoEdgeDegenerate (hc : HeredClass) : Prop :=
  ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (hc.constraintOf vtype).forb0 → φ₀ ρ = 1

/-- **`thm:degenerate-obstruction`, abstract form.**  An edge-degenerate class with a quotient point
of positive one-root edge density is not root-plantable at the one-vertex type.  (The `e ≠ 0`
witness is supplied by an arbitrarily-large star in [`StarWitness`](./StarWitness.lean).) -/
theorem edgeDegenerate_not_rootPlantable_of_witness (hc : HeredClass) (hdeg : EdgeDegenerate hc)
    (hwit : ∃ ψ ∈ Qσ (hc.constraintOf vtype).forbσ, (PositiveHomSpace.toPosHom ψ) e ≠ 0) :
    ¬ RootPlantable (hc.constraintOf vtype) := by
  refine pinning_obstruction (hc.constraintOf vtype) e 0 ?_ hwit
  intro φ₀ hφ₀ hσ
  exact ae_e_eq_zero_of_pinned hσ (hdeg φ₀ hφ₀)

/-- **`cor:codegenerate`, abstract form.**  A co-edge-degenerate class with a quotient point of
one-root edge density below `1` is not root-plantable at the one-vertex type.  (The `e ≠ 1` witness
is supplied by an arbitrarily-large co-star in [`StarWitness`](./StarWitness.lean).) -/
theorem coEdgeDegenerate_not_rootPlantable_of_witness (hc : HeredClass) (hdeg : CoEdgeDegenerate hc)
    (hwit : ∃ ψ ∈ Qσ (hc.constraintOf vtype).forbσ, (PositiveHomSpace.toPosHom ψ) e ≠ 1) :
    ¬ RootPlantable (hc.constraintOf vtype) := by
  refine pinning_obstruction (hc.constraintOf vtype) e 1 ?_ hwit
  intro φ₀ hφ₀ hσ
  exact ae_e_eq_one_of_pinned hσ (hdeg φ₀ hφ₀)

/-- The root-planting set of an edge-degenerate class is contained in the level set `{χ : χ e = 0}`
(the structured `S_vtype ⊆ {χ(e)=0} ⊊ Q_vtype` half of `thm:degenerate-obstruction`). -/
theorem Sσ_subset_e_eq_zero_of_edgeDegenerate (hc : HeredClass) (hdeg : EdgeDegenerate hc) :
    Sσ (hc.constraintOf vtype)
      ⊆ {χ : PositiveHomSpace vtype | (PositiveHomSpace.toPosHom χ) e = 0} := by
  refine Sσ_subset_eval_eq_of_ae_pinned (hc.constraintOf vtype) e 0 ?_
  intro φ₀ hφ₀ hσ
  exact ae_e_eq_zero_of_pinned hσ (hdeg φ₀ hφ₀)

end FlagAlgebras.MetaTheory
