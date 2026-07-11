import LeanFlagAlgebras.MetaTheory.GraphonRootedHom
import LeanFlagAlgebras.MetaTheory.GraphonHom
import LeanFlagAlgebras.MetaTheory.MeasureUniqueness
import LeanFlagAlgebras.MetaTheory.SupportClosure

/-! # The rooted-view measure of a graphon

The measure layer of the rooted transport: the law of the rooted conditional homomorphism
`graphonRootedHom W σ' u v` under a `W`-random root pair **is** the abstract extension
measure `ℙ[graphonHom W]`.  Concretely:

* `rootedViewPoint` — the (junk-totalised) map `I × I → X_{σ'}` sending an admissible pair to
  the point of its rooted conditional homomorphism, with `measurable_rootedViewPoint`.
* `rootMass` — the total root-factor mass `∫∫ rootWeight`; `rootMass_eq_typeFlag` identifies
  it with `φ_W`'s value on the two-vertex type flag (the normaliser of the extension
  measure's defining ratio, since `downwardNormalizingFactor` of the unit flag is `1` at a
  two-vertex type: `dnf_emptyFlag_two`).
* `integral_unnormRootedDensity` — integrating out the pinned coordinates recovers the
  unrooted induced density (`graphonFlagDensity`).
* `card_stdRooted_class` — **the rooted-vs-unrooted counting bridge**: the number of
  standard-rooted graphs in a rooted class is `downwardNormalizingFactor` times the number of
  labelled graphs in its unlabelled class (a same-size double count over pairs `(G, θ)` of a
  graph and a root placement, in the style of `FlagOperators.isoInjectiveMapSet`).
* `integral_rootedClassSum` — the **bridge integral identity** assembling the last two:
  `∫∫ (unnormalised rooted class-sum of F) = dnf F.2 · graphonProfileFun W ⟨F.1, unlabel F.2⟩`.
* `rootedViewMeasure` and `rootedViewMeasure_eq_extend` — the normalised weighted pushforward
  and its identification with `ℙ[graphonHom W]` via `measure_eq_of_integral_flag_eq`
  (agreement of all flag integrals; the flag-evaluation integrals of the pushforward reduce
  by the bridge identity to exactly the `φ₀⟦f⟧₀ / φ₀⟦1⟧₀` ratio of
  `probMeasure_extend_emptyType_positiveHom_spec`).

Everything here is Tier-1 (no certificate material); the kernel-dictionary consumers live in
`GraphonKernelTransport.lean`.
-/

open MeasureTheory unitInterval Finset
open scoped Classical ENNReal

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-! ## A junk point and the rooted-view map -/

/-- The constant graphon with kernel value `c ∈ [0,1]`. -/
noncomputable def constGraphon (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) : Graphon where
  W := fun _ _ => c
  measurable := measurable_const
  symm := fun _ _ => rfl
  nonneg := fun _ _ => h0
  le_one := fun _ _ => h1

/-- Every two-vertex-type homomorphism space is inhabited: the rooted conditional
homomorphism of the constant-`1/2` graphon at any pair is admissible (`rootWeight = 1/2`). -/
theorem nonempty_positiveHomSpace (σ' : FlagType (Fin 2)) :
    Nonempty (PositiveHomSpace σ') := by
  have hrw : rootWeight (constGraphon (1/2) (by norm_num) (by norm_num)) σ' (0 : I) (0 : I)
      = 1/2 := by
    unfold rootWeight adjWeight constGraphon
    dsimp only
    split_ifs <;> norm_num
  have hpos : RootAdmissible (constGraphon (1/2) (by norm_num) (by norm_num)) σ' (0 : I) (0 : I) := by
    unfold RootAdmissible
    rw [hrw]
    norm_num
  exact ⟨posHomPoint
    (graphonRootedHom (constGraphon (1/2) (by norm_num) (by norm_num)) σ' 0 0 hpos)⟩

/-- The rooted-view map: an admissible pair goes to the point of its rooted conditional
homomorphism; inadmissible pairs (a null set of the weighted measure) go to a junk point. -/
noncomputable def rootedViewPoint (W : Graphon) (σ' : FlagType (Fin 2)) (z : I × I) :
    PositiveHomSpace σ' :=
  if h : RootAdmissible W σ' z.1 z.2
  then posHomPoint (graphonRootedHom W σ' z.1 z.2 h)
  else Classical.choice (nonempty_positiveHomSpace σ')

@[simp]
theorem rootedViewPoint_of_admissible (W : Graphon) (σ' : FlagType (Fin 2)) (z : I × I)
    (h : RootAdmissible W σ' z.1 z.2) :
    rootedViewPoint W σ' z = posHomPoint (graphonRootedHom W σ' z.1 z.2 h) := dif_pos h

/-- Measurability of the rooted-view map (coordinatewise on the profile space via
`measurable_graphonRootedProfileFun`, with a measurable case split on `RootAdmissible`). -/
theorem measurable_rootedViewPoint (W : Graphon) (σ' : FlagType (Fin 2)) :
    Measurable (rootedViewPoint W σ') := by
  classical
  set s : Set (I × I) := {z | RootAdmissible W σ' z.1 z.2} with hsdef
  have hsmeas : MeasurableSet s :=
    measurableSet_lt measurable_const (measurable_rootWeight W σ')
  have hk : Measurable (fun p : s =>
      fun F => graphonRootedProfileFun W σ' (p : I × I).1 (p : I × I).2 F) :=
    measurable_pi_lambda _
      (fun F => (measurable_graphonRootedProfileFun W σ' F).comp measurable_subtype_coe)
  have hg : Measurable (fun p : s => graphonRootedProfile W σ' (p : I × I).1 (p : I × I).2) :=
    hk.subtype_mk
  have hcoeeq : ∀ p : s, (graphonRootedHom W σ' (p : I × I).1 (p : I × I).2 p.2).coe
      = graphonRootedProfile W σ' (p : I × I).1 (p : I × I).2 := by
    intro p
    apply Subtype.ext
    funext F
    exact graphonRootedHom_coe W σ' (p : I × I).1 (p : I × I).2 p.2 F
  have heq : (fun p : s => posHomPoint (graphonRootedHom W σ' (p : I × I).1 (p : I × I).2 p.2))
      = fun p : s => (⟨graphonRootedProfile W σ' (p : I × I).1 (p : I × I).2,
          ⟨graphonRootedHom W σ' (p : I × I).1 (p : I × I).2 p.2, hcoeeq p⟩⟩
        : PositiveHomSpace σ') := by
    funext p
    exact Subtype.ext (hcoeeq p)
  have hgood : Measurable (fun p : s =>
      posHomPoint (graphonRootedHom W σ' (p : I × I).1 (p : I × I).2 p.2)) := by
    rw [heq]
    exact Measurable.subtype_mk hg
  have hbad : Measurable (fun _ : (sᶜ : Set (I × I)) =>
      Classical.choice (nonempty_positiveHomSpace σ')) := measurable_const
  exact Measurable.dite hgood hbad hsmeas

/-! ## The mass and the analytic half of the bridge -/

/-- The total root-factor mass: `∫∫ W` at an edge type, `1 − ∫∫ W` at a non-edge type. -/
noncomputable def rootMass (W : Graphon) (σ' : FlagType (Fin 2)) : ℝ :=
  ∫ z : I × I, rootWeight W σ' z.1 z.2

/-- The swap automorphism of any two-vertex graph type: both permutations of `Fin 2`
preserve adjacency of a two-vertex `SimpleGraph` (the only possible edge is symmetric). -/
private noncomputable def swapIso (σ' : FlagType (Fin 2)) : σ' ≃g σ' where
  toEquiv := Equiv.swap 0 1
  map_rel_iff' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp <;>
      first
        | rfl
        | exact ⟨fun h => σ'.symm h, fun h => σ'.symm h⟩

/-- At a two-vertex type the downward normalizing factor of the unit flag is `1`
(`isomorphismCount` of the type on itself is `2 = 2!/0!`: the full symmetric group acts). -/
theorem dnf_emptyFlag_two (σ' : FlagType (Fin 2)) :
    downwardNormalizingFactor (emptyFlag σ') = 1 := by
  classical
  show downwardNormalizingFactor_labeledGraph (emptyLabeledGraph σ') = 1
  dsimp only [downwardNormalizingFactor_labeledGraph]
  have hnum : isomorphismCount (emptyLabeledGraph σ') = 2 := by
    dsimp only [isomorphismCount]
    have hset : (isoLabeledGraphSetWithSameGraph (emptyLabeledGraph σ')
          : Set (LabeledGraph σ' (Fin 2)))
        = {emptyLabeledGraph σ',
            (⟨σ', (swapIso σ').toRelEmbedding⟩ : LabeledGraph σ' (Fin 2))} := by
      ext H
      simp only [isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hgraph, -⟩
        -- `hgraph : σ' = H.graph`; the type embedding's underlying function is injective
        -- on `Fin 2`, so it is either the identity or the swap.
        obtain ⟨Hgraph, Htype⟩ := H
        simp only [emptyLabeledGraph] at hgraph
        subst hgraph
        have h0 : Htype 0 = 0 ∨ Htype 0 = 1 := by omega
        have h1 : Htype 1 = 0 ∨ Htype 1 = 1 := by omega
        have hinj : Htype 0 ≠ Htype 1 := by
          intro h
          exact absurd (Htype.inj' h) (by decide)
        rcases h0 with h0 | h0
        · left
          rcases h1 with h1 | h1
          · exact absurd (h0.trans h1.symm) hinj
          · congr 1
            apply RelEmbedding.ext
            intro t
            fin_cases t
            · exact h0
            · exact h1
        · right
          rcases h1 with h1 | h1
          · congr 1
            apply RelEmbedding.ext
            intro t
            fin_cases t
            · show Htype 0 = (swapIso σ').toRelEmbedding 0
              rw [h0]; rfl
            · show Htype 1 = (swapIso σ').toRelEmbedding 1
              rw [h1]; rfl
          · exact absurd (h1.trans h0.symm) hinj.symm
      · rintro (rfl | rfl)
        · exact ⟨rfl, flagEqv.refl _⟩
        · refine ⟨rfl, ?_⟩
          exact ⟨⟨swapIso σ', by funext t; rfl⟩⟩
    have hne : emptyLabeledGraph σ' ≠
        (⟨σ', (swapIso σ').toRelEmbedding⟩ : LabeledGraph σ' (Fin 2)) := by
      intro h
      have h0 : (emptyLabeledGraph σ').type_embed 0
          = ((⟨σ', (swapIso σ').toRelEmbedding⟩ : LabeledGraph σ' (Fin 2))).type_embed 0 := by
        rw [h]
      simp [emptyLabeledGraph, swapIso] at h0
    rw [Set.toFinset_congr hset, Set.toFinset_insert, Set.toFinset_singleton]
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  rw [hnum]
  norm_num

/-- Two graphs on `Fin 2` give the same unlabelled flag iff they are equal (not just
isomorphic): a `Fin 2`-graph is fully determined by its `Adj 0 1` truth value, and an
isomorphism forces that value to match, via the swap/identity case split on the bijection. -/
private lemma graphFlag_eq_typeFlag_iff (σ' : SimpleGraph (Fin 2)) (H : SimpleGraph (Fin 2)) :
    graphFlag H = graphFlag σ' ↔ H = σ' := by
  rw [graphFlag_eq_iff]
  constructor
  · rintro ⟨f⟩
    have hf0 : f 0 = 0 ∨ f 0 = 1 := by omega
    have hf1 : f 1 = 0 ∨ f 1 = 1 := by omega
    have hfinj : f 0 ≠ f 1 := f.injective.ne (by decide)
    have hkey : H.Adj 0 1 ↔ σ'.Adj 0 1 := by
      rcases hf0 with hf0 | hf0 <;> rcases hf1 with hf1 | hf1
      · exact absurd (hf0.trans hf1.symm) hfinj
      · rw [← f.map_adj_iff, hf0, hf1]
      · rw [← f.map_adj_iff, hf0, hf1]
        exact ⟨fun h => σ'.symm h, fun h => σ'.symm h⟩
      · exact absurd (hf1.trans hf0.symm) hfinj.symm
    ext a b
    fin_cases a <;> fin_cases b
    · simp
    · exact hkey
    · constructor <;> intro h
      · exact (hkey.mp h.symm).symm
      · exact (hkey.mpr h.symm).symm
    · simp
  · rintro rfl; exact ⟨SimpleGraph.Iso.refl⟩

/-- The induced density of a two-vertex graph type is the root-factor integral over `I × I`
(identifying `Fin 2 → I` with `I × I` via the volume-preserving `finTwoArrow` equivalence;
mirrors `graphonFlagDensity_top_two`, generalised past `⊤`). -/
private lemma graphonFlagDensity_two (W : Graphon) (σ' : SimpleGraph (Fin 2)) :
    graphonFlagDensity W σ' = ∫ z : I × I, adjWeight W (σ'.Adj 0 1) z.1 z.2 := by
  have hpairs : belowDiagPairs 2 = {((0 : Fin 2), (1 : Fin 2))} := by
    unfold belowDiagPairs; ext p; fin_cases p <;> simp
  have hw : ∀ x : Fin 2 → I, inducedWeight W σ' x = adjWeight W (σ'.Adj 0 1) (x 0) (x 1) := by
    intro x
    unfold inducedWeight
    rw [hpairs, Finset.prod_singleton]
  have hcomp : ∫ x : Fin 2 → I,
        adjWeight W (σ'.Adj 0 1) (MeasurableEquiv.finTwoArrow x).1
          (MeasurableEquiv.finTwoArrow x).2
      = ∫ z : I × I, adjWeight W (σ'.Adj 0 1) z.1 z.2 :=
    (measurePreserving_finTwoArrow (volume : Measure I)).integral_comp'
      (fun z : I × I => adjWeight W (σ'.Adj 0 1) z.1 z.2)
  calc graphonFlagDensity W σ'
      = ∫ x : Fin 2 → I, adjWeight W (σ'.Adj 0 1) (x 0) (x 1) := by
        unfold graphonFlagDensity
        exact integral_congr_ae (Filter.Eventually.of_forall hw)
    _ = ∫ x : Fin 2 → I, adjWeight W (σ'.Adj 0 1)
          (MeasurableEquiv.finTwoArrow x).1 (MeasurableEquiv.finTwoArrow x).2 := by rfl
    _ = ∫ z : I × I, adjWeight W (σ'.Adj 0 1) z.1 z.2 := hcomp

/-- The mass is `φ_W`'s value on the two-vertex type flag: `rootMass = φ_W ⟨σ'⟩₀`.

Proof route: `⟨σ'⟩₀ = ⟦basisVector ⟨2, σ'.toEmptyTypeFlag⟩⟧` (`RandomHom.lean:49-57`), so the
right side is `graphonProfileFun W ⟨2, σ'.toEmptyTypeFlag⟩` (`graphonHom_coe`), a sum of
two-vertex induced densities; compute both sides against `W.edgeDensity` (the unlabelled
two-vertex class of the type contains exactly one graph on `Fin 2`). -/
theorem rootMass_eq_typeFlag (W : Graphon) (σ' : FlagType (Fin 2)) :
    rootMass W σ' = (graphonHom W) ⟨σ'⟩₀ := by
  classical
  have hcoe : (graphonHom W) ⟨σ'⟩₀ = graphonProfileFun W ⟨2, σ'.toEmptyTypeFlag⟩ := by
    show (graphonHom W).coe _ = _
    exact graphonHom_coe W _
  rw [hcoe]
  have hteq : σ'.toEmptyTypeFlag = graphFlag σ' := rfl
  have hfilter : (Finset.univ.filter (fun H : SimpleGraph
        (Fin (⟨2, σ'.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).1) =>
        graphFlag H = (⟨2, σ'.toEmptyTypeFlag⟩ : FinFlag ∅ₜ).2)) = {σ'} := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hteq]
    exact graphFlag_eq_typeFlag_iff σ' H
  unfold graphonProfileFun
  rw [hfilter, Finset.sum_singleton, graphonFlagDensity_two]
  rfl

/-- **Integrating out the pinned coordinates recovers the unrooted density**: for any graph
`G` on `Fin n` (`2 ≤ n`),
`∫∫ unnormRootedDensity W hn G u v du dv = graphonFlagDensity W G`.

Proof route: unfold both sides to integrals of `inducedWeight`; the map
`(u, v, y) ↦ pinRoots hn u v y` from `I × I × (Fin n → I)` onto `Fin n → I` pushes the
product volume to the pi volume after discarding the two overridden dummy coordinates of
`y` (marginalise the two root coordinates of the target via
`volume_preserving_piEquivPiSubtypeProd` at the root predicate, then identify the two-point
pi factor with `I × I`). -/
private lemma integrable_of_bounds_rooted {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-! ### Private machinery for `integral_unnormRootedDensity`: splitting `Fin n → I` at the
two standard root coordinates and identifying that two-point factor with `I × I`. -/

private def rootPred {n : ℕ} (hn : 2 ≤ n) : Fin n → Prop :=
  fun i => i = Fin.castLE hn 0 ∨ i = Fin.castLE hn 1

private lemma castLE01_ne_pin {n : ℕ} (hn : 2 ≤ n) :
    Fin.castLE hn (0 : Fin 2) ≠ Fin.castLE hn (1 : Fin 2) := by
  intro h
  exact absurd (Fin.castLE_injective hn h) (by decide)

private def rootsEquivFin2 {n : ℕ} (hn : 2 ≤ n) : Fin 2 ≃ {i : Fin n // rootPred hn i} where
  toFun j := if j = 0 then ⟨Fin.castLE hn 0, Or.inl rfl⟩ else ⟨Fin.castLE hn 1, Or.inr rfl⟩
  invFun i := if i.1 = Fin.castLE hn 0 then 0 else 1
  left_inv j := by
    fin_cases j <;> simp [(castLE01_ne_pin hn).symm]
  right_inv i := by
    obtain ⟨i, hi⟩ := i
    rcases hi with h | h
    · subst h; simp
    · subst h
      have hne : Fin.castLE hn (1 : Fin 2) ≠ Fin.castLE hn (0 : Fin 2) :=
        (castLE01_ne_pin hn).symm
      simp [hne]

/-- The pi-split of `Fin n → I` at the root predicate. -/
private noncomputable def rootsSplit {n : ℕ} (hn : 2 ≤ n) :
    (Fin n → I) ≃ᵐ ({i : Fin n // rootPred hn i} → I) × ({i : Fin n // ¬ rootPred hn i} → I) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => I) (rootPred hn)

/-- The identification of the root part with `I × I`. -/
private noncomputable def rootsToII {n : ℕ} (hn : 2 ≤ n) :
    ({i : Fin n // rootPred hn i} → I) ≃ᵐ I × I :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => I) (rootsEquivFin2 hn).symm).trans
    MeasurableEquiv.finTwoArrow

private lemma rootsToII_apply {n : ℕ} (hn : 2 ≤ n) (r : {i : Fin n // rootPred hn i} → I) :
    (rootsToII hn) r = (r (rootsEquivFin2 hn 0), r (rootsEquivFin2 hn 1)) := by
  unfold rootsToII
  show MeasurableEquiv.finTwoArrow
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => I) (rootsEquivFin2 hn).symm r) = _
  have h0 := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 2 => I)
    (rootsEquivFin2 hn).symm r (rootsEquivFin2 hn 0)
  have h1 := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 2 => I)
    (rootsEquivFin2 hn).symm r (rootsEquivFin2 hn 1)
  simp only [Equiv.symm_apply_apply] at h0 h1
  rw [show (MeasurableEquiv.finTwoArrow :
      (Fin 2 → I) ≃ᵐ I × I) (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => I)
        (rootsEquivFin2 hn).symm r)
      = (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => I)
        (rootsEquivFin2 hn).symm r 0,
        MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => I) (rootsEquivFin2 hn).symm r 1) from rfl]
  rw [h0, h1]

private noncomputable def rootsPart {n : ℕ} (hn : 2 ≤ n) (u v : I) :
    {i : Fin n // rootPred hn i} → I :=
  fun i => if i.1 = Fin.castLE hn 0 then u else v

private instance rootsPos_prob {n : ℕ} (hn : 2 ≤ n) :
    IsProbabilityMeasure (volume : Measure ({i : Fin n // rootPred hn i} → I)) := by
  infer_instance

private instance rootsNeg_prob {n : ℕ} (hn : 2 ≤ n) :
    IsProbabilityMeasure (volume : Measure ({i : Fin n // ¬ rootPred hn i} → I)) := by
  infer_instance

private lemma rootsSplit_symm_apply_pos {n : ℕ} (hn : 2 ≤ n)
    (r : {i : Fin n // rootPred hn i} → I) (m : {i : Fin n // ¬ rootPred hn i} → I) (x : Fin n)
    (h : rootPred hn x) : (rootsSplit hn).symm (r, m) x = r ⟨x, h⟩ := by
  unfold rootsSplit
  show (Equiv.piEquivPiSubtypeProd (rootPred hn) (fun _ : Fin n => I)).symm (r, m) x = r ⟨x, h⟩
  simp [Equiv.piEquivPiSubtypeProd, h]

private lemma rootsSplit_symm_apply_neg {n : ℕ} (hn : 2 ≤ n)
    (r : {i : Fin n // rootPred hn i} → I) (m : {i : Fin n // ¬ rootPred hn i} → I) (x : Fin n)
    (h : ¬ rootPred hn x) : (rootsSplit hn).symm (r, m) x = m ⟨x, h⟩ := by
  unfold rootsSplit
  show (Equiv.piEquivPiSubtypeProd (rootPred hn) (fun _ : Fin n => I)).symm (r, m) x = m ⟨x, h⟩
  simp [Equiv.piEquivPiSubtypeProd, h]

private lemma rootsSplit_apply_snd {n : ℕ} (hn : 2 ≤ n) (y : Fin n → I) (x : Fin n)
    (h : ¬ rootPred hn x) : ((rootsSplit hn) y).2 ⟨x, h⟩ = y x := by
  unfold rootsSplit
  show ((Equiv.piEquivPiSubtypeProd (rootPred hn) (fun _ : Fin n => I)).toFun y).2 ⟨x, h⟩ = y x
  rfl

private lemma pinRoots_eq_rootsSplit_symm {n : ℕ} (hn : 2 ≤ n) (u v : I) (y : Fin n → I) :
    pinRoots hn u v y
      = (rootsSplit hn).symm (rootsPart hn u v, ((rootsSplit hn) y).2) := by
  funext x
  by_cases h0 : x = Fin.castLE hn 0
  · subst h0
    rw [pinRoots_apply_root0]
    have hrp : rootPred hn (Fin.castLE hn (0 : Fin 2)) := Or.inl rfl
    rw [rootsSplit_symm_apply_pos hn _ _ _ hrp]
    unfold rootsPart
    simp
  by_cases h1 : x = Fin.castLE hn 1
  · subst h1
    rw [pinRoots_apply_root1]
    have hrp : rootPred hn (Fin.castLE hn (1 : Fin 2)) := Or.inr rfl
    rw [rootsSplit_symm_apply_pos hn _ _ _ hrp]
    unfold rootsPart
    simp [(castLE01_ne_pin hn).symm]
  · rw [pinRoots_apply_of_ne hn u v y h0 h1]
    have hrp : ¬ rootPred hn x := fun hc => hc.elim h0 h1
    rw [rootsSplit_symm_apply_neg hn _ _ _ hrp, rootsSplit_apply_snd hn y x hrp]

private lemma marginal_step {n : ℕ} (hn : 2 ≤ n) (F : (Fin n → I) → ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) (u v : I) :
    ∫ y : Fin n → I, F (pinRoots hn u v y)
      = ∫ m : {i : Fin n // ¬ rootPred hn i} → I,
          F ((rootsSplit hn).symm (rootsPart hn u v, m)) := by
  set K : ({i : Fin n // rootPred hn i} → I) × ({i : Fin n // ¬ rootPred hn i} → I) → ℝ :=
    fun z => F ((rootsSplit hn).symm (rootsPart hn u v, z.2)) with hKdef
  have hFeq : (fun y : Fin n → I => F (pinRoots hn u v y)) = fun y => K (rootsSplit hn y) := by
    funext y
    rw [hKdef]
    simp only
    congr 1
    exact pinRoots_eq_rootsSplit_symm hn u v y
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => I) (rootPred hn)
  show ∫ y : Fin n → I, F (pinRoots hn u v y) = _
  rw [hFeq]
  rw [show (rootsSplit hn) = MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => I)
      (rootPred hn) from rfl] at *
  rw [hmp.integral_comp' K]
  have hKmeas : Measurable K := by
    apply hF.comp
    apply (rootsSplit hn).symm.measurable.comp
    exact measurable_const.prodMk measurable_snd
  have hKint : Integrable K volume := by
    apply integrable_of_bounds_rooted hKmeas
    · intro z; exact hF0 _
    · intro z; exact hF1 _
  rw [show (volume : Measure (({i : Fin n // rootPred hn i} → I)
      × ({i : Fin n // ¬ rootPred hn i} → I)))
      = (volume : Measure ({i : Fin n // rootPred hn i} → I)).prod volume from rfl,
    integral_prod _ hKint]
  simp only [hKdef]
  rw [MeasureTheory.integral_const]
  simp

/-- Integrating out the two overridden dummy coordinates of `y` (marginalising them via
`volume_preserving_piEquivPiSubtypeProd` at the root predicate and identifying the two-point
factor with `I × I`) recovers the plain sample integral. -/
private theorem integral_pinRoots_eq {n : ℕ} (hn : 2 ≤ n) (F : (Fin n → I) → ℝ)
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) :
    ∫ z : I × I, ∫ y : Fin n → I, F (pinRoots hn z.1 z.2 y) = ∫ x : Fin n → I, F x := by
  have hstep : (fun z : I × I => ∫ y : Fin n → I, F (pinRoots hn z.1 z.2 y))
      = fun z : I × I => ∫ m : {i : Fin n // ¬ rootPred hn i} → I,
          F ((rootsSplit hn).symm (rootsPart hn z.1 z.2, m)) := by
    funext z
    exact marginal_step hn F hF hF0 hF1 z.1 z.2
  rw [hstep]
  set g : ({i : Fin n // rootPred hn i} → I) → ℝ :=
    fun r => ∫ m : {i : Fin n // ¬ rootPred hn i} → I, F ((rootsSplit hn).symm (r, m))
    with hgdef
  have hstep2 : (fun z : I × I => ∫ m : {i : Fin n // ¬ rootPred hn i} → I,
      F ((rootsSplit hn).symm (rootsPart hn z.1 z.2, m)))
      = fun z : I × I => g ((rootsToII hn).symm z) := by
    funext z
    rw [hgdef]
    simp only
    have hR : (rootsToII hn) (rootsPart hn z.1 z.2) = (z.1, z.2) := by
      rw [rootsToII_apply]
      unfold rootsPart
      show (if (rootsEquivFin2 hn (0 : Fin 2) : Fin n) = Fin.castLE hn 0 then z.1 else z.2,
          if (rootsEquivFin2 hn (1 : Fin 2) : Fin n) = Fin.castLE hn 0 then z.1 else z.2) = _
      simp [rootsEquivFin2]
    have hRsymm := (rootsToII hn).symm_apply_apply (rootsPart hn z.1 z.2)
    rw [hR] at hRsymm
    rw [hRsymm]
  rw [hstep2]
  have hmpToII : MeasurePreserving (rootsToII hn) volume volume := by
    unfold rootsToII
    exact (measurePreserving_finTwoArrow (volume : Measure I)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => I) (rootsEquivFin2 hn).symm)
  have hmpToIIsymm : MeasurePreserving (rootsToII hn).symm volume volume :=
    MeasurePreserving.symm (rootsToII hn) hmpToII
  rw [hmpToIIsymm.integral_comp' g]
  rw [hgdef]
  simp only
  set K2 : ({i : Fin n // rootPred hn i} → I) × ({i : Fin n // ¬ rootPred hn i} → I) → ℝ :=
    fun z => F ((rootsSplit hn).symm z) with hK2def
  have hmpSplit := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => I) (rootPred hn)
  have hK2meas : Measurable K2 := hF.comp (rootsSplit hn).symm.measurable
  have hK2int : Integrable K2 volume := by
    apply integrable_of_bounds_rooted hK2meas
    · intro z; exact hF0 _
    · intro z; exact hF1 _
  have hfinal : ∫ r : {i : Fin n // rootPred hn i} → I,
      ∫ m : {i : Fin n // ¬ rootPred hn i} → I, F ((rootsSplit hn).symm (r, m))
      = ∫ y : Fin n → I, F y := by
    rw [show (volume : Measure (({i : Fin n // rootPred hn i} → I)
        × ({i : Fin n // ¬ rootPred hn i} → I)))
        = (volume : Measure ({i : Fin n // rootPred hn i} → I)).prod volume from rfl] at *
    rw [← integral_prod K2 hK2int]
    have hcomp : ∫ y : Fin n → I, K2 (rootsSplit hn y) = ∫ z, K2 z ∂(volume.prod volume) :=
      hmpSplit.integral_comp' K2
    have hcomp2 : (fun y : Fin n → I => K2 (rootsSplit hn y)) = F := by
      funext y
      show F ((rootsSplit hn).symm (rootsSplit hn y)) = F y
      rw [MeasurableEquiv.symm_apply_apply]
    rw [hcomp2] at hcomp
    exact hcomp.symm
  exact hfinal

theorem integral_unnormRootedDensity (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) :
    ∫ z : I × I, unnormRootedDensity W hn G z.1 z.2 = graphonFlagDensity W G := by
  unfold unnormRootedDensity graphonFlagDensity
  exact integral_pinRoots_eq hn (inducedWeight W G) (measurable_inducedWeight W G)
    (fun x => inducedWeight_nonneg W G x) (fun x => inducedWeight_le_one W G x)

/-! ## The counting half of the bridge -/

/-! ### Private machinery for `card_stdRooted_class`: the roots-vs-graph double count -/

/-- `unlabel` of any labelled-graph flag is `graphFlag` of its underlying graph: both sides
unfold to the same `RelEmbedding.ofIsEmpty` construction. -/
private lemma unlabel_quot_eq_graphFlag {σ' : FlagType (Fin 2)} {n : ℕ}
    (L : LabeledGraph σ' (Fin n)) :
    unlabel (⟦L⟧ : Flag σ' (Fin n)) = graphFlag L.graph := rfl

/-- Root-compatibility at an arbitrary root embedding `θ : Fin 2 ↪ Fin n` (generalising
`RootCompatible`, which is the case `θ = Fin.castLE hn`). -/
private def RootCompatibleAt (σ' : FlagType (Fin 2)) {n : ℕ} (θ : Fin 2 ↪ Fin n)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b : Fin 2, σ'.Adj a b ↔ G.Adj (θ a) (θ b)

/-- The labelled graph rooted at an arbitrary embedding `θ` (generalising `mkStdRooted`). -/
private def mkRootedAt (σ' : FlagType (Fin 2)) {n : ℕ} (θ : Fin 2 ↪ Fin n)
    (G : SimpleGraph (Fin n)) (h : RootCompatibleAt σ' θ G) : LabeledGraph σ' (Fin n) where
  graph := G
  type_embed := ⟨θ, fun {a b} => (h a b).symm⟩

@[simp]
private lemma mkRootedAt_graph (σ' : FlagType (Fin 2)) {n : ℕ} (θ : Fin 2 ↪ Fin n)
    (G : SimpleGraph (Fin n)) (h : RootCompatibleAt σ' θ G) :
    (mkRootedAt σ' θ G h).graph = G := rfl

@[simp]
private lemma mkRootedAt_type_embed_toEmbedding (σ' : FlagType (Fin 2)) {n : ℕ}
    (θ : Fin 2 ↪ Fin n) (G : SimpleGraph (Fin n)) (h : RootCompatibleAt σ' θ G) :
    (mkRootedAt σ' θ G h).type_embed.toEmbedding = θ := rfl

/-- A labelled graph is `mkRootedAt` of its own graph and type-embedding. -/
private lemma eq_mkRootedAt_self (σ' : FlagType (Fin 2)) {n : ℕ} (L : LabeledGraph σ' (Fin n)) :
    L = mkRootedAt σ' L.type_embed.toEmbedding L.graph (fun a b => type_embed_Adj_iff L a b) := by
  cases L with
  | mk graph type_embed =>
    congr 1

/-- The standard root embedding `Fin.castLE hn`, as a `Function.Embedding`. -/
private def castLEEmb {n : ℕ} (hn : 2 ≤ n) : Fin 2 ↪ Fin n :=
  ⟨Fin.castLE hn, Fin.castLE_injective hn⟩

private lemma mkRootedAt_castLEEmb_eq_mkStdRooted (σ' : FlagType (Fin 2)) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (h : RootCompatibleAt σ' (castLEEmb hn) G) :
    mkRootedAt σ' (castLEEmb hn) G h = mkStdRooted σ' hn G h := rfl

/-- Root-compatibility transports along a permutation carrying one root embedding to
another. -/
private lemma rootCompatibleAt_comap_of_perm (σ' : FlagType (Fin 2)) {n : ℕ}
    {θ₁ θ₂ : Fin 2 ↪ Fin n} (π : Fin n ≃ Fin n) (hπ : ∀ i, π (θ₁ i) = θ₂ i)
    {G : SimpleGraph (Fin n)} (h : RootCompatibleAt σ' θ₁ G) :
    RootCompatibleAt σ' θ₂ (G.comap ⇑π.symm) := by
  have hθ : ∀ i, π.symm (θ₂ i) = θ₁ i := fun i => by rw [← hπ i, Equiv.symm_apply_apply]
  intro a b
  show σ'.Adj a b ↔ G.Adj (π.symm (θ₂ a)) (π.symm (θ₂ b))
  rw [hθ a, hθ b]
  exact h a b

/-- The transported rooted labelled graph is flag-equivalent to the original. -/
private lemma mkRootedAt_comap_perm_flagEqv (σ' : FlagType (Fin 2)) {n : ℕ}
    {θ₁ θ₂ : Fin 2 ↪ Fin n} (π : Fin n ≃ Fin n) (hπ : ∀ i, π (θ₁ i) = θ₂ i)
    {G : SimpleGraph (Fin n)} (h : RootCompatibleAt σ' θ₁ G) :
    mkRootedAt σ' θ₂ (G.comap ⇑π.symm) (rootCompatibleAt_comap_of_perm σ' π hπ h)
      ∼f mkRootedAt σ' θ₁ G h := by
  have hθ : ∀ i, π.symm (θ₂ i) = θ₁ i := fun i => by rw [← hπ i, Equiv.symm_apply_apply]
  refine ⟨⟨SimpleGraph.Iso.comap π.symm G, ?_⟩⟩
  funext a
  show (SimpleGraph.Iso.comap π.symm G) (θ₂ a) = θ₁ a
  rw [SimpleGraph.Iso.comap_apply]
  exact hθ a

/-- A labelled graph rooted at `θ` (via any proof) whose type-embedding realises `θ` is the
graph itself: extracted from `L.type_embed.toEmbedding = θ` via `eq_mkRootedAt_self` and proof
irrelevance of `RootCompatibleAt`. -/
private lemma mkRootedAt_eq_of_toEmbedding_eq (σ' : FlagType (Fin 2)) {n : ℕ}
    {L : LabeledGraph σ' (Fin n)} {θ : Fin 2 ↪ Fin n} (hL : L.type_embed.toEmbedding = θ)
    (h : RootCompatibleAt σ' θ L.graph) :
    mkRootedAt σ' θ L.graph h = L := by
  subst hL
  exact (eq_mkRootedAt_self σ' L).symm

/-- Membership in the `θ`-rooted fibre gives root-compatibility of the underlying graph at
`θ`. -/
private lemma exists_rootedAt_of_mem (σ' : FlagType (Fin 2)) {n : ℕ} {θ : Fin 2 ↪ Fin n}
    {L : LabeledGraph σ' (Fin n)} (hL : L.type_embed.toEmbedding = θ) :
    RootCompatibleAt σ' θ L.graph := by
  intro a b
  rw [← hL]
  exact type_embed_Adj_iff L a b

/-- A labelled graph is determined by its graph and its type-embedding function: since the
underlying `graph` fields agree, `subst` identifies the two ambient `SimpleGraph`s before
comparing the (now non-dependent) `type_embed` fields via `RelEmbedding.ext`. Avoids the
motive failures of rewriting a `LabeledGraph`'s `graph` field underneath a `type_embed` that
depends on it. -/
private lemma labeledGraph_ext_of_toEmbedding (σ' : FlagType (Fin 2)) {n : ℕ}
    {L L' : LabeledGraph σ' (Fin n)} (hgraph : L.graph = L'.graph)
    (hemb : L.type_embed.toEmbedding = L'.type_embed.toEmbedding) : L = L' := by
  cases L with
  | mk graph type_embed =>
    cases L' with
    | mk graph' type_embed' =>
      dsimp only at hgraph hemb
      subst hgraph
      congr 1
      apply RelEmbedding.ext
      intro a
      exact DFunLike.congr_fun hemb a

/-- **Fibre-independence over the root embedding**: for a fixed flag class `F2`, the number of
labelled graphs on `Fin n` in that class whose type-embedding realises `θ` does not depend on
`θ` (any two embeddings differ by a permutation, which transports one rooted representative
set onto the other bijectively; the flag class is preserved by
`mkRootedAt_comap_perm_flagEqv`). -/
private lemma card_rootedAt_fiber_eq (σ' : FlagType (Fin 2)) {n : ℕ} (F2 : Flag σ' (Fin n))
    (θ₁ θ₂ : Fin 2 ↪ Fin n) :
    (Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
        (⟦L⟧ : Flag σ' (Fin n)) = F2 ∧ L.type_embed.toEmbedding = θ₁)).card
      = (Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
        (⟦L⟧ : Flag σ' (Fin n)) = F2 ∧ L.type_embed.toEmbedding = θ₂)).card := by
  obtain ⟨π, hπ⟩ := exists_perm_comp_emb θ₁ θ₂
  have hπsymm : ∀ i, π.symm (θ₂ i) = θ₁ i := fun i => by rw [← hπ i, Equiv.symm_apply_apply]
  refine Finset.card_bij'
    (fun L hL => mkRootedAt σ' θ₂ (L.graph.comap ⇑π.symm)
      (rootCompatibleAt_comap_of_perm σ' π hπ
        (exists_rootedAt_of_mem σ' (Finset.mem_filter.mp hL).2.2)))
    (fun L hL => mkRootedAt σ' θ₁ (L.graph.comap ⇑π)
      (rootCompatibleAt_comap_of_perm σ' π.symm hπsymm
        (exists_rootedAt_of_mem σ' (Finset.mem_filter.mp hL).2.2)))
    ?_ ?_ ?_ ?_
  · intro L hL
    dsimp only
    obtain ⟨hFL, hθL⟩ := (Finset.mem_filter.mp hL).2
    have hc : RootCompatibleAt σ' θ₁ L.graph := exists_rootedAt_of_mem σ' hθL
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, mkRootedAt_type_embed_toEmbedding _ _ _ _⟩
    rw [flagEqv.sound (mkRootedAt_comap_perm_flagEqv σ' π hπ hc),
      mkRootedAt_eq_of_toEmbedding_eq σ' hθL hc]
    exact hFL
  · intro L hL
    dsimp only
    obtain ⟨hFL, hθL⟩ := (Finset.mem_filter.mp hL).2
    have hc : RootCompatibleAt σ' θ₂ L.graph := exists_rootedAt_of_mem σ' hθL
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, mkRootedAt_type_embed_toEmbedding _ _ _ _⟩
    have hflag := flagEqv.sound (mkRootedAt_comap_perm_flagEqv σ' π.symm hπsymm hc)
    simp only [Equiv.symm_symm] at hflag
    rw [hflag, mkRootedAt_eq_of_toEmbedding_eq σ' hθL hc]
    exact hFL
  · intro L hL
    dsimp only
    obtain ⟨-, hθL⟩ := (Finset.mem_filter.mp hL).2
    apply labeledGraph_ext_of_toEmbedding σ'
    · show (L.graph.comap ⇑π.symm).comap ⇑π = L.graph
      rw [SimpleGraph.comap_comap]
      have hidfun : (⇑π.symm ∘ ⇑π : Fin n → Fin n) = id := funext fun x => π.symm_apply_apply x
      rw [hidfun, SimpleGraph.comap_id]
    · exact hθL.symm
  · intro L hL
    dsimp only
    obtain ⟨-, hθL⟩ := (Finset.mem_filter.mp hL).2
    apply labeledGraph_ext_of_toEmbedding σ'
    · show (L.graph.comap ⇑π).comap ⇑π.symm = L.graph
      rw [SimpleGraph.comap_comap]
      have hidfun : (⇑π ∘ ⇑π.symm : Fin n → Fin n) = id := funext fun x => π.apply_symm_apply x
      rw [hidfun, SimpleGraph.comap_id]
    · exact hθL.symm

/-- **Fibre size over the underlying graph**: for `K0` isomorphic (as a plain graph) to
`Frep.graph`, the number of labelled graphs on `Fin n` in the flag class of `Frep` whose
underlying graph is exactly `K0` equals `isomorphismCount Frep` (transport `Frep`'s
type-embedding along the graph isomorphism `K0 ≃g Frep.graph` to exhibit the fibre as
literally `isoLabeledGraphSetWithSameGraph` of the transported representative). -/
private lemma card_graph_fiber_eq_isomorphismCount (σ' : FlagType (Fin 2)) {n : ℕ}
    (Frep : LabeledGraph σ' (Fin n)) {K0 : SimpleGraph (Fin n)}
    (hK0 : graphFlag K0 = graphFlag Frep.graph) :
    (Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
        (⟦L⟧ : Flag σ' (Fin n)) = ⟦Frep⟧ ∧ L.graph = K0)).card = isomorphismCount Frep := by
  obtain ⟨e⟩ := (graphFlag_eq_iff K0 Frep.graph).mp hK0
  set L0 : LabeledGraph σ' (Fin n) := ⟨K0, Frep.type_embed.trans e.symm.toRelEmbedding⟩ with hL0def
  have hL0graph : L0.graph = K0 := rfl
  have hL0iso : L0 ∼f Frep := by
    refine ⟨⟨e, ?_⟩⟩
    funext a
    show e (L0.type_embed a) = Frep.type_embed a
    show e (e.symm (Frep.type_embed a)) = Frep.type_embed a
    exact e.apply_symm_apply _
  have hset : (Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
        (⟦L⟧ : Flag σ' (Fin n)) = ⟦Frep⟧ ∧ L.graph = K0))
      = (isoLabeledGraphSetWithSameGraph L0).toFinset := by
    ext L
    simp only [Set.mem_toFinset, isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hL0graph]
    constructor
    · rintro ⟨hLquot, hLgraph⟩
      exact ⟨hLgraph.symm, flagEqv.trans hL0iso (flagEqv.symm (Quotient.exact hLquot))⟩
    · rintro ⟨hLgraph, hLiso⟩
      exact ⟨flagEqv.sound (flagEqv.trans (flagEqv.symm hLiso) hL0iso), hLgraph.symm⟩
  rw [hset]
  exact isomorphismCount_respect_eqv hL0iso

/-- The graph-fibre of a flag class is empty over any graph not isomorphic to a
representative. -/
private lemma card_graph_fiber_eq_zero_of_not_mem (σ' : FlagType (Fin 2)) {n : ℕ}
    (F2 : Flag σ' (Fin n)) {K0 : SimpleGraph (Fin n)} (hK0 : graphFlag K0 ≠ unlabel F2) :
    (Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
        (⟦L⟧ : Flag σ' (Fin n)) = F2 ∧ L.graph = K0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro L _
  rintro ⟨hLquot, hLgraph⟩
  apply hK0
  have := unlabel_quot_eq_graphFlag L
  rw [hLquot, hLgraph] at this
  exact this.symm

/-- **The rooted-vs-unrooted counting bridge**: the number of standard-rooted graphs in the
rooted class of `F` equals `downwardNormalizingFactor F.2` times the number of labelled
graphs in the unlabelled class of `F` (as rationals).

Proof route: double-count the pairs `(G, θ)` of a graph
`G : SimpleGraph (Fin F.1)` and a root placement `θ : Fin 2 ↪ Fin F.1` whose labelled graph
`(G, θ)` is flag-isomorphic to a representative of `F.2`.  Counting by `θ` first gives
`(number of unlabelled-class members) × isomorphismCount`; counting by `G` first gives
`(number of root placements = F.1!/(F.1−2)!) × (the standard-rooted class count)` — the
per-`θ` count is independent of `θ` by conjugating with a permutation carrying `θ` to the
standard placement (`exists_perm_comp_emb` + `graphComapEquiv`, the idiom of
`StdRootedBridge`).  Divide; `downwardNormalizingFactor` is by definition
`isomorphismCount / (F.1!/(F.1−2)!)` (`FlagOperators.lean:60-64`). -/
theorem card_stdRooted_class {σ' : FlagType (Fin 2)} (F : FinFlag σ') :
    ((Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
        ∃ h : RootCompatible σ' (finFlag_size_ge_n₀ F) G,
          (⟦mkStdRooted σ' (finFlag_size_ge_n₀ F) G h⟧ : Flag σ' (Fin F.1)) = F.2)).card : ℚ)
      = downwardNormalizingFactor F.2
        * ((Finset.univ.filter (fun H : SimpleGraph (Fin F.1) =>
            graphFlag H = unlabel F.2)).card : ℚ) := by
  classical
  set n := F.1 with hndef
  set hn : 2 ≤ n := finFlag_size_ge_n₀ F with hndefh
  set Frep : LabeledGraph σ' (Fin n) := F.2.out with hFrepdef
  have hFrepquot : (⟦Frep⟧ : Flag σ' (Fin n)) = F.2 := Quotient.out_eq F.2
  set T : Finset (LabeledGraph σ' (Fin n)) :=
    Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) => (⟦L⟧ : Flag σ' (Fin n)) = F.2)
    with hTdef
  set U : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter (fun H : SimpleGraph (Fin n) => graphFlag H = unlabel F.2) with hUdef
  -- Step A: the standard-rooted count is the `castLEEmb`-fibre of `T`.
  have hstepA : (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        ∃ h : RootCompatible σ' hn G, (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F.2)).card
      = (T.filter (fun L => L.type_embed.toEmbedding = castLEEmb hn)).card := by
    refine Finset.card_bij'
      (fun G hG => mkStdRooted σ' hn G (Finset.mem_filter.mp hG).2.choose)
      (fun L _ => L.graph)
      ?hi ?hj ?linv ?rinv
    case hi =>
      intro G hG
      obtain ⟨-, hex⟩ := Finset.mem_filter.mp hG
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [hTdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hex.choose_spec⟩
    case hj =>
      intro L hL
      obtain ⟨hLT, hLemb⟩ := Finset.mem_filter.mp hL
      have hc : RootCompatibleAt σ' (castLEEmb hn) L.graph := exists_rootedAt_of_mem σ' hLemb
      rw [hTdef, Finset.mem_filter] at hLT
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hc, ?_⟩
      show (⟦mkRootedAt σ' (castLEEmb hn) L.graph hc⟧ : Flag σ' (Fin n)) = F.2
      rw [mkRootedAt_eq_of_toEmbedding_eq σ' hLemb hc]
      exact hLT.2
    case linv =>
      intro G hG
      rfl
    case rinv =>
      intro L hL
      obtain ⟨-, hLemb⟩ := Finset.mem_filter.mp hL
      have hc : RootCompatibleAt σ' (castLEEmb hn) L.graph := exists_rootedAt_of_mem σ' hLemb
      show mkStdRooted σ' hn L.graph _ = L
      rw [← mkRootedAt_castLEEmb_eq_mkStdRooted σ' hn L.graph hc]
      exact mkRootedAt_eq_of_toEmbedding_eq σ' hLemb hc
  -- Step B (Way 2): fibring `T` by the root embedding gives a constant-size fibre count.
  have hstepB : T.card
      = (Fintype.card (Fin 2 ↪ Fin n))
        * (T.filter (fun L => L.type_embed.toEmbedding = castLEEmb hn)).card := by
    have hfiber : T.card
        = ∑ θ : Fin 2 ↪ Fin n, (T.filter (fun L => L.type_embed.toEmbedding = θ)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    have hTfilter : ∀ θ : Fin 2 ↪ Fin n, T.filter (fun L => L.type_embed.toEmbedding = θ)
        = Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
            (⟦L⟧ : Flag σ' (Fin n)) = F.2 ∧ L.type_embed.toEmbedding = θ) := by
      intro θ
      rw [hTdef, Finset.filter_filter]
    have hconst : ∀ θ ∈ (Finset.univ : Finset (Fin 2 ↪ Fin n)),
        (T.filter (fun L => L.type_embed.toEmbedding = θ)).card
          = (T.filter (fun L => L.type_embed.toEmbedding = castLEEmb hn)).card := by
      intro θ _
      rw [hTfilter, hTfilter]
      exact card_rootedAt_fiber_eq σ' F.2 θ (castLEEmb hn)
    rw [hfiber, Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ,
      Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
  -- Step C (Way 1): fibring `T` by the underlying graph gives `U.card * isomorphismCount Frep`.
  have hUgraph : unlabel F.2 = graphFlag Frep.graph := by
    rw [← hFrepquot]; exact unlabel_quot_eq_graphFlag Frep
  have hstepC : T.card = U.card * isomorphismCount Frep := by
    have hfiber : T.card = ∑ K0 : SimpleGraph (Fin n), (T.filter (fun L => L.graph = K0)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    have hTfilter : ∀ K0 : SimpleGraph (Fin n), T.filter (fun L => L.graph = K0)
        = Finset.univ.filter (fun L : LabeledGraph σ' (Fin n) =>
            (⟦L⟧ : Flag σ' (Fin n)) = F.2 ∧ L.graph = K0) := by
      intro K0
      rw [hTdef, Finset.filter_filter]
    have hpointwise : ∀ K0 : SimpleGraph (Fin n),
        (T.filter (fun L => L.graph = K0)).card
          = if K0 ∈ U then isomorphismCount Frep else 0 := by
      intro K0
      rw [hTfilter]
      by_cases hK0 : K0 ∈ U
      · rw [if_pos hK0]
        rw [hUdef, Finset.mem_filter] at hK0
        have hgraphFlag : graphFlag K0 = graphFlag Frep.graph := hK0.2.trans hUgraph
        have hcard := card_graph_fiber_eq_isomorphismCount σ' Frep hgraphFlag
        rw [hFrepquot] at hcard
        exact hcard
      · rw [if_neg hK0]
        apply card_graph_fiber_eq_zero_of_not_mem σ' F.2
        simp only [hUdef, Finset.mem_filter, Finset.mem_univ, true_and] at hK0
        exact hK0
    rw [hfiber, Finset.sum_congr rfl (fun K0 _ => hpointwise K0), Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, smul_eq_mul]
  -- Assemble: combine the two counts of `T.card` and divide.
  have hcast : (Fintype.card (Fin 2 ↪ Fin n) : ℚ)
      * ((T.filter (fun L => L.type_embed.toEmbedding = castLEEmb hn)).card : ℚ)
      = (U.card : ℚ) * (isomorphismCount Frep : ℚ) := by
    exact_mod_cast hstepB.symm.trans hstepC
  have hM : Fintype.card (Fin 2 ↪ Fin n) = n.factorial / (n - 2).factorial := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    symm
    apply Nat.div_eq_of_eq_mul_left (Nat.factorial_pos (n - 2))
    rw [mul_comm]
    exact (Nat.factorial_mul_descFactorial hn).symm
  have hMpos : (0 : ℚ) < (Fintype.card (Fin 2 ↪ Fin n) : ℚ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨castLEEmb hn⟩
  have hdnf : downwardNormalizingFactor F.2
      = (isomorphismCount Frep : ℚ) / (Fintype.card (Fin 2 ↪ Fin n) : ℚ) := by
    rw [← hFrepquot]
    show downwardNormalizingFactor_labeledGraph Frep = _
    unfold downwardNormalizingFactor_labeledGraph
    rw [hM]
  rw [hstepA, hdnf, div_mul_eq_mul_div, eq_div_iff hMpos.ne']
  rw [mul_comm ((T.filter (fun L => L.type_embed.toEmbedding = castLEEmb hn)).card : ℚ)
    (Fintype.card (Fin 2 ↪ Fin n) : ℚ)]
  rw [hcast]
  ring

/-! ## The bridge integral identity -/

/-- The unnormalised rooted class-sum (the numerator of `graphonRootedProfileFun`). -/
noncomputable def rootedClassSum (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (F : FinFlag σ') : ℝ :=
  ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
      ∃ h : RootCompatible σ' (finFlag_size_ge_n₀ F) G,
        (⟦mkStdRooted σ' (finFlag_size_ge_n₀ F) G h⟧ : Flag σ' (Fin F.1)) = F.2),
    unnormRootedDensity W (finFlag_size_ge_n₀ F) G u v

/-- The class-sum is the profile times the root factor (including at inadmissible pairs,
where both sides vanish: the class-sum is squeezed by `sum_unnormRootedDensity`). -/
theorem rootedClassSum_eq_profile_mul (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (F : FinFlag σ') :
    rootedClassSum W σ' u v F
      = graphonRootedProfileFun W σ' u v F * rootWeight W σ' u v := by
  unfold graphonRootedProfileFun rootedClassSum
  set hn := finFlag_size_ge_n₀ F with hndef
  rcases (rootWeight_nonneg W σ' u v).lt_or_eq with hpos | hz
  · exact (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
  · rw [← hz, mul_zero]
    have hsub : (Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
        ∃ h : RootCompatible σ' hn G,
          (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin F.1)) = F.2))
        ⊆ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) => RootCompatible σ' hn G) := by
      intro G hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
      exact hG.1
    have hbound : (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
          ∃ h : RootCompatible σ' hn G,
            (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin F.1)) = F.2),
          unnormRootedDensity W hn G u v)
        ≤ ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) => RootCompatible σ' hn G),
          unnormRootedDensity W hn G u v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun G _ _ => unnormRootedDensity_nonneg W hn G u v)
    rw [sum_unnormRootedDensity W σ' hn u v, ← hz] at hbound
    have hnonneg : 0 ≤ (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
          ∃ h : RootCompatible σ' hn G,
            (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin F.1)) = F.2),
          unnormRootedDensity W hn G u v) :=
      Finset.sum_nonneg fun G _ => unnormRootedDensity_nonneg W hn G u v
    linarith

/-- `graphonFlagDensity` is constant on the graph-isomorphism class of a graph: transport
the isomorphism to a `comap` along its underlying `Equiv` and apply
`graphonFlagDensity_comap_equiv`. -/
private lemma graphonFlagDensity_eq_of_graphFlag_eq (W : Graphon) {n : ℕ}
    {H H0 : SimpleGraph (Fin n)} (h : graphFlag H = graphFlag H0) :
    graphonFlagDensity W H = graphonFlagDensity W H0 := by
  obtain ⟨e⟩ := (graphFlag_eq_iff H H0).mp h
  have hcomap : H0.comap ⇑e.toEquiv = H := by
    ext u v
    show H0.Adj (e.toEquiv u) (e.toEquiv v) ↔ H.Adj u v
    rw [show e.toEquiv u = e u from rfl, show e.toEquiv v = e v from rfl]
    exact SimpleGraph.Iso.map_adj_iff e
  rw [← hcomap]
  exact graphonFlagDensity_comap_equiv W e.toEquiv H0

/-- **The bridge integral identity**: the total rooted mass of the class of `F` is the
`downwardNormalizingFactor`-weighted unrooted mass of its unlabelling.

Assembles `integral_unnormRootedDensity` (each summand integrates to the unrooted density),
constancy of `graphonFlagDensity` on unlabelled classes (`graphonFlagDensity_comap_equiv` +
`graphFlag_eq_iff`), and `card_stdRooted_class`. -/
theorem integral_rootedClassSum (W : Graphon) (σ' : FlagType (Fin 2)) (F : FinFlag σ') :
    ∫ z : I × I, rootedClassSum W σ' z.1 z.2 F
      = (downwardNormalizingFactor F.2 : ℝ)
        * graphonProfileFun W ⟨F.1, unlabel F.2⟩ := by
  set n := F.1 with hndefn
  set hn := finFlag_size_ge_n₀ F with hndef
  set rootedFilter : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∃ h : RootCompatible σ' hn G, (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F.2)
    with hrootedFilterdef
  set U : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter (fun H : SimpleGraph (Fin n) => graphFlag H = unlabel F.2) with hUdef
  -- (a)+(b): integral of the sum is the sum of unrooted densities over the rooted filter.
  have hintegral : ∫ z : I × I, rootedClassSum W σ' z.1 z.2 F
      = ∑ G ∈ rootedFilter, graphonFlagDensity W G := by
    unfold rootedClassSum
    rw [hrootedFilterdef]
    rw [integral_finset_sum _
      (fun G (_ : G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
          ∃ h : RootCompatible σ' hn G, (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F.2)) =>
        integrable_of_bounds_rooted (measurable_unnormRootedDensity W hn G)
          (fun z => unnormRootedDensity_nonneg W hn G z.1 z.2)
          (fun z => unnormRootedDensity_le_one W hn G z.1 z.2))]
    exact Finset.sum_congr rfl (fun G _ => integral_unnormRootedDensity W hn G)
  rw [hintegral]
  -- every `G` in the rooted filter unlabels to `unlabel F.2`, i.e. lies in `U`.
  have hmem_unlabel : ∀ G ∈ rootedFilter, graphFlag G = unlabel F.2 := by
    intro G hG
    rw [hrootedFilterdef, Finset.mem_filter] at hG
    obtain ⟨-, h, hquot⟩ := hG
    exact congrArg unlabel hquot
  by_cases hU : U.Nonempty
  · obtain ⟨H0, hH0⟩ := hU
    rw [hUdef, Finset.mem_filter] at hH0
    have hD_rooted : ∀ G ∈ rootedFilter, graphonFlagDensity W G = graphonFlagDensity W H0 :=
      fun G hG => graphonFlagDensity_eq_of_graphFlag_eq W ((hmem_unlabel G hG).trans hH0.2.symm)
    have hD_U : ∀ H ∈ U, graphonFlagDensity W H = graphonFlagDensity W H0 := by
      intro H hH
      rw [hUdef, Finset.mem_filter] at hH
      exact graphonFlagDensity_eq_of_graphFlag_eq W (hH.2.trans hH0.2.symm)
    rw [Finset.sum_congr rfl hD_rooted, Finset.sum_const, nsmul_eq_mul]
    show (rootedFilter.card : ℝ) * graphonFlagDensity W H0
        = (downwardNormalizingFactor F.2 : ℝ) * graphonProfileFun W ⟨n, unlabel F.2⟩
    have hprofile : graphonProfileFun W (⟨n, unlabel F.2⟩ : FinFlag ∅ₜ) = U.card * graphonFlagDensity W H0 := by
      show (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => graphFlag H = unlabel F.2),
          graphonFlagDensity W H) = _
      rw [← hUdef, Finset.sum_congr rfl hD_U, Finset.sum_const, nsmul_eq_mul]
    rw [hprofile, ← mul_assoc]
    congr 1
    have hcard := card_stdRooted_class F
    rw [← hrootedFilterdef, ← hUdef] at hcard
    exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty] at hU
    have hcard := card_stdRooted_class F
    rw [← hrootedFilterdef, ← hUdef, hU, Finset.card_empty] at hcard
    simp only [Nat.cast_zero, mul_zero] at hcard
    have hrooted_empty : rootedFilter = ∅ := by
      rw [← Finset.card_eq_zero]; exact_mod_cast hcard
    rw [hrooted_empty, Finset.sum_empty]
    show (0 : ℝ) = (downwardNormalizingFactor F.2 : ℝ) * graphonProfileFun W ⟨n, unlabel F.2⟩
    have hprofile0 : graphonProfileFun W (⟨n, unlabel F.2⟩ : FinFlag ∅ₜ) = 0 := by
      show (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => graphFlag H = unlabel F.2),
          graphonFlagDensity W H) = 0
      rw [← hUdef, hU, Finset.sum_empty]
    rw [hprofile0, mul_zero]

/-! ## The rooted-view measure and its identification -/

/-- **The rooted-view measure**: the normalised `rootWeight`-weighted law of the rooted
conditional homomorphism — the law of the view of `φ_W` from a `W`-random ordered root pair
(an edge for `τ`, a non-edge for `η`). -/
noncomputable def rootedViewMeasure (W : Graphon) (σ' : FlagType (Fin 2)) :
    Measure (PositiveHomSpace σ') :=
  (ENNReal.ofReal (rootMass W σ'))⁻¹ •
    Measure.map (rootedViewPoint W σ')
      ((volume : Measure (I × I)).withDensity
        fun z => ENNReal.ofReal (rootWeight W σ' z.1 z.2))

/-- `toPosHom` undoes `posHomPoint` (private copy of the `ComplementHom.lean` lemma of the same
name, avoiding a new import). -/
private lemma toPosHom_posHomPoint (σ' : FlagType (Fin 2)) (φ : PositiveHom σ') :
    PositiveHomSpace.toPosHom (posHomPoint φ) = φ := by
  apply PositiveHom.coe_injective
  apply (DFunLike.coe_injective (F := FlagDensitySpace σ'))
  funext F
  show (PositiveHomSpace.toPosHom (posHomPoint φ)).coe F = φ.coe F
  rw [PositiveHom.coe_flag, PositiveHomSpace.toPosHom_basisVector, posHomPoint_val_apply,
    ← PositiveHom.coe_flag]

/-- **The measure identification**: the rooted-view measure of `W` is the abstract extension
measure of `φ_W` at the type `σ'`.

Proof route: both are probability measures (the rooted-view mass is
`rootMass / rootMass = 1` under `hσ` via `rootMass_eq_typeFlag`); by
`measure_eq_of_integral_flag_eq` it suffices to match all flag-evaluation integrals.  For a
flag `F`, the pushforward integral is
`(1/rootMass) ∫∫ rootWeight · graphonRootedProfileFun … F = (1/rootMass) ∫∫ rootedClassSum`
(`rootedClassSum_eq_profile_mul`; the junk region is `rootWeight`-null), which by
`integral_rootedClassSum` is `dnf F.2 · graphonProfileFun W ⟨F.1, unlabel F.2⟩ / rootMass`;
the extension-measure integral is `φ_W ⟦F⟧₀ / φ_W ⟦1⟧₀`
(`probMeasure_extend_emptyType_positiveHom_spec`), which unfolds to the same value by
`downward_basisVector`, `one_downward_eq`, `dnf_emptyFlag_two`, and `rootMass_eq_typeFlag`;
extend from basis flags to all of `FlagAlgebra σ'` by linearity of both sides (integral and
algebra evaluation), as `measure_eq_of_integral_flag_eq`'s callers reduce to basis vectors. -/
theorem rootedViewMeasure_eq_extend (W : Graphon) (σ' : FlagType (Fin 2))
    (hσ : (graphonHom W) ⟨σ'⟩₀ > 0) :
    rootedViewMeasure W σ'
      = (probMeasure_extend_emptyType_positiveHom (graphonHom W) hσ
          : Measure (PositiveHomSpace σ')) := by
  have hmass : rootMass W σ' > 0 := by rw [rootMass_eq_typeFlag]; exact hσ
  set c : ENNReal := ENNReal.ofReal (rootMass W σ') with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrootWeight_integrable : Integrable (fun z : I × I => rootWeight W σ' z.1 z.2) volume :=
    integrable_of_bounds_rooted (measurable_rootWeight W σ')
      (fun z => rootWeight_nonneg W σ' z.1 z.2) (fun z => rootWeight_le_one W σ' z.1 z.2)
  have hmeasφ : Measurable (rootedViewPoint W σ') := measurable_rootedViewPoint W σ'
  set ν : Measure (I × I) :=
    (volume : Measure (I × I)).withDensity (fun z => ENNReal.ofReal (rootWeight W σ' z.1 z.2))
    with hνdef
  have hνuniv : ν Set.univ = c := by
    rw [hνdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hrootWeight_integrable
        (Filter.Eventually.of_forall (fun z => rootWeight_nonneg W σ' z.1 z.2))]
    rfl
  have hprob : IsProbabilityMeasure (rootedViewMeasure W σ') := by
    constructor
    show ((c⁻¹) • Measure.map (rootedViewPoint W σ') ν) Set.univ = 1
    rw [Measure.smul_apply, Measure.map_apply hmeasφ MeasurableSet.univ, Set.preimage_univ,
      hνuniv, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hc0 hctop
  set P : ProbabilityMeasure (PositiveHomSpace σ') := ⟨rootedViewMeasure W σ', hprob⟩ with hPdef
  set Q : ProbabilityMeasure (PositiveHomSpace σ') :=
    probMeasure_extend_emptyType_positiveHom (graphonHom W) hσ with hQdef
  have hmR : (0 : ℝ) ≤ rootMass W σ' := hmass.le
  have hcinv_toReal : c⁻¹.toReal = (rootMass W σ')⁻¹ := by
    rw [hcdef, ENNReal.toReal_inv, ENNReal.toReal_ofReal hmR]
  have haemeasφ : AEMeasurable (rootedViewPoint W σ') ν := hmeasφ.aemeasurable
  have hρmeas : Measurable (fun z : I × I => ENNReal.ofReal (rootWeight W σ' z.1 z.2)) :=
    (measurable_rootWeight W σ').ennreal_ofReal
  -- **The basis case**: the crux computation.
  have hbasis : ∀ F : FinFlag σ',
      ∫ χ, (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ')
        ∂(rootedViewMeasure W σ')
        = ((graphonHom W) ⟦(⟦basisVector F⟧ : FlagAlgebra σ')⟧₀)
          / ((graphonHom W) ⟦(1 : FlagAlgebra σ')⟧₀) := by
    intro F
    have hpointwise : ∀ z : I × I,
        (ENNReal.ofReal (rootWeight W σ' z.1 z.2)).toReal
          • (PositiveHomSpace.toPosHom (rootedViewPoint W σ' z))
              (⟦basisVector F⟧ : FlagAlgebra σ')
          = rootedClassSum W σ' z.1 z.2 F := by
      intro z
      rw [smul_eq_mul, ENNReal.toReal_ofReal (rootWeight_nonneg W σ' z.1 z.2),
        rootedClassSum_eq_profile_mul,
        mul_comm (graphonRootedProfileFun W σ' z.1 z.2 F) (rootWeight W σ' z.1 z.2)]
      by_cases hadm : RootAdmissible W σ' z.1 z.2
      · congr 1
        rw [rootedViewPoint_of_admissible W σ' z hadm, toPosHom_posHomPoint σ',
          ← PositiveHom.coe_flag, graphonRootedHom_coe]
      · unfold RootAdmissible at hadm
        push_neg at hadm
        have hz0 : rootWeight W σ' z.1 z.2 = 0 :=
          le_antisymm hadm (rootWeight_nonneg W σ' z.1 z.2)
        rw [hz0]; ring
    have haesm : AEStronglyMeasurable
        (fun χ : PositiveHomSpace σ' =>
          (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ'))
        (Measure.map (rootedViewPoint W σ') ν) :=
      (continuous_eval (⟦basisVector F⟧ : FlagAlgebra σ')).aestronglyMeasurable
    have hLHS : ∫ χ, (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ')
        ∂(rootedViewMeasure W σ')
        = (rootMass W σ')⁻¹
          * ((downwardNormalizingFactor F.2 : ℝ) * graphonProfileFun W ⟨F.1, unlabel F.2⟩) := by
      show ∫ χ, (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ')
          ∂((c⁻¹) • Measure.map (rootedViewPoint W σ') ν) = _
      rw [integral_smul_measure, integral_map haemeasφ haesm, hνdef,
        integral_withDensity_eq_integral_toReal_smul hρmeas
          (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
      rw [funext hpointwise, integral_rootedClassSum, smul_eq_mul, hcinv_toReal]
    have hRHS : ((graphonHom W) ⟦(⟦basisVector F⟧ : FlagAlgebra σ')⟧₀)
          / ((graphonHom W) ⟦(1 : FlagAlgebra σ')⟧₀)
        = ((downwardNormalizingFactor F.2 : ℝ) * graphonProfileFun W ⟨F.1, unlabel F.2⟩)
          / (rootMass W σ') := by
      congr 1
      · rw [downward_basisVector, PositiveHom.map_smul, ← PositiveHom.coe_flag, graphonHom_coe]
      · rw [one_downward_eq, PositiveHom.map_smul, ← rootMass_eq_typeFlag, dnf_emptyFlag_two]
        norm_num
    rw [hLHS, hRHS, div_eq_inv_mul]
  -- **Linearity**: extend from basis vectors to all of `FlagAlgebra σ'`.
  have hspec : ∀ f : FlagAlgebra σ',
      ∫ χ, (PositiveHomSpace.toPosHom χ) f ∂(rootedViewMeasure W σ')
        = ((graphonHom W) ⟦f⟧₀) / ((graphonHom W) ⟦(1 : FlagAlgebra σ')⟧₀) := by
    intro f
    rcases Quotient.exists_rep f with ⟨frep, rfl⟩
    rw [flagVector_eq_sum_basisVector frep, sum_quot]
    have hintegrable : ∀ F ∈ frep.support,
        Integrable (fun χ : PositiveHomSpace σ' =>
            (PositiveHomSpace.toPosHom χ) (⟦frep F • basisVector F⟧ : FlagAlgebra σ'))
          (rootedViewMeasure W σ') := by
      intro F _
      have hbase : Integrable (fun χ : PositiveHomSpace σ' =>
          (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ'))
          (rootedViewMeasure W σ') :=
        BoundedContinuousFunction.integrable _
          (BoundedContinuousFunction.mkOfCompact (evalContinuousMap (⟦basisVector F⟧ : FlagAlgebra σ')))
      have heq : (fun χ : PositiveHomSpace σ' =>
            (PositiveHomSpace.toPosHom χ) (⟦frep F • basisVector F⟧ : FlagAlgebra σ'))
          = fun χ => frep F * (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ') := by
        funext χ
        rw [smul_quot, PositiveHom.map_smul]
      rw [heq]
      exact hbase.const_mul (frep F)
    simp_rw [PositiveHom.map_sum]
    rw [integral_finset_sum _ hintegrable]
    have hstep : ∀ F ∈ frep.support,
        ∫ χ, (PositiveHomSpace.toPosHom χ) (⟦frep F • basisVector F⟧ : FlagAlgebra σ')
            ∂(rootedViewMeasure W σ')
          = (frep F * ((graphonHom W) ⟦(⟦basisVector F⟧ : FlagAlgebra σ')⟧₀))
            / ((graphonHom W) ⟦(1 : FlagAlgebra σ')⟧₀) := by
      intro F _
      have heq : (fun χ : PositiveHomSpace σ' =>
            (PositiveHomSpace.toPosHom χ) (⟦frep F • basisVector F⟧ : FlagAlgebra σ'))
          = fun χ => frep F * (PositiveHomSpace.toPosHom χ) (⟦basisVector F⟧ : FlagAlgebra σ') := by
        funext χ
        rw [smul_quot, PositiveHom.map_smul]
      rw [heq, integral_const_mul, hbasis F, mul_div_assoc]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_div]
    congr 1
    rw [downward_sum, PositiveHom.map_sum]
    apply Finset.sum_congr rfl
    intro F _
    rw [smul_quot, downward_smul, PositiveHom.map_smul]
  -- **Assemble**: both are probability measures agreeing on all flag-evaluation integrals.
  suffices hPQ : P = Q from congrArg (fun p : ProbabilityMeasure (PositiveHomSpace σ') =>
    (p : Measure (PositiveHomSpace σ'))) hPQ
  apply measure_eq_of_integral_flag_eq
  intro f
  show ∫ χ, (PositiveHomSpace.toPosHom χ) f ∂(rootedViewMeasure W σ')
      = ∫ χ, (PositiveHomSpace.toPosHom χ) f ∂(Q : Measure (PositiveHomSpace σ'))
  rw [hspec f, hQdef, probMeasure_extend_emptyType_positiveHom_spec hσ f]

end FlagAlgebras.MetaTheory
