import LeanFlagAlgebras.MetaTheory.GraphonInducedDensity
import LeanFlagAlgebras.MetaTheory.StdRootedBridge

/-! # Rooted induced densities of a graphon

The analytic layer of the rooted conditional homomorphism: for a graphon `W`, a
standard-rooted graph `G` on `Fin n` (`StdRootedBridge`), and pinned root samples `u v : I`,
the **unnormalised rooted density**

`unnormRootedDensity W hn G u v = ∫_{y : Fin n → I} inducedWeight W G (pinRoots hn u v y)`

integrates the induced weight with the two root coordinates overridden by `u, v` (the two
dummy coordinates of `y` integrate out on the probability space; this keeps every lemma free
of `Fin (n−2)` arithmetic).  For a `RootCompatible` graph the `(0,1)`-pair factor of the
weight is the **root factor** `rootWeight W σ' u v` (`W u v` at an edge type, `1 − W u v` at a
non-edge type), which is why all identities below carry it:

* `unnormRootedDensity_two` — on a two-vertex graph the density **is** its root factor.
* `sum_unnormRootedDensity` — total mass: the densities of all `RootCompatible` graphs on
  `Fin n` sum to `rootWeight` (extension partition from the two-vertex case).
* `unnormRootedDensity_comap_rootfix_perm` — invariance under root-fixing relabelling.
* `unnormRootedDensity_extension_sum` — the extension partition along `Fin.castLE`.
* `unnormRootedDensity_block_mul` — the glued block product: two rooted densities at the
  same type multiply to `rootWeight` times the total density of the graphs on
  `Fin (n₁ + n₂ − 2)` restricting to the two factors along the glue embeddings (the roots
  are SHARED, whence the single surviving `rootWeight` factor).
* `exists_rootFixing_emb_range` / `stdRooted_subset_iso_iff` — the subset↔embedding bridge
  the profile's averaging argument runs on (rooted analogues of the `orderEmbOfFin` and
  `comap_iso_induce_range` steps of `GraphonHom.lean`).

Everything is stated for an arbitrary two-vertex type `σ' : FlagType (Fin 2)`; no
certificate material enters.
-/

open MeasureTheory unitInterval Finset
open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-- On a probability space, a measurable function squeezed between two constants is
integrable (local copy of the `GraphonInducedDensity` workhorse). -/
private lemma integrable_of_bounds' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-! ## The root factor and pinning -/

/-- The root factor: the edge weight of the root pair itself — `W u v` if the type has an
edge, `1 − W u v` if not. -/
noncomputable def rootWeight (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I) : ℝ :=
  adjWeight W (σ'.Adj 0 1) u v

lemma rootWeight_nonneg (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I) :
    0 ≤ rootWeight W σ' u v :=
  adjWeight_nonneg W _ u v

lemma rootWeight_le_one (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I) :
    rootWeight W σ' u v ≤ 1 :=
  adjWeight_le_one W _ u v

/-- The pinned pair `(u, v)` is admissible for `(W, σ')` when its root factor is positive:
the conditional profile exists at such pairs. -/
def RootAdmissible (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I) : Prop :=
  0 < rootWeight W σ' u v

/-- The root factor is jointly measurable in the pinned pair. -/
lemma measurable_rootWeight (W : Graphon) (σ' : FlagType (Fin 2)) :
    Measurable (fun z : I × I => rootWeight W σ' z.1 z.2) := by
  unfold rootWeight adjWeight
  have hpair : Measurable (fun z : I × I => W.W z.1 z.2) :=
    show Measurable (Function.uncurry W.W) from W.measurable
  split_ifs
  · exact hpair
  · exact measurable_const.sub hpair

/-- Override the two root coordinates of a sample by the pinned values `u, v`. -/
noncomputable def pinRoots {n : ℕ} (hn : 2 ≤ n) (u v : I) (y : Fin n → I) : Fin n → I :=
  Function.update (Function.update y (Fin.castLE hn 0) u) (Fin.castLE hn 1) v

/-- The two standard roots are distinct (private helper for the `pinRoots` API). -/
private lemma castLE01_ne {n : ℕ} (hn : 2 ≤ n) :
    Fin.castLE hn (0 : Fin 2) ≠ Fin.castLE hn (1 : Fin 2) := by
  intro h
  exact absurd (Fin.castLE_injective hn h) (by decide)

@[simp]
lemma pinRoots_apply_root0 {n : ℕ} (hn : 2 ≤ n) (u v : I) (y : Fin n → I) :
    pinRoots hn u v y (Fin.castLE hn 0) = u := by
  unfold pinRoots
  rw [Function.update_of_ne (castLE01_ne hn), Function.update_self]

@[simp]
lemma pinRoots_apply_root1 {n : ℕ} (hn : 2 ≤ n) (u v : I) (y : Fin n → I) :
    pinRoots hn u v y (Fin.castLE hn 1) = v := by
  unfold pinRoots
  rw [Function.update_self]

lemma pinRoots_apply_of_ne {n : ℕ} (hn : 2 ≤ n) (u v : I) (y : Fin n → I) {i : Fin n}
    (h0 : i ≠ Fin.castLE hn 0) (h1 : i ≠ Fin.castLE hn 1) :
    pinRoots hn u v y i = y i := by
  unfold pinRoots
  rw [Function.update_of_ne h1, Function.update_of_ne h0]

/-- Pinning commutes with precomposition by a root-fixing permutation. -/
lemma pinRoots_comp_rootfix_perm {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (π : Fin ℓ ≃ Fin ℓ)
    (hπ : ∀ a : Fin 2, π (Fin.castLE hℓ a) = Fin.castLE hℓ a) (u v : I) (y : Fin ℓ → I) :
    pinRoots hℓ u v y ∘ ⇑π = pinRoots hℓ u v (y ∘ ⇑π) := by
  funext i
  show pinRoots hℓ u v y (π i) = pinRoots hℓ u v (y ∘ ⇑π) i
  by_cases h0 : i = Fin.castLE hℓ 0
  · subst h0
    rw [hπ 0, pinRoots_apply_root0, pinRoots_apply_root0]
  by_cases h1 : i = Fin.castLE hℓ 1
  · subst h1
    rw [hπ 1, pinRoots_apply_root1, pinRoots_apply_root1]
  have hπ0 : π i ≠ Fin.castLE hℓ 0 := by
    intro h
    exact h0 (π.injective (h.trans (hπ 0).symm))
  have hπ1 : π i ≠ Fin.castLE hℓ 1 := by
    intro h
    exact h1 (π.injective (h.trans (hπ 1).symm))
  rw [pinRoots_apply_of_ne hℓ u v y hπ0 hπ1, pinRoots_apply_of_ne hℓ u v (y ∘ ⇑π) h0 h1]
  rfl

/-- `pinRoots` at fixed pinned values `u, v` is measurable in the sample `y`. -/
private lemma measurable_pinRoots {n : ℕ} (hn : 2 ≤ n) (u v : I) :
    Measurable (pinRoots hn u v) := by
  apply measurable_pi_lambda (pinRoots hn u v)
  intro i
  by_cases h0 : i = Fin.castLE hn 0
  · have heq : (fun y : Fin n → I => pinRoots hn u v y i) = fun _ => u := by
      subst h0; funext y; exact pinRoots_apply_root0 hn u v y
    rw [heq]; exact measurable_const
  by_cases h1 : i = Fin.castLE hn 1
  · have heq : (fun y : Fin n → I => pinRoots hn u v y i) = fun _ => v := by
      subst h1; funext y; exact pinRoots_apply_root1 hn u v y
    rw [heq]; exact measurable_const
  · have heq : (fun y : Fin n → I => pinRoots hn u v y i) = fun y => y i :=
      funext fun y => pinRoots_apply_of_ne hn u v y h0 h1
    rw [heq]; exact measurable_pi_apply i

/-- Jointly in `(u, v, y)`, `pinRoots` is measurable. -/
private lemma measurable_pinRoots_uncurry {n : ℕ} (hn : 2 ≤ n) :
    Measurable (fun p : (I × I) × (Fin n → I) => pinRoots hn p.1.1 p.1.2 p.2) := by
  apply measurable_pi_lambda (fun p : (I × I) × (Fin n → I) => pinRoots hn p.1.1 p.1.2 p.2)
  intro i
  by_cases h0 : i = Fin.castLE hn 0
  · have heq : (fun p : (I × I) × (Fin n → I) => pinRoots hn p.1.1 p.1.2 p.2 i)
        = fun p => p.1.1 := by
      subst h0; funext p; exact pinRoots_apply_root0 hn p.1.1 p.1.2 p.2
    rw [heq]; exact (measurable_fst.comp measurable_fst)
  by_cases h1 : i = Fin.castLE hn 1
  · have heq : (fun p : (I × I) × (Fin n → I) => pinRoots hn p.1.1 p.1.2 p.2 i)
        = fun p => p.1.2 := by
      subst h1; funext p; exact pinRoots_apply_root1 hn p.1.1 p.1.2 p.2
    rw [heq]; exact (measurable_snd.comp measurable_fst)
  · have heq : (fun p : (I × I) × (Fin n → I) => pinRoots hn p.1.1 p.1.2 p.2 i)
        = fun p => p.2 i :=
      funext fun p => pinRoots_apply_of_ne hn p.1.1 p.1.2 p.2 h0 h1
    rw [heq]; exact (measurable_pi_apply i).comp measurable_snd

/-! ## The unnormalised rooted density -/

/-- The unnormalised rooted density: the induced weight integrated with the root
coordinates pinned at `u, v`.  For `RootCompatible` graphs its root-pair factor is
`rootWeight`. -/
noncomputable def unnormRootedDensity (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : I) : ℝ :=
  ∫ y : Fin n → I, inducedWeight W G (pinRoots hn u v y)

/-- The pinned integrand is measurable, nonneg, and bounded (a private bundling used
throughout this section). -/
private lemma measurable_pinnedInducedWeight (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : I) :
    Measurable (fun y : Fin n → I => inducedWeight W G (pinRoots hn u v y)) :=
  (measurable_inducedWeight W G).comp (measurable_pinRoots hn u v)

private lemma integrable_pinnedInducedWeight (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : I) :
    Integrable (fun y : Fin n → I => inducedWeight W G (pinRoots hn u v y))
      (volume : Measure (Fin n → I)) :=
  integrable_of_bounds' (measurable_pinnedInducedWeight W hn G u v)
    (fun _y => inducedWeight_nonneg W G _) (fun _y => inducedWeight_le_one W G _)

lemma unnormRootedDensity_nonneg (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : I) : 0 ≤ unnormRootedDensity W hn G u v :=
  integral_nonneg fun _y => inducedWeight_nonneg W G _

lemma unnormRootedDensity_le_one (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : I) : unnormRootedDensity W hn G u v ≤ 1 := by
  have h : unnormRootedDensity W hn G u v ≤ ∫ _ : Fin n → I, (1 : ℝ) :=
    integral_mono (integrable_pinnedInducedWeight W hn G u v) (integrable_const 1)
      (fun y => inducedWeight_le_one W G _)
  simpa using h

/-- Joint measurability in the pinned pair (needed for the rooted-view measure). -/
lemma measurable_unnormRootedDensity (W : Graphon) {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) :
    Measurable (fun z : I × I => unnormRootedDensity W hn G z.1 z.2) := by
  have hjoint : Measurable (fun p : (I × I) × (Fin n → I) =>
      inducedWeight W G (pinRoots hn p.1.1 p.1.2 p.2)) :=
    (measurable_inducedWeight W G).comp (measurable_pinRoots_uncurry hn)
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- On a two-vertex graph the unnormalised rooted density is exactly the root factor of its
own adjacency (the only pair is the root pair, and the integrand is constant). -/
theorem unnormRootedDensity_two (W : Graphon) (G : SimpleGraph (Fin 2)) (u v : I) :
    unnormRootedDensity W (le_refl 2) G u v = adjWeight W (G.Adj 0 1) u v := by
  have hpairs : belowDiagPairs 2 = {((0 : Fin 2), (1 : Fin 2))} := by
    unfold belowDiagPairs
    ext p
    fin_cases p <;> simp
  have hconst : ∀ y : Fin 2 → I,
      inducedWeight W G (pinRoots (le_refl 2) u v y) = adjWeight W (G.Adj 0 1) u v := by
    intro y
    unfold inducedWeight
    rw [hpairs, Finset.prod_singleton]
    have h0 : pinRoots (le_refl 2) u v y 0 = u := by
      have := pinRoots_apply_root0 (le_refl 2) u v y
      simpa [Fin.castLE_rfl] using this
    have h1 : pinRoots (le_refl 2) u v y 1 = v := by
      have := pinRoots_apply_root1 (le_refl 2) u v y
      simpa [Fin.castLE_rfl] using this
    rw [h0, h1]
  unfold unnormRootedDensity
  rw [integral_congr_ae (Filter.Eventually.of_forall hconst)]
  simp

/-- `RootCompatible` is exactly the `Fin.castLE`-fibre condition over the type itself. -/
theorem rootCompatible_iff_comap_eq (σ' : FlagType (Fin 2)) {n : ℕ} (hn : 2 ≤ n)
    (H : SimpleGraph (Fin n)) :
    RootCompatible σ' hn H ↔ H.comap (Fin.castLE hn) = σ' := by
  unfold RootCompatible
  constructor
  · intro h
    ext a b
    rw [SimpleGraph.comap_adj]
    exact (h a b).symm
  · intro h a b
    rw [← h]
    exact SimpleGraph.comap_adj

/-! ## The four structural identities -/

/-- Sort the image of a pair under `e` into increasing order (private copy of the
`GraphonInducedDensity` reindexing helper). -/
private def sortPair {n : ℕ} (e : Fin n ≃ Fin n) (p : Fin n × Fin n) : Fin n × Fin n :=
  if e p.1 < e p.2 then (e p.1, e p.2) else (e p.2, e p.1)

private lemma sortPair_mem {n : ℕ} (e : Fin n ≃ Fin n) {p : Fin n × Fin n}
    (hp : p ∈ belowDiagPairs n) : sortPair e p ∈ belowDiagPairs n := by
  have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hne : e p.1 ≠ e p.2 := fun h => (ne_of_lt hp') (e.injective h)
  unfold sortPair belowDiagPairs
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (not_lt.mp h) hne.symm

private lemma sortPair_left_inv {n : ℕ} (e : Fin n ≃ Fin n) {p : Fin n × Fin n}
    (hp : p ∈ belowDiagPairs n) : sortPair e.symm (sortPair e p) = p := by
  have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hne : e p.1 ≠ e p.2 := fun h => (ne_of_lt hp') (e.injective h)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have hsp : sortPair e p = (e p.1, e p.2) := by unfold sortPair; rw [if_pos h1]
    rw [hsp]
    simp [sortPair, hp', Equiv.symm_apply_apply]
  · have hsp : sortPair e p = (e p.2, e p.1) := by
      unfold sortPair; rw [if_neg (not_lt.mpr h1.le)]
    rw [hsp]
    simp [sortPair, not_lt.mpr hp'.le, Equiv.symm_apply_apply]

/-- The pointwise reindexing identity: precomposing the vertex labels of the induced weight
with `e` amounts to comapping the graph along `e` (private copy of the
`GraphonInducedDensity` lemma of the same shape). -/
private lemma inducedWeight_comap_equiv {n : ℕ} (W : Graphon) (e : Fin n ≃ Fin n)
    (G : SimpleGraph (Fin n)) (x : Fin n → I) :
    inducedWeight W (G.comap e) x = inducedWeight W G (x ∘ e.symm) := by
  unfold inducedWeight
  apply Finset.prod_nbij' (sortPair e) (sortPair e.symm)
  · exact fun p hp => sortPair_mem e hp
  · exact fun q hq => sortPair_mem e.symm hq
  · exact fun p hp => sortPair_left_inv e hp
  · exact fun q hq => by simpa [Equiv.symm_symm] using sortPair_left_inv e.symm hq
  · intro p hp
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hne : e p.1 ≠ e p.2 := fun h => (ne_of_lt hp') (e.injective h)
    show adjWeight W ((G.comap e).Adj p.1 p.2) (x p.1) (x p.2)
        = adjWeight W (G.Adj (sortPair e p).1 (sortPair e p).2)
            ((x ∘ e.symm) (sortPair e p).1) ((x ∘ e.symm) (sortPair e p).2)
    rw [SimpleGraph.comap_adj]
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have hsp : sortPair e p = (e p.1, e p.2) := by unfold sortPair; rw [if_pos h1]
      simp [hsp, Function.comp, Equiv.symm_apply_apply]
    · have hsp : sortPair e p = (e p.2, e p.1) := by
        unfold sortPair; rw [if_neg (not_lt.mpr h1.le)]
      simp only [hsp, Function.comp, Equiv.symm_apply_apply]
      calc adjWeight W (G.Adj (e p.1) (e p.2)) (x p.1) (x p.2)
          = adjWeight W (G.Adj (e p.2) (e p.1)) (x p.1) (x p.2) :=
            adjWeight_congr W (G.adj_comm (e p.1) (e p.2)) _ _
        _ = adjWeight W (G.Adj (e p.2) (e p.1)) (x p.2) (x p.1) :=
            adjWeight_symm W _ _ _

/-- **Root-fixing relabelling invariance** of the unnormalised rooted density.

Proof route: the pointwise reindex of `inducedWeight` along `π` (as in
`graphonFlagDensity_comap_equiv`, whose pointwise lemma is private in
`GraphonInducedDensity` — reprove a private copy), `pinRoots_comp_rootfix_perm`, and the
change of variables `volume_measurePreserving_piCongrLeft`. -/
theorem unnormRootedDensity_comap_rootfix_perm (W : Graphon) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (π : Fin ℓ ≃ Fin ℓ) (hπ : ∀ a : Fin 2, π (Fin.castLE hℓ a) = Fin.castLE hℓ a)
    (H : SimpleGraph (Fin ℓ)) (u v : I) :
    unnormRootedDensity W hℓ (H.comap ⇑π) u v = unnormRootedDensity W hℓ H u v := by
  have hπsymm : ∀ a : Fin 2, π.symm (Fin.castLE hℓ a) = Fin.castLE hℓ a := by
    intro a
    apply π.injective
    rw [Equiv.apply_symm_apply, hπ a]
  have hpointwise : ∀ y : Fin ℓ → I,
      inducedWeight W (H.comap ⇑π) (pinRoots hℓ u v y)
        = inducedWeight W H (pinRoots hℓ u v (y ∘ ⇑π.symm)) := by
    intro y
    rw [inducedWeight_comap_equiv W π H (pinRoots hℓ u v y),
      pinRoots_comp_rootfix_perm hℓ π.symm hπsymm u v y]
  have hΦ : ∀ y : Fin ℓ → I,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => I) π) y = y ∘ ⇑π.symm := by
    intro y
    funext j
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin ℓ => I) π y (π.symm j)
    simpa [Equiv.apply_symm_apply] using h
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin ℓ => I) π
  have hcomp := hmp.integral_comp' (fun z : Fin ℓ → I => inducedWeight W H (pinRoots hℓ u v z))
  unfold unnormRootedDensity
  calc (∫ y : Fin ℓ → I, inducedWeight W (H.comap ⇑π) (pinRoots hℓ u v y))
      = ∫ y : Fin ℓ → I, inducedWeight W H (pinRoots hℓ u v (y ∘ ⇑π.symm)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ∫ y : Fin ℓ → I,
          inducedWeight W H (pinRoots hℓ u v ((MeasurableEquiv.piCongrLeft (fun _ => I) π) y)) := by
        simp only [hΦ]
    _ = ∫ z : Fin ℓ → I, inducedWeight W H (pinRoots hℓ u v z) := hcomp

/-! ### Private machinery: reconstructing a graph from its upper-triangle edge set

(Private copy of the `GraphonInducedDensity` combinatorial core; generic in the graph, the
graph host size, and the sample point — no pinning appears until the very end.) -/

private def graphOfPairs {m : ℕ} (S : Finset (Fin m × Fin m)) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun u v => u < v ∧ (u, v) ∈ S)

private lemma graphOfPairs_adj_of_lt {m : ℕ} {S : Finset (Fin m × Fin m)} {u v : Fin m}
    (huv : u < v) : (graphOfPairs S).Adj u v ↔ (u, v) ∈ S := by
  unfold graphOfPairs
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h.2
    · exact absurd h.1 (asymm huv)
  · exact fun h => ⟨ne_of_lt huv, Or.inl ⟨huv, h⟩⟩

private lemma graphOfPairs_filter_eq {m : ℕ} (H : SimpleGraph (Fin m)) :
    graphOfPairs (belowDiagPairs m |>.filter (fun p => H.Adj p.1 p.2)) = H := by
  ext u v
  rcases lt_trichotomy u v with huv | huv | huv
  · rw [graphOfPairs_adj_of_lt huv, Finset.mem_filter, mem_belowDiagPairs]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨huv, h⟩⟩
  · subst huv
    simp
  · rw [(graphOfPairs _).adj_comm u v, graphOfPairs_adj_of_lt huv,
      Finset.mem_filter, mem_belowDiagPairs]
    exact (and_iff_right huv).trans (H.adj_comm v u)

private lemma comap_graphOfPairs_eq {n m : ℕ} (f : Fin n → Fin m)
    (hf_lt : ∀ {a b : Fin n}, a < b → f a < f b) (G : SimpleGraph (Fin n))
    (E : Finset (Fin m × Fin m))
    (hE : ∀ p ∈ belowDiagPairs n, ((f p.1, f p.2) ∈ E ↔ G.Adj p.1 p.2)) :
    (graphOfPairs E).comap f = G := by
  ext k1 k2
  rw [SimpleGraph.comap_adj]
  rcases lt_trichotomy k1 k2 with hk | hk | hk
  · rw [graphOfPairs_adj_of_lt (hf_lt hk)]
    exact hE (k1, k2) (mem_belowDiagPairs.mpr hk)
  · subst hk; simp
  · calc (graphOfPairs E).Adj (f k1) (f k2)
        ↔ (graphOfPairs E).Adj (f k2) (f k1) := (graphOfPairs E).adj_comm _ _
      _ ↔ (f k2, f k1) ∈ E := graphOfPairs_adj_of_lt (hf_lt hk)
      _ ↔ G.Adj k2 k1 := hE (k2, k1) (mem_belowDiagPairs.mpr hk)
      _ ↔ G.Adj k1 k2 := G.adj_comm k2 k1

/-! ### Private machinery: the extension fibre (private copy of `GraphonInducedDensity`'s
extension-partition combinatorics). -/

private def extOldIdx {n ℓ : ℕ} (h : n ≤ ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (belowDiagPairs n).image (Prod.map (Fin.castLE h) (Fin.castLE h))

private def extNewIdx {n ℓ : ℕ} (h : n ≤ ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  belowDiagPairs ℓ \ extOldIdx h

private noncomputable def extGEdges {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n)) :
    Finset (Fin ℓ × Fin ℓ) :=
  ((belowDiagPairs n).filter (fun p => G.Adj p.1 p.2)).image (Prod.map (Fin.castLE h) (Fin.castLE h))

private noncomputable def extFiber {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n)) :
    Finset (SimpleGraph (Fin ℓ)) :=
  Finset.univ.filter (fun H : SimpleGraph (Fin ℓ) => H.comap (Fin.castLE h) = G)

private lemma extFiber_mem_iff {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin ℓ)) : H ∈ extFiber h G ↔ H.comap (Fin.castLE h) = G := by
  unfold extFiber; simp

private lemma extCastLE_injective {n ℓ : ℕ} (h : n ≤ ℓ) :
    Function.Injective
      (Prod.map (Fin.castLE h) (Fin.castLE h) : Fin n × Fin n → Fin ℓ × Fin ℓ) :=
  (Fin.castLE_injective h).prodMap (Fin.castLE_injective h)

private lemma extOldIdx_sub {n ℓ : ℕ} (h : n ≤ ℓ) : extOldIdx h ⊆ belowDiagPairs ℓ := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rw [mem_belowDiagPairs] at hp ⊢
  exact (Fin.castLE_lt_castLE_iff h).mpr hp

private lemma extGEdges_sub {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n)) :
    extGEdges h G ⊆ extOldIdx h := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

private lemma extOldIdx_union_newIdx {n ℓ : ℕ} (h : n ≤ ℓ) :
    extOldIdx h ∪ extNewIdx h = belowDiagPairs ℓ :=
  Finset.union_sdiff_of_subset (extOldIdx_sub h)

private lemma extOldIdx_disjoint_newIdx {n ℓ : ℕ} (h : n ≤ ℓ) :
    Disjoint (extOldIdx h) (extNewIdx h) := Finset.disjoint_sdiff

private lemma extInducedWeight_split {n ℓ : ℕ} (h : n ≤ ℓ) (W : Graphon)
    (H : SimpleGraph (Fin ℓ)) (x : Fin ℓ → I) :
    inducedWeight W H x
      = (∏ p ∈ extOldIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
        * ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
  unfold inducedWeight
  rw [← extOldIdx_union_newIdx h, Finset.prod_union (extOldIdx_disjoint_newIdx h)]

private lemma extOldPart_eq {n ℓ : ℕ} (h : n ≤ ℓ) (W : Graphon) (G : SimpleGraph (Fin n))
    {H : SimpleGraph (Fin ℓ)} (hH : H ∈ extFiber h G) (x : Fin ℓ → I) :
    (∏ p ∈ extOldIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
      = inducedWeight W G (x ∘ Fin.castLE h) := by
  have hHG : H.comap (Fin.castLE h) = G := (extFiber_mem_iff h G H).mp hH
  unfold extOldIdx inducedWeight
  rw [Finset.prod_image (fun a _ b _ heq => extCastLE_injective h heq)]
  apply Finset.prod_congr rfl
  intro p _
  have hadj : (H.comap (Fin.castLE h)).Adj p.1 p.2 ↔ H.Adj (Fin.castLE h p.1) (Fin.castLE h p.2) :=
    SimpleGraph.comap_adj
  rw [hHG] at hadj
  simp only [Prod.map_fst, Prod.map_snd, Function.comp_apply]
  exact adjWeight_congr W hadj.symm _ _

private lemma extGEdges_union_iff {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    {S : Finset (Fin ℓ × Fin ℓ)} (hS : S ⊆ extNewIdx h) {p : Fin n × Fin n}
    (hp : p ∈ belowDiagPairs n) :
    (Fin.castLE h p.1, Fin.castLE h p.2) ∈ extGEdges h G ∪ S ↔ G.Adj p.1 p.2 := by
  rw [Finset.mem_union]
  have hGE : (Fin.castLE h p.1, Fin.castLE h p.2) ∈ extGEdges h G ↔ G.Adj p.1 p.2 := by
    unfold extGEdges
    rw [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, heq⟩
      have hqeq : q = p := extCastLE_injective h heq
      rw [hqeq] at hq
      exact (Finset.mem_filter.mp hq).2
    · intro hGadj
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hGadj⟩, rfl⟩
  have hnotS : (Fin.castLE h p.1, Fin.castLE h p.2) ∉ S := by
    intro hmem
    have hIn : (Fin.castLE h p.1, Fin.castLE h p.2) ∈ extNewIdx h := hS hmem
    have hOld : (Fin.castLE h p.1, Fin.castLE h p.2) ∈ extOldIdx h :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    exact Finset.disjoint_left.mp (extOldIdx_disjoint_newIdx h) hOld hIn
  rw [hGE]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd h1 hnotS
  · exact fun h1 => Or.inl h1

private def extToGraph {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    (S : Finset (Fin ℓ × Fin ℓ)) : SimpleGraph (Fin ℓ) :=
  graphOfPairs (extGEdges h G ∪ S)

private noncomputable def extToNewSubset {n ℓ : ℕ} (h : n ≤ ℓ) (H : SimpleGraph (Fin ℓ)) :
    Finset (Fin ℓ × Fin ℓ) :=
  (extNewIdx h).filter (fun p => H.Adj p.1 p.2)

private lemma extToGraph_mem_fiber {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    {S : Finset (Fin ℓ × Fin ℓ)} (hS : S ∈ (extNewIdx h).powerset) :
    extToGraph h G S ∈ extFiber h G := by
  rw [extFiber_mem_iff]
  exact comap_graphOfPairs_eq (Fin.castLE h) (fun {a b} hab => (Fin.castLE_lt_castLE_iff h).mpr hab)
    G _ (fun p hp => extGEdges_union_iff h G (Finset.mem_powerset.mp hS) hp)

private lemma extGEdges_eq_oldIdx_filter {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    {H : SimpleGraph (Fin ℓ)} (hH : H ∈ extFiber h G) :
    extGEdges h G = (extOldIdx h).filter (fun p => H.Adj p.1 p.2) := by
  have hHG : H.comap (Fin.castLE h) = G := (extFiber_mem_iff h G H).mp hH
  ext q
  unfold extGEdges extOldIdx
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
    refine ⟨⟨p, hp1, rfl⟩, ?_⟩
    have hadj : (H.comap (Fin.castLE h)).Adj p.1 p.2 ↔ H.Adj (Fin.castLE h p.1) (Fin.castLE h p.2) :=
      SimpleGraph.comap_adj
    rw [hHG] at hadj
    simp only [Prod.map_fst, Prod.map_snd]
    exact hadj.mp hp2
  · rintro ⟨⟨p, hp, rfl⟩, hHadj⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    have hadj : (H.comap (Fin.castLE h)).Adj p.1 p.2 ↔ H.Adj (Fin.castLE h p.1) (Fin.castLE h p.2) :=
      SimpleGraph.comap_adj
    rw [hHG] at hadj
    simp only [Prod.map_fst, Prod.map_snd] at hHadj
    exact hadj.mpr hHadj

private lemma extLeft_inv {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    {H : SimpleGraph (Fin ℓ)} (hH : H ∈ extFiber h G) :
    extToGraph h G (extToNewSubset h H) = H := by
  unfold extToGraph
  have hEq : extGEdges h G ∪ extToNewSubset h H
      = (belowDiagPairs ℓ).filter (fun p => H.Adj p.1 p.2) := by
    unfold extToNewSubset
    rw [extGEdges_eq_oldIdx_filter h G hH, ← Finset.filter_union, extOldIdx_union_newIdx]
  rw [hEq, graphOfPairs_filter_eq]

private lemma extRight_inv {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    {S : Finset (Fin ℓ × Fin ℓ)} (hS : S ∈ (extNewIdx h).powerset) :
    extToNewSubset h (extToGraph h G S) = S := by
  have hSsub : S ⊆ extNewIdx h := Finset.mem_powerset.mp hS
  unfold extToNewSubset extToGraph
  apply Finset.ext
  intro p
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hpNew, hpAdj⟩
    have hpBelow : p ∈ belowDiagPairs ℓ := (Finset.mem_sdiff.mp hpNew).1
    have hlt : p.1 < p.2 := mem_belowDiagPairs.mp hpBelow
    rw [graphOfPairs_adj_of_lt hlt, Finset.mem_union] at hpAdj
    rcases hpAdj with hpAdj | hpAdj
    · exact absurd hpNew (fun hpNew' =>
        Finset.disjoint_left.mp (extOldIdx_disjoint_newIdx h) (extGEdges_sub h G hpAdj) hpNew')
    · exact hpAdj
  · intro hpS
    have hpNew := hSsub hpS
    refine ⟨hpNew, ?_⟩
    have hpBelow : p ∈ belowDiagPairs ℓ := (Finset.mem_sdiff.mp hpNew).1
    have hlt : p.1 < p.2 := mem_belowDiagPairs.mp hpBelow
    rw [graphOfPairs_adj_of_lt hlt, Finset.mem_union]
    exact Or.inr hpS

private lemma extFactor_eq {n ℓ : ℕ} (h : n ≤ ℓ) (W : Graphon) (x : Fin ℓ → I)
    (H : SimpleGraph (Fin ℓ)) :
    (∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
      = (∏ p ∈ extToNewSubset h H, W.W (x p.1) (x p.2))
        * ∏ p ∈ extNewIdx h \ extToNewSubset h H, (1 - W.W (x p.1) (x p.2)) := by
  unfold extToNewSubset
  have hsplit := Finset.prod_filter_mul_prod_filter_not (extNewIdx h) (fun p => H.Adj p.1 p.2)
    (fun p => adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
  rw [← hsplit]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hadj : H.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    unfold adjWeight
    rw [if_pos hadj]
  · rw [Finset.filter_not]
    apply Finset.prod_congr rfl
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hnadj : ¬ H.Adj p.1 p.2 := fun hAdj => hp'.2 (Finset.mem_filter.mpr ⟨hp'.1, hAdj⟩)
    unfold adjWeight
    rw [if_neg hnadj]

private lemma extFiber_sum_eq_one {n ℓ : ℕ} (h : n ≤ ℓ) (W : Graphon) (G : SimpleGraph (Fin n))
    (x : Fin ℓ → I) :
    ∑ H ∈ extFiber h G, ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) = 1 := by
  have hbij : ∑ H ∈ extFiber h G, ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2)
      = ∑ S ∈ (extNewIdx h).powerset,
          (∏ p ∈ S, W.W (x p.1) (x p.2)) * ∏ p ∈ extNewIdx h \ S, (1 - W.W (x p.1) (x p.2)) := by
    apply Finset.sum_nbij' (extToNewSubset h) (extToGraph h G)
    · exact fun H _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    · exact fun S hS => extToGraph_mem_fiber h G hS
    · exact fun H hH => extLeft_inv h G hH
    · exact fun S hS => extRight_inv h G hS
    · exact fun H _ => extFactor_eq h W x H
  rw [hbij, ← Finset.prod_add]
  simp

/-! ### Private machinery: the pinned marginalisation lemma (generalisation of
`GraphonInducedDensity`'s `extMarginal` to an arbitrary bounded measurable function). -/

private def extSubtypeEquiv {n ℓ : ℕ} (h : n ≤ ℓ) :
    Fin n ≃ {i : Fin ℓ // (i : ℕ) < n} where
  toFun k := ⟨Fin.castLE h k, k.2⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv k := by simp
  right_inv i := by
    apply Subtype.ext
    simp

/-- Marginalisation for an arbitrary bounded measurable function of the sample: the integral of
a function of the restriction to the first `n` coordinates is the integral of that function on
`Fin n → I`. -/
private lemma pinnedMarginal {n ℓ : ℕ} (h : n ≤ ℓ) (g : (Fin n → I) → ℝ) (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    ∫ x : Fin ℓ → I, g (x ∘ Fin.castLE h) = ∫ y : Fin n → I, g y := by
  classical
  set p : Fin ℓ → Prop := fun i => (i : ℕ) < n with hp_def
  set Ψ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin ℓ => I) p with hΨ_def
  set ι := extSubtypeEquiv h with hι_def
  have hcomp : ∀ x : Fin ℓ → I, (Ψ x).1 ∘ ι = x ∘ Fin.castLE h := by
    intro x
    funext k
    rfl
  have hmeas : Measurable (fun z : ({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I) =>
      z.1 ∘ ι) :=
    measurable_pi_iff.mpr (fun k => (measurable_pi_apply (ι k)).comp measurable_fst)
  set G' : ({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I) → ℝ :=
    fun z => g (z.1 ∘ ι) with hG'_def
  have hstep1 : ∫ x : Fin ℓ → I, g (x ∘ Fin.castLE h)
      = ∫ z : ({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I), G' z := by
    have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin ℓ => I) p
    rw [← hΨ_def] at hmp
    rw [← hmp.integral_comp' G']
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [hG'_def, hcomp x]
  have hstep2 : ∫ z : ({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I), G' z
      = ∫ z1 : {i : Fin ℓ // p i} → I, g (z1 ∘ ι) := by
    have hInt : Integrable G' volume := by
      apply integrable_of_bounds' (hg.comp hmeas)
      · exact fun z => hg0 _
      · exact fun z => hg1 _
    rw [show (volume : Measure (({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I)))
        = (volume : Measure ({i : Fin ℓ // p i} → I)).prod volume from rfl,
      integral_prod _ hInt]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z1
    simp [hG'_def]
  have hstep3 : ∫ z1 : {i : Fin ℓ // p i} → I, g (z1 ∘ ι)
      = ∫ y : Fin n → I, g y := by
    have hmp2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n => I) ι.symm
    have hΦeq : ∀ z1 : {i : Fin ℓ // p i} → I,
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => I) ι.symm) z1 = z1 ∘ ι := by
      intro z1
      funext k
      have hkey := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => I) ι.symm z1
          (ι k)
      simpa [Equiv.symm_apply_apply] using hkey
    rw [← hmp2.integral_comp' g]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z1
    simp only [hΦeq]
  rw [hstep1, hstep2, hstep3]

/-- `pinRoots` commutes with the extension embedding `Fin.castLE h` (private helper: pinning
at the small size `n` after restricting a large sample, versus restricting after pinning at the
compatible large size `ℓ`, agree — both send the two roots to `u, v` and everything else rides
along unchanged). -/
private lemma pinRoots_comp_castLE {n ℓ : ℕ} (hn : 2 ≤ n) (h : n ≤ ℓ) (u v : I)
    (x : Fin ℓ → I) :
    pinRoots (hn.trans h) u v x ∘ Fin.castLE h = pinRoots hn u v (x ∘ Fin.castLE h) := by
  funext k
  by_cases h0 : k = Fin.castLE hn 0
  · subst h0
    have hcast : Fin.castLE h (Fin.castLE hn (0 : Fin 2)) = Fin.castLE (hn.trans h) 0 := by
      simp [Fin.castLE_castLE]
    show pinRoots (hn.trans h) u v x (Fin.castLE h (Fin.castLE hn 0))
      = pinRoots hn u v (x ∘ Fin.castLE h) (Fin.castLE hn 0)
    rw [hcast, pinRoots_apply_root0, pinRoots_apply_root0]
  by_cases h1 : k = Fin.castLE hn 1
  · subst h1
    have hcast : Fin.castLE h (Fin.castLE hn (1 : Fin 2)) = Fin.castLE (hn.trans h) 1 := by
      simp [Fin.castLE_castLE]
    show pinRoots (hn.trans h) u v x (Fin.castLE h (Fin.castLE hn 1))
      = pinRoots hn u v (x ∘ Fin.castLE h) (Fin.castLE hn 1)
    rw [hcast, pinRoots_apply_root1, pinRoots_apply_root1]
  · have hne0 : Fin.castLE h k ≠ Fin.castLE (hn.trans h) 0 := by
      intro heq
      apply h0
      apply Fin.castLE_injective h
      rw [heq]
      simp [Fin.castLE_castLE]
    have hne1 : Fin.castLE h k ≠ Fin.castLE (hn.trans h) 1 := by
      intro heq
      apply h1
      apply Fin.castLE_injective h
      rw [heq]
      simp [Fin.castLE_castLE]
    show pinRoots (hn.trans h) u v x (Fin.castLE h k) = pinRoots hn u v (x ∘ Fin.castLE h) k
    rw [pinRoots_apply_of_ne (hn.trans h) u v x hne0 hne1,
      pinRoots_apply_of_ne hn u v (x ∘ Fin.castLE h) h0 h1]
    rfl

/-- **Extension partition** for the rooted density: extending along `Fin.castLE` (which is
root-fixing) partitions the density exactly as in the unrooted
`graphonFlagDensity_extension_sum`; the pinned coordinates ride along since
`pinRoots hℓ u v x ∘ Fin.castLE h = pinRoots hn u v (x ∘ Fin.castLE h)`. -/
theorem unnormRootedDensity_extension_sum (W : Graphon) {n ℓ : ℕ} (hn : 2 ≤ n) (h : n ≤ ℓ)
    (G : SimpleGraph (Fin n)) (u v : I) :
    unnormRootedDensity W hn G u v
      = ∑ H ∈ Finset.univ.filter
          (fun H : SimpleGraph (Fin ℓ) => H.comap (Fin.castLE h) = G),
          unnormRootedDensity W (hn.trans h) H u v := by
  show unnormRootedDensity W hn G u v = ∑ H ∈ extFiber h G, unnormRootedDensity W (hn.trans h) H u v
  have hgmeas : Measurable (fun y : Fin n → I => inducedWeight W G (pinRoots hn u v y)) :=
    measurable_pinnedInducedWeight W hn G u v
  have hmarg := pinnedMarginal h (fun y : Fin n → I => inducedWeight W G (pinRoots hn u v y))
    hgmeas (fun y => inducedWeight_nonneg W G _) (fun y => inducedWeight_le_one W G _)
  have hpointwise : ∀ x : Fin ℓ → I,
      inducedWeight W G (pinRoots hn u v (x ∘ Fin.castLE h))
        = ∑ H ∈ extFiber h G, inducedWeight W H (pinRoots (hn.trans h) u v x) := by
    intro x
    rw [← pinRoots_comp_castLE hn h u v x]
    calc inducedWeight W G (pinRoots (hn.trans h) u v x ∘ Fin.castLE h)
        = inducedWeight W G (pinRoots (hn.trans h) u v x ∘ Fin.castLE h) * 1 := by ring
      _ = inducedWeight W G (pinRoots (hn.trans h) u v x ∘ Fin.castLE h)
            * (∑ H ∈ extFiber h G,
                ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2)
                  ((pinRoots (hn.trans h) u v x) p.1) ((pinRoots (hn.trans h) u v x) p.2)) := by
          rw [extFiber_sum_eq_one h W G (pinRoots (hn.trans h) u v x)]
      _ = ∑ H ∈ extFiber h G, inducedWeight W G (pinRoots (hn.trans h) u v x ∘ Fin.castLE h)
            * ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2)
                ((pinRoots (hn.trans h) u v x) p.1) ((pinRoots (hn.trans h) u v x) p.2) := by
          rw [Finset.mul_sum]
      _ = ∑ H ∈ extFiber h G,
            (∏ p ∈ extOldIdx h, adjWeight W (H.Adj p.1 p.2)
                ((pinRoots (hn.trans h) u v x) p.1) ((pinRoots (hn.trans h) u v x) p.2))
              * ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2)
                  ((pinRoots (hn.trans h) u v x) p.1) ((pinRoots (hn.trans h) u v x) p.2) := by
          apply Finset.sum_congr rfl
          intro H hH
          rw [extOldPart_eq h W G hH (pinRoots (hn.trans h) u v x)]
      _ = ∑ H ∈ extFiber h G, inducedWeight W H (pinRoots (hn.trans h) u v x) := by
          apply Finset.sum_congr rfl
          intro H _
          rw [extInducedWeight_split h W H (pinRoots (hn.trans h) u v x)]
  calc unnormRootedDensity W hn G u v
      = ∫ y : Fin n → I, inducedWeight W G (pinRoots hn u v y) := rfl
    _ = ∫ x : Fin ℓ → I, inducedWeight W G (pinRoots hn u v (x ∘ Fin.castLE h)) := hmarg.symm
    _ = ∫ x : Fin ℓ → I, ∑ H ∈ extFiber h G,
          inducedWeight W H (pinRoots (hn.trans h) u v x) :=
        integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ∑ H ∈ extFiber h G, ∫ x : Fin ℓ → I, inducedWeight W H (pinRoots (hn.trans h) u v x) :=
        integral_finset_sum _ (fun H _ => integrable_pinnedInducedWeight W (hn.trans h) H u v)
    _ = ∑ H ∈ extFiber h G, unnormRootedDensity W (hn.trans h) H u v := rfl

/-- **Total mass**: the unnormalised rooted densities of all `RootCompatible` graphs on
`Fin n` sum to the root factor (extension partition from the two-vertex case via
`rootCompatible_iff_comap_eq` + `unnormRootedDensity_two`). -/
theorem sum_unnormRootedDensity (W : Graphon) (σ' : FlagType (Fin 2)) {n : ℕ} (hn : 2 ≤ n)
    (u v : I) :
    ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => RootCompatible σ' hn H),
      unnormRootedDensity W hn H u v = rootWeight W σ' u v := by
  have hext := unnormRootedDensity_extension_sum W (le_refl 2) hn σ' u v
  rw [unnormRootedDensity_two] at hext
  have hfilter : (Finset.univ.filter (fun H : SimpleGraph (Fin n) => RootCompatible σ' hn H))
      = Finset.univ.filter (fun H : SimpleGraph (Fin n) => H.comap (Fin.castLE hn) = σ') := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact rootCompatible_iff_comap_eq σ' hn H
  rw [hfilter]
  exact hext.symm

/-! ## The glue embeddings and the block product -/

/-- `n₁ ≤ n₁ + n₂ − 2` when both sizes are at least two. -/
theorem glue_le₁ {n₁ n₂ : ℕ} (_hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) : n₁ ≤ n₁ + n₂ - 2 := by omega

/-- `2 ≤ n₁ + n₂ − 2` when both sizes are at least two. -/
theorem glue_le₂ {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) : 2 ≤ n₁ + n₂ - 2 := by omega

/-- The second glue embedding: roots to roots, non-root vertex `k` (`2 ≤ k`) to
`n₁ + k − 2` (the second non-root block of the glued host). -/
noncomputable def glueEmb₂ (n₁ : ℕ) {n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    Fin n₂ ↪ Fin (n₁ + n₂ - 2) where
  toFun k :=
    if hk : (k : ℕ) < 2 then ⟨k, by omega⟩ else ⟨n₁ + k - 2, by omega⟩
  inj' := by
    intro a b hab
    simp only at hab
    split_ifs at hab with ha hb hb <;> apply Fin.ext <;>
      (have := Fin.val_eq_of_eq hab; simp only [] at this ⊢) <;> omega

/-- The second glue embedding is root-fixing. -/
theorem rootFixing_glueEmb₂ {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    RootFixing hn₂ (glue_le₂ hn₁ hn₂) (glueEmb₂ n₁ hn₁ hn₂) := by
  intro a
  have hk : ((Fin.castLE hn₂ a : Fin n₂) : ℕ) < 2 := a.isLt
  apply Fin.ext
  show (if hk' : ((Fin.castLE hn₂ a : Fin n₂) : ℕ) < 2
      then (⟨(Fin.castLE hn₂ a : Fin n₂), by omega⟩ : Fin (n₁ + n₂ - 2))
      else ⟨n₁ + (Fin.castLE hn₂ a : Fin n₂) - 2, by omega⟩).val
    = (Fin.castLE (glue_le₂ hn₁ hn₂) a).val
  rw [dif_pos hk]
  rfl

/-- The two glue images overlap exactly in the roots. -/
theorem glue_range_inter {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    Set.range ⇑(⟨Fin.castLE (glue_le₁ hn₁ hn₂),
        Fin.castLE_injective (glue_le₁ hn₁ hn₂)⟩ : Fin n₁ ↪ Fin (n₁ + n₂ - 2))
      ∩ Set.range ⇑(glueEmb₂ n₁ hn₁ hn₂)
      = ({Fin.castLE (glue_le₂ hn₁ hn₂) 0, Fin.castLE (glue_le₂ hn₁ hn₂) 1}
          : Set (Fin (n₁ + n₂ - 2))) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_range, Function.Embedding.coeFn_mk,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨k, hk⟩⟩
    have hxa : (x : ℕ) = (a : ℕ) := by rw [← ha]; rfl
    have hxa' : (x : ℕ) < n₁ := hxa ▸ a.isLt
    have hxk : (x : ℕ) = (if hk' : ((k : Fin n₂) : ℕ) < 2 then ((k : ℕ) : ℕ) else n₁ + (k : ℕ) - 2) := by
      rw [← hk]
      show (if hk' : ((k : Fin n₂) : ℕ) < 2 then (⟨(k : ℕ), by omega⟩ : Fin (n₁ + n₂ - 2))
          else (⟨n₁ + (k : ℕ) - 2, by omega⟩ : Fin (n₁ + n₂ - 2))).val
        = if hk' : ((k : Fin n₂) : ℕ) < 2 then (k : ℕ) else n₁ + (k : ℕ) - 2
      split_ifs with hk' <;> rfl
    by_cases hk2 : (k : ℕ) < 2
    · rw [dif_pos hk2] at hxk
      have hxval : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by omega
      rcases hxval with hv | hv
      · left; exact Fin.ext (by simpa using hv)
      · right; exact Fin.ext (by simpa using hv)
    · exfalso
      rw [dif_neg hk2] at hxk
      omega
  · rintro (rfl | rfl)
    · refine ⟨⟨⟨0, by omega⟩, ?_⟩, ⟨⟨0, by omega⟩, ?_⟩⟩
      · apply Fin.ext; simp
      · apply Fin.ext
        have hk0 : (((⟨0, by omega⟩ : Fin n₂) : Fin n₂) : ℕ) < 2 := by norm_num
        show (if hk' : (((⟨0, by omega⟩ : Fin n₂) : Fin n₂) : ℕ) < 2
            then (⟨((⟨0, by omega⟩ : Fin n₂) : ℕ), by omega⟩ : Fin (n₁ + n₂ - 2))
            else ⟨n₁ + ((⟨0, by omega⟩ : Fin n₂) : ℕ) - 2, by omega⟩).val
          = (Fin.castLE (glue_le₂ hn₁ hn₂) (0 : Fin 2)).val
        rw [dif_pos hk0]
        simp
    · refine ⟨⟨⟨1, by omega⟩, ?_⟩, ⟨⟨1, by omega⟩, ?_⟩⟩
      · apply Fin.ext; simp
      · apply Fin.ext
        have hk1 : (((⟨1, by omega⟩ : Fin n₂) : Fin n₂) : ℕ) < 2 := by norm_num
        show (if hk' : (((⟨1, by omega⟩ : Fin n₂) : Fin n₂) : ℕ) < 2
            then (⟨((⟨1, by omega⟩ : Fin n₂) : ℕ), by omega⟩ : Fin (n₁ + n₂ - 2))
            else ⟨n₁ + ((⟨1, by omega⟩ : Fin n₂) : ℕ) - 2, by omega⟩).val
          = (Fin.castLE (glue_le₂ hn₁ hn₂) (1 : Fin 2)).val
        rw [dif_pos hk1]
        simp

/-! ### Private machinery for the glued block product -/

/-- `pinRoots` commutes with precomposition by *any* root-fixing embedding (not just
`Fin.castLE`): the general form of `pinRoots_comp_castLE`. -/
private lemma pinRoots_comp_rootfix_emb {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (e : Fin p ↪ Fin q)
    (he : RootFixing hp hq e) (u v : I) (x : Fin q → I) :
    pinRoots hq u v x ∘ ⇑e = pinRoots hp u v (x ∘ ⇑e) := by
  funext k
  by_cases h0 : k = Fin.castLE hp 0
  · subst h0
    show pinRoots hq u v x (e (Fin.castLE hp 0)) = pinRoots hp u v (x ∘ ⇑e) (Fin.castLE hp 0)
    rw [he 0, pinRoots_apply_root0, pinRoots_apply_root0]
  by_cases h1 : k = Fin.castLE hp 1
  · subst h1
    show pinRoots hq u v x (e (Fin.castLE hp 1)) = pinRoots hp u v (x ∘ ⇑e) (Fin.castLE hp 1)
    rw [he 1, pinRoots_apply_root1, pinRoots_apply_root1]
  · have hne0 : e k ≠ Fin.castLE hq 0 := fun heq => h0 (e.injective (heq.trans (he 0).symm))
    have hne1 : e k ≠ Fin.castLE hq 1 := fun heq => h1 (e.injective (heq.trans (he 1).symm))
    show pinRoots hq u v x (e k) = pinRoots hp u v (x ∘ ⇑e) k
    rw [pinRoots_apply_of_ne hq u v x hne0 hne1, pinRoots_apply_of_ne hp u v (x ∘ ⇑e) h0 h1]
    rfl

/-- **Root-factor extraction**: the unnormalised rooted density of *any* graph `K` factors as
the `(0,1)`-pair's own adjacency weight (a constant in the pinned pair, not integrated) times
the integral of the remaining pairs.  Purely pointwise combinatorics — no `RootCompatible`
hypothesis needed; the value of the extracted factor is identified with `rootWeight` at the
call sites via `RootCompatible`. -/
private lemma unnormRootedDensity_root_factor {k : ℕ} (hk : 2 ≤ k) (K : SimpleGraph (Fin k))
    (u v : I) :
    unnormRootedDensity W hk K u v
      = adjWeight W (K.Adj (Fin.castLE hk 0) (Fin.castLE hk 1)) u v
        * ∫ y : Fin k → I, ∏ p ∈ (belowDiagPairs k).erase
              ((Fin.castLE hk 0 : Fin k), (Fin.castLE hk 1 : Fin k)),
            adjWeight W (K.Adj p.1 p.2) (pinRoots hk u v y p.1) (pinRoots hk u v y p.2) := by
  have hmemroot : ((Fin.castLE hk 0 : Fin k), (Fin.castLE hk 1 : Fin k)) ∈ belowDiagPairs k := by
    rw [mem_belowDiagPairs]
    exact (Fin.castLE_lt_castLE_iff hk).mpr (by decide)
  have hpointwise : ∀ y : Fin k → I,
      inducedWeight W K (pinRoots hk u v y)
        = adjWeight W (K.Adj (Fin.castLE hk 0) (Fin.castLE hk 1)) u v
          * ∏ p ∈ (belowDiagPairs k).erase ((Fin.castLE hk 0 : Fin k), (Fin.castLE hk 1 : Fin k)),
              adjWeight W (K.Adj p.1 p.2) (pinRoots hk u v y p.1) (pinRoots hk u v y p.2) := by
    intro y
    unfold inducedWeight
    rw [show (∏ p ∈ belowDiagPairs k, adjWeight W (K.Adj p.1 p.2)
          (pinRoots hk u v y p.1) (pinRoots hk u v y p.2))
        = adjWeight W (K.Adj (Fin.castLE hk 0) (Fin.castLE hk 1))
            (pinRoots hk u v y (Fin.castLE hk 0)) (pinRoots hk u v y (Fin.castLE hk 1))
          * ∏ p ∈ (belowDiagPairs k).erase ((Fin.castLE hk 0 : Fin k), (Fin.castLE hk 1 : Fin k)),
              adjWeight W (K.Adj p.1 p.2) (pinRoots hk u v y p.1) (pinRoots hk u v y p.2)
        from (Finset.mul_prod_erase (belowDiagPairs k) _ hmemroot).symm]
    rw [pinRoots_apply_root0, pinRoots_apply_root1]
  unfold unnormRootedDensity
  calc ∫ y : Fin k → I, inducedWeight W K (pinRoots hk u v y)
      = ∫ y : Fin k → I, adjWeight W (K.Adj (Fin.castLE hk 0) (Fin.castLE hk 1)) u v
          * ∏ p ∈ (belowDiagPairs k).erase ((Fin.castLE hk 0 : Fin k), (Fin.castLE hk 1 : Fin k)),
              adjWeight W (K.Adj p.1 p.2) (pinRoots hk u v y p.1) (pinRoots hk u v y p.2) :=
        integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = adjWeight W (K.Adj (Fin.castLE hk 0) (Fin.castLE hk 1)) u v
          * ∫ y : Fin k → I, ∏ p ∈ (belowDiagPairs k).erase
                ((Fin.castLE hk 0 : Fin k), (Fin.castLE hk 1 : Fin k)),
              adjWeight W (K.Adj p.1 p.2) (pinRoots hk u v y p.1) (pinRoots hk u v y p.2) :=
        integral_const_mul _ _

/-- `glueEmb₂` is strictly monotone. -/
private lemma glueEmb₂_strictMono {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    StrictMono (glueEmb₂ n₁ hn₁ hn₂) := by
  intro a b hab
  unfold glueEmb₂
  simp only [Function.Embedding.coeFn_mk]
  have hab' : (a : ℕ) < (b : ℕ) := hab
  split_ifs with ha hb hb <;> simp only [Fin.mk_lt_mk] <;> omega

/-- The two glue embeddings cover the whole glued host. -/
private lemma glue_range_union {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    Set.range ⇑(⟨Fin.castLE (glue_le₁ hn₁ hn₂), Fin.castLE_injective (glue_le₁ hn₁ hn₂)⟩
        : Fin n₁ ↪ Fin (n₁ + n₂ - 2))
      ∪ Set.range ⇑(glueEmb₂ n₁ hn₁ hn₂) = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_range, Function.Embedding.coeFn_mk, Set.mem_univ, iff_true]
  by_cases hx : (x : ℕ) < n₁
  · exact Or.inl ⟨⟨(x : ℕ), hx⟩, Fin.ext rfl⟩
  · push_neg at hx
    have hklt : (x : ℕ) - n₁ + 2 < n₂ := by omega
    refine Or.inr ⟨⟨(x : ℕ) - n₁ + 2, hklt⟩, ?_⟩
    apply Fin.ext
    have hknot2 : ¬ (((⟨(x : ℕ) - n₁ + 2, hklt⟩ : Fin n₂) : ℕ) < 2) := by
      show ¬ ((x : ℕ) - n₁ + 2 < 2)
      omega
    show (if hk : (((⟨(x : ℕ) - n₁ + 2, hklt⟩ : Fin n₂) : ℕ)) < 2
        then (((⟨(x : ℕ) - n₁ + 2, hklt⟩ : Fin n₂) : ℕ))
        else n₁ + (((⟨(x : ℕ) - n₁ + 2, hklt⟩ : Fin n₂) : ℕ)) - 2) = (x : ℕ)
    rw [dif_neg hknot2]
    show n₁ + ((x : ℕ) - n₁ + 2) - 2 = (x : ℕ)
    omega

/-- If an increasing pair of `Fin n₁` and an increasing pair of `Fin n₂` glue to the *same*
pair of the glued host, both pairs must be the respective root pairs (the glue images overlap
exactly in the roots, `glue_range_inter`, and the two root-fixing embeddings are injective and
order-preserving). -/
private lemma glue_pair_eq_root {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    {a : Fin n₁ × Fin n₁} {b : Fin n₂ × Fin n₂}
    (ha : a ∈ belowDiagPairs n₁) (hb : b ∈ belowDiagPairs n₂)
    (heq : (Fin.castLE (glue_le₁ hn₁ hn₂) a.1, Fin.castLE (glue_le₁ hn₁ hn₂) a.2)
        = (glueEmb₂ n₁ hn₁ hn₂ b.1, glueEmb₂ n₁ hn₁ hn₂ b.2)) :
    a = (Fin.castLE hn₁ 0, Fin.castLE hn₁ 1) ∧ b = (Fin.castLE hn₂ 0, Fin.castLE hn₂ 1) := by
  have ha' : (a.1 : Fin n₁) < a.2 := mem_belowDiagPairs.mp ha
  have hb' : (b.1 : Fin n₂) < b.2 := mem_belowDiagPairs.mp hb
  have heq1 : Fin.castLE (glue_le₁ hn₁ hn₂) a.1 = glueEmb₂ n₁ hn₁ hn₂ b.1 := congrArg Prod.fst heq
  have heq2 : Fin.castLE (glue_le₁ hn₁ hn₂) a.2 = glueEmb₂ n₁ hn₁ hn₂ b.2 := congrArg Prod.snd heq
  have hmem1 : Fin.castLE (glue_le₁ hn₁ hn₂) a.1
      ∈ ({Fin.castLE (glue_le₂ hn₁ hn₂) 0, Fin.castLE (glue_le₂ hn₁ hn₂) 1}
          : Set (Fin (n₁ + n₂ - 2))) := by
    rw [← glue_range_inter hn₁ hn₂]
    exact ⟨⟨a.1, rfl⟩, ⟨b.1, heq1.symm⟩⟩
  have hmem2 : Fin.castLE (glue_le₁ hn₁ hn₂) a.2
      ∈ ({Fin.castLE (glue_le₂ hn₁ hn₂) 0, Fin.castLE (glue_le₂ hn₁ hn₂) 1}
          : Set (Fin (n₁ + n₂ - 2))) := by
    rw [← glue_range_inter hn₁ hn₂]
    exact ⟨⟨a.2, rfl⟩, ⟨b.2, heq2.symm⟩⟩
  have hcastcast : ∀ c : Fin 2,
      Fin.castLE (glue_le₂ hn₁ hn₂) c = Fin.castLE (glue_le₁ hn₁ hn₂) (Fin.castLE hn₁ c) := by
    intro c
    apply Fin.ext
    simp [Fin.castLE_castLE]
  have ha1 : a.1 = Fin.castLE hn₁ 0 ∨ a.1 = Fin.castLE hn₁ 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem1
    rcases hmem1 with h | h
    · left
      apply Fin.castLE_injective (glue_le₁ hn₁ hn₂)
      rw [h, hcastcast]
    · right
      apply Fin.castLE_injective (glue_le₁ hn₁ hn₂)
      rw [h, hcastcast]
  have ha2 : a.2 = Fin.castLE hn₁ 0 ∨ a.2 = Fin.castLE hn₁ 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
    rcases hmem2 with h | h
    · left
      apply Fin.castLE_injective (glue_le₁ hn₁ hn₂)
      rw [h, hcastcast]
    · right
      apply Fin.castLE_injective (glue_le₁ hn₁ hn₂)
      rw [h, hcastcast]
  have haeq : a.1 = Fin.castLE hn₁ 0 ∧ a.2 = Fin.castLE hn₁ 1 := by
    rcases ha1 with h1 | h1 <;> rcases ha2 with h2 | h2
    · exfalso; rw [h1, h2] at ha'; exact lt_irrefl _ ha'
    · exact ⟨h1, h2⟩
    · exfalso
      rw [h1, h2] at ha'
      rw [Fin.castLE_lt_castLE_iff] at ha'
      exact absurd ha' (by decide)
    · exfalso; rw [h1, h2] at ha'; exact lt_irrefl _ ha'
  refine ⟨Prod.ext haeq.1 haeq.2, ?_⟩
  have hb1 : Fin.castLE (glue_le₁ hn₁ hn₂) (Fin.castLE hn₁ (0 : Fin 2)) = glueEmb₂ n₁ hn₁ hn₂ b.1 := by
    rw [← haeq.1]; exact heq1
  have hb2 : Fin.castLE (glue_le₁ hn₁ hn₂) (Fin.castLE hn₁ (1 : Fin 2)) = glueEmb₂ n₁ hn₁ hn₂ b.2 := by
    rw [← haeq.2]; exact heq2
  have hrootfix : RootFixing hn₂ (glue_le₂ hn₁ hn₂) (glueEmb₂ n₁ hn₁ hn₂) :=
    rootFixing_glueEmb₂ hn₁ hn₂
  have hb1eq : b.1 = Fin.castLE hn₂ 0 := by
    apply (glueEmb₂ n₁ hn₁ hn₂).injective
    rw [hrootfix 0, hcastcast]
    exact hb1.symm
  have hb2eq : b.2 = Fin.castLE hn₂ 1 := by
    apply (glueEmb₂ n₁ hn₁ hn₂).injective
    rw [hrootfix 1, hcastcast]
    exact hb2.symm
  exact Prod.ext hb1eq hb2eq

/-- **Two-block marginalisation** (abstract version of `GraphonInducedDensity`'s private
`blkMarginal`, for arbitrary bounded measurable functions instead of `inducedWeight`): the
integral of a product of a function of the first `p` coordinates and a function of the last
`q` coordinates splits as the product of the two integrals. -/
private lemma blkMarginalAbstract {p q : ℕ} (Φ : (Fin p → I) → ℝ) (Ψ : (Fin q → I) → ℝ)
    (_hΦ : Measurable Φ) (_hΦ0 : ∀ y, 0 ≤ Φ y) (_hΦ1 : ∀ y, Φ y ≤ 1)
    (_hΨ : Measurable Ψ) (_hΨ0 : ∀ y, 0 ≤ Ψ y) (_hΨ1 : ∀ y, Ψ y ≤ 1) :
    ∫ x : Fin (p + q) → I, Φ (x ∘ Fin.castAdd q) * Ψ (x ∘ Fin.natAdd p)
      = (∫ y : Fin p → I, Φ y) * (∫ y : Fin q → I, Ψ y) := by
  classical
  set e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm with he_def
  set Θ := (MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => I) e).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => I)) with hΘ_def
  have hmp1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => I) e)
      volume volume := volume_measurePreserving_piCongrLeft (fun _ => I) e
  have hmp2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => I))
      volume volume := volume_measurePreserving_sumPiEquivProdPi (fun _ => I)
  have hmpΘ : MeasurePreserving Θ volume volume := by
    rw [hΘ_def]; exact hmp1.trans hmp2
  have hΘeq : ∀ x : Fin (p + q) → I, Θ x = (x ∘ Fin.castAdd q, x ∘ Fin.natAdd p) := by
    intro x
    have hstep : ∀ w : Fin p ⊕ Fin q,
        (MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => I) e) x w = x (finSumFinEquiv w) := by
      intro w
      have hkey := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin p ⊕ Fin q => I) e x
          (finSumFinEquiv w)
      simpa [he_def, Equiv.symm_apply_apply] using hkey
    have hΘx : Θ x = (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => I))
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => I) e) x) := by
      rw [hΘ_def]; rfl
    rw [hΘx]
    apply Prod.ext
    · funext i
      show (MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => I) e) x (Sum.inl i)
          = (x ∘ Fin.castAdd q) i
      rw [hstep (Sum.inl i), finSumFinEquiv_apply_left]
      rfl
    · funext j
      show (MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => I) e) x (Sum.inr j)
          = (x ∘ Fin.natAdd p) j
      rw [hstep (Sum.inr j), finSumFinEquiv_apply_right]
      rfl
  rw [← integral_prod_mul Φ Ψ, ← Measure.volume_eq_prod,
    ← hmpΘ.integral_comp' (fun z : (Fin p → I) × (Fin q → I) => Φ z.1 * Ψ z.2)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [hΘeq]

/-- **Dropping the two pinned root coordinates**: since pinning always overrides positions
`0, 1` regardless of the sample, the pinned integral over `Fin k → I` equals the integral of
the same (extended) integrand over just the `k − 2` non-root coordinates.  Proof route:
change of variables along `finCongr (2 + (k − 2) = k)`, then `blkMarginalAbstract` with a
constant `1` first factor (the two root coordinates integrate away for free, being a
probability space). -/
private lemma pinnedIntegral_drop_roots {k : ℕ} (hk : 2 ≤ k) (D : (Fin k → I) → ℝ)
    (hD : Measurable D) (hD0 : ∀ y, 0 ≤ D y) (hD1 : ∀ y, D y ≤ 1) (u v : I) :
    ∫ y : Fin k → I, D (pinRoots hk u v y)
      = ∫ z : Fin (k - 2) → I, D (pinRoots hk u v
          (fun i : Fin k => if hi : (i : ℕ) < 2 then u else z ⟨(i : ℕ) - 2, by omega⟩)) := by
  have hk2 : 2 + (k - 2) = k := by omega
  set e : Fin (2 + (k - 2)) ≃ Fin k := finCongr hk2 with he_def
  set extend : (Fin (k - 2) → I) → (Fin k → I) :=
    fun z i => if hi : (i : ℕ) < 2 then u else z ⟨(i : ℕ) - 2, by omega⟩ with hextend_def
  set Ψ2 : (Fin (k - 2) → I) → ℝ := fun z => D (pinRoots hk u v (extend z)) with hΨ2_def
  have hextend_meas : Measurable extend := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : (i : ℕ) < 2
    · simp only [hextend_def, hi, dif_pos]
      exact measurable_const
    · have heq : (fun z : Fin (k - 2) → I => extend z i) = fun z => z ⟨(i : ℕ) - 2, by omega⟩ := by
        funext z; simp [hextend_def, hi]
      rw [heq]; exact measurable_pi_apply _
  have hΨ2meas : Measurable Ψ2 :=
    hD.comp ((measurable_pinRoots hk u v).comp hextend_meas)
  have hΨ2_0 : ∀ z, 0 ≤ Ψ2 z := fun z => hD0 _
  have hΨ2_1 : ∀ z, Ψ2 z ≤ 1 := fun z => hD1 _
  have hΦ0meas : Measurable (fun _ : Fin 2 → I => (1 : ℝ)) := measurable_const
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin k => I) e
  have hΦeq : ∀ x : Fin (2 + (k - 2)) → I,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin k => I) e) x = x ∘ e.symm := by
    intro x
    funext j
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin k => I) e x (e.symm j)
    simpa [Equiv.apply_symm_apply] using h
  have hstep1 : ∫ y : Fin k → I, D (pinRoots hk u v y)
      = ∫ x : Fin (2 + (k - 2)) → I, D (pinRoots hk u v (x ∘ ⇑e.symm)) := by
    rw [← hmp.integral_comp' (fun y : Fin k → I => D (pinRoots hk u v y))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [hΦeq]
  have hpointwise : ∀ x : Fin (2 + (k - 2)) → I,
      D (pinRoots hk u v (x ∘ ⇑e.symm))
        = (1 : ℝ) * Ψ2 (x ∘ Fin.natAdd 2) := by
    intro x
    rw [one_mul]
    have hfun : pinRoots hk u v (x ∘ ⇑e.symm) = pinRoots hk u v (extend (x ∘ Fin.natAdd 2)) := by
      funext i
      by_cases h0 : i = Fin.castLE hk 0
      · subst h0; rw [pinRoots_apply_root0, pinRoots_apply_root0]
      by_cases h1 : i = Fin.castLE hk 1
      · subst h1; rw [pinRoots_apply_root1, pinRoots_apply_root1]
      · rw [pinRoots_apply_of_ne hk u v _ h0 h1, pinRoots_apply_of_ne hk u v _ h0 h1]
        have h0' : (i : ℕ) ≠ 0 := fun he => h0 (Fin.ext (by simpa using he))
        have h1' : (i : ℕ) ≠ 1 := fun he => h1 (Fin.ext (by simpa using he))
        have hnot2 : ¬ ((i : ℕ) < 2) := by omega
        have hival : 2 ≤ (i : ℕ) := by omega
        show x (e.symm i) = extend (x ∘ Fin.natAdd 2) i
        rw [hextend_def]
        simp only [hnot2, dif_neg, not_false_iff]
        have hesymm : e.symm i = Fin.natAdd 2 ⟨(i : ℕ) - 2, by omega⟩ := by
          apply e.injective
          rw [Equiv.apply_symm_apply]
          apply Fin.ext
          show (i : ℕ) = ((finCongr hk2) (Fin.natAdd 2 ⟨(i : ℕ) - 2, by omega⟩) : ℕ)
          simp only [finCongr_apply_coe]
          show (i : ℕ) = 2 + ((i : ℕ) - 2)
          omega
        rw [hesymm]
        rfl
    rw [hfun]
  calc ∫ y : Fin k → I, D (pinRoots hk u v y)
      = ∫ x : Fin (2 + (k - 2)) → I, D (pinRoots hk u v (x ∘ ⇑e.symm)) := hstep1
    _ = ∫ x : Fin (2 + (k - 2)) → I,
          (1 : ℝ) * Ψ2 (x ∘ Fin.natAdd 2) := integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ∫ x : Fin (2 + (k - 2)) → I,
          (fun _ : Fin 2 → I => (1 : ℝ)) (x ∘ Fin.castAdd (k - 2)) * Ψ2 (x ∘ Fin.natAdd 2) := rfl
    _ = (∫ _ : Fin 2 → I, (1 : ℝ)) * ∫ z : Fin (k - 2) → I, Ψ2 z :=
        blkMarginalAbstract (fun _ : Fin 2 → I => (1 : ℝ)) Ψ2 hΦ0meas
          (fun _ => zero_le_one) (fun _ => le_refl 1) hΨ2meas hΨ2_0 hΨ2_1
    _ = ∫ z : Fin (k - 2) → I, Ψ2 z := by simp

/-- **The glued marginalisation**: the integral over the glued host of the product of the two
pinned block integrands splits as the product of the two individual pinned integrals.  The
two blocks' coordinates are genuinely disjoint (`n₁ + n₂ − 2 = n₁ + (n₂ − 2)`); the pinned
roots ride along as constants on both sides via `pinnedIntegral_drop_roots`. -/
private lemma glue_marginal_split {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (D1 : (Fin n₁ → I) → ℝ) (D2 : (Fin n₂ → I) → ℝ)
    (hD1meas : Measurable D1) (hD10 : ∀ y, 0 ≤ D1 y) (hD11 : ∀ y, D1 y ≤ 1)
    (hD2meas : Measurable D2) (hD20 : ∀ y, 0 ≤ D2 y) (hD21 : ∀ y, D2 y ≤ 1) (u v : I) :
    ∫ x : Fin (n₁ + n₂ - 2) → I,
        D1 (pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
          * D2 (pinRoots hn₂ u v (x ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂)))
      = (∫ y1 : Fin n₁ → I, D1 (pinRoots hn₁ u v y1))
          * (∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2)) := by
  set extend2 : (Fin (n₂ - 2) → I) → (Fin n₂ → I) :=
    fun z i => if hi : (i : ℕ) < 2 then u else z ⟨(i : ℕ) - 2, by omega⟩ with hextend2_def
  set Ψ2 : (Fin (n₂ - 2) → I) → ℝ := fun z => D2 (pinRoots hn₂ u v (extend2 z)) with hΨ2_def
  have hA2 : (∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2)) = ∫ z : Fin (n₂ - 2) → I, Ψ2 z :=
    pinnedIntegral_drop_roots hn₂ D2 hD2meas hD20 hD21 u v
  have hextend2_meas : Measurable extend2 := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : (i : ℕ) < 2
    · simp only [hextend2_def, hi, dif_pos]
      exact measurable_const
    · have heq : (fun z : Fin (n₂ - 2) → I => extend2 z i) = fun z => z ⟨(i : ℕ) - 2, by omega⟩ := by
        funext z; simp [hextend2_def, hi]
      rw [heq]; exact measurable_pi_apply _
  have hΨ2meas : Measurable Ψ2 := hD2meas.comp ((measurable_pinRoots hn₂ u v).comp hextend2_meas)
  have hΨ2_0 : ∀ z, 0 ≤ Ψ2 z := fun z => hD20 _
  have hΨ2_1 : ∀ z, Ψ2 z ≤ 1 := fun z => hD21 _
  have hnatm : n₁ + (n₂ - 2) = n₁ + n₂ - 2 := by omega
  set em : Fin (n₁ + (n₂ - 2)) ≃ Fin (n₁ + n₂ - 2) := finCongr hnatm with hem_def
  set D1' : (Fin n₁ → I) → ℝ := fun y1 => D1 (pinRoots hn₁ u v y1) with hD1'_def
  have hD1'meas : Measurable D1' := hD1meas.comp (measurable_pinRoots hn₁ u v)
  have hD1'0 : ∀ y, 0 ≤ D1' y := fun y => hD10 _
  have hD1'1 : ∀ y, D1' y ≤ 1 := fun y => hD11 _
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin (n₁ + n₂ - 2) => I) em
  have hΦeq : ∀ x' : Fin (n₁ + (n₂ - 2)) → I,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (n₁ + n₂ - 2) => I) em) x' = x' ∘ em.symm := by
    intro x'
    funext j
    have h := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Fin (n₁ + n₂ - 2) => I) em x' (em.symm j)
    simpa [Equiv.apply_symm_apply] using h
  have hstep1 : ∫ x : Fin (n₁ + n₂ - 2) → I,
        D1 (pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
          * D2 (pinRoots hn₂ u v (x ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂)))
      = ∫ x' : Fin (n₁ + (n₂ - 2)) → I,
          D1 (pinRoots hn₁ u v ((x' ∘ ⇑em.symm) ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
            * D2 (pinRoots hn₂ u v ((x' ∘ ⇑em.symm) ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂))) := by
    rw [← hmp.integral_comp' (fun x : Fin (n₁ + n₂ - 2) → I =>
      D1 (pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
        * D2 (pinRoots hn₂ u v (x ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂))))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x'
    simp only [hΦeq]
  have hcastAdd_eq : ∀ (x' : Fin (n₁ + (n₂ - 2)) → I) (a : Fin n₁),
      (x' ∘ ⇑em.symm) (Fin.castLE (glue_le₁ hn₁ hn₂) a) = (x' ∘ Fin.castAdd (n₂ - 2)) a := by
    intro x' a
    have hval : em.symm (Fin.castLE (glue_le₁ hn₁ hn₂) a) = Fin.castAdd (n₂ - 2) a := by
      apply em.injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      show ((Fin.castLE (glue_le₁ hn₁ hn₂) a : Fin (n₁ + n₂ - 2)) : ℕ)
          = ((em (Fin.castAdd (n₂ - 2) a) : Fin (n₁ + n₂ - 2)) : ℕ)
      rw [hem_def]
      simp
    show x' (em.symm (Fin.castLE (glue_le₁ hn₁ hn₂) a)) = x' (Fin.castAdd (n₂ - 2) a)
    rw [hval]
  have hpointwise2 : ∀ (x' : Fin (n₁ + (n₂ - 2)) → I) (k : Fin n₂),
      (x' ∘ ⇑em.symm) (glueEmb₂ n₁ hn₁ hn₂ k)
        = extend2 (x' ∘ Fin.natAdd n₁) k ∨ (k : ℕ) < 2 := by
    intro x' k
    by_cases hk : (k : ℕ) < 2
    · exact Or.inr hk
    · left
      have hknot : ¬ (((k : Fin n₂) : ℕ) < 2) := hk
      show x' (em.symm (glueEmb₂ n₁ hn₁ hn₂ k)) = extend2 (x' ∘ Fin.natAdd n₁) k
      rw [hextend2_def]
      simp only [hknot, dif_neg, not_false_iff]
      have hesymm : em.symm (glueEmb₂ n₁ hn₁ hn₂ k) = Fin.natAdd n₁ ⟨(k : ℕ) - 2, by omega⟩ := by
        apply em.injective
        rw [Equiv.apply_symm_apply]
        apply Fin.ext
        have hgval : glueEmb₂ n₁ hn₁ hn₂ k
            = (⟨n₁ + (k : ℕ) - 2, by omega⟩ : Fin (n₁ + n₂ - 2)) := by
          show (if hk' : ((k : Fin n₂) : ℕ) < 2 then (⟨(k : ℕ), by omega⟩ : Fin (n₁ + n₂ - 2))
              else (⟨n₁ + (k : ℕ) - 2, by omega⟩ : Fin (n₁ + n₂ - 2))) = ⟨n₁ + (k : ℕ) - 2, by omega⟩
          rw [dif_neg hknot]
        show ((glueEmb₂ n₁ hn₁ hn₂ k : Fin (n₁ + n₂ - 2)) : ℕ)
            = ((em (Fin.natAdd n₁ ⟨(k : ℕ) - 2, by omega⟩) : Fin (n₁ + n₂ - 2)) : ℕ)
        rw [hgval, hem_def]
        simp only [finCongr_apply_coe, Fin.val_natAdd]
        omega
      rw [hesymm]
      rfl
  have hpointwise : ∀ x' : Fin (n₁ + (n₂ - 2)) → I,
      D1 (pinRoots hn₁ u v ((x' ∘ ⇑em.symm) ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
          * D2 (pinRoots hn₂ u v ((x' ∘ ⇑em.symm) ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂)))
        = D1' (x' ∘ Fin.castAdd (n₂ - 2)) * Ψ2 (x' ∘ Fin.natAdd n₁) := by
    intro x'
    have heq1 : (x' ∘ ⇑em.symm) ∘ Fin.castLE (glue_le₁ hn₁ hn₂) = x' ∘ Fin.castAdd (n₂ - 2) := by
      funext a; exact hcastAdd_eq x' a
    have heq2 : pinRoots hn₂ u v ((x' ∘ ⇑em.symm) ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂))
        = pinRoots hn₂ u v (extend2 (x' ∘ Fin.natAdd n₁)) := by
      funext k
      by_cases h0 : k = Fin.castLE hn₂ 0
      · subst h0; rw [pinRoots_apply_root0, pinRoots_apply_root0]
      by_cases h1 : k = Fin.castLE hn₂ 1
      · subst h1; rw [pinRoots_apply_root1, pinRoots_apply_root1]
      · rw [pinRoots_apply_of_ne hn₂ u v _ h0 h1, pinRoots_apply_of_ne hn₂ u v _ h0 h1]
        rcases hpointwise2 x' k with h | h
        · exact h
        · exfalso
          have h0' : (k : ℕ) ≠ 0 := fun he => h0 (Fin.ext (by simpa using he))
          have h1' : (k : ℕ) ≠ 1 := fun he => h1 (Fin.ext (by simpa using he))
          omega
    rw [heq1, heq2]
  calc ∫ x : Fin (n₁ + n₂ - 2) → I,
      D1 (pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
        * D2 (pinRoots hn₂ u v (x ∘ ⇑(glueEmb₂ n₁ hn₁ hn₂)))
      = ∫ x' : Fin (n₁ + (n₂ - 2)) → I,
          D1' (x' ∘ Fin.castAdd (n₂ - 2)) * Ψ2 (x' ∘ Fin.natAdd n₁) := by
        rw [hstep1]; exact integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = (∫ y1 : Fin n₁ → I, D1' y1) * ∫ z : Fin (n₂ - 2) → I, Ψ2 z :=
        blkMarginalAbstract D1' Ψ2 hD1'meas hD1'0 hD1'1 hΨ2meas hΨ2_0 hΨ2_1
    _ = (∫ y1 : Fin n₁ → I, D1 (pinRoots hn₁ u v y1))
          * (∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2)) := by rw [hA2]

set_option maxHeartbeats 2000000 in
/-- **The glued block product**: two rooted densities at the same type multiply to the root
factor times the total rooted density of the glued fibre.  The roots are shared between the
two blocks, so exactly one `rootWeight` factor survives on the right: the LHS carries
`rootWeight²` inside the two densities, while each glued summand carries only one.

Proof route: pointwise, split the pairs of the glued host into block-1 pairs (image of
`Fin.castLE`), block-2 pairs (image of `glueEmb₂`), and cross pairs (one non-root vertex in
each block); over the fibre the cross parts sum to `1` (partition of unity), the root pair
belongs to both blocks but is counted once (it is the shared `rootWeight`); the integral of
the two non-root block marginals splits since the pinned roots are constants and the two
blocks integrate disjoint coordinates, following the `sumPiEquivProdPi` change-of-variables
used for the unrooted block product `graphonFlagDensity_block_mul`. -/
theorem unnormRootedDensity_block_mul (W : Graphon) (σ' : FlagType (Fin 2)) {n₁ n₂ : ℕ}
    (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    (hG₁ : RootCompatible σ' hn₁ G₁) (hG₂ : RootCompatible σ' hn₂ G₂) (u v : I) :
    unnormRootedDensity W hn₁ G₁ u v * unnormRootedDensity W hn₂ G₂ u v
      = rootWeight W σ' u v
        * ∑ H ∈ Finset.univ.filter
            (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) =>
              H.comap (Fin.castLE (glue_le₁ hn₁ hn₂)) = G₁
              ∧ H.comap ⇑(glueEmb₂ n₁ hn₁ hn₂) = G₂),
            unnormRootedDensity W (glue_le₂ hn₁ hn₂) H u v := by
  classical
  set Glue1 : Fin n₁ ↪ Fin (n₁ + n₂ - 2) :=
      ⟨Fin.castLE (glue_le₁ hn₁ hn₂), Fin.castLE_injective (glue_le₁ hn₁ hn₂)⟩ with hGlue1_def
  set Glue2 : Fin n₂ ↪ Fin (n₁ + n₂ - 2) := glueEmb₂ n₁ hn₁ hn₂ with hGlue2_def
  set root1 : Fin n₁ × Fin n₁ := (Fin.castLE hn₁ 0, Fin.castLE hn₁ 1) with hroot1_def
  set root2 : Fin n₂ × Fin n₂ := (Fin.castLE hn₂ 0, Fin.castLE hn₂ 1) with hroot2_def
  set rootm : Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2) :=
      (Fin.castLE (glue_le₂ hn₁ hn₂) 0, Fin.castLE (glue_le₂ hn₁ hn₂) 1) with hrootm_def
  have hroot1mem : root1 ∈ belowDiagPairs n₁ := by
    rw [mem_belowDiagPairs, hroot1_def]
    exact (Fin.castLE_lt_castLE_iff hn₁).mpr (by decide)
  have hroot2mem : root2 ∈ belowDiagPairs n₂ := by
    rw [mem_belowDiagPairs, hroot2_def]
    exact (Fin.castLE_lt_castLE_iff hn₂).mpr (by decide)
  have hg1r0 : Glue1 (Fin.castLE hn₁ 0) = Fin.castLE (glue_le₂ hn₁ hn₂) 0 := by
    apply Fin.ext
    show ((Fin.castLE (glue_le₁ hn₁ hn₂) (Fin.castLE hn₁ 0) : Fin (n₁ + n₂ - 2)) : ℕ)
        = ((Fin.castLE (glue_le₂ hn₁ hn₂) (0 : Fin 2) : Fin (n₁ + n₂ - 2)) : ℕ)
    simp [Fin.castLE_castLE]
  have hg1r1 : Glue1 (Fin.castLE hn₁ 1) = Fin.castLE (glue_le₂ hn₁ hn₂) 1 := by
    apply Fin.ext
    show ((Fin.castLE (glue_le₁ hn₁ hn₂) (Fin.castLE hn₁ 1) : Fin (n₁ + n₂ - 2)) : ℕ)
        = ((Fin.castLE (glue_le₂ hn₁ hn₂) (1 : Fin 2) : Fin (n₁ + n₂ - 2)) : ℕ)
    simp [Fin.castLE_castLE]
  have hg2r0 : Glue2 (Fin.castLE hn₂ 0) = Fin.castLE (glue_le₂ hn₁ hn₂) 0 :=
    rootFixing_glueEmb₂ hn₁ hn₂ 0
  have hg2r1 : Glue2 (Fin.castLE hn₂ 1) = Fin.castLE (glue_le₂ hn₁ hn₂) 1 :=
    rootFixing_glueEmb₂ hn₁ hn₂ 1
  have hGlue1_at_root1 : Prod.map ⇑Glue1 ⇑Glue1 root1 = rootm := by
    rw [hroot1_def, hrootm_def]; simp [hg1r0, hg1r1]
  have hGlue2_at_root2 : Prod.map ⇑Glue2 ⇑Glue2 root2 = rootm := by
    rw [hroot2_def, hrootm_def]; simp [hg2r0, hg2r1]
  have hGlue1_root_fst : Glue1 root1.1 = rootm.1 := congrArg Prod.fst hGlue1_at_root1
  have hGlue1_root_snd : Glue1 root1.2 = rootm.2 := congrArg Prod.snd hGlue1_at_root1
  have hGlue2_root_fst : Glue2 root2.1 = rootm.1 := congrArg Prod.fst hGlue2_at_root2
  have hGlue2_root_snd : Glue2 root2.2 = rootm.2 := congrArg Prod.snd hGlue2_at_root2
  set E1 : Finset (Fin n₁ × Fin n₁) := (belowDiagPairs n₁).erase root1 with hE1_def
  set E2 : Finset (Fin n₂ × Fin n₂) := (belowDiagPairs n₂).erase root2 with hE2_def
  set Em : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      (belowDiagPairs (n₁ + n₂ - 2)).erase rootm with hEm_def
  set gOld1 : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      E1.image (Prod.map ⇑Glue1 ⇑Glue1) with hgOld1_def
  set gOld2 : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      E2.image (Prod.map ⇑Glue2 ⇑Glue2) with hgOld2_def
  set gCross : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      Em \ (gOld1 ∪ gOld2) with hgCross_def
  have hGlue1_inj : Function.Injective (Prod.map ⇑Glue1 ⇑Glue1) :=
    Glue1.injective.prodMap Glue1.injective
  have hGlue2_inj : Function.Injective (Prod.map ⇑Glue2 ⇑Glue2) :=
    Glue2.injective.prodMap Glue2.injective
  have hgOld1_sub_Em : gOld1 ⊆ Em := by
    intro q hq
    rw [hgOld1_def] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hp' : p ∈ belowDiagPairs n₁ := Finset.mem_of_mem_erase hp
    have hpne : p ≠ root1 := Finset.ne_of_mem_erase hp
    rw [hEm_def, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro heq
      exact hpne (hGlue1_inj (heq.trans hGlue1_at_root1.symm))
    · rw [mem_belowDiagPairs] at hp' ⊢
      exact (Fin.castLE_lt_castLE_iff (glue_le₁ hn₁ hn₂)).mpr hp'
  have hgOld2_sub_Em : gOld2 ⊆ Em := by
    intro q hq
    rw [hgOld2_def] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hp' : p ∈ belowDiagPairs n₂ := Finset.mem_of_mem_erase hp
    have hpne : p ≠ root2 := Finset.ne_of_mem_erase hp
    rw [hEm_def, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro heq
      exact hpne (hGlue2_inj (heq.trans hGlue2_at_root2.symm))
    · rw [mem_belowDiagPairs] at hp' ⊢
      exact glueEmb₂_strictMono hn₁ hn₂ hp'
  have hgOld12_disjoint : Disjoint gOld1 gOld2 := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rw [hgOld1_def] at hq1
    rw [hgOld2_def] at hq2
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq1
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hq2
    have ha' : a ∈ belowDiagPairs n₁ := Finset.mem_of_mem_erase ha
    have hb' : b ∈ belowDiagPairs n₂ := Finset.mem_of_mem_erase hb
    have hane : a ≠ root1 := Finset.ne_of_mem_erase ha
    obtain ⟨haeq, _⟩ := glue_pair_eq_root hn₁ hn₂ ha' hb' hab.symm
    exact hane haeq
  have hgOld_union_sub_Em : gOld1 ∪ gOld2 ⊆ Em := Finset.union_subset hgOld1_sub_Em hgOld2_sub_Em
  have hEm_eq : gOld1 ∪ gOld2 ∪ gCross = Em := by
    rw [hgCross_def]; exact Finset.union_sdiff_of_subset hgOld_union_sub_Em
  have hgOldUnion_disjoint_cross : Disjoint (gOld1 ∪ gOld2) gCross := by
    rw [hgCross_def]; exact Finset.disjoint_sdiff
  have hrootm_notin_Em : rootm ∉ Em := by
    rw [hEm_def, Finset.mem_erase]; rintro ⟨hne, -⟩; exact hne rfl
  have hgCross_sub_Em : gCross ⊆ Em := by rw [hgCross_def]; exact Finset.sdiff_subset
  have hrootm_notin_gCross : rootm ∉ gCross := fun h => hrootm_notin_Em (hgCross_sub_Em h)
  have hnotin_gCross_of_mem_gOld1 : ∀ q, q ∈ gOld1 → q ∉ gCross := by
    intro q hq hqc
    rw [hgCross_def, Finset.mem_sdiff] at hqc
    exact hqc.2 (Finset.mem_union_left _ hq)
  have hnotin_gCross_of_mem_gOld2 : ∀ q, q ∈ gOld2 → q ∉ gCross := by
    intro q hq hqc
    rw [hgCross_def, Finset.mem_sdiff] at hqc
    exact hqc.2 (Finset.mem_union_right _ hq)
  -- The two "old edge" sets: the images of `G₁`'s / `G₂`'s own (full) adjacency.
  set oldG1Edges : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      ((belowDiagPairs n₁).filter (fun p => G₁.Adj p.1 p.2)).image (Prod.map ⇑Glue1 ⇑Glue1)
      with holdG1E_def
  set oldG2Edges : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      ((belowDiagPairs n₂).filter (fun p => G₂.Adj p.1 p.2)).image (Prod.map ⇑Glue2 ⇑Glue2)
      with holdG2E_def
  have hmemOld1_iff : ∀ p ∈ belowDiagPairs n₁,
      (Prod.map ⇑Glue1 ⇑Glue1 p ∈ oldG1Edges ↔ G₁.Adj p.1 p.2) := by
    intro p hp
    rw [holdG1E_def, Finset.mem_image]
    constructor
    · rintro ⟨q, hq, heq⟩
      have hqeq : q = p := hGlue1_inj heq
      rw [hqeq] at hq
      exact (Finset.mem_filter.mp hq).2
    · intro hadj
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hadj⟩, rfl⟩
  have hmemOld2_iff : ∀ p ∈ belowDiagPairs n₂,
      (Prod.map ⇑Glue2 ⇑Glue2 p ∈ oldG2Edges ↔ G₂.Adj p.1 p.2) := by
    intro p hp
    rw [holdG2E_def, Finset.mem_image]
    constructor
    · rintro ⟨q, hq, heq⟩
      have hqeq : q = p := hGlue2_inj heq
      rw [hqeq] at hq
      exact (Finset.mem_filter.mp hq).2
    · intro hadj
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hadj⟩, rfl⟩
  have hconsistent : G₁.Adj (Fin.castLE hn₁ 0) (Fin.castLE hn₁ 1)
      ↔ G₂.Adj (Fin.castLE hn₂ 0) (Fin.castLE hn₂ 1) := by
    rw [← hG₁ 0 1, ← hG₂ 0 1]
  have hmemOld2_implies : ∀ p : Fin n₁ × Fin n₁, p ∈ belowDiagPairs n₁ →
      Prod.map ⇑Glue1 ⇑Glue1 p ∈ oldG2Edges → p = root1 ∧ G₁.Adj p.1 p.2 := by
    intro p hp hmem
    rw [holdG2E_def, Finset.mem_image] at hmem
    obtain ⟨b, hb, hab⟩ := hmem
    have hb2 : b ∈ belowDiagPairs n₂ := (Finset.mem_filter.mp hb).1
    have hbAdj : G₂.Adj b.1 b.2 := (Finset.mem_filter.mp hb).2
    obtain ⟨hpeq, hbeq⟩ := glue_pair_eq_root hn₁ hn₂ hp hb2 hab.symm
    have hpeq' : p = root1 := by rw [hroot1_def]; exact hpeq
    refine ⟨hpeq', ?_⟩
    rw [hpeq]
    show G₁.Adj (Fin.castLE hn₁ 0) (Fin.castLE hn₁ 1)
    rw [hconsistent]
    rw [hbeq] at hbAdj
    exact hbAdj
  have hmemOld1_implies : ∀ p : Fin n₂ × Fin n₂, p ∈ belowDiagPairs n₂ →
      Prod.map ⇑Glue2 ⇑Glue2 p ∈ oldG1Edges → p = root2 ∧ G₂.Adj p.1 p.2 := by
    intro p hp hmem
    rw [holdG1E_def, Finset.mem_image] at hmem
    obtain ⟨a, ha, hab⟩ := hmem
    have ha2 : a ∈ belowDiagPairs n₁ := (Finset.mem_filter.mp ha).1
    have haAdj : G₁.Adj a.1 a.2 := (Finset.mem_filter.mp ha).2
    obtain ⟨haeq, hpeq⟩ := glue_pair_eq_root hn₁ hn₂ ha2 hp hab
    have hpeq' : p = root2 := by rw [hroot2_def]; exact hpeq
    refine ⟨hpeq', ?_⟩
    rw [hpeq]
    show G₂.Adj (Fin.castLE hn₂ 0) (Fin.castLE hn₂ 1)
    rw [← hconsistent]
    rw [haeq] at haAdj
    exact haAdj
  have hmemOld2_notroot : ∀ p ∈ belowDiagPairs n₁, p ≠ root1 →
      Prod.map ⇑Glue1 ⇑Glue1 p ∉ oldG2Edges := fun p hp hpne hmem =>
    hpne (hmemOld2_implies p hp hmem).1
  have hmemOld1_notroot : ∀ p ∈ belowDiagPairs n₂, p ≠ root2 →
      Prod.map ⇑Glue2 ⇑Glue2 p ∉ oldG1Edges := fun p hp hpne hmem =>
    hpne (hmemOld1_implies p hp hmem).1
  have hUnionMem1 : ∀ (S : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2))), S ⊆ gCross →
      ∀ p ∈ belowDiagPairs n₁,
        (Prod.map ⇑Glue1 ⇑Glue1 p ∈ oldG1Edges ∪ oldG2Edges ∪ S ↔ G₁.Adj p.1 p.2) := by
    intro S hS p hp
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hproot : p = root1
    · subst hproot
      have hSnot : Prod.map ⇑Glue1 ⇑Glue1 root1 ∉ S := by
        rw [hGlue1_at_root1]
        exact fun h => hrootm_notin_gCross (hS h)
      have h1 : Prod.map ⇑Glue1 ⇑Glue1 root1 ∈ oldG1Edges ↔ G₁.Adj root1.1 root1.2 :=
        hmemOld1_iff root1 hroot1mem
      have h2 : Prod.map ⇑Glue1 ⇑Glue1 root1 ∈ oldG2Edges ↔ G₁.Adj root1.1 root1.2 := by
        rw [hGlue1_at_root1, ← hGlue2_at_root2, hmemOld2_iff root2 hroot2mem]
        show G₂.Adj (Fin.castLE hn₂ 0) (Fin.castLE hn₂ 1) ↔ G₁.Adj (Fin.castLE hn₁ 0) (Fin.castLE hn₁ 1)
        exact hconsistent.symm
      rw [h1, h2]
      constructor
      · rintro ((h | h) | h)
        · exact h
        · exact h
        · exact absurd h hSnot
      · intro h; exact Or.inl (Or.inl h)
    · have h1 : Prod.map ⇑Glue1 ⇑Glue1 p ∈ oldG1Edges ↔ G₁.Adj p.1 p.2 := hmemOld1_iff p hp
      have h2 : Prod.map ⇑Glue1 ⇑Glue1 p ∉ oldG2Edges := hmemOld2_notroot p hp hproot
      have h3 : Prod.map ⇑Glue1 ⇑Glue1 p ∉ S := by
        have hmemgOld1 : Prod.map ⇑Glue1 ⇑Glue1 p ∈ gOld1 := by
          rw [hgOld1_def]
          exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hproot, hp⟩, rfl⟩
        exact fun h => hnotin_gCross_of_mem_gOld1 _ hmemgOld1 (hS h)
      rw [h1]
      constructor
      · rintro ((h | h) | h)
        · exact h
        · exact absurd h h2
        · exact absurd h h3
      · intro h; exact Or.inl (Or.inl h)
  have hUnionMem2 : ∀ (S : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2))), S ⊆ gCross →
      ∀ p ∈ belowDiagPairs n₂,
        (Prod.map ⇑Glue2 ⇑Glue2 p ∈ oldG1Edges ∪ oldG2Edges ∪ S ↔ G₂.Adj p.1 p.2) := by
    intro S hS p hp
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hproot : p = root2
    · subst hproot
      have hSnot : Prod.map ⇑Glue2 ⇑Glue2 root2 ∉ S := by
        rw [hGlue2_at_root2]
        exact fun h => hrootm_notin_gCross (hS h)
      have h2 : Prod.map ⇑Glue2 ⇑Glue2 root2 ∈ oldG2Edges ↔ G₂.Adj root2.1 root2.2 :=
        hmemOld2_iff root2 hroot2mem
      have h1 : Prod.map ⇑Glue2 ⇑Glue2 root2 ∈ oldG1Edges ↔ G₂.Adj root2.1 root2.2 := by
        rw [hGlue2_at_root2, ← hGlue1_at_root1, hmemOld1_iff root1 hroot1mem]
        show G₁.Adj (Fin.castLE hn₁ 0) (Fin.castLE hn₁ 1) ↔ G₂.Adj (Fin.castLE hn₂ 0) (Fin.castLE hn₂ 1)
        exact hconsistent
      rw [h1, h2]
      constructor
      · rintro ((h | h) | h)
        · exact h
        · exact h
        · exact absurd h hSnot
      · intro h; exact Or.inl (Or.inr h)
    · have h2 : Prod.map ⇑Glue2 ⇑Glue2 p ∈ oldG2Edges ↔ G₂.Adj p.1 p.2 := hmemOld2_iff p hp
      have h1 : Prod.map ⇑Glue2 ⇑Glue2 p ∉ oldG1Edges := hmemOld1_notroot p hp hproot
      have h3 : Prod.map ⇑Glue2 ⇑Glue2 p ∉ S := by
        have hmemgOld2 : Prod.map ⇑Glue2 ⇑Glue2 p ∈ gOld2 := by
          rw [hgOld2_def]
          exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hproot, hp⟩, rfl⟩
        exact fun h => hnotin_gCross_of_mem_gOld2 _ hmemgOld2 (hS h)
      rw [h2]
      constructor
      · rintro ((h | h) | h)
        · exact absurd h h1
        · exact h
        · exact absurd h h3
      · intro h; exact Or.inl (Or.inr h)
  -- The "erased-root-pair" own densities of `G₁`, `G₂`.
  set D1 : (Fin n₁ → I) → ℝ :=
      fun y1 => ∏ p ∈ E1, adjWeight W (G₁.Adj p.1 p.2) (y1 p.1) (y1 p.2) with hD1_def
  set D2 : (Fin n₂ → I) → ℝ :=
      fun y2 => ∏ p ∈ E2, adjWeight W (G₂.Adj p.1 p.2) (y2 p.1) (y2 p.2) with hD2_def
  have hD1meas : Measurable D1 := by
    rw [hD1_def]
    apply Finset.measurable_prod
    intro p _
    have hpair : Measurable fun x : Fin n₁ → I => W.W (x p.1) (x p.2) :=
      show Measurable (Function.uncurry W.W ∘ fun x : Fin n₁ → I => (x p.1, x p.2)) from
        W.measurable.comp ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))
    unfold adjWeight
    split_ifs
    · exact hpair
    · exact measurable_const.sub hpair
  have hD10 : ∀ y, 0 ≤ D1 y := fun y => Finset.prod_nonneg fun _ _ => adjWeight_nonneg W _ _ _
  have hD11 : ∀ y, D1 y ≤ 1 := fun y =>
    Finset.prod_le_one (fun _ _ => adjWeight_nonneg W _ _ _) (fun _ _ => adjWeight_le_one W _ _ _)
  have hD2meas : Measurable D2 := by
    rw [hD2_def]
    apply Finset.measurable_prod
    intro p _
    have hpair : Measurable fun x : Fin n₂ → I => W.W (x p.1) (x p.2) :=
      show Measurable (Function.uncurry W.W ∘ fun x : Fin n₂ → I => (x p.1, x p.2)) from
        W.measurable.comp ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))
    unfold adjWeight
    split_ifs
    · exact hpair
    · exact measurable_const.sub hpair
  have hD20 : ∀ y, 0 ≤ D2 y := fun y => Finset.prod_nonneg fun _ _ => adjWeight_nonneg W _ _ _
  have hD21 : ∀ y, D2 y ≤ 1 := fun y =>
    Finset.prod_le_one (fun _ _ => adjWeight_nonneg W _ _ _) (fun _ _ => adjWeight_le_one W _ _ _)
  have hHG1adj : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)), H.comap ⇑Glue1 = G₁ → ∀ p ∈ belowDiagPairs n₁,
      (H.Adj (Glue1 p.1) (Glue1 p.2) ↔ G₁.Adj p.1 p.2) := by
    intro H hHG1 p _
    have h := SimpleGraph.comap_adj (G := H) (f := ⇑Glue1) (u := p.1) (v := p.2)
    rw [hHG1] at h
    exact h.symm
  have hHG2adj : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)), H.comap ⇑Glue2 = G₂ → ∀ p ∈ belowDiagPairs n₂,
      (H.Adj (Glue2 p.1) (Glue2 p.2) ↔ G₂.Adj p.1 p.2) := by
    intro H hHG2 p _
    have h := SimpleGraph.comap_adj (G := H) (f := ⇑Glue2) (u := p.1) (v := p.2)
    rw [hHG2] at h
    exact h.symm
  have holdPart1_eq : ∀ (H : SimpleGraph (Fin (n₁ + n₂ - 2))), H.comap ⇑Glue1 = G₁ →
      ∀ z : Fin (n₁ + n₂ - 2) → I,
        (∏ q ∈ gOld1, adjWeight W (H.Adj q.1 q.2) (z q.1) (z q.2)) = D1 (z ∘ ⇑Glue1) := by
    intro H hHG1 z
    rw [hD1_def, hgOld1_def]
    rw [Finset.prod_image (fun a _ b _ heq => hGlue1_inj heq)]
    apply Finset.prod_congr rfl
    intro p hp
    have hp' : p ∈ belowDiagPairs n₁ := Finset.mem_of_mem_erase hp
    have hadj := hHG1adj H hHG1 p hp'
    simp only [Prod.map_fst, Prod.map_snd, Function.comp_apply]
    exact adjWeight_congr W hadj _ _
  have holdPart2_eq : ∀ (H : SimpleGraph (Fin (n₁ + n₂ - 2))), H.comap ⇑Glue2 = G₂ →
      ∀ z : Fin (n₁ + n₂ - 2) → I,
        (∏ q ∈ gOld2, adjWeight W (H.Adj q.1 q.2) (z q.1) (z q.2)) = D2 (z ∘ ⇑Glue2) := by
    intro H hHG2 z
    rw [hD2_def, hgOld2_def]
    rw [Finset.prod_image (fun a _ b _ heq => hGlue2_inj heq)]
    apply Finset.prod_congr rfl
    intro p hp
    have hp' : p ∈ belowDiagPairs n₂ := Finset.mem_of_mem_erase hp
    have hadj := hHG2adj H hHG2 p hp'
    simp only [Prod.map_fst, Prod.map_snd, Function.comp_apply]
    exact adjWeight_congr W hadj _ _
  -- The reconstruction bijection: `fiber ≃ gCross.powerset`.
  set toGraph : Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) → SimpleGraph (Fin (n₁ + n₂ - 2)) :=
      fun S => graphOfPairs (oldG1Edges ∪ oldG2Edges ∪ S) with htoGraph_def
  set toCross : SimpleGraph (Fin (n₁ + n₂ - 2)) → Finset (Fin (n₁ + n₂ - 2) × Fin (n₁ + n₂ - 2)) :=
      fun H => gCross.filter (fun p => H.Adj p.1 p.2) with htoCross_def
  have htoGraph_mem_fiber : ∀ S ∈ gCross.powerset,
      toGraph S ∈ Finset.univ.filter
        (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂) := by
    intro S hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact comap_graphOfPairs_eq (⇑Glue1)
        (fun {a b} hab => (Fin.castLE_lt_castLE_iff (glue_le₁ hn₁ hn₂)).mpr hab) G₁ _
        (fun p hp => hUnionMem1 S (Finset.mem_powerset.mp hS) p hp)
    · exact comap_graphOfPairs_eq (⇑Glue2) (fun {a b} hab => glueEmb₂_strictMono hn₁ hn₂ hab) G₂ _
        (fun p hp => hUnionMem2 S (Finset.mem_powerset.mp hS) p hp)
  have holdG1E_sub : oldG1Edges ⊆ belowDiagPairs (n₁ + n₂ - 2) := by
    intro q hq
    rw [holdG1E_def, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hp' : p ∈ belowDiagPairs n₁ := (Finset.mem_filter.mp hp).1
    rw [mem_belowDiagPairs] at hp' ⊢
    exact (Fin.castLE_lt_castLE_iff (glue_le₁ hn₁ hn₂)).mpr hp'
  have holdG2E_sub : oldG2Edges ⊆ belowDiagPairs (n₁ + n₂ - 2) := by
    intro q hq
    rw [holdG2E_def, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hp' : p ∈ belowDiagPairs n₂ := (Finset.mem_filter.mp hp).1
    rw [mem_belowDiagPairs] at hp' ⊢
    exact glueEmb₂_strictMono hn₁ hn₂ hp'
  have holdUnion_disjoint_cross : Disjoint (oldG1Edges ∪ oldG2Edges) gCross := by
    rw [Finset.disjoint_left]
    intro q hq hqc
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rw [holdG1E_def, Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      have hp' : p ∈ belowDiagPairs n₁ := (Finset.mem_filter.mp hp).1
      by_cases hproot : p = root1
      · subst hproot
        rw [hGlue1_at_root1] at hqc
        exact hrootm_notin_gCross hqc
      · have hmemgOld1 : Prod.map ⇑Glue1 ⇑Glue1 p ∈ gOld1 := by
          rw [hgOld1_def]; exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hproot, hp'⟩, rfl⟩
        exact hnotin_gCross_of_mem_gOld1 _ hmemgOld1 hqc
    · rw [holdG2E_def, Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      have hp' : p ∈ belowDiagPairs n₂ := (Finset.mem_filter.mp hp).1
      by_cases hproot : p = root2
      · subst hproot
        rw [hGlue2_at_root2] at hqc
        exact hrootm_notin_gCross hqc
      · have hmemgOld2 : Prod.map ⇑Glue2 ⇑Glue2 p ∈ gOld2 := by
          rw [hgOld2_def]; exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hproot, hp'⟩, rfl⟩
        exact hnotin_gCross_of_mem_gOld2 _ hmemgOld2 hqc
  have hrootmmem : rootm ∈ belowDiagPairs (n₁ + n₂ - 2) := by
    rw [mem_belowDiagPairs, hrootm_def]
    exact (Fin.castLE_lt_castLE_iff (glue_le₂ hn₁ hn₂)).mpr (by decide)
  have hOldUnion_eq : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)), H.comap ⇑Glue1 = G₁ → H.comap ⇑Glue2 = G₂ →
      oldG1Edges ∪ oldG2Edges = (gOld1 ∪ gOld2 ∪ {rootm}).filter (fun p => H.Adj p.1 p.2) := by
    intro H hHG1 hHG2
    ext q
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro (hq | hq)
      · rw [holdG1E_def, Finset.mem_image] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        have hp' : p ∈ belowDiagPairs n₁ := (Finset.mem_filter.mp hp).1
        have hpAdj : G₁.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
        have hHAdj : H.Adj (Glue1 p.1) (Glue1 p.2) := (hHG1adj H hHG1 p hp').mpr hpAdj
        by_cases hproot : p = root1
        · subst hproot
          rw [hGlue1_root_fst, hGlue1_root_snd] at hHAdj
          exact ⟨Or.inr rfl, hHAdj⟩
        · exact ⟨Or.inl (Or.inl (Finset.mem_image.mpr
            ⟨p, Finset.mem_erase.mpr ⟨hproot, hp'⟩, rfl⟩)), hHAdj⟩
      · rw [holdG2E_def, Finset.mem_image] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        have hp' : p ∈ belowDiagPairs n₂ := (Finset.mem_filter.mp hp).1
        have hpAdj : G₂.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
        have hHAdj : H.Adj (Glue2 p.1) (Glue2 p.2) := (hHG2adj H hHG2 p hp').mpr hpAdj
        by_cases hproot : p = root2
        · subst hproot
          rw [hGlue2_root_fst, hGlue2_root_snd] at hHAdj
          exact ⟨Or.inr rfl, hHAdj⟩
        · exact ⟨Or.inl (Or.inr (Finset.mem_image.mpr
            ⟨p, Finset.mem_erase.mpr ⟨hproot, hp'⟩, rfl⟩)), hHAdj⟩
    · rintro ⟨(hq | hq) | hq, hHAdj⟩
      · rw [hgOld1_def, Finset.mem_image] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        have hp' : p ∈ belowDiagPairs n₁ := Finset.mem_of_mem_erase hp
        have hpAdj : G₁.Adj p.1 p.2 := (hHG1adj H hHG1 p hp').mp hHAdj
        exact Or.inl (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp', hpAdj⟩, rfl⟩)
      · rw [hgOld2_def, Finset.mem_image] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        have hp' : p ∈ belowDiagPairs n₂ := Finset.mem_of_mem_erase hp
        have hpAdj : G₂.Adj p.1 p.2 := (hHG2adj H hHG2 p hp').mp hHAdj
        exact Or.inr (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp', hpAdj⟩, rfl⟩)
      · subst hq
        rw [← hGlue1_root_fst, ← hGlue1_root_snd] at hHAdj
        have hpAdj : G₁.Adj (Fin.castLE hn₁ 0) (Fin.castLE hn₁ 1) :=
          (hHG1adj H hHG1 root1 hroot1mem).mp hHAdj
        exact Or.inl (Finset.mem_image.mpr ⟨root1, Finset.mem_filter.mpr ⟨hroot1mem, hpAdj⟩,
          hGlue1_at_root1⟩)
  have hbelow_eq : gOld1 ∪ gOld2 ∪ {rootm} ∪ gCross = belowDiagPairs (n₁ + n₂ - 2) := by
    have hstep1 : gOld1 ∪ gOld2 ∪ {rootm} ∪ gCross = insert rootm (gOld1 ∪ gOld2 ∪ gCross) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hstep1, hEm_eq, hEm_def]
    exact Finset.insert_erase hrootmmem
  have hLeftInvEdges : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)),
      H.comap ⇑Glue1 = G₁ → H.comap ⇑Glue2 = G₂ →
      oldG1Edges ∪ oldG2Edges ∪ gCross.filter (fun p => H.Adj p.1 p.2)
        = (belowDiagPairs (n₁ + n₂ - 2)).filter (fun p => H.Adj p.1 p.2) := by
    intro H hHG1 hHG2
    rw [hOldUnion_eq H hHG1 hHG2, ← Finset.filter_union, hbelow_eq]
  have hLeft_inv : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)),
      H.comap ⇑Glue1 = G₁ → H.comap ⇑Glue2 = G₂ → toGraph (toCross H) = H := by
    intro H hHG1 hHG2
    show graphOfPairs (oldG1Edges ∪ oldG2Edges ∪ gCross.filter (fun p => H.Adj p.1 p.2)) = H
    rw [hLeftInvEdges H hHG1 hHG2, graphOfPairs_filter_eq]
  have hRight_inv : ∀ S ∈ gCross.powerset, toCross (toGraph S) = S := by
    intro S hS
    have hSsub : S ⊆ gCross := Finset.mem_powerset.mp hS
    show gCross.filter (fun p => (graphOfPairs (oldG1Edges ∪ oldG2Edges ∪ S)).Adj p.1 p.2) = S
    apply Finset.ext
    intro p
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hpCross, hpAdj⟩
      have hpEm : p ∈ Em := hgCross_sub_Em hpCross
      have hpBelow : p ∈ belowDiagPairs (n₁ + n₂ - 2) := Finset.mem_of_mem_erase hpEm
      have hlt : p.1 < p.2 := mem_belowDiagPairs.mp hpBelow
      rw [graphOfPairs_adj_of_lt hlt, Finset.mem_union] at hpAdj
      rcases hpAdj with hpAdj | hpAdj
      · exact absurd hpCross (fun hpCross' =>
          Finset.disjoint_left.mp holdUnion_disjoint_cross hpAdj hpCross')
      · exact hpAdj
    · intro hpS
      have hpCross := hSsub hpS
      refine ⟨hpCross, ?_⟩
      have hpEm : p ∈ Em := hgCross_sub_Em hpCross
      have hpBelow : p ∈ belowDiagPairs (n₁ + n₂ - 2) := Finset.mem_of_mem_erase hpEm
      have hlt : p.1 < p.2 := mem_belowDiagPairs.mp hpBelow
      rw [graphOfPairs_adj_of_lt hlt, Finset.mem_union]
      exact Or.inr hpS
  have hFactor_eq : ∀ (H : SimpleGraph (Fin (n₁ + n₂ - 2))) (z : Fin (n₁ + n₂ - 2) → I),
      (∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2))
        = (∏ p ∈ toCross H, W.W (z p.1) (z p.2))
          * ∏ p ∈ gCross \ toCross H, (1 - W.W (z p.1) (z p.2)) := by
    intro H z
    show (∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2))
        = (∏ p ∈ gCross.filter (fun p => H.Adj p.1 p.2), W.W (z p.1) (z p.2))
          * ∏ p ∈ gCross \ gCross.filter (fun p => H.Adj p.1 p.2), (1 - W.W (z p.1) (z p.2))
    have hsplit := Finset.prod_filter_mul_prod_filter_not gCross (fun p => H.Adj p.1 p.2)
      (fun p => adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2))
    rw [← hsplit]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      have hadj : H.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
      unfold adjWeight
      rw [if_pos hadj]
    · rw [Finset.filter_not]
      apply Finset.prod_congr rfl
      intro p hp
      have hp' := Finset.mem_sdiff.mp hp
      have hnadj : ¬ H.Adj p.1 p.2 := fun hAdj => hp'.2 (Finset.mem_filter.mpr ⟨hp'.1, hAdj⟩)
      unfold adjWeight
      rw [if_neg hnadj]
  have hfiber_sum_eq_one : ∀ z : Fin (n₁ + n₂ - 2) → I,
      ∑ H ∈ Finset.univ.filter
          (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
        ∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2) = 1 := by
    intro z
    have hbij : ∑ H ∈ Finset.univ.filter
          (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
        ∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2)
        = ∑ S ∈ gCross.powerset,
            (∏ p ∈ S, W.W (z p.1) (z p.2)) * ∏ p ∈ gCross \ S, (1 - W.W (z p.1) (z p.2)) := by
      apply Finset.sum_nbij' toCross toGraph
      · intro H _
        show gCross.filter (fun p => H.Adj p.1 p.2) ∈ gCross.powerset
        exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      · exact fun S hS => htoGraph_mem_fiber S hS
      · intro H hH
        exact hLeft_inv H (Finset.mem_filter.mp hH).2.1 (Finset.mem_filter.mp hH).2.2
      · exact fun S hS => hRight_inv S hS
      · exact fun H _ => hFactor_eq H z
    rw [hbij, ← Finset.prod_add]
    simp
  have hpointwise : ∀ z : Fin (n₁ + n₂ - 2) → I,
      D1 (z ∘ ⇑Glue1) * D2 (z ∘ ⇑Glue2)
        = ∑ H ∈ Finset.univ.filter
            (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
          ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2) := by
    intro z
    calc D1 (z ∘ ⇑Glue1) * D2 (z ∘ ⇑Glue2)
        = D1 (z ∘ ⇑Glue1) * D2 (z ∘ ⇑Glue2) * 1 := by ring
      _ = D1 (z ∘ ⇑Glue1) * D2 (z ∘ ⇑Glue2)
            * (∑ H ∈ Finset.univ.filter
                (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
              ∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2)) := by
          rw [hfiber_sum_eq_one z]
      _ = ∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            D1 (z ∘ ⇑Glue1) * D2 (z ∘ ⇑Glue2)
              * ∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2) := by
          rw [Finset.mul_sum]
      _ = ∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            (∏ q ∈ gOld1, adjWeight W (H.Adj q.1 q.2) (z q.1) (z q.2))
              * (∏ q ∈ gOld2, adjWeight W (H.Adj q.1 q.2) (z q.1) (z q.2))
              * ∏ p ∈ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2) := by
          apply Finset.sum_congr rfl
          intro H hH
          obtain ⟨hHG1, hHG2⟩ := (Finset.mem_filter.mp hH).2
          rw [holdPart1_eq H hHG1 z, holdPart2_eq H hHG2 z]
      _ = ∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            ∏ p ∈ gOld1 ∪ gOld2 ∪ gCross, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2) := by
          apply Finset.sum_congr rfl
          intro H _
          rw [Finset.prod_union hgOldUnion_disjoint_cross, Finset.prod_union hgOld12_disjoint]
      _ = ∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (z p.1) (z p.2) := by
          rw [hEm_eq]
  -- Integrate the pointwise partition and match against `glue_marginal_split`.
  have hcore : (∫ y1 : Fin n₁ → I, D1 (pinRoots hn₁ u v y1))
        * (∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2))
      = ∑ H ∈ Finset.univ.filter
          (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
        ∫ y : Fin (n₁ + n₂ - 2) → I,
          ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v y p.1)
            (pinRoots (glue_le₂ hn₁ hn₂) u v y p.2) := by
    rw [← glue_marginal_split hn₁ hn₂ D1 D2 hD1meas hD10 hD11 hD2meas hD20 hD21 u v]
    have hpt2 : ∀ x : Fin (n₁ + n₂ - 2) → I,
        D1 (pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
            * D2 (pinRoots hn₂ u v (x ∘ ⇑Glue2))
          = ∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v x p.1)
              (pinRoots (glue_le₂ hn₁ hn₂) u v x p.2) := by
      intro x
      have hcast1 : pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂))
          = pinRoots (glue_le₂ hn₁ hn₂) u v x ∘ ⇑Glue1 :=
        (pinRoots_comp_rootfix_emb hn₁ (glue_le₂ hn₁ hn₂) Glue1
          (rootFixing_castLE hn₁ (glue_le₂ hn₁ hn₂) (glue_le₁ hn₁ hn₂)) u v x).symm
      have hcast2 : pinRoots hn₂ u v (x ∘ ⇑Glue2)
          = pinRoots (glue_le₂ hn₁ hn₂) u v x ∘ ⇑Glue2 :=
        (pinRoots_comp_rootfix_emb hn₂ (glue_le₂ hn₁ hn₂) Glue2
          (rootFixing_glueEmb₂ hn₁ hn₂) u v x).symm
      rw [hcast1, hcast2]
      exact hpointwise (pinRoots (glue_le₂ hn₁ hn₂) u v x)
    calc ∫ x : Fin (n₁ + n₂ - 2) → I,
          D1 (pinRoots hn₁ u v (x ∘ Fin.castLE (glue_le₁ hn₁ hn₂)))
            * D2 (pinRoots hn₂ u v (x ∘ ⇑Glue2))
        = ∫ x : Fin (n₁ + n₂ - 2) → I,
            ∑ H ∈ Finset.univ.filter
                (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
              ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v x p.1)
                (pinRoots (glue_le₂ hn₁ hn₂) u v x p.2) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt2)
      _ = ∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            ∫ x : Fin (n₁ + n₂ - 2) → I,
              ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v x p.1)
                (pinRoots (glue_le₂ hn₁ hn₂) u v x p.2) := by
          apply integral_finset_sum
          intro H _
          apply integrable_of_bounds'
          · apply Finset.measurable_prod
            intro p _
            have hpair : Measurable fun x : Fin (n₁ + n₂ - 2) → I =>
                W.W (pinRoots (glue_le₂ hn₁ hn₂) u v x p.1) (pinRoots (glue_le₂ hn₁ hn₂) u v x p.2) :=
              show Measurable (Function.uncurry W.W ∘ fun x : Fin (n₁ + n₂ - 2) → I =>
                  (pinRoots (glue_le₂ hn₁ hn₂) u v x p.1, pinRoots (glue_le₂ hn₁ hn₂) u v x p.2)) from
                W.measurable.comp
                  (((measurable_pi_apply p.1).comp (measurable_pinRoots (glue_le₂ hn₁ hn₂) u v)).prodMk
                    ((measurable_pi_apply p.2).comp (measurable_pinRoots (glue_le₂ hn₁ hn₂) u v)))
            unfold adjWeight
            split_ifs
            · exact hpair
            · exact measurable_const.sub hpair
          · exact fun x => Finset.prod_nonneg fun _ _ => adjWeight_nonneg W _ _ _
          · exact fun x => Finset.prod_le_one (fun _ _ => adjWeight_nonneg W _ _ _)
              (fun _ _ => adjWeight_le_one W _ _ _)
  have hG1root : adjWeight W (G₁.Adj (Fin.castLE hn₁ 0) (Fin.castLE hn₁ 1)) u v = rootWeight W σ' u v :=
    adjWeight_congr W (hG₁ 0 1).symm u v
  have hG2root : adjWeight W (G₂.Adj (Fin.castLE hn₂ 0) (Fin.castLE hn₂ 1)) u v = rootWeight W σ' u v :=
    adjWeight_congr W (hG₂ 0 1).symm u v
  have hA1eq : unnormRootedDensity W hn₁ G₁ u v
      = rootWeight W σ' u v * ∫ y1 : Fin n₁ → I, D1 (pinRoots hn₁ u v y1) := by
    rw [unnormRootedDensity_root_factor hn₁ G₁ u v, hG1root]
  have hA2eq : unnormRootedDensity W hn₂ G₂ u v
      = rootWeight W σ' u v * ∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2) := by
    rw [unnormRootedDensity_root_factor hn₂ G₂ u v, hG2root]
  have hHrootAdj : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)), H.comap ⇑Glue1 = G₁ →
      (H.Adj rootm.1 rootm.2 ↔ σ'.Adj 0 1) := by
    intro H hHG1
    rw [← hGlue1_root_fst, ← hGlue1_root_snd, hHG1adj H hHG1 root1 hroot1mem]
    exact (hG₁ 0 1).symm
  have hHrootWeight : ∀ H : SimpleGraph (Fin (n₁ + n₂ - 2)), H.comap ⇑Glue1 = G₁ →
      adjWeight W (H.Adj rootm.1 rootm.2) u v = rootWeight W σ' u v := fun H hHG1 =>
    adjWeight_congr W (hHrootAdj H hHG1) u v
  have hHeq : ∀ H ∈ Finset.univ.filter
      (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
      unnormRootedDensity W (glue_le₂ hn₁ hn₂) H u v
        = rootWeight W σ' u v * ∫ y : Fin (n₁ + n₂ - 2) → I,
            ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v y p.1)
              (pinRoots (glue_le₂ hn₁ hn₂) u v y p.2) := by
    intro H hH
    obtain ⟨hHG1, _⟩ := (Finset.mem_filter.mp hH).2
    rw [unnormRootedDensity_root_factor (glue_le₂ hn₁ hn₂) H u v, hHrootWeight H hHG1]
  calc unnormRootedDensity W hn₁ G₁ u v * unnormRootedDensity W hn₂ G₂ u v
      = (rootWeight W σ' u v * ∫ y1 : Fin n₁ → I, D1 (pinRoots hn₁ u v y1))
          * (rootWeight W σ' u v * ∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2)) := by
        rw [hA1eq, hA2eq]
    _ = rootWeight W σ' u v * (rootWeight W σ' u v *
          ((∫ y1 : Fin n₁ → I, D1 (pinRoots hn₁ u v y1))
            * ∫ y2 : Fin n₂ → I, D2 (pinRoots hn₂ u v y2))) := by ring
    _ = rootWeight W σ' u v * (rootWeight W σ' u v *
          (∑ H ∈ Finset.univ.filter
              (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
            ∫ y : Fin (n₁ + n₂ - 2) → I,
              ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v y p.1)
                (pinRoots (glue_le₂ hn₁ hn₂) u v y p.2))) := by rw [hcore]
    _ = rootWeight W σ' u v * ∑ H ∈ Finset.univ.filter
            (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
          (rootWeight W σ' u v * ∫ y : Fin (n₁ + n₂ - 2) → I,
            ∏ p ∈ Em, adjWeight W (H.Adj p.1 p.2) (pinRoots (glue_le₂ hn₁ hn₂) u v y p.1)
              (pinRoots (glue_le₂ hn₁ hn₂) u v y p.2)) := by rw [Finset.mul_sum]
    _ = rootWeight W σ' u v * ∑ H ∈ Finset.univ.filter
            (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => H.comap ⇑Glue1 = G₁ ∧ H.comap ⇑Glue2 = G₂),
          unnormRootedDensity W (glue_le₂ hn₁ hn₂) H u v := by
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        exact (hHeq H hH).symm

/-! ## The subset ↔ embedding bridge -/

/-- Every subset of the host containing the roots and of the right size is the range of a
root-fixing embedding (order the non-root part after the roots). -/
theorem exists_rootFixing_emb_range {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ)
    (S : Finset (Fin ℓ))
    (hroots : ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) ⊆ ↑S)
    (hcard : S.card = n) :
    ∃ j : Fin n ↪ Fin ℓ, RootFixing hn hℓ j ∧ Set.range ⇑j = ↑S := by
  classical
  set r0 : Fin ℓ := Fin.castLE hℓ 0 with hr0def
  set r1 : Fin ℓ := Fin.castLE hℓ 1 with hr1def
  have hne : r0 ≠ r1 := castLE01_ne hℓ
  have hr0S : r0 ∈ S := by
    have h := hroots (Set.mem_insert r0 {r1})
    simpa using h
  have hr1S : r1 ∈ S := by
    have h := hroots (Set.mem_insert_of_mem r0 (Set.mem_singleton r1))
    simpa using h
  set T : Finset (Fin ℓ) := (S.erase r0).erase r1 with hTdef
  have hr1S' : r1 ∈ S.erase r0 := Finset.mem_erase.mpr ⟨hne.symm, hr1S⟩
  have hSeq : S = insert r0 (insert r1 T) := by
    rw [hTdef, Finset.insert_erase hr1S', Finset.insert_erase hr0S]
  have hr0T : r0 ∉ T := by
    rw [hTdef, Finset.mem_erase]
    rintro ⟨-, h⟩
    exact (Finset.mem_erase.mp h).1 rfl
  have hr1T : r1 ∉ T := by
    rw [hTdef, Finset.mem_erase]
    rintro ⟨h, -⟩
    exact h rfl
  have hTsub : T ⊆ S := by
    rw [hTdef]
    exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hTcard : T.card = n - 2 := by
    have h1 : (S.erase r0).card = n - 1 := by rw [Finset.card_erase_of_mem hr0S, hcard]
    have h2 : T.card = (S.erase r0).card - 1 := by
      rw [hTdef]; exact Finset.card_erase_of_mem hr1S'
    omega
  have hcast_mem : ∀ c : Fin 2, Fin.castLE hℓ c = r0 ∨ Fin.castLE hℓ c = r1 := by
    intro c
    fin_cases c <;> simp [hr0def, hr1def]
  set jf : Fin n → Fin ℓ :=
    fun a => if h : (a : ℕ) < 2 then Fin.castLE hℓ ⟨(a : ℕ), h⟩
      else T.orderEmbOfFin hTcard ⟨(a : ℕ) - 2, by omega⟩ with hjfdef
  have hjinj : Function.Injective jf := by
    intro a b hab
    rw [hjfdef] at hab
    simp only at hab
    split_ifs at hab with ha hb hb
    · have hval : (a : ℕ) = (b : ℕ) := by
        have := Fin.val_eq_of_eq hab
        simpa using this
      exact Fin.ext hval
    · exfalso
      have hmemT : Fin.castLE hℓ (⟨(a : ℕ), ha⟩ : Fin 2) ∈ (T : Set (Fin ℓ)) := by
        rw [← Finset.range_orderEmbOfFin T hTcard]
        exact ⟨⟨(b : ℕ) - 2, by omega⟩, hab.symm⟩
      rcases hcast_mem ⟨(a : ℕ), ha⟩ with h0 | h1
      · rw [h0] at hmemT; exact hr0T (by simpa using hmemT)
      · rw [h1] at hmemT; exact hr1T (by simpa using hmemT)
    · exfalso
      have hmemT : Fin.castLE hℓ (⟨(b : ℕ), hb⟩ : Fin 2) ∈ (T : Set (Fin ℓ)) := by
        rw [← Finset.range_orderEmbOfFin T hTcard]
        exact ⟨⟨(a : ℕ) - 2, by omega⟩, hab⟩
      rcases hcast_mem ⟨(b : ℕ), hb⟩ with h0 | h1
      · rw [h0] at hmemT; exact hr0T (by simpa using hmemT)
      · rw [h1] at hmemT; exact hr1T (by simpa using hmemT)
    · have hidx : ((⟨(a : ℕ) - 2, by omega⟩ : Fin (n - 2)) : ℕ)
          = ((⟨(b : ℕ) - 2, by omega⟩ : Fin (n - 2)) : ℕ) := by
        have := (T.orderEmbOfFin hTcard).injective hab
        simpa using congrArg Fin.val this
      simp only at hidx
      exact Fin.ext (by omega)
  refine ⟨⟨jf, hjinj⟩, ?_, ?_⟩
  · intro c
    show jf (Fin.castLE hn c) = Fin.castLE hℓ c
    have hc2 : ((Fin.castLE hn c : Fin n) : ℕ) < 2 := c.isLt
    rw [hjfdef]
    simp only
    rw [dif_pos hc2]
    congr 1
  · ext y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      show jf a ∈ (↑S : Set (Fin ℓ))
      rw [hjfdef]
      simp only
      split_ifs with ha
      · rcases hcast_mem ⟨(a : ℕ), ha⟩ with h0 | h1
        · rw [h0, hSeq]; simp
        · rw [h1, hSeq]; simp
      · have hmemT : T.orderEmbOfFin hTcard ⟨(a : ℕ) - 2, by omega⟩ ∈ (T : Set (Fin ℓ)) := by
          rw [← Finset.range_orderEmbOfFin T hTcard]
          exact ⟨_, rfl⟩
        exact hTsub hmemT
    · intro hy
      have hyS : y ∈ S := hy
      rw [hSeq, Finset.mem_insert, Finset.mem_insert] at hyS
      rcases hyS with rfl | rfl | hyT
      · refine ⟨Fin.castLE hn 0, ?_⟩
        show jf (Fin.castLE hn (0 : Fin 2)) = r0
        rw [hjfdef]; simp only
        rw [dif_pos (show ((Fin.castLE hn (0 : Fin 2) : Fin n) : ℕ) < 2 from (0 : Fin 2).isLt)]
        exact congrArg (Fin.castLE hℓ) (Fin.ext rfl)
      · refine ⟨Fin.castLE hn 1, ?_⟩
        show jf (Fin.castLE hn (1 : Fin 2)) = r1
        rw [hjfdef]; simp only
        rw [dif_pos (show ((Fin.castLE hn (1 : Fin 2) : Fin n) : ℕ) < 2 from (1 : Fin 2).isLt)]
        exact congrArg (Fin.castLE hℓ) (Fin.ext rfl)
      · have hyT' : y ∈ (↑T : Set (Fin ℓ)) := hyT
        rw [← Finset.range_orderEmbOfFin T hTcard] at hyT'
        obtain ⟨idx, hidx⟩ := hyT'
        have hidxlt : (idx : ℕ) < n - 2 := idx.isLt
        have ha_lt : (idx : ℕ) + 2 < n := by omega
        set a0 : Fin n := ⟨(idx : ℕ) + 2, ha_lt⟩ with ha0def
        have ha0val : (a0 : ℕ) = (idx : ℕ) + 2 := rfl
        have ha0not2 : ¬ ((a0 : ℕ) < 2) := by omega
        refine ⟨a0, ?_⟩
        show jf a0 = y
        rw [hjfdef]
        simp only
        rw [dif_neg ha0not2]
        have hval2 : (⟨(a0 : ℕ) - 2, by omega⟩ : Fin (n - 2)) = idx := by
          apply Fin.ext
          show (a0 : ℕ) - 2 = (idx : ℕ)
          omega
        rw [hval2, hidx]

/-- **The subset ↔ embedding condition bridge**: for a root-fixing embedding `j` with range
`S`, the "some rooted induced subgraph on `S` is a copy of `G`" clause of the count formula
(`flagDensity₁_stdRooted`) is equivalent to the pullback along `j` having the flag class of
`G`.  (The rooted analogue of the `comap_iso_induce_range` + `graphFlag_eq_iff` step in
`GraphonHom.lean`'s averaging.) -/
theorem stdRooted_subset_iso_iff {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) {σ' : FlagType (Fin 2)}
    (H : SimpleGraph (Fin ℓ)) (hH : RootCompatible σ' hℓ H)
    (G : SimpleGraph (Fin n)) (hG : RootCompatible σ' hn G)
    (j : Fin n ↪ Fin ℓ) (hj : RootFixing hn hℓ j) (S : Finset (Fin ℓ))
    (hS : Set.range ⇑j = ↑S) :
    (∃ h : (mkStdRooted σ' hℓ H hH).type_verts ⊆ (↑S : Set (Fin ℓ)),
        Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hH) (↑S) h).coe
          ≃f mkStdRooted σ' hn G hG))
      ↔ (⟦mkStdRooted σ' hn (H.comap ⇑j)
            (rootCompatible_comap_of_rootFixing hn hℓ j hj hH)⟧ : Flag σ' (Fin n))
          = ⟦mkStdRooted σ' hn G hG⟧ := by
  classical
  have hRoots : (mkStdRooted σ' hℓ H hH).type_verts ⊆ (↑S : Set (Fin ℓ)) := by
    rw [mkStdRooted_type_verts, ← hS]
    rintro x hx
    rcases hx with rfl | rfl
    · exact ⟨Fin.castLE hn 0, hj 0⟩
    · exact ⟨Fin.castLE hn 1, hj 1⟩
  set eqv : Fin n ≃ (↑S : Set (Fin ℓ)) := (Equiv.ofInjective j j.injective).trans (Equiv.setCongr hS)
    with heqvdef
  have heqv_apply : ∀ a : Fin n, ((eqv a : Fin ℓ)) = j a := by
    intro a
    simp only [heqvdef, Equiv.trans_apply, Equiv.setCongr_apply, Equiv.ofInjective_apply]
  have hjeqv : ∀ u : (↑S : Set (Fin ℓ)), j (eqv.symm u) = (u : Fin ℓ) := by
    intro u
    have h1 := heqv_apply (eqv.symm u)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  set graph_iso : ((⊤ : H.Subgraph).induce (↑S : Set (Fin ℓ))).coe ≃g H.comap ⇑j :=
    ⟨eqv.symm, by
      intro u v
      show (H.comap ⇑j).Adj (eqv.symm u) (eqv.symm v)
          ↔ ((⊤ : H.Subgraph).induce (↑S : Set (Fin ℓ))).Adj u.1 v.1
      simp only [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj]
      simp only [SimpleGraph.comap_adj]
      rw [hjeqv u, hjeqv v]
      constructor
      · intro hadj; exact ⟨u.2, v.2, hadj⟩
      · rintro ⟨-, -, hadj⟩; exact hadj⟩ with hgidef
  have coeIso : (LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hH) (↑S) hRoots).coe
      ≃f mkStdRooted σ' hn (H.comap ⇑j) (rootCompatible_comap_of_rootFixing hn hℓ j hj hH) := by
    refine ⟨graph_iso, ?_⟩
    funext t
    show graph_iso
        ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hH) (↑S) hRoots).type_embed t)
      = Fin.castLE hn t
    have hstep :
        (LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hH) (↑S) hRoots).type_embed t
          = ⟨Fin.castLE hℓ t, hRoots ((mkStdRooted σ' hℓ H hH).type_verts_contain t)⟩ := rfl
    rw [hstep]
    have hval : graph_iso
        (⟨Fin.castLE hℓ t, hRoots ((mkStdRooted σ' hℓ H hH).type_verts_contain t)⟩
          : (↑S : Set (Fin ℓ)))
        = eqv.symm ⟨Fin.castLE hℓ t, hRoots ((mkStdRooted σ' hℓ H hH).type_verts_contain t)⟩ := by
      rw [hgidef]; rfl
    rw [hval]
    apply j.injective
    rw [hjeqv, hj t]
  constructor
  · rintro ⟨h, ⟨φ⟩⟩
    rw [Quotient.eq]
    exact ⟨coeIso.symm.trans φ⟩
  · intro heq
    rw [Quotient.eq] at heq
    obtain ⟨χ⟩ := heq
    exact ⟨hRoots, ⟨coeIso.trans χ⟩⟩

end FlagAlgebras.MetaTheory
