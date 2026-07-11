import LeanFlagAlgebras.MetaTheory.GraphonBasic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Induced flag densities of a graphon

The analytic layer of the `φ_W` construction (infrastructure toward `thm:k4free-p4-tripartite`'s
representation input; no direct `paper.tex` display — the paper treats "every graphon is a limit
object" as folklore).  For a graphon `W` and a labelled graph `G` on `Fin n` we define the
**induced density**

`graphonFlagDensity W G = ∫_{x : Fin n → I} ∏_{i<j} wt(G.Adj i j, x i, x j)`,

where the factor is `W (x i) (x j)` for an edge and `1 − W (x i) (x j)` for a non-edge: the
probability that a `W`-random graph on `n` sampled points equals `G` exactly (as a labelled
graph).  The three key identities proved here drive the `zeroSpaceProp`/`mulProp` discharge in
`MetaTheory/GraphonHom.lean`:

* `graphonFlagDensity_comap_equiv` — **relabelling invariance**: precomposing the vertex labels
  with a permutation does not change the density (change of variables via
  `volume_measurePreserving_piCongrLeft`).
* `graphonFlagDensity_extension_sum` — **extension partition**: the density of `G` on `Fin n`
  is the sum of the densities of all graphs `H` on `Fin ℓ` (`n ≤ ℓ`) restricting to `G` on the
  first `n` vertices.  Pointwise this is a partition of unity over the new vertex pairs
  (`Finset.prod_add`), and the integral of the restricted weight marginalises through
  `volume_preserving_piEquivPiSubtypeProd`.
* `graphonFlagDensity_block_mul` — **block product**: the product of two densities is the sum
  of the densities of all graphs on `Fin (n₁ + n₂)` restricting to the two factors on the two
  blocks (partition of unity over the cross pairs, then
  `volume_measurePreserving_sumPiEquivProdPi` + `integral_prod`).

Corollaries: `graphonFlagDensity_mem_Icc`, `graphonFlagDensity_fin_zero = 1`,
`sum_graphonFlagDensity = 1` (total mass), and the edge computation
`graphonFlagDensity_top_two = W.edgeDensity` linking back to `GraphonBasic`.
-/

open MeasureTheory unitInterval Finset
open scoped Classical

namespace FlagAlgebras.MetaTheory

/-- On a probability space, a measurable function squeezed between two constants is
integrable (local copy of the `GraphonBasic` workhorse). -/
private lemma integrable_of_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-! ## Ordered pairs and the edge factor -/

/-- The strictly increasing vertex pairs of `Fin n`: the index set of the weight product.
Each unordered pair `{i,j}` appears exactly once, as `(min, max)`. -/
def belowDiagPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

lemma mem_belowDiagPairs {n : ℕ} {p : Fin n × Fin n} : p ∈ belowDiagPairs n ↔ p.1 < p.2 := by
  unfold belowDiagPairs
  simp

/-- The edge factor of the induced weight: `W u v` if the (decidable) adjacency `b` holds and
`1 − W u v` otherwise. -/
noncomputable def adjWeight (W : Graphon) (b : Prop) (u v : I) : ℝ :=
  if b then W.W u v else 1 - W.W u v

lemma adjWeight_nonneg (W : Graphon) (b : Prop) (u v : I) : 0 ≤ adjWeight W b u v := by
  unfold adjWeight
  split_ifs
  · exact W.nonneg u v
  · linarith [W.le_one u v]

lemma adjWeight_le_one (W : Graphon) (b : Prop) (u v : I) : adjWeight W b u v ≤ 1 := by
  unfold adjWeight
  split_ifs
  · exact W.le_one u v
  · linarith [W.nonneg u v]

/-- The factor is symmetric in the two sample points (symmetry of the kernel). -/
lemma adjWeight_symm (W : Graphon) (b : Prop) (u v : I) :
    adjWeight W b u v = adjWeight W b v u := by
  unfold adjWeight
  rw [W.symm u v]

/-- The factor is congruent along equivalent adjacency propositions. -/
lemma adjWeight_congr (W : Graphon) {b b' : Prop} (h : b ↔ b') (u v : I) :
    adjWeight W b u v = adjWeight W b' u v := by
  unfold adjWeight
  by_cases hb : b
  · rw [if_pos hb, if_pos (h.mp hb)]
  · rw [if_neg hb, if_neg (fun hb' => hb (h.mpr hb'))]

/-- Complementary factors sum to one: `adjWeight b + adjWeight (¬ b) = 1`. -/
lemma adjWeight_add_not (W : Graphon) (b : Prop) (u v : I) :
    adjWeight W b u v + adjWeight W (¬ b) u v = 1 := by
  unfold adjWeight
  by_cases hb : b
  · rw [if_pos hb, if_neg (not_not_intro hb)]; ring
  · rw [if_neg hb, if_pos hb]; ring

/-! ## The induced weight and the induced density -/

/-- The pointwise induced weight of the labelled graph `G` at the sample `x`: the product of
the edge factors over all strictly increasing vertex pairs.  This is the conditional
probability that a `W`-random graph on the sampled points `x` equals `G`. -/
noncomputable def inducedWeight (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → I) : ℝ :=
  ∏ p ∈ belowDiagPairs n, adjWeight W (G.Adj p.1 p.2) (x p.1) (x p.2)

lemma inducedWeight_nonneg (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → I) :
    0 ≤ inducedWeight W G x :=
  Finset.prod_nonneg fun _ _ => adjWeight_nonneg W _ _ _

lemma inducedWeight_le_one (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → I) :
    inducedWeight W G x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => adjWeight_nonneg W _ _ _)
    (fun _ _ => adjWeight_le_one W _ _ _)

lemma measurable_inducedWeight (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) :
    Measurable (inducedWeight W G) := by
  -- Finite product of measurable factors.  Each factor: `adjWeight` at a fixed proposition is
  -- either `W.W (x i) (x j)` or `1 − W.W (x i) (x j)`; compose `W.measurable` with the
  -- measurable evaluation pair `(measurable_pi_apply i).prodMk (measurable_pi_apply j)` and
  -- split on the `if` (the condition does not depend on `x`).
  apply Finset.measurable_prod
  intro p _
  have hpair : Measurable fun x : Fin n → I => W.W (x p.1) (x p.2) :=
    show Measurable (Function.uncurry W.W ∘ fun x : Fin n → I => (x p.1, x p.2)) from
      W.measurable.comp ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))
  unfold adjWeight
  split_ifs
  · exact hpair
  · exact measurable_const.sub hpair

lemma integrable_inducedWeight (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) :
    Integrable (inducedWeight W G) (volume : Measure (Fin n → I)) :=
  integrable_of_bounds (measurable_inducedWeight W G) (inducedWeight_nonneg W G)
    (inducedWeight_le_one W G)

/-- **The induced flag density** of the labelled graph `G` in the graphon `W`: the probability
that a `W`-random graph on `n` uniform samples equals `G` as a labelled graph. -/
noncomputable def graphonFlagDensity (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  ∫ x : Fin n → I, inducedWeight W G x

lemma graphonFlagDensity_nonneg (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) :
    0 ≤ graphonFlagDensity W G :=
  integral_nonneg fun x => inducedWeight_nonneg W G x

lemma graphonFlagDensity_le_one (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphonFlagDensity W G ≤ 1 := by
  -- `∫ wt ≤ ∫ 1 = 1` on the probability space, as in `GraphonBasic.deg_le_one`.
  have h : graphonFlagDensity W G ≤ ∫ _ : Fin n → I, (1 : ℝ) :=
    integral_mono (integrable_inducedWeight W G) (integrable_const 1) (inducedWeight_le_one W G)
  simpa using h

lemma graphonFlagDensity_mem_Icc (W : Graphon) {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphonFlagDensity W G ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨graphonFlagDensity_nonneg W G, graphonFlagDensity_le_one W G⟩

/-- Graphs on no vertices have induced density one (the empty product integrated over a
probability space). -/
lemma graphonFlagDensity_fin_zero (W : Graphon) (G : SimpleGraph (Fin 0)) :
    graphonFlagDensity W G = 1 := by
  -- `belowDiagPairs 0 = ∅`, so the weight is constantly `1`; `∫ 1 = 1` since the pi volume
  -- on `Fin 0 → I` is a probability measure.
  have hempty : belowDiagPairs 0 = ∅ := by
    unfold belowDiagPairs
    rw [Finset.univ_eq_empty]
    simp
  have hw : inducedWeight W G = fun _ => (1 : ℝ) := by
    funext x
    unfold inducedWeight
    rw [hempty, Finset.prod_empty]
  unfold graphonFlagDensity
  rw [hw]
  simp

/-! ## Relabelling invariance -/

/-- Sort the image of a pair under `e` into increasing order: the reindexing map used to prove
relabelling invariance of the induced weight. -/
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
with `e` amounts to comapping the graph along `e`. -/
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

/-- **Relabelling invariance**: pulling the graph back along a permutation of the vertex
labels does not change the induced density.

Proof route: pointwise, `inducedWeight W (G.comap e) x = inducedWeight W G (x ∘ e.symm)` by
reindexing the pair product along `p ↦ (e p.1, e p.2)` sorted into increasing order
(`Finset.prod_nbij'`; the factor is symmetric in its two sample points by `adjWeight_symm`
and `G.adj_comm`).  Then change variables with
`volume_measurePreserving_piCongrLeft` for the self-equiv `e.symm` of `Fin n`. -/
theorem graphonFlagDensity_comap_equiv (W : Graphon) {n : ℕ} (e : Fin n ≃ Fin n)
    (G : SimpleGraph (Fin n)) :
    graphonFlagDensity W (G.comap e) = graphonFlagDensity W G := by
  have hΦ : ∀ x : Fin n → I,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => I) e) x = x ∘ e.symm := by
    intro x
    funext j
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => I) e x (e.symm j)
    simpa [Equiv.apply_symm_apply] using h
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => I) e
  have hcomp := hmp.integral_comp' (inducedWeight W G)
  unfold graphonFlagDensity
  calc (∫ x : Fin n → I, inducedWeight W (G.comap e) x)
      = ∫ x : Fin n → I, inducedWeight W G (x ∘ e.symm) :=
        integral_congr_ae (Filter.Eventually.of_forall (inducedWeight_comap_equiv W e G))
    _ = ∫ x : Fin n → I, inducedWeight W G ((MeasurableEquiv.piCongrLeft (fun _ => I) e) x) := by
        simp only [hΦ]
    _ = ∫ y : Fin n → I, inducedWeight W G y := hcomp

/-! ## Reconstructing a graph from its upper-triangle edge set -/

/-- The graph whose upper-triangle adjacency (`p.1 < p.2`) is exactly membership in `S`.
Built via `SimpleGraph.fromRel`, which symmetrizes and removes loops automatically. -/
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

/-- Every graph on `Fin m` is `graphOfPairs` of its own upper-triangle edge set. -/
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

/-- Recovering `H.comap f = G` from an edge-membership check on the upper triangle: if the
`f`-images of every increasing pair of `Fin n` are `E`-members exactly when `G` says so, then
`graphOfPairs E` comaps along `f` to `G`. -/
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

/-! ## The extension partition -/

/-- The pairs of `Fin ℓ` both lying inside the first `n` vertices (the "old" positions). -/
private def extOldIdx {n ℓ : ℕ} (h : n ≤ ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (belowDiagPairs n).image (Prod.map (Fin.castLE h) (Fin.castLE h))

/-- The remaining pairs of `Fin ℓ` (at least one endpoint among the new vertices). -/
private def extNewIdx {n ℓ : ℕ} (h : n ≤ ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  belowDiagPairs ℓ \ extOldIdx h

/-- The edge set of `G`, embedded into the old positions of `Fin ℓ`. -/
private noncomputable def extGEdges {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n)) :
    Finset (Fin ℓ × Fin ℓ) :=
  ((belowDiagPairs n).filter (fun p => G.Adj p.1 p.2)).image (Prod.map (Fin.castLE h) (Fin.castLE h))

/-- The fibre of graphs on `Fin ℓ` restricting to `G` on the first `n` vertices. -/
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

/-- Pointwise, the induced weight splits over old/new position pairs. -/
private lemma extInducedWeight_split {n ℓ : ℕ} (h : n ≤ ℓ) (W : Graphon)
    (H : SimpleGraph (Fin ℓ)) (x : Fin ℓ → I) :
    inducedWeight W H x
      = (∏ p ∈ extOldIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
        * ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
  unfold inducedWeight
  rw [← extOldIdx_union_newIdx h, Finset.prod_union (extOldIdx_disjoint_newIdx h)]

/-- Over the fibre, the old-position factor is constantly `G`'s induced weight at the
restricted sample. -/
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

/-- Membership of a cast old-position pair in `extGEdges h G ∪ S` (for `S` among the new
positions) matches `G`'s own adjacency. -/
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

/-- Reconstruction: for `S` among the new positions, `graphOfPairs (extGEdges h G ∪ S)`
lies in the fibre over `G`. -/
private def extToGraph {n ℓ : ℕ} (h : n ≤ ℓ) (G : SimpleGraph (Fin n))
    (S : Finset (Fin ℓ × Fin ℓ)) : SimpleGraph (Fin ℓ) :=
  graphOfPairs (extGEdges h G ∪ S)

/-- The new-position edge set of a fibre graph. -/
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

/-- The equivalence identifying `Fin n` with the "old" (`< n`) positions of `Fin ℓ`. -/
private def extSubtypeEquiv {n ℓ : ℕ} (h : n ≤ ℓ) :
    Fin n ≃ {i : Fin ℓ // (i : ℕ) < n} where
  toFun k := ⟨Fin.castLE h k, k.2⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv k := by simp
  right_inv i := by
    apply Subtype.ext
    simp

/-- Marginalisation: the integral of a function depending only on the restriction to the
first `n` coordinates is the integral of that function on `Fin n → I`. -/
private lemma extMarginal {n ℓ : ℕ} (h : n ≤ ℓ) (W : Graphon) (G : SimpleGraph (Fin n)) :
    ∫ x : Fin ℓ → I, inducedWeight W G (x ∘ Fin.castLE h) = graphonFlagDensity W G := by
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
    fun z => inducedWeight W G (z.1 ∘ ι) with hG'_def
  have hstep1 : ∫ x : Fin ℓ → I, inducedWeight W G (x ∘ Fin.castLE h)
      = ∫ z : ({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I), G' z := by
    have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin ℓ => I) p
    rw [← hΨ_def] at hmp
    rw [← hmp.integral_comp' G']
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [hG'_def, hcomp x]
  have hstep2 : ∫ z : ({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I), G' z
      = ∫ z1 : {i : Fin ℓ // p i} → I, inducedWeight W G (z1 ∘ ι) := by
    have hInt : Integrable G' volume := by
      apply integrable_of_bounds ((measurable_inducedWeight W G).comp hmeas)
      · exact fun z => inducedWeight_nonneg W G _
      · exact fun z => inducedWeight_le_one W G _
    rw [show (volume : Measure (({i : Fin ℓ // p i} → I) × ({i : Fin ℓ // ¬ p i} → I)))
        = (volume : Measure ({i : Fin ℓ // p i} → I)).prod volume from rfl,
      integral_prod _ hInt]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z1
    simp [hG'_def]
  have hstep3 : ∫ z1 : {i : Fin ℓ // p i} → I, inducedWeight W G (z1 ∘ ι)
      = graphonFlagDensity W G := by
    have hmp2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n => I) ι.symm
    have hΦeq : ∀ z1 : {i : Fin ℓ // p i} → I,
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => I) ι.symm) z1 = z1 ∘ ι := by
      intro z1
      funext k
      have hkey := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => I) ι.symm z1
          (ι k)
      simpa [Equiv.symm_apply_apply] using hkey
    unfold graphonFlagDensity
    rw [← hmp2.integral_comp' (inducedWeight W G)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z1
    simp only [hΦeq]
  rw [hstep1, hstep2, hstep3]

/-- **Extension partition**: the induced density of `G` on `Fin n` equals the total induced
density of all graphs on `Fin ℓ` (`n ≤ ℓ`) whose restriction to the first `n` vertices
(`SimpleGraph.comap (Fin.castLE h)`) is `G`.

Proof route: for each sample `x : Fin ℓ → I`, split `inducedWeight W H x` over the pairs of
`Fin ℓ` lying inside the first `n` vertices versus the rest; summing over the fibre
`{H | H.comap (Fin.castLE h) = G}` the inside part is constantly
`inducedWeight W G (x ∘ Fin.castLE h)` and the outside parts sum to `1` by the binomial
partition of unity (`Finset.prod_add` + `adjWeight_add_not`, with the fibre in bijection with
the powerset of the new pairs).  Finally
`∫_{I^ℓ} inducedWeight W G (x ∘ Fin.castLE h) = graphonFlagDensity W G` by marginalisation
(`volume_preserving_piEquivPiSubtypeProd` at the predicate `fun i : Fin ℓ => (i : ℕ) < n`,
plus `volume_measurePreserving_piCongrLeft` to identify the subtype pi with `Fin n → I`). -/
theorem graphonFlagDensity_extension_sum (W : Graphon) {n ℓ : ℕ} (h : n ≤ ℓ)
    (G : SimpleGraph (Fin n)) :
    graphonFlagDensity W G
      = ∑ H ∈ Finset.univ.filter
          (fun H : SimpleGraph (Fin ℓ) => H.comap (Fin.castLE h) = G),
          graphonFlagDensity W H := by
  show graphonFlagDensity W G = ∑ H ∈ extFiber h G, graphonFlagDensity W H
  rw [← extMarginal h W G]
  have hpointwise : ∀ x : Fin ℓ → I,
      inducedWeight W G (x ∘ Fin.castLE h) = ∑ H ∈ extFiber h G, inducedWeight W H x := by
    intro x
    calc inducedWeight W G (x ∘ Fin.castLE h)
        = inducedWeight W G (x ∘ Fin.castLE h) * 1 := by ring
      _ = inducedWeight W G (x ∘ Fin.castLE h) * (∑ H ∈ extFiber h G,
            ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2)) := by
          rw [extFiber_sum_eq_one h W G x]
      _ = ∑ H ∈ extFiber h G, inducedWeight W G (x ∘ Fin.castLE h)
            * ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
          rw [Finset.mul_sum]
      _ = ∑ H ∈ extFiber h G, (∏ p ∈ extOldIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
            * ∏ p ∈ extNewIdx h, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
          apply Finset.sum_congr rfl
          intro H hH
          rw [extOldPart_eq h W G hH x]
      _ = ∑ H ∈ extFiber h G, inducedWeight W H x := by
          apply Finset.sum_congr rfl
          intro H _
          rw [extInducedWeight_split h W H x]
  calc ∫ x : Fin ℓ → I, inducedWeight W G (x ∘ Fin.castLE h)
      = ∫ x : Fin ℓ → I, ∑ H ∈ extFiber h G, inducedWeight W H x :=
        integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ∑ H ∈ extFiber h G, ∫ x : Fin ℓ → I, inducedWeight W H x :=
        integral_finset_sum _ (fun H _ => integrable_inducedWeight W H)
    _ = ∑ H ∈ extFiber h G, graphonFlagDensity W H := rfl

/-- Total mass: the induced densities of all graphs on `Fin n` sum to one.  (The extension
partition from the unique graph on `Fin 0`, whose density is `1` and whose fibre is
everything.) -/
theorem sum_graphonFlagDensity (W : Graphon) (n : ℕ) :
    ∑ H : SimpleGraph (Fin n), graphonFlagDensity W H = 1 := by
  have hsub : Subsingleton (SimpleGraph (Fin 0)) := ⟨fun G1 G2 => by ext u _; exact u.elim0⟩
  have hext := graphonFlagDensity_extension_sum W (Nat.zero_le n) (⊥ : SimpleGraph (Fin 0))
  rw [graphonFlagDensity_fin_zero W (⊥ : SimpleGraph (Fin 0))] at hext
  have hfilter : Finset.univ.filter
      (fun H : SimpleGraph (Fin n) => H.comap (Fin.castLE (Nat.zero_le n)) = (⊥ : SimpleGraph (Fin 0)))
      = Finset.univ :=
    Finset.filter_true_of_mem fun H _ => hsub.elim _ _
  rw [hfilter] at hext
  exact hext.symm

/-! ## The block product -/

/-- The pairs of `Fin (n₁+n₂)` both lying in the first block. -/
private def blkIdx1 (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  (belowDiagPairs n₁).image (Prod.map (Fin.castAdd n₂) (Fin.castAdd n₂))

/-- The pairs of `Fin (n₁+n₂)` both lying in the second block. -/
private def blkIdx2 (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  (belowDiagPairs n₂).image (Prod.map (Fin.natAdd n₁) (Fin.natAdd n₁))

private def blkOldIdx (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  blkIdx1 n₁ n₂ ∪ blkIdx2 n₁ n₂

/-- The cross pairs: one endpoint in each block. -/
private def blkCross (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  belowDiagPairs (n₁ + n₂) \ blkOldIdx n₁ n₂

private noncomputable def blkG1Edges {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) :
    Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  ((belowDiagPairs n₁).filter (fun p => G₁.Adj p.1 p.2)).image
    (Prod.map (Fin.castAdd n₂) (Fin.castAdd n₂))

private noncomputable def blkG2Edges {n₁ n₂ : ℕ} (G₂ : SimpleGraph (Fin n₂)) :
    Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  ((belowDiagPairs n₂).filter (fun p => G₂.Adj p.1 p.2)).image
    (Prod.map (Fin.natAdd n₁) (Fin.natAdd n₁))

private noncomputable def blkFiber {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁))
    (G₂ : SimpleGraph (Fin n₂)) : Finset (SimpleGraph (Fin (n₁ + n₂))) :=
  Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂)) =>
    H.comap (Fin.castAdd n₂) = G₁ ∧ H.comap (Fin.natAdd n₁) = G₂)

private lemma blkFiber_mem_iff {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    (H : SimpleGraph (Fin (n₁ + n₂))) :
    H ∈ blkFiber G₁ G₂ ↔ H.comap (Fin.castAdd n₂) = G₁ ∧ H.comap (Fin.natAdd n₁) = G₂ := by
  unfold blkFiber; simp

private lemma blkCastAdd_injective (n₁ n₂ : ℕ) :
    Function.Injective
      (Prod.map (Fin.castAdd n₂) (Fin.castAdd n₂) : Fin n₁ × Fin n₁ → Fin (n₁+n₂) × Fin (n₁+n₂)) :=
  (Fin.castAdd_injective n₁ n₂).prodMap (Fin.castAdd_injective n₁ n₂)

private lemma blkNatAdd_injective (n₁ n₂ : ℕ) :
    Function.Injective
      (Prod.map (Fin.natAdd n₁) (Fin.natAdd n₁) : Fin n₂ × Fin n₂ → Fin (n₁+n₂) × Fin (n₁+n₂)) :=
  (Fin.natAdd_injective n₂ n₁).prodMap (Fin.natAdd_injective n₂ n₁)

private lemma blkIdx1_sub (n₁ n₂ : ℕ) : blkIdx1 n₁ n₂ ⊆ belowDiagPairs (n₁ + n₂) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rw [mem_belowDiagPairs] at hp ⊢
  exact Fin.strictMono_castAdd n₂ hp

private lemma blkIdx2_sub (n₁ n₂ : ℕ) : blkIdx2 n₁ n₂ ⊆ belowDiagPairs (n₁ + n₂) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rw [mem_belowDiagPairs] at hp ⊢
  exact Fin.strictMono_natAdd n₁ hp

private lemma blkIdx1_disjoint_blkIdx2 (n₁ n₂ : ℕ) : Disjoint (blkIdx1 n₁ n₂) (blkIdx2 n₁ n₂) := by
  rw [Finset.disjoint_left]
  intro q hq1 hq2
  obtain ⟨p1, -, rfl⟩ := Finset.mem_image.mp hq1
  obtain ⟨p2, -, heq⟩ := Finset.mem_image.mp hq2
  have hfst : Fin.natAdd n₁ p2.1 = Fin.castAdd n₂ p1.1 := congrArg Prod.fst heq
  have hval : (Fin.natAdd n₁ p2.1 : ℕ) = (Fin.castAdd n₂ p1.1 : ℕ) := congrArg Fin.val hfst
  rw [Fin.val_natAdd, Fin.val_castAdd] at hval
  have hlt := p1.1.isLt
  omega

private lemma blkOldIdx_sub (n₁ n₂ : ℕ) : blkOldIdx n₁ n₂ ⊆ belowDiagPairs (n₁ + n₂) :=
  Finset.union_subset (blkIdx1_sub n₁ n₂) (blkIdx2_sub n₁ n₂)

private lemma blkOldIdx_union_cross (n₁ n₂ : ℕ) :
    blkOldIdx n₁ n₂ ∪ blkCross n₁ n₂ = belowDiagPairs (n₁ + n₂) :=
  Finset.union_sdiff_of_subset (blkOldIdx_sub n₁ n₂)

private lemma blkOldIdx_disjoint_cross (n₁ n₂ : ℕ) : Disjoint (blkOldIdx n₁ n₂) (blkCross n₁ n₂) :=
  Finset.disjoint_sdiff

/-- Pointwise, the induced weight splits over the two blocks and the cross pairs. -/
private lemma blkInducedWeight_split (n₁ n₂ : ℕ) (W : Graphon) (H : SimpleGraph (Fin (n₁ + n₂)))
    (x : Fin (n₁ + n₂) → I) :
    inducedWeight W H x
      = ((∏ p ∈ blkIdx1 n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
          * ∏ p ∈ blkIdx2 n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
        * ∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
  unfold inducedWeight
  rw [← blkOldIdx_union_cross n₁ n₂, Finset.prod_union (blkOldIdx_disjoint_cross n₁ n₂)]
  congr 1
  unfold blkOldIdx
  rw [Finset.prod_union (blkIdx1_disjoint_blkIdx2 n₁ n₂)]

private lemma blkOldPart1_eq {n₁ n₂ : ℕ} (W : Graphon) (G₁ : SimpleGraph (Fin n₁))
    (G₂ : SimpleGraph (Fin n₂)) {H : SimpleGraph (Fin (n₁ + n₂))} (hH : H ∈ blkFiber G₁ G₂)
    (x : Fin (n₁ + n₂) → I) :
    (∏ p ∈ blkIdx1 n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
      = inducedWeight W G₁ (x ∘ Fin.castAdd n₂) := by
  have hHG : H.comap (Fin.castAdd n₂) = G₁ := ((blkFiber_mem_iff G₁ G₂ H).mp hH).1
  unfold blkIdx1 inducedWeight
  rw [Finset.prod_image (fun a _ b _ heq => blkCastAdd_injective n₁ n₂ heq)]
  apply Finset.prod_congr rfl
  intro p _
  have hadj : (H.comap (Fin.castAdd n₂)).Adj p.1 p.2
      ↔ H.Adj (Fin.castAdd n₂ p.1) (Fin.castAdd n₂ p.2) := SimpleGraph.comap_adj
  rw [hHG] at hadj
  simp only [Prod.map_fst, Prod.map_snd, Function.comp_apply]
  exact adjWeight_congr W hadj.symm _ _

private lemma blkOldPart2_eq {n₁ n₂ : ℕ} (W : Graphon) (G₁ : SimpleGraph (Fin n₁))
    (G₂ : SimpleGraph (Fin n₂)) {H : SimpleGraph (Fin (n₁ + n₂))} (hH : H ∈ blkFiber G₁ G₂)
    (x : Fin (n₁ + n₂) → I) :
    (∏ p ∈ blkIdx2 n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
      = inducedWeight W G₂ (x ∘ Fin.natAdd n₁) := by
  have hHG : H.comap (Fin.natAdd n₁) = G₂ := ((blkFiber_mem_iff G₁ G₂ H).mp hH).2
  unfold blkIdx2 inducedWeight
  rw [Finset.prod_image (fun a _ b _ heq => blkNatAdd_injective n₁ n₂ heq)]
  apply Finset.prod_congr rfl
  intro p _
  have hadj : (H.comap (Fin.natAdd n₁)).Adj p.1 p.2
      ↔ H.Adj (Fin.natAdd n₁ p.1) (Fin.natAdd n₁ p.2) := SimpleGraph.comap_adj
  rw [hHG] at hadj
  simp only [Prod.map_fst, Prod.map_snd, Function.comp_apply]
  exact adjWeight_congr W hadj.symm _ _

private lemma blkGEdges_union_iff {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    {S : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂))} (hS : S ⊆ blkCross n₁ n₂)
    {p : Fin (n₁ + n₂) × Fin (n₁ + n₂)} (hp : p ∈ blkOldIdx n₁ n₂) :
    p ∈ blkG1Edges G₁ ∪ blkG2Edges G₂ ∪ S ↔ p ∈ blkG1Edges G₁ ∪ blkG2Edges G₂ := by
  have hnotS : p ∉ S := fun hmem =>
    Finset.disjoint_left.mp (blkOldIdx_disjoint_cross n₁ n₂) hp (hS hmem)
  rw [Finset.mem_union]
  exact ⟨fun h => h.resolve_right hnotS, Or.inl⟩

private lemma blkG1Edges_iff {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) {p : Fin n₁ × Fin n₁}
    (hp : p ∈ belowDiagPairs n₁) :
    (Fin.castAdd n₂ p.1, Fin.castAdd n₂ p.2) ∈ blkG1Edges (n₂ := n₂) G₁ ↔ G₁.Adj p.1 p.2 := by
  unfold blkG1Edges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqeq : q = p := blkCastAdd_injective n₁ n₂ heq
    rw [hqeq] at hq
    exact (Finset.mem_filter.mp hq).2
  · intro hAdj
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hAdj⟩, rfl⟩

private lemma blkG2Edges_iff {n₁ n₂ : ℕ} (G₂ : SimpleGraph (Fin n₂)) {p : Fin n₂ × Fin n₂}
    (hp : p ∈ belowDiagPairs n₂) :
    (Fin.natAdd n₁ p.1, Fin.natAdd n₁ p.2) ∈ blkG2Edges (n₁ := n₁) G₂ ↔ G₂.Adj p.1 p.2 := by
  unfold blkG2Edges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqeq : q = p := blkNatAdd_injective n₁ n₂ heq
    rw [hqeq] at hq
    exact (Finset.mem_filter.mp hq).2
  · intro hAdj
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hAdj⟩, rfl⟩

private lemma blkG1Edges_sub {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) :
    blkG1Edges (n₂ := n₂) G₁ ⊆ blkIdx1 n₁ n₂ := by
  intro q hq
  unfold blkG1Edges at hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

private lemma blkG2Edges_sub {n₁ n₂ : ℕ} (G₂ : SimpleGraph (Fin n₂)) :
    blkG2Edges (n₁ := n₁) G₂ ⊆ blkIdx2 n₁ n₂ := by
  intro q hq
  unfold blkG2Edges at hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

/-- Reconstruction: for `S` among the cross positions, `graphOfPairs (blkG1Edges ∪ blkG2Edges ∪ S)`
lies in the fibre over `(G₁, G₂)`. -/
private def blkToGraph {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    (S : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂))) : SimpleGraph (Fin (n₁ + n₂)) :=
  graphOfPairs (blkG1Edges G₁ ∪ blkG2Edges G₂ ∪ S)

/-- The cross edge set of a fibre graph. -/
private noncomputable def blkToCross {n₁ n₂ : ℕ} (H : SimpleGraph (Fin (n₁ + n₂))) :
    Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
  (blkCross n₁ n₂).filter (fun p => H.Adj p.1 p.2)

private lemma blkToGraph_mem_fiber {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    {S : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂))} (hS : S ∈ (blkCross n₁ n₂).powerset) :
    blkToGraph G₁ G₂ S ∈ blkFiber G₁ G₂ := by
  have hSsub : S ⊆ blkCross n₁ n₂ := Finset.mem_powerset.mp hS
  rw [blkFiber_mem_iff]
  refine ⟨comap_graphOfPairs_eq (Fin.castAdd n₂)
      (fun {a b} hab => Fin.strictMono_castAdd n₂ hab) G₁ _ (fun p hp => ?_),
    comap_graphOfPairs_eq (Fin.natAdd n₁)
      (fun {a b} hab => Fin.strictMono_natAdd n₁ hab) G₂ _ (fun p hp => ?_)⟩
  · have hq1 : (Fin.castAdd n₂ p.1, Fin.castAdd n₂ p.2) ∈ blkIdx1 n₁ n₂ :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hqNotG2 : (Fin.castAdd n₂ p.1, Fin.castAdd n₂ p.2) ∉ blkG2Edges (n₁ := n₁) G₂ :=
      fun hmem => Finset.disjoint_left.mp (blkIdx1_disjoint_blkIdx2 n₁ n₂) hq1
        (blkG2Edges_sub G₂ hmem)
    rw [blkGEdges_union_iff G₁ G₂ hSsub (Finset.mem_union_left _ hq1), Finset.mem_union,
      blkG1Edges_iff G₁ hp]
    exact ⟨fun h => h.resolve_right hqNotG2, Or.inl⟩
  · have hq2 : (Fin.natAdd n₁ p.1, Fin.natAdd n₁ p.2) ∈ blkIdx2 n₁ n₂ :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hqNotG1 : (Fin.natAdd n₁ p.1, Fin.natAdd n₁ p.2) ∉ blkG1Edges (n₂ := n₂) G₁ :=
      fun hmem => Finset.disjoint_left.mp (blkIdx1_disjoint_blkIdx2 n₁ n₂) (blkG1Edges_sub G₁ hmem)
        hq2
    rw [blkGEdges_union_iff G₁ G₂ hSsub (Finset.mem_union_right _ hq2), Finset.mem_union,
      blkG2Edges_iff G₂ hp]
    constructor
    · rintro (h | h)
      · exact absurd h hqNotG1
      · exact h
    · exact fun h => Or.inr h

private lemma blkGEdges_eq_oldIdx_filter {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁))
    (G₂ : SimpleGraph (Fin n₂)) {H : SimpleGraph (Fin (n₁ + n₂))} (hH : H ∈ blkFiber G₁ G₂) :
    blkG1Edges G₁ ∪ blkG2Edges G₂ = (blkOldIdx n₁ n₂).filter (fun p => H.Adj p.1 p.2) := by
  have hHG1 : H.comap (Fin.castAdd n₂) = G₁ := ((blkFiber_mem_iff G₁ G₂ H).mp hH).1
  have hHG2 : H.comap (Fin.natAdd n₁) = G₂ := ((blkFiber_mem_iff G₁ G₂ H).mp hH).2
  ext q
  unfold blkOldIdx
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (hq | hq)
    · unfold blkG1Edges at hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hadj : (H.comap (Fin.castAdd n₂)).Adj p.1 p.2
          ↔ H.Adj (Fin.castAdd n₂ p.1) (Fin.castAdd n₂ p.2) := SimpleGraph.comap_adj
      rw [hHG1] at hadj
      refine ⟨Or.inl (Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩), ?_⟩
      simp only [Prod.map_fst, Prod.map_snd] at hadj ⊢
      exact hadj.mp (Finset.mem_filter.mp hp).2
    · unfold blkG2Edges at hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hadj : (H.comap (Fin.natAdd n₁)).Adj p.1 p.2
          ↔ H.Adj (Fin.natAdd n₁ p.1) (Fin.natAdd n₁ p.2) := SimpleGraph.comap_adj
      rw [hHG2] at hadj
      refine ⟨Or.inr (Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩), ?_⟩
      simp only [Prod.map_fst, Prod.map_snd] at hadj ⊢
      exact hadj.mp (Finset.mem_filter.mp hp).2
  · rintro ⟨(hq | hq), hHadj⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hadj : (H.comap (Fin.castAdd n₂)).Adj p.1 p.2
          ↔ H.Adj (Fin.castAdd n₂ p.1) (Fin.castAdd n₂ p.2) := SimpleGraph.comap_adj
      rw [hHG1] at hadj
      simp only [Prod.map_fst, Prod.map_snd] at hHadj
      exact Or.inl (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hadj.mpr hHadj⟩, rfl⟩)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hadj : (H.comap (Fin.natAdd n₁)).Adj p.1 p.2
          ↔ H.Adj (Fin.natAdd n₁ p.1) (Fin.natAdd n₁ p.2) := SimpleGraph.comap_adj
      rw [hHG2] at hadj
      simp only [Prod.map_fst, Prod.map_snd] at hHadj
      exact Or.inr (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hadj.mpr hHadj⟩, rfl⟩)

private lemma blkLeft_inv {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    {H : SimpleGraph (Fin (n₁ + n₂))} (hH : H ∈ blkFiber G₁ G₂) :
    blkToGraph G₁ G₂ (blkToCross H) = H := by
  unfold blkToGraph
  have hEq : blkG1Edges G₁ ∪ blkG2Edges G₂ ∪ blkToCross H
      = (belowDiagPairs (n₁ + n₂)).filter (fun p => H.Adj p.1 p.2) := by
    unfold blkToCross
    rw [blkGEdges_eq_oldIdx_filter G₁ G₂ hH, ← Finset.filter_union, blkOldIdx_union_cross]
  rw [hEq, graphOfPairs_filter_eq]

private lemma blkRight_inv {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂))
    {S : Finset (Fin (n₁ + n₂) × Fin (n₁ + n₂))} (hS : S ∈ (blkCross n₁ n₂).powerset) :
    blkToCross (blkToGraph G₁ G₂ S) = S := by
  have hSsub : S ⊆ blkCross n₁ n₂ := Finset.mem_powerset.mp hS
  unfold blkToCross blkToGraph
  apply Finset.ext
  intro p
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hpCross, hpAdj⟩
    have hpBelow : p ∈ belowDiagPairs (n₁ + n₂) := (Finset.mem_sdiff.mp hpCross).1
    have hlt : p.1 < p.2 := mem_belowDiagPairs.mp hpBelow
    rw [graphOfPairs_adj_of_lt hlt, Finset.mem_union] at hpAdj
    rcases hpAdj with hpAdj | hpAdj
    · exfalso
      have hOld : p ∈ blkOldIdx n₁ n₂ := by
        rcases Finset.mem_union.mp hpAdj with h | h
        · exact Finset.mem_union_left _ (blkG1Edges_sub G₁ h)
        · exact Finset.mem_union_right _ (blkG2Edges_sub G₂ h)
      exact Finset.disjoint_left.mp (blkOldIdx_disjoint_cross n₁ n₂) hOld hpCross
    · exact hpAdj
  · intro hpS
    have hpCross := hSsub hpS
    refine ⟨hpCross, ?_⟩
    have hpBelow : p ∈ belowDiagPairs (n₁ + n₂) := (Finset.mem_sdiff.mp hpCross).1
    have hlt : p.1 < p.2 := mem_belowDiagPairs.mp hpBelow
    rw [graphOfPairs_adj_of_lt hlt, Finset.mem_union]
    exact Or.inr hpS

private lemma blkFactor_eq {n₁ n₂ : ℕ} (W : Graphon) (x : Fin (n₁ + n₂) → I)
    (H : SimpleGraph (Fin (n₁ + n₂))) :
    (∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
      = (∏ p ∈ blkToCross H, W.W (x p.1) (x p.2))
        * ∏ p ∈ blkCross n₁ n₂ \ blkToCross H, (1 - W.W (x p.1) (x p.2)) := by
  unfold blkToCross
  have hsplit := Finset.prod_filter_mul_prod_filter_not (blkCross n₁ n₂) (fun p => H.Adj p.1 p.2)
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

private lemma blkFiber_sum_eq_one {n₁ n₂ : ℕ} (W : Graphon) (G₁ : SimpleGraph (Fin n₁))
    (G₂ : SimpleGraph (Fin n₂)) (x : Fin (n₁ + n₂) → I) :
    ∑ H ∈ blkFiber G₁ G₂, ∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) = 1 := by
  have hbij : ∑ H ∈ blkFiber G₁ G₂, ∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2)
      = ∑ S ∈ (blkCross n₁ n₂).powerset,
          (∏ p ∈ S, W.W (x p.1) (x p.2)) * ∏ p ∈ blkCross n₁ n₂ \ S, (1 - W.W (x p.1) (x p.2)) := by
    apply Finset.sum_nbij' blkToCross (blkToGraph G₁ G₂)
    · exact fun H _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    · exact fun S hS => blkToGraph_mem_fiber G₁ G₂ hS
    · exact fun H hH => blkLeft_inv G₁ G₂ hH
    · exact fun S hS => blkRight_inv G₁ G₂ hS
    · exact fun H _ => blkFactor_eq W x H
  rw [hbij, ← Finset.prod_add]
  simp

/-- Marginalisation for the block product: the integral of the product of the two block
weights (each depending only on its own block of coordinates) is the product of the two
induced densities. -/
private lemma blkMarginal {n₁ n₂ : ℕ} (W : Graphon) (G₁ : SimpleGraph (Fin n₁))
    (G₂ : SimpleGraph (Fin n₂)) :
    ∫ x : Fin (n₁ + n₂) → I,
      inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁)
      = graphonFlagDensity W G₁ * graphonFlagDensity W G₂ := by
  classical
  set e : Fin (n₁ + n₂) ≃ Fin n₁ ⊕ Fin n₂ := finSumFinEquiv.symm with he_def
  set Θ := (MeasurableEquiv.piCongrLeft (fun _ : Fin n₁ ⊕ Fin n₂ => I) e).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n₁ ⊕ Fin n₂ => I)) with hΘ_def
  have hmp1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n₁ ⊕ Fin n₂ => I) e)
      volume volume := volume_measurePreserving_piCongrLeft (fun _ => I) e
  have hmp2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n₁ ⊕ Fin n₂ => I))
      volume volume := volume_measurePreserving_sumPiEquivProdPi (fun _ => I)
  have hmpΘ : MeasurePreserving Θ volume volume := by
    rw [hΘ_def]; exact hmp1.trans hmp2
  have hΘeq : ∀ x : Fin (n₁ + n₂) → I, Θ x = (x ∘ Fin.castAdd n₂, x ∘ Fin.natAdd n₁) := by
    intro x
    have hstep : ∀ w : Fin n₁ ⊕ Fin n₂,
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n₁ ⊕ Fin n₂ => I) e) x w = x (finSumFinEquiv w) := by
      intro w
      have hkey := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n₁ ⊕ Fin n₂ => I) e x
          (finSumFinEquiv w)
      simpa [he_def, Equiv.symm_apply_apply] using hkey
    have hΘx : Θ x = (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n₁ ⊕ Fin n₂ => I))
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin n₁ ⊕ Fin n₂ => I) e) x) := by
      rw [hΘ_def]; rfl
    rw [hΘx]
    apply Prod.ext
    · funext i
      show (MeasurableEquiv.piCongrLeft (fun _ : Fin n₁ ⊕ Fin n₂ => I) e) x (Sum.inl i)
          = (x ∘ Fin.castAdd n₂) i
      rw [hstep (Sum.inl i), finSumFinEquiv_apply_left]
      rfl
    · funext j
      show (MeasurableEquiv.piCongrLeft (fun _ : Fin n₁ ⊕ Fin n₂ => I) e) x (Sum.inr j)
          = (x ∘ Fin.natAdd n₁) j
      rw [hstep (Sum.inr j), finSumFinEquiv_apply_right]
      rfl
  unfold graphonFlagDensity
  rw [← integral_prod_mul (inducedWeight W G₁) (inducedWeight W G₂), ← Measure.volume_eq_prod,
    ← hmpΘ.integral_comp'
      (fun z : (Fin n₁ → I) × (Fin n₂ → I) => inducedWeight W G₁ z.1 * inducedWeight W G₂ z.2)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [hΘeq]

/-- **Block product**: the product of the induced densities of `G₁` on `Fin n₁` and `G₂` on
`Fin n₂` equals the total induced density of all graphs on `Fin (n₁ + n₂)` restricting to
`G₁` on the first block (`Fin.castAdd n₂`) and to `G₂` on the second block
(`Fin.natAdd n₁`).

Proof route: pointwise, the weight of `H` on `Fin (n₁+n₂)` factors into block-1 pairs,
block-2 pairs, and cross pairs; over the fibre the cross parts sum to `1`
(`Finset.prod_add` partition of unity again), leaving
`inducedWeight W G₁ (x ∘ castAdd) * inducedWeight W G₂ (x ∘ natAdd)`.  The integral of the
product of the two block marginals splits as the product of integrals via
`volume_measurePreserving_sumPiEquivProdPi` (through the label equivalence
`finSumFinEquiv : Fin n₁ ⊕ Fin n₂ ≃ Fin (n₁+n₂)` and
`volume_measurePreserving_piCongrLeft`) followed by `integral_prod` (Fubini for the
product of bounded measurable functions of the two coordinates). -/
theorem graphonFlagDensity_block_mul (W : Graphon) {n₁ n₂ : ℕ}
    (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    graphonFlagDensity W G₁ * graphonFlagDensity W G₂
      = ∑ H ∈ Finset.univ.filter
          (fun H : SimpleGraph (Fin (n₁ + n₂)) =>
            H.comap (Fin.castAdd n₂) = G₁ ∧ H.comap (Fin.natAdd n₁) = G₂),
          graphonFlagDensity W H := by
  show graphonFlagDensity W G₁ * graphonFlagDensity W G₂
    = ∑ H ∈ blkFiber G₁ G₂, graphonFlagDensity W H
  rw [← blkMarginal W G₁ G₂]
  have hpointwise : ∀ x : Fin (n₁ + n₂) → I,
      inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁)
        = ∑ H ∈ blkFiber G₁ G₂, inducedWeight W H x := by
    intro x
    calc inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁)
        = (inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁)) * 1 := by
          ring
      _ = (inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁))
            * (∑ H ∈ blkFiber G₁ G₂,
                ∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2)) := by
          rw [blkFiber_sum_eq_one W G₁ G₂ x]
      _ = ∑ H ∈ blkFiber G₁ G₂,
            (inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁))
              * ∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
          rw [Finset.mul_sum]
      _ = ∑ H ∈ blkFiber G₁ G₂,
            ((∏ p ∈ blkIdx1 n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
                * ∏ p ∈ blkIdx2 n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2))
              * ∏ p ∈ blkCross n₁ n₂, adjWeight W (H.Adj p.1 p.2) (x p.1) (x p.2) := by
          apply Finset.sum_congr rfl
          intro H hH
          rw [blkOldPart1_eq W G₁ G₂ hH x, blkOldPart2_eq W G₁ G₂ hH x]
      _ = ∑ H ∈ blkFiber G₁ G₂, inducedWeight W H x := by
          apply Finset.sum_congr rfl
          intro H _
          rw [blkInducedWeight_split n₁ n₂ W H x]
  calc ∫ x : Fin (n₁ + n₂) → I,
        inducedWeight W G₁ (x ∘ Fin.castAdd n₂) * inducedWeight W G₂ (x ∘ Fin.natAdd n₁)
      = ∫ x : Fin (n₁ + n₂) → I, ∑ H ∈ blkFiber G₁ G₂, inducedWeight W H x :=
        integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ∑ H ∈ blkFiber G₁ G₂, ∫ x : Fin (n₁ + n₂) → I, inducedWeight W H x :=
        integral_finset_sum _ (fun H _ => integrable_inducedWeight W H)
    _ = ∑ H ∈ blkFiber G₁ G₂, graphonFlagDensity W H := rfl

/-! ## The edge computation -/

/-- The induced density of the single edge `⊤` on `Fin 2` is the edge density of the graphon:
`∫∫ W = p`.  (Identify `Fin 2 → I` with `I × I` via the volume-preserving
`MeasurableEquiv.piFinTwoEquiv`, then compare with `Graphon.edgeDensity_eq_integral_prod`.) -/
theorem graphonFlagDensity_top_two (W : Graphon) :
    graphonFlagDensity W (⊤ : SimpleGraph (Fin 2)) = W.edgeDensity := by
  have hpairs : belowDiagPairs 2 = {((0 : Fin 2), (1 : Fin 2))} := by
    unfold belowDiagPairs
    ext p
    fin_cases p <;> simp
  have hw : ∀ x : Fin 2 → I, inducedWeight W (⊤ : SimpleGraph (Fin 2)) x = W.W (x 0) (x 1) := by
    intro x
    unfold inducedWeight
    rw [hpairs, Finset.prod_singleton]
    have : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by decide
    unfold adjWeight
    rw [if_pos this]
  have hcomp : ∫ x : Fin 2 → I, W.W (MeasurableEquiv.finTwoArrow x).1 (MeasurableEquiv.finTwoArrow x).2
      = ∫ z : I × I, W.W z.1 z.2 :=
    (measurePreserving_finTwoArrow (volume : Measure I)).integral_comp'
      (fun z : I × I => W.W z.1 z.2)
  calc graphonFlagDensity W (⊤ : SimpleGraph (Fin 2))
      = ∫ x : Fin 2 → I, W.W (x 0) (x 1) := by
        unfold graphonFlagDensity
        exact integral_congr_ae (Filter.Eventually.of_forall hw)
    _ = ∫ x : Fin 2 → I, W.W (MeasurableEquiv.finTwoArrow x).1 (MeasurableEquiv.finTwoArrow x).2 := by
        rfl
    _ = ∫ z : I × I, W.W z.1 z.2 := hcomp
    _ = W.edgeDensity := (Graphon.edgeDensity_eq_integral_prod W).symm

end FlagAlgebras.MetaTheory
