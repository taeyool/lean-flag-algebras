import LeanFlagAlgebras.MetaTheory.StarWitness
import LeanFlagAlgebras.MetaTheory.ConstrainedRep
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Chebyshev

/-! # The `C₄`-free class is a degeneracy counterexample (paper §9.1)

The `C₄`-free graphs are the original obstruction of §9.1: hereditary, *not* clone-closed (the
independent blow-up of `K₂` into two clone classes of size `2` is `K_{2,2} = C₄`), yet they fail
root-plantability at the one-vertex type because they are **edge-degenerate** — the classical
Kővári–Sós–Turán bound, here in its elementary `C₄` form.

* `c4FreeClass : HeredClass` — `Mem G := (cycleGraph 4).Free G` (no `C₄` subgraph).
* `c4free_card_edges_sq_le` — the counting heart: a `C₄`-free graph on `N` vertices has any two
  distinct vertices sharing at most one common neighbour, so `(2·e(G))² ≤ 2·N³`.
* `lem:c4-edge-zero` (`c4FreeClass_edgeDegenerate`) — every constrained unlabelled limit has edge
  density `0`: the edge densities of the representing `C₄`-free graphs are `≤ √(2N)/(N-1) → 0`.
* `cor:c4-counterexample` (`c4free_not_rootPlantable`) — `C₄`-free is not root-plantable at the
  one-vertex type (edge-degenerate + contains all stars ⟹ `degenerate_not_rootPlantable`).
-/

open SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The `C₄`-free hereditary class -/

/-- The 4-cycle `C₄ = cycleGraph 4` on `Fin 4`. -/
abbrev C4g : SimpleGraph (Fin 4) := cycleGraph 4

/-- **The `C₄`-free hereditary class.**  `G` is in the class iff it contains no copy of `C₄` (not
necessarily induced).  Heredity mirrors `c5FreeClass`. -/
def c4FreeClass : HeredClass where
  Mem {_V} _ _ G := C4g.Free G
  comap {_V _W} _ _ _ _ {_G} {_H} e hG := fun hc4 => hG (hc4.trans ⟨e.toCopy⟩)

/-- **A square gives a `C₄`.**  Four distinct vertices with the four cyclic edges `x–a–y–b–x` form a
copy of `cycleGraph 4`.  (Analogue of `c5_copy_of_pentagon`.) -/
lemma c4_copy_of_square {V : Type} (G : SimpleGraph V) (x a y b : V)
    (e_xa : G.Adj x a) (e_ay : G.Adj a y) (e_yb : G.Adj y b) (e_bx : G.Adj b x)
    (h_xa : x ≠ a) (h_ay : a ≠ y) (h_yb : y ≠ b) (h_bx : b ≠ x)
    (h_xy : x ≠ y) (h_ab : a ≠ b) :
    C4g ⊑ G := by
  refine ⟨Hom.toCopy ⟨![x, a, y, b], ?_⟩ ?_⟩
  · intro i j hij
    rw [show C4g = cycleGraph 4 from rfl, cycleGraph_adj] at hij
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hij; decide)
        | exact e_xa | exact e_xa.symm | exact e_ay | exact e_ay.symm
        | exact e_yb | exact e_yb.symm | exact e_bx | exact e_bx.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exact absurd hij h_xa) | (exact absurd hij.symm h_xa)
        | (exact absurd hij h_ay) | (exact absurd hij.symm h_ay)
        | (exact absurd hij h_yb) | (exact absurd hij.symm h_yb)
        | (exact absurd hij h_bx) | (exact absurd hij.symm h_bx)
        | (exact absurd hij h_xy) | (exact absurd hij.symm h_xy)
        | (exact absurd hij h_ab) | (exact absurd hij.symm h_ab)

/-! ## The counting bound (elementary Kővári–Sós–Turán for `C₄`) -/

/-- In a `C₄`-free graph two distinct vertices have at most one common neighbour. -/
lemma c4free_common_neighbors_le_one {N : ℕ} (G : SimpleGraph (Fin N)) (hG : C4g.Free G)
    {x y : Fin N} (hxy : x ≠ y) :
    (G.commonNeighbors x y).toFinset.card ≤ 1 := by
  by_contra hcard
  push_neg at hcard
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcard
  rw [Set.mem_toFinset, mem_commonNeighbors] at ha hb
  obtain ⟨hxa, hya⟩ := ha
  obtain ⟨hxb, hyb⟩ := hb
  exact hG (c4_copy_of_square G x a y b hxa hya.symm hyb hxb.symm
    hxa.ne hya.ne.symm hyb.ne hxb.ne.symm hxy hab)

/-- **Cherry double-count.**  Each vertex `v` carries `(neighborFinset v).offDiag.card` ordered
pairs of distinct neighbours, and summing over `v` equals summing the common-neighbour counts over
the ordered distinct pairs `(x,y)` (each vertex of an ordered cherry `(x,v,y)` regrouped by its
endpoints). -/
private lemma cherry_count_eq {N : ℕ} (G : SimpleGraph (Fin N)) :
    ∑ v : Fin N, (G.neighborFinset v).offDiag.card
      = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
          (G.commonNeighbors p.1 p.2).toFinset.card := by
  -- Rewrite the left summand as a filter over `univ.offDiag`, then swap the order of summation.
  have hleft : ∀ v : Fin N, (G.neighborFinset v).offDiag.card
      = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
          (if G.Adj v p.1 ∧ G.Adj v p.2 then 1 else 0) := by
    intro v
    rw [show (G.neighborFinset v).offDiag
        = ((Finset.univ : Finset (Fin N)).offDiag).filter
            (fun p => G.Adj v p.1 ∧ G.Adj v p.2) from ?_]
    · rw [Finset.card_filter]
    · ext p
      simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      tauto
  simp_rw [hleft]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  ext v
  simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [G.adj_comm v p.1, G.adj_comm v p.2]

/-- **The counting heart.**  A `C₄`-free graph on `N` vertices has `(∑ deg)² ≤ 2 N³`, equivalently
`(2·e(G))² ≤ 2 N³`.  Double-counting cherries `∑ deg·(deg−1) = ∑_{x≠y} |common nbrs| ≤ N(N−1)` then
Cauchy–Schwarz `(∑ deg)² ≤ N·∑ deg²`. -/
theorem c4free_card_edges_sq_le {N : ℕ} (G : SimpleGraph (Fin N)) (hG : C4g.Free G) :
    (2 * G.edgeFinset.card) ^ 2 ≤ 2 * N ^ 3 := by
  classical
  set S : ℕ := ∑ v : Fin N, G.degree v with hSdef
  -- `S = 2 * e(G)`.
  have hS_edges : S = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  -- Each off-diagonal neighbour count is `deg*deg - deg`.
  have hoff : ∀ v : Fin N, (G.neighborFinset v).offDiag.card
      = G.degree v * G.degree v - G.degree v := by
    intro v
    rw [Finset.offDiag_card, SimpleGraph.card_neighborFinset_eq_degree]
  -- (a) The cherry count is at most `N*(N-1)`.
  have hcherry : ∑ v : Fin N, (G.neighborFinset v).offDiag.card ≤ N * (N - 1) := by
    rw [cherry_count_eq]
    calc ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
            (G.commonNeighbors p.1 p.2).toFinset.card
        ≤ ∑ _p ∈ (Finset.univ : Finset (Fin N)).offDiag, 1 := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          rw [Finset.mem_offDiag] at hp
          exact c4free_common_neighbors_le_one G hG hp.2.2
      _ = (Finset.univ : Finset (Fin N)).offDiag.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = N * (N - 1) := by
          rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]
  -- (b) `∑ deg² ≤ N*(N-1) + S`.
  have hsumsq : ∑ v : Fin N, (G.degree v) ^ 2 ≤ N * (N - 1) + S := by
    have hpoint : ∀ v : Fin N, (G.degree v) ^ 2
        = (G.neighborFinset v).offDiag.card + G.degree v := by
      intro v
      rw [hoff v, sq]
      have hle : G.degree v ≤ G.degree v * G.degree v := by
        nlinarith [Nat.zero_le (G.degree v)]
      omega
    calc ∑ v : Fin N, (G.degree v) ^ 2
        = ∑ v : Fin N, ((G.neighborFinset v).offDiag.card + G.degree v) := by
          exact Finset.sum_congr rfl (fun v _ => hpoint v)
      _ = (∑ v : Fin N, (G.neighborFinset v).offDiag.card) + S := by
          rw [Finset.sum_add_distrib]
      _ ≤ N * (N - 1) + S := by exact Nat.add_le_add_right hcherry S
  -- (c) Cauchy–Schwarz: `S² ≤ N * ∑ deg²`.
  have hCS : S ^ 2 ≤ N * ∑ v : Fin N, (G.degree v) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun v => G.degree v)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  -- `S ≤ N * N`: each degree is at most `N`.
  have hdeg_le : ∀ v : Fin N, G.degree v ≤ N := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    calc (G.neighborFinset v).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = N := by rw [Finset.card_univ, Fintype.card_fin]
  have hS_le : S ≤ N * N := by
    calc S = ∑ v : Fin N, G.degree v := hSdef
      _ ≤ ∑ _v : Fin N, N := Finset.sum_le_sum (fun v _ => hdeg_le v)
      _ = N * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- Combine: `S² ≤ N*(N*(N-1)+S) ≤ N³ + N*S ≤ 2N³`.
  rw [← hS_edges]
  have hkey : S ^ 2 ≤ N * (N * (N - 1) + S) :=
    le_trans hCS (Nat.mul_le_mul_left N hsumsq)
  have hbound1 : N * (N * (N - 1)) ≤ N ^ 3 := by
    have : N * (N - 1) ≤ N * N := Nat.mul_le_mul_left N (Nat.sub_le N 1)
    calc N * (N * (N - 1)) ≤ N * (N * N) := Nat.mul_le_mul_left N this
      _ = N ^ 3 := by ring
  have hbound2 : N * S ≤ N ^ 3 := by
    calc N * S ≤ N * (N * N) := Nat.mul_le_mul_left N hS_le
      _ = N ^ 3 := by ring
  have hexpand : N * (N * (N - 1) + S) = N * (N * (N - 1)) + N * S := by ring
  rw [hexpand] at hkey
  calc S ^ 2 ≤ N * (N * (N - 1)) + N * S := hkey
    _ ≤ N ^ 3 + N ^ 3 := Nat.add_le_add hbound1 hbound2
    _ = 2 * N ^ 3 := by ring

/-! ## Edge density of a concrete graph -/

/-- The unlabelled edge as a `∅ₜ`-flag (the single edge `⊤` on `Fin 2`, the unlabelling of
`edgeLabeled`). -/
noncomputable def unlabelledEdgeFlag : Flag ∅ₜ (Fin 2) := graphFlag edgeGraph

/-- For the empty type `∅ₜ` a labelled-graph isomorphism is the same datum as a plain graph
isomorphism: the `type_preserve` law is vacuous (`Fin 0` is empty). -/
private lemma emptyf_iso_iff {V W : Type} (A : LabeledGraph ∅ₜ V) (B : LabeledGraph ∅ₜ W) :
    Nonempty (A ≃f B) ↔ Nonempty (A.graph ≃g B.graph) := by
  constructor
  · rintro ⟨f⟩; exact ⟨f.graph_iso⟩
  · rintro ⟨g⟩; exact ⟨⟨g, funext (fun t => (IsEmpty.false t).elim)⟩⟩

/-- The subgraph of `G` induced on a vertex subset `S` is isomorphic to the single edge `⊤` on
`Fin 2` exactly when `S` is a pair `{u, w}` of distinct adjacent vertices. -/
private lemma induced_iso_top_iff {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    Nonempty (((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe ≃g (⊤ : SimpleGraph (Fin 2)))
      ↔ ∃ u w, u ≠ w ∧ G.Adj u w ∧ S = {u, w} := by
  constructor
  · rintro ⟨f⟩
    have hcard2 : Fintype.card (↑((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).verts) = 2 := by
      rw [f.card_eq]; simp
    rw [Subgraph.induce_verts] at hcard2
    have hScard : S.card = 2 := by
      rw [← hcard2, ← Set.toFinset_card]; congr 1; ext x; simp
    obtain ⟨u, w, huw, hSeq⟩ := Finset.card_eq_two.mp hScard
    refine ⟨u, w, huw, ?_, hSeq⟩
    have huS : u ∈ (↑S : Set (Fin N)) := by rw [hSeq]; simp
    have hwS : w ∈ (↑S : Set (Fin N)) := by rw [hSeq]; simp
    have key : ((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe.Adj ⟨u, huS⟩ ⟨w, hwS⟩ := by
      rw [← f.map_adj_iff]; simp only [top_adj]; intro h
      apply huw; have := f.injective h; exact congrArg Subtype.val this
    rw [Subgraph.coe_adj] at key
    simp only [Subgraph.induce_adj, Subgraph.top_adj] at key
    exact key.2.2
  · rintro ⟨u, w, huw, hadj, rfl⟩
    have hcoe_top : ((⊤ : G.Subgraph).induce (↑({u, w} : Finset (Fin N)))).coe = (⊤ : SimpleGraph _) := by
      ext a b
      simp only [Subgraph.coe_adj, Subgraph.induce_adj, Subgraph.top_adj, top_adj]
      constructor
      · rintro ⟨_, _, h⟩; intro hab; exact G.ne_of_adj h (congrArg Subtype.val hab)
      · intro hab
        have ha := a.2; have hb := b.2
        simp only [Finset.coe_insert, Finset.coe_singleton] at ha hb
        have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
        refine ⟨a.2, b.2, ?_⟩
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact absurd (by rw [ha, hb]) hab'
        · exact hadj
        · exact hadj.symm
        · exact absurd (by rw [ha, hb]) hab'
    have hcard : Fintype.card (↑(↑({u, w} : Finset (Fin N)) : Set (Fin N))) = 2 := by
      have h1 : Fintype.card (↑(↑({u, w} : Finset (Fin N)) : Set (Fin N)))
          = ({u, w} : Finset (Fin N)).card := by
        rw [← Set.toFinset_card]; congr 1; ext x; simp
      rw [h1, Finset.card_eq_two]; exact ⟨u, w, huw, rfl⟩
    let e : (↑(↑({u, w} : Finset (Fin N)) : Set (Fin N))) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
    rw [hcoe_top]
    exact ⟨Iso.completeGraph e⟩

/-- The `2`-vertex subsets inducing a single edge are in bijection with the edges of `G` (via
`S ↦ s(u, w)`, inverse `e ↦ e.toFinset`), so they are equinumerous with `G.edgeFinset`. -/
private lemma count_edges {N : ℕ} (G : SimpleGraph (Fin N)) :
    (Finset.univ.filter
        (fun S : Finset (Fin N) => ∃ u w, u ≠ w ∧ G.Adj u w ∧ S = {u, w})).card
      = G.edgeFinset.card := by
  have himg : Finset.univ.filter
        (fun S : Finset (Fin N) => ∃ u w, u ≠ w ∧ G.Adj u w ∧ S = {u, w})
      = G.edgeFinset.image Sym2.toFinset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, mem_edgeFinset]
    constructor
    · rintro ⟨u, w, huw, hadj, rfl⟩
      exact ⟨s(u, w), by rw [mem_edgeSet]; exact hadj, by rw [Sym2.toFinset_mk_eq]⟩
    · rintro ⟨e, he, rfl⟩
      induction e with
      | _ u w =>
        rw [mem_edgeSet] at he
        exact ⟨u, w, G.ne_of_adj he, he, by rw [Sym2.toFinset_mk_eq]⟩
  rw [himg, Finset.card_image_of_injOn]
  intro e1 he1 e2 he2 heq
  rw [Finset.mem_coe, mem_edgeFinset] at he1 he2
  induction e1 with
  | _ a b =>
  induction e2 with
  | _ c d =>
    rw [mem_edgeSet] at he1 he2
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at heq
    have ha : a ∈ ({c, d} : Finset (Fin N)) := heq ▸ (by simp : a ∈ ({a, b} : Finset (Fin N)))
    have hb : b ∈ ({c, d} : Finset (Fin N)) := heq ▸ (by simp : b ∈ ({a, b} : Finset (Fin N)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have hab := G.ne_of_adj he1
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · rw [Sym2.eq_swap]
    · exact absurd rfl hab

/-- The unlabelled-edge density of a finite graph is `e(G)/C(N,2)`. -/
theorem flagDensity_unlabelledEdge_eq {N : ℕ} (G : SimpleGraph (Fin N)) :
    flagDensity₁ unlabelledEdgeFlag (graphFlag G) = (G.edgeFinset.card : ℚ) / (N.choose 2) := by
  unfold unlabelledEdgeFlag graphFlag edgeGraph
  rw [flagDensity₁_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero]
  congr 1
  norm_cast
  rw [← count_edges G]
  congr 1
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨_, hiso⟩
    rw [emptyf_iso_iff] at hiso
    exact (induced_iso_top_iff G S).mp hiso
  · intro hex
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [LabeledGraph.type_verts, Set.image_univ, Set.mem_range] at hx
      obtain ⟨t, _⟩ := hx; exact (IsEmpty.false t).elim
    · rw [emptyf_iso_iff]
      exact (induced_iso_top_iff G S).mpr hex

/-! ## `lem:c4-edge-zero`: the class is edge-degenerate -/

/-- The square of the unlabelled-edge density `e(G)/C(N,2)` is bounded by `2N/(N-1)²` once the
counting heart `(2·e(G))² ≤ 2N³` is available (`N ≥ 2`).  Shared analytic helper, reused by the
complement (dense) obstruction in `DenseObstruction`. -/
lemma edgeDensity_sq_bound (m N : ℕ) (hN : 2 ≤ N) (hsq : (2 * m) ^ 2 ≤ 2 * N ^ 3) :
    ((m : ℝ) / (N.choose 2)) ^ 2 ≤ 2 * (N : ℝ) / ((N : ℝ) - 1) ^ 2 := by
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hchoose : (N.choose 2 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := Nat.cast_choose_two (K := ℝ) N
  rw [hchoose]
  have hsqR : (2 * (m : ℝ)) ^ 2 ≤ 2 * (N : ℝ) ^ 3 := by exact_mod_cast hsq
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsqR, hN1pos.le, sq_nonneg ((m : ℝ)), mul_pos hNpos hN1pos]

/-- The upper bound `2N/(N-1)² → 0` as `N → ∞` (squeezed by `8/N`).  Shared analytic helper, reused
by the complement (dense) obstruction in `DenseObstruction`. -/
lemma edgeDensity_bound_tendsto_zero :
    Tendsto (fun N : ℕ => (2 * (N : ℝ)) / ((N : ℝ) - 1) ^ 2) atTop (𝓝 0) := by
  have hub : Tendsto (fun N : ℕ => (8 : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)
  apply squeeze_zero' (g := fun N : ℕ => (8 : ℝ) / (N : ℝ)) ?_ ?_ hub
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  · filter_upwards [eventually_gt_atTop 2] with N hN
    have hN2 : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    rw [div_le_div_iff₀ (by positivity) hNpos]
    nlinarith [sq_nonneg ((N : ℝ) - 2)]

/-- **`lem:c4-edge-zero`.**  `C₄`-free is edge-degenerate: every constrained unlabelled limit
`φ₀ ∈ Q₀` has `φ₀(ρ) = 0`. -/
theorem c4FreeClass_edgeDegenerate : EdgeDegenerate c4FreeClass := by
  intro φ₀ hφ₀
  -- Reduce `φ₀ ρ` to the unlabelled-edge density via `downward_basisVector`.
  have hedgeunlabel : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, unlabelledEdgeFlag⟩ := rfl
  have hρ : φ₀ ρ
      = (downwardNormalizingFactor edgeFF.2 : ℝ) * φ₀.coe ⟨2, unlabelledEdgeFlag⟩ := by
    show φ₀ (downward e) = _
    rw [e, downward_basisVector, PositiveHom.map_smul, hedgeunlabel, ← PositiveHom.coe_flag]
  -- It suffices to show the unlabelled-edge density coefficient is zero.
  suffices h : φ₀.coe ⟨2, unlabelledEdgeFlag⟩ = 0 by rw [hρ, h, mul_zero]
  -- The forbidden-flag hypothesis from membership in `Q₀`.
  set forb0 := (c4FreeClass.constraintOf vtype).forb0 with hforb0def
  have hforb : ∀ F : FinFlag ∅ₜ, forb0 F → φ₀.coe F = 0 := by
    intro F hF
    have hmem := (mem_Qσ_iff forb0 (posHomPoint φ₀)).mp hφ₀ F hF
    rw [posHomPoint_val_apply] at hmem
    rw [PositiveHom.coe_flag]
    exact hmem
  -- Constrained flag sequence representing `φ₀`.
  obtain ⟨s, hconv, hff⟩ := exists_constrained_flagSeq_limit φ₀ forb0 hforb
  rw [flagSeq_convergesTo_iff] at hconv
  obtain ⟨hinc, hconvF⟩ := hconv
  have hlim := hconvF ⟨2, unlabelledEdgeFlag⟩
  set L : ℝ := φ₀.coe ⟨2, unlabelledEdgeFlag⟩ with hLdef
  -- Each component's unlabelled-edge density is `e(G_t)/C(N_t,2)`.
  have hdensity : ∀ t, flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩
      = ((((s t).2.out.graph).edgeFinset.card : ℚ) / ((s t).1).choose 2 : ℝ) := by
    intro t
    show (flagDensity₁ unlabelledEdgeFlag (s t).2 : ℝ) = _
    have hgf : (s t).2 = graphFlag ((s t).2.out.graph) := by
      conv_lhs => rw [← Quotient.out_eq (s t).2]
      show (⟦(s t).2.out⟧ : Flag ∅ₜ _) = ⟦_⟧
      apply Quotient.sound
      refine ⟨{ graph_iso := SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
      funext z; exact Fin.elim0 z
    have hval : flagDensity₁ unlabelledEdgeFlag (s t).2
        = (((s t).2.out.graph).edgeFinset.card : ℚ) / ((s t).1).choose 2 := by
      conv_lhs => rw [hgf]
      exact flagDensity_unlabelledEdge_eq ((s t).2.out.graph)
    rw [hval]; push_cast; ring
  -- Each representing graph is `C₄`-free.
  have hfree : ∀ t, C4g.Free ((s t).2.out.graph) := by
    intro t
    apply HeredClass.mem_of_forbiddenFree c4FreeClass ((s t).2.out)
    intro F hForb
    have hForb0 : forb0 F := by
      show ¬ c4FreeClass.underlyingMem F.2
      have hfb : ¬ c4FreeClass.underlyingMem (unlabel F.2) := hForb
      rwa [unlabel_emptyType] at hfb
    have hzero := hff t F hForb0
    rwa [← Quotient.out_eq (s t).2] at hzero
  -- Squeeze the squared density between `0` and `2N_t/(N_t-1)² → 0`.
  have hbound : ∀ t, 2 ≤ (s t).1 →
      (flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩) ^ 2
        ≤ 2 * ((s t).1 : ℝ) / (((s t).1 : ℝ) - 1) ^ 2 := by
    intro t ht
    rw [hdensity t]
    exact edgeDensity_sq_bound _ _ ht (c4free_card_edges_sq_le _ (hfree t))
  have hNtop : Tendsto (fun t => ((s t).1 : ℕ)) atTop atTop :=
    hinc.tendsto_atTop
  have hub : Tendsto (fun t => 2 * ((s t).1 : ℝ) / (((s t).1 : ℝ) - 1) ^ 2)
      atTop (𝓝 0) := edgeDensity_bound_tendsto_zero.comp hNtop
  have hsq0 : Tendsto (fun t => (flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t => 2 * ((s t).1 : ℝ) / (((s t).1 : ℝ) - 1) ^ 2) ?_ ?_ hub
    · filter_upwards with t using sq_nonneg _
    · obtain ⟨T, hT⟩ := hinc.eventually_ge 2
      filter_upwards [eventually_ge_atTop T] with t ht
      exact hbound t (hT t ht)
  have hsqL : Tendsto (fun t => (flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩) ^ 2)
      atTop (𝓝 (L ^ 2)) := hlim.pow 2
  -- Uniqueness of limits forces `L² = 0`, hence `L = 0`.
  have hL2 : L ^ 2 = 0 := tendsto_nhds_unique hsqL hsq0
  exact pow_eq_zero_iff (by norm_num) |>.mp hL2

/-! ## Stars are `C₄`-free -/

/-- Every star is `C₄`-free (it is a tree, hence acyclic). -/
theorem starLabeled_c4free (n : ℕ) : c4FreeClass.Mem (starLabeled n).graph := by
  show C4g.Free (starLabeled n).graph
  rintro ⟨c⟩
  -- The four cycle vertices, distinct via injectivity of the copy.
  set w : Fin 4 → Fin (n + 1) := fun i => c.toHom i with hw
  have hinj : Function.Injective w := c.injective'
  -- Each cyclic edge of `C₄` maps to a star edge; the star adjacency says one endpoint is `0`.
  have hstar : ∀ i j : Fin 4, C4g.Adj i j →
      (w i = 0 ∧ w j ≠ 0) ∨ (w i ≠ 0 ∧ w j = 0) := by
    intro i j hij
    exact c.toHom.map_rel hij
  -- The four cyclic adjacencies of `C₄ = cycleGraph 4`.
  have e01 : C4g.Adj 0 1 := by rw [show C4g = cycleGraph 4 from rfl, cycleGraph_adj]; decide
  have e12 : C4g.Adj 1 2 := by rw [show C4g = cycleGraph 4 from rfl, cycleGraph_adj]; decide
  have e23 : C4g.Adj 2 3 := by rw [show C4g = cycleGraph 4 from rfl, cycleGraph_adj]; decide
  have e30 : C4g.Adj 3 0 := by rw [show C4g = cycleGraph 4 from rfl, cycleGraph_adj]; decide
  -- Each cyclic edge contains the star centre `0` as one of its endpoints.
  have c01 : w 0 = 0 ∨ w 1 = 0 := (hstar 0 1 e01).imp (·.1) (·.2)
  have c23 : w 2 = 0 ∨ w 3 = 0 := (hstar 2 3 e23).imp (·.1) (·.2)
  -- The vertex `{0,1}`-endpoint at the centre and the `{2,3}`-endpoint at the centre are equal,
  -- but their preimages are distinct (no shared index), contradicting injectivity.
  rcases c01 with h0 | h1 <;> rcases c23 with h2 | h3
  · exact absurd (hinj (h0.trans h2.symm)) (by decide)
  · exact absurd (hinj (h0.trans h3.symm)) (by decide)
  · exact absurd (hinj (h1.trans h2.symm)) (by decide)
  · exact absurd (hinj (h1.trans h3.symm)) (by decide)

/-! ## `cor:c4-counterexample` -/

/-- **`cor:c4-counterexample`.**  The `C₄`-free class is not root-plantable at the one-vertex type:
the element `-e` is non-negative almost surely under every admissible one-root random extension, but
is negative at some point of `Q_vtype`. -/
theorem c4free_not_rootPlantable :
    ¬ RootPlantable (c4FreeClass.constraintOf vtype) := by
  refine degenerate_not_rootPlantable c4FreeClass c4FreeClass_edgeDegenerate ?_
  intro N
  exact ⟨N, le_rfl, starLabeled_c4free N⟩

end FlagAlgebras.MetaTheory
