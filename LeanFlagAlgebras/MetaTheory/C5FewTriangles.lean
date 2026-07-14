import LeanFlagAlgebras.MetaTheory.C5Free
import LeanFlagAlgebras.MetaTheory.ConstrainedRep
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Few triangles in `C₅`-free graphs (paper §9.5, `lem:c5-few-triangles`)

The `C₅`-free edge-type obstruction (`thm:c5-edge-not-root-plantable`) rests on the fact that
`C₅`-free graphs have *few triangles*: the common-neighbour (triangle) flag over the two-root edge
type is pinned to `0` under random edge-rooting because the unlabelled triangle density vanishes in
every `C₅`-free limit.

This module proves the combinatorial heart:

* `unlabelledTriangleFlag : Flag ∅ₜ (Fin 3)` — the unlabelled triangle `K₃`, and
  `flagDensity_unlabelledTriangle_eq` — its density in a finite graph is `T(G)/C(N,3)` where
  `T(G) = #(G.cliqueFinset 3)`.
* `c5free_three_mul_triangle_le` (`lem:c5-few-triangles`) — `3·T(G) ≤ 2·e(G)` for `C₅`-free `G`,
  via `3·T(G) = ∑_v e(G[N(v)]) ≤ ∑_v deg(v) = 2·e(G)` (each triangle counted at its three vertices;
  `e(G[N(v)]) ≤ |N(v)|` is `lem:c5-nbhd`).
* `c5FreeClass_triangleDensity_zero` — every constrained unlabelled limit of the `C₅`-free class has
  triangle density `0` (the squeeze `T(G)/C(N,3) ≤ (2/3)·N(N-1)/C(N,3) → 0`), mirroring
  `c4FreeClass_edgeDegenerate`.
-/

open SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The unlabelled triangle flag and its density -/

/-- The unlabelled triangle `K₃ = (⊤ : SimpleGraph (Fin 3))` as a `∅ₜ`-flag. -/
noncomputable def unlabelledTriangleFlag : Flag ∅ₜ (Fin 3) := graphFlag (⊤ : SimpleGraph (Fin 3))

/-- A `3`-subset `S` of `G` induces the complete graph `K₃` exactly when `S` is a triangle of `G`
(`G.IsNClique 3 S`). -/
theorem induced_iso_top3_iff {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    Nonempty (((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe ≃g (⊤ : SimpleGraph (Fin 3)))
      ↔ G.IsNClique 3 S := by
  constructor
  · rintro ⟨f⟩
    have hcard3 : Fintype.card (↑((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).verts) = 3 := by
      rw [f.card_eq]; simp
    rw [Subgraph.induce_verts] at hcard3
    have hScard : S.card = 3 := by
      rw [← hcard3, ← Set.toFinset_card]; congr 1; ext x; simp
    refine ⟨?_, hScard⟩
    intro u huS w hwS huw
    have key : ((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe.Adj ⟨u, huS⟩ ⟨w, hwS⟩ := by
      rw [← f.map_adj_iff]; simp only [top_adj]; intro h
      apply huw; have := f.injective h; exact congrArg Subtype.val this
    rw [Subgraph.coe_adj] at key
    simp only [Subgraph.induce_adj, Subgraph.top_adj] at key
    exact key.2.2
  · intro hS
    obtain ⟨hclique, hScard⟩ := hS
    have hcoe_top : ((⊤ : G.Subgraph).induce (↑S : Set (Fin N))).coe = (⊤ : SimpleGraph _) := by
      ext a b
      simp only [Subgraph.coe_adj, Subgraph.induce_adj, Subgraph.top_adj, top_adj]
      constructor
      · rintro ⟨_, _, h⟩; intro hab; exact G.ne_of_adj h (congrArg Subtype.val hab)
      · intro hab
        have hab' : (a : Fin N) ≠ (b : Fin N) := fun h => hab (Subtype.ext h)
        exact ⟨a.2, b.2, hclique a.2 b.2 hab'⟩
    have hcard : Fintype.card (↑(↑S : Set (Fin N))) = 3 := by
      have h1 : Fintype.card (↑(↑S : Set (Fin N))) = S.card := by
        rw [← Set.toFinset_card]; congr 1; ext x; simp
      rw [h1, hScard]
    let e : (↑(↑S : Set (Fin N))) ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
    rw [hcoe_top]
    exact ⟨Iso.completeGraph e⟩

/-- For the empty type `∅ₜ` a labelled-graph isomorphism is the same datum as a plain graph
isomorphism: the `type_preserve` law is vacuous (`Fin 0` is empty). -/
private lemma emptyf_iso_iff {V W : Type} (A : LabeledGraph ∅ₜ V) (B : LabeledGraph ∅ₜ W) :
    Nonempty (A ≃f B) ↔ Nonempty (A.graph ≃g B.graph) := by
  constructor
  · rintro ⟨f⟩; exact ⟨f.graph_iso⟩
  · rintro ⟨g⟩; exact ⟨⟨g, funext (fun t => (IsEmpty.false t).elim)⟩⟩

/-- The unlabelled-triangle density of a finite graph is `T(G)/C(N,3)`, `T(G) = #(G.cliqueFinset 3)`.
Mirror of `flagDensity_unlabelledEdge_eq`. -/
theorem flagDensity_unlabelledTriangle_eq {N : ℕ} (G : SimpleGraph (Fin N)) :
    flagDensity₁ unlabelledTriangleFlag (graphFlag G)
      = ((G.cliqueFinset 3).card : ℚ) / (N.choose 3) := by
  unfold unlabelledTriangleFlag graphFlag
  rw [flagDensity₁_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero]
  congr 1
  norm_cast
  have hcl : G.cliqueFinset 3
      = Finset.univ.filter (fun S : Finset (Fin N) => G.IsNClique 3 S) := by
    ext S
    simp only [mem_cliqueFinset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hcl]
  congr 1
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨_, hiso⟩
    rw [emptyf_iso_iff] at hiso
    exact (induced_iso_top3_iff G S).mp hiso
  · intro hcl3
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [LabeledGraph.type_verts, Set.image_univ, Set.mem_range] at hx
      obtain ⟨z, _⟩ := hx; exact (IsEmpty.false z).elim
    · rw [emptyf_iso_iff]
      exact (induced_iso_top3_iff G S).mpr hcl3

/-! ## `lem:c5-few-triangles`: `3·T(G) ≤ 2·e(G)` -/

/-- **Triangles through `v` ↔ edges of `G[N(v)]`.**  The induced neighbourhood subgraph `G[N(v)]`
has as many edges as `G` has triangles containing `v`: the edge `{a,b}` of `G[N(v)]` corresponds to
the triangle `{v,a,b}` (inverse: a triangle `t ∋ v` corresponds to the edge `t \ {v}`). -/
private lemma card_edgeFinset_induce_neighborSet_eq {N : ℕ} (G : SimpleGraph (Fin N)) (v : Fin N) :
    (G.induce (G.neighborSet v)).edgeFinset.card
      = ((G.cliqueFinset 3).filter (fun t => v ∈ t)).card := by
  classical
  have hmap := map_edgeFinset_induce (G := G) (s := G.neighborSet v)
  have hcard1 : (G.induce (G.neighborSet v)).edgeFinset.card
      = (G.edgeFinset ∩ (G.neighborSet v).toFinset.sym2).card := by
    rw [← hmap, Finset.card_map]
  rw [hcard1]
  apply Finset.card_bij (fun e _ => insert v e.toFinset)
  · -- the edge `{a,b}` maps to the triangle `{v,a,b}`
    intro e he
    induction e with
    | _ a b =>
      rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff,
        Set.mem_toFinset, Set.mem_toFinset, mem_neighborSet, mem_neighborSet] at he
      obtain ⟨hadjab, hva, hvb⟩ := he
      rw [Sym2.toFinset_mk_eq, Finset.mem_filter, mem_cliqueFinset_iff]
      exact ⟨is3Clique_triple_iff.mpr ⟨hva, hvb, hadjab⟩, Finset.mem_insert_self v _⟩
  · -- injectivity
    intro e1 he1 e2 he2 heq
    induction e1 with
    | _ a b =>
    induction e2 with
    | _ c d =>
      rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff,
        Set.mem_toFinset, Set.mem_toFinset, mem_neighborSet, mem_neighborSet] at he1 he2
      obtain ⟨hadjab, hva, hvb⟩ := he1
      obtain ⟨hadjcd, hvc, hvd⟩ := he2
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at heq
      have hab : a ≠ b := G.ne_of_adj hadjab
      have hva' : v ≠ a := G.ne_of_adj hva
      have hvb' : v ≠ b := G.ne_of_adj hvb
      have hvc' : v ≠ c := G.ne_of_adj hvc
      have hvd' : v ≠ d := G.ne_of_adj hvd
      have hvab : v ∉ ({a, b} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hva', hvb'⟩
      have hvcd : v ∉ ({c, d} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hvc', hvd'⟩
      have hsets : ({a, b} : Finset (Fin N)) = {c, d} := by
        rw [← Finset.erase_insert hvab, heq, Finset.erase_insert hvcd]
      have ha : a ∈ ({c, d} : Finset (Fin N)) := hsets ▸ Finset.mem_insert_self a {b}
      have hb : b ∈ ({c, d} : Finset (Fin N)) :=
        hsets ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · rfl
      · rw [Sym2.eq_swap]
      · exact absurd rfl hab
  · -- surjectivity
    intro t ht
    rw [Finset.mem_filter, mem_cliqueFinset_iff] at ht
    obtain ⟨hclq, hvt⟩ := ht
    have herase : (t.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem hvt, hclq.card_eq]
    obtain ⟨a, b, hab, hter⟩ := Finset.card_eq_two.mp herase
    have hat : a ∈ t :=
      Finset.mem_of_mem_erase (by rw [hter]; exact Finset.mem_insert_self a {b})
    have hbt : b ∈ t :=
      Finset.mem_of_mem_erase (by rw [hter]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    have hav : a ≠ v :=
      Finset.ne_of_mem_erase (by rw [hter]; exact Finset.mem_insert_self a {b})
    have hbv : b ≠ v :=
      Finset.ne_of_mem_erase (by rw [hter]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    have htins : t = insert v {a, b} := by rw [← hter, Finset.insert_erase hvt]
    have hclique : G.IsClique (↑t : Set (Fin N)) := hclq.1
    have hva : G.Adj v a := hclique hvt hat (Ne.symm hav)
    have hvb : G.Adj v b := hclique hvt hbt (Ne.symm hbv)
    have hadjab : G.Adj a b := hclique hat hbt hab
    refine ⟨s(a, b), ?_, ?_⟩
    · rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff,
        Set.mem_toFinset, Set.mem_toFinset, mem_neighborSet, mem_neighborSet]
      exact ⟨hadjab, hva, hvb⟩
    · rw [Sym2.toFinset_mk_eq]; exact htins.symm

/-- **Vertex-localised triangle count.**  `3·T(G) = ∑_v e(G[N(v)])`: each triangle is counted once
at each of its three vertices, and the triangles through `v` are exactly the edges of the
neighbourhood subgraph `G[N(v)]`. -/
theorem three_mul_card_cliqueFinset_three_eq {N : ℕ} (G : SimpleGraph (Fin N)) :
    3 * (G.cliqueFinset 3).card
      = ∑ v : Fin N, (G.induce (G.neighborSet v)).edgeFinset.card := by
  classical
  simp_rw [card_edgeFinset_induce_neighborSet_eq G]
  rw [eq_comm]
  calc ∑ v : Fin N, ((G.cliqueFinset 3).filter (fun t => v ∈ t)).card
      = ∑ v : Fin N, ∑ t ∈ G.cliqueFinset 3, (if v ∈ t then 1 else 0) := by
        simp_rw [Finset.card_filter]
    _ = ∑ t ∈ G.cliqueFinset 3, ∑ v : Fin N, (if v ∈ t then 1 else 0) := Finset.sum_comm
    _ = ∑ t ∈ G.cliqueFinset 3, t.card := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [← Finset.card_filter, Finset.filter_univ_mem]
    _ = ∑ _t ∈ G.cliqueFinset 3, 3 := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        exact (mem_cliqueFinset_iff.mp ht).card_eq
    _ = 3 * (G.cliqueFinset 3).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **`lem:c5-few-triangles`.**  A `C₅`-free graph has at most `(2/3)·e(G)` triangles:
`3·T(G) = ∑_v e(G[N(v)]) ≤ ∑_v |N(v)| = ∑_v deg(v) = 2·e(G)`. -/
theorem c5free_three_mul_triangle_le {N : ℕ} (G : SimpleGraph (Fin N)) (hG : C5g.Free G) :
    3 * (G.cliqueFinset 3).card ≤ 2 * G.edgeFinset.card := by
  rw [three_mul_card_cliqueFinset_three_eq]
  calc ∑ v : Fin N, (G.induce (G.neighborSet v)).edgeFinset.card
      ≤ ∑ v : Fin N, G.degree v := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        calc (G.induce (G.neighborSet v)).edgeFinset.card
            ≤ Fintype.card (G.neighborSet v) := c5free_neighborhood_edge_card_le G hG v
          _ = G.degree v := G.card_neighborSet_eq_degree v
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-! ## `C₅`-free limits have triangle density zero -/

/-- `T(G) ≤ N²` for a `C₅`-free graph (from `3·T ≤ 2e ≤ 2·C(N,2) = N(N-1) ≤ N²`). -/
theorem c5free_triangle_le_sq {N : ℕ} (G : SimpleGraph (Fin N)) (hG : C5g.Free G) :
    ((G.cliqueFinset 3).card : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h3 : (3 : ℝ) * (G.cliqueFinset 3).card ≤ 2 * G.edgeFinset.card := by
    exact_mod_cast c5free_three_mul_triangle_le G hG
  have he : (G.edgeFinset.card : ℝ) ≤ (N.choose 2 : ℝ) := by
    have := G.card_edgeFinset_le_card_choose_two
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hc2 : (N.choose 2 : ℝ) ≤ (N : ℝ) ^ 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [Nat.cast_nonneg (α := ℝ) N, sq_nonneg ((N : ℝ))]
  nlinarith [Nat.cast_nonneg (α := ℝ) (G.cliqueFinset 3).card]

/-- `C(N,3) = N(N-1)(N-2)/6` over `ℝ` (for `N ≥ 2`, so the integer subtractions cast cleanly). -/
private lemma cast_choose_three (N : ℕ) (hN : 2 ≤ N) :
    (N.choose 3 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) / 6 := by
  have hnat : 6 * N.choose 3 = N * (N - 1) * (N - 2) := by
    have hd := Nat.descFactorial_eq_factorial_mul_choose N 3
    have hval : N.descFactorial 3 = (N - 2) * ((N - 1) * ((N - 0) * 1)) := rfl
    rw [hval, Nat.sub_zero, Nat.mul_one] at hd
    have h6 : Nat.factorial 3 = 6 := by decide
    rw [h6] at hd
    rw [← hd]; ring
  have hreal : (6 : ℝ) * (N.choose 3 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) := by
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_sub (show 2 ≤ N by omega)] at hcast
    linarith [hcast]
  rw [eq_div_iff (by norm_num : (6 : ℝ) ≠ 0)]; linarith [hreal]

/-- The bound `N²/C(N,3) → 0` as `N → ∞` (squeezed by `24/N`). -/
theorem sq_div_choose_three_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 / (N.choose 3 : ℝ)) atTop (𝓝 0) := by
  have hub : Tendsto (fun N : ℕ => (24 : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (24 : ℝ)
  apply squeeze_zero' (g := fun N : ℕ => (24 : ℝ) / (N : ℝ)) ?_ ?_ hub
  · filter_upwards [eventually_ge_atTop 3] with N _
    positivity
  · filter_upwards [eventually_ge_atTop 4] with N hN
    have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have hN2 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
    rw [cast_choose_three N (by omega)]
    have hb : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) / 6 := by positivity
    rw [div_le_div_iff₀ hb hNpos]
    have hpoly : (0 : ℝ) ≤ 3 * (N : ℝ) ^ 2 - 12 * (N : ℝ) + 8 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (N : ℝ) - 4 by linarith)
        (show (0 : ℝ) ≤ (N : ℝ) by linarith)]
    nlinarith [mul_nonneg hNpos.le hpoly]

/-- **`C₅`-free limits have triangle density zero.**  Every constrained unlabelled limit `φ₀ ∈ Q₀`
of the `C₅`-free class assigns the unlabelled triangle density `0`.  Mirror of
`c4FreeClass_edgeDegenerate`, with `e(G)/C(N,2)` replaced by `T(G)/C(N,3)` and the squeeze coming
from `c5free_triangle_le_sq` + `sq_div_choose_three_tendsto_zero`.  (`forb0` is `σ`-independent, so
this serves at any type, in particular the two-root edge type.) -/
theorem c5FreeClass_triangleDensity_zero {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    (φ₀ : PositiveHom ∅ₜ) (hφ₀ : posHomPoint φ₀ ∈ Qσ (c5FreeClass.constraintOf σ).forb0) :
    φ₀.coe ⟨3, unlabelledTriangleFlag⟩ = 0 := by
  -- The forbidden-flag hypothesis from membership in `Q₀`.
  set forb0 := (c5FreeClass.constraintOf σ).forb0 with hforb0def
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
  have hlim := hconvF ⟨3, unlabelledTriangleFlag⟩
  set L : ℝ := φ₀.coe ⟨3, unlabelledTriangleFlag⟩ with hLdef
  -- Each component's unlabelled-triangle density is `T(G_t)/C(N_t,3)`.
  have hdensity : ∀ t, flagDensitySeq s t ⟨3, unlabelledTriangleFlag⟩
      = ((((s t).2.out.graph).cliqueFinset 3).card : ℚ) / ((s t).1).choose 3 := by
    intro t
    show (flagDensity₁ unlabelledTriangleFlag (s t).2 : ℝ) = _
    have hgf : (s t).2 = graphFlag ((s t).2.out.graph) := by
      conv_lhs => rw [← Quotient.out_eq (s t).2]
      show (⟦(s t).2.out⟧ : Flag ∅ₜ _) = ⟦_⟧
      apply Quotient.sound
      refine ⟨{ graph_iso := SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
      funext z; exact Fin.elim0 z
    have hval : flagDensity₁ unlabelledTriangleFlag (s t).2
        = (((s t).2.out.graph).cliqueFinset 3).card / ((s t).1).choose 3 := by
      conv_lhs => rw [hgf]
      exact flagDensity_unlabelledTriangle_eq ((s t).2.out.graph)
    rw [hval]; push_cast; ring
  -- Each representing graph is `C₅`-free.
  have hfree : ∀ t, C5g.Free ((s t).2.out.graph) := by
    intro t
    apply HeredClass.mem_of_forbiddenFree c5FreeClass ((s t).2.out)
    intro F hForb
    have hForb0 : forb0 F := by
      show ¬ c5FreeClass.underlyingMem F.2
      have hfb : ¬ c5FreeClass.underlyingMem (unlabel F.2) := hForb
      rwa [unlabel_emptyType] at hfb
    have hzero := hff t F hForb0
    rwa [← Quotient.out_eq (s t).2] at hzero
  -- The density is nonneg and bounded by `N_t²/C(N_t,3) → 0`.
  have hdnn : ∀ t, (0 : ℝ) ≤ flagDensitySeq s t ⟨3, unlabelledTriangleFlag⟩ := by
    intro t
    rw [hdensity t]
    have hge : (0 : ℚ) ≤ (((s t).2.out.graph).cliqueFinset 3).card / ((s t).1).choose 3 := by
      positivity
    exact_mod_cast hge
  have hdle : ∀ t, flagDensitySeq s t ⟨3, unlabelledTriangleFlag⟩
      ≤ ((s t).1 : ℝ) ^ 2 / (((s t).1).choose 3 : ℝ) := by
    intro t
    rw [hdensity t]
    push_cast
    have hnum : ((((s t).2.out.graph).cliqueFinset 3).card : ℝ) ≤ ((s t).1 : ℝ) ^ 2 :=
      c5free_triangle_le_sq _ (hfree t)
    have hden0 : (0 : ℝ) ≤ (((s t).1).choose 3 : ℝ) := by positivity
    exact div_le_div_of_nonneg_right hnum hden0
  have hNtop : Tendsto (fun t => ((s t).1 : ℕ)) atTop atTop := hinc.tendsto_atTop
  have hub : Tendsto (fun t => ((s t).1 : ℝ) ^ 2 / (((s t).1).choose 3 : ℝ))
      atTop (𝓝 0) := sq_div_choose_three_tendsto_zero.comp hNtop
  have hd0 : Tendsto (fun t => flagDensitySeq s t ⟨3, unlabelledTriangleFlag⟩)
      atTop (𝓝 0) := squeeze_zero hdnn hdle hub
  exact tendsto_nhds_unique hlim hd0

end FlagAlgebras.MetaTheory
