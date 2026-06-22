import LeanFlagAlgebras.MetaTheory.C5Free
import LeanFlagAlgebras.MetaTheory.SparseRootRepair

/-! # `C₅`-free root-plantability at the one-vertex type (paper §8)

The one-root case is the first example where root-plantability holds without a global
blow-up-closure hypothesis.  Ordinary false-twin duplication of a vertex may create `C₅`s (if the
root sits in a triangle).  The repair is local: clone the root into a small independent set, but
first delete all old edges inside its neighbourhood.  The deleted set is only linear in the number
of vertices (`lem:c5-nbhd`), so it is invisible to fixed-size labelled flag densities.

This file builds the one-root planting `P_L(G,r)` and proves it `C₅`-free (`lem:c5-planting-free`);
the sparse-root-repair instance and the root-plantability theorem (`thm:c5-one-root`) are added once
[`SparseRootRepair`](./SparseRootRepair.lean) is available.
-/

open FlagAlgebras SimpleGraph

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-- The one-vertex type: a single labelled vertex with no edges. -/
abbrev oneVertexType : FlagType (Fin 1) := ⊥

/-- **One-root planting** `P_L(G,r)` (`def:c5-one-root-planting`).  Vertices: the non-root vertices
`U = V(G) ∖ {r}` (`Sum.inl`) together with an independent root cluster `R` of `L` new vertices
(`Sum.inr`); here `r = θ(0)` is the labelled root.  Adjacency: `R` is independent; each cluster
vertex is joined to exactly `N_G(r) ∩ U`; inside `U` keep every `G`-edge except those with both
endpoints in `N_G(r)`. -/
def oneRootPlant {n : ℕ} (G : LabeledGraph oneVertexType (Fin n)) (L : ℕ) :
    SimpleGraph ({v : Fin n // v ∉ Set.range G.type_embed} ⊕ (Fin 1 × Fin L)) where
  Adj p q :=
    match p, q with
    | Sum.inl u, Sum.inl u' =>
        G.graph.Adj u.1 u'.1 ∧
          ¬ (G.graph.Adj (G.type_embed 0) u.1 ∧ G.graph.Adj (G.type_embed 0) u'.1)
    | Sum.inl u, Sum.inr _ => G.graph.Adj (G.type_embed 0) u.1
    | Sum.inr _, Sum.inl u => G.graph.Adj (G.type_embed 0) u.1
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (u | x) (u' | x') h
    · exact ⟨h.1.symm, fun hc => h.2 ⟨hc.2, hc.1⟩⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    rintro (u | x) h
    · exact G.graph.irrefl h.1
    · exact h

/-- The labelled root `r = θ(0)` is not a non-root vertex: it lies in the range of the type
embedding, while the carrier `U` of `oneRootPlant` excludes that range. -/
private lemma root_ne {n : ℕ} (G : LabeledGraph oneVertexType (Fin n))
    (u : {v : Fin n // v ∉ Set.range G.type_embed}) :
    u.1 ≠ G.type_embed 0 := fun h => u.2 ⟨0, h.symm⟩

/-- Distinct cluster-free images give distinct base vertices: `Sum.inl`-distinctness descends through
`Subtype.val`. -/
private lemma val_ne_of_inl_ne {n : ℕ} (G : LabeledGraph oneVertexType (Fin n)) {L : ℕ}
    {u u' : {v : Fin n // v ∉ Set.range G.type_embed}}
    (h : (Sum.inl u : _ ⊕ (Fin 1 × Fin L)) ≠ Sum.inl u') : u.1 ≠ u'.1 :=
  fun he => h (congrArg Sum.inl (Subtype.ext he))

/-- **The one-root planted graph is `C₅`-free** (`lem:c5-planting-free`).  If `G` is `C₅`-free then
`P_L(G,r)` is `C₅`-free for every `L`.

A copy of `C₅` gives five distinct vertices `f 0,…,f 4` with the five cyclic edges present.  The
cluster `R` is independent, so no two consecutive `f i` lie in `R` — the cluster indices form an
independent set of the `5`-cycle, of size `≤ 2`.  Lift each image to a base vertex (`Sum.inl u ↦ u`,
cluster `↦ r`).  With at most one cluster index the lift is injective and the five cyclic edges all
become `G`-edges (`inl–inl` edges keep their `G`-edge; an `inl–inr`/`inr–inl` edge places the
non-root endpoint in `N(r)`, i.e. gives a `G`-edge to `r`), reconstructing a pentagon in `G`
(`c5_copy_of_pentagon`), contradicting `hG`.  With exactly two cluster indices (necessarily
non-adjacent) the `5`-cycle still has a consecutive `inl–inl` edge whose two endpoints are each
adjacent to a cluster vertex, hence both in `N(r)`; but the `inl–inl` adjacency forbids both
endpoints from lying in `N(r)`, a direct contradiction. -/
theorem oneRootPlant_c5free {n : ℕ} (G : LabeledGraph oneVertexType (Fin n))
    (hG : C5g.Free G.graph) (L : ℕ) : C5g.Free (oneRootPlant G L) := by
  rintro ⟨φ⟩
  set f := φ.toHom with hf_def
  have hf : Function.Injective f := φ.injective'
  -- The five cyclic edges of the copy, present in `oneRootPlant`.
  have E : ∀ i j : Fin 5, (cycleGraph 5).Adj i j → (oneRootPlant G L).Adj (f i) (f j) :=
    fun i j h => f.map_rel h
  have e01 := E 0 1 (by decide)
  have e12 := E 1 2 (by decide)
  have e23 := E 2 3 (by decide)
  have e34 := E 3 4 (by decide)
  have e40 := E 4 0 (by decide)
  -- The ten pairwise distinctnesses of the five images.
  have D : ∀ i j : Fin 5, i ≠ j → f i ≠ f j := fun i j hij h => hij (hf h)
  have d01 := D 0 1 (by decide)
  have d02 := D 0 2 (by decide)
  have d03 := D 0 3 (by decide)
  have d04 := D 0 4 (by decide)
  have d12 := D 1 2 (by decide)
  have d13 := D 1 3 (by decide)
  have d14 := D 1 4 (by decide)
  have d23 := D 2 3 (by decide)
  have d24 := D 2 4 (by decide)
  have d34 := D 3 4 (by decide)
  clear E D hf hf_def
  -- Case on which images lie in the cluster (`Sum.inr`).  Reverting the edge and distinctness
  -- facts substitutes the concrete `inl`/`inr` shapes into them after the split.
  revert e01 e12 e23 e34 e40 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34
  rcases (f 0) with u0 | x0 <;> rcases (f 1) with u1 | x1 <;>
    rcases (f 2) with u2 | x2 <;> rcases (f 3) with u3 | x3 <;>
    rcases (f 4) with u4 | x4 <;>
    intro e01 e12 e23 e34 e40 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34 <;>
    first
      -- Two consecutive cluster images would force an `inr–inr` (i.e. `False`) edge.
      | exact e01 | exact e12 | exact e23 | exact e34 | exact e40
      -- No cluster image: the pentagon `u₀,u₁,u₂,u₃,u₄` in `G`.
      | exact hG (c5_copy_of_pentagon G.graph u0.1 u1.1 u2.1 u3.1 u4.1
          e01.1 e12.1 e23.1 e34.1 e40.1
          (val_ne_of_inl_ne G d01) (val_ne_of_inl_ne G d02) (val_ne_of_inl_ne G d03)
          (val_ne_of_inl_ne G d04) (val_ne_of_inl_ne G d12) (val_ne_of_inl_ne G d13)
          (val_ne_of_inl_ne G d14) (val_ne_of_inl_ne G d23) (val_ne_of_inl_ne G d24)
          (val_ne_of_inl_ne G d34))
      -- One cluster image at position 0: pentagon `r,u₁,u₂,u₃,u₄`.
      | exact hG (c5_copy_of_pentagon G.graph (G.type_embed 0) u1.1 u2.1 u3.1 u4.1
          e01 e12.1 e23.1 e34.1 (show G.graph.Adj (G.type_embed 0) u4.1 from e40).symm
          (fun h => root_ne G u1 h.symm) (fun h => root_ne G u2 h.symm)
          (fun h => root_ne G u3 h.symm) (fun h => root_ne G u4 h.symm)
          (val_ne_of_inl_ne G d12) (val_ne_of_inl_ne G d13) (val_ne_of_inl_ne G d14)
          (val_ne_of_inl_ne G d23) (val_ne_of_inl_ne G d24) (val_ne_of_inl_ne G d34))
      -- One cluster image at position 1: pentagon `u₀,r,u₂,u₃,u₄`.
      | exact hG (c5_copy_of_pentagon G.graph u0.1 (G.type_embed 0) u2.1 u3.1 u4.1
          (show G.graph.Adj (G.type_embed 0) u0.1 from e01).symm e12 e23.1 e34.1 e40.1
          (fun h => root_ne G u0 h) (val_ne_of_inl_ne G d02) (val_ne_of_inl_ne G d03)
          (val_ne_of_inl_ne G d04) (fun h => root_ne G u2 h.symm) (fun h => root_ne G u3 h.symm)
          (fun h => root_ne G u4 h.symm) (val_ne_of_inl_ne G d23) (val_ne_of_inl_ne G d24)
          (val_ne_of_inl_ne G d34))
      -- One cluster image at position 2: pentagon `u₀,u₁,r,u₃,u₄`.
      | exact hG (c5_copy_of_pentagon G.graph u0.1 u1.1 (G.type_embed 0) u3.1 u4.1
          e01.1 (show G.graph.Adj (G.type_embed 0) u1.1 from e12).symm e23 e34.1 e40.1
          (val_ne_of_inl_ne G d01) (fun h => root_ne G u0 h) (val_ne_of_inl_ne G d03)
          (val_ne_of_inl_ne G d04) (fun h => root_ne G u1 h) (val_ne_of_inl_ne G d13)
          (val_ne_of_inl_ne G d14) (fun h => root_ne G u3 h.symm) (fun h => root_ne G u4 h.symm)
          (val_ne_of_inl_ne G d34))
      -- One cluster image at position 3: pentagon `u₀,u₁,u₂,r,u₄`.
      | exact hG (c5_copy_of_pentagon G.graph u0.1 u1.1 u2.1 (G.type_embed 0) u4.1
          e01.1 e12.1 (show G.graph.Adj (G.type_embed 0) u2.1 from e23).symm e34 e40.1
          (val_ne_of_inl_ne G d01) (val_ne_of_inl_ne G d02) (fun h => root_ne G u0 h)
          (val_ne_of_inl_ne G d04) (val_ne_of_inl_ne G d12) (fun h => root_ne G u1 h)
          (val_ne_of_inl_ne G d14) (fun h => root_ne G u2 h) (val_ne_of_inl_ne G d24)
          (fun h => root_ne G u4 h.symm))
      -- One cluster image at position 4: pentagon `u₀,u₁,u₂,u₃,r`.
      | exact hG (c5_copy_of_pentagon G.graph u0.1 u1.1 u2.1 u3.1 (G.type_embed 0)
          e01.1 e12.1 e23.1 (show G.graph.Adj (G.type_embed 0) u3.1 from e34).symm e40
          (val_ne_of_inl_ne G d01) (val_ne_of_inl_ne G d02) (val_ne_of_inl_ne G d03)
          (fun h => root_ne G u0 h) (val_ne_of_inl_ne G d12) (val_ne_of_inl_ne G d13)
          (fun h => root_ne G u1 h) (val_ne_of_inl_ne G d23) (fun h => root_ne G u2 h)
          (fun h => root_ne G u3 h))
      -- Two cluster images at positions {0,2}: the `inl–inl` edge `u₃–u₄` has both ends in `N(r)`.
      | exact e34.2 ⟨(show G.graph.Adj (G.type_embed 0) u3.1 from e23),
          (show G.graph.Adj (G.type_embed 0) u4.1 from e40)⟩
      -- Two cluster images at positions {0,3}: the `inl–inl` edge `u₁–u₂` has both ends in `N(r)`.
      | exact e12.2 ⟨(show G.graph.Adj (G.type_embed 0) u1.1 from e01),
          (show G.graph.Adj (G.type_embed 0) u2.1 from e23)⟩
      -- Two cluster images at positions {1,3}: the `inl–inl` edge `u₄–u₀` has both ends in `N(r)`.
      | exact e40.2 ⟨(show G.graph.Adj (G.type_embed 0) u4.1 from e34),
          (show G.graph.Adj (G.type_embed 0) u0.1 from e01)⟩
      -- Two cluster images at positions {1,4}: the `inl–inl` edge `u₂–u₃` has both ends in `N(r)`.
      | exact e23.2 ⟨(show G.graph.Adj (G.type_embed 0) u2.1 from e12),
          (show G.graph.Adj (G.type_embed 0) u3.1 from e34)⟩
      -- Two cluster images at positions {2,4}: the `inl–inl` edge `u₀–u₁` has both ends in `N(r)`.
      | exact e01.2 ⟨(show G.graph.Adj (G.type_embed 0) u0.1 from e40),
          (show G.graph.Adj (G.type_embed 0) u1.1 from e12)⟩

/-- For an altered non-root pair of the one-root planting, the two endpoints are `G`-adjacent and
both lie in `N_G(r)` (where `r = θ(0)`).  This is the reduction of clause (iii)'s predicate: the
planting changed the within-`U` adjacency exactly on `G`-edges with both ends in the root
neighbourhood. -/
private lemma altered_pair_spec {n : ℕ} (G : LabeledGraph oneVertexType (Fin n)) (L : ℕ)
    (u u' : nonRoot G)
    (halt : (oneRootPlant G L).Adj (Sum.inl u) (Sum.inl u') ≠ G.graph.Adj u.1 u'.1) :
    G.graph.Adj u.1 u'.1 ∧ G.graph.Adj (G.type_embed 0) u.1 ∧ G.graph.Adj (G.type_embed 0) u'.1 := by
  -- `(oneRootPlant G L).Adj (inl u) (inl u')` reduces by the `def`.
  have hadj : (oneRootPlant G L).Adj (Sum.inl u) (Sum.inl u')
      = (G.graph.Adj u.1 u'.1 ∧
          ¬ (G.graph.Adj (G.type_embed 0) u.1 ∧ G.graph.Adj (G.type_embed 0) u'.1)) := rfl
  rw [hadj] at halt
  by_cases hg : G.graph.Adj u.1 u'.1
  · refine ⟨hg, ?_, ?_⟩ <;> by_contra hc
    · exact halt (by rw [eq_iff_iff]; exact ⟨fun _ => hg, fun _ => ⟨hg, fun hpr => hc hpr.1⟩⟩)
    · exact halt (by rw [eq_iff_iff]; exact ⟨fun _ => hg, fun _ => ⟨hg, fun hpr => hc hpr.2⟩⟩)
  · exact absurd (by rw [eq_iff_iff]; exact ⟨fun h => absurd h.1 hg, fun h => absurd h hg⟩) halt

/-- **Clause (iii) for the one-root planting** (the sparse-repair bound).  For `r = θ(0)` and
`N = N_G(r)`, an "altered" non-root pair (one where the planting changed the `G`-adjacency) is exactly
a `G`-edge with both endpoints in `N`; such pairs inject into `G[N]`'s edge set, so there are at most
`e(G[N]) ≤ |N|` of them (`lem:c5-nbhd`), hence at most `n`. -/
private lemma altered_card_le {n : ℕ} (G : LabeledGraph oneVertexType (Fin n))
    (hMem : C5g.Free G.graph) (L : ℕ) :
    ((Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
        ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => (oneRootPlant G L).Adj (Sum.inl u) (Sum.inl u')
              ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p)).card : ℝ)
      ≤ (n : ℝ) := by
  classical
  set r : Fin n := G.type_embed 0 with hr
  set N : Set (Fin n) := G.graph.neighborSet r with hN
  set Filt : Finset (Sym2 (nonRoot G)) := Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
      ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => (oneRootPlant G L).Adj (Sum.inl u) (Sum.inl u')
            ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p) with hFilt
  -- `e(G[N]) ≤ |N|`  (`lem:c5-nbhd`) and `|N| = deg(r) ≤ n`, giving the final bound from `|Filt|`.
  have hnbhd : (G.graph.induce N).edgeFinset.card ≤ Fintype.card ↥N :=
    c5free_neighborhood_edge_card_le G.graph hMem r
  have hNn : Fintype.card ↥N ≤ n := by
    have hcd : Fintype.card ↥N = G.graph.degree r := card_neighborSet_eq_degree G.graph r
    have hlt := G.graph.degree_lt_card_verts r
    simp only [Fintype.card_fin] at hlt
    omega
  -- It suffices to show `|Filt| ≤ e(G[N])`.
  suffices hcard_le : Filt.card ≤ (G.graph.induce N).edgeFinset.card by
    calc (Filt.card : ℝ) ≤ ((G.graph.induce N).edgeFinset.card : ℝ) := by exact_mod_cast hcard_le
      _ ≤ (Fintype.card ↥N : ℝ) := by exact_mod_cast hnbhd
      _ ≤ (n : ℝ) := by exact_mod_cast hNn
  -- Empty case is trivial; otherwise we obtain `Nonempty ↥N` from any altered pair.
  rcases Filt.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]; simp
  · obtain ⟨p₀, hp₀⟩ := hne
    have hNne : Nonempty ↥N := by
      induction p₀ using Sym2.ind with
      | _ u u' =>
        have hmem := hp₀
        rw [hFilt, Finset.mem_filter] at hmem
        obtain ⟨_, _, halt⟩ := hmem
        rw [Sym2.lift_mk] at halt
        obtain ⟨_, hru, _⟩ := altered_pair_spec G L u u' halt
        exact ⟨⟨u.1, hru⟩⟩
    -- The injective map `s(u,u') ↦ s(⟨u.1,_⟩, ⟨u'.1,_⟩)` from altered pairs into `G[N]`'s edges.
    refine Finset.card_le_card_of_injOn
      (fun p => Sym2.map (fun u : nonRoot G =>
        (⟨if h : u.1 ∈ N then u.1 else (Classical.arbitrary (↥N)).1, by
          by_cases h : u.1 ∈ N
          · rw [dif_pos h]; exact h
          · rw [dif_neg h]; exact (Classical.arbitrary (↥N)).2⟩ : ↥N)) p) ?_ ?_
    · -- maps into the edge finset
      intro p hp
      simp only [Finset.mem_coe] at hp
      induction p using Sym2.ind with
      | _ u u' =>
        have hmem := hp
        rw [hFilt, Finset.mem_filter] at hmem
        obtain ⟨_, _, halt⟩ := hmem
        rw [Sym2.lift_mk] at halt
        obtain ⟨hg, hru, hru'⟩ := altered_pair_spec G L u u' halt
        have huN : u.1 ∈ N := hru
        have hu'N : u'.1 ∈ N := hru'
        simp only [Sym2.map_pair_eq, Finset.mem_coe, mem_edgeFinset, mem_edgeSet, comap_adj,
          Function.Embedding.coe_subtype, dif_pos huN, dif_pos hu'N]
        exact hg
    · -- injective on `Filt`
      intro p hp q hq hpq
      simp only [Finset.mem_coe] at hp hq
      induction p using Sym2.ind with
      | _ u u' =>
        induction q using Sym2.ind with
        | _ v v' =>
          simp only [Sym2.map_pair_eq] at hpq
          have hpmem := hp
          rw [hFilt, Finset.mem_filter] at hpmem
          obtain ⟨_, _, halt_p⟩ := hpmem
          rw [Sym2.lift_mk] at halt_p
          obtain ⟨_, hru, hru'⟩ := altered_pair_spec G L u u' halt_p
          have hqmem := hq
          rw [hFilt, Finset.mem_filter] at hqmem
          obtain ⟨_, _, halt_q⟩ := hqmem
          rw [Sym2.lift_mk] at halt_q
          obtain ⟨_, hrv, hrv'⟩ := altered_pair_spec G L v v' halt_q
          have huN : u.1 ∈ N := hru
          have hu'N : u'.1 ∈ N := hru'
          have hvN : v.1 ∈ N := hrv
          have hv'N : v'.1 ∈ N := hrv'
          simp only [dif_pos huN, dif_pos hu'N, dif_pos hvN, dif_pos hv'N, Sym2.eq_iff,
            Subtype.mk.injEq] at hpq
          rw [Sym2.eq_iff]
          rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩

set_option maxHeartbeats 800000 in
/-- **Sparse root-blow-up repairs for `C₅`-free graphs at the one-vertex type**
(`def:sparse-root-repair` instance, `thm:c5-one-root`).  Take cluster size `L = ⌊λn⌋` and
`H = P_L(G,r)` (the one-root planting): the cross-adjacencies are exactly the prescribed ones
(clauses (i)–(ii)), and the only old–old edges deleted are the `G`-edges inside `N_G(r)`, of which
there are at most `|N_G(r)| ≤ n` (`lem:c5-nbhd`), which is `≤ ρn²` once `n ≥ 1/ρ`. -/
theorem c5FreeClass_sparseRootRepair_oneVertex :
    SparseRootRepair c5FreeClass oneVertexType := by
  refine ⟨by norm_num, ?_⟩
  intro lam ρ hlam0 hlam1 hρ0
  refine ⟨max ⌈2 / lam⌉₊ (max ⌈1 / ρ⌉₊ 1), ?_⟩
  intro n G hMem hn
  -- `hMem : c5FreeClass.Mem G.graph` is `C5g.Free G.graph`.
  have hMem' : C5g.Free G.graph := hMem
  -- Threshold consequences.
  have hn1 : (1 : ℕ) ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn2lam : ⌈(2 : ℝ) / lam⌉₊ ≤ n := le_trans (le_max_left _ _) hn
  have hn1rho : ⌈(1 : ℝ) / ρ⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  refine ⟨⌊lam * (n : ℝ)⌋₊, oneRootPlant G ⌊lam * (n : ℝ)⌋₊, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Llb : lam * n / 2 ≤ (L : ℝ)`
    have hlamn2 : (2 : ℝ) ≤ lam * (n : ℝ) := by
      have h2 : (2 : ℝ) / lam ≤ (n : ℝ) := by
        calc (2 : ℝ) / lam ≤ (⌈(2 : ℝ) / lam⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn2lam
      rw [div_le_iff₀ hlam0] at h2; linarith
    have hfloor := Nat.lt_floor_add_one (lam * (n : ℝ))
    have hfloorR : (⌊lam * (n : ℝ)⌋₊ : ℝ) > lam * (n : ℝ) - 1 := by linarith [hfloor]
    nlinarith [hfloorR, hlamn2]
  · -- `Lub : (L : ℝ) ≤ lam * n`
    exact Nat.floor_le (by positivity)
  · -- `Mem`: `C₅`-free
    exact oneRootPlant_c5free G hMem' ⌊lam * (n : ℝ)⌋₊
  · -- clause (i): vacuous on `Fin 1`
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · -- clause (ii)
    intro i a u
    have hi0 : i = 0 := Fin.fin_one_eq_zero i
    subst hi0
    exact Iff.rfl
  · -- clause (iii): the sparse-edge bound
    have hcard := altered_card_le G hMem' ⌊lam * (n : ℝ)⌋₊
    refine le_trans hcard ?_
    -- `n ≤ ρ * n²` because `ρ * n ≥ 1`.
    have hρn : (1 : ℝ) ≤ ρ * (n : ℝ) := by
      have h1 : (1 : ℝ) / ρ ≤ (n : ℝ) := by
        calc (1 : ℝ) / ρ ≤ (⌈(1 : ℝ) / ρ⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn1rho
      rw [div_le_iff₀ hρ0] at h1; linarith
    have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith [hρn, hnpos]

/-- **`C₅`-free root-plantability at the one-vertex type** (`thm:c5-one-root`).  Combining the sparse
root-blow-up repair instance with `sparseRootRepair_finitePlanting` and
`finitePlanting_root_plantable`. -/
theorem c5free_one_root_plantable :
    RootPlantable (c5FreeClass.constraintOf oneVertexType) :=
  finitePlanting_root_plantable c5FreeClass oneVertexType (by norm_num)
    (sparseRootRepair_finitePlanting c5FreeClass oneVertexType c5FreeClass_sparseRootRepair_oneVertex)

end FlagAlgebras.MetaTheory
