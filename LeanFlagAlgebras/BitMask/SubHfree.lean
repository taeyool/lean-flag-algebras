import LeanFlagAlgebras.BitMask.RootedHfree

/-! # Subgraph-forbid (non-clique) kernel bridges

The subgraph-route generators (`C5freeEdge`-style, forbidding `F` as a
**non-induced subgraph**) test forbid-freeness analytically: zero induced
density of **every** supergraph of `F` (`supergraphSym2List`). This module
proves that family condition equivalent to the combinatorial
`¬ subgraphContains F G` — the pivot that lets the typed/empty-typed
completeness layers reuse the rooted-sweep kernel machinery
(`labeledEmittedHfree_mem_iff`) with the decidable subgraph test as the
mask predicate. The key construction is the **pullback graph**: a
subgraph copy of `F` in `G` induces, on its image, a supergraph of `F`
listed in the family. -/

namespace FlagAlgebras.Compute.BitMask

open FlagAlgebras.Compute

/-- The pullback of `G` along an embedding: the `m`-vertex graph whose
edges are exactly the `f`-preimages of `G`'s edges. -/
def pullbackGraph {m n : ℕ} (f : Fin m ↪ Fin n) (G : Sym2Graph n) :
    Sym2Graph m where
  edges := Finset.univ.filter (fun e => ¬ e.IsDiag ∧ e.map f ∈ G.edges)
  edges_valid := fun _ he => (Finset.mem_filter.mp he).2.1

lemma mem_pullbackGraph {m n : ℕ} (f : Fin m ↪ Fin n) (G : Sym2Graph n)
    (i j : Fin m) :
    s(i, j) ∈ (pullbackGraph f G).edges
      ↔ i ≠ j ∧ s(f i, f j) ∈ G.edges := by
  unfold pullbackGraph
  rw [Finset.mem_filter]
  simp [Sym2.mk_isDiag_iff, Sym2.map_pair_eq]

/-- The pullback is an induced copy inside `G` (the host's
diagonal-freeness rules out `i = j`). -/
lemma inducedContains_pullbackGraph {m n : ℕ} (f : Fin m ↪ Fin n)
    (G : Sym2Graph n) : inducedContains (pullbackGraph f G) G := by
  refine ⟨f, fun i j => ?_⟩
  rw [mem_pullbackGraph]
  constructor
  · intro hG
    refine ⟨?_, hG⟩
    rintro rfl
    exact G.edges_valid _ hG (Sym2.mk_isDiag_iff.mpr rfl)
  · exact fun h => h.2

/-- A subgraph-copy embedding makes the pullback a supergraph of `F`. -/
lemma subset_pullbackGraph {m n : ℕ} {H : Sym2Graph m} {f : Fin m ↪ Fin n}
    {G : Sym2Graph n}
    (hf : ∀ i j : Fin m, s(i, j) ∈ H.edges → s(f i, f j) ∈ G.edges) :
    H.edges ⊆ (pullbackGraph f G).edges := by
  intro e he
  induction e using Sym2.ind with | _ i j =>
  rw [mem_pullbackGraph]
  exact ⟨fun hij => H.edges_valid _ he (Sym2.mk_isDiag_iff.mpr hij),
    hf i j he⟩

/-- Every non-diagonal edge is listed in `allEdgesList`. -/
lemma mem_allEdgesList {m : ℕ} {e : Sym2 (Fin m)} (he : ¬ e.IsDiag) :
    e ∈ allEdgesList m := by
  unfold allEdgesList
  rw [List.mem_dedup, List.mem_filter]
  refine ⟨?_, by simp [he]⟩
  induction e using Sym2.ind with | _ i j =>
  rw [List.mem_flatMap]
  exact ⟨i, List.mem_finRange i,
    List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩

/-- Every edge-superset of `H` (same vertex count) is listed in the
supergraph family. -/
lemma mem_supergraphSym2List_of_superset {m : ℕ} {H K : Sym2Graph m}
    (hsub : H.edges ⊆ K.edges) :
    (⟦K⟧ : Sym2EmptyTypedFlag m) ∈ supergraphSym2List H := by
  unfold supergraphSym2List
  rw [List.mem_map]
  refine ⟨((allEdgesList m).filter (fun e => !decide (e ∈ H.edges))).filter
      (fun e => decide (e ∈ K.edges)),
    List.mem_sublists.mpr List.filter_sublist, ?_⟩
  congr 1
  refine Sym2Graph.ext ?_
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with h | h
    · exact hsub h
    · have h2 := List.mem_toFinset.mp (Finset.mem_filter.mp h).1
      exact of_decide_eq_true (List.mem_filter.mp h2).2
  · intro hK
    by_cases hH : e ∈ H.edges
    · exact Finset.mem_union_left _ hH
    · refine Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ?_, K.edges_valid _ hK⟩)
      refine List.mem_filter.mpr ⟨List.mem_filter.mpr
        ⟨mem_allEdgesList (K.edges_valid _ hK), ?_⟩, decide_eq_true hK⟩
      simp [hH]

/-- **The pivot.** Zero induced density of every listed supergraph of
`H` is exactly subgraph-`H`-freeness. -/
theorem supergraph_densities_iff_not_subgraphContains {m n : ℕ}
    (H : Sym2Graph m) (G : Sym2Graph n) :
    (∀ s ∈ supergraphSym2List H,
        sym2EmptyTypeFlagDensity₁ s (⟦G⟧ : Sym2EmptyTypedFlag n) = 0)
      ↔ ¬ subgraphContains H G := by
  constructor
  · rintro hall ⟨f, hf⟩
    have hzero := hall _
      (mem_supergraphSym2List_of_superset (subset_pullbackGraph hf))
    rw [← not_inducedContains_iff_density_eq_zero] at hzero
    exact hzero (inducedContains_pullbackGraph f G)
  · intro hno s hs
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hs
    rw [← not_inducedContains_iff_density_eq_zero]
    rintro ⟨f, hf⟩
    exact hno ⟨f, fun i j hij =>
      (hf i j).mpr (Finset.mem_union_left _ hij)⟩

/-- The family condition as a mask-level test through the encode/decode
roundtrip — the `hpq` shape the typed subgraph-route wiring feeds to
`labeledEmittedHfree_mem_iff`. -/
theorem supergraph_densities_iff_maskTest {m n : ℕ} (H : Sym2Graph m)
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (G : Sym2Graph n) :
    (∀ s ∈ supergraphSym2List H,
        sym2EmptyTypeFlagDensity₁ s (⟦G⟧ : Sym2EmptyTypedFlag n) = 0)
      ↔ (!decide (subgraphContains H
          (graphOfMask₂ n (maskOfGraph₂ G)))) = true := by
  rw [supergraph_densities_iff_not_subgraphContains,
    graphOfMask₂_maskOfGraph₂ hinj G, Bool.not_eq_true',
    decide_eq_false_iff_not]


/-- An emitted list of literal graphs names exactly the subgraph-`F`-free
empty-typed flags (family form) — the subgraph-route analogue of
`emittedFreeFlags_toFinset_eq`. -/
theorem emittedSubFreeFlags_toFinset_eq {n m : ℕ} (F : Sym2Graph m)
    {reps : List ℕ} (canonOf : Sym2Graph n → ℕ)
    (hspec : ∀ G : Sym2Graph n,
      canonOf G ∈ reps ∧ G ∼sf graphOfMask₂ n (canonOf G))
    (Gs : List (Sym2Graph n))
    (hfree : ∀ G ∈ Gs, ¬ subgraphContains F G)
    (hcover : ∀ h ∈ reps, ¬ subgraphContains F (graphOfMask₂ n h) →
      h ∈ Gs.map canonOf) :
    (emittedFlags Gs).toFinset
      = Finset.univ.filter
          (fun S => ∀ s ∈ supergraphSym2List F,
            sym2EmptyTypeFlagDensity₁ s S = 0) := by
  apply Finset.ext
  intro S
  simp only [emittedFlags, List.mem_toFinset, List.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and]
  obtain ⟨G', rfl⟩ := Quotient.exists_rep S
  rw [supergraph_densities_iff_not_subgraphContains]
  constructor
  · rintro ⟨G, hG, hGS⟩ hcon
    exact hfree G hG
      (subgraphContains_of_eqv (Sym2GraphEqv.symm (Quotient.exact hGS)) hcon)
  · intro hfreeG'
    obtain ⟨hmem, heqv⟩ := hspec G'
    have hfreeh : ¬ subgraphContains F (graphOfMask₂ n (canonOf G')) :=
      fun hcon => hfreeG' (subgraphContains_of_eqv (Sym2GraphEqv.symm heqv) hcon)
    obtain ⟨G, hG, hGh⟩ := List.mem_map.mp (hcover (canonOf G') hmem hfreeh)
    refine ⟨G, hG, ?_⟩
    have h1 := (hspec G).2
    rw [hGh] at h1
    exact Quotient.sound (h1.trans (Sym2GraphEqv.symm heqv))

end FlagAlgebras.Compute.BitMask
