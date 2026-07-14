import LeanFlagAlgebras.MetaTheory.PairSubsetCount
import LeanFlagAlgebras.MetaTheory.HeredClass

/-! # Unlabelled flags as plain graphs: the `∅ₜ` bridge

Infrastructure for the `φ_W` construction (`MetaTheory/GraphonHom.lean`).  At the empty type
an (iso-class) flag carries no root data, so `Flag ∅ₜ (Fin n)` is the set of `n`-vertex graphs
up to isomorphism, reached from `SimpleGraph (Fin n)` by `graphFlag` (`HeredClass.lean`).
This file makes that identification workable:

* `flagEqv_emptyType_iff` / `graphFlag_eq_iff` — at `∅ₜ`, flag isomorphism is graph
  isomorphism, and `graphFlag G = graphFlag H ↔ Nonempty (G ≃g H)`.
* `graphFlag_out` / `graphFlag_surjective` — every unlabelled flag is `graphFlag` of a graph.
* `graphComapEquiv` / `graphFlag_comap_equiv` — pulling back along a vertex permutation is an
  equivalence of `SimpleGraph (Fin n)` fixing the flag class.
* `comap_iso_induce_range` — the pullback along an embedding is isomorphic to the induced
  subgraph on its range.
* `exists_perm_comp_emb` / `exists_perm_comp_emb_pair` — any two embeddings (resp. disjoint
  pairs of embeddings) of `Fin n` into `Fin ℓ` differ by a permutation of `Fin ℓ`; the
  reindexing engine of the subset-averaging arguments.
* `flagDensity₁_graphFlag` — the unlabelled flag density as a vertex-subset count:
  `p(F, H) = #{S : H[S] ≅ F} / C(ℓ,n)` (specialising `flagDensity₁_eq_subset_count_div`).
* `flagDensity₂_graphFlag` — the unlabelled pair density on a host with exactly `n₁ + n₂`
  vertices as a count of ordered partitions
  `#{(S₁,S₂) disjoint : H[S₁] ≅ F₁, H[S₂] ≅ F₂} / C(n₁+n₂, n₁)`
  (specialising `flagDensity₂_eq_subset_count_div`; the multinomial coefficient
  `multinomialCoefficient ![n₁, n₂] (n₁+n₂)` evaluates to the binomial).
-/

open Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-! ## Flag isomorphism at the empty type -/

/-- At the empty type a labelled-graph isomorphism is the same datum as a plain graph
isomorphism: the `type_preserve` law is vacuous (`Fin 0` is empty).  (Public version of the
private lemma of `C4Free.lean`.) -/
theorem flagEqv_emptyType_iff {V W : Type} (A : LabeledGraph ∅ₜ V) (B : LabeledGraph ∅ₜ W) :
    Nonempty (A ≃f B) ↔ Nonempty (A.graph ≃g B.graph) := by
  constructor
  · rintro ⟨f⟩; exact ⟨f.graph_iso⟩
  · rintro ⟨g⟩; exact ⟨⟨g, funext (fun t => (IsEmpty.false t).elim)⟩⟩

/-- Two graphs give the same unlabelled flag iff they are isomorphic. -/
theorem graphFlag_eq_iff {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) :
    graphFlag G = graphFlag H ↔ Nonempty (G ≃g H) := by
  show (⟦_⟧ : Flag ∅ₜ V) = ⟦_⟧ ↔ _
  rw [Quotient.eq]
  exact flagEqv_emptyType_iff _ _

/-- Every unlabelled flag is the `graphFlag` of the graph underlying its chosen
representative. -/
theorem graphFlag_out {V : Type} [Fintype V] [DecidableEq V] (F : Flag ∅ₜ V) :
    graphFlag (F.out.graph) = F := by
  set Hrep : LabeledGraph ∅ₜ V :=
    {graph := F.out.graph, type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj F.out.graph.Adj} with hHrep
  have hiso : Hrep ∼f F.out := by
    refine ⟨⟨?_, ?_⟩⟩
    · rw [hHrep]
    · ext t; exact (IsEmpty.false t).elim
  have heq := flagEqv.sound hiso
  rw [Quotient.out_eq F] at heq
  exact heq

theorem graphFlag_surjective (V : Type) [Fintype V] [DecidableEq V] :
    Function.Surjective (graphFlag : SimpleGraph V → Flag ∅ₜ V) :=
  fun F => ⟨F.out.graph, graphFlag_out F⟩

/-! ## Relabelling -/

/-- Pulling back along a vertex equivalence, as an equivalence of graph types. -/
def graphComapEquiv {V W : Type} (e : V ≃ W) : SimpleGraph W ≃ SimpleGraph V where
  toFun G := G.comap ⇑e
  invFun G := G.comap ⇑e.symm
  left_inv G := by ext u v; simp
  right_inv G := by ext u v; simp

@[simp]
theorem graphComapEquiv_apply {V W : Type} (e : V ≃ W) (G : SimpleGraph W) :
    graphComapEquiv e G = G.comap ⇑e := rfl

/-- Pulling back along a vertex permutation does not change the flag class. -/
theorem graphFlag_comap_equiv {V : Type} [Fintype V] [DecidableEq V] (e : V ≃ V)
    (G : SimpleGraph V) : graphFlag (G.comap ⇑e) = graphFlag G := by
  rw [graphFlag_eq_iff]
  exact ⟨SimpleGraph.Iso.comap e G⟩

/-! ## Embeddings, ranges, and permutations -/

/-- The pullback of `H` along an embedding is isomorphic to the induced subgraph on the
embedding's range (via `Equiv.ofInjective`). -/
theorem comap_iso_induce_range {V W : Type} (H : SimpleGraph W) (j : V ↪ W) :
    Nonempty (H.comap ⇑j ≃g H.induce (Set.range ⇑j)) := by
  refine ⟨⟨Equiv.ofInjective j j.injective, ?_⟩⟩
  intro u v
  simp [SimpleGraph.comap_adj, SimpleGraph.induce]

/-- Any two embeddings of `Fin n` into `Fin ℓ` differ by a permutation of the codomain.

Proof route: both ranges have complement of size `ℓ − n`; combine the range bijection
`j₁ i ↦ j₂ i` with an arbitrary bijection of the complements (`Fintype.equivOfCardEq`)
through `Equiv.Set.sumCompl`. -/
theorem exists_perm_comp_emb {n ℓ : ℕ} (j₁ j₂ : Fin n ↪ Fin ℓ) :
    ∃ π : Fin ℓ ≃ Fin ℓ, ∀ i, π (j₁ i) = j₂ i := by
  classical
  have hcard : Fintype.card (Set.range ⇑j₁) = Fintype.card (Set.range ⇑j₂) := by
    rw [Fintype.card_range, Fintype.card_range]
  have hcardcompl :
      Fintype.card (↥(Set.range ⇑j₁)ᶜ) = Fintype.card (↥(Set.range ⇑j₂)ᶜ) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hcard]
  set e1 : ↥(Set.range ⇑j₁) ≃ ↥(Set.range ⇑j₂) :=
    (Equiv.ofInjective j₁ j₁.injective).symm.trans (Equiv.ofInjective j₂ j₂.injective) with he1
  set e2 : ↥(Set.range ⇑j₁)ᶜ ≃ ↥(Set.range ⇑j₂)ᶜ := Fintype.equivOfCardEq hcardcompl with he2
  set π : Fin ℓ ≃ Fin ℓ :=
    (Equiv.Set.sumCompl (Set.range ⇑j₁)).symm.trans
      ((e1.sumCongr e2).trans (Equiv.Set.sumCompl (Set.range ⇑j₂))) with hπ
  refine ⟨π, ?_⟩
  intro i
  have hmem : j₁ i ∈ Set.range ⇑j₁ := ⟨i, rfl⟩
  rw [hπ]
  simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmem,
    Equiv.sumCongr_apply, Sum.map_inl, he1, Equiv.trans_apply,
    Equiv.ofInjective_symm_apply, Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]

/-- Any two *disjoint pairs* of embeddings differ by a single permutation of the codomain
(the pair version of `exists_perm_comp_emb`, needed for the pair-density averaging). -/
theorem exists_perm_comp_emb_pair {n₁ n₂ ℓ : ℕ}
    (j₁ k₁ : Fin n₁ ↪ Fin ℓ) (j₂ k₂ : Fin n₂ ↪ Fin ℓ)
    (hj : Disjoint (Set.range ⇑j₁) (Set.range ⇑j₂))
    (hk : Disjoint (Set.range ⇑k₁) (Set.range ⇑k₂)) :
    ∃ π : Fin ℓ ≃ Fin ℓ, (∀ i, π (j₁ i) = k₁ i) ∧ (∀ i, π (j₂ i) = k₂ i) := by
  classical
  -- range equivalences
  set e1 : ↥(Set.range ⇑j₁) ≃ ↥(Set.range ⇑k₁) :=
    (Equiv.ofInjective j₁ j₁.injective).symm.trans (Equiv.ofInjective k₁ k₁.injective) with he1
  set e2 : ↥(Set.range ⇑j₂) ≃ ↥(Set.range ⇑k₂) :=
    (Equiv.ofInjective j₂ j₂.injective).symm.trans (Equiv.ofInjective k₂ k₂.injective) with he2
  -- union equivalence
  set f1 : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂) ≃ ↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂) :=
    (Equiv.Set.union hj).trans ((e1.sumCongr e2).trans (Equiv.Set.union hk).symm) with hf1
  -- cardinalities of the unions agree
  have hcardU : Fintype.card ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂)
      = Fintype.card ↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂) := Fintype.card_congr f1
  have hcardcompl :
      Fintype.card (↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂)ᶜ)
        = Fintype.card (↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂)ᶜ) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hcardU]
  set e3 : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂)ᶜ ≃ ↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂)ᶜ :=
    Fintype.equivOfCardEq hcardcompl with he3
  set π : Fin ℓ ≃ Fin ℓ :=
    (Equiv.Set.sumCompl (Set.range ⇑j₁ ∪ Set.range ⇑j₂)).symm.trans
      ((f1.sumCongr e3).trans (Equiv.Set.sumCompl (Set.range ⇑k₁ ∪ Set.range ⇑k₂))) with hπ
  refine ⟨π, ?_, ?_⟩
  · intro i
    have hmem1 : j₁ i ∈ Set.range ⇑j₁ := ⟨i, rfl⟩
    have hmemU : j₁ i ∈ Set.range ⇑j₁ ∪ Set.range ⇑j₂ := Or.inl hmem1
    rw [hπ]
    simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmemU,
      Equiv.sumCongr_apply, Sum.map_inl]
    rw [hf1]
    simp only [Equiv.trans_apply,
      Equiv.Set.union_apply_left (a := (⟨j₁ i, hmemU⟩ : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂))) hj hmem1,
      Equiv.sumCongr_apply, Sum.map_inl, he1, Equiv.trans_apply,
      Equiv.ofInjective_symm_apply, Equiv.Set.union_symm_apply_left,
      Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]
  · intro i
    have hmem2 : j₂ i ∈ Set.range ⇑j₂ := ⟨i, rfl⟩
    have hmemU : j₂ i ∈ Set.range ⇑j₁ ∪ Set.range ⇑j₂ := Or.inr hmem2
    rw [hπ]
    simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmemU,
      Equiv.sumCongr_apply, Sum.map_inl]
    rw [hf1]
    simp only [Equiv.trans_apply,
      Equiv.Set.union_apply_right (a := (⟨j₂ i, hmemU⟩ : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂))) hj hmem2,
      Equiv.sumCongr_apply, Sum.map_inr, he2, Equiv.trans_apply,
      Equiv.ofInjective_symm_apply, Equiv.Set.union_symm_apply_right,
      Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]

/-! ## Unlabelled flag densities as subset counts -/

/-- The `graphFlag` representative record has empty `type_verts`: the empty type `∅ₜ = Fin 0`
has no elements to embed. -/
private lemma graphFlagRep_type_verts_eq_empty {V : Type} (G : SimpleGraph V) :
    (⟨G, RelEmbedding.ofIsEmpty ∅ₜ.Adj G.Adj⟩ : LabeledGraph ∅ₜ V).type_verts = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro v hv
  rw [LabeledGraph.mem_type_verts] at hv
  obtain ⟨t, _⟩ := hv
  exact (IsEmpty.false t).elim

/-- **The unlabelled flag density as a subset count**: for graphs `F` on `Fin n` and `H` on
`Fin ℓ`, the flag density of `graphFlag F` in `graphFlag H` is the number of vertex subsets
of `H` inducing a copy of `F`, over `C(ℓ, n)`.

Proof route: `flagDensity₁_eq_subset_count_div` (`LabeledCount.lean`); at `∅ₜ` the root-
containment clause is vacuous (`type_verts = ∅`), `≃f` reduces to `≃g`
(`flagEqv_emptyType_iff`), and the coe of `inducedLabeledSubgraph` on `↑S` is graph-
isomorphic to `H.induce ↑S`; the sizes reduce via `emptyType_size` and
`Fintype.card_fin`. -/
theorem flagDensity₁_graphFlag {n ℓ : ℕ} (F : SimpleGraph (Fin n)) (H : SimpleGraph (Fin ℓ)) :
    flagDensity₁ (graphFlag F) (graphFlag H)
      = ((Finset.univ.filter
          (fun S : Finset (Fin ℓ) => Nonempty (H.induce ↑S ≃g F))).card : ℚ)
        / (ℓ.choose n) := by
  show flagDensity₁ (⟦(⟨F, RelEmbedding.ofIsEmpty ∅ₜ.Adj F.Adj⟩ : LabeledGraph ∅ₜ (Fin n))⟧)
        (⟦(⟨H, RelEmbedding.ofIsEmpty ∅ₜ.Adj H.Adj⟩ : LabeledGraph ∅ₜ (Fin ℓ))⟧) = _
  rw [flagDensity₁_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero]
  congr 1
  rw [Nat.cast_inj]
  congr 1
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨_, hiso⟩
    rw [flagEqv_emptyType_iff] at hiso
    simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.inducedLabeledSubgraph] at hiso
    rw [SimpleGraph.induce_eq_coe_induce_top]
    exact hiso
  · intro hiso
    refine ⟨?_, ?_⟩
    · rw [graphFlagRep_type_verts_eq_empty]; exact Set.empty_subset _
    · rw [flagEqv_emptyType_iff]
      simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.inducedLabeledSubgraph]
      rw [← SimpleGraph.induce_eq_coe_induce_top]
      exact hiso

/-- **The unlabelled pair density on a tight host as an ordered-partition count**: for graphs
`F₁` on `Fin n₁`, `F₂` on `Fin n₂` and a host `H` on exactly `n₁ + n₂` vertices, the pair
density counts the ordered pairs of disjoint vertex subsets inducing copies of `F₁` and `F₂`,
over the binomial `C(n₁+n₂, n₁)`.

Proof route: `flagDensity₂_eq_subset_count_div` (`PairSubsetCount.lean`); at `∅ₜ`
disjointness-outside-roots is plain disjointness, `≃f` reduces to `≃g` as in
`flagDensity₁_graphFlag`, and
`multinomialCoefficient ![n₁, n₂] (n₁ + n₂) = (n₁ + n₂).choose n₁`
(`multinomialCoefficient_eq_choose_mul_multinomial` + `Nat.multinomial` on a pair). -/
theorem flagDensity₂_graphFlag {n₁ n₂ : ℕ} (F₁ : SimpleGraph (Fin n₁))
    (F₂ : SimpleGraph (Fin n₂)) (H : SimpleGraph (Fin (n₁ + n₂))) :
    flagDensity₂ (graphFlag F₁) (graphFlag F₂) (graphFlag H)
      = ((Finset.univ.filter
          (fun P : Finset (Fin (n₁ + n₂)) × Finset (Fin (n₁ + n₂)) =>
            Disjoint P.1 P.2
            ∧ Nonempty (H.induce ↑P.1 ≃g F₁) ∧ Nonempty (H.induce ↑P.2 ≃g F₂))).card : ℚ)
        / ((n₁ + n₂).choose n₁) := by
  show flagDensity₂ (⟦(⟨F₁, RelEmbedding.ofIsEmpty ∅ₜ.Adj F₁.Adj⟩ : LabeledGraph ∅ₜ (Fin n₁))⟧)
        (⟦(⟨F₂, RelEmbedding.ofIsEmpty ∅ₜ.Adj F₂.Adj⟩ : LabeledGraph ∅ₜ (Fin n₂))⟧)
        (⟦(⟨H, RelEmbedding.ofIsEmpty ∅ₜ.Adj H.Adj⟩ : LabeledGraph ∅ₜ (Fin (n₁ + n₂)))⟧) = _
  rw [flagDensity₂_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero]
  have hmulti : multinomialCoefficient ![n₁, n₂] (n₁ + n₂) = (n₁ + n₂).choose n₁ := by
    rw [multinomialCoefficient_eq_choose_mul_multinomial]
    have hsum : (∑ x, (![n₁, n₂] : Fin 2 → ℕ) x) = n₁ + n₂ := by simp [Fin.sum_univ_two]
    rw [hsum, Nat.choose_self, one_mul]
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [huniv, Nat.binomial_eq_choose (by decide : (0 : Fin 2) ≠ 1)]
    simp
  rw [hmulti]
  congr 1
  rw [Nat.cast_inj]
  congr 1
  apply Finset.filter_congr
  intro P _
  unfold IsInducedPairOn
  constructor
  · rintro ⟨hdisj, ⟨_, hiso1⟩, ⟨_, hiso2⟩⟩
    rw [graphFlagRep_type_verts_eq_empty, Set.diff_empty, Set.diff_empty] at hdisj
    refine ⟨?_, ?_, ?_⟩
    · rw [← Finset.disjoint_coe, Set.disjoint_iff_inter_eq_empty]
      exact hdisj
    · rw [flagEqv_emptyType_iff] at hiso1
      simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.inducedLabeledSubgraph] at hiso1
      rw [SimpleGraph.induce_eq_coe_induce_top]
      exact hiso1
    · rw [flagEqv_emptyType_iff] at hiso2
      simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.inducedLabeledSubgraph] at hiso2
      rw [SimpleGraph.induce_eq_coe_induce_top]
      exact hiso2
  · rintro ⟨hdisj, hiso1, hiso2⟩
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [graphFlagRep_type_verts_eq_empty, Set.diff_empty, Set.diff_empty,
        ← Set.disjoint_iff_inter_eq_empty, Finset.disjoint_coe]
      exact hdisj
    · exact graphFlagRep_type_verts_eq_empty H ▸ Set.empty_subset _
    · rw [flagEqv_emptyType_iff]
      simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.inducedLabeledSubgraph]
      rw [← SimpleGraph.induce_eq_coe_induce_top]
      exact hiso1
    · exact graphFlagRep_type_verts_eq_empty H ▸ Set.empty_subset _
    · rw [flagEqv_emptyType_iff]
      simp only [LabeledSubgraph.coe_graph, LabeledSubgraph.inducedLabeledSubgraph]
      rw [← SimpleGraph.induce_eq_coe_induce_top]
      exact hiso2

end FlagAlgebras.MetaTheory
