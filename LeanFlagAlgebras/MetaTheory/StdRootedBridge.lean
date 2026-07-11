import LeanFlagAlgebras.MetaTheory.PairSubsetCount
import LeanFlagAlgebras.MetaTheory.EmptyTypeGraphBridge

/-! # Standard-rooted flags on `Fin n`: the two-root bridge

The two-root analogue of `MetaTheory/EmptyTypeGraphBridge.lean`.  For a two-vertex type
`σ : FlagType (Fin 2)` a **standard-rooted** graph is a `G : SimpleGraph (Fin n)` whose
adjacency at the vertex pair `(0, 1)` matches `σ` (`RootCompatible`); such a `G` carries the
canonical root embedding `Fin.castLE`, giving the labelled graph `mkStdRooted` and its flag
class.  The rooted conditional profile of `GraphonRootedHom.lean` sums over exactly these
graphs (pinning the samples of coordinates `0, 1` is only meaningful for the standard
embedding).

Contents:

* `RootCompatible` / `mkStdRooted` / `mkStdRooted_type_verts` — the standard rooting.
* `mkStdRooted_flag_eq_iff` — two standard-rooted graphs give the same flag iff they are
  isomorphic by a **root-fixing** graph isomorphism.
* `exists_stdRooted_rep` — every flag class on `Fin n` has a standard-rooted representative
  (relabel any representative to put its roots at `0, 1`).
* `rootCompatible_comap_of_rootFixing` / `rootCompatible_comap_perm` /
  `mkStdRooted_comap_rootfix_perm` — pulling back along root-fixing maps preserves the
  standard rooting, and root-fixing permutations preserve the flag class.
* `exists_rootfix_perm_comp_emb` / `exists_rootfix_perm_comp_emb_pair` — the root-fixing
  permutation engine: any two root-fixing embeddings (resp. pairs of embeddings overlapping
  exactly in the roots) differ by a root-fixing permutation of the codomain.
* `flagTypeFin2_size` / `flagDensity₁_stdRooted` — the size bookkeeping and the rooted
  density-as-subset-count formula (instantiating the general
  `flagDensity₁_eq_subset_count_div` at standard-rooted representatives).

This module is deliberately certificate-free: it works with an arbitrary
`σ : FlagType (Fin 2)`; the transports to the generated `FlagType_2_0`/`FlagType_2_1` live
downstream with the consumers.
-/

open Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

variable {σ : FlagType (Fin 2)}

/-! ## The standard rooting -/

/-- `G` accepts the standard rooting: its adjacency on the first two vertices matches the
two-vertex type `σ`. -/
def RootCompatible (σ : FlagType (Fin 2)) {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    Prop :=
  ∀ a b : Fin 2, σ.Adj a b ↔ G.Adj (Fin.castLE hn a) (Fin.castLE hn b)

/-- The standard-rooted labelled graph: `G` with the roots at vertices `0, 1` via the
`Fin.castLE` embedding. -/
def mkStdRooted (σ : FlagType (Fin 2)) {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (h : RootCompatible σ hn G) : LabeledGraph σ (Fin n) where
  graph := G
  type_embed :=
    { toFun := Fin.castLE hn
      inj' := Fin.castLE_injective hn
      map_rel_iff' := fun {a b} => (h a b).symm }

@[simp]
theorem mkStdRooted_graph {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (h : RootCompatible σ hn G) : (mkStdRooted σ hn G h).graph = G := rfl

@[simp]
theorem mkStdRooted_type_embed_apply {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (h : RootCompatible σ hn G) (a : Fin 2) :
    (mkStdRooted σ hn G h).type_embed a = Fin.castLE hn a := rfl

/-- The labelled vertices of a standard-rooted graph are exactly `{0, 1}`. -/
theorem mkStdRooted_type_verts {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (h : RootCompatible σ hn G) :
    (mkStdRooted σ hn G h).type_verts
      = ({Fin.castLE hn 0, Fin.castLE hn 1} : Set (Fin n)) := by
  ext x
  simp only [LabeledGraph.mem_type_verts, mkStdRooted_type_embed_apply, Fin.exists_fin_two,
    Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]

/-! ## Flag classes of standard-rooted graphs -/

/-- Two standard-rooted graphs give the same flag iff they are isomorphic by a root-fixing
graph isomorphism.  (The two-root analogue of `graphFlag_eq_iff`: `type_preserve` for the
standard embeddings says exactly that the iso fixes `0` and `1`.) -/
theorem mkStdRooted_flag_eq_iff {n : ℕ} (hn : 2 ≤ n) (G G' : SimpleGraph (Fin n))
    (h : RootCompatible σ hn G) (h' : RootCompatible σ hn G') :
    (⟦mkStdRooted σ hn G h⟧ : Flag σ (Fin n)) = ⟦mkStdRooted σ hn G' h'⟧
      ↔ ∃ ψ : G ≃g G', ∀ a : Fin 2, ψ (Fin.castLE hn a) = Fin.castLE hn a := by
  rw [Quotient.eq]
  constructor
  · rintro ⟨φ⟩
    refine ⟨φ.graph_iso, fun a => ?_⟩
    have := congrFun φ.type_preserve a
    simpa only [Function.comp_apply, mkStdRooted_type_embed_apply] using this
  · rintro ⟨ψ, hψ⟩
    exact ⟨⟨ψ, funext fun a => by
      simp only [Function.comp_apply, mkStdRooted_type_embed_apply]
      exact hψ a⟩⟩

/-- Every flag class on `Fin n` has a standard-rooted representative: relabel any
representative by a permutation carrying its roots to `0, 1`.

The proof takes `F.out`, extends the injection `Fin 2 → Fin n` given by its `type_embed`
to a permutation `π` of `Fin n` sending `type_embed a ↦ Fin.castLE hn a`
(via `exists_perm_comp_emb` from `EmptyTypeGraphBridge` applied to the two-element
embeddings), pulls the graph back along `π.symm`, and checks the resulting labelled graph
is flag-equivalent to `F.out` via the iso `π`. -/
theorem exists_stdRooted_rep {n : ℕ} (hn : 2 ≤ n) (F : FlagWithSize σ n) :
    ∃ (G : SimpleGraph (Fin n)) (h : RootCompatible σ hn G),
      (⟦mkStdRooted σ hn G h⟧ : Flag σ (Fin n)) = F := by
  set Hrep : LabeledGraph σ (Fin n) := F.out with hHrep
  set e : Fin 2 ↪ Fin n := Hrep.type_embed.toEmbedding with he
  set s : Fin 2 ↪ Fin n := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ with hs
  obtain ⟨π, hπ⟩ := exists_perm_comp_emb e s
  set G : SimpleGraph (Fin n) := Hrep.graph.comap ⇑π.symm with hGdef
  have hsymm : ∀ a : Fin 2, π.symm (Fin.castLE hn a) = Hrep.type_embed a := by
    intro a
    have hπa : π (e a) = Fin.castLE hn a := hπ a
    have : π.symm (Fin.castLE hn a) = e a := by
      rw [← hπa, Equiv.symm_apply_apply]
    rw [this, he]
    rfl
  have h : RootCompatible σ hn G := by
    intro a b
    show σ.Adj a b ↔ G.Adj (Fin.castLE hn a) (Fin.castLE hn b)
    rw [hGdef]
    simp only [SimpleGraph.comap_adj]
    rw [hsymm a, hsymm b]
    exact type_embed_Adj_iff Hrep a b
  refine ⟨G, h, ?_⟩
  have hiso : mkStdRooted σ hn G h ∼f Hrep := by
    refine ⟨⟨SimpleGraph.Iso.comap π.symm Hrep.graph, ?_⟩⟩
    funext a
    simp only [Function.comp_apply, mkStdRooted_type_embed_apply]
    exact (SimpleGraph.Iso.comap_apply π.symm Hrep.graph (Fin.castLE hn a)).trans (hsymm a)
  have heq := flagEqv.sound hiso
  rw [hHrep] at heq
  rwa [Quotient.out_eq] at heq

/-! ## Root-fixing maps -/

/-- An embedding `Fin n ↪ Fin ℓ` is root-fixing when it carries the standard roots to the
standard roots. -/
def RootFixing {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (j : Fin n ↪ Fin ℓ) : Prop :=
  ∀ a : Fin 2, j (Fin.castLE hn a) = Fin.castLE hℓ a

/-- The inclusion `Fin.castLE` is root-fixing. -/
theorem rootFixing_castLE {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (h : n ≤ ℓ) :
    RootFixing hn hℓ ⟨Fin.castLE h, Fin.castLE_injective h⟩ := by
  intro a
  show Fin.castLE h (Fin.castLE hn a) = Fin.castLE hℓ a
  simp [Fin.castLE_castLE]

/-- Pulling back along a root-fixing embedding preserves root compatibility. -/
theorem rootCompatible_comap_of_rootFixing {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ)
    (j : Fin n ↪ Fin ℓ) (hj : RootFixing hn hℓ j) {H : SimpleGraph (Fin ℓ)}
    (hH : RootCompatible σ hℓ H) : RootCompatible σ hn (H.comap ⇑j) := by
  intro a b
  show σ.Adj a b ↔ H.Adj (j (Fin.castLE hn a)) (j (Fin.castLE hn b))
  rw [hj a, hj b]
  exact hH a b

/-- Root compatibility is preserved by pulling back along a root-fixing permutation. -/
theorem rootCompatible_comap_perm {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (π : Fin ℓ ≃ Fin ℓ)
    (hπ : ∀ a : Fin 2, π (Fin.castLE hℓ a) = Fin.castLE hℓ a) {H : SimpleGraph (Fin ℓ)}
    (hH : RootCompatible σ hℓ H) : RootCompatible σ hℓ (H.comap ⇑π) := by
  intro a b
  show σ.Adj a b ↔ H.Adj (π (Fin.castLE hℓ a)) (π (Fin.castLE hℓ b))
  rw [hπ a, hπ b]
  exact hH a b

/-- Pulling back along a root-fixing permutation does not change the standard-rooted flag
class. -/
theorem mkStdRooted_comap_rootfix_perm {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (π : Fin ℓ ≃ Fin ℓ)
    (hπ : ∀ a : Fin 2, π (Fin.castLE hℓ a) = Fin.castLE hℓ a) (H : SimpleGraph (Fin ℓ))
    (hH : RootCompatible σ hℓ H) :
    (⟦mkStdRooted σ hℓ (H.comap ⇑π) (rootCompatible_comap_perm hℓ π hπ hH)⟧
        : Flag σ (Fin ℓ))
      = ⟦mkStdRooted σ hℓ H hH⟧ := by
  rw [mkStdRooted_flag_eq_iff]
  exact ⟨SimpleGraph.Iso.comap π H, hπ⟩

/-! ## The root-fixing permutation engine -/

/-- Any two root-fixing embeddings of `Fin n` into `Fin ℓ` differ by a root-fixing
permutation of the codomain.  (Root-fixing of `π` on the roots follows from the first clause
and `RootFixing`; it is exposed for convenience.)

The proof adapts the complement construction of `exists_perm_comp_emb`
(`EmptyTypeGraphBridge`) relative to the roots: the ranges agree on the roots, so the
range bijection `j₁ i ↦ j₂ i` already fixes them, and the complement bijection never
touches them. -/
theorem exists_rootfix_perm_comp_emb {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ)
    (j₁ j₂ : Fin n ↪ Fin ℓ) (hj₁ : RootFixing hn hℓ j₁) (hj₂ : RootFixing hn hℓ j₂) :
    ∃ π : Fin ℓ ≃ Fin ℓ,
      (∀ i, π (j₁ i) = j₂ i) ∧ ∀ a : Fin 2, π (Fin.castLE hℓ a) = Fin.castLE hℓ a := by
  obtain ⟨π, hπ⟩ := exists_perm_comp_emb j₁ j₂
  refine ⟨π, hπ, fun a => ?_⟩
  calc π (Fin.castLE hℓ a) = π (j₁ (Fin.castLE hn a)) := by rw [hj₁ a]
    _ = j₂ (Fin.castLE hn a) := hπ (Fin.castLE hn a)
    _ = Fin.castLE hℓ a := hj₂ a

/-- A root-fixing embedding sends a point to a root iff the point itself is a root
(injectivity plus `RootFixing` on each of the two roots). -/
private lemma mem_roots_iff_of_rootFixing {n' ℓ : ℕ} (hn' : 2 ≤ n') (hℓ : 2 ≤ ℓ)
    (j : Fin n' ↪ Fin ℓ) (hj : RootFixing hn' hℓ j) (i : Fin n') :
    j i ∈ ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ))
      ↔ i ∈ ({Fin.castLE hn' 0, Fin.castLE hn' 1} : Set (Fin n')) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h0 | h1)
    · exact Or.inl (j.injective (h0.trans (hj 0).symm))
    · exact Or.inr (j.injective (h1.trans (hj 1).symm))
  · rintro (rfl | rfl)
    · exact Or.inl (hj 0)
    · exact Or.inr (hj 1)

/-- The range of a root-fixing embedding restricted to the non-root domain points is exactly
the range of the embedding minus the roots. -/
private lemma range_restrict_roots_compl {n' ℓ : ℕ} (hn' : 2 ≤ n') (hℓ : 2 ≤ ℓ)
    (j : Fin n' ↪ Fin ℓ) (hj : RootFixing hn' hℓ j) :
    Set.range (fun x : ↥(({Fin.castLE hn' 0, Fin.castLE hn' 1} : Set (Fin n'))ᶜ) => j x.1)
      = Set.range ⇑j \ ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, rfl⟩, ?_⟩
    rw [mem_roots_iff_of_rootFixing hn' hℓ j hj]
    exact x.2
  · rintro ⟨⟨i, rfl⟩, hnot⟩
    exact ⟨⟨i, fun hR => hnot ((mem_roots_iff_of_rootFixing hn' hℓ j hj i).mpr hR)⟩, rfl⟩

/-- The pair version of `exists_rootfix_perm_comp_emb`, for pairs of root-fixing embeddings
whose ranges overlap **exactly** in the roots (the gluing configuration of the rooted
`mulProp`): a single root-fixing permutation aligns both simultaneously.

The proof splits `Fin ℓ` into the roots, the two non-root range parts, and the rest; the
non-root parts of the ranges are disjoint by the overlap hypotheses, so the three-piece
assembly of `exists_perm_comp_emb_pair` applies on the complement of the roots. -/
theorem exists_rootfix_perm_comp_emb_pair {n₁ n₂ ℓ : ℕ}
    (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hℓ : 2 ≤ ℓ)
    (j₁ k₁ : Fin n₁ ↪ Fin ℓ) (j₂ k₂ : Fin n₂ ↪ Fin ℓ)
    (hj₁ : RootFixing hn₁ hℓ j₁) (hk₁ : RootFixing hn₁ hℓ k₁)
    (hj₂ : RootFixing hn₂ hℓ j₂) (hk₂ : RootFixing hn₂ hℓ k₂)
    (hj : Set.range ⇑j₁ ∩ Set.range ⇑j₂
        = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)))
    (hk : Set.range ⇑k₁ ∩ Set.range ⇑k₂
        = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ))) :
    ∃ π : Fin ℓ ≃ Fin ℓ, (∀ i, π (j₁ i) = k₁ i) ∧ (∀ i, π (j₂ i) = k₂ i) := by
  classical
  set j₂r : ↥(({Fin.castLE hn₂ 0, Fin.castLE hn₂ 1} : Set (Fin n₂))ᶜ) ↪ Fin ℓ :=
    ⟨fun x => j₂ x.1, fun x y hxy => Subtype.ext (j₂.injective hxy)⟩ with hj2r
  set k₂r : ↥(({Fin.castLE hn₂ 0, Fin.castLE hn₂ 1} : Set (Fin n₂))ᶜ) ↪ Fin ℓ :=
    ⟨fun x => k₂ x.1, fun x y hxy => Subtype.ext (k₂.injective hxy)⟩ with hk2r
  have hBj : Set.range ⇑j₂r
      = Set.range ⇑j₂ \ ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) :=
    range_restrict_roots_compl hn₂ hℓ j₂ hj₂
  have hBk : Set.range ⇑k₂r
      = Set.range ⇑k₂ \ ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) :=
    range_restrict_roots_compl hn₂ hℓ k₂ hk₂
  have hAB : Disjoint (Set.range ⇑j₁) (Set.range ⇑j₂r) := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    rw [hBj] at hyB
    exact hyB.2 (hj ▸ (⟨hyA, hyB.1⟩ : y ∈ Set.range ⇑j₁ ∩ Set.range ⇑j₂))
  have hA'B' : Disjoint (Set.range ⇑k₁) (Set.range ⇑k₂r) := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    rw [hBk] at hyB
    exact hyB.2 (hk ▸ (⟨hyA, hyB.1⟩ : y ∈ Set.range ⇑k₁ ∩ Set.range ⇑k₂))
  set e1 : ↥(Set.range ⇑j₁) ≃ ↥(Set.range ⇑k₁) :=
    (Equiv.ofInjective j₁ j₁.injective).symm.trans (Equiv.ofInjective k₁ k₁.injective) with he1
  set e2 : ↥(Set.range ⇑j₂r) ≃ ↥(Set.range ⇑k₂r) :=
    (Equiv.ofInjective j₂r j₂r.injective).symm.trans (Equiv.ofInjective k₂r k₂r.injective) with he2
  set f1 : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂r) ≃ ↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂r) :=
    (Equiv.Set.union hAB).trans ((e1.sumCongr e2).trans (Equiv.Set.union hA'B').symm) with hf1
  have hcardU : Fintype.card ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂r)
      = Fintype.card ↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂r) := Fintype.card_congr f1
  have hcardcompl :
      Fintype.card (↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂r)ᶜ)
        = Fintype.card (↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂r)ᶜ) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hcardU]
  set e3 : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂r)ᶜ ≃ ↥(Set.range ⇑k₁ ∪ Set.range ⇑k₂r)ᶜ :=
    Fintype.equivOfCardEq hcardcompl with he3
  set π : Fin ℓ ≃ Fin ℓ :=
    (Equiv.Set.sumCompl (Set.range ⇑j₁ ∪ Set.range ⇑j₂r)).symm.trans
      ((f1.sumCongr e3).trans (Equiv.Set.sumCompl (Set.range ⇑k₁ ∪ Set.range ⇑k₂r))) with hπdef
  have hclause1 : ∀ i, π (j₁ i) = k₁ i := by
    intro i
    have hmem1 : j₁ i ∈ Set.range ⇑j₁ := ⟨i, rfl⟩
    have hmemU : j₁ i ∈ Set.range ⇑j₁ ∪ Set.range ⇑j₂r := Or.inl hmem1
    rw [hπdef]
    simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmemU,
      Equiv.sumCongr_apply, Sum.map_inl]
    rw [hf1]
    simp only [Equiv.trans_apply,
      Equiv.Set.union_apply_left
        (a := (⟨j₁ i, hmemU⟩ : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂r))) hAB hmem1,
      Equiv.sumCongr_apply, Sum.map_inl, he1, Equiv.trans_apply,
      Equiv.ofInjective_symm_apply, Equiv.Set.union_symm_apply_left,
      Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]
  refine ⟨π, hclause1, ?_⟩
  intro i
  by_cases hi : i ∈ ({Fin.castLE hn₂ 0, Fin.castLE hn₂ 1} : Set (Fin n₂))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · calc π (j₂ (Fin.castLE hn₂ 0)) = π (Fin.castLE hℓ 0) := by rw [hj₂ 0]
        _ = π (j₁ (Fin.castLE hn₁ 0)) := by rw [hj₁ 0]
        _ = k₁ (Fin.castLE hn₁ 0) := hclause1 (Fin.castLE hn₁ 0)
        _ = Fin.castLE hℓ 0 := hk₁ 0
        _ = k₂ (Fin.castLE hn₂ 0) := (hk₂ 0).symm
    · calc π (j₂ (Fin.castLE hn₂ 1)) = π (Fin.castLE hℓ 1) := by rw [hj₂ 1]
        _ = π (j₁ (Fin.castLE hn₁ 1)) := by rw [hj₁ 1]
        _ = k₁ (Fin.castLE hn₁ 1) := hclause1 (Fin.castLE hn₁ 1)
        _ = Fin.castLE hℓ 1 := hk₁ 1
        _ = k₂ (Fin.castLE hn₂ 1) := (hk₂ 1).symm
  · have hmem2 : j₂r ⟨i, hi⟩ ∈ Set.range ⇑j₂r := ⟨⟨i, hi⟩, rfl⟩
    have hmemU : j₂r ⟨i, hi⟩ ∈ Set.range ⇑j₁ ∪ Set.range ⇑j₂r := Or.inr hmem2
    have hval : (j₂r ⟨i, hi⟩ : Fin ℓ) = j₂ i := rfl
    rw [← hval, hπdef]
    simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmemU,
      Equiv.sumCongr_apply, Sum.map_inl]
    rw [hf1]
    simp only [Equiv.trans_apply,
      Equiv.Set.union_apply_right
        (a := (⟨j₂r ⟨i, hi⟩, hmemU⟩ : ↥(Set.range ⇑j₁ ∪ Set.range ⇑j₂r))) hAB hmem2,
      Equiv.sumCongr_apply, Sum.map_inr, he2, Equiv.trans_apply,
      Equiv.ofInjective_symm_apply, Equiv.Set.union_symm_apply_right,
      Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]
    rfl

/-! ## Sizes and the rooted density-as-count formula -/

/-- Any two-vertex type has size two. -/
theorem flagTypeFin2_size (σ : FlagType (Fin 2)) : σ.size = 2 := by
  show Fintype.card (Fin 2) = 2
  exact Fintype.card_fin 2

/-- **The rooted flag density as a roots-containing-subset count**: for standard-rooted
`G` on `Fin n` and host `H` on `Fin ℓ`, the density is the number of vertex subsets of the
host containing the roots and inducing a rooted copy of `G`, over `C(ℓ−2, n−2)`.
(Instantiates the general `flagDensity₁_eq_subset_count_div` at the standard-rooted
representatives; only the size bookkeeping `flagTypeFin2_size` is new.) -/
theorem flagDensity₁_stdRooted {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ)
    (G : SimpleGraph (Fin n)) (hG : RootCompatible σ hn G)
    (H : SimpleGraph (Fin ℓ)) (hH : RootCompatible σ hℓ H) :
    flagDensity₁ (⟦mkStdRooted σ hn G hG⟧ : Flag σ (Fin n))
        (⟦mkStdRooted σ hℓ H hH⟧ : Flag σ (Fin ℓ))
      = ((Finset.univ.filter (fun S : Finset (Fin ℓ) =>
          ∃ h : (mkStdRooted σ hℓ H hH).type_verts ⊆ (↑S : Set (Fin ℓ)),
            Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ hℓ H hH) (↑S) h).coe
              ≃f mkStdRooted σ hn G hG))).card : ℚ)
        / ((ℓ - 2).choose (n - 2)) := by
  rw [flagDensity₁_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, flagTypeFin2_size]

end FlagAlgebras.MetaTheory
