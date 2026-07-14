import LeanFlagAlgebras.MetaTheory.C5FewTriangles
import LeanFlagAlgebras.MetaTheory.StarWitness

/-! # The `C₅`-free edge-type obstruction (paper §9.5)

The `C₅`-free class is root-plantable at the one-vertex type (`thm:c5-one-root`) and the two-root
non-edge type (`thm:c5-nonedge-root`).  At the two-root **edge** type `τ` it is *not*: a book graph
provides a pinning obstruction.  This is the section that refutes the natural all-types `C₅`-free
conjecture.

The mechanism is pinning of the **common-neighbour triangle flag** `F_△` over the edge type `τ`:

* Under random edge-rooting of any constrained unlabelled limit, `F_△` is pinned almost surely to
  `0` (`ae_Ftri_eq_zero_of_pinned`), because `C₅`-free graphs have few triangles
  (`lem:c5-few-triangles`, via `C5FewTriangles`): the unlabelled triangle density vanishes, so the
  downward average `⟨F_△⟩_τ` is killed.
* The **book graph** `B_n` (`def:c5-book`) is `C₅`-free (`book_c5free`) yet has a special edge whose
  endpoints share *every* other vertex, giving `F_△`-density `1` (`book_Ftri_density`); the limit is
  a quotient point `ψ ∈ Q_τ` with `ψ(F_△) = 1` (`lem:c5-book`, `exists_book_Qτ_point`).
* `thm:c5-edge-not-root-plantable` (`c5free_edge_not_rootPlantable`) assembles these via the abstract
  `pinning_obstruction`.

`cor:c5-no-pin` records that at the one-vertex type the edge and triangle flags give *no* obstruction
(the triangle flag is pinned at `0` and the quotient attains only `0`; the edge flag is not pinned at
all).
-/

open MeasureTheory SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The two-root edge type and the common-neighbour triangle flag -/

/-- The **two-root edge type** `τ`: two labelled vertices joined by an edge (`⊤` on `Fin 2`). -/
abbrev edgeType : FlagType (Fin 2) := ⊤

/-- The **common-neighbour triangle** as a labelled graph over the edge type: the complete graph `K₃`
on `Fin 3`, with the two roots `0,1` (joined by the type edge) and the unlabelled vertex `2` adjacent
to both. -/
def triangleLabeled : LabeledGraph edgeType (Fin 3) where
  graph := ⊤
  type_embed :=
    { toFun := fun i => i.castLE (by omega)
      inj' := Fin.castLE_injective (by omega)
      map_rel_iff' := by
        intro a b
        rw [top_adj, top_adj]
        constructor
        · intro hne hab
          exact hne (congrArg (fun i : Fin 2 => i.castLE (by omega)) hab)
        · intro hne hc
          exact hne (Fin.castLE_injective (by omega) hc) }

/-- The common-neighbour triangle as a size-tagged flag over the edge type. -/
noncomputable def triangleFF : FinFlag edgeType := ⟨3, (⟦triangleLabeled⟧ : Flag edgeType (Fin 3))⟩

/-- **The triangle edge-type flag** `F_△ ∈ A^τ` (paper's `F_△`): the three-vertex `τ`-flag in which
the one unlabelled vertex is adjacent to both roots. -/
noncomputable def F_tri : FlagAlgebra edgeType := ⟦basisVector triangleFF⟧

/-- `F_△` is nonnegative at every positive homomorphism (a single basis flag). -/
lemma F_tri_eval_nonneg (φ : PositiveHom edgeType) : 0 ≤ φ F_tri :=
  positiveHom_basisVector_ge_zero φ triangleFF

/-- The triangle edge-type flag un-labels to the unlabelled triangle on `Fin 3`. -/
theorem unlabel_triangleFF :
    unlabel triangleFF.2 = unlabelledTriangleFlag := by
  show unlabel (⟦triangleLabeled⟧ : Flag edgeType (Fin 3)) = graphFlag (⊤ : SimpleGraph (Fin 3))
  apply Quotient.sound
  refine ⟨{ graph_iso := SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
  funext z; exact Fin.elim0 z

/-! ## Generalized quotient-point assembly -/

/-- **Witness assembly (general flag).**  Given an increasing sequence of `σ`-flags whose underlying
graphs are all in the class and whose `F`-densities converge to `c`, there is a quotient point
`ψ ∈ Q_σ` with `ψ(⟦basisVector F⟧) = c`.  Generalisation of `exists_Qσ_point_edge_eq`. -/
theorem exists_Qσ_point_flag_eq (hc : HeredClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    (F : FinFlag σ) (s : FlagSeq σ) (hinc : Increases s)
    (hmem : ∀ n, hc.underlyingMem (unlabel (s n).2))
    (c : ℝ) (hlim : Tendsto (fun n => (flagDensity₁ F.2 (s n).2 : ℝ)) atTop (𝓝 c)) :
    ∃ ψ ∈ Qσ (hc.constraintOf σ).forbσ, (PositiveHomSpace.toPosHom ψ) ⟦basisVector F⟧ = c := by
  classical
  obtain ⟨a, ϕ, hmono, hconv⟩ := increasing_flagSeq_contain_convergent_subseq s hinc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (s ∘ ϕ) hconv
  set ψ : PositiveHomSpace σ := posHomPoint φ with hψ
  obtain ⟨_, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  have hclass : ∀ (k : ℕ), hc.Mem ((s (ϕ k)).2.out).graph := by
    intro k
    have hm := hmem (ϕ k)
    rw [← Quotient.out_eq (s (ϕ k)).2, hc.underlyingMem_unlabel_mk] at hm
    exact hm
  refine ⟨ψ, ?_, ?_⟩
  · rw [mem_Qσ_iff]
    intro Fb hFb
    have hψval : ψ.val Fb = a Fb := by
      rw [hψ, posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
    rw [hψval]
    have hzero : ∀ k, (flagDensity₁ Fb.2 (s (ϕ k)).2 : ℝ) = 0 := by
      intro k
      rw [← Quotient.out_eq (s (ϕ k)).2]
      exact_mod_cast flagDensity_forbidden_eq_zero_of_mem hc _ (hclass k) Fb hFb
    have hF_tendsto : Tendsto (fun k => (flagDensity₁ Fb.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 (a Fb)) := hpt Fb
    have h0 : Tendsto (fun k => (flagDensity₁ Fb.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 0) := by simp only [hzero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hF_tendsto h0
  · have hval : (PositiveHomSpace.toPosHom ψ) ⟦basisVector F⟧ = a F := by
      rw [PositiveHomSpace.toPosHom_basisVector, hψ, posHomPoint_val_apply,
        ← PositiveHom.coe_flag, hφ]
    rw [hval]
    have h_sub : Tendsto (fun k => (flagDensity₁ F.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 (a F)) := hpt F
    have h_c : Tendsto (fun k => (flagDensity₁ F.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 c) := hlim.comp hmono.tendsto_atTop
    exact tendsto_nhds_unique h_sub h_c

/-! ## `cor:c5-edge-pinned`: the triangle flag is pinned to `0` under random edge-rooting -/

/-- The downward average of `F_△` is killed by every constrained unlabelled limit: `φ₀ ⟦F_△⟧₀ = 0`
(a scalar multiple of the unlabelled triangle density, which vanishes by `C5FewTriangles`). -/
theorem Ftri_downward_zero {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ (c5FreeClass.constraintOf edgeType).forb0) :
    φ₀ (⟦F_tri⟧₀ : FlagAlgebra ∅ₜ) = 0 := by
  show φ₀ (downward (⟦basisVector triangleFF⟧ : FlagAlgebra edgeType)) = 0
  rw [downward_basisVector, PositiveHom.map_smul]
  have htri : φ₀ (⟦basisVector ⟨triangleFF.1, unlabel triangleFF.2⟩⟧ : FlagAlgebra ∅ₜ) = 0 := by
    rw [← PositiveHom.coe_flag]
    show φ₀.coe (⟨3, unlabel triangleFF.2⟩ : FinFlag ∅ₜ) = 0
    rw [unlabel_triangleFF]
    exact c5FreeClass_triangleDensity_zero φ₀ hφ₀
  rw [htri, mul_zero]

/-- **`cor:c5-edge-pinned`.**  Under any admissible random edge-rooting, the triangle flag `F_△` is
almost surely `0`: a `[0,1]`-valued variable of mean `0` vanishes a.s.  (The mean is
`φ₀ ⟦F_△⟧₀ / φ₀ ⟦1⟧₀ = 0` by `Ftri_downward_zero`.) -/
theorem ae_Ftri_eq_zero_of_pinned {φ₀ : PositiveHom ∅ₜ}
    (hφ₀ : posHomPoint φ₀ ∈ Qσ (c5FreeClass.constraintOf edgeType).forb0)
    (hσ : φ₀ ⟨edgeType⟩₀ > 0) :
    ∀ᵐ χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace edgeType)),
      (PositiveHomSpace.toPosHom χ) F_tri = 0 := by
  set g : PositiveHomSpace edgeType → ℝ := fun χ => (PositiveHomSpace.toPosHom χ) F_tri with hg
  have fpos : ∀ χ, 0 ≤ g χ := fun χ => F_tri_eval_nonneg _
  have hint : Integrable g (ℙ[φ₀] : Measure (PositiveHomSpace edgeType)) :=
    BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact (evalContinuousMap F_tri))
  have hf0 : ∫ χ, g χ ∂(ℙ[φ₀] : Measure (PositiveHomSpace edgeType)) = 0 := by
    simp only [hg]
    rw [probMeasure_extend_emptyType_positiveHom_spec hσ F_tri, Ftri_downward_zero hφ₀, zero_div]
  have hae := (integral_eq_zero_iff_of_nonneg fpos hint).mp hf0
  filter_upwards [hae] with χ hχ
  exact hχ

/-! ## `def:c5-book`: the book graph -/

/-- **The book graph** `B_n` (`def:c5-book`), as a `τ`-flag on `Fin (n+2)`: vertices `0,1` are the
two roots, joined by the type edge; vertices `2,…,n+1` are the `n` pages, each adjacent to both roots
and to nothing else. -/
def bookLabeled (n : ℕ) : LabeledGraph edgeType (Fin (n + 2)) where
  graph :=
    { Adj := fun i j => i ≠ j ∧ (i.val < 2 ∨ j.val < 2)
      symm := fun i j h => ⟨h.1.symm, h.2.symm⟩
      loopless := fun i h => h.1 rfl }
  type_embed :=
    { toFun := fun i => i.castLE (by omega)
      inj' := Fin.castLE_injective (by omega)
      map_rel_iff' := by
        intro a b
        rw [top_adj]
        constructor
        · rintro ⟨hne, _⟩ hab
          exact hne (congrArg (fun i : Fin 2 => i.castLE (by omega)) hab)
        · intro hne
          exact ⟨fun hc => hne (Fin.castLE_injective (by omega) hc), Or.inl a.isLt⟩ }

/-- **`lem:c5-book`, freeness part.**  Each book graph `B_n` is `C₅`-free.  A `5`-cycle would have to
use at least three pages (only two of its five vertices can be roots), and each page's two cycle
neighbours must be the two roots — forcing a root to appear three times. -/
theorem book_c5free (n : ℕ) : C5g.Free (bookLabeled n).graph := by
  rintro ⟨φ⟩
  set f := φ.toHom with hfdef
  have hinj : Function.Injective f := φ.injective'
  -- Every `C₅`-edge has a root (vertex of value `< 2`) endpoint: `{i | f i is a root}` is a
  -- vertex cover of `C₅`, hence has at least `3` elements; but the only roots are `0,1`.
  have hcov : ∀ i j : Fin 5, C5g.Adj i j → (f i).val < 2 ∨ (f j).val < 2 := by
    intro i j hij
    exact (f.map_adj hij).2
  -- At most two `C₅`-vertices map to roots (`f` injective into the two values `< 2`).
  have htwo : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      (f i).val < 2 → (f j).val < 2 → (f k).val < 2 → False := by
    intro i j k hij hik hjk hi hj hk
    have h3 : (f i).val = (f j).val ∨ (f i).val = (f k).val ∨ (f j).val = (f k).val := by omega
    rcases h3 with h | h | h
    · exact hij (hinj (Fin.ext h))
    · exact hik (hinj (Fin.ext h))
    · exact hjk (hinj (Fin.ext h))
  -- Any vertex cover of `C₅` contains three distinct vertices (min cover size is `3`).
  have key : ∀ r : Fin 5 → Bool,
      (r 0 = true ∨ r 1 = true) → (r 1 = true ∨ r 2 = true) →
      (r 2 = true ∨ r 3 = true) → (r 3 = true ∨ r 4 = true) →
      (r 4 = true ∨ r 0 = true) →
      ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ r i = true ∧ r j = true ∧ r k = true := by decide
  set r : Fin 5 → Bool := fun i => decide ((f i).val < 2) with hr
  have hrt : ∀ i, r i = true ↔ (f i).val < 2 := fun i => by simp only [hr, decide_eq_true_eq]
  have c01 : r 0 = true ∨ r 1 = true := (hcov 0 1 (by decide)).imp (hrt 0).mpr (hrt 1).mpr
  have c12 : r 1 = true ∨ r 2 = true := (hcov 1 2 (by decide)).imp (hrt 1).mpr (hrt 2).mpr
  have c23 : r 2 = true ∨ r 3 = true := (hcov 2 3 (by decide)).imp (hrt 2).mpr (hrt 3).mpr
  have c34 : r 3 = true ∨ r 4 = true := (hcov 3 4 (by decide)).imp (hrt 3).mpr (hrt 4).mpr
  have c40 : r 4 = true ∨ r 0 = true := (hcov 4 0 (by decide)).imp (hrt 4).mpr (hrt 0).mpr
  obtain ⟨i, j, k, hij, hik, hjk, ri, rj, rk⟩ := key r c01 c12 c23 c34 c40
  exact htwo i j k hij hik hjk ((hrt i).mp ri) ((hrt j).mp rj) ((hrt k).mp rk)

/-- The book graph's type embedding sends label `t` to the vertex of the same value. -/
private theorem bookLabeled_type_embed_val (n : ℕ) (t : Fin 2) :
    ((bookLabeled n).type_embed t).val = t.val := rfl

/-- The book graph's type embedding sends `0 ↦ 0`. -/
private theorem bookLabeled_type_embed_zero (n : ℕ) :
    (bookLabeled n).type_embed 0 = (0 : Fin (n + 2)) := by
  apply Fin.ext; rw [bookLabeled_type_embed_val]; rfl

/-- The book graph's type embedding sends `1 ↦ 1`. -/
private theorem bookLabeled_type_embed_one (n : ℕ) :
    (bookLabeled n).type_embed 1 = (1 : Fin (n + 2)) := by
  apply Fin.ext
  rw [bookLabeled_type_embed_val, Fin.val_one]
  rfl

open LabeledSubgraph in
/-- **Forward iso.**  For a page `v` (a vertex `≠ 0, 1`) the labelled subgraph of `B_n` induced on
`{0, 1, v}` is flag-isomorphic to the common-neighbour triangle `triangleLabeled`. -/
private theorem triIso_fwd (n : ℕ) (v : Fin (n + 2)) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (h : (bookLabeled n).type_verts ⊆ (↑({0, 1, v} : Finset (Fin (n + 2))) : Set (Fin (n + 2)))) :
    Nonempty ((inducedLabeledSubgraph (bookLabeled n) (↑({0, 1, v} : Finset (Fin (n + 2)))) h).coe
      ≃f triangleLabeled) := by
  classical
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by apply Fin.ne_of_val_ne; simp
  set G := bookLabeled n with hGdef
  set S : Set (Fin (n + 2)) := (↑({0, 1, v} : Finset (Fin (n + 2))) : Set (Fin (n + 2))) with hS
  have h0S : (0 : Fin (n + 2)) ∈ S := by rw [hS]; simp
  have h1S : (1 : Fin (n + 2)) ∈ S := by rw [hS]; simp
  have hvS : v ∈ S := by rw [hS]; simp
  set IG := inducedLabeledSubgraph G S h with hIG
  have hverts : IG.subgraph.verts = S := inducedLabeledSubgraph_verts G S h
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ S := fun a => hverts ▸ a.property
  have valS : ∀ a : ↥IG.subgraph.verts, a.val = 0 ∨ a.val = 1 ∨ a.val = v := by
    intro a
    have hm := memS a
    rw [hS] at hm
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hm
  have key : ∀ (a b : ↥IG.subgraph.verts), IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce S).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  let f : Fin 3 → ↥IG.subgraph.verts := fun i =>
    if i = 0 then ⟨0, hverts ▸ h0S⟩ else if i = 1 then ⟨1, hverts ▸ h1S⟩ else ⟨v, hverts ▸ hvS⟩
  have hf0 : (f 0).val = (0 : Fin (n + 2)) := by simp [f]
  have hf1 : (f 1).val = (1 : Fin (n + 2)) := by simp [f]
  have hf2 : (f 2).val = v := by simp [f]
  have hfinj : Function.Injective f := by
    intro a b hab
    have hval : (f a).val = (f b).val := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.reduceFinMk, Fin.isValue, hf0, hf1, hf2] at hval ⊢ <;>
      first
        | rfl
        | exact absurd hval h01
        | exact absurd hval.symm h01
        | exact absurd hval hv0.symm
        | exact absurd hval hv0
        | exact absurd hval hv1.symm
        | exact absurd hval hv1
  have hScard : S.ncard = 3 := by
    rw [hS, Set.ncard_coe_finset]
    have e1 : (1 : Fin (n + 2)) ∉ ({v} : Finset (Fin (n + 2))) := by
      simp only [Finset.mem_singleton]; exact hv1.symm
    have e0 : (0 : Fin (n + 2)) ∉ ({1, v} : Finset (Fin (n + 2))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨h01, hv0.symm⟩
    rw [show ({0, 1, v} : Finset (Fin (n + 2))) = insert 0 (insert 1 {v}) from rfl,
      Finset.card_insert_of_notMem e0, Finset.card_insert_of_notMem e1, Finset.card_singleton]
  have hcard : Fintype.card ↥IG.subgraph.verts = Fintype.card (Fin 3) := by
    rw [Fintype.card_congr (Equiv.setCongr hverts), Fintype.card_fin,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hScard]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard.symm⟩
  let ef : Fin 3 ≃ ↥IG.subgraph.verts := Equiv.ofBijective f hfbij
  refine ⟨LabeledGraphIso.symm ⟨{ toEquiv := ef, map_rel_iff' := ?_ }, ?_⟩⟩
  · intro a b
    show IG.coe.graph.Adj (ef a) (ef b) ↔ triangleLabeled.graph.Adj a b
    rw [key (ef a) (ef b)]
    show G.graph.Adj (f a).val (f b).val ↔ (⊤ : SimpleGraph (Fin 3)).Adj a b
    rw [show G.graph.Adj (f a).val (f b).val
          ↔ (f a).val ≠ (f b).val ∧ ((f a).val.val < 2 ∨ (f b).val.val < 2) from Iff.rfl, top_adj]
    constructor
    · rintro ⟨hne, _⟩ hab
      exact hne (by rw [hab])
    · intro hne
      refine ⟨fun hh => hne (hfinj (Subtype.ext hh)), ?_⟩
      by_contra hc
      push_neg at hc
      have ea : (f a).val = v := by
        rcases valS (f a) with hh | hh | hh
        · rw [hh] at hc; simp at hc
        · rw [hh] at hc; simp at hc
        · exact hh
      have eb : (f b).val = v := by
        rcases valS (f b) with hh | hh | hh
        · rw [hh] at hc; simp at hc
        · rw [hh] at hc; simp at hc
        · exact hh
      exact hne (hfinj (Subtype.ext (ea.trans eb.symm)))
  · funext t
    fin_cases t
    · show ef (triangleLabeled.type_embed 0) = IG.coe.type_embed 0
      apply Subtype.ext
      show (f 0).val = (IG.type_embed (0 : Fin 2)).val
      rw [hf0, IG.embed_eq 0, bookLabeled_type_embed_zero]
    · show ef (triangleLabeled.type_embed 1) = IG.coe.type_embed 1
      apply Subtype.ext
      show (f 1).val = (IG.type_embed (1 : Fin 2)).val
      rw [hf1, IG.embed_eq 1, bookLabeled_type_embed_one]

open LabeledSubgraph in
/-- **Backward iso.**  Conversely, if the labelled subgraph induced on `Sf` is flag-isomorphic to
`triangleLabeled`, then `Sf = {0, 1, v}` for a page `v ≠ 0, 1`. -/
private theorem triIso_bwd (n : ℕ) (Sf : Finset (Fin (n + 2)))
    (h : (bookLabeled n).type_verts ⊆ (↑Sf : Set (Fin (n + 2))))
    (hiso : Nonempty ((inducedLabeledSubgraph (bookLabeled n) (↑Sf) h).coe ≃f triangleLabeled)) :
    ∃ v, v ≠ 0 ∧ v ≠ 1 ∧ Sf = {0, 1, v} := by
  classical
  obtain ⟨φ⟩ := hiso
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by apply Fin.ne_of_val_ne; simp
  set IG := inducedLabeledSubgraph (bookLabeled n) (↑Sf) h with hIG
  have hverts : IG.subgraph.verts = (↑Sf : Set (Fin (n + 2))) := inducedLabeledSubgraph_verts _ _ h
  have hcard3 : Fintype.card ↥IG.subgraph.verts = 3 := by
    rw [Fintype.card_congr φ.graph_iso.toEquiv]; simp
  have hSfcard : Sf.card = 3 := by
    rw [← hcard3, Fintype.card_congr (Equiv.setCongr hverts), ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have h0Sf : (0 : Fin (n + 2)) ∈ Sf := by
    have hm : (0 : Fin (n + 2)) ∈ (bookLabeled n).type_verts :=
      LabeledGraph.mem_type_verts.mpr ⟨0, bookLabeled_type_embed_zero n⟩
    have := h hm; rwa [Finset.mem_coe] at this
  have h1Sf : (1 : Fin (n + 2)) ∈ Sf := by
    have hm : (1 : Fin (n + 2)) ∈ (bookLabeled n).type_verts :=
      LabeledGraph.mem_type_verts.mpr ⟨1, bookLabeled_type_embed_one n⟩
    have := h hm; rwa [Finset.mem_coe] at this
  have hsub01 : ({0, 1} : Finset (Fin (n + 2))) ⊆ Sf := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0Sf
    · exact h1Sf
  have hdiff : (Sf \ {0, 1}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub01, hSfcard, Finset.card_pair h01]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
  have hvmem : v ∈ Sf \ {0, 1} := hv ▸ Finset.mem_singleton_self v
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hvmem
  push_neg at hvmem
  refine ⟨v, hvmem.2.1, hvmem.2.2, ?_⟩
  calc Sf = {0, 1} ∪ (Sf \ {0, 1}) := (Finset.union_sdiff_of_subset hsub01).symm
    _ = {0, 1} ∪ {v} := by rw [hv]
    _ = {0, 1, v} := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

open LabeledSubgraph in
/-- **`lem:c5-book`, density part.**  Rooted at the edge `(0,1)`, the book `B_n` (with `n ≥ 1`) has
common-neighbour triangle density `1`: every page is adjacent to both roots, so every one-vertex
extension induces `F_△`.  (`τ`-typed analogue of `star_edge_density`.) -/
theorem book_Ftri_density (n : ℕ) (hn : 1 ≤ n) :
    flagDensity₁ triangleFF.2 (⟦bookLabeled n⟧ : Flag edgeType (Fin (n + 2))) = 1 := by
  classical
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by apply Fin.ne_of_val_ne; simp
  -- The labelled type vertices of `B_n` are exactly the two roots `{0, 1}`.
  have hbook_tv : (bookLabeled n).type_verts = (↑({0, 1} : Finset (Fin (n + 2))) : Set (Fin (n + 2))) := by
    ext x
    rw [LabeledGraph.mem_type_verts]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl⟩
      fin_cases t
      · exact Or.inl (bookLabeled_type_embed_zero n)
      · exact Or.inr (bookLabeled_type_embed_one n)
    · rintro (rfl | rfl)
      · exact ⟨0, bookLabeled_type_embed_zero n⟩
      · exact ⟨1, bookLabeled_type_embed_one n⟩
  -- The number of pages is `n`.
  have hpages_card : (Finset.univ.filter (fun v : Fin (n + 2) => v ≠ 0 ∧ v ≠ 1)).card = n := by
    have heq : (Finset.univ.filter (fun v : Fin (n + 2) => v ≠ 0 ∧ v ≠ 1))
        = ({0, 1} : Finset (Fin (n + 2)))ᶜ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
        Finset.mem_insert, Finset.mem_singleton, not_or]
    rw [heq, Finset.card_compl, Finset.card_pair h01, Fintype.card_fin]
    omega
  -- The numerator: the inducing `3`-subsets are exactly `{{0,1,v} : v a page}`.
  have hcount : (Finset.univ.filter (fun S : Finset (Fin (n + 2)) =>
        ∃ (hh : (bookLabeled n).type_verts ⊆ (↑S : Set (Fin (n + 2)))),
          Nonempty ((inducedLabeledSubgraph (bookLabeled n) (↑S) hh).coe ≃f triangleLabeled))).card
      = n := by
    have hset : (Finset.univ.filter (fun S : Finset (Fin (n + 2)) =>
          ∃ (hh : (bookLabeled n).type_verts ⊆ (↑S : Set (Fin (n + 2)))),
            Nonempty ((inducedLabeledSubgraph (bookLabeled n) (↑S) hh).coe ≃f triangleLabeled)))
        = (Finset.univ.filter (fun v : Fin (n + 2) => v ≠ 0 ∧ v ≠ 1)).image
            (fun v => ({0, 1, v} : Finset (Fin (n + 2)))) := by
      ext Sf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hh, hiso⟩
        obtain ⟨v, hv0, hv1, hSfeq⟩ := triIso_bwd n Sf hh hiso
        exact ⟨v, ⟨hv0, hv1⟩, hSfeq.symm⟩
      · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
        have hsub : (bookLabeled n).type_verts
            ⊆ (↑({0, 1, v} : Finset (Fin (n + 2))) : Set (Fin (n + 2))) := by
          rw [hbook_tv]
          intro x hx
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hx ⊢
          tauto
        exact ⟨hsub, triIso_fwd n v hv0 hv1 hsub⟩
    have hinjOn : Set.InjOn (fun v : Fin (n + 2) => ({0, 1, v} : Finset (Fin (n + 2))))
        (↑(Finset.univ.filter (fun v : Fin (n + 2) => v ≠ 0 ∧ v ≠ 1))) := by
      intro a ha b _ hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
      have hab' : ({0, 1, a} : Finset (Fin (n + 2))) = {0, 1, b} := hab
      have hmem : a ∈ ({0, 1, b} : Finset (Fin (n + 2))) := hab' ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hh | hh | hh
      · exact absurd hh ha.1
      · exact absurd hh ha.2
      · exact hh
    rw [hset, Finset.card_image_of_injOn hinjOn, hpages_card]
  -- The denominator: `C((n+2)-2, 3-2) = C(n,1) = n`.
  have hdenom : (((bookLabeled n).size - edgeType.size).choose
      (triangleLabeled.size - edgeType.size) : ℚ) = (n : ℚ) := by
    have hnat : ((bookLabeled n).size - edgeType.size).choose
        (triangleLabeled.size - edgeType.size) = n := by
      simp only [LabeledGraph.size, FlagType.size, Fintype.card_fin]
      rw [Nat.add_sub_cancel, show (3 : ℕ) - 2 = 1 from rfl, Nat.choose_one_right]
    rw [hnat]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  show flagDensity₁ (⟦triangleLabeled⟧ : Flag edgeType (Fin 3))
      (⟦bookLabeled n⟧ : Flag edgeType (Fin (n + 2))) = 1
  rw [flagDensity₁_eq_subset_count_div triangleLabeled (bookLabeled n), hcount, hdenom,
    div_self hn0]

/-- The underlying graph of `B_n` is in the `C₅`-free class. -/
theorem bookLabeled_mem (n : ℕ) : c5FreeClass.Mem (bookLabeled n).graph := book_c5free n

/-! ## `lem:c5-book`: a quotient point of triangle density `1` -/

/-- **`lem:c5-book`.**  There is a quotient point `ψ ∈ Q_τ` of the `C₅`-free class with
`ψ(F_△) = 1`, the limit of the book sequence rooted at its special edge. -/
theorem exists_book_Qτ_point :
    ∃ ψ ∈ Qσ (c5FreeClass.constraintOf edgeType).forbσ,
      (PositiveHomSpace.toPosHom ψ) F_tri = 1 := by
  -- The book sequence `B_{k+1}` (sizes `(k+1)+2` strictly increasing) of `C₅`-free flags whose
  -- `F_△`-densities are constantly `1`; its limit is the desired quotient point.
  set s : FlagSeq edgeType := fun k => ⟨(k + 1) + 2, ⟦bookLabeled (k + 1)⟧⟩ with hs
  have hinc : Increases s := by
    apply increases_of_consecutive_lt
    intro k
    show ((k + 1) + 2 : ℕ) < ((k + 1 + 1) + 2)
    omega
  have hmem : ∀ k, c5FreeClass.underlyingMem (unlabel (s k).2) := by
    intro k
    show c5FreeClass.underlyingMem (unlabel (⟦bookLabeled (k + 1)⟧ : Flag edgeType (Fin ((k + 1) + 2))))
    rw [c5FreeClass.underlyingMem_unlabel_mk]
    exact bookLabeled_mem (k + 1)
  have hlim : Tendsto (fun k => (flagDensity₁ triangleFF.2 (s k).2 : ℝ)) atTop (𝓝 1) := by
    have hconst : ∀ k, (flagDensity₁ triangleFF.2 (s k).2 : ℝ) = 1 := by
      intro k
      show (flagDensity₁ triangleFF.2 (⟦bookLabeled (k + 1)⟧ : Flag edgeType (Fin ((k + 1) + 2))) : ℝ) = 1
      rw [book_Ftri_density (k + 1) (by omega)]; norm_num
    simp only [hconst]; exact tendsto_const_nhds
  obtain ⟨ψ, hψQ, hψ⟩ := exists_Qσ_point_flag_eq c5FreeClass triangleFF s hinc hmem 1 hlim
  exact ⟨ψ, hψQ, hψ⟩

/-! ## `thm:c5-edge-not-root-plantable` -/

/-- **`thm:c5-edge-not-root-plantable`.**  The `C₅`-free graph class is not root-plantable at the
two-root edge type `τ`: `−F_△` is non-negative almost surely under every admissible edge random
extension, but is negative at a book-limit point of `Q_τ`. -/
theorem c5free_edge_not_rootPlantable :
    ¬ RootPlantable (c5FreeClass.constraintOf edgeType) := by
  refine pinning_obstruction (c5FreeClass.constraintOf edgeType) F_tri 0 ?_ ?_
  · intro φ₀ hφ₀ hσ
    exact ae_Ftri_eq_zero_of_pinned hφ₀ hσ
  · obtain ⟨ψ, hψQ, hψ⟩ := exists_book_Qτ_point
    exact ⟨ψ, hψQ, by rw [hψ]; norm_num⟩

/-! ## `cor:c5-no-pin`: no obstruction at the one-vertex type -/

/-- The one-root **triangle** flag over the one-vertex type: the three-vertex `vtype`-flag in which
the root and the two unlabelled vertices form a triangle (`K₃` on `Fin 3`, root `0`). -/
def triOverVtypeLabeled : LabeledGraph vtype (Fin 3) where
  graph := ⊤
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp [vtype] }

/-- The one-root triangle flag over the one-vertex type. -/
noncomputable def triOverVtypeFF : FinFlag vtype := ⟨3, (⟦triOverVtypeLabeled⟧ : Flag vtype (Fin 3))⟩

/-! ### Helper lemmas for `cor:c5-no-pin` -/

/-- The bound `N / C(N-1, 2) → 0` as `N → ∞` (squeezed by `8/N`).  This sends the one-root triangle
density `O(1/N)` to `0`. -/
private theorem card_div_choose_two_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) / ((N - 1).choose 2 : ℝ)) atTop (𝓝 0) := by
  have hub : Tendsto (fun N : ℕ => (8 : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)
  apply squeeze_zero' (g := fun N : ℕ => (8 : ℝ) / (N : ℝ)) ?_ ?_ hub
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 5] with N hN
    have hN5 : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hcast : ((N - 1).choose 2 : ℝ) = ((N : ℝ) - 1) * ((N : ℝ) - 2) / 2 := by
      rw [Nat.cast_choose_two]
      have h1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [h1]; ring
    rw [hcast]
    have hb : (0 : ℝ) < ((N : ℝ) - 1) * ((N : ℝ) - 2) / 2 := by
      have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
      positivity
    rw [div_le_div_iff₀ hb hpos]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (N : ℝ) - 5 by linarith) hpos.le, hN5]

/-- **Triangles through `v` ↔ edges of `G[N(v)]`** (a copy of the analogous private lemma in
`C5FewTriangles`, needed here because that one is not exported): the induced neighbourhood subgraph
`G[N(v)]` has as many edges as `G` has triangles containing `v`. -/
private lemma card_edgeFinset_induce_nbhd_eq {N : ℕ} (G : SimpleGraph (Fin N)) (v : Fin N) :
    (G.induce (G.neighborSet v)).edgeFinset.card
      = ((G.cliqueFinset 3).filter (fun t => v ∈ t)).card := by
  classical
  have hmap := map_edgeFinset_induce (G := G) (s := G.neighborSet v)
  have hcard1 : (G.induce (G.neighborSet v)).edgeFinset.card
      = (G.edgeFinset ∩ (G.neighborSet v).toFinset.sym2).card := by
    rw [← hmap, Finset.card_map]
  rw [hcard1]
  apply Finset.card_bij (fun e _ => insert v e.toFinset)
  · intro e he
    induction e with
    | _ a b =>
      rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff,
        Set.mem_toFinset, Set.mem_toFinset, mem_neighborSet, mem_neighborSet] at he
      obtain ⟨hadjab, hva, hvb⟩ := he
      rw [Sym2.toFinset_mk_eq, Finset.mem_filter, mem_cliqueFinset_iff]
      exact ⟨is3Clique_triple_iff.mpr ⟨hva, hvb, hadjab⟩, Finset.mem_insert_self v _⟩
  · intro e1 he1 e2 he2 heq
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
  · intro t ht
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

/-- **Witness assembly at the empty type.**  An increasing sequence of in-class unlabelled flags has a
subsequence whose limit is a positive homomorphism `φ₀` landing in `Q₀ = Qσ (...).forb0`, and whose
densities converge to `φ₀`'s values.  (The `∅ₜ`-typed analogue of `exists_Qσ_point_flag_eq`,
returning the underlying homomorphism so its base value can be read off.) -/
private theorem exists_Q0_point (s : FlagSeq ∅ₜ) (hinc : Increases s)
    (hmem : ∀ n, c5FreeClass.underlyingMem (s n).2) :
    ∃ (φ₀ : PositiveHom ∅ₜ) (ϕ : ℕ → ℕ), StrictMono ϕ ∧
      posHomPoint φ₀ ∈ Qσ (c5FreeClass.constraintOf vtype).forb0 ∧
      ∀ F : FinFlag ∅ₜ, Tendsto (fun k => (flagDensity₁ F.2 (s (ϕ k)).2 : ℝ)) atTop
        (𝓝 (φ₀.coe F)) := by
  classical
  obtain ⟨a, ϕ, hmono, hconv⟩ := increasing_flagSeq_contain_convergent_subseq s hinc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (s ∘ ϕ) hconv
  obtain ⟨_, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  have hclass : ∀ (k : ℕ), c5FreeClass.Mem ((s (ϕ k)).2.out).graph := by
    intro k
    have hm := hmem (ϕ k)
    rw [← Quotient.out_eq (s (ϕ k)).2, c5FreeClass.underlyingMem_mk] at hm
    exact hm
  have hφcoe : ∀ F, φ.coe F = a F := fun F => by rw [hφ]
  refine ⟨φ, ϕ, hmono, ?_, ?_⟩
  · rw [mem_Qσ_iff]
    intro D hD
    have hval : (posHomPoint φ).val D = a D := by
      rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
    rw [hval]
    have hforbσ : (c5FreeClass.constraintOf ∅ₜ).forbσ D := by
      show ¬ c5FreeClass.underlyingMem (unlabel D.2)
      rw [unlabel_emptyType]; exact hD
    have hzero : ∀ k, (flagDensity₁ D.2 (s (ϕ k)).2 : ℝ) = 0 := by
      intro k
      rw [← Quotient.out_eq (s (ϕ k)).2]
      exact_mod_cast flagDensity_forbidden_eq_zero_of_mem c5FreeClass _ (hclass k) D hforbσ
    have hD_tendsto : Tendsto (fun k => (flagDensity₁ D.2 (s (ϕ k)).2 : ℝ)) atTop
        (𝓝 (a D)) := hpt D
    have h0 : Tendsto (fun k => (flagDensity₁ D.2 (s (ϕ k)).2 : ℝ)) atTop (𝓝 0) := by
      simp only [hzero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hD_tendsto h0
  · intro F
    rw [hφcoe F]
    exact hpt F

/-- The edgeless graph `⊥` on `Fin N` is `C₅`-free (no edges at all). -/
private theorem bot_c5free (N : ℕ) : C5g.Free (⊥ : SimpleGraph (Fin N)) := by
  rintro ⟨φ⟩
  have h := φ.toHom.map_adj (show C5g.Adj 0 1 by decide)
  simp only [SimpleGraph.bot_adj] at h

/-- The balanced complete bipartite graph `K_{m,m}` on `Fin (2·m)`, split into the first and second
halves by `· < m`. -/
private def biPartGraph (m : ℕ) : SimpleGraph (Fin (2 * m)) where
  Adj i j := (i.val < m) ≠ (j.val < m)
  symm := fun _ _ h => Ne.symm h
  loopless := fun _ h => h rfl

/-- `K_{m,m}` is bipartite, hence has no odd cycle, hence is `C₅`-free: a `C₅`-copy would `2`-colour
the `5`-cycle by the side predicate, a parity contradiction. -/
private theorem biPartGraph_c5free (m : ℕ) : C5g.Free (biPartGraph m) := by
  rintro ⟨φ⟩
  set f := φ.toHom with hf
  have key : ∀ c0 c1 c2 c3 c4 : Bool, c0 ≠ c1 → c1 ≠ c2 → c2 ≠ c3 → c3 ≠ c4 → c4 ≠ c0 → False := by
    intro c0 c1 c2 c3 c4 h01 h12 h23 h34 h40
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;>
      first
        | exact absurd rfl h01
        | exact absurd rfl h12
        | exact absurd rfl h23
        | exact absurd rfl h34
        | exact absurd rfl h40
  have hadj : ∀ i j : Fin 5, C5g.Adj i j →
      decide ((f i).val < m) ≠ decide ((f j).val < m) := by
    intro i j hij
    have h : ((f i).val < m) ≠ ((f j).val < m) := f.map_adj hij
    intro heq
    exact h (propext (decide_eq_decide.mp heq))
  exact key _ _ _ _ _ (hadj 0 1 (by decide)) (hadj 1 2 (by decide)) (hadj 2 3 (by decide))
    (hadj 3 4 (by decide)) (hadj 4 0 (by decide))

/-- The first half `{j : j.val < m}` of `Fin (2·m)` has exactly `m` elements. -/
private lemma card_fin_lt (m : ℕ) :
    (Finset.univ.filter (fun j : Fin (2 * m) => j.val < m)).card = m := by
  have key : Finset.univ.filter (fun j : Fin (2 * m) => j.val < m)
      = Finset.image (Fin.castLE (show m ≤ 2 * m by omega)) Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, by apply Fin.ext; rfl⟩
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact i.isLt
  rw [key, Finset.card_image_of_injective _ (Fin.castLE_injective _), Finset.card_univ,
    Fintype.card_fin]

/-- Every vertex of `K_{m,m}` has degree `m`. -/
private lemma biPartGraph_degree (m : ℕ) (v : Fin (2 * m)) : (biPartGraph m).degree v = m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v.val < m
  · have hnb : (biPartGraph m).neighborFinset v
        = Finset.univ.filter (fun j : Fin (2 * m) => ¬ (j.val < m)) := by
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      show ((v.val < m) ≠ (j.val < m)) ↔ ¬ (j.val < m)
      constructor
      · intro hadj hjm
        exact hadj (propext ⟨fun _ => hjm, fun _ => hv⟩)
      · intro hjm heq
        rw [eq_iff_iff] at heq
        exact hjm (heq.mp hv)
    rw [hnb]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * m))))
      (fun j => j.val < m)
    rw [card_fin_lt, Finset.card_univ, Fintype.card_fin] at h
    omega
  · have hnb : (biPartGraph m).neighborFinset v
        = Finset.univ.filter (fun j : Fin (2 * m) => j.val < m) := by
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      show ((v.val < m) ≠ (j.val < m)) ↔ (j.val < m)
      constructor
      · intro hadj
        by_contra hjm
        exact hadj (propext ⟨fun h => absurd h hv, fun h => absurd h hjm⟩)
      · intro hjm heq
        rw [eq_iff_iff] at heq
        exact hv (heq.mpr hjm)
    rw [hnb, card_fin_lt]

/-- `K_{m,m}` has exactly `m²` edges (`2·#edges = ∑ deg = 2m·m`). -/
private lemma biPartGraph_card_edges (m : ℕ) : (biPartGraph m).edgeFinset.card = m * m := by
  have hsum : ∑ v : Fin (2 * m), (biPartGraph m).degree v = 2 * (m * m) := by
    simp_rw [biPartGraph_degree]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h2 : 2 * (biPartGraph m).edgeFinset.card = 2 * (m * m) := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, hsum]
  omega

/-- The unlabelled edge `K₂` as a `∅ₜ`-flag (a local copy of `C4Free.unlabelledEdgeFlag`, which is
not in this file's import closure). -/
private noncomputable def uEdgeFlag : Flag ∅ₜ (Fin 2) := graphFlag edgeGraph

/-- For the empty type a labelled-graph isomorphism is the same datum as a plain graph isomorphism
(`type_preserve` is vacuous since `Fin 0` is empty).  Local copy. -/
private lemma emptyf_iso_iff' {V W : Type} (A : LabeledGraph ∅ₜ V) (B : LabeledGraph ∅ₜ W) :
    Nonempty (A ≃f B) ↔ Nonempty (A.graph ≃g B.graph) := by
  constructor
  · rintro ⟨f⟩; exact ⟨f.graph_iso⟩
  · rintro ⟨g⟩; exact ⟨⟨g, funext (fun t => (IsEmpty.false t).elim)⟩⟩

/-- The subgraph of `G` induced on `S` is isomorphic to the single edge `⊤` on `Fin 2` exactly when
`S` is a pair `{u, w}` of distinct adjacent vertices.  Local copy of `C4Free.induced_iso_top_iff`. -/
private lemma induced_iso_edge_iff {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
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

/-- The `2`-vertex edge-inducing subsets are in bijection with `G.edgeFinset`.  Local copy of
`C4Free.count_edges`. -/
private lemma count_edge_subsets {N : ℕ} (G : SimpleGraph (Fin N)) :
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

/-- The unlabelled-edge density of a finite graph is `e(G)/C(N,2)`.  Local copy of
`C4Free.flagDensity_unlabelledEdge_eq`. -/
private theorem flagDensity_uEdge_eq {N : ℕ} (G : SimpleGraph (Fin N)) :
    flagDensity₁ uEdgeFlag (graphFlag G) = (G.edgeFinset.card : ℚ) / (N.choose 2) := by
  unfold uEdgeFlag graphFlag edgeGraph
  rw [flagDensity₁_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, emptyType_size, Nat.sub_zero]
  congr 1
  norm_cast
  rw [← count_edge_subsets G]
  congr 1
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨_, hiso⟩
    rw [emptyf_iso_iff'] at hiso
    exact (induced_iso_edge_iff G S).mp hiso
  · intro hex
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [LabeledGraph.type_verts, Set.image_univ, Set.mem_range] at hx
      obtain ⟨t, _⟩ := hx; exact (IsEmpty.false t).elim
    · rw [emptyf_iso_iff']
      exact (induced_iso_edge_iff G S).mpr hex

/-- `unlabel edgeFF.2` is the unlabelled edge `K₂`. -/
private theorem unlabel_edgeFF : unlabel edgeFF.2 = uEdgeFlag := by
  show unlabel (⟦edgeLabeled⟧ : Flag vtype (Fin 2)) = graphFlag edgeGraph
  apply Quotient.sound
  refine ⟨{ graph_iso := SimpleGraph.Iso.refl, type_preserve := ?_ }⟩
  funext z; exact Fin.elim0 z

open LabeledSubgraph in
/-- **`cor:c5-no-pin` (triangle half).**  The one-root triangle flag over the one-vertex type has
density `0` at *every* quotient point of the `C₅`-free class: the number of triangles through a
vertex is `≤ deg(v) ≤ n` (`lem:c5-nbhd`), so the one-root triangle density is `O(1/n)` and vanishes
in the limit.  Thus this flag is pinned at `0` while the quotient also attains only `0` — no pinning
obstruction arises. -/
theorem c5free_triOverVtype_zero_on_Qvtype
    (χ : PositiveHomSpace vtype) (hχ : χ ∈ Qσ (c5FreeClass.constraintOf vtype).forbσ) :
    (PositiveHomSpace.toPosHom χ) ⟦basisVector triOverVtypeFF⟧ = 0 := by
  classical
  set forbσ := (c5FreeClass.constraintOf vtype).forbσ with hforbσdef
  -- `(toPosHom χ)` vanishes on every forbidden flag.
  have hψ : ∀ F : FinFlag vtype, forbσ F → (PositiveHomSpace.toPosHom χ).coe F = 0 := by
    intro F hF
    rw [PositiveHom.coe_flag, PositiveHomSpace.toPosHom_basisVector]
    exact (mem_Qσ_iff forbσ χ).mp hχ F hF
  -- A forbidden-free vtype-flag sequence converging to `(toPosHom χ).coe`.
  obtain ⟨s, hconv, hff⟩ := exists_constrained_flagSeq_limit (PositiveHomSpace.toPosHom χ) forbσ hψ
  rw [flagSeq_convergesTo_iff] at hconv
  obtain ⟨hinc, hconvF⟩ := hconv
  -- Each representing graph is `C₅`-free.
  have hfree : ∀ t, C5g.Free ((s t).2.out.graph) := by
    intro t
    apply HeredClass.mem_of_forbiddenFree c5FreeClass ((s t).2.out)
    intro F hForb
    have hzero := hff t F hForb
    rwa [← Quotient.out_eq (s t).2] at hzero
  -- The per-term density bound: `p(F_△, sₜ) ≤ nₜ / C(nₜ-1, 2)` once `nₜ ≥ 3`.
  have hbound : ∀ t, 3 ≤ (s t).1 →
      flagDensitySeq s t triOverVtypeFF ≤ ((s t).1 : ℝ) / (((s t).1 - 1).choose 2 : ℝ) := by
    intro t _
    show (flagDensity₁ triOverVtypeFF.2 (s t).2 : ℝ) ≤ _
    set n := (s t).1 with hn
    set H := (s t).2.out with hH
    set r := H.type_embed 0 with hr
    have hst2 : (s t).2 = (⟦H⟧ : Flag vtype (Fin n)) := (Quotient.out_eq (s t).2).symm
    -- Flag density as a subset-count.
    have hdens : flagDensity₁ triOverVtypeFF.2 (s t).2
        = ((Finset.univ.filter (fun S : Finset (Fin n) =>
            ∃ (h : H.type_verts ⊆ (↑S : Set (Fin n))),
              Nonempty ((inducedLabeledSubgraph H (↑S) h).coe ≃f triOverVtypeLabeled))).card : ℚ)
          / ((H.size - vtype.size).choose (triOverVtypeLabeled.size - vtype.size)) := by
      rw [show triOverVtypeFF.2 = (⟦triOverVtypeLabeled⟧ : Flag vtype (Fin 3)) from rfl, hst2]
      exact flagDensity₁_eq_subset_count_div triOverVtypeLabeled H
    -- The inducing 3-subsets are 3-cliques of `G` through the root `r`.
    have hsubset : (Finset.univ.filter (fun S : Finset (Fin n) =>
          ∃ (h : H.type_verts ⊆ (↑S : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph H (↑S) h).coe ≃f triOverVtypeLabeled)))
        ⊆ ((H.graph.cliqueFinset 3).filter (fun S => r ∈ S)) := by
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨h, hiso⟩ := hS
      obtain ⟨φ⟩ := hiso
      rw [Finset.mem_filter, mem_cliqueFinset_iff]
      refine ⟨(induced_iso_top3_iff H.graph S).mp ⟨φ.graph_iso⟩, ?_⟩
      have hr_mem : r ∈ H.type_verts := LabeledGraph.mem_type_verts.mpr ⟨0, rfl⟩
      have hmem := h hr_mem
      rwa [Finset.mem_coe] at hmem
    -- Hence the numerator is at most `n`.
    have hnumle : (Finset.univ.filter (fun S : Finset (Fin n) =>
          ∃ (h : H.type_verts ⊆ (↑S : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph H (↑S) h).coe ≃f triOverVtypeLabeled))).card ≤ n := by
      calc _ ≤ ((H.graph.cliqueFinset 3).filter (fun S => r ∈ S)).card := Finset.card_le_card hsubset
        _ = (H.graph.induce (H.graph.neighborSet r)).edgeFinset.card :=
              (card_edgeFinset_induce_nbhd_eq H.graph r).symm
        _ ≤ Fintype.card (H.graph.neighborSet r) :=
              c5free_neighborhood_edge_card_le H.graph (hfree t) r
        _ ≤ n := by
              have h1 : (H.graph.neighborFinset r).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
              rw [Fintype.card_fin] at h1
              rwa [H.graph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    -- The denominator is `C(n-1, 2)`.
    have hdenomeq : (H.size - vtype.size).choose (triOverVtypeLabeled.size - vtype.size)
        = (n - 1).choose 2 := by
      rw [hn]
      norm_num [LabeledGraph.size, FlagType.size, Fintype.card_fin]
    rw [hdens, hdenomeq]
    have hnum' : ((Finset.univ.filter (fun S : Finset (Fin n) =>
          ∃ (h : H.type_verts ⊆ (↑S : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph H (↑S) h).coe ≃f triOverVtypeLabeled))).card : ℝ)
        ≤ (n : ℝ) := by exact_mod_cast hnumle
    have hden0 : (0 : ℝ) ≤ (((n - 1).choose 2 : ℕ) : ℝ) := by positivity
    push_cast
    exact div_le_div_of_nonneg_right hnum' hden0
  -- Squeeze the density to `0`.
  have hub : Tendsto (fun t => ((s t).1 : ℝ) / (((s t).1 - 1).choose 2 : ℝ)) atTop (𝓝 0) :=
    card_div_choose_two_tendsto_zero.comp hinc.tendsto_atTop
  have hd0 : Tendsto (fun t => flagDensitySeq s t triOverVtypeFF) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t => ((s t).1 : ℝ) / (((s t).1 - 1).choose 2 : ℝ)) ?_ ?_ hub
    · filter_upwards with t
      show (0 : ℝ) ≤ (flagDensity₁ triOverVtypeFF.2 (s t).2 : ℝ)
      exact_mod_cast flagListDensity₁_ge_zero triOverVtypeFF.2 (s t).2
    · obtain ⟨T, hT⟩ := hinc.eventually_ge 3
      filter_upwards [eventually_ge_atTop T] with t ht
      exact hbound t (hT t ht)
  have hgoal : (PositiveHomSpace.toPosHom χ).coe triOverVtypeFF = 0 :=
    tendsto_nhds_unique (hconvF triOverVtypeFF) hd0
  rw [← PositiveHom.coe_flag]
  exact hgoal

/-- **`cor:c5-no-pin` (edge half).**  The one-root edge flag is *not* pinned: there are two
constrained unlabelled limits assigning the unlabelled edge densities `0` (edgeless graphs) and
`1/2` (balanced complete bipartite graphs); under random rooting these give distinct almost-sure
one-root edge densities, so no single value is pinned. -/
theorem c5free_edge_not_pinned :
    ∃ φ₀ φ₀' : PositiveHom ∅ₜ,
      posHomPoint φ₀ ∈ Qσ (c5FreeClass.constraintOf vtype).forb0 ∧
      posHomPoint φ₀' ∈ Qσ (c5FreeClass.constraintOf vtype).forb0 ∧
      φ₀ ρ ≠ φ₀' ρ := by
  classical
  -- The base value of `ρ` is a fixed positive multiple of the unlabelled-edge density.
  have hFF : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, uEdgeFlag⟩ := by
    show (⟨2, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, uEdgeFlag⟩
    rw [unlabel_edgeFF]
  have hρ : ∀ ψ : PositiveHom ∅ₜ,
      ψ ρ = (downwardNormalizingFactor edgeFF.2 : ℝ) * ψ.coe ⟨2, uEdgeFlag⟩ := by
    intro ψ
    show ψ (downward e) = _
    rw [e, downward_basisVector, PositiveHom.map_smul, hFF, ← PositiveHom.coe_flag]
  have hdnf : (0 : ℝ) < (downwardNormalizingFactor edgeFF.2 : ℝ) := by
    exact_mod_cast downwardNormalizingFactor_pos edgeFF.2
  -- The edgeless sequence: `C₅`-free graphs of edge density `0`.
  set s_e : FlagSeq ∅ₜ := fun k => ⟨k + 2, graphFlag (⊥ : SimpleGraph (Fin (k + 2)))⟩ with hs_e
  have hinc_e : Increases s_e :=
    increases_of_consecutive_lt (fun k => by show k + 2 < (k + 1) + 2; omega)
  have hmem_e : ∀ k, c5FreeClass.underlyingMem (s_e k).2 := by
    intro k
    show c5FreeClass.underlyingMem (graphFlag (⊥ : SimpleGraph (Fin (k + 2))))
    exact bot_c5free (k + 2)
  -- The balanced complete bipartite sequence: `C₅`-free graphs of edge density `→ 1/2`.
  set s_b : FlagSeq ∅ₜ := fun k => ⟨2 * (k + 1), graphFlag (biPartGraph (k + 1))⟩ with hs_b
  have hinc_b : Increases s_b :=
    increases_of_consecutive_lt (fun k => by show 2 * (k + 1) < 2 * ((k + 1) + 1); omega)
  have hmem_b : ∀ k, c5FreeClass.underlyingMem (s_b k).2 := by
    intro k
    show c5FreeClass.underlyingMem (graphFlag (biPartGraph (k + 1)))
    exact biPartGraph_c5free (k + 1)
  obtain ⟨φ₀, ϕ₀, _, hφ₀mem, hφ₀tend⟩ := exists_Q0_point s_e hinc_e hmem_e
  obtain ⟨φ₀', ϕ₀', _, hφ₀'mem, hφ₀'tend⟩ := exists_Q0_point s_b hinc_b hmem_b
  refine ⟨φ₀, φ₀', hφ₀mem, hφ₀'mem, ?_⟩
  -- Edgeless: the unlabelled-edge coefficient is `0`.
  have hzero : φ₀.coe ⟨2, uEdgeFlag⟩ = 0 := by
    have hterm : ∀ k, (flagDensity₁ (⟨2, uEdgeFlag⟩ : FinFlag ∅ₜ).2 (s_e (ϕ₀ k)).2 : ℝ)
        = 0 := by
      intro k
      show (flagDensity₁ uEdgeFlag
        (graphFlag (⊥ : SimpleGraph (Fin (ϕ₀ k + 2)))) : ℝ) = 0
      rw [flagDensity_uEdge_eq]
      simp
    have h0 : Tendsto (fun k => (flagDensity₁ (⟨2, uEdgeFlag⟩ : FinFlag ∅ₜ).2
        (s_e (ϕ₀ k)).2 : ℝ)) atTop (𝓝 0) := by
      simp only [hterm]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hφ₀tend ⟨2, uEdgeFlag⟩) h0
  -- Bipartite: the unlabelled-edge coefficient is `≥ 1/4`.
  have hpos : (1 : ℝ) / 4 ≤ φ₀'.coe ⟨2, uEdgeFlag⟩ := by
    have hterm : ∀ k, (1 : ℝ) / 4 ≤ (flagDensity₁ (⟨2, uEdgeFlag⟩ : FinFlag ∅ₜ).2
        (s_b (ϕ₀' k)).2 : ℝ) := by
      intro k
      show (1 : ℝ) / 4 ≤ (flagDensity₁ uEdgeFlag
        (graphFlag (biPartGraph (ϕ₀' k + 1))) : ℝ)
      set p := ϕ₀' k + 1 with hp
      have hp1 : 1 ≤ p := by omega
      have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      rw [flagDensity_uEdge_eq, biPartGraph_card_edges]
      push_cast
      have hden : (((2 * p).choose 2 : ℕ) : ℝ) = (p : ℝ) * (2 * (p : ℝ) - 1) := by
        rw [Nat.cast_choose_two]; push_cast; ring
      rw [hden, le_div_iff₀ (by nlinarith [hpR] : (0 : ℝ) < (p : ℝ) * (2 * (p : ℝ) - 1))]
      nlinarith [hpR]
    exact ge_of_tendsto' (hφ₀'tend ⟨2, uEdgeFlag⟩) hterm
  rw [hρ φ₀, hρ φ₀', hzero, mul_zero]
  exact ne_of_lt (mul_pos hdnf (by linarith [hpos]))

end FlagAlgebras.MetaTheory
