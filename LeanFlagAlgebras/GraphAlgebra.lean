import «LeanFlagAlgebras».SubgraphDensity

import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Unique

open Finset
open SimpleGraph
open Classical

-- set of all graphs (up to isomorphism) on n vertices
def IsoSimpleGraphWithSize (n : ℕ) : Type
  := QuotSimpleGraph (Fin n)

instance (n : ℕ) : Inhabited (IsoSimpleGraphWithSize n) where
  default := ⟦emptyGraph (Fin n)⟧

instance : Unique (IsoSimpleGraphWithSize 0) where
  uniq := by
    intro G
    have : G = ⟦Quotient.out G⟧ := by simp only [Quotient.out_eq]
    rw [this]
    apply Quotient.sound
    let H := Quotient.out G
    show graph_eqv H (emptyGraph (Fin 0))
    have H_iso : H ≃g emptyGraph (Fin 0) :=
      ⟨Equiv.refl _, by
        intro u v
        exact False.elim (Fin.elim0 u)
      ⟩
    exact Nonempty.intro H_iso

noncomputable instance (n : ℕ) : Fintype (IsoSimpleGraphWithSize n)
  := quotSimpleGraphFintype (Fin n)

-- set of all graphs (up to isomorphism) on a finite vertex set
def IsoSimpleGraph : Type
  := Σ (n : ℕ), IsoSimpleGraphWithSize n

instance : One IsoSimpleGraph where
  one := ⟨0, (default : IsoSimpleGraphWithSize 0)⟩

abbrev GraphVector : Type
  := IsoSimpleGraph →₀ ℝ

noncomputable instance : HMul ℝ GraphVector GraphVector where
  hMul r g := r • g

noncomputable instance : AddCommMonoid GraphVector
  := Finsupp.instAddCommMonoid

noncomputable instance : AddCommGroup GraphVector
  := Finsupp.instAddCommGroup

noncomputable instance : Module ℝ GraphVector
  := Finsupp.module IsoSimpleGraph ℝ

noncomputable def basisElementFromGraph (G : IsoSimpleGraph) : GraphVector
  := Finsupp.single G 1

lemma basisElementFromGraph_support
    (G : IsoSimpleGraph)
    : (basisElementFromGraph G).support = {G}
  := by
  dsimp [basisElementFromGraph]
  rw [Finsupp.support_single_ne_zero _ (by simp)]

lemma graphVector_eq_sum_basisElement
    (g : GraphVector)
    : g = ∑ G in g.support, g G • basisElementFromGraph G
  := by
  dsimp [basisElementFromGraph]
  rw [← Finsupp.sum_single g]
  apply sum_congr
  · simp
  · intros; simp

noncomputable instance : One GraphVector where
  one := basisElementFromGraph 1

lemma subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0
    [Fintype V] {G : SimpleGraph V} {H : Subgraph G}
    : H = ⊥ ↔ Nonempty (H.coe ≃g (emptyGraph (Fin 0)))
  := by
  constructor
  . intro h_eq
    rw [h_eq]
    have f_iso : (⊥ : Subgraph G).verts ≃ Fin 0 := Fintype.equivFinOfCardEq (by simp)
    exact Nonempty.intro ⟨f_iso, by simp⟩
  . intro h_iso
    have h_verts : H.verts = ∅ := by
      ext u
      constructor
      . intro h_u
        let u' : Fin 0 := h_iso.some ⟨u, h_u⟩
        exact Fin.elim0 u'
      . exact False.elim
    simp_all [Subgraph.ext_iff, Set.ext_iff]
    ext u v
    simp
    intro h_uv
    have : u ∈ H.verts := H.edge_vert h_uv
    exact h_verts u this

lemma subgraphPairCount_one
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphPairCount (emptyGraph (Fin 0)) H G = subgraphCount H G
  := by
  dsimp [subgraphPairCount, subgraphCount]
  let S₀ := { (G', G'') : Subgraph G × Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g (emptyGraph (Fin 0))) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H) ∧
                G'.verts ∩ G''.verts = ∅ }
  let S₁ := { G' : Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  show S₀.toFinset.card = S₁.toFinset.card
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    let f : Subgraph G × Subgraph G → Subgraph G :=
      fun ⟨_, G''⟩ => G''
    have h_f_S₀_S₁ : Set.MapsTo f S₀ S₁ :=
      fun ⟨_, G''⟩ ⟨_,_,h₃,h₄,_⟩ => ⟨h₃, h₄⟩
    have h_f_inj : Set.InjOn f S₀ := by
      intro ⟨G₀,G₁⟩ ⟨_,h₂,_,_⟩ ⟨G'₀,G'₁⟩ ⟨_,h₂',_,_⟩ h_eq
      dsimp [f] at h_eq
      simp [h_eq]
      have h_G₀ : G₀ = ⊥ := subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mpr h₂
      have h_G₀' : G'₀ = ⊥ := subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mpr h₂'
      rw [h_G₀, h_G₀']
    have h_f_surj : Set.SurjOn f S₀ S₁ := by
      intro G'' ⟨h₁,h₂⟩
      use ⟨⊥, G''⟩
      simp
      have h_bot_isinduced : (⊥ : Subgraph G).IsInduced := by
        dsimp [Subgraph.IsInduced]
        intro u _ h_u _ _
        exact False.elim h_u
      have h_bot_iso : Nonempty ((⊥ : Subgraph G).coe ≃g (emptyGraph (Fin 0))) :=
        subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mp rfl
      exact ⟨h_bot_isinduced, h_bot_iso, h₁, h₂, Disjoint.inter_eq fun _ a _ ↦ a⟩
    exact Set.BijOn.equiv f (Set.BijOn.mk h_f_S₀_S₁ h_f_inj h_f_surj)
  have h_count : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]

lemma subgraphPairDensity_one
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphPairDensity (emptyGraph (Fin 0)) H G  = subgraphDensity H G
  := by
  dsimp [subgraphPairDensity, subgraphDensity]
  rw [←subgraphPairCount_one H G]
  simp

lemma quotSubgraphPairDensity_one
    (H : IsoSimpleGraphWithSize n) (G : IsoSimpleGraphWithSize m)
    : quotSubgraphPairDensity (1 : IsoSimpleGraph).2 H G = quotSubgraphDensity H G
  := by
  rcases Quotient.exists_rep (1 : IsoSimpleGraph).2 with ⟨Orep, hOrep⟩
  rcases Quotient.exists_rep H with ⟨Hrep, hHrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [<- hOrep, ← hHrep, ← hGrep]
  have orep_eq_empty : Orep = emptyGraph (Fin 0) := by
    exact edgeFinset_inj.mp rfl
  rw [orep_eq_empty]
  exact subgraphPairDensity_one Hrep Grep

noncomputable def finiteGraphModuleBasis
    : Basis IsoSimpleGraph ℝ GraphVector
  :=
  have h_indep : LinearIndependent ℝ basisElementFromGraph := by
    rw [linearIndependent_iff'']
    intro s f h_supp h_sum G
    by_cases hG : G ∈ s
    · have : (∑ i ∈ s, f i • basisElementFromGraph i) G = 0 := by
        simp [h_sum]
      rw [← this, sum_eq_sum_diff_singleton_add hG _]
      simp [basisElementFromGraph, sum_apply']
      rw [sum_eq_zero]
      intro H hH
      have hHG : H ≠ G := by
        simp_all only [Finsupp.coe_zero, Pi.zero_apply, mem_sdiff, mem_singleton, ne_eq, not_false_eq_true]
      exact Finsupp.single_apply_eq_zero.mpr fun a ↦ h_supp H fun _ ↦ hHG (id (Eq.symm a))
    · exact h_supp G hG
  have h_span : ∀ f, f ∈ Submodule.span ℝ (Set.range basisElementFromGraph) := by
    intro f
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use f
    ext G
    simp [basisElementFromGraph]
  Basis.mk h_indep (fun v _ ↦ h_span v)

-- GraphVector is a free ℝ-module generated by IsoSimpleGraph
instance : Module.Free ℝ GraphVector := by
  apply Module.Free.of_basis
  exact finiteGraphModuleBasis

noncomputable def densityGraphSum
    (G : IsoSimpleGraph) (ℓ : ℕ) : GraphVector
  :=
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ F in ℓ_graphs, (quotSubgraphDensity G.2 F) • basisElementFromGraph ⟨ℓ, F⟩

noncomputable def zeroElement
    (G : IsoSimpleGraph) (ℓ : ℕ)
    : GraphVector
  := basisElementFromGraph G - densityGraphSum G ℓ

noncomputable def zeroSpanSet : Set GraphVector
  :=
  let S (G : IsoSimpleGraph) := (zeroElement G) '' {ℓ | G.1 ≤ ℓ}
  ⋃₀ Set.range S

lemma zeroSpanSet_eq_zeroElement
    (hk : k ∈ zeroSpanSet)
    : ∃ (G : IsoSimpleGraph) (ℓ : ℕ), k = zeroElement G ℓ
  := by
  simp [zeroSpanSet] at hk
  rcases hk with ⟨G, ℓ, hk⟩
  exact ⟨G, ℓ, (by simp_all only)⟩

noncomputable def ZeroSet : Submodule ℝ GraphVector
  :=
  Submodule.span ℝ zeroSpanSet

lemma zeroSet_eq_sum_spanElement
    {k : GraphVector} (h_zero : k ∈ ZeroSet)
    : ∃ (I : Type) (hI : Fintype I) (c : I → ℝ) (v : I → GraphVector),
    (∀ i, v i ∈ zeroSpanSet) ∧ (k = ∑ i, c i • v i)
  := by
  sorry

lemma zeroSet_closed_under_add
    (h₁ h₂ : GraphVector) (h₁_zero : h₁ ∈ ZeroSet) (h₂_zero : h₂ ∈ ZeroSet)
    : h₁ + h₂ ∈ ZeroSet
  := by
  apply Submodule.add_mem <;> assumption

lemma zeroSet_closed_under_sum
    (S : Finset α) (f : α → GraphVector) (h_zero : ∀ G ∈ S, f G ∈ ZeroSet)
    : ∑ G ∈ S, f G ∈ ZeroSet
  := by
  apply Submodule.sum_mem
  assumption

lemma zeroSet_closed_under_smul
    (r : ℝ) (h : GraphVector) (h_zero : h ∈ ZeroSet)
    : r • h ∈ ZeroSet
  := by
  apply SMulMemClass.smul_mem
  assumption

def graph_algebra_eqv (g h : GraphVector) : Prop
  :=
  g - h ∈ ZeroSet

theorem graph_algebra_eqv.refl
    (g : GraphVector) : graph_algebra_eqv g g
  := by
  rw [graph_algebra_eqv]
  simp

theorem graph_algebra_eqv.symm
    : ∀ {g h : GraphVector}, graph_algebra_eqv g h → graph_algebra_eqv h g
  :=
  sub_mem_comm_iff.mp

theorem graph_algebra_eqv.trans
    : ∀ {f g h : GraphVector}, graph_algebra_eqv f g → graph_algebra_eqv g h → graph_algebra_eqv f h
  := by
  intros f g h hfg hgh
  rw [graph_algebra_eqv] at *
  have : f - h = (f - g) + (g - h) := by simp
  rw [this]
  exact zeroSet_closed_under_add (f - g) (g - h) hfg hgh

instance graphVectorSetoid
    : Setoid GraphVector
  where
    r     := graph_algebra_eqv
    iseqv := {
      refl := graph_algebra_eqv.refl,
      symm := graph_algebra_eqv.symm,
      trans := graph_algebra_eqv.trans
    }

abbrev GraphAlgebra : Type :=
  Quotient graphVectorSetoid

noncomputable instance : Add GraphAlgebra where
  add := by
    apply Quotient.map₂ (· + ·)
    intro f f' hf g g' hg
    show graph_algebra_eqv (f + g) (f' + g')
    dsimp [graph_algebra_eqv]
    have h := zeroSet_closed_under_add (f - f') (g - g') hf hg
    have : f - f' + (g - g') = (f + g) - (f' + g') := sub_add_sub_comm f f' g g'
    rw [←this]
    exact h

noncomputable instance : HSMul ℝ GraphAlgebra GraphAlgebra where
  hSMul r := by
    apply Quotient.map (r • ·)
    intro g g' hg
    simp
    show graph_algebra_eqv (r • g) (r • g')
    dsimp [graph_algebra_eqv]
    rw [← smul_sub]
    apply zeroSet_closed_under_smul
    exact hg

instance : Zero GraphAlgebra where
  zero := ⟦0⟧

noncomputable instance : One GraphAlgebra where
  one := ⟦1⟧

noncomputable instance : Neg GraphAlgebra where
  neg := ((-1 : ℝ) • ·)

noncomputable def graph_mul
    (H₁ H₂ : IsoSimpleGraph) : GraphVector
  :=
  let ℓ := H₁.1 + H₂.1
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ G in ℓ_graphs, (quotSubgraphPairDensity H₁.2 H₂.2 G) • basisElementFromGraph ⟨ℓ, G⟩

lemma graph_mul_comm
    (G H : IsoSimpleGraph) : graph_mul G H = graph_mul H G
  := by
  dsimp [graph_mul]
  rw [add_comm]
  apply sum_congr
  · rfl
  · intros
    simp [quotSubgraphPairDensity_comm]

noncomputable instance : Mul GraphVector where
  mul g h := ∑ G in g.support, ∑ H in h.support, ((g G) * (h H)) • graph_mul G H

lemma graphVector_mul_comm
    (g h : GraphVector) : g * h = h * g
  := by
  show ∑ G in g.support, ∑ H in h.support, _ = ∑ H in h.support, ∑ G in g.support, _
  rw [sum_comm]
  apply sum_congr
  · rfl
  · intros
    apply sum_congr
    · rfl
    · intros
      rw [mul_comm, graph_mul_comm]

noncomputable instance : CommMagma GraphVector where
  mul_comm := graphVector_mul_comm

instance : IsScalarTower ℝ GraphVector GraphVector where
  smul_assoc r g h := by
    show ∑ G in (r • g).support, _ = r • ∑ G in g.support, _
    by_cases hr : r = 0
    · simp [hr]
    · have hg_supp : (r • g).support = g.support := Finsupp.support_smul_eq hr
      rw [hg_supp]
      repeat (rw [smul_sum]; congr; apply funext; intro)
      simp [smul_mul_assoc, mul_assoc, smul_smul]

noncomputable instance : HasDistribNeg GraphVector where
  neg_mul g h := sorry
  mul_neg g h := sorry

lemma graphVector_left_distrib
    (f g h : GraphVector) : f * (g + h) = f * g + f * h
  := by
  sorry

lemma graphVector_zero_mul
    (f : GraphVector) : 0 * f = 0
  := by
  sorry

noncomputable instance : NonUnitalNonAssocRing GraphVector where
  left_distrib := graphVector_left_distrib
  right_distrib := by
    simp [mul_comm, graphVector_left_distrib]
  zero_mul := graphVector_zero_mul
  mul_zero := by
    intros; rw [mul_comm, graphVector_zero_mul]

lemma graph_mul_zero
    (G H : IsoSimpleGraph) (ℓ : ℕ)
    : (basisElementFromGraph G) * (zeroElement H ℓ) ∈ ZeroSet
  := by
  sorry

lemma graphVector_mul_zero
    (g : GraphVector) {k : GraphVector} (hk : k ∈ ZeroSet) : g * k ∈ ZeroSet
  := by
  rw [graphVector_eq_sum_basisElement g, sum_mul]
  apply zeroSet_closed_under_sum
  intro G _
  obtain ⟨I, hI, c, v, hv, hk_sum⟩ := zeroSet_eq_sum_spanElement hk
  rw [hk_sum, mul_sum]
  apply zeroSet_closed_under_sum
  intro i _
  rw [smul_mul_assoc]
  apply zeroSet_closed_under_smul
  rw [mul_comm, smul_mul_assoc]
  apply zeroSet_closed_under_smul
  obtain ⟨H, ℓ, hvi⟩ := zeroSpanSet_eq_zeroElement (hv i)
  simp [mul_comm, graph_mul_zero, hvi]

lemma graph_mul_one
    (G : IsoSimpleGraph) : graph_algebra_eqv (graph_mul G 1) (basisElementFromGraph G)
  := by
  rw [graph_mul_comm]
  apply graph_algebra_eqv.symm
  dsimp [graph_algebra_eqv]
  have : graph_mul 1 G = densityGraphSum G G.1 := by
    dsimp [densityGraphSum, graph_mul]
    rw [add_comm]
    apply sum_congr
    · rfl
    · intros
      rw [quotSubgraphPairDensity_one]
      rfl
  rw [this, ZeroSet]
  refine Submodule.mem_span.mpr fun p a ↦ a ?_
  refine Set.mem_sUnion.mpr ?_
  let S := (fun G ℓ ↦ basisElementFromGraph G - densityGraphSum G ℓ) G '' {ℓ | G.fst ≤ ℓ}
  use S; constructor
  · exact Set.mem_range_self G
  · dsimp [S]
    refine Set.mem_image_of_mem (fun ℓ ↦ basisElementFromGraph G - densityGraphSum G ℓ) ?_
    simp

lemma graphVector_mul_one
    (g : GraphVector) : graph_algebra_eqv (g * 1) g
  := by
  show ∑ G in g.support, ∑ H in (1 : GraphVector).support, _ - g ∈ ZeroSet
  have h_supp_one : Finsupp.support (1 : GraphVector) = {1} := by
    show Finsupp.support (basisElementFromGraph 1) = {1}
    dsimp [basisElementFromGraph]
    rw [Finsupp.support_single_ne_zero _ (by simp)]
  rw [sum_comm, h_supp_one, sum_singleton]
  have hg : g = ∑ G in g.support, g G • basisElementFromGraph G := by
    simp [basisElementFromGraph]
    nth_rw 1 [← Finsupp.sum_single g, Finsupp.sum]
  nth_rw 3 [hg]
  rw [← sum_sub_distrib]
  apply zeroSet_closed_under_sum
  intro G _
  have : (1 : GraphVector) 1 = 1 := by
    show (basisElementFromGraph 1) 1 = 1
    simp [basisElementFromGraph]
  rw [this, mul_one, ← smul_sub]
  apply zeroSet_closed_under_smul
  exact graph_mul_one G

noncomputable instance : Mul GraphAlgebra where
  mul := by
    apply Quotient.map₂ (· * ·)
    intro g' g hg h' h hh
    show graph_algebra_eqv (g' * h') (g * h)
    dsimp [graph_algebra_eqv]
    let kg := g' - g
    let kh := h' - h
    have hkg : kg ∈ ZeroSet := hg
    have hkh : kh ∈ ZeroSet := hh
    have : g' * h' = (g + kg) * (h + kh) := by
      rw [← sub_add_cancel g' g, ← sub_add_cancel h' h]
      simp only [kg, kh, add_comm]
    rw [this]
    rw [graphVector_left_distrib, right_distrib, right_distrib]
    rw [add_assoc, add_sub_cancel_left]
    apply zeroSet_closed_under_add
    · rw [mul_comm]
      exact graphVector_mul_zero h hkg
    · apply zeroSet_closed_under_add
      · exact graphVector_mul_zero g hkh
      · exact graphVector_mul_zero kg hkh

lemma graphAlgebra_mul_comm
    (g h : GraphAlgebra) : g * h = h * g
  := by
  rw [← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  rw [mul_comm]

lemma graphAlgebra_left_distrib
    (f g h : GraphAlgebra) : f * (g + h) = f * g + f * h
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  rw [graphVector_left_distrib]

lemma graphAlgebra_mul_zero
    (g : GraphAlgebra) : g * 0 = 0
  := by
  rcases Quotient.exists_rep g with ⟨grep, hgrep⟩
  rw [← hgrep]
  apply Quotient.sound
  simp; rfl

lemma graphAlgebra_mul_one
    (g : GraphAlgebra) : g * 1 = g
  := by
  rcases Quotient.exists_rep g with ⟨grep, hgrep⟩
  rw [← hgrep]
  apply Quotient.sound
  simp
  apply graphVector_mul_one

noncomputable instance : Ring GraphAlgebra where
  add := (· + ·)
  add_assoc a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c]
    apply Quotient.sound
    simp_all
    rw [add_assoc]
  zero := 0
  zero_add a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  add_zero a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp
  neg := -(·)
  add_comm a b := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    apply Quotient.sound
    simp
    rw [add_comm]
  neg_add_cancel a := by
    rw [← Quotient.out_eq a]
    apply Quotient.sound
    simp; rfl
  mul := (· * ·)
  mul_assoc := sorry
  zero_mul a := by
    rw [graphAlgebra_mul_comm]
    apply graphAlgebra_mul_zero
  mul_zero := graphAlgebra_mul_zero
  one := 1
  one_mul a := by
    rw [graphAlgebra_mul_comm]
    apply graphAlgebra_mul_one
  mul_one := graphAlgebra_mul_one
  left_distrib := graphAlgebra_left_distrib
  right_distrib a b c := by
    simp [graphAlgebra_mul_comm, graphAlgebra_left_distrib]
  nsmul n g := (n : ℝ) • g
  nsmul_zero g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  nsmul_succ n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul z g := (z : ℝ) • g
  zsmul_zero' g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp; rfl
  zsmul_succ' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    have : (n + 1 : ℝ) • Quotient.out g = (n : ℝ) • Quotient.out g + Quotient.out g := by
      rw [add_smul, one_smul]
    rw [this]
  zsmul_neg' n g := by
    simp
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [← neg_smul, neg_add_rev]

noncomputable instance : CommRing GraphAlgebra where
  mul_comm := graphAlgebra_mul_comm

noncomputable instance : Algebra ℝ GraphAlgebra where
  smul r g := r • g
  toFun r := r • 1
  map_zero' := by
    simp
    apply Quotient.sound
    simp; rfl
  map_one' := by
    simp
    apply Quotient.sound
    simp; rfl
  map_add' := by
    intros; simp
    apply Quotient.sound
    simp
    rw [add_smul]
  map_mul' := sorry
  smul_def' := sorry
  commutes' := by
    intros; simp
    rw [mul_comm]
