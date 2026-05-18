import «LeanFlagAlgebras».GraphAlgebra.SubgraphDensity
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Unique
import Mathlib.Tactic.Linarith.Frontend

/-! # The Graph Algebra

This file constructs the (commutative) `ℝ`-algebra `GraphAlgebra` that is the
semantic foundation of the flag-algebra development. We start from the free
`ℝ`-module `GraphVector` on isomorphism classes of finite simple graphs, equip
it with a multiplication given by random-overlap subgraph densities
(`graphMul`, built from `quotSubgraphPairDensity`), and then quotient by
`ZeroSet`, the subspace forcing a graph to equal its expansion as a density
combination of larger graphs (the `zeroElement` relations). The resulting
`GraphAlgebra := Quotient graphVectorSetoid` is shown to be a commutative ring
and an `ℝ`-algebra; this is the size-free density algebra later refined into
the typed flag algebra `A^σ`. Densities come from `GraphAlgebra.SubgraphDensity`. -/

open Finset
open SimpleGraph
open Classical

namespace GraphAlgebras

-- set of all graphs (up to isomorphism) on n vertices
abbrev IsoSimpleGraphWithSize (n : ℕ) : Type
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
/-- An isomorphism class of finite simple graphs, bundled with its vertex
count `n`; the basis index of the graph algebra. -/
def IsoSimpleGraph : Type
  := Σ (n : ℕ), IsoSimpleGraphWithSize n

instance : One IsoSimpleGraph where
  one := ⟨0, (default : IsoSimpleGraphWithSize 0)⟩

lemma isoSimpleGraph_one_fst
    : (1 : IsoSimpleGraph).1 = 0
  := rfl

lemma isoSimpleGraph_one_snd
    : (1 : IsoSimpleGraph).2 = ⟦emptyGraph (Fin 0)⟧
  := rfl

/-- The free `ℝ`-module on `IsoSimpleGraph`: formal real combinations of
graph isomorphism classes, the carrier before quotienting by `ZeroSet`. -/
abbrev GraphVector : Type
  := IsoSimpleGraph →₀ ℝ

noncomputable instance : AddCommMonoid GraphVector
  := Finsupp.instAddCommMonoid

noncomputable instance : AddCommGroup GraphVector
  := Finsupp.instAddCommGroup

noncomputable instance : Module ℝ GraphVector
  := Finsupp.module IsoSimpleGraph ℝ

/-- The basis vector of `GraphVector` corresponding to a single graph `G`
(the indicator finsupp at `G`). -/
noncomputable def basisElementFromGraph (G : IsoSimpleGraph) : GraphVector
  := Finsupp.single G 1

@[simp]
lemma basisElementFromGraph_apply_self
    (G : IsoSimpleGraph)
    : (basisElementFromGraph G) G = 1
  := by
  simp [basisElementFromGraph]

@[simp]
lemma basisElementFromGraph_support
    (G : IsoSimpleGraph)
    : (basisElementFromGraph G).support = {G}
  := by
  dsimp [basisElementFromGraph]
  rw [Finsupp.support_single_ne_zero _ (by simp)]

/-- Every `GraphVector` is its own finite combination of basis elements;
the standard handle for reducing module proofs to single graphs. -/
lemma graphVector_eq_sum_basisElement
    (g : GraphVector)
    : g = ∑ G ∈ g.support, g G • basisElementFromGraph G
  := by
  dsimp [basisElementFromGraph]
  rw [← Finsupp.sum_single g]
  apply sum_congr
  · simp
  · intros; simp

noncomputable instance : One GraphVector where
  one := basisElementFromGraph 1

lemma quotSubgraphDensity_one
    (G : IsoSimpleGraphWithSize n)
    : quotSubgraphDensity (1 : IsoSimpleGraph).2 G = 1
  := by
  exact quotSubgraphDensity_empty G

lemma quotSubgraphPairDensity_one
    (H : IsoSimpleGraphWithSize n) (G : IsoSimpleGraphWithSize m)
    : quotSubgraphPairDensity (1 : IsoSimpleGraph).2 H G = quotSubgraphDensity H G
  := by
  exact quotSubgraphPairDensity_empty H G

@[simp]
lemma graphVector_one_support
    : (1 : GraphVector).support = {(1 : IsoSimpleGraph)}
  := by
  show (basisElementFromGraph 1).support = {(1 : IsoSimpleGraph)}
  simp [basisElementFromGraph_support]

@[simp]
lemma graphVector_one_apply_one
    : (1 : GraphVector) 1 = 1
  := by
  show (basisElementFromGraph 1) 1 = 1
  simp [basisElementFromGraph_apply_self]

/-- `basisElementFromGraph` is an `ℝ`-basis of `GraphVector`, witnessing that
the module is free on `IsoSimpleGraph`. -/
noncomputable def finiteGraphModuleBasis
    : Module.Basis IsoSimpleGraph ℝ GraphVector
  :=
  have h_indep : LinearIndependent ℝ basisElementFromGraph := by
    rw [linearIndependent_iff'']
    intro s f h_supp h_sum G
    by_cases hG : G ∈ s
    · have : (∑ i ∈ s, f i • basisElementFromGraph i) G = 0 := by
        simp [h_sum]
      rw [← this, sum_eq_sum_diff_singleton_add hG _]
      simp [basisElementFromGraph]
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
  Module.Basis.mk h_indep (fun v _ ↦ h_span v)

-- GraphVector is a free ℝ-module generated by IsoSimpleGraph
instance : Module.Free ℝ GraphVector := by
  apply Module.Free.of_basis
  exact finiteGraphModuleBasis

@[simp]
lemma rat_smul_eq_real_smul
    (a : ℚ) (g : GraphVector) : a • g = (a : ℝ) • g
  := rfl

/-- Expansion of `G` at size `ℓ`: the combination `∑_F d(G,F) • F` over all
graphs `F` on `ℓ` vertices, weighted by the density of `G` inside `F`. -/
noncomputable def densityGraphSum
    (G : IsoSimpleGraph) (ℓ : ℕ) : GraphVector
  :=
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ F ∈ ℓ_graphs, (quotSubgraphDensity G.2 F) • basisElementFromGraph ⟨ℓ, F⟩

/-- The defining relation of the algebra: a graph minus its size-`ℓ`
density expansion. These vectors are quotiented away in `ZeroSet`. -/
noncomputable def zeroElement
    (G : IsoSimpleGraph) (ℓ : ℕ)
    : GraphVector
  := basisElementFromGraph G - densityGraphSum G ℓ

/-- All `zeroElement G ℓ` with `G.1 ≤ ℓ`; its span is `ZeroSet`. -/
noncomputable def zeroSpanSet : Set GraphVector
  :=
  {k | ∃ (G : IsoSimpleGraph) (ℓ : ℕ), G.1 ≤ ℓ ∧ k = zeroElement G ℓ}

@[simp]
lemma mem_zeroSpanSet
    {k : GraphVector} : k ∈ zeroSpanSet ↔ ∃ G ℓ, G.1 ≤ ℓ ∧ k = zeroElement G ℓ
  := Iff.rfl

lemma zeroSpanSet_exists_zeroElement
    (hk : k ∈ zeroSpanSet)
    : ∃ (G : IsoSimpleGraph) (ℓ : ℕ), G.1 ≤ ℓ ∧ k = zeroElement G ℓ
  := by
  simp [zeroSpanSet] at hk
  rcases hk with ⟨G, ℓ, hk⟩
  exact ⟨G, ℓ, (by simp_all), (by simp_all)⟩

/-- The submodule of `GraphVector` spanned by the density relations; the
quotient by `ZeroSet` identifies a graph with its density expansions. -/
noncomputable def ZeroSet : Submodule ℝ GraphVector
  :=
  Submodule.span ℝ zeroSpanSet

lemma zeroElement_in_zeroSet
    {G : IsoSimpleGraph} {ℓ : ℕ} (hℓ : G.1 ≤ ℓ)
    : zeroElement G ℓ ∈ ZeroSet
  := by
  apply Submodule.mem_span.mpr fun p a ↦ a ?_
  simp; use G; use ℓ

/-- Membership in `ZeroSet` unfolds to an explicit finite linear combination
of `zeroSpanSet` generators. -/
lemma zeroSet_eq_sum_spanElement
    {k : GraphVector} (h_zero : k ∈ ZeroSet)
    : ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (v : I → GraphVector),
    (∀ i, v i ∈ zeroSpanSet) ∧ (k = ∑ i, c i • v i)
  := by
  revert h_zero
  apply Submodule.span_induction
  · intro k h_zero
    use PUnit; use inferInstance
    use fun _ ↦ 1; use fun _ ↦ k
    simp_all only [mem_zeroSpanSet, implies_true, univ_unique, PUnit.default_eq_unit, one_smul, sum_const,
      card_singleton, and_self]
  · use Empty; use inferInstance
    use fun _ ↦ 0; use fun _ ↦ 0
    simp
  · intro x hx y hy hx_ind hy_ind
    rcases hx_ind with ⟨I, hI, c, v, hv, hx⟩
    rcases hy_ind with ⟨J, hJ, d, w, hw, hy⟩
    use Sum I J; use inferInstance
    use Sum.elim c d; use Sum.elim v w
    subst hy hx
    simp_all only [mem_zeroSpanSet, Sum.forall, Sum.elim_inl, implies_true, Sum.elim_inr, and_self,
      Fintype.sum_sum_type]
  · intro r x hx hx_ind
    rcases hx_ind with ⟨I, hI, c, v, hv, hx⟩
    use I; use hI; use fun i ↦ r * c i; use fun i ↦ v i
    constructor
    · intro i
      subst hx
      simp_all only [mem_zeroSpanSet]
    · rw [hx, smul_sum]
      apply sum_congr (by rfl)
      intro i _
      rw [smul_smul]

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
    (r : ℝ) (g : GraphVector) (h_zero : g ∈ ZeroSet)
    : r • g ∈ ZeroSet
  := by
  apply SMulMemClass.smul_mem
  assumption

lemma zero_smul_zeroSet
    {r : ℝ} {g : GraphVector} (h_zero : r = 0)
    : r • g ∈ ZeroSet
  := by
  subst h_zero
  simp_all only [zero_smul, Submodule.zero_mem]

/-- The algebra equivalence: two graph vectors are equal modulo the density
relations iff their difference lies in `ZeroSet`. -/
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

/-- The setoid on `GraphVector` induced by `graph_algebra_eqv`; its
quotient is `GraphAlgebra`. -/
instance graphVectorSetoid
    : Setoid GraphVector
  where
    r     := graph_algebra_eqv
    iseqv := {
      refl := graph_algebra_eqv.refl,
      symm := graph_algebra_eqv.symm,
      trans := graph_algebra_eqv.trans
    }

/-- The graph algebra: `GraphVector` quotiented by the density relations.
Equipped below with a commutative-ring and `ℝ`-algebra structure. -/
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

noncomputable instance : SMul ℝ GraphAlgebra where
  smul r := by
    apply Quotient.map (r • ·)
    intro g g' hg
    show graph_algebra_eqv (r • g) (r • g')
    dsimp [graph_algebra_eqv]
    rw [← smul_sub]
    apply zeroSet_closed_under_smul
    exact hg

noncomputable instance : MulAction ℝ GraphAlgebra where
  one_smul g := by
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
  mul_smul r s g := by
    rw [← Quotient.out_eq g]
    apply Quotient.sound
    simp
    rw [mul_smul]

instance : Zero GraphAlgebra where
  zero := ⟦0⟧

noncomputable instance : One GraphAlgebra where
  one := ⟦1⟧

noncomputable instance : Neg GraphAlgebra where
  neg := ((-1 : ℝ) • ·)

/-- Product of two graphs computed at a fixed ambient size `ℓ`: expand into
size-`ℓ` graphs weighted by `quotSubgraphPairDensity` (the density of finding
disjoint copies of `H₁` and `H₂`). -/
noncomputable def graphMulWithSize
    (H₁ H₂ : IsoSimpleGraph) (ℓ : ℕ) : GraphVector
  :=
  let ℓ_graphs : Finset (IsoSimpleGraphWithSize ℓ) := univ
  ∑ G ∈ ℓ_graphs, (quotSubgraphPairDensity H₁.2 H₂.2 G) • basisElementFromGraph ⟨ℓ, G⟩

lemma graphMulWithSize_comm
    (H₁ H₂ : IsoSimpleGraph) (ℓ : ℕ) : graphMulWithSize H₁ H₂ ℓ = graphMulWithSize H₂ H₁ ℓ
  := by
  dsimp [graphMulWithSize]
  apply sum_congr (by rfl)
  intro G _
  simp [quotSubgraphPairDensity_comm]

lemma sum_smul
    (s : Finset ι) (f : ι → ℝ) (g : GraphVector) : (∑ i ∈ s, f i) • g = ∑ i ∈ s, f i • g
  := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intros r R hr ih
    simp [sum_insert hr, Module.add_smul, ih]

/-- Key well-definedness fact: the size-`ℓ` product is independent of `ℓ`
modulo the density relations, once `ℓ` is large enough (uses the density
chain rule). -/
lemma graphMulWithSize_indep_on_size
    {H₁ H₂ : IsoSimpleGraph} {ℓ₁ ℓ₂ : ℕ} (hℓ₁ : H₁.1 + H₂.1 ≤ ℓ₁) (hℓ₂ : H₁.1 + H₂.1 ≤ ℓ₂)
    : graph_algebra_eqv (graphMulWithSize H₁ H₂ ℓ₁) (graphMulWithSize H₁ H₂ ℓ₂)
  := by
  wlog hℓ : ℓ₁ ≤ ℓ₂ generalizing ℓ₁ ℓ₂
  · have hℓ' : ℓ₂ ≤ ℓ₁ := Nat.le_of_not_ge hℓ
    have h_eqv := this hℓ₂ hℓ₁ hℓ'
    exact graph_algebra_eqv.symm h_eqv
  · dsimp [graph_algebra_eqv, graphMulWithSize]
    have : ∑ G₂ : IsoSimpleGraphWithSize ℓ₂, (quotSubgraphPairDensity H₁.2 H₂.2 G₂ : ℝ) • basisElementFromGraph ⟨ℓ₂, G₂⟩
      = ∑ G₁ : IsoSimpleGraphWithSize ℓ₁, ∑ G₂ : IsoSimpleGraphWithSize ℓ₂,
        (quotSubgraphPairDensity H₁.2 H₂.2 G₁ : ℝ) • (quotSubgraphDensity G₁ G₂ : ℝ) • basisElementFromGraph ⟨ℓ₂, G₂⟩
      := by
      rw [sum_comm]
      apply sum_congr (by rfl)
      intro G₂ _
      simp [density_chain_rule _ _ _ hℓ₁ hℓ, sum_smul]
      apply sum_congr (by rfl)
      intro G₁ _
      rw [mul_smul]
    rw [this, ← sum_sub_distrib]
    apply zeroSet_closed_under_sum
    intro G₁ _
    rw [← smul_sum, ← smul_sub]
    apply zeroSet_closed_under_smul
    show zeroElement ⟨ℓ₁, G₁⟩ ℓ₂ ∈ ZeroSet
    exact zeroElement_in_zeroSet hℓ

/-- The canonical product of two graphs, taken at the minimal ambient size
`H₁.1 + H₂.1`; the basis-level multiplication of the graph algebra. -/
noncomputable def graphMul
    (H₁ H₂ : IsoSimpleGraph) : GraphVector
  :=
  graphMulWithSize H₁ H₂ (H₁.1 + H₂.1)

lemma graphMul_indep_on_size
    {H₁ H₂ : IsoSimpleGraph} {ℓ' : ℕ} (hℓ' : H₁.1 + H₂.1 ≤ ℓ')
    : graph_algebra_eqv (graphMul H₁ H₂) (graphMulWithSize H₁ H₂ ℓ')
  := by
  refine graphMulWithSize_indep_on_size ?_ hℓ'
  simp

lemma graphMul_comm
    (G H : IsoSimpleGraph) : graphMul G H = graphMul H G
  := by
  simp [graphMul, add_comm, graphMulWithSize_comm]

/-- Bilinear extension of `graphMul` to all of `GraphVector`. -/
noncomputable instance : Mul GraphVector where
  mul g h := ∑ G ∈ g.support, ∑ H ∈ h.support, ((g G) * (h H)) • graphMul G H

lemma graphVector_mul_comm
    (g h : GraphVector) : g * h = h * g
  := by
  show ∑ G ∈ g.support, ∑ H ∈ h.support, _ = ∑ H ∈ h.support, ∑ G ∈ g.support, _
  rw [sum_comm]
  apply sum_congr rfl
  intros
  apply sum_congr rfl
  intros
  rw [mul_comm, graphMul_comm]

noncomputable instance : CommMagma GraphVector where
  mul_comm := graphVector_mul_comm

instance : IsScalarTower ℝ GraphVector GraphVector where
  smul_assoc r g h := by
    show ∑ G ∈ (r • g).support, _ = r • ∑ G ∈ g.support, _
    by_cases hr : r = 0
    · simp [hr]
    · have hg_supp : (r • g).support = g.support := Finsupp.support_smul_eq hr
      rw [hg_supp]
      repeat (rw [smul_sum]; congr; apply funext; intro)
      simp [mul_assoc, smul_smul]

lemma graphVector_neg_mul
    (g h : GraphVector) : -g * h = -(g * h)
  := by
  show ∑ G ∈ (-g).support, ∑ H ∈ h.support, _ = -∑ G ∈ g.support, ∑ H ∈ h.support, _
  rw [Finsupp.support_neg g]
  simp_all only [Finsupp.coe_neg, Pi.neg_apply, neg_mul, neg_smul, sum_neg_distrib]

noncomputable instance : HasDistribNeg GraphVector where
  neg_mul := graphVector_neg_mul
  mul_neg g h := by
    rw [mul_comm g (-h), mul_comm g h, graphVector_neg_mul h g]

/-- General support-bookkeeping lemma: a sum of `ψ g + ψ h` over the support
of `g + h` splits as the sum over `g`'s support plus the sum over `h`'s,
provided `ψ` vanishes appropriately. Used to prove distributivity. -/
lemma graphVector_add_support
    (g h : GraphVector) {α : Type} [AddCommGroup α] (ψ : GraphVector → IsoSimpleGraph → α)
    (hψ1 : ∀ g h x, g x + h x = 0 → ψ g x + ψ h x = 0)
    (hψ2 : ∀ g x, g x =0 -> ψ g x = 0)
    : ∑ K ∈ (g + h).support, (ψ g K + ψ h K) =
      ∑ G ∈ g.support, ψ g G + ∑ H ∈ h.support, ψ h H
  := by
  have add_support_sub : (g + h).support ⊆ g.support ∪ h.support := Finsupp.support_add
  have sum_decomposition : ∑ x ∈ (g + h).support, (ψ g x + ψ h x) =
  ∑ x ∈ g.support ∪ h.support, (ψ g x + ψ h x) - ∑ x ∈ (g.support ∪ h.support) \ (g + h).support, (ψ g x + ψ h x) := by
    rw [sum_sdiff_eq_sub add_support_sub]
    exact
      Eq.symm
        (sub_sub_self (∑ x ∈ g.support ∪ h.support, (ψ g x + ψ h x))
          (∑ x ∈ (g + h).support, (ψ g x + ψ h x)))
  have sum_extra_eq_0 : ∑ x ∈ (g.support ∪ h.support) \ (g + h).support, (ψ g x + ψ h x) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff] at hx
    obtain ⟨h_in_union, h_not_in_sum⟩ := hx
    rw [Finsupp.notMem_support_iff, Finsupp.add_apply] at h_not_in_sum
    rw [←union_sdiff_self_eq_union, mem_union] at h_in_union
    exact hψ1 g h x h_not_in_sum
  rw [sum_decomposition, sum_extra_eq_0, sub_zero]
  have disjoint_1 : Disjoint g.support (h.support \ g.support) := disjoint_sdiff
  have disjoint_2 : Disjoint (g.support \ h.support) (g.support ∩ h.support) := disjoint_sdiff_inter g.support h.support
  have disjoint_3 : Disjoint (g.support ∩ h.support) (h.support \ g.support)  := by
    rw [inter_comm]; symm
    exact disjoint_sdiff_inter h.support g.support
  have decomposition : ∑ x ∈ g.support ∪ h.support, (ψ g x + ψ h x) = ∑ x ∈ g.support \ h.support ∪ g.support ∩ h.support, (ψ g x + ψ h x) + ∑ x ∈ h.support \ g.support, (ψ g x + ψ h x) := by
    rw [←union_sdiff_self_eq_union]
    rw [sdiff_union_inter g.support h.support]
    exact sum_union disjoint_1
  rw [decomposition, sum_union disjoint_2, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have sum_not_g_supp_eq_0 : ∑ x ∈ g.support \ h.support, ψ h x = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff, Finsupp.notMem_support_iff] at hx
    apply hψ2
    exact hx.2
  have sum_not_f_supp_eq_0 : ∑ x ∈ h.support \ g.support, ψ g x = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff, Finsupp.notMem_support_iff] at hx
    apply hψ2
    exact hx.2
  rw [sum_not_g_supp_eq_0, sum_not_f_supp_eq_0, add_zero, zero_add]
  rw [add_assoc, add_assoc, ← sum_union disjoint_3, union_comm, inter_comm, sdiff_union_inter h.support g.support]
  rw [←add_assoc, inter_comm, ← sum_union disjoint_2, sdiff_union_inter g.support h.support]

lemma graphVector_left_distrib
    (f g h : GraphVector) : f * (g + h) = f * g + f * h
  := by
  show ∑ F ∈ f.support, ∑ K ∈ (g + h).support, _ = ∑ F ∈ f.support, ∑ G ∈ g.support, _ + ∑ F ∈ f.support, ∑ H ∈ h.support, _
  simp [← sum_add_distrib]
  apply sum_congr rfl
  intro F _
  simp [mul_add, add_smul]
  let ψ : GraphVector → IsoSimpleGraph → GraphVector
    := fun g G => (f F * g G) • graphMul F G
  have hψ1 : ∀ (g h : GraphVector) (x : IsoSimpleGraph), g x + h x = 0 → ψ g x + ψ h x = 0 := by
    intro g' h' x hx
    simp [ψ]
    rw [add_eq_zero_iff_neg_eq] at hx
    rw [←hx]
    simp
  have hψ2 : ∀ (g : GraphVector) (x : IsoSimpleGraph), g x = 0 → ψ g x = 0 := by
    intro g x hx
    simp [ψ]
    left; right
    exact hx
  rw [graphVector_add_support g h ψ hψ1 hψ2]

lemma graphVector_right_distrib
    (f g h : GraphVector) : (f + g) * h = f * h + g * h
  := by
  simp [graphVector_mul_comm, graphVector_left_distrib]

lemma graphVector_zero_mul
    (f : GraphVector) : 0 * f = 0
  := by
  show ∑ G ∈ (0 : GraphVector).support, ∑ H ∈ f.support, _ = 0
  simp

lemma graphVector_mul_sum
    (s : Finset ι) (f : ι → GraphVector) (g : GraphVector)
    : g * ∑ i ∈ s, f i = ∑ i ∈ s, g * f i
  := by
  refine Finset.induction_on s ?_ ?_
  · simp
    rw [graphVector_mul_comm, graphVector_zero_mul]
  · intros r R hr ih
    simp [sum_insert hr, graphVector_left_distrib, ih]

lemma graphVector_sum_mul
    (s : Finset ι) (f : ι → GraphVector) (g : GraphVector)
    : (∑ i ∈ s, f i) * g = ∑ i ∈ s, f i * g
  := by
  simp [graphVector_mul_comm, graphVector_mul_sum]

noncomputable instance : NonUnitalNonAssocRing GraphVector where
  left_distrib := graphVector_left_distrib
  right_distrib := by
    simp [mul_comm, graphVector_left_distrib]
  zero_mul := graphVector_zero_mul
  mul_zero := by
    intros; rw [mul_comm, graphVector_zero_mul]

lemma graph_mul_zeroElement
    (G H : IsoSimpleGraph) {ℓ : ℕ} (hℓ : H.1 ≤ ℓ)
    : (basisElementFromGraph G) * (zeroElement H ℓ) ∈ ZeroSet
  := by
  dsimp [zeroElement]
  rw [mul_sub]
  show graph_algebra_eqv (∑ G' ∈ _, ∑ H' ∈ _, _) _
  simp; dsimp [densityGraphSum]
  rw [mul_sum]
  let L := G.1 + H.1 + ℓ
  apply graph_algebra_eqv.trans
  · show graph_algebra_eqv _
      (∑ F : IsoSimpleGraphWithSize L, (quotSubgraphPairDensity H.2 G.2 F) • basisElementFromGraph ⟨L, F⟩)
    dsimp [graph_algebra_eqv, graphMul]
    show graph_algebra_eqv _ (graphMulWithSize H G L)
    rw [graphMulWithSize_comm]
    apply graphMulWithSize_indep_on_size
    · rw [add_comm]
    · rw [add_comm]
      exact Nat.le_add_right (G.fst + H.fst) ℓ
  apply graph_algebra_eqv.trans
  · show graph_algebra_eqv _
      (∑ F' : IsoSimpleGraphWithSize ℓ, ∑ F : IsoSimpleGraphWithSize L,
        ((quotSubgraphDensity H.2 F' : ℝ) * (quotSubgraphPairDensity F' G.2 F)) • basisElementFromGraph ⟨L, F⟩)
    dsimp [graph_algebra_eqv]
    rw [sum_comm, ← sum_sub_distrib]
    apply zeroSet_closed_under_sum
    intro F _
    rw [← sum_smul, ← sub_smul]
    apply zero_smul_zeroSet
    rw [density_chain_rule' H.2 G.2 F hℓ (by simp [L, add_comm])]
    simp
  dsimp [graph_algebra_eqv]
  rw [← sum_sub_distrib]
  apply zeroSet_closed_under_sum
  intro F' _
  have : ∑ F : IsoSimpleGraphWithSize L,
      ((quotSubgraphDensity H.snd F' : ℝ) * ↑(quotSubgraphPairDensity F' G.snd F)) • basisElementFromGraph ⟨L, F⟩ =
      ∑ F : IsoSimpleGraphWithSize L,
      (quotSubgraphDensity H.snd F') • ↑(quotSubgraphPairDensity F' G.snd F) • basisElementFromGraph ⟨L, F⟩ := by
    apply sum_congr (by rfl)
    intros; simp [mul_smul]
  rw [this, mul_comm]
  simp [← smul_sum, smul_mul_assoc, ← smul_sub]
  apply zeroSet_closed_under_smul
  apply graph_algebra_eqv.trans
  · show graph_algebra_eqv (graphMulWithSize ⟨ℓ, F'⟩ G L) (graphMul ⟨ℓ, F'⟩ G)
    apply graph_algebra_eqv.symm
    apply graphMul_indep_on_size (by simp [L, add_comm])
  · have : graphMul ⟨ℓ, F'⟩ G = basisElementFromGraph ⟨ℓ, F'⟩ * basisElementFromGraph G := by
      show graphMul ⟨ℓ, F'⟩ G = ∑ _ ∈ (basisElementFromGraph ⟨ℓ, F'⟩).support, ∑ _ ∈ (basisElementFromGraph G).support, _
      simp
    rw [this]
    apply graph_algebra_eqv.refl

/-- `ZeroSet` is a two-sided ideal: multiplying any vector by a relation
stays inside `ZeroSet`. This is what makes multiplication descend to
`GraphAlgebra`. -/
lemma graphVector_mul_zeroSet
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
  obtain ⟨H, ℓ, hℓ, hvi⟩ := zeroSpanSet_exists_zeroElement (hv i)
  simp [mul_comm, hvi]
  exact graph_mul_zeroElement G H hℓ

lemma graph_mul_one
    (G : IsoSimpleGraph) : graphMul G 1 = basisElementFromGraph G
  := by
  rw [graphMul_comm]
  simp [graphMul, graphMulWithSize, isoSimpleGraph_one_fst]
  rw [zero_add]
  have h_univ_split : univ = insert G.2 (univ.erase G.2) := Eq.symm (insert_erase (by simp))
  rw [h_univ_split, sum_insert (notMem_erase _ _)]
  have : ((1 : ℚ) : ℝ) = (1 : ℝ) := by simp
  rw [quotSubgraphPairDensity_one, quotSubgraphDensity_self, this, one_smul]
  rw [← add_zero (basisElementFromGraph G)]; congr
  apply sum_eq_zero
  intro G' hG'
  rw [quotSubgraphPairDensity_one]
  have hG'_ne_G : G.2 ≠ G' := by aesop
  simp [quotSubgraphDensity_other hG'_ne_G]

lemma graphVector_mul_one
    (g : GraphVector) : g * 1 = g
  := by
  rw [graphVector_eq_sum_basisElement g, sum_mul]
  apply sum_congr (by rfl)
  intro G _
  rw [smul_mul_assoc]; congr
  show ∑ _ ∈ (basisElementFromGraph G).support, _ = _
  simp only [basisElementFromGraph_support, sum_singleton,
    basisElementFromGraph_apply_self, one_mul, graphVector_one_support, graphVector_one_apply_one, one_smul]
  exact graph_mul_one G

noncomputable instance : MulOneClass GraphVector where
  one_mul g := by
    rw [graphVector_mul_comm, graphVector_mul_one]
  mul_one := graphVector_mul_one

lemma graphVector_smul_mul_smul_comm
    (g h : GraphVector) (a b : ℝ)
    : a • g * b • h = (a * b) • (g * h)
  := by
  by_cases hab : a = 0 ∨ b = 0
  · cases' hab with ha hb
    · simp [ha, zero_mul, zero_smul]
    · simp [hb, mul_zero, zero_smul]
  · have ha : a ≠ 0 := by simp_all only [not_or, ne_eq, not_false_eq_true]
    have hb : b ≠ 0 := by simp_all only [not_or, ne_eq, not_false_eq_true]
    show ∑ G ∈ (a • g).support, ∑ H ∈ (b • h).support, _ = (a * b) • ∑ G ∈ _, ∑ H ∈ _, _
    rw [Finsupp.support_smul_eq ha, Finsupp.support_smul_eq hb]
    repeat (rw [smul_sum]; apply sum_congr (by rfl); intros)
    simp [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    congr 1; ring

/-- The triple product `G₁ * G₂ * G₃` equals, modulo relations, the size-`ℓ`
expansion weighted by `quotSubgraphTripleDensity`; the workhorse for
associativity. -/
lemma graph_mul_mul_eqv_sum_tripleDensity
    {G₁ G₂ G₃ : IsoSimpleGraph} {ℓ : ℕ} (hℓ : G₁.1 + G₂.1 + G₃.1 ≤ ℓ)
    : graph_algebra_eqv
      (basisElementFromGraph G₁ * basisElementFromGraph G₂ * basisElementFromGraph G₃)
      (∑ (F : IsoSimpleGraphWithSize ℓ), (quotSubgraphTripleDensity G₁.2 G₂.2 G₃.2 F) • basisElementFromGraph ⟨ℓ, F⟩)
  := by
  show (∑ G ∈ _, ∑ G' ∈ _, _) * _ - _ ∈ ZeroSet
  simp; dsimp [graphMul, graphMulWithSize]
  rw [graphVector_sum_mul]
  let ℓ' := G₁.1 + G₂.1
  apply graph_algebra_eqv.trans
  · show graph_algebra_eqv _
      (∑ (F : IsoSimpleGraphWithSize ℓ), ∑ (F' : IsoSimpleGraphWithSize ℓ'),
        (quotSubgraphPairDensity G₁.2 G₂.2 F') • (quotSubgraphPairDensity F' G₃.2 F) • basisElementFromGraph ⟨ℓ, F⟩)
    dsimp [graph_algebra_eqv]
    rw [sum_comm, ← sum_sub_distrib]
    apply zeroSet_closed_under_sum
    intro F' _
    rw [← smul_sum, smul_mul_assoc, ← smul_sub]
    apply zeroSet_closed_under_smul
    show ∑ F ∈ _, _ - _ ∈ ZeroSet
    simp
    apply graph_algebra_eqv.trans
    · apply graphMul_indep_on_size hℓ
    · dsimp [graph_algebra_eqv, graphMulWithSize]
      rw [← sum_sub_distrib]
      apply zeroSet_closed_under_sum
      intro G _
      simp
  · dsimp [graph_algebra_eqv]
    rw [← sum_sub_distrib]
    apply zeroSet_closed_under_sum
    intro G _
    simp [smul_smul, ← sum_smul, ← sub_smul]
    apply zero_smul_zeroSet
    have hℓ' : G₁.1 + G₂.1 ≤ ℓ' := Nat.le_refl (G₁.1 + G₂.1)
    have hℓ₂ : ℓ' + G₃.1 ≤ ℓ := by simp_all only [ℓ']
    rw [density_chain_rule'' G₁.2 G₂.2 G₃.2 G hℓ' hℓ₂]
    simp

lemma graph_mul_assoc
    (F G H : IsoSimpleGraph)
    : graph_algebra_eqv
      (basisElementFromGraph F * basisElementFromGraph G * basisElementFromGraph H)
      (basisElementFromGraph F * (basisElementFromGraph G * basisElementFromGraph H))
  := by
  let ℓ := F.1 + G.1 + H.1
  have hℓ : F.1 + G.1 + H.1 ≤ ℓ := Nat.le_refl (F.1 + G.1 + H.1)
  apply graph_algebra_eqv.trans
  · apply graph_mul_mul_eqv_sum_tripleDensity hℓ
  apply graph_algebra_eqv.symm
  rw [graphVector_mul_comm]
  apply graph_algebra_eqv.trans
  · have hℓ' : G.1 + H.1 + F.1 ≤ ℓ := by simp [ℓ]; linarith
    apply graph_mul_mul_eqv_sum_tripleDensity hℓ'
  dsimp [graph_algebra_eqv]
  rw [← sum_sub_distrib]
  apply zeroSet_closed_under_sum
  intros
  rw [← quotSubgraphTripleDensity_comm _ _ _ _ hℓ]
  simp only [sub_self, zero_mem]

/-- Associativity of the `GraphVector` product modulo the density relations
(it is only associative after passing to the quotient). -/
lemma graphVector_mul_assoc
    (f g h : GraphVector) : graph_algebra_eqv (f * g * h) (f * (g * h))
  := by
  dsimp [graph_algebra_eqv]
  rw [graphVector_eq_sum_basisElement f,
      graphVector_eq_sum_basisElement g,
      graphVector_eq_sum_basisElement h]
  simp [graphVector_mul_sum, graphVector_sum_mul, ← sum_sub_distrib, graphVector_smul_mul_smul_comm, mul_assoc]
  repeat (apply zeroSet_closed_under_sum; intros)
  rw [← smul_sub]
  apply zeroSet_closed_under_smul
  apply graph_mul_assoc

/-- Multiplication on `GraphAlgebra`, descended from `GraphVector` using that
`ZeroSet` is an ideal (`graphVector_mul_zeroSet`). -/
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
      exact graphVector_mul_zeroSet h hkg
    · apply zeroSet_closed_under_add
      · exact graphVector_mul_zeroSet g hkh
      · exact graphVector_mul_zeroSet kg hkh

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
  rw [← Quotient.out_eq g]
  apply Quotient.sound
  simp only [mul_zero, Setoid.refl]

lemma graphAlgebra_mul_one
    (g : GraphAlgebra) : g * 1 = g
  := by
  rw [← Quotient.out_eq g]
  apply Quotient.sound
  simp only [mul_one, Setoid.refl]

lemma graphAlgebra_mul_assoc
    (f g h : GraphAlgebra) : f * g * h = f * (g * h)
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  apply graphVector_mul_assoc

lemma graphAlgebra_smul_mul_smul_comm
    (g h : GraphAlgebra) (a b : ℝ)
    : a • g * b • h = (a * b) • (g * h)
  := by
  rw [← Quotient.out_eq g, ← Quotient.out_eq h]
  apply Quotient.sound
  simp
  rw [graphVector_smul_mul_smul_comm]

/-- `GraphAlgebra` is a ring: addition and multiplication descend from
`GraphVector`, with associativity/distributivity proved modulo the
relations. -/
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
    simp
  mul := (· * ·)
  mul_assoc := graphAlgebra_mul_assoc
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
    simp
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
    simp
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

/-- `GraphAlgebra` is commutative (subgraph densities are symmetric). -/
noncomputable instance : CommRing GraphAlgebra where
  mul_comm := graphAlgebra_mul_comm

/-- `1 ≠ 0` in `GraphAlgebra`: the relations do not collapse the algebra.
Proved via the density evaluation functional `φ`, which sends `1` to `1`
but every relation to `0`. -/
instance : NeZero (1 : GraphAlgebra) where
  out := by
    intro one_eq_zero
    have h_one_zeroSet : (1 : GraphVector) ∈ ZeroSet := by
      rw [← sub_zero 1]
      exact Quotient.exact one_eq_zero
    have zeroSet_decomp := zeroSet_eq_sum_spanElement h_one_zeroSet
    rcases zeroSet_decomp with ⟨I, hI, c, v, hv, hx⟩
    have zeroElem_exists : ∀ (i : I), ∃ (G : IsoSimpleGraph) (ℓ : ℕ), G.1 ≤ ℓ ∧ v i = zeroElement G ℓ := by
      intro t; exact zeroSpanSet_exists_zeroElement (hv t)
    choose G ℓ hG using zeroElem_exists
    let L := Finset.sup (univ : Finset I) ℓ
    let F := (default : IsoSimpleGraphWithSize L)
    let φ : GraphVector → ℝ
      := fun g => ∑ G ∈ g.support, (g G) * quotSubgraphDensity G.2 F
    have φ_add : ∀ (g h : GraphVector), φ (g + h) = φ g + φ h := by
      intro g h
      simp [φ, add_mul]
      let ψ : GraphVector → IsoSimpleGraph → ℝ
        := fun g G => (g G) * quotSubgraphDensity G.2 F
      have hψ1 : ∀ (g h : GraphVector) (x : IsoSimpleGraph), g x + h x = 0 → ψ g x + ψ h x = 0 := by
        intro g' h' x hx
        simp [ψ]
        rw [add_eq_zero_iff_eq_neg] at hx
        rw [hx]
        simp
      have hψ2 : ∀ (g : GraphVector) (x : IsoSimpleGraph), g x = 0 → ψ g x = 0 := by
        intro g x hx
        simp [ψ]
        left; exact hx
      rw [graphVector_add_support g h ψ hψ1 hψ2]
    have φ_smul : ∀ (r : ℝ) (g : GraphVector), φ (r • g) = r * φ g := by
      intro r g
      show ∑ G ∈ _, _ = _ * ∑ G ∈ _, _
      by_cases hr : r = 0
      · simp [hr]
      · have hg_supp : (r • g).support = g.support := Finsupp.support_smul_eq hr
        rw [hg_supp, mul_sum]
        apply sum_congr (by rfl)
        intro x _
        simp [mul_assoc]
    have φ_sum : ∀ (s : Finset I) (f : I → GraphVector), φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
      intro s f
      refine Finset.induction_on s ?_ ?_
      · simp [φ]
      · intro r R hr ih
        simp [sum_insert hr]
        rw [φ_add, ih]
    have hφ : ∀ (i : I), φ (v i) = 0 := by
      intro i
      let iG := G i
      have ⟨hℓ', hG2⟩ : iG.fst ≤ ℓ i ∧ v i = zeroElement iG (ℓ i) := by apply hG
      have hℓ : ℓ i ≤ L := by apply Finset.le_sup; simp
      have φ_sum' : ∀ (s : Finset (IsoSimpleGraphWithSize (ℓ i))) (f : IsoSimpleGraphWithSize (ℓ i) → GraphVector), φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
        intro s f
        refine Finset.induction_on s ?_ ?_
        · simp [φ]
        · intro r R hr ih
          simp [sum_insert hr]
          rw [φ_add, ih]
      rw [hG2]
      dsimp [zeroElement]
      rw [sub_eq_add_neg, φ_add]
      rw [← @neg_one_smul ℝ GraphVector _, φ_smul (-1 : ℝ) _, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]
      dsimp [densityGraphSum]
      rw [φ_sum']
      have : φ (basisElementFromGraph iG) = quotSubgraphDensity iG.2 F := by
        simp [φ, basisElementFromGraph_support]
      rw [this]
      rw [density_chain_rule''' _ _ hℓ' hℓ]
      simp
      dsimp [IsoSimpleGraphWithSize]
      apply sum_congr (by rfl)
      · intro x
        rw [φ_smul]
        simp
        by_cases s : quotSubgraphDensity iG.snd x = 0
        · right; exact s
        · left
          dsimp [φ]
          simp
    have h_φ_1 : φ 1 = 1 := by
      show ∑ G ∈ (basisElementFromGraph 1).support, _ = 1
      simp [sum_singleton, quotSubgraphDensity_one]
    have h_φ_sum : φ (∑ i, c i • v i) = 0 := by
      simp_all only [mul_zero, sum_const_zero, zero_ne_one]
    rw [hx]at h_φ_1
    have zero_eq_one : (0 : ℝ) = (1 : ℝ) := by rw [←h_φ_1, ←h_φ_sum]
    exact zero_ne_one zero_eq_one

instance : Nontrivial GraphAlgebra where
  exists_pair_ne := ⟨0, 1, (by simp)⟩

/-- The `ℝ`-algebra structure on `GraphAlgebra` (scalars act as `r • 1`);
this is the algebra `A` in which density bounds are expressed. -/
noncomputable instance : Algebra ℝ GraphAlgebra where
  algebraMap := {
    toFun := fun r => r • 1
    map_one' := by
      apply Quotient.sound
      simp only [one_smul, Setoid.refl]
    map_mul' := by
      intro x y
      apply Quotient.sound
      simp only [smul_one_mul]
      rw [mul_smul]
    map_zero' := by
      apply Quotient.sound
      simp only [zero_smul, Setoid.refl]
    map_add' := by
      intro x y
      apply Quotient.sound
      simp only
      rw [add_smul]
  }
  smul_def' r g := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    nth_rw 1 [← one_mul g]
    nth_rw 2 [← one_smul ℝ g]
    rw [graphAlgebra_smul_mul_smul_comm, mul_one]
  commutes' := by
    intros; simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [mul_comm]

end GraphAlgebras
