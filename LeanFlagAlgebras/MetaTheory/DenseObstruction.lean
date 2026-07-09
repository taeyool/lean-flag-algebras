import LeanFlagAlgebras.MetaTheory.C4Free

/-! # A dense obstruction: complements of `C₄`-free graphs (paper §9.2, `cor:codegenerate`)

One might hope the degeneracy failures of §9.1 are an artefact of *sparsity*.  They are not:
root-plantability is invariant under complementation (`lem:complementation`), so every sparse
obstruction has a dense mirror.  Rather than formalise the full complementation *isomorphism* of
flag algebras, we exhibit the mirror of the `C₄`-free counterexample directly.

`coC4FreeClass` is the class of graphs whose complement is `C₄`-free.  It is *dense* — its members
have edge density tending to `1` — yet it is **not** root-plantable at the one-vertex type, for the
dual boundary-pinning reason: the one-root edge density is pinned to `1` across all constrained
limits, while a co-star (rooted at its isolated vertex) realises a quotient point of edge density
`0`.  Density is therefore not the dividing line for root-plantability.

The only complementation facts used are elementary: the edge-count identity
`e(G) + e(Gᶜ) = C(|G|,2)` and the observation that the complement of a co-star is a star.
-/

open SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-- The one-root edge rooted at vertex `1` instead of `0` (the second label placement on the edge
`⊤` of `Fin 2`).  It is flag-isomorphic to `edgeLabeled` via the swap `0 ↔ 1`. -/
private def edgeLabeled' : LabeledGraph vtype (Fin 2) where
  graph := edgeGraph
  type_embed :=
    { toFun := fun _ => 1
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [edgeGraph, top_adj, ne_eq]
        constructor
        · intro h; exact absurd rfl h
        · intro h; exact (h.ne (Subsingleton.elim a b)).elim }

/-- The edge is rigid up to two label placements: `isomorphismCount edgeLabeled = 2`, the root may sit
on either endpoint of `K₂` and both placements are flag-isomorphic via the swap `0 ↔ 1`. -/
private theorem isomorphismCount_edgeLabeled : isomorphismCount edgeLabeled = 2 := by
  classical
  -- `edgeLabeled' ∼f edgeLabeled` via the swap `0 ↔ 1`, which carries the root `1` to `0`.
  have hiso' : edgeLabeled' ∼f edgeLabeled := by
    refine ⟨{ graph_iso := Iso.completeGraph (Equiv.swap (0 : Fin 2) 1), type_preserve := ?_ }⟩
    funext t
    show (Iso.completeGraph (Equiv.swap (0 : Fin 2) 1)) (edgeLabeled'.type_embed t)
        = edgeLabeled.type_embed t
    show (Equiv.swap (0 : Fin 2) 1) 1 = 0
    simp
  -- The two members of the iso-set.
  have hmem0 : edgeLabeled ∈ isoLabeledGraphSetWithSameGraph edgeLabeled :=
    ⟨rfl, flagEqv.refl edgeLabeled⟩
  have hmem1 : edgeLabeled' ∈ isoLabeledGraphSetWithSameGraph edgeLabeled :=
    ⟨rfl, flagEqv.symm hiso'⟩
  -- The root-placement of a member is forced to be `0` or `1`, and that determines it entirely.
  have hroot : ∀ (H : LabeledGraph vtype (Fin 2)),
      H ∈ isoLabeledGraphSetWithSameGraph edgeLabeled →
      H = edgeLabeled ∨ H = edgeLabeled' := by
    rintro ⟨Hgraph, Hembed⟩ ⟨hgr, _⟩
    -- The underlying graph of `H` is `⊤`.
    have hgr' : Hgraph = edgeGraph := hgr.symm
    subst hgr'
    -- The embedding is determined by the image of `(0 : Fin 1)`, which is `0` or `1`.
    rcases Fin.exists_fin_two.mp ⟨Hembed 0, rfl⟩ with h0 | h1
    · left
      have : Hembed = edgeLabeled.type_embed := by
        apply RelEmbedding.ext; intro t
        rw [Subsingleton.elim t 0]; exact h0
      simp only [edgeLabeled]; congr
    · right
      have : Hembed = edgeLabeled'.type_embed := by
        apply RelEmbedding.ext; intro t
        rw [Subsingleton.elim t 0]; exact h1
      simp only [edgeLabeled']; congr
  -- `edgeLabeled ≠ edgeLabeled'` because their roots differ (`0 ≠ 1`).
  have hne : (edgeLabeled : LabeledGraph vtype (Fin 2)) ≠ edgeLabeled' := by
    intro h
    have : edgeLabeled.type_embed 0 = edgeLabeled'.type_embed 0 := by rw [h]
    exact absurd this (by decide)
  -- The iso-set's `Finset` is exactly `{edgeLabeled, edgeLabeled'}`, hence has card `2`.
  dsimp only [isomorphismCount]
  rw [show (isoLabeledGraphSetWithSameGraph edgeLabeled).toFinset
        = ({edgeLabeled, edgeLabeled'} : Finset (LabeledGraph vtype (Fin 2))) from ?_]
  · rw [Finset.card_pair hne]
  · ext H
    simp only [Set.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hH; exact hroot H hH
    · rintro (rfl | rfl); exacts [hmem0, hmem1]

/-- The unlabelling weight of the one-root edge flag is `1`: the edge `K₂` admits exactly two
type-embeddings of the root (`isomorphismCount edgeLabeled = 2`), and the descending-factorial
normaliser is `2!/1! = 2`.  Consequently `φ₀ ρ` equals the *unlabelled edge density* of the base
limit (no scaling), so `ρ` is a genuine `[0,1]`-valued density. -/
theorem downwardNormalizingFactor_edge_eq_one :
    downwardNormalizingFactor edgeFF.2 = 1 := by
  show downwardNormalizingFactor (⟦edgeLabeled⟧ : Flag vtype (Fin 2)) = 1
  rw [downwardNormalizingFactor, Quotient.lift_mk, downwardNormalizingFactor_labeledGraph,
    isomorphismCount_edgeLabeled]
  norm_num

/-- An induced embedding `f : H ↪g G` complements to an induced embedding `Hᶜ ↪g Gᶜ`: it has the
same underlying (injective) map, and `Gᶜ.Adj (f a) (f b) ↔ Hᶜ.Adj a b` since complementation only
negates adjacency and `f` preserves both adjacency and distinctness. -/
private def complEmbedding {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W} (f : H ↪g G) :
    Hᶜ ↪g Gᶜ where
  toFun := f
  inj' := f.injective
  map_rel_iff' := by
    intro a b
    show Gᶜ.Adj (f a) (f b) ↔ Hᶜ.Adj a b
    simp only [SimpleGraph.compl_adj]
    rw [f.injective.ne_iff, f.map_rel_iff]

/-- **The complement-of-`C₄`-free class.**  `G` is in the class iff `Gᶜ` contains no `C₄`.  It is
hereditary because an induced embedding `H ↪g G` complements to an induced embedding `Hᶜ ↪g Gᶜ`. -/
def coC4FreeClass : HeredClass where
  Mem {_V} _ _ G := C4g.Free Gᶜ
  comap {_V _W} _ _ _ _ {_G} {_H} e hG := fun hc4 => hG (hc4.trans ⟨(complEmbedding e).toCopy⟩)

/-- The complement of the co-star `K_n ⊎ K_1` (rooted at the isolated vertex) is the star `K_{1,n}`;
hence each co-star lies in the complement-of-`C₄`-free class. -/
theorem coStarLabeled_coC4free (n : ℕ) : coC4FreeClass.Mem (coStarLabeled n).graph := by
  show C4g.Free (coStarLabeled n).graphᶜ
  -- The complement of the co-star is the star: `Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0)`.
  have hcompl : (coStarLabeled n).graphᶜ = (starLabeled n).graph := by
    ext i j
    simp only [SimpleGraph.compl_adj]
    show (i ≠ j ∧ ¬(i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j))
        ↔ (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0)
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp only [hi, hj, ne_eq] <;> tauto
  rw [hcompl]
  exact starLabeled_c4free n

/-- **Complementary edge counts.**  A graph and its complement partition the edges of `⊤`:
`e(G) + e(Gᶜ) = C(|V|, 2)`. -/
private theorem card_edgeFinset_add_compl {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  rw [← Finset.card_union_of_disjoint (disjoint_edgeFinset.mpr disjoint_compl_right),
    ← card_edgeFinset_top_eq_card_choose_two (V := V)]
  congr 1
  ext e
  induction e with
  | _ a b =>
    simp only [Finset.mem_union, mem_edgeFinset, mem_edgeSet, top_adj, compl_adj]
    constructor
    · rintro (h | ⟨hne, _⟩)
      · exact G.ne_of_adj h
      · exact hne
    · intro hne
      by_cases hab : G.Adj a b
      · exact Or.inl hab
      · exact Or.inr ⟨hne, hab⟩

/-- **Co-edge-degeneracy.**  The complement-of-`C₄`-free class is co-edge-degenerate: every
constrained unlabelled limit has edge density `1`.  Edge density of `G` is `1 − e(Gᶜ)/C(N,2)`, and
`e(Gᶜ)` is subquadratic since `Gᶜ` is `C₄`-free (`c4free_card_edges_sq_le`), so the density tends to
`1`. -/
theorem coC4FreeClass_coEdgeDegenerate : CoEdgeDegenerate coC4FreeClass := by
  intro φ₀ hφ₀
  -- Reduce `φ₀ ρ` to the unlabelled-edge density; the normaliser is `1`.
  have hedgeunlabel : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, unlabelledEdgeFlag⟩ := rfl
  have hρ : φ₀ ρ
      = (downwardNormalizingFactor edgeFF.2 : ℝ) * φ₀.coe ⟨2, unlabelledEdgeFlag⟩ := by
    show φ₀ (downward e) = _
    rw [e, downward_basisVector, PositiveHom.map_smul, hedgeunlabel, ← PositiveHom.coe_flag]
  rw [downwardNormalizingFactor_edge_eq_one] at hρ
  -- It suffices to show the unlabelled-edge density coefficient is one.
  suffices h : φ₀.coe ⟨2, unlabelledEdgeFlag⟩ = 1 by rw [hρ, h]; norm_num
  -- The forbidden-flag hypothesis from membership in `Q₀`.
  set forb0 := (coC4FreeClass.constraintOf vtype).forb0 with hforb0def
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
  -- Each representing graph's complement is `C₄`-free.
  have hfree : ∀ t, C4g.Free ((s t).2.out.graph)ᶜ := by
    intro t
    have hmemc : coC4FreeClass.Mem ((s t).2.out.graph) := by
      apply HeredClass.mem_of_forbiddenFree coC4FreeClass ((s t).2.out)
      intro F hForb
      have hForb0 : forb0 F := by
        show ¬ coC4FreeClass.underlyingMem F.2
        have hfb : ¬ coC4FreeClass.underlyingMem (unlabel F.2) := hForb
        rwa [unlabel_emptyType] at hfb
      have hzero := hff t F hForb0
      rwa [← Quotient.out_eq (s t).2] at hzero
    exact hmemc
  -- The vertex count `N_t = (s t).1` of the representing graph.
  have hcardV : ∀ t, Fintype.card (Fin ((s t).1)) = (s t).1 := fun t => Fintype.card_fin _
  -- The complement edge density `c_t := e(Gᶜ)/C(N,2)`.
  set cseq : ℕ → ℝ := fun t =>
    ((((s t).2.out.graph)ᶜ.edgeFinset.card : ℝ) / ((s t).1).choose 2) with hcseqdef
  -- `d_t = 1 - c_t` once `N_t ≥ 1` (so `C(N,2) > 0` is not needed for the algebraic identity below;
  -- we use the additive identity directly).
  have hdc : ∀ t, 2 ≤ (s t).1 →
      flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩ = 1 - cseq t := by
    intro t hN2
    rw [hdensity t, hcseqdef]
    -- `N_t ≥ 2`, so `C(N,2) > 0`; use `e(G) + e(Gᶜ) = C(N,2)`.
    have hchoose_pos : 0 < ((s t).1).choose 2 := Nat.choose_pos hN2
    have hadd := card_edgeFinset_add_compl ((s t).2.out.graph)
    rw [hcardV t] at hadd
    have hchooseR : (0 : ℝ) < (((s t).1).choose 2 : ℝ) := by exact_mod_cast hchoose_pos
    have hsum : ((((s t).2.out.graph).edgeFinset.card : ℝ)
        + (((s t).2.out.graph)ᶜ.edgeFinset.card : ℝ)) = (((s t).1).choose 2 : ℝ) := by
      exact_mod_cast hadd
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (ne_of_gt hchooseR)]
    push_cast
    linarith
  -- The complement density squared is bounded by `2N/(N-1)²` and tends to `0`.
  have hbound : ∀ t, 2 ≤ (s t).1 → (cseq t) ^ 2 ≤ 2 * ((s t).1 : ℝ) / (((s t).1 : ℝ) - 1) ^ 2 := by
    intro t ht
    -- `c4free_card_edges_sq_le` may pick a different `DecidableRel` instance for `edgeFinset`;
    -- the cardinality is instance-independent, so transport the bound to the ambient instance.
    have hsq : (2 * ((s t).2.out.graph)ᶜ.edgeFinset.card) ^ 2 ≤ 2 * ((s t).1) ^ 3 := by
      have h := c4free_card_edges_sq_le ((s t).2.out.graph)ᶜ (hfree t)
      convert h using 6
    have hb := edgeDensity_sq_bound ((s t).2.out.graph)ᶜ.edgeFinset.card (s t).1 ht hsq
    -- `cseq t` is the same density.
    have hcseq : cseq t = (((s t).2.out.graph)ᶜ.edgeFinset.card : ℝ) / ((s t).1).choose 2 := by
      simp only [hcseqdef]
    rw [hcseq]
    exact hb
  have hNtop : Tendsto (fun t => ((s t).1 : ℕ)) atTop atTop :=
    hinc.tendsto_atTop
  have hub : Tendsto (fun t => 2 * ((s t).1 : ℝ) / (((s t).1 : ℝ) - 1) ^ 2)
      atTop (𝓝 0) := edgeDensity_bound_tendsto_zero.comp hNtop
  -- `c_t² → 0`, hence `c_t → 0`.
  have hcsq0 : Tendsto (fun t => (cseq t) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t => 2 * ((s t).1 : ℝ) / (((s t).1 : ℝ) - 1) ^ 2) ?_ ?_ hub
    · filter_upwards with t using sq_nonneg _
    · obtain ⟨T, hT⟩ := hinc.eventually_ge 2
      filter_upwards [eventually_ge_atTop T] with t ht
      exact hbound t (hT t ht)
  have hc0 : Tendsto cseq atTop (𝓝 0) := by
    have := (hcsq0.sqrt)
    simp only [Real.sqrt_zero] at this
    have heq : ∀ t, Real.sqrt ((cseq t) ^ 2) = cseq t := by
      intro t
      rw [Real.sqrt_sq]
      rw [hcseqdef]
      positivity
    simpa only [heq] using this
  -- `d_t → 1 - 0 = 1`, eventually `d_t = 1 - c_t`.
  have hd1 : Tendsto (fun t => flagDensitySeq s t ⟨2, unlabelledEdgeFlag⟩)
      atTop (𝓝 1) := by
    have hsub : Tendsto (fun t => 1 - cseq t) atTop (𝓝 (1 - 0)) :=
      (tendsto_const_nhds).sub hc0
    rw [sub_zero] at hsub
    apply hsub.congr'
    obtain ⟨T, hT⟩ := hinc.eventually_ge 2
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hdc t (hT t ht)).symm
  -- Uniqueness of limits forces `L = 1`.
  exact tendsto_nhds_unique hlim hd1

/-- **`cor:codegenerate` (concrete dense obstruction).**  The complement of the `C₄`-free class is a
*dense* hereditary class that is not root-plantable at the one-vertex type: `e − 𝟙_vtype` is
non-negative almost surely under every admissible one-root random extension, but negative at some
point of `Q_vtype`.  Together with `c4free_not_rootPlantable` this shows root-plantability is
governed by boundary pinning, not by sparsity or density. -/
theorem coC4free_not_rootPlantable :
    ¬ RootPlantable (coC4FreeClass.constraintOf vtype) :=
  coDegenerate_not_rootPlantable coC4FreeClass coC4FreeClass_coEdgeDegenerate
    (fun N => ⟨N, le_rfl, coStarLabeled_coC4free N⟩)

end FlagAlgebras.MetaTheory
