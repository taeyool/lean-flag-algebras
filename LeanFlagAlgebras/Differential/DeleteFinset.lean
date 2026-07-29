import «LeanFlagAlgebras».Differential.Ensemble

/-! # Carrier-generic densities and iterated vertex deletion

Support for Razborov's iterated-deletion estimates (29)–(33): the one-step
Lemma 4.2 a) was proved on the canonical carriers `Fin (L+1)`, but deleting a
*set* of vertices one at a time naturally lives on subtype carriers. This
file provides:

* `pdensityVec g X` / `pEval g X v` — the linear density of a formal
  combination of models in a host `X` on an **arbitrary** finite carrier, and
  the rooted evaluation `p^{(X,v)}(g)`; both are isomorphism-invariant and
  agree with `densityEval` on `Fin` carriers;
* `deleteFinset N W` — the graph `N` with a finite set `W` of vertices
  removed (a single-level subtype carrier), with the bookkeeping isomorphisms
  `deleteFinset N ∅ ≅ N` and
  `deleteVertex (deleteFinset N W) w ≅ deleteFinset N (insert w W)`;
* `vertex_deletion_pdensity` — Lemma 4.2 a) transported to arbitrary
  carriers: `p(g, N − v) = p(g, N) + (1/|V|) · p^{(N,v)}(∂₁ g)`. -/

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## Carrier-generic densities -/

/-- The linear density of a formal combination of models in a host on an
arbitrary finite carrier. Agrees with `densityEval` on `Fin` carriers. -/
noncomputable def pdensityVec {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector ∅ₜ) (X : LabeledGraph ∅ₜ V) : ℝ :=
  linearExtension (fun M : FinFlag ∅ₜ => (flagDensity₁ M.2 (⟦X⟧ : Flag ∅ₜ V) : ℝ)) g

/-- The rooted evaluation `p^{(X,v)}(g)` of a formal combination of `1`-flags
on an arbitrary finite carrier. -/
noncomputable def pEval {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector vertexType) (X : LabeledGraph ∅ₜ V) (v : V) : ℝ :=
  linearExtension
    (fun F : FinFlag vertexType => (flagDensity₁ F.2 (⟦rootedAt X v⟧ : Flag vertexType V) : ℝ)) g

theorem pdensityVec_fin {L : ℕ} (g : FlagVector ∅ₜ) (X : LabeledGraph ∅ₜ (Fin L))
    : pdensityVec g X = densityEval g ⟨L, ⟦X⟧⟩
  := rfl

theorem pEval_fin {L : ℕ} (g : FlagVector vertexType) (X : LabeledGraph ∅ₜ (Fin L)) (v : Fin L)
    : pEval g X v = densityEval g ⟨L, ⟦rootedAt X v⟧⟩
  := rfl

/-- Density of a fixed flag is invariant under isomorphism of the host, even
across different carriers. -/
theorem flagDensity₁_congr_iso {U V W : Type} [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : Flag σ W) {X : LabeledGraph σ U} {Y : LabeledGraph σ V} (φ : X ≃f Y)
    : flagDensity₁ F (⟦X⟧ : Flag σ U) = flagDensity₁ F (⟦Y⟧ : Flag σ V)
  := by
  conv_lhs => rw [← Quotient.out_eq F, flagDensity₁_mk]
  conv_rhs => rw [← Quotient.out_eq F, flagDensity₁_mk]
  exact labeledGraphDensity_respect_eqv φ LabeledGraphIso.refl

theorem flagDensity₁_getCanonicalFlag {U W : Type} [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W] {ℓ : ℕ}
    (F : Flag σ U) (X : LabeledGraph σ W) (h : Fintype.card W = ℓ)
    : flagDensity₁ F (getCanonicalFlag X h) = flagDensity₁ F (⟦X⟧ : Flag σ W)
  := by
  conv_lhs => rw [← Quotient.out_eq F, ← Quotient.out_eq (getCanonicalFlag X h), flagDensity₁_mk]
  conv_rhs => rw [← Quotient.out_eq F, flagDensity₁_mk]
  exact labeledGraphDensity_respect_eqv (getCanonicalFlag_iso X h) LabeledGraphIso.refl

theorem pdensityVec_congr {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (g : FlagVector ∅ₜ) {X : LabeledGraph ∅ₜ U} {Y : LabeledGraph ∅ₜ V} (φ : X ≃f Y)
    : pdensityVec g X = pdensityVec g Y
  := by
  dsimp only [pdensityVec, linearExtension]
  apply Finset.sum_congr rfl
  intro M _
  rw [flagDensity₁_congr_iso M.2 φ]

/-- Transport rooting along an isomorphism. -/
noncomputable def rootedAtIso {U V : Type} {X : LabeledGraph ∅ₜ U} {Y : LabeledGraph ∅ₜ V}
    (φ : X ≃f Y) (v : U) (w : V) (hw : φ.graph_iso v = w)
    : rootedAt X v ≃f rootedAt Y w where
  graph_iso := φ.graph_iso
  type_preserve := by
    funext t
    show φ.graph_iso v = w
    exact hw

theorem pEval_congr {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (g : FlagVector vertexType) {X : LabeledGraph ∅ₜ U} {Y : LabeledGraph ∅ₜ V}
    (φ : X ≃f Y) (v : U) (w : V) (hw : φ.graph_iso v = w)
    : pEval g X v = pEval g Y w
  := by
  dsimp only [pEval, linearExtension]
  apply Finset.sum_congr rfl
  intro F _
  rw [flagDensity₁_congr_iso F.2 (rootedAtIso φ v w hw)]

/-- The rooted evaluation is bounded by the ℓ¹-norm of the coefficients. -/
theorem abs_pEval_le {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector vertexType) (X : LabeledGraph ∅ₜ V) (v : V)
    : |pEval g X v| ≤ ∑ F ∈ g.support, |g F|
  := by
  dsimp only [pEval, linearExtension]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro F _
  rw [smul_eq_mul, abs_mul]
  have h₀ : (0 : ℚ) ≤ flagDensity₁ F.2 (⟦rootedAt X v⟧ : Flag vertexType V) :=
    flagListDensity_ge_zero _ _
  have h₁ : flagDensity₁ F.2 (⟦rootedAt X v⟧ : Flag vertexType V) ≤ 1 :=
    flagListDensity_le_one _ _
  have h2 : |(flagDensity₁ F.2 (⟦rootedAt X v⟧ : Flag vertexType V) : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ (flagDensity₁ F.2 (⟦rootedAt X v⟧ : Flag vertexType V) : ℝ) := by
        exact_mod_cast h₀
      linarith
    · exact_mod_cast h₁
  calc |g F| * |(flagDensity₁ F.2 (⟦rootedAt X v⟧ : Flag vertexType V) : ℝ)|
      ≤ |g F| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |g F| := mul_one _

/-! ## Deleting a finite set of vertices -/

/-- The graph `N` with the vertices of `W` removed. -/
def deleteFinset {V : Type} (N : LabeledGraph ∅ₜ V) (W : Finset V)
    : LabeledGraph ∅ₜ {u : V // u ∉ W} where
  graph := N.graph.comap (fun u => u.val)
  type_embed := RelEmbedding.ofIsEmpty _ _

theorem card_deleteFinset {V : Type} [Fintype V] [DecidableEq V] (W : Finset V)
    : Fintype.card {u : V // u ∉ W} = Fintype.card V - W.card
  := by
  rw [Fintype.card_subtype_compl]
  congr 1
  exact Fintype.card_coe W

/-- Deleting nothing is the identity. -/
noncomputable def deleteFinsetEmptyIso {V : Type} (N : LabeledGraph ∅ₜ V)
    : deleteFinset N ∅ ≃f N where
  graph_iso := {
    toEquiv := Equiv.subtypeUnivEquiv (fun x => Finset.notMem_empty x)
    map_rel_iff' := Iff.rfl
  }
  type_preserve := by
    ext x
    exact x.elim0

/-- Deleting `insert w W` is deleting `W` and then `w`. -/
noncomputable def deleteFinsetInsertIso {V : Type} (N : LabeledGraph ∅ₜ V)
    (W : Finset V) (w : V) (hw : w ∉ W)
    : deleteVertex (deleteFinset N W) ⟨w, hw⟩ ≃f deleteFinset N (insert w W) where
  graph_iso := {
    toFun := fun a => ⟨a.val.val, by
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, a.val.property⟩
      intro hc
      exact a.property (Subtype.ext hc)⟩
    invFun := fun b => ⟨⟨b.val, by
        have hb := b.property
        simp only [Finset.mem_insert, not_or] at hb
        exact hb.2⟩, by
      intro hc
      have h1 := congrArg Subtype.val hc
      have hb := b.property
      simp only [Finset.mem_insert, not_or] at hb
      exact hb.1 h1⟩
    left_inv := fun a => rfl
    right_inv := fun b => rfl
    map_rel_iff' := Iff.rfl
  }
  type_preserve := by
    ext x
    exact x.elim0

/-! ## Lemma 4.2 a) on arbitrary carriers -/

/-- **Lemma 4.2 a), carrier-generic vector form**: for a graph `N` on any
`(n+1)`-element carrier, a vertex `v` and a combination of models `g`
supported on sizes `≤ n`,

`p(g, N − v) = p(g, N) + (1/(n+1)) · p^{(N,v)}(∂₁ g)`. -/
theorem vertex_deletion_pdensity {V : Type} [Fintype V] [DecidableEq V]
    (g : FlagVector ∅ₜ) {n : ℕ} (hV : Fintype.card V = n + 1)
    (h_supp : ∀ M ∈ g.support, M.1 ≤ n)
    (N : LabeledGraph ∅ₜ V) (v : V)
    : pdensityVec g (deleteVertex N v)
      = pdensityVec g N + (1 / ((n : ℝ) + 1)) * pEval (partialVertexVec g) N v
  := by
  set e : V ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hV with he
  set N' : LabeledGraph ∅ₜ (Fin (n + 1)) := labeledGraphFromVertexIso N e with hN'
  have hev : (labeledGraphFromVertexIso_iso N e).graph_iso v = e v := rfl
  have h1 : pdensityVec g N = densityEval g ⟨n + 1, ⟦N'⟧⟩ := by
    rw [← pdensityVec_fin]
    exact pdensityVec_congr g (labeledGraphFromVertexIso_iso N e)
  have h2 : pEval (partialVertexVec g) N v
      = densityEval (partialVertexVec g) ⟨n + 1, ⟦rootedAt N' (e v)⟧⟩ := by
    rw [← pEval_fin]
    exact pEval_congr _ (labeledGraphFromVertexIso_iso N e) v (e v) hev
  have h3 : pdensityVec g (deleteVertex N v) = densityEval g ⟨n, deleteVertexFlag N' (e v)⟩ := by
    have hdel : deleteVertex N v ≃f deleteVertex N' (e v) :=
      deleteVertexIso (labeledGraphFromVertexIso_iso N e) v (e v) hev
    have h4 : pdensityVec g (deleteVertex N v) = pdensityVec g (deleteVertex N' (e v)) :=
      pdensityVec_congr g hdel
    rw [h4]
    dsimp only [pdensityVec, densityEval, linearExtension]
    apply Finset.sum_congr rfl
    intro M _
    show g M • ((flagDensity₁ M.2 (⟦deleteVertex N' (e v)⟧ : Flag ∅ₜ _) : ℝ))
      = g M • ((flagDensity₁ M.2 (deleteVertexFlag N' (e v)) : ℝ))
    congr 1
    rw [Rat.cast_inj]
    exact (flagDensity₁_getCanonicalFlag M.2 (deleteVertex N' (e v)) (card_ne_vertex (e v))).symm
  rw [h1, h2, h3]
  exact vertex_deletion_density_vec g h_supp N' (e v)

end Differential
end FlagAlgebras
