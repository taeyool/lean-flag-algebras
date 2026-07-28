import «LeanFlagAlgebras».Differential.Eval
import «LeanFlagAlgebras».Differential.SubsetCount
import Mathlib.Tactic.LinearCombination

/-! # The vertex-deletion operator `∂₁` (Razborov §4.3, Lemma 4.2)

This file develops, for the theory of simple graphs, the first differential
operator of Razborov's §4.3 "Differential methods":

* `vertexType` — the (unique, since graphs are vertex uniform) type `1` of
  size one;
* `rootedAt N v` — the `1`-flag `(N, v)` obtained by placing the label at `v`;
* `deleteVertexFlag N v` — the flag of `N − v` on the canonical carrier;
* `muVec σ M` — Razborov's auxiliary labelling operator `μ_ℓ^σ(M) = ∑ {F ∈
  ℱ_ℓ^σ | F|₀ ≅ M}` (stated for arbitrary `σ`, used at `σ = 1, E, Ē`);
* `piVertexVec M` — the model-level upward operator
  `π¹(M) = ∑ {F ∈ ℱ_{ℓ+1}¹ | F↓ ≅ M}` (attach a labelled root in all ways);
* `partialVertexVec` — the vertex-deletion operator
  `∂₁ M = ℓ (π¹(M) − μ_ℓ¹(M))`, extended linearly to `ℝℱ⁰`;
* `partialVertex` — the induced linear map `A⁰ → A¹` (Lemma 4.2 b)).

The main results are Razborov's Lemma 4.2:

* a) `vertex_deletion_density` : for a model `M` on `ℓ` vertices, a graph `N`
  on `L + 1 ≥ ℓ + 1` vertices and `v ∈ V(N)`,
  `p(M, N − v) = p(M, N) + (1/(L+1)) · p^{(N,v)}(∂₁ M)`;
* b) `partialVertexVec_zeroSpace` : `∂₁(K⁰) ⊆ K¹`, so `∂₁` descends to a
  linear map `partialVertex : A⁰ → A¹`;
* c) `downward_partialVertexVec` : `⟦∂₁ f⟧₁ = 0` for every `f ∈ A⁰`.

The two purely combinatorial counting identities feeding a) —
`sum_rootExtensions_density` (`p^{(N,v)}(π¹ M) = p(M, N − v)`) and
`total_probability_vertex` (conditioning a uniformly random `ℓ`-subset on
whether it contains `v`) — are stated here and proved by exhibiting explicit
bijections between the relevant sets of labelled subgraphs. -/

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

/-! ## The one-vertex type and rooted flags -/

/-- The type `1` of size one: a single labelled vertex (no edges). Since the
theory of graphs is vertex uniform this is *the* type of size one. -/
abbrev vertexType : FlagType (Fin 1) := ⊥

/-- The `1`-flag `(N, v)`: the (unlabelled) graph `N` with its single label
placed at the vertex `v`. -/
def rootedAt {V : Type} (N : LabeledGraph ∅ₜ V) (v : V) : LabeledGraph vertexType V where
  graph := N.graph
  type_embed := {
    toFun := fun _ => v
    inj' := fun a b _ => Subsingleton.elim a b
    map_rel_iff' := by
      intro a b
      constructor
      · intro h
        exact absurd h (N.graph.irrefl)
      · intro h
        simp only [SimpleGraph.bot_adj] at h
  }

@[simp]
theorem rootedAt_graph {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    : (rootedAt N v).graph = N.graph
  := rfl

@[simp]
theorem rootedAt_type_embed {V : Type} (N : LabeledGraph ∅ₜ V) (v : V) (i : Fin 1)
    : (rootedAt N v).type_embed i = v
  := rfl

/-- Every `1`-flag is of the form `rootedAt N v`: rooting the underlying
unlabelled graph at the labelled vertex recovers the flag. -/
theorem rootedAt_unlabeledGraph_self {V : Type} (G : LabeledGraph vertexType V)
    : rootedAt (unlabeledGraph G) (G.type_embed 0) = G
  := by
  obtain ⟨graph, emb⟩ := G
  dsimp only [rootedAt, unlabeledGraph]
  congr 1
  ext x
  have hx : x = 0 := Subsingleton.elim x 0
  subst hx
  rfl

/-! ## Vertex deletion -/

theorem card_ne_vertex {L : ℕ} (v : Fin (L + 1))
    : Fintype.card {u : Fin (L + 1) // u ≠ v} = L
  := by
  simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq,
    Nat.add_sub_cancel]

/-- The graph `N` with the vertex `v` deleted, as a labelled graph on the
subtype `{u // u ≠ v}`. -/
def deleteVertex {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    : LabeledGraph ∅ₜ {u : V // u ≠ v} where
  graph := N.graph.comap (fun u => u.val)
  type_embed := RelEmbedding.ofIsEmpty _ _

@[simp]
theorem deleteVertex_adj {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    (u w : {u : V // u ≠ v})
    : (deleteVertex N v).graph.Adj u w ↔ N.graph.Adj u.val w.val
  := Iff.rfl

/-- The flag of `N − v` on the canonical carrier `Fin L`. -/
noncomputable def deleteVertexFlag {L : ℕ} (N : LabeledGraph ∅ₜ (Fin (L + 1))) (v : Fin (L + 1))
    : Flag ∅ₜ (Fin L)
  :=
  getCanonicalFlag (deleteVertex N v) (card_ne_vertex v)

/-! ## The labelling operator `μ_ℓ^σ` and the upward operator `π¹` -/

variable {n₀ : ℕ}

/-- Razborov's auxiliary labelling operator `μ_ℓ^σ`: the sum of all `σ`-flags
on the same vertex set whose underlying unlabelled flag is `M`, i.e. all ways
of placing the labels of `σ` onto the vertices of `M`. (Unlike `π^σ` this map
does *not* respect the zero spaces, cf. Razborov §4.3.) -/
noncomputable def muVec (σ : FlagType (Fin n₀)) (M : FinFlag ∅ₜ) : FlagVector σ :=
  ∑ F ∈ labelExtensions M.2 σ, basisVector ⟨M.1, F⟩

/-- Remove the labelled root of a `1`-flag, keeping all other vertices. -/
def unroot {V : Type} (F : LabeledGraph vertexType V)
    : LabeledGraph ∅ₜ {u : V // u ≠ F.type_embed 0}
  :=
  deleteVertex (unlabeledGraph F) (F.type_embed 0)

/-- The flag of a `1`-flag with its root removed, on the canonical carrier. -/
noncomputable def unrootFlag {L : ℕ} (F : LabeledGraph vertexType (Fin (L + 1)))
    : Flag ∅ₜ (Fin L)
  :=
  getCanonicalFlag (unroot F) (card_ne_vertex (F.type_embed 0))

/-- The root extensions of an unlabelled flag `M` on `ℓ` vertices: all
`1`-flags on `ℓ + 1` vertices whose root-deleted flag is `M`. -/
noncomputable def rootExtensions {ℓ : ℕ} (M : FlagWithSize ∅ₜ ℓ)
    : Finset (FlagWithSize vertexType (ℓ + 1))
  :=
  {F : FlagWithSize vertexType (ℓ + 1) | unrootFlag F.out = M}

/-- Razborov's model-level upward operator `π¹(M)`: the sum of all `1`-flags
obtained from `M` by attaching a new labelled root in every possible way. -/
noncomputable def piVertexVec (M : FinFlag ∅ₜ) : FlagVector vertexType :=
  ∑ F ∈ rootExtensions M.2, basisVector ⟨M.1 + 1, F⟩

/-- Razborov's vertex-deletion operator on formal combinations of models:
`∂₁ M = ℓ (π¹(M) − μ_ℓ¹(M))` for a model `M` on `ℓ` vertices, extended
linearly to `ℝℱ⁰`. -/
noncomputable def partialVertexVec : FlagVector ∅ₜ → FlagVector vertexType :=
  linearExtension (fun M : FinFlag ∅ₜ => (M.1 : ℝ) • (piVertexVec M - muVec vertexType M))

@[simp]
theorem partialVertexVec_basisVector (M : FinFlag ∅ₜ)
    : partialVertexVec (basisVector M) = (M.1 : ℝ) • (piVertexVec M - muVec vertexType M)
  := by
  dsimp only [partialVertexVec]
  rw [linearExtension_basisVector]

theorem partialVertexVec_sub (f f' : FlagVector ∅ₜ)
    : partialVertexVec (f - f') = partialVertexVec f - partialVertexVec f'
  := by
  dsimp only [partialVertexVec]
  rw [linearExtension_sub]

theorem partialVertexVec_eq_sum (f : FlagVector ∅ₜ)
    : partialVertexVec f = ∑ M ∈ f.support, f M • partialVertexVec (basisVector M)
  := by
  simp_rw [partialVertexVec_basisVector]
  rfl

/-! ## Density evaluations of `μ` and `π` -/

theorem densityEval_muVec {σ : FlagType (Fin n₀)} (M : FinFlag ∅ₜ) (R : FinFlag σ)
    : densityEval (muVec σ M) R = ∑ F ∈ labelExtensions M.2 σ, (flagDensity₁ F R.2 : ℝ)
  := by
  dsimp only [muVec]
  rw [densityEval_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [densityEval_basisVector]

theorem densityEval_piVertexVec (M : FinFlag ∅ₜ) (R : FinFlag vertexType)
    : densityEval (piVertexVec M) R = ∑ F ∈ rootExtensions M.2, (flagDensity₁ F R.2 : ℝ)
  := by
  dsimp only [piVertexVec]
  rw [densityEval_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [densityEval_basisVector]

/-! ## Glue lemmas for the counting identities -/

theorem emptyType_type_verts {W : Type} (X : LabeledGraph ∅ₜ W)
    : X.type_verts = ∅
  := by
  dsimp only [LabeledGraph.type_verts]
  simp only [Set.image_univ, Matrix.range_empty]

theorem emptyType_type_verts_subset {W : Type} (X : LabeledGraph ∅ₜ W) (S : Set W)
    : X.type_verts ⊆ S
  := by
  rw [emptyType_type_verts]
  exact Set.empty_subset S

theorem rootedAt_type_verts_subset {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    {S : Set V} (hv : v ∈ S)
    : (rootedAt N v).type_verts ⊆ S
  := by
  intro u hu
  rw [LabeledGraph.mem_type_verts] at hu
  obtain ⟨t, rfl⟩ := hu
  exact hv

theorem mem_of_rootedAt_type_verts_subset {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    {S : Set V} (h : (rootedAt N v).type_verts ⊆ S)
    : v ∈ S
  :=
  h ((rootedAt N v).type_verts_contain 0)

theorem unlabel_out (F : Flag vertexType V)
    : unlabel F = ⟦unlabeledGraph F.out⟧
  := by
  conv_lhs => rw [← Quotient.out_eq F]
  rfl

/-- Transport a labelled-graph isomorphism through unlabelling (the concrete
isomorphism, not just its existence). -/
def unlabeledGraphIso {V W : Type} {G : LabeledGraph vertexType V}
    {G' : LabeledGraph vertexType W} (φ : G ≃f G')
    : unlabeledGraph G ≃f unlabeledGraph G' where
  graph_iso := φ.graph_iso
  type_preserve := by
    ext x
    exact x.elim0

/-- Unlabelling an induced subgraph of a rooted flag gives the corresponding
induced subgraph of the underlying unlabelled graph. -/
theorem unlabeledGraph_induced_rootedAt {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    (S : Set V) (hsub : (rootedAt N v).type_verts ⊆ S)
    : unlabeledGraph ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).coe)
      = (LabeledSubgraph.inducedLabeledSubgraph N S (emptyType_type_verts_subset N S)).coe
  :=
  emptyType_labeledGraph_ext rfl

/-- The canonical isomorphism between an induced subgraph of `N − v` and the
corresponding induced subgraph of `N` (on the image vertex set). -/
noncomputable def deleteVertex_induce_iso {V : Type} (N : LabeledGraph ∅ₜ V) (v : V)
    (S' : Set {u : V // u ≠ v})
    : (LabeledSubgraph.inducedLabeledSubgraph (deleteVertex N v) S'
        (emptyType_type_verts_subset _ S')).coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph N (Subtype.val '' S')
        (emptyType_type_verts_subset N _)).coe where
  graph_iso := {
    toEquiv := Equiv.Set.image Subtype.val S' Subtype.val_injective
    map_rel_iff' := by
      intro a b
      simp only [LabeledSubgraph.coe_graph, SimpleGraph.Subgraph.coe_adj,
        SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj]
      constructor
      · rintro ⟨_, _, h⟩
        exact ⟨a.property, b.property, h⟩
      · rintro ⟨_, _, h⟩
        refine ⟨?_, ?_, h⟩
        · simp only [Set.mem_image, Subtype.exists, Subtype.coe_eta]
          exact ⟨a.val.val, a.val.property, a.property, rfl⟩
        · simp only [Set.mem_image, Subtype.exists, Subtype.coe_eta]
          exact ⟨b.val.val, b.val.property, b.property, rfl⟩
  }
  type_preserve := by
    ext x
    exact x.elim0

theorem labelExtensions_eq_filter {ℓ : ℕ} (M : FlagWithSize ∅ₜ ℓ) (σ' : FlagType (Fin n₀))
    : labelExtensions M σ' = Finset.univ.filter (fun F => unlabel F = M)
  := rfl

theorem rootExtensions_eq_filter {ℓ : ℕ} (M : FlagWithSize ∅ₜ ℓ)
    : rootExtensions M = Finset.univ.filter (fun F => unrootFlag F.out = M)
  := rfl

/-- Transport `deleteVertex` along a labelled-graph isomorphism. -/
noncomputable def deleteVertexIso {V W : Type} {A : LabeledGraph ∅ₜ V} {B : LabeledGraph ∅ₜ W}
    (φ : A ≃f B) (v : V) (w : W) (hw : φ.graph_iso v = w)
    : deleteVertex A v ≃f deleteVertex B w where
  graph_iso := {
    toEquiv := Equiv.subtypeEquiv φ.graph_iso.toEquiv (fun u => by
      subst hw
      simp only [RelIso.coe_fn_toEquiv, ne_eq, not_iff_not]
      exact (Equiv.apply_eq_iff_eq φ.graph_iso.toEquiv).symm)
    map_rel_iff' := by
      intro a b
      simp only [RelIso.coe_fn_toEquiv, Equiv.subtypeEquiv_apply]
      exact φ.graph_iso.map_adj_iff
  }
  type_preserve := by
    ext x
    exact x.elim0

/-- Transport `unroot` along a labelled-graph isomorphism of `1`-flags. -/
noncomputable def unrootIso {V W : Type} {G : LabeledGraph vertexType V}
    {G' : LabeledGraph vertexType W} (φ : G ≃f G')
    : unroot G ≃f unroot G'
  :=
  deleteVertexIso (unlabeledGraphIso φ) (G.type_embed 0) (G'.type_embed 0)
    (congrFun φ.type_preserve 0)

/-- Unrooting the induced subgraph of `(N, v)` on `S ∋ v` gives the induced
subgraph of `N − v` on `S − v` (as a preimage). This is the key glue between
the root extensions of a model and the vertex-deleted host. -/
noncomputable def unroot_induced_rootedAt_iso {L : ℕ} (N : LabeledGraph ∅ₜ (Fin (L + 1)))
    (v : Fin (L + 1)) (S : Set (Fin (L + 1))) (hsub : (rootedAt N v).type_verts ⊆ S)
    : unroot ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).coe)
      ≃f (LabeledSubgraph.inducedLabeledSubgraph (deleteVertex N v)
          (Subtype.val ⁻¹' S) (emptyType_type_verts_subset _ _)).coe where
  graph_iso := {
    toFun := fun a =>
      ⟨⟨a.val.val, fun hav => a.property (Subtype.ext (by
          rw [hav]
          exact ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).embed_eq 0).symm))⟩,
        a.val.property⟩
    invFun := fun b =>
      ⟨⟨b.val.val, b.property⟩, fun hb => b.val.property (by
          have := congrArg (fun x => (Subtype.val x : Fin (L + 1))) hb
          simpa using this)⟩
    left_inv := fun a => rfl
    right_inv := fun b => rfl
    map_rel_iff' := by
      intro a b
      constructor
      · rintro ⟨_, _, h⟩
        exact ⟨a.val.property, b.val.property, h⟩
      · rintro ⟨_, _, h⟩
        exact ⟨a.val.property, b.val.property, h⟩
  }
  type_preserve := by
    ext x
    exact x.elim0

/-! ## The two counting identities behind Lemma 4.2 a) -/

set_option maxHeartbeats 1600000 in
/-- `p^{(N,v)}(π¹ M) = p(M, N − v)` (Razborov, proof of Lemma 4.2 a)): the
total density in `(N, v)` of all root extensions of `M` equals the density of
`M` in `N − v`. Indeed, an induced copy of a root extension of `M` in `(N, v)`
is the root `v` together with an `ℓ`-subset of `V(N) − v` inducing `M`, and
conversely. -/
theorem sum_rootExtensions_density {ℓ L : ℕ} (M : FlagWithSize ∅ₜ ℓ) (hL : ℓ ≤ L)
    (N : LabeledGraph ∅ₜ (Fin (L + 1))) (v : Fin (L + 1))
    : ∑ F ∈ rootExtensions M, flagDensity₁ F ⟦rootedAt N v⟧
      = flagDensity₁ M (deleteVertexFlag N v)
  := by
  -- Both densities have the same normalising factor `C(L, ℓ)`.
  have hterm : ∀ F ∈ rootExtensions M,
      (flagDensity₁ F ⟦rootedAt N v⟧ : ℚ)
        = ((inducingSubsets F.out (rootedAt N v)).toFinset.card : ℚ) / (L.choose ℓ) := by
    intro F _
    conv_lhs => rw [← Quotient.out_eq F]
    rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div]
    simp only [Fintype.card_fin, Nat.add_sub_cancel]
  have hdel : (flagDensity₁ M (deleteVertexFlag N v) : ℚ)
      = ((inducingSubsets M.out (deleteVertex N v)).toFinset.card : ℚ) / (L.choose ℓ) := by
    have h1 : flagDensity₁ M (deleteVertexFlag N v)
        = labeledGraphDensity M.out (deleteVertex N v) := by
      rw [flagDensity₁_out]
      exact labeledGraphDensity_respect_eqv
        (getCanonicalFlag_iso (deleteVertex N v) (card_ne_vertex v)) LabeledGraphIso.refl
    rw [h1, labeledGraphDensity_eq_card_div, card_ne_vertex v]
    simp only [Fintype.card_fin, Nat.sub_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, hdel]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  -- Count comparison via the bijection `S ↦ S ∩ (V − v)`.
  have hcnt : ∀ F ∈ rootExtensions M,
      (inducingSubsets F.out (rootedAt N v)).toFinset.card
        = labeledGraphCount F.out (rootedAt N v) := by
    intro F _
    rw [labeledGraphCount_eq_card_inducingSubsets]
  rw [Finset.sum_congr rfl hcnt, rootExtensions_eq_filter,
    sum_labeledGraphCount_filter (fun F => unrootFlag F.out = M) (rootedAt N v)]
  apply Finset.card_bij (fun (S : Set (Fin (L + 1))) (_ : S ∈ _) =>
    (Subtype.val ⁻¹' S : Set {u : Fin (L + 1) // u ≠ v}))
  · -- membership
    intro S hS
    rw [Finset.mem_biUnion] at hS
    obtain ⟨F, hF, hSF⟩ := hS
    rw [Finset.mem_filter] at hF
    obtain ⟨-, hFM⟩ := hF
    rw [Set.mem_toFinset] at hSF
    obtain ⟨hsub, ⟨ψ⟩⟩ := hSF
    rw [Set.mem_toFinset]
    refine ⟨emptyType_type_verts_subset _ _, ?_⟩
    dsimp only [unrootFlag] at hFM
    have hMun : Nonempty (M.out ≃f unroot F.out) := (getCanonicalFlag_eq_iff _ _ M).mp hFM
    exact ⟨(((unroot_induced_rootedAt_iso N v S hsub).symm.trans (unrootIso ψ)).trans
      hMun.some.symm)⟩
  · -- injectivity: members of the union all contain `v`
    intro S₁ h₁ S₂ h₂ heq
    have hmem : ∀ S, S ∈ (Finset.univ.filter
        (fun F : FlagWithSize vertexType (ℓ + 1) => unrootFlag F.out = M)).biUnion
        (fun F => (inducingSubsets F.out (rootedAt N v)).toFinset) → v ∈ S := by
      intro S hS
      rw [Finset.mem_biUnion] at hS
      obtain ⟨F, -, hSF⟩ := hS
      rw [Set.mem_toFinset] at hSF
      obtain ⟨hsub, -⟩ := hSF
      exact mem_of_rootedAt_type_verts_subset N v hsub
    have hv₁ : v ∈ S₁ := hmem S₁ h₁
    have hv₂ : v ∈ S₂ := hmem S₂ h₂
    ext u
    by_cases huv : u = v
    · subst huv
      simp only [hv₁, hv₂]
    · constructor
      · intro hu
        have h3 : (⟨u, huv⟩ : {x : Fin (L + 1) // x ≠ v}) ∈
            (Subtype.val ⁻¹' S₁ : Set {x : Fin (L + 1) // x ≠ v}) := hu
        rw [heq] at h3
        exact h3
      · intro hu
        have h3 : (⟨u, huv⟩ : {x : Fin (L + 1) // x ≠ v}) ∈
            (Subtype.val ⁻¹' S₂ : Set {x : Fin (L + 1) // x ≠ v}) := hu
        rw [← heq] at h3
        exact h3
  · -- surjectivity
    intro S' hS'
    rw [Set.mem_toFinset] at hS'
    obtain ⟨h₀, ⟨ψ₀⟩⟩ := hS'
    have h1 : v ∉ (Subtype.val '' S' : Set (Fin (L + 1))) := by
      rintro ⟨w, -, hwv⟩
      exact w.property hwv
    have hvS : v ∈ insert v (Subtype.val '' S' : Set (Fin (L + 1))) := Set.mem_insert v _
    have hsub : (rootedAt N v).type_verts ⊆ insert v (Subtype.val '' S') :=
      rootedAt_type_verts_subset N v hvS
    have hpre : (Subtype.val ⁻¹' (insert v (Subtype.val '' S'))
        : Set {u : Fin (L + 1) // u ≠ v}) = S' := by
      ext w
      simp only [Set.mem_preimage, Set.mem_insert_iff]
      constructor
      · rintro (hw | hw)
        · exact absurd hw w.property
        · obtain ⟨x, hx, hxw⟩ := hw
          have hxw' : x = w := Subtype.val_injective hxw
          exact hxw' ▸ hx
      · intro hw
        exact Or.inr ⟨w, hw, rfl⟩
    have hcardS' : Fintype.card S' = ℓ := by
      have hsz := labeledGraphIso_size_eq _ _ ψ₀
      simp only [LabeledGraph.size, Fintype.card_fin] at hsz
      exact hsz
    have hcardImg : Fintype.card (Subtype.val '' S' : Set (Fin (L + 1))) = ℓ := by
      rw [← Fintype.card_congr (Equiv.Set.image Subtype.val S' Subtype.val_injective)]
      exact hcardS'
    have hcard : Fintype.card
        ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
          (insert v (Subtype.val '' S')) hsub).subgraph.verts) = ℓ + 1 := by
      have h2 : (LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
          (insert v (Subtype.val '' S')) hsub).size = ℓ + 1 := by
        rw [LabeledSubgraph.inducedLabeledSubgraph_size, Set.card_insert _ h1, hcardImg]
      exact h2
    refine ⟨insert v (Subtype.val '' S'), ?_, hpre⟩
    rw [Finset.mem_biUnion]
    refine ⟨getCanonicalFlag
      ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
        (insert v (Subtype.val '' S')) hsub).coe) hcard, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [unrootFlag]
      rw [getCanonicalFlag_eq_iff]
      have i1 : unroot ((getCanonicalFlag
          ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
            (insert v (Subtype.val '' S')) hsub).coe) hcard).out)
          ≃f unroot ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
            (insert v (Subtype.val '' S')) hsub).coe) :=
        unrootIso (getCanonicalFlag_iso _ hcard)
      have hsets : (LabeledSubgraph.inducedLabeledSubgraph (deleteVertex N v)
          (Subtype.val ⁻¹' (insert v (Subtype.val '' S')))
          (emptyType_type_verts_subset _ _))
          = (LabeledSubgraph.inducedLabeledSubgraph (deleteVertex N v) S'
            (emptyType_type_verts_subset _ _)) := by
        apply labeledSubgraph_eq_from_subgraph_eq
        dsimp only [LabeledSubgraph.inducedLabeledSubgraph]
        rw [hpre]
      have i2 : unroot ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
          (insert v (Subtype.val '' S')) hsub).coe)
          ≃f (LabeledSubgraph.inducedLabeledSubgraph (deleteVertex N v) S'
            (emptyType_type_verts_subset _ _)).coe :=
        (unroot_induced_rootedAt_iso N v (insert v (Subtype.val '' S')) hsub).trans
          (LabeledGraphIso.labeledSubgraphIso_eq hsets)
      exact ⟨((i1.trans i2).trans ψ₀).symm⟩
    · rw [Set.mem_toFinset]
      exact ⟨hsub, ⟨(getCanonicalFlag_iso _ hcard).symm⟩⟩

/-- Total probability (Razborov, proof of Lemma 4.2 a)): condition the
uniformly random `ℓ`-subset `V ⊆ V(N)` defining `p(M, N)` on whether `v ∈ V`:
`p(M, N) = (ℓ/(L+1)) · p^{(N,v)}(μ_ℓ¹ M) + (1 − ℓ/(L+1)) · p(M, N − v)`,
where `P[N|_V ≅ M ∣ v ∈ V] = p^{(N,v)}(μ_ℓ¹(M))` and
`P[N|_V ≅ M ∣ v ∉ V] = p(M, N − v)`. -/
theorem total_probability_vertex {ℓ L : ℕ} (M : FlagWithSize ∅ₜ ℓ) (hL : ℓ ≤ L)
    (N : LabeledGraph ∅ₜ (Fin (L + 1))) (v : Fin (L + 1))
    : (flagDensity₁ M ⟦N⟧ : ℚ)
      = ((ℓ : ℚ) / ((L : ℚ) + 1))
          * (∑ F ∈ labelExtensions M vertexType, flagDensity₁ F ⟦rootedAt N v⟧)
        + (((L + 1 - ℓ : ℕ) : ℚ) / ((L : ℚ) + 1)) * flagDensity₁ M (deleteVertexFlag N v)
  := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · -- `ℓ = 0`: the empty model has density `1` everywhere and no label extensions.
    have hM : M = emptyFlag ∅ₜ := Subsingleton.elim _ _
    rw [hM, flagDensity_empty, flagDensity_empty]
    have hsum : (∑ F ∈ labelExtensions (emptyFlag ∅ₜ) vertexType,
        flagDensity₁ F ⟦rootedAt N v⟧) = 0 := by
      apply Finset.sum_eq_zero
      intro F _
      exact (F.out.type_embed 0).elim0
    rw [hsum]
    have hL1 : ((L : ℚ) + 1) ≠ 0 := by positivity
    simp only [Nat.cast_zero, zero_div, zero_mul, zero_add, Nat.sub_zero, mul_one]
    rw [eq_comm, div_eq_one_iff_eq hL1]
    push_cast
    ring
  -- Main case: write `ℓ = k + 1`.
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  set cAll : Finset (Set (Fin (L + 1))) := (inducingSubsets M.out N).toFinset with hcAll
  set cIn : Finset (Set (Fin (L + 1))) := cAll.filter (fun S => v ∈ S) with hcIn
  set cOut : Finset (Set (Fin (L + 1))) := cAll.filter (fun S => v ∉ S) with hcOut
  have hsplit : cIn.card + cOut.card = cAll.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  -- The density of `M` in `N` counts `cAll`.
  have hpN : (flagDensity₁ M ⟦N⟧ : ℚ) = (cAll.card : ℚ) / ((L + 1).choose (k + 1)) := by
    conv_lhs => rw [← Quotient.out_eq M]
    rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div, hcAll]
    simp only [Fintype.card_fin, Nat.sub_zero]
  -- The `μ`-evaluation counts `cIn`.
  have hSμ : (∑ F ∈ labelExtensions M vertexType, flagDensity₁ F ⟦rootedAt N v⟧ : ℚ)
      = (cIn.card : ℚ) / (L.choose k) := by
    have hterm : ∀ F ∈ labelExtensions M vertexType,
        (flagDensity₁ F ⟦rootedAt N v⟧ : ℚ)
          = ((inducingSubsets F.out (rootedAt N v)).toFinset.card : ℚ) / (L.choose k) := by
      intro F _
      conv_lhs => rw [← Quotient.out_eq F]
      rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div]
      simp only [Fintype.card_fin, Nat.add_sub_cancel]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    congr 1
    rw [← Nat.cast_sum]
    congr 1
    have hcnt : ∀ F ∈ labelExtensions M vertexType,
        (inducingSubsets F.out (rootedAt N v)).toFinset.card
          = labeledGraphCount F.out (rootedAt N v) := by
      intro F _
      rw [labeledGraphCount_eq_card_inducingSubsets]
    rw [Finset.sum_congr rfl hcnt, labelExtensions_eq_filter,
      sum_labeledGraphCount_filter (fun F => unlabel F = M) (rootedAt N v)]
    congr 1
    -- The union of the label-extension subset families is exactly `cIn`.
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_toFinset, hcIn, hcAll]
    constructor
    · rintro ⟨F, hF, hS⟩
      obtain ⟨hsub, ⟨ψ⟩⟩ := hS
      have hv : v ∈ S := mem_of_rootedAt_type_verts_subset N v hsub
      refine ⟨?_, hv⟩
      refine ⟨emptyType_type_verts_subset N S, ?_⟩
      have hFM : Nonempty (unlabeledGraph F.out ≃f M.out) := by
        have h2 : (⟦unlabeledGraph F.out⟧ : Flag ∅ₜ (Fin (k + 1))) = M := by
          rw [← unlabel_out F, hF]
        exact ⟨(Quotient.mk_eq_iff_out.mp h2).some⟩
      have ψu : (LabeledSubgraph.inducedLabeledSubgraph N S
          (emptyType_type_verts_subset N S)).coe ≃f unlabeledGraph F.out :=
        (unlabeledGraph_induced_rootedAt N v S hsub) ▸ (unlabeledGraphIso ψ)
      exact ⟨ψu.trans hFM.some⟩
    · rintro ⟨hSAll, hv⟩
      obtain ⟨h₀, ⟨ψ₀⟩⟩ := hSAll
      have hsub : (rootedAt N v).type_verts ⊆ S := rootedAt_type_verts_subset N v hv
      have hcard : Fintype.card
          ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).subgraph.verts)
          = k + 1 := by
        have hsz := labeledGraphIso_size_eq _ _ ψ₀
        simp only [LabeledGraph.size, Fintype.card_fin] at hsz
        exact hsz
      refine ⟨getCanonicalFlag
        ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).coe) hcard, ?_, ?_⟩
      · -- its unlabelling is `M`
        rw [unlabel_out]
        have hiso : unlabeledGraph
            (getCanonicalFlag
              ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).coe) hcard).out
            ≃f (LabeledSubgraph.inducedLabeledSubgraph N S
              (emptyType_type_verts_subset N S)).coe :=
          (unlabeledGraph_induced_rootedAt N v S hsub) ▸
            (unlabeledGraphIso (getCanonicalFlag_iso _ hcard))
        calc (⟦unlabeledGraph
            (getCanonicalFlag
              ((LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub).coe) hcard).out⟧
              : Flag ∅ₜ (Fin (k + 1)))
            = ⟦M.out⟧ := Quotient.sound ⟨hiso.trans ψ₀⟩
          _ = M := Quotient.out_eq M
      · exact ⟨hsub, ⟨(getCanonicalFlag_iso _ hcard).symm⟩⟩
  -- The density of `M` in `N − v` counts `cOut`.
  have hpDel : (flagDensity₁ M (deleteVertexFlag N v) : ℚ)
      = (cOut.card : ℚ) / (L.choose (k + 1)) := by
    have h1 : flagDensity₁ M (deleteVertexFlag N v)
        = labeledGraphDensity M.out (deleteVertex N v) := by
      rw [flagDensity₁_out]
      exact labeledGraphDensity_respect_eqv
        (getCanonicalFlag_iso (deleteVertex N v) (card_ne_vertex v)) LabeledGraphIso.refl
    rw [h1, labeledGraphDensity_eq_card_div]
    rw [card_ne_vertex v]
    simp only [Fintype.card_fin, Nat.sub_zero]
    congr 1
    rw [Nat.cast_inj]
    -- Bijection `S' ↦ val '' S'` between subsets of `N − v` and `v`-avoiding subsets of `N`.
    apply Finset.card_bij (fun (S' : Set {u : Fin (L + 1) // u ≠ v}) (_ : S' ∈ _) =>
      Subtype.val '' S')
    · intro S' hS'
      rw [Set.mem_toFinset] at hS'
      obtain ⟨_, ⟨ψ⟩⟩ := hS'
      rw [hcOut, Finset.mem_filter]
      constructor
      · rw [hcAll, Set.mem_toFinset]
        exact ⟨emptyType_type_verts_subset N _,
          ⟨((deleteVertex_induce_iso N v S').symm.trans ψ)⟩⟩
      · rintro ⟨u, _, huv⟩
        exact u.property huv
    · intro a _ b _ hab
      exact Set.image_injective.mpr Subtype.val_injective hab
    · intro S hS
      rw [hcOut, Finset.mem_filter, hcAll, Set.mem_toFinset] at hS
      obtain ⟨⟨h₀, ⟨ψ₀⟩⟩, hv⟩ := hS
      have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set {u : Fin (L + 1) // u ≠ v}) = S := by
        ext u
        constructor
        · rintro ⟨⟨w, hw⟩, hmem, rfl⟩
          exact hmem
        · intro hu
          exact ⟨⟨u, fun huv => hv (huv ▸ hu)⟩, hu, rfl⟩
      refine ⟨Subtype.val ⁻¹' S, ?_, himg⟩
      rw [Set.mem_toFinset]
      refine ⟨emptyType_type_verts_subset _ _, ?_⟩
      exact ⟨(deleteVertex_induce_iso N v _).trans (himg.symm ▸ ψ₀)⟩
  -- Assemble via the binomial identities.
  rw [hpN, hSμ, hpDel, ← hsplit]
  have hL1 : ((L : ℚ) + 1) ≠ 0 := by positivity
  have hℓL1 : k + 1 ≤ L + 1 := le_trans hL (Nat.le_succ L)
  have hd1 : (((L + 1).choose (k + 1) : ℕ) : ℚ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.choose_pos hℓL1)).ne'
  have hd2 : ((L.choose (k + 1) : ℕ) : ℚ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.choose_pos hL)).ne'
  have hd3 : ((L.choose k : ℕ) : ℚ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.choose_pos (le_trans (Nat.le_succ k) hL))).ne'
  have hb1 : ((L : ℚ) + 1) * (L.choose k) = ((L + 1).choose (k + 1)) * (k + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq L k
  have hpascal : (((L + 1).choose (k + 1) : ℕ) : ℚ) = L.choose k + L.choose (k + 1) := by
    exact_mod_cast Nat.choose_succ_succ L k
  have hcast : ((L + 1 - (k + 1) : ℕ) : ℚ) = (L : ℚ) + 1 - ((k : ℚ) + 1) := by
    rw [Nat.cast_sub hℓL1]
    push_cast
    ring
  rw [hcast]
  push_cast
  have e1 : ((k : ℚ) + 1) / ((L : ℚ) + 1) * ((cIn.card : ℚ) / (L.choose k))
      = (cIn.card : ℚ) / ((L + 1).choose (k + 1)) := by
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hL1 hd3) hd1]
    linear_combination (-(cIn.card : ℚ)) * hb1
  have e2 : ((L : ℚ) + 1 - ((k : ℚ) + 1)) / ((L : ℚ) + 1) * ((cOut.card : ℚ) / (L.choose (k + 1)))
      = (cOut.card : ℚ) / ((L + 1).choose (k + 1)) := by
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hL1 hd2) hd1]
    linear_combination (cOut.card : ℚ) * hb1 + (cOut.card : ℚ) * ((L : ℚ) + 1) * hpascal
  rw [e1, e2, div_add_div_same]

/-! ## Lemma 4.2 a) -/

/-- **Razborov, Lemma 4.2 a)** (for graphs): for a model `M` on `ℓ` vertices,
a graph `N` on `L + 1 ≥ ℓ + 1` vertices and a vertex `v` of `N`,

`p(M, N − v) = p(M, N) + (1/(L+1)) · p^{(N,v)}(∂₁ M)`. -/
theorem vertex_deletion_density (M : FinFlag ∅ₜ) {L : ℕ} (hL : M.1 ≤ L)
    (N : LabeledGraph ∅ₜ (Fin (L + 1))) (v : Fin (L + 1))
    : (flagDensity₁ M.2 (deleteVertexFlag N v) : ℝ)
      = (flagDensity₁ M.2 ⟦N⟧ : ℝ)
        + (1 / ((L : ℝ) + 1))
            * densityEval (partialVertexVec (basisVector M)) ⟨L + 1, ⟦rootedAt N v⟧⟩
  := by
  have hπ := sum_rootExtensions_density M.2 hL N v
  have hμ := total_probability_vertex M.2 hL N v
  rw [partialVertexVec_basisVector, densityEval_smul, densityEval_sub,
    densityEval_piVertexVec, densityEval_muVec]
  rw [← Rat.cast_sum, ← Rat.cast_sum, hπ]
  -- Everything is now a cast of a rational identity; prove it over `ℚ`.
  set P : ℚ := flagDensity₁ M.2 (deleteVertexFlag N v) with hP
  set p : ℚ := flagDensity₁ M.2 ⟦N⟧ with hp
  set Sμ : ℚ := ∑ F ∈ labelExtensions M.2 vertexType, flagDensity₁ F ⟦rootedAt N v⟧ with hSμ
  have hsub : ((L + 1 - M.1 : ℕ) : ℚ) = (L : ℚ) + 1 - M.1 := by
    have h1 : M.1 ≤ L + 1 := le_trans hL (Nat.le_succ L)
    push_cast [h1]
    ring
  rw [hsub] at hμ
  have key : P = p + (1 / ((L : ℚ) + 1)) * ((M.1 : ℚ) * (P - Sμ)) := by
    have h1 : ((L : ℚ) + 1) ≠ 0 := by positivity
    field_simp at hμ ⊢
    linarith [hμ]
  calc (P : ℝ) = ((p + (1 / ((L : ℚ) + 1)) * ((M.1 : ℚ) * (P - Sμ))) : ℚ) := by
        exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) key
    _ = (p : ℝ) + 1 / ((L : ℝ) + 1) * ((M.1 : ℝ) * ((P : ℝ) - (Sμ : ℝ))) := by
        push_cast
        ring

/-- Linear extension of Lemma 4.2 a) to arbitrary formal combinations of
models supported on sizes `≤ L`. -/
theorem vertex_deletion_density_vec (f : FlagVector ∅ₜ) {L : ℕ}
    (h_supp : ∀ M ∈ f.support, M.1 ≤ L)
    (N : LabeledGraph ∅ₜ (Fin (L + 1))) (v : Fin (L + 1))
    : densityEval f ⟨L, deleteVertexFlag N v⟩
      = densityEval f ⟨L + 1, ⟦N⟧⟩
        + (1 / ((L : ℝ) + 1)) * densityEval (partialVertexVec f) ⟨L + 1, ⟦rootedAt N v⟧⟩
  := by
  have hexp : ∀ (G : FinFlag ∅ₜ), densityEval f G
      = ∑ M ∈ f.support, f M * (flagDensity₁ M.2 G.2 : ℝ) := by
    intro G
    dsimp only [densityEval, linearExtension]
    apply Finset.sum_congr rfl
    intro M _
    rw [smul_eq_mul]
  have hpart : densityEval (partialVertexVec f) ⟨L + 1, ⟦rootedAt N v⟧⟩
      = ∑ M ∈ f.support,
          f M * densityEval (partialVertexVec (basisVector M)) ⟨L + 1, ⟦rootedAt N v⟧⟩ := by
    rw [partialVertexVec_eq_sum, densityEval_sum]
    apply Finset.sum_congr rfl
    intro M _
    rw [densityEval_smul]
  rw [hexp, hexp, hpart, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro M hM
  rw [vertex_deletion_density M (h_supp M hM) N v]
  ring

/-! ## Lemma 4.2 b): `∂₁` respects the zero spaces -/

theorem partialVertexVec_support_le {f : FlagVector ∅ₜ} {B : ℕ}
    (h : ∀ M ∈ f.support, M.1 ≤ B)
    : ∀ F ∈ (partialVertexVec f).support, F.1 ≤ B + 1
  := by
  intro F hF
  dsimp only [partialVertexVec, linearExtension] at hF
  have h1 : F ∈ f.support.biUnion
      (fun M => (f M • ((M.1 : ℝ) • (piVertexVec M - muVec vertexType M))).support) :=
    Finsupp.support_finset_sum hF
  rw [Finset.mem_biUnion] at h1
  obtain ⟨M, hM, hFM⟩ := h1
  have h2 : F ∈ (piVertexVec M - muVec vertexType M).support :=
    Finsupp.support_smul (Finsupp.support_smul hFM)
  have h3 : F ∈ (piVertexVec M).support ∪ (muVec vertexType M).support :=
    Finsupp.support_sub h2
  have hsize : F.1 = M.1 + 1 ∨ F.1 = M.1 := by
    rw [Finset.mem_union] at h3
    rcases h3 with h4 | h4
    · left
      dsimp only [piVertexVec] at h4
      have h5 := Finsupp.support_finset_sum h4
      rw [Finset.mem_biUnion] at h5
      obtain ⟨G, _, hFG⟩ := h5
      rw [basisVector_support, Finset.mem_singleton] at hFG
      rw [hFG]
    · right
      dsimp only [muVec] at h4
      have h5 := Finsupp.support_finset_sum h4
      rw [Finset.mem_biUnion] at h5
      obtain ⟨G, _, hFG⟩ := h5
      rw [basisVector_support, Finset.mem_singleton] at hFG
      rw [hFG]
  have hMB := h M hM
  rcases hsize with h6 | h6 <;> omega

/-- **Razborov, Lemma 4.2 b)**: `∂₁(K⁰) ⊆ K¹`. Consequently `∂₁` defines a
linear mapping from `A⁰` to `A¹` (see `partialVertex`). The proof evaluates
`∂₁ k` at an arbitrary large rooted host `(N, v)` via Lemma 4.2 a): both
`p(k, N − v)` and `p(k, N)` vanish because `k ∈ K⁰`. -/
theorem partialVertexVec_zeroSpace {k : FlagVector ∅ₜ} (hk : k ∈ ZeroSpace ∅ₜ)
    : partialVertexVec k ∈ ZeroSpace vertexType
  := by
  obtain ⟨L₀, hL₀⟩ := zeroSpace_densityEval_eventually_zero hk
  set B : ℕ := max L₀ (k.support.sup (fun M => M.1)) with hB
  have h_supp : ∀ M ∈ k.support, M.1 ≤ B :=
    fun M hM => le_trans (Finset.le_sup hM) (le_max_right _ _)
  apply mem_zeroSpace_of_densityEval_zero (L := B + 1)
  · exact partialVertexVec_support_le h_supp
  · intro G
    set N : LabeledGraph ∅ₜ (Fin (B + 1)) := unlabeledGraph G.out with hN
    set v : Fin (B + 1) := G.out.type_embed 0 with hv
    have hG : (⟦rootedAt N v⟧ : FlagWithSize vertexType (B + 1)) = G := by
      rw [hN, hv, rootedAt_unlabeledGraph_self, Quotient.out_eq]
    have hkey := vertex_deletion_density_vec k h_supp N v
    rw [hL₀ B (le_max_left _ _) (deleteVertexFlag N v),
      hL₀ (B + 1) (le_trans (le_max_left _ _) (Nat.le_succ B)) ⟦N⟧] at hkey
    have hmul : (1 / ((B : ℝ) + 1)) * densityEval (partialVertexVec k) ⟨B + 1, ⟦rootedAt N v⟧⟩ = 0 := by
      linarith [hkey]
    have hpos : (1 / ((B : ℝ) + 1)) ≠ 0 := by positivity
    have := (mul_eq_zero.mp hmul).resolve_left hpos
    rwa [hG] at this

/-- The vertex-deletion operator `∂₁ : A⁰ → A¹`, descended to the flag
algebras via Lemma 4.2 b). -/
noncomputable def partialVertex : FlagAlgebra ∅ₜ → FlagAlgebra vertexType :=
  Quotient.lift (fun f : FlagVector ∅ₜ => (⟦partialVertexVec f⟧ : FlagAlgebra vertexType))
    (by
      intro f g hfg
      apply Quotient.sound
      show partialVertexVec f ∼v partialVertexVec g
      dsimp only [flagVectorEqv]
      rw [← partialVertexVec_sub]
      exact partialVertexVec_zeroSpace hfg)

theorem partialVertex_quot (f : FlagVector ∅ₜ)
    : partialVertex ⟦f⟧ = ⟦partialVertexVec f⟧
  := rfl

/-- `∂₁` is additive on the flag algebra. -/
theorem partialVertex_add (f g : FlagAlgebra ∅ₜ)
    : partialVertex (f + g) = partialVertex f + partialVertex g
  := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← add_quot, partialVertex_quot,
    partialVertex_quot, partialVertex_quot, ← add_quot]
  apply congrArg
  dsimp only [partialVertexVec]
  rw [linearExtension_add]

/-- `∂₁` commutes with scalars on the flag algebra. -/
theorem partialVertex_smul (r : ℝ) (f : FlagAlgebra ∅ₜ)
    : partialVertex (r • f) = r • partialVertex f
  := by
  rw [← Quotient.out_eq f, ← smul_quot, partialVertex_quot, partialVertex_quot, ← smul_quot]
  apply congrArg
  dsimp only [partialVertexVec]
  rw [linearExtension_smul]

/-! ## Lemma 4.2 c): `⟦∂₁ f⟧₁ = 0`

The averaging operator kills the image of `∂₁`, because `μ_ℓ¹` and `π¹` have
the same downward image: placing a random label on `M` (μ) and averaging over
the label of a random root extension (π) both recover `M`. -/

instance : Subsingleton (SimpleGraph (Fin 1)) := by
  constructor
  intro G H
  ext a b
  have hab : a = b := Subsingleton.elim a b
  subst hab
  constructor
  · intro h
    exact absurd h (G.irrefl)
  · intro h
    exact absurd h (H.irrefl)

instance : Subsingleton (LabeledGraph ∅ₜ (Fin 1)) := by
  constructor
  intro G H
  obtain ⟨g₁, e₁⟩ := G
  obtain ⟨g₂, e₂⟩ := H
  have hg : g₁ = g₂ := Subsingleton.elim _ _
  subst hg
  congr 1
  ext x
  exact x.elim0

instance : Subsingleton (Flag ∅ₜ (Fin 1)) := by
  constructor
  intro a b
  rcases Quotient.exists_rep a with ⟨x, rfl⟩
  rcases Quotient.exists_rep b with ⟨y, rfl⟩
  rw [Subsingleton.elim x y]

noncomputable instance : Unique (Flag ∅ₜ (Fin 1)) where
  default := ⟦unlabeledGraph (emptyLabeledGraph vertexType)⟧
  uniq := fun a => Subsingleton.elim a _

/-- The single-vertex flag has density `1` in every flag with at least one
vertex. -/
theorem flagDensity_singleVertex {ℓ : ℕ} (K : Flag ∅ₜ (Fin 1)) (M : FlagWithSize ∅ₜ ℓ)
    (hℓ : 1 ≤ ℓ)
    : flagDensity₁ K M = 1
  := by
  have h := density_chain_rule₁₁ (σ := ∅ₜ) 1 (emptyFlag ∅ₜ) M
    (le_refl 0) (Nat.zero_le 1) hℓ
  rw [flagDensity_empty, Fintype.sum_unique, flagDensity_empty, one_mul] at h
  rw [Subsingleton.elim K (default : Flag ∅ₜ (Fin 1))]
  exact h.symm

theorem isomorphismCount_vertexType_fin1 (G : LabeledGraph vertexType (Fin 1))
    : isomorphismCount G = 1
  := by
  dsimp only [isomorphismCount]
  rw [Set.toFinset_card]
  refine Fintype.card_eq_one_iff.mpr ⟨⟨G, rfl, ⟨LabeledGraphIso.refl⟩⟩, ?_⟩
  rintro ⟨H, hgraph, -⟩
  apply Subtype.ext
  show H = G
  obtain ⟨g₁, e₁⟩ := G
  obtain ⟨g₂, e₂⟩ := H
  simp only at hgraph
  subst hgraph
  congr 1
  ext x
  rw [Subsingleton.elim (e₂ x) (e₁ x)]

theorem downwardNormalizingFactor_emptyFlag_vertexType
    : downwardNormalizingFactor (emptyFlag vertexType) = 1
  := by
  show downwardNormalizingFactor_labeledGraph (emptyLabeledGraph vertexType) = 1
  dsimp only [downwardNormalizingFactor_labeledGraph]
  rw [isomorphismCount_vertexType_fin1]
  norm_num

/-- The total unlabelling weight of all label extensions of a nonempty model
at the one-vertex type is `1` (every vertex is a valid root). -/
theorem sum_downwardNormalizingFactor_labelExtensions_vertexType
    {ℓ : ℕ} (M : FlagWithSize ∅ₜ ℓ) (hℓ : 1 ≤ ℓ)
    : ∑ F ∈ labelExtensions M vertexType, downwardNormalizingFactor F = 1
  := by
  have h := flagDensity_mul_downwardNormalizingFactor_eq_sum_labelExtensions
    (emptyFlag vertexType) M hℓ
  rw [flagDensity_singleVertex _ M hℓ, downwardNormalizingFactor_emptyFlag_vertexType,
    one_mul] at h
  calc ∑ F ∈ labelExtensions M vertexType, downwardNormalizingFactor F
      = ∑ G ∈ labelExtensions M vertexType,
          flagDensity₁ (emptyFlag vertexType) G * downwardNormalizingFactor G := by
        apply Finset.sum_congr rfl
        intro F _
        rw [flagDensity_empty, one_mul]
    _ = 1 := h.symm

/-- The downward image of `μ_ℓ¹(M)` is `M` itself (as flag vectors): the
unlabelling weights of the label extensions sum to `1`. -/
theorem downwardFlagVector_muVec (M : FinFlag ∅ₜ) (hM : 1 ≤ M.1)
    : downwardFlagVector (muVec vertexType M) = basisVector M
  := by
  dsimp only [muVec]
  rw [downwardFlagVector_sum]
  have hterm : ∀ F ∈ labelExtensions M.2 vertexType,
      downwardFlagVector (basisVector ⟨M.1, F⟩)
        = (downwardNormalizingFactor F : ℝ) • basisVector M := by
    intro F hF
    rw [downwardFlagVector_basisVector]
    dsimp only [downwardFlag]
    have h : unlabel F = M.2 := by
      dsimp only [labelExtensions] at hF
      simpa using hF
    rw [h, rat_smul_eq_real_smul]
    congr
  rw [Finset.sum_congr rfl hterm, ← sum_smul]
  have : (∑ F ∈ labelExtensions M.2 vertexType, (downwardNormalizingFactor F : ℝ)) = 1 := by
    rw [← Rat.cast_sum, sum_downwardNormalizingFactor_labelExtensions_vertexType M.2 hM]
    norm_num
  rw [this, one_smul]

theorem unrootFlag_respect_eqv {L : ℕ} {G G' : LabeledGraph vertexType (Fin (L + 1))}
    (h : G ∼f G')
    : unrootFlag G = unrootFlag G'
  :=
  getCanonicalFlag_eq_of_iso (unrootIso h.some) _ _

theorem unlabeledGraph_rootedAt {V : Type} (X : LabeledGraph ∅ₜ V) (r : V)
    : unlabeledGraph (rootedAt X r) = X
  :=
  emptyType_labeledGraph_ext rfl

theorem unroot_rootedAt {V : Type} (X : LabeledGraph ∅ₜ V) (r : V)
    : unroot (rootedAt X r) = deleteVertex X r
  :=
  congrArg (fun A => deleteVertex A r) (unlabeledGraph_rootedAt X r)

/-- A `1`-flag whose graph equals `X`'s graph is `X` rooted at its label. -/
theorem eq_rootedAt_of_graph_eq {V : Type} (X : LabeledGraph ∅ₜ V)
    (H' : LabeledGraph vertexType V) (h : X.graph = H'.graph)
    : H' = rootedAt X (H'.type_embed 0)
  := by
  obtain ⟨g', e'⟩ := H'
  simp only at h
  subst h
  dsimp only [rootedAt]
  congr 1
  ext x
  have hx : x = 0 := Subsingleton.elim x 0
  subst hx
  rfl

/-- The induced subgraph of `X` on the complement of a vertex is `X − r`. -/
noncomputable def deleteVertex_induce_compl_iso {V : Type} (X : LabeledGraph ∅ₜ V) (r : V)
    : (LabeledSubgraph.inducedLabeledSubgraph X {u : V | u ≠ r}
        (emptyType_type_verts_subset _ _)).coe
      ≃f deleteVertex X r where
  graph_iso := {
    toFun := fun a => ⟨a.val, a.property⟩
    invFun := fun b => ⟨b.val, b.property⟩
    left_inv := fun a => rfl
    right_inv := fun b => rfl
    map_rel_iff' := by
      intro a b
      constructor
      · intro h
        exact ⟨a.property, b.property, h⟩
      · rintro ⟨_, _, h⟩
        exact h
  }
  type_preserve := by
    ext x
    exact x.elim0

/-- The unlabelling weight of a `1`-flag on `ℓ + 1` vertices is its number of
realising root placements divided by `ℓ + 1`. -/
theorem downwardNormalizingFactor_vertexType {ℓ : ℕ} (F : FlagWithSize vertexType (ℓ + 1))
    : downwardNormalizingFactor F = (isomorphismCount F.out : ℚ) / ((ℓ : ℚ) + 1)
  := by
  conv_lhs => rw [← Quotient.out_eq F]
  show downwardNormalizingFactor_labeledGraph F.out = _
  dsimp only [downwardNormalizingFactor_labeledGraph]
  have hfac : (ℓ + 1).factorial / (ℓ + 1 - 1).factorial = ℓ + 1 := by
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    exact Nat.mul_div_cancel _ (Nat.factorial_pos ℓ)
  rw [hfac]
  push_cast
  ring

/-- The number of root placements on the graph of `X` realising a fixed
`1`-flag `F` (with at least one realising root) is `F`'s isomorphism count. -/
theorem isomorphismCount_eq_card_roots {ℓ : ℕ} (X : LabeledGraph ∅ₜ (Fin (ℓ + 1)))
    (F : FlagWithSize vertexType (ℓ + 1)) (r₀ : Fin (ℓ + 1))
    (h : (⟦rootedAt X r₀⟧ : FlagWithSize vertexType (ℓ + 1)) = F)
    : isomorphismCount F.out
      = (Finset.univ.filter (fun r : Fin (ℓ + 1) =>
          (⟦rootedAt X r⟧ : FlagWithSize vertexType (ℓ + 1)) = F)).card
  := by
  rw [isomorphismCount_respect_eqv (flagEqv.symm (Quotient.mk_eq_iff_out.mp h))]
  dsimp only [isomorphismCount]
  apply Finset.card_bij
    (fun (H' : LabeledGraph vertexType (Fin (ℓ + 1))) (_ : H' ∈ _) => H'.type_embed 0)
  · intro H' hH'
    simp only [Set.mem_toFinset, isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq] at hH'
    obtain ⟨hgraph, hiso⟩ := hH'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : H' = rootedAt X (H'.type_embed 0) := eq_rootedAt_of_graph_eq X H' hgraph
    calc (⟦rootedAt X (H'.type_embed 0)⟧ : FlagWithSize vertexType (ℓ + 1))
        = ⟦H'⟧ := by rw [← h1]
      _ = ⟦rootedAt X r₀⟧ := Quotient.sound (flagEqv.symm hiso)
      _ = F := h
  · intro H₁ h₁ H₂ h₂ heq
    simp only [Set.mem_toFinset, isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq] at h₁ h₂
    rw [eq_rootedAt_of_graph_eq X H₁ h₁.1, eq_rootedAt_of_graph_eq X H₂ h₂.1, heq]
  · intro r hr
    rw [Finset.mem_filter] at hr
    refine ⟨rootedAt X r, ?_, rfl⟩
    simp only [Set.mem_toFinset, isoLabeledGraphSetWithSameGraph, Set.mem_setOf_eq]
    exact ⟨rfl, Quotient.exact (h.trans hr.2.symm)⟩

/-- The per-graph grouping identity behind Lemma 4.2 c): for a fixed
unlabelled flag `H` on `ℓ + 1` vertices, the unlabelling weights of the root
extensions of `M` with underlying flag `H` sum to `p(M, H)` — a realising
root placement of `H` is the same thing as a vertex `r` with `H − r ≅ M`. -/
theorem sum_downwardNormalizingFactor_rootExtensions {ℓ : ℕ} (M : FlagWithSize ∅ₜ ℓ)
    (H : FlagWithSize ∅ₜ (ℓ + 1))
    : ∑ F ∈ (rootExtensions M).filter (fun F => unlabel F = H), downwardNormalizingFactor F
      = flagDensity₁ M H
  := by
  set T : Finset (Fin (ℓ + 1)) :=
    Finset.univ.filter (fun r => unrootFlag (rootedAt H.out r) = M) with hT
  -- the map `r ↦ ⟦(H, r)⟧` sends `T` onto the filtered root extensions
  have hmaps : ∀ r ∈ T,
      (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1))
        ∈ (rootExtensions M).filter (fun F => unlabel F = H) := by
    intro r hr
    rw [hT, Finset.mem_filter] at hr
    rw [Finset.mem_filter]
    constructor
    · show (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) ∈ rootExtensions M
      rw [rootExtensions_eq_filter, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)).out
          ∼f rootedAt H.out r := by
        show (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)).out ≈ rootedAt H.out r
        exact Quotient.eq_mk_iff_out.mp rfl
      rw [unrootFlag_respect_eqv h1]
      exact hr.2
    · show unlabel (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = H
      show (⟦unlabeledGraph (rootedAt H.out r)⟧ : FlagWithSize ∅ₜ (ℓ + 1)) = H
      rw [unlabeledGraph_rootedAt]
      exact Quotient.out_eq H
  -- fibre sizes are the isomorphism counts
  have hfiber : ∀ F ∈ (rootExtensions M).filter (fun F => unlabel F = H),
      (T.filter (fun r => (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F)).card
        = isomorphismCount F.out := by
    intro F hF
    rw [Finset.mem_filter] at hF
    obtain ⟨hFroot, hFH⟩ := hF
    -- a realising root exists since `unlabel F = H`
    have hex : ∃ r₀ : Fin (ℓ + 1),
        (⟦rootedAt H.out r₀⟧ : FlagWithSize vertexType (ℓ + 1)) = F := by
      have h2 : (⟦unlabeledGraph F.out⟧ : FlagWithSize ∅ₜ (ℓ + 1)) = H := by
        rw [← unlabel_out F, hFH]
      have hψ : unlabeledGraph F.out ∼f H.out := Quotient.mk_eq_iff_out.mp h2
      obtain ⟨ψ⟩ := hψ
      refine ⟨ψ.graph_iso (F.out.type_embed 0), ?_⟩
      have hiso : F.out ∼f rootedAt H.out (ψ.graph_iso (F.out.type_embed 0)) := by
        refine ⟨{ graph_iso := ψ.graph_iso, type_preserve := ?_ }⟩
        funext x
        have hx : x = 0 := Subsingleton.elim x 0
        subst hx
        rfl
      calc (⟦rootedAt H.out (ψ.graph_iso (F.out.type_embed 0))⟧
            : FlagWithSize vertexType (ℓ + 1))
          = ⟦F.out⟧ := Quotient.sound (flagEqv.symm hiso)
        _ = F := Quotient.out_eq F
    obtain ⟨r₀, hr₀⟩ := hex
    rw [isomorphismCount_eq_card_roots H.out F r₀ hr₀]
    congr 1
    -- the `T`-condition is implied by landing in the fibre of `F`
    ext r
    simp only [Finset.mem_filter, hT, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      refine ⟨?_, h⟩
      have h1 : rootedAt H.out r ∼f F.out :=
        Quotient.mk_eq_iff_out.mp h
      rw [unrootFlag_respect_eqv h1]
      rw [rootExtensions_eq_filter, Finset.mem_filter] at hFroot
      exact hFroot.2
  -- `T` counts the subsets inducing `M` (complement bijection)
  have hTcard : T.card = labeledGraphCount M.out H.out := by
    rw [labeledGraphCount_eq_card_inducingSubsets]
    apply Finset.card_bij (fun (r : Fin (ℓ + 1)) (_ : r ∈ T) => ({u | u ≠ r} : Set (Fin (ℓ + 1))))
    · intro r hr
      rw [hT, Finset.mem_filter] at hr
      rw [Set.mem_toFinset]
      refine ⟨emptyType_type_verts_subset _ _, ?_⟩
      have h1 : Nonempty (M.out ≃f unroot (rootedAt H.out r)) := by
        dsimp only [unrootFlag] at hr
        exact (getCanonicalFlag_eq_iff _ _ M).mp hr.2
      have h2 : unroot (rootedAt H.out r) = deleteVertex H.out r := unroot_rootedAt H.out r
      rw [h2] at h1
      exact ⟨(deleteVertex_induce_compl_iso H.out r).trans h1.some.symm⟩
    · intro r₁ h₁ r₂ h₂ heq
      by_contra hne
      have : r₂ ∈ ({u | u ≠ r₁} : Set (Fin (ℓ + 1))) := fun hc => hne hc.symm
      rw [heq] at this
      exact this rfl
    · intro S hS
      rw [Set.mem_toFinset] at hS
      obtain ⟨h₀, ⟨ψ₀⟩⟩ := hS
      -- `S` has `ℓ` elements, so its complement is a single vertex `r`
      have hcardS : S.toFinset.card = ℓ := by
        have hsz := labeledGraphIso_size_eq _ _ ψ₀
        simp only [LabeledGraph.size, Fintype.card_fin] at hsz
        rw [Set.toFinset_card]
        exact hsz
      have hcompl : S.toFinsetᶜ.card = 1 := by
        rw [Finset.card_compl, hcardS, Fintype.card_fin, Nat.add_sub_cancel_left]
      obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcompl
      have hSr : S = ({u | u ≠ r} : Set (Fin (ℓ + 1))) := by
        ext u
        have h3 : u ∈ S.toFinset ↔ u ∉ S.toFinsetᶜ := by
          simp only [Finset.mem_compl, not_not]
        constructor
        · intro hu
          intro huv
          have h4 : u ∉ S.toFinsetᶜ := h3.mp (Set.mem_toFinset.mpr hu)
          rw [hr, Finset.mem_singleton] at h4
          exact h4 huv
        · intro hu
          by_contra hc
          have h5 : u ∈ S.toFinsetᶜ := by
            rw [Finset.mem_compl, Set.mem_toFinset]
            exact hc
          rw [hr, Finset.mem_singleton] at h5
          exact hu h5
      refine ⟨r, ?_, hSr.symm⟩
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [unrootFlag]
      rw [getCanonicalFlag_eq_iff]
      have h2 : unroot (rootedAt H.out r) = deleteVertex H.out r := unroot_rootedAt H.out r
      rw [h2]
      have hψ : (LabeledSubgraph.inducedLabeledSubgraph H.out {u | u ≠ r}
          (emptyType_type_verts_subset _ _)).coe ≃f M.out := by
        have hsets : (LabeledSubgraph.inducedLabeledSubgraph H.out S h₀)
            = (LabeledSubgraph.inducedLabeledSubgraph H.out {u | u ≠ r}
              (emptyType_type_verts_subset _ _)) := by
          apply labeledSubgraph_eq_from_subgraph_eq
          dsimp only [LabeledSubgraph.inducedLabeledSubgraph]
          rw [← hSr]
        exact (LabeledGraphIso.labeledSubgraphIso_eq hsets).symm.trans ψ₀
      exact ⟨((deleteVertex_induce_compl_iso H.out r).symm.trans hψ).symm⟩
  -- `T` is partitioned by the flag classes of its rooted graphs
  have hpart : T = ((rootExtensions M).filter (fun F => unlabel F = H)).biUnion
      (fun F => T.filter (fun r =>
        (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F)) := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hr
      refine ⟨⟦rootedAt H.out r⟧, ?_, ⟨hr, rfl⟩⟩
      have h1 := hmaps r hr
      rw [Finset.mem_filter] at h1
      exact h1
    · rintro ⟨F, -, hrT, -⟩
      exact hrT
  have hdisj : ∀ F₁ ∈ (rootExtensions M).filter (fun F => unlabel F = H),
      ∀ F₂ ∈ (rootExtensions M).filter (fun F => unlabel F = H), F₁ ≠ F₂ →
      Disjoint (T.filter (fun r =>
          (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F₁))
        (T.filter (fun r =>
          (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F₂)) := by
    intro F₁ _ F₂ _ hne
    rw [Finset.disjoint_left]
    intro r hr₁ hr₂
    rw [Finset.mem_filter] at hr₁ hr₂
    exact hne (hr₁.2.symm.trans hr₂.2)
  have hcards : T.card = ∑ F ∈ (rootExtensions M).filter (fun F => unlabel F = H),
      (T.filter (fun r =>
        (⟦rootedAt H.out r⟧ : FlagWithSize vertexType (ℓ + 1)) = F)).card := by
    conv_lhs => rw [hpart]
    exact Finset.card_biUnion hdisj
  -- assemble
  have hsum : ∑ F ∈ (rootExtensions M).filter (fun F => unlabel F = H),
      downwardNormalizingFactor F = (T.card : ℚ) / ((ℓ : ℚ) + 1) := by
    rw [hcards]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro F hF
    rw [downwardNormalizingFactor_vertexType]
    congr 1
    rw [Nat.cast_inj]
    exact (hfiber F hF).symm
  rw [hsum, hTcard]
  rw [flagDensity₁_out, labeledGraphDensity_eq_card_div, labeledGraphCount_eq_card_inducingSubsets]
  simp only [Fintype.card_fin, Nat.sub_zero, Nat.choose_succ_self_right]
  push_cast
  ring

/-- The downward image of `π¹(M)` is flag-equal to `M`: grouping the root
extensions of `M` by their underlying unlabelled graph `H`, the unlabelling
weights of the extensions with a fixed `H` sum to exactly `p(M, H)` (a root
placement of `H` realising an extension of `M` is the same thing as a vertex
`r ∈ V(H)` with `H − r ≅ M`). -/
theorem downwardFlagVector_piVertexVec (M : FinFlag ∅ₜ) (hM : 1 ≤ M.1)
    : downwardFlagVector (piVertexVec M) ∼v basisVector M
  := by
  have heq : downwardFlagVector (piVertexVec M) = flagExpansion M (M.1 + 1) := by
    dsimp only [piVertexVec]
    rw [downwardFlagVector_sum]
    calc ∑ F ∈ rootExtensions M.2, downwardFlagVector (basisVector ⟨M.1 + 1, F⟩)
        = ∑ F ∈ rootExtensions M.2,
            downwardNormalizingFactor F • basisVector ⟨M.1 + 1, unlabel F⟩ := by
          apply Finset.sum_congr rfl
          intro F _
          rw [downwardFlagVector_basisVector]
          rfl
      _ = ∑ H : FlagWithSize ∅ₜ (M.1 + 1),
            ∑ F ∈ (rootExtensions M.2).filter (fun F => unlabel F = H),
              downwardNormalizingFactor F • basisVector ⟨M.1 + 1, unlabel F⟩ := by
          rw [Finset.sum_fiberwise_of_maps_to (fun F _ => Finset.mem_univ (unlabel F))]
      _ = ∑ H : FlagWithSize ∅ₜ (M.1 + 1),
            (flagDensity₁ M.2 H) • basisVector ⟨M.1 + 1, H⟩ := by
          apply Finset.sum_congr rfl
          intro H _
          have hs : ∀ F ∈ (rootExtensions M.2).filter (fun F => unlabel F = H),
              downwardNormalizingFactor F • basisVector ⟨M.1 + 1, unlabel F⟩
                = downwardNormalizingFactor F • (basisVector ⟨M.1 + 1, H⟩ : FlagVector ∅ₜ) := by
            intro F hF
            rw [Finset.mem_filter] at hF
            rw [hF.2]
          rw [Finset.sum_congr rfl hs]
          simp_rw [rat_smul_eq_real_smul]
          rw [← sum_smul, ← Rat.cast_sum, sum_downwardNormalizingFactor_rootExtensions M.2 H]
      _ = flagExpansion M (M.1 + 1) := rfl
  exact (flagVector_eq_eqv heq).trans
    (basisVector_eqv_flagExpansion M (M.1 + 1) (Nat.le_succ M.1)).symm

theorem downward_partialVertexVec_basis (M : FinFlag ∅ₜ)
    : downwardFlagVectorQuot (partialVertexVec (basisVector M)) = 0
  := by
  rw [partialVertexVec_basisVector]
  rcases Nat.eq_zero_or_pos M.1 with h0 | h1
  · rw [h0]
    rw [Nat.cast_zero, zero_smul]
    exact downwardFlagVectorQuot_zero
  · dsimp only [downwardFlagVectorQuot]
    rw [downwardFlagVector_smul, downwardFlagVector_sub, downwardFlagVector_muVec M h1]
    rw [smul_quot]
    have hpi : downwardFlagVector (piVertexVec M) - basisVector M ∈ ZeroSpace ∅ₜ :=
      downwardFlagVector_piVertexVec M h1
    have hzero : (⟦downwardFlagVector (piVertexVec M) - basisVector M⟧ : FlagAlgebra ∅ₜ) = 0 := by
      apply Quotient.sound
      show _ - 0 ∈ ZeroSpace ∅ₜ
      rwa [sub_zero]
    rw [hzero, smul_zero]

/-- **Razborov, Lemma 4.2 c)** (vector form): `⟦∂₁ f⟧₁ = 0` for every formal
combination of models `f`. -/
theorem downward_partialVertexVec (f : FlagVector ∅ₜ)
    : downwardFlagVectorQuot (partialVertexVec f) = 0
  := by
  dsimp only [partialVertexVec, linearExtension]
  have h : ∀ M ∈ f.support,
      downwardFlagVectorQuot (f M • ((M.1 : ℝ) • (piVertexVec M - muVec vertexType M))) = 0 := by
    intro M _
    rw [downwardFlagVectorQuot_smul]
    have := downward_partialVertexVec_basis M
    rw [partialVertexVec_basisVector] at this
    rw [this, smul_zero]
  calc downwardFlagVectorQuot
        (∑ M ∈ f.support, f M • ((M.1 : ℝ) • (piVertexVec M - muVec vertexType M)))
      = ∑ M ∈ f.support,
          downwardFlagVectorQuot (f M • ((M.1 : ℝ) • (piVertexVec M - muVec vertexType M))) := by
        dsimp only [downwardFlagVectorQuot]
        rw [downwardFlagVector_sum, sum_quot]
    _ = 0 := by
        rw [Finset.sum_congr rfl h, Finset.sum_const_zero]

/-- **Razborov, Lemma 4.2 c)**: `⟦∂₁ f⟧₁ = 0` for every `f ∈ A⁰`. -/
theorem downward_partialVertex (f : FlagAlgebra ∅ₜ)
    : ⟦partialVertex f⟧₀ = 0
  := by
  rcases Quotient.exists_rep f with ⟨g, rfl⟩
  rw [partialVertex_quot]
  exact downward_partialVertexVec g

end Differential
end FlagAlgebras
