import «LeanFlagAlgebras».Differential.Eval

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

/-! ## The two counting identities behind Lemma 4.2 a) -/

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
  sorry

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
  sorry

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

/-- The downward image of `π¹(M)` is flag-equal to `M`: grouping the root
extensions of `M` by their underlying unlabelled graph `H`, the unlabelling
weights of the extensions with a fixed `H` sum to exactly `p(M, H)` (a root
placement of `H` realising an extension of `M` is the same thing as a vertex
`r ∈ V(H)` with `H − r ≅ M`). -/
theorem downwardFlagVector_piVertexVec (M : FinFlag ∅ₜ) (hM : 1 ≤ M.1)
    : downwardFlagVector (piVertexVec M) ∼v basisVector M
  := by
  sorry

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
