import LeanFlagAlgebras.MetaTheory.EdgeObstruction

/-! # The edgeless and complete limit points at the one-vertex type (paper §10 groundwork)

`prop:single-point` pins the whole root-planting set of an edge-degenerate class to one
point of `X_vtype`: the labelled **empty-graph limit** `o`, the homomorphism assigning
density `1` to the edgeless `vtype`-flag of each size and `0` to every flag containing an
edge (dually, for a co-edge-degenerate class, the **complete-graph limit**).  This module
constructs the two points and proves they are the unique points with the respective
vanishing pattern:

* `IsEdgelessFlag` / `IsCompleteFlag` — the flag's underlying graph is `⊥` / `⊤`
  (well-defined on flag-isomorphism classes).
* `edgelessFlag_unique` / `completeFlag_unique` — at the one-vertex type there is exactly
  one edgeless (resp. complete) flag of each size: all root placements are isomorphic.
* `exists_edgelessPoint` / `exists_completePoint` — the boolean profiles are realised by
  points of `X_vtype` (limits of the constant flag sequences of edgeless / complete
  graphs rooted at a vertex).
* `val_eq_boolean_of_nonEdgeless_zero` / `val_eq_boolean_of_nonComplete_zero` — the
  vanishing pattern *determines* the whole profile: the flags of each size sum to `1`
  and only one flag per size survives.  Uniqueness
  (`eq_edgelessPoint_of_nonEdgeless_zero`, `eq_completePoint_of_nonComplete_zero`)
  follows.
* `edgelessPoint` / `completePoint` with their value lemmas `edgelessPoint_val` /
  `completePoint_val`.
-/

open SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- Transport `= ⊥` along a graph isomorphism: a graph isomorphic to the edgeless graph is
edgeless. -/
private lemma graph_eq_bot_of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G = ⊥) : H = ⊥ := by
  subst hG
  ext u v
  simp only [bot_adj, iff_false]
  intro hadj
  exact (bot_adj _ _).mp (e.symm.map_adj_iff.mpr hadj)

/-- Transport `= ⊤` along a graph isomorphism: a graph isomorphic to the complete graph is
complete. -/
private lemma graph_eq_top_of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G = ⊤) : H = ⊤ := by
  subst hG
  ext u v
  simp only [top_adj]
  constructor
  · exact fun hadj => hadj.ne
  · intro huv
    exact e.symm.map_adj_iff.mp ((top_adj _ _).mpr fun hEq => huv (e.symm.injective hEq))

/-! ## Edgeless and complete flags -/

/-- The flag's underlying graph is edgeless (`= ⊥`).  Well-defined on isomorphism
classes: a flag isomorphism carries a graph isomorphism, and a graph isomorphic to `⊥`
is `⊥`. -/
def IsEdgelessFlag {V : Type} : Flag σ V → Prop :=
  Quotient.lift (fun G : LabeledGraph σ V => G.graph = ⊥) (by
    -- `propext`; transport edgelessness through the graph isomorphism of a flag iso.
    intro a b hab
    obtain ⟨φ⟩ := hab
    exact propext ⟨fun h => graph_eq_bot_of_iso φ.graph_iso h,
      fun h => graph_eq_bot_of_iso φ.graph_iso.symm h⟩)

/-- The flag's underlying graph is complete (`= ⊤`).  Well-defined on isomorphism
classes. -/
def IsCompleteFlag {V : Type} : Flag σ V → Prop :=
  Quotient.lift (fun G : LabeledGraph σ V => G.graph = ⊤) (by
    intro a b hab
    obtain ⟨φ⟩ := hab
    exact propext ⟨fun h => graph_eq_top_of_iso φ.graph_iso h,
      fun h => graph_eq_top_of_iso φ.graph_iso.symm h⟩)

@[simp] lemma isEdgelessFlag_mk {V : Type} (G : LabeledGraph σ V) :
    IsEdgelessFlag (⟦G⟧ : Flag σ V) ↔ G.graph = ⊥ := Iff.rfl

@[simp] lemma isCompleteFlag_mk {V : Type} (G : LabeledGraph σ V) :
    IsCompleteFlag (⟦G⟧ : Flag σ V) ↔ G.graph = ⊤ := Iff.rfl

/-- Unlabelling does not change the underlying graph: a flag is edgeless if and only if
its unlabelling is. -/
lemma isEdgelessFlag_unlabel_iff {V : Type} (F : Flag σ V) :
    IsEdgelessFlag (unlabel F) ↔ IsEdgelessFlag F :=
  Quotient.inductionOn F fun _ => Iff.rfl

/-- Unlabelling does not change the underlying graph: a flag is complete if and only if
its unlabelling is. -/
lemma isCompleteFlag_unlabel_iff {V : Type} (F : Flag σ V) :
    IsCompleteFlag (unlabel F) ↔ IsCompleteFlag F :=
  Quotient.inductionOn F fun _ => Iff.rfl

/-! ## Uniqueness of the edgeless / complete flag of each size at `vtype` -/

/-- At the one-vertex type there is exactly one edgeless flag of each size: any
root-preserving bijection between edgeless graphs is an isomorphism, and a permutation
moving one root to the other exists (`Equiv.swap`). -/
theorem edgelessFlag_unique {m : ℕ} {F F' : FlagWithSize vtype m}
    (hF : IsEdgelessFlag F) (hF' : IsEdgelessFlag F') : F = F' := by
  revert hF hF'
  refine Quotient.inductionOn₂ F F' fun A B hF hF' => ?_
  rw [isEdgelessFlag_mk] at hF hF'
  apply Quotient.sound
  refine ⟨⟨⟨Equiv.swap (A.type_embed 0) (B.type_embed 0), ?_⟩, ?_⟩⟩
  · intro a b
    simp only [hF, hF', bot_adj]
  · funext t
    have ht : t = 0 := Subsingleton.elim t 0
    subst ht
    simp only [Function.comp_apply, RelIso.coe_fn_mk, Equiv.swap_apply_left]

/-- At the one-vertex type there is exactly one complete flag of each size: any
bijection is an isomorphism of complete graphs. -/
theorem completeFlag_unique {m : ℕ} {F F' : FlagWithSize vtype m}
    (hF : IsCompleteFlag F) (hF' : IsCompleteFlag F') : F = F' := by
  revert hF hF'
  refine Quotient.inductionOn₂ F F' fun A B hF hF' => ?_
  rw [isCompleteFlag_mk] at hF hF'
  apply Quotient.sound
  refine ⟨⟨⟨Equiv.swap (A.type_embed 0) (B.type_embed 0), ?_⟩, ?_⟩⟩
  · intro a b
    simp only [hF, hF', top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  · funext t
    have ht : t = 0 := Subsingleton.elim t 0
    subst ht
    simp only [Function.comp_apply, RelIso.coe_fn_mk, Equiv.swap_apply_left]

/-- At the empty type there is exactly one edgeless flag of each size (no root
constraint: the identity bijection of the two `⊥` graphs is an isomorphism, and type
preservation is vacuous). -/
theorem edgelessFlag_unique_emptyType {m : ℕ} {F F' : FlagWithSize ∅ₜ m}
    (hF : IsEdgelessFlag F) (hF' : IsEdgelessFlag F') : F = F' := by
  revert hF hF'
  refine Quotient.inductionOn₂ F F' fun A B hF hF' => ?_
  rw [isEdgelessFlag_mk] at hF hF'
  apply Quotient.sound
  refine ⟨⟨⟨Equiv.refl (Fin m), ?_⟩, ?_⟩⟩
  · intro a b
    simp only [hF, hF', Equiv.refl_apply, bot_adj]
  · funext t
    exact t.elim0

/-- At the empty type there is exactly one complete flag of each size. -/
theorem completeFlag_unique_emptyType {m : ℕ} {F F' : FlagWithSize ∅ₜ m}
    (hF : IsCompleteFlag F) (hF' : IsCompleteFlag F') : F = F' := by
  revert hF hF'
  refine Quotient.inductionOn₂ F F' fun A B hF hF' => ?_
  rw [isCompleteFlag_mk] at hF hF'
  apply Quotient.sound
  refine ⟨⟨⟨Equiv.refl (Fin m), ?_⟩, ?_⟩⟩
  · intro a b
    simp only [hF, hF', Equiv.refl_apply, top_adj]
  · funext t
    exact t.elim0

/-! ## The two labelled limit graphs -/

/-- The edgeless graph on `n+1` vertices, rooted at `0`: the finite stage of the labelled
empty-graph limit. -/
def edgelessLabeled (n : ℕ) : LabeledGraph vtype (Fin (n + 1)) where
  graph := ⊥
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [bot_adj] }

/-- The complete graph on `n+1` vertices, rooted at `0`: the finite stage of the labelled
complete-graph limit. -/
def completeLabeled (n : ℕ) : LabeledGraph vtype (Fin (n + 1)) where
  graph := ⊤
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [top_adj, ne_eq]
        constructor
        · intro h; exact absurd rfl h
        · intro h; exact (h.ne (Subsingleton.elim a b)).elim }

@[simp] lemma edgelessLabeled_graph (n : ℕ) : (edgelessLabeled n).graph = ⊥ := rfl

@[simp] lemma completeLabeled_graph (n : ℕ) : (completeLabeled n).graph = ⊤ := rfl

/-! ## Existence of the boolean profile points -/

/-- The edgeless flag sequence: stage `n` is the edgeless graph on `n + 1` vertices. -/
private def edgelessSeq : FlagSeq vtype :=
  fun n => ⟨n + 1, (⟦edgelessLabeled n⟧ : Flag vtype (Fin (n + 1)))⟩

/-- The complete flag sequence: stage `n` is the complete graph on `n + 1` vertices. -/
private def completeSeq : FlagSeq vtype :=
  fun n => ⟨n + 1, (⟦completeLabeled n⟧ : Flag vtype (Fin (n + 1)))⟩

private lemma edgelessSeq_increases : Increases edgelessSeq :=
  increases_of_consecutive_lt fun n => Nat.lt_succ_self (n + 1)

private lemma completeSeq_increases : Increases completeSeq :=
  increases_of_consecutive_lt fun n => Nat.lt_succ_self (n + 1)

/-- A non-edgeless flag has density `0` in every stage of the edgeless sequence: a positive
density would exhibit its graph as (isomorphic to) an induced subgraph of `⊥`, forcing it to
be `⊥`. -/
private lemma flagDensity₁_eq_zero_of_not_edgeless {F : FinFlag vtype}
    (hF : ¬ IsEdgelessFlag F.2) (j : ℕ) :
    flagDensity₁ F.2 (⟦edgelessLabeled j⟧ : Flag vtype (Fin (j + 1))) = 0 := by
  by_contra hne
  apply hF
  have hF2 : F.2 = (⟦Quotient.out F.2⟧ : Flag vtype (Fin F.1)) := (Quotient.out_eq F.2).symm
  rw [hF2] at hne
  rw [hF2, isEdgelessFlag_mk]
  obtain ⟨S, hroot, ⟨φ⟩⟩ :=
    exists_inducing_subset_of_flagDensity₁_ne_zero (Quotient.out F.2) (edgelessLabeled j) hne
  refine graph_eq_bot_of_iso φ.graph_iso ?_
  ext u v
  simp only [bot_adj, iff_false]
  intro hadj
  rw [LabeledSubgraph.coe_adj_iff] at hadj
  have hadj' : ((⊤ : (edgelessLabeled j).graph.Subgraph).induce
      (↑S : Set (Fin (j + 1)))).Adj u.val v.val := hadj
  simp only [Subgraph.induce_adj, Subgraph.top_adj, edgelessLabeled_graph, bot_adj, and_false] at hadj'

/-- A non-complete flag has density `0` in every stage of the complete sequence: a positive
density would exhibit its graph as (isomorphic to) an induced subgraph of `⊤`, forcing it to
be `⊤`. -/
private lemma flagDensity₁_eq_zero_of_not_complete {F : FinFlag vtype}
    (hF : ¬ IsCompleteFlag F.2) (j : ℕ) :
    flagDensity₁ F.2 (⟦completeLabeled j⟧ : Flag vtype (Fin (j + 1))) = 0 := by
  by_contra hne
  apply hF
  have hF2 : F.2 = (⟦Quotient.out F.2⟧ : Flag vtype (Fin F.1)) := (Quotient.out_eq F.2).symm
  rw [hF2] at hne
  rw [hF2, isCompleteFlag_mk]
  obtain ⟨S, hroot, ⟨φ⟩⟩ :=
    exists_inducing_subset_of_flagDensity₁_ne_zero (Quotient.out F.2) (completeLabeled j) hne
  refine graph_eq_top_of_iso φ.graph_iso ?_
  ext u v
  simp only [top_adj]
  constructor
  · exact fun hadj => hadj.ne
  · intro huv
    rw [LabeledSubgraph.coe_adj_iff]
    have hu : u.val ∈ (↑S : Set (Fin (j + 1))) := by
      simpa only [LabeledSubgraph.inducedLabeledSubgraph_verts] using u.property
    have hv : v.val ∈ (↑S : Set (Fin (j + 1))) := by
      simpa only [LabeledSubgraph.inducedLabeledSubgraph_verts] using v.property
    show ((⊤ : (completeLabeled j).graph.Subgraph).induce (↑S : Set (Fin (j + 1)))).Adj u.val v.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj, completeLabeled_graph, top_adj, ne_eq]
    exact ⟨hu, hv, fun hEq => huv (Subtype.ext hEq)⟩

/-- There is a point of `X_vtype` vanishing on every non-edgeless flag: the limit of the
edgeless flag sequence.

Proof route: the sequence `n ↦ ⟨n+1, ⟦edgelessLabeled n⟧⟩` has strictly increasing sizes
(`increases_of_consecutive_lt`), so a convergent subsequence exists
(`increasing_flagSeq_contain_convergent_subseq`) with limit a positive homomorphism
(`flagSeq_limit_mem_positiveHom`); take `posHomPoint` of it.  A non-edgeless flag `F` has
density `0` in every stage — otherwise `exists_inducing_subset_of_flagDensity₁_ne_zero`
would exhibit `F`'s graph as (isomorphic to) an induced subgraph of `⊥`, forcing it to be
`⊥` — so the limit value is `0` (`tendsto_nhds_unique` with the constant-`0` sequence). -/
lemma exists_edgelessPoint :
    ∃ χ : PositiveHomSpace vtype,
      ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0 := by
  classical
  obtain ⟨a, ϕ, -, hconv⟩ :=
    increasing_flagSeq_contain_convergent_subseq edgelessSeq edgelessSeq_increases
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (edgelessSeq ∘ ϕ) hconv
  obtain ⟨-, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  refine ⟨posHomPoint φ, fun F hF => ?_⟩
  have hval : (posHomPoint φ).val F = a F := by
    rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
  rw [hval]
  have hz : ∀ k, flagDensitySeq (edgelessSeq ∘ ϕ) k F = 0 := fun k => by
    show (flagDensity₁ F.2 (⟦edgelessLabeled (ϕ k)⟧ : Flag vtype (Fin (ϕ k + 1))) : ℝ) = 0
    exact_mod_cast flagDensity₁_eq_zero_of_not_edgeless hF (ϕ k)
  have h0 : Tendsto (fun k => flagDensitySeq (edgelessSeq ∘ ϕ) k F) atTop (𝓝 (0 : ℝ)) := by
    simp only [hz]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hpt F) h0

/-- There is a point of `X_vtype` vanishing on every non-complete flag: the limit of the
complete flag sequence (mirror of `exists_edgelessPoint`, with "induced subgraph of `⊤`
is complete"). -/
lemma exists_completePoint :
    ∃ χ : PositiveHomSpace vtype,
      ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0 := by
  classical
  obtain ⟨a, ϕ, -, hconv⟩ :=
    increasing_flagSeq_contain_convergent_subseq completeSeq completeSeq_increases
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (completeSeq ∘ ϕ) hconv
  obtain ⟨-, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  refine ⟨posHomPoint φ, fun F hF => ?_⟩
  have hval : (posHomPoint φ).val F = a F := by
    rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
  rw [hval]
  have hz : ∀ k, flagDensitySeq (completeSeq ∘ ϕ) k F = 0 := fun k => by
    show (flagDensity₁ F.2 (⟦completeLabeled (ϕ k)⟧ : Flag vtype (Fin (ϕ k + 1))) : ℝ) = 0
    exact_mod_cast flagDensity₁_eq_zero_of_not_complete hF (ϕ k)
  have h0 : Tendsto (fun k => flagDensitySeq (completeSeq ∘ ϕ) k F) atTop (𝓝 (0 : ℝ)) := by
    simp only [hz]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hpt F) h0

/-! ## The vanishing pattern determines the whole profile -/

/-- A point of `X_vtype` vanishing on every non-edgeless flag has the boolean edgeless
profile.

Proof route: the negative case is the hypothesis.  For edgeless `F`, the values over all
flags of size `F.1` sum to `1` (`sum_positiveHom_basisVector_flagWithSize_eq_one` for
`toPosHom χ`, converted by `PositiveHomSpace.toPosHom_basisVector`; `F.1 ≥ 1` by
`finFlag_size_ge_n₀`); all summands except the one at `F.2` vanish (`Finset.sum_eq_single`
— a non-edgeless flag by hypothesis, an edgeless one equals `F.2` by
`edgelessFlag_unique`), so `χ.val F = 1`. -/
theorem val_eq_boolean_of_nonEdgeless_zero {χ : PositiveHomSpace vtype}
    (h : ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0) (F : FinFlag vtype) :
    χ.val F = if IsEdgelessFlag F.2 then 1 else 0 := by
  by_cases hF : IsEdgelessFlag F.2
  · rw [if_pos hF]
    have key := sum_positiveHom_basisVector_flagWithSize_eq_one
      (PositiveHomSpace.toPosHom χ) F.1 (finFlag_size_ge_n₀ F)
    simp only [PositiveHomSpace.toPosHom_basisVector] at key
    have hsum : (∑ F' : FlagWithSize vtype F.1, χ.val ⟨F.1, F'⟩) = χ.val ⟨F.1, F.2⟩ := by
      refine Finset.sum_eq_single F.2 (fun b _ hb => ?_)
        (fun hmem => absurd (Finset.mem_univ F.2) hmem)
      by_cases hb' : IsEdgelessFlag b
      · exact absurd (edgelessFlag_unique hb' hF) hb
      · exact h ⟨F.1, b⟩ hb'
    rw [hsum] at key
    exact key
  · rw [if_neg hF]
    exact h F hF

/-- A point of `X_vtype` vanishing on every non-complete flag has the boolean complete
profile (mirror of `val_eq_boolean_of_nonEdgeless_zero`). -/
theorem val_eq_boolean_of_nonComplete_zero {χ : PositiveHomSpace vtype}
    (h : ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0) (F : FinFlag vtype) :
    χ.val F = if IsCompleteFlag F.2 then 1 else 0 := by
  by_cases hF : IsCompleteFlag F.2
  · rw [if_pos hF]
    have key := sum_positiveHom_basisVector_flagWithSize_eq_one
      (PositiveHomSpace.toPosHom χ) F.1 (finFlag_size_ge_n₀ F)
    simp only [PositiveHomSpace.toPosHom_basisVector] at key
    have hsum : (∑ F' : FlagWithSize vtype F.1, χ.val ⟨F.1, F'⟩) = χ.val ⟨F.1, F.2⟩ := by
      refine Finset.sum_eq_single F.2 (fun b _ hb => ?_)
        (fun hmem => absurd (Finset.mem_univ F.2) hmem)
      by_cases hb' : IsCompleteFlag b
      · exact absurd (completeFlag_unique hb' hF) hb
      · exact h ⟨F.1, b⟩ hb'
    rw [hsum] at key
    exact key
  · rw [if_neg hF]
    exact h F hF

/-! ## The two points -/

/-- **The labelled empty-graph limit** `o ∈ X_vtype` (paper `prop:single-point`): density
`1` on the edgeless flag of each size, `0` on every edge-containing flag. -/
noncomputable def edgelessPoint : PositiveHomSpace vtype :=
  Classical.choose exists_edgelessPoint

/-- **The labelled complete-graph limit** in `X_vtype`: density `1` on the complete flag
of each size, `0` on every flag missing an edge. -/
noncomputable def completePoint : PositiveHomSpace vtype :=
  Classical.choose exists_completePoint

lemma edgelessPoint_val (F : FinFlag vtype) :
    edgelessPoint.val F = if IsEdgelessFlag F.2 then 1 else 0 :=
  val_eq_boolean_of_nonEdgeless_zero (Classical.choose_spec exists_edgelessPoint) F

lemma completePoint_val (F : FinFlag vtype) :
    completePoint.val F = if IsCompleteFlag F.2 then 1 else 0 :=
  val_eq_boolean_of_nonComplete_zero (Classical.choose_spec exists_completePoint) F

/-- Any point vanishing on the non-edgeless flags *is* the empty-graph limit.
(Two points of `X_vtype` with the same values on all flags are equal: `Subtype.ext`
through the `FunLike` structure of `FlagDensitySpace`.) -/
theorem eq_edgelessPoint_of_nonEdgeless_zero {χ : PositiveHomSpace vtype}
    (h : ∀ F : FinFlag vtype, ¬ IsEdgelessFlag F.2 → χ.val F = 0) : χ = edgelessPoint := by
  apply Subtype.ext
  apply DFunLike.ext
  intro F
  rw [val_eq_boolean_of_nonEdgeless_zero h F, edgelessPoint_val F]

/-- Any point vanishing on the non-complete flags *is* the complete-graph limit. -/
theorem eq_completePoint_of_nonComplete_zero {χ : PositiveHomSpace vtype}
    (h : ∀ F : FinFlag vtype, ¬ IsCompleteFlag F.2 → χ.val F = 0) : χ = completePoint := by
  apply Subtype.ext
  apply DFunLike.ext
  intro F
  rw [val_eq_boolean_of_nonComplete_zero h F, completePoint_val F]

end FlagAlgebras.MetaTheory
