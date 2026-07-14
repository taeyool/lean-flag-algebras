import «LeanFlagAlgebras».Utils.SubgraphUtil
import «LeanFlagAlgebras».Utils.TacticChoose
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Cast.Field

/-!
# Subgraph density

This file is the semantic foundation of the GraphAlgebra layer. It defines the
*subgraph density* `d(H, G)` — the probability that a uniformly random size-`|H|`
induced subgraph of `G` is isomorphic to `H` — together with its pair and triple
generalizations, and lifts every notion to isomorphism classes (`QuotSimpleGraph`).

The headline results are the *chain rule* / averaging identities
(`quotSubgraphDensity_eq_sum_density_prods` and friends, exported as
`density_chain_rule*`): a density can be re-expanded as a sum over intermediate
flags. These identities are the combinatorial heart on which the FlagAlgebra
layer (the quotient algebra A^σ, positive homomorphisms, SOS certificates) is
built.
-/

open Finset
open SimpleGraph
open Classical

namespace GraphAlgebras

variable {T U V W X : Type}
  [Fintype T] [DecidableEq T]
  [Fintype U] [DecidableEq U]
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  [Fintype X] [DecidableEq X]


lemma choose_pair_eq_factorial_div
    (n m k : ℕ) (h_size : m + k ≤ n)
    : n.choose m * (n - m).choose k = n.factorial / (m.factorial * k.factorial * (n - (m + k)).factorial)
  := by
  have h₁ : m ≤ n := Nat.le_of_add_right_le h_size
  have h₂ : k ≤ n - m := (Nat.le_sub_iff_add_le' h₁).mpr h_size
  repeat rw [Nat.choose_eq_factorial_div_factorial] <;> try assumption
  rw [← Nat.mul_div_assoc _ (Nat.factorial_mul_factorial_dvd_factorial h₂)]
  rw [Nat.mul_comm, ← Nat.mul_div_assoc _ (Nat.factorial_mul_factorial_dvd_factorial h₁)]
  rw [(n - m).factorial.mul_comm, m.factorial.mul_comm, ← Nat.div_div_eq_div_mul _ _ m.factorial]
  rw [Nat.mul_div_cancel _ (Nat.factorial_pos (n - m))]
  rw [Nat.div_div_eq_div_mul, Nat.sub_sub, Nat.mul_assoc]

lemma choose_pair_zero
    (n m k : ℕ) (h_size : m + k > n)
    : n.choose m * (n - m).choose k = 0
  := by
  by_cases hm : m > n
  · simp only [Nat.choose_eq_zero_of_lt hm, zero_mul]
  · have hk : k > n - m := by omega
    rw [Nat.choose_eq_zero_of_lt hk, mul_zero]

lemma choose_pair_comm
    (n m k : ℕ)
    : n.choose m * (n - m).choose k = n.choose k * (n - k).choose m
  := by
  by_cases h_size : m + k ≤ n
  · simp only [h_size, choose_pair_eq_factorial_div, Nat.add_comm, Nat.mul_comm]
  · have h_size' : m + k > n := Nat.not_le.mp h_size
    simp only [h_size', choose_pair_zero, Nat.add_comm]


/-- The finite set of induced subgraphs of `G` that are isomorphic to `H`. -/
noncomputable def subgraphSet (H : SimpleGraph V) (G : SimpleGraph W) : Finset (Subgraph G)
  :=
  let p (G' : Subgraph G) : Prop := G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H)
  { G' : Subgraph G | p G' }.toFinset

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
lemma mem_subgraphSet_iff {H : SimpleGraph V} {G : SimpleGraph W} {g : Subgraph G} :
    g ∈ subgraphSet H G ↔ g.IsInduced ∧ Nonempty (g.coe ≃g H) := by
  simp [subgraphSet]

/-- The number of induced subgraphs of `G` that are isomorphic to `H`. -/
noncomputable def subgraphCount (H : SimpleGraph V) (G : SimpleGraph W) : ℕ
  :=
  (subgraphSet H G).card


/-- The subgraph density `d(H, G)`: the fraction of size-`|H|` induced subgraphs of
`G` that are isomorphic to `H`, i.e. the probability that a uniformly random
`|H|`-vertex induced subgraph of `G` is a copy of `H`. -/
noncomputable def subgraphDensity (H : SimpleGraph V) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraphCount H G
  let card_V := Fintype.card V
  let card_W := Fintype.card W
  let num_of_all_induced_subgraph := card_W.choose card_V
  subgraph_cnt / num_of_all_induced_subgraph


/-- The set of *disjoint* pairs of induced subgraphs of `G`, one isomorphic to
`H₁` and the other to `H₂`, whose vertex sets do not overlap. -/
noncomputable def subgraphPairSet (H₁ : SimpleGraph U) (H₂ : SimpleGraph V) (G : SimpleGraph W) : Finset (Subgraph G × Subgraph G)
  :=
  let p (G₁ G₂ : Subgraph G) : Prop :=
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅
  { (G₁, G₂) : Subgraph G × Subgraph G | p G₁ G₂ }.toFinset

omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [DecidableEq W] in
lemma pair_mem_subgraphPairSet_iff
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W} {g₁ g₂ : Subgraph G} :
    ⟨g₁, g₂⟩ ∈ subgraphPairSet H₁ H₂ G ↔
      g₁.IsInduced ∧ Nonempty (g₁.coe ≃g H₁) ∧
      g₂.IsInduced ∧ Nonempty (g₂.coe ≃g H₂) ∧
      g₁.verts ∩ g₂.verts = ∅ := by
  simp only [subgraphPairSet, Set.toFinset_setOf, mem_filter, mem_univ, true_and]

/-- The number of disjoint `(H₁, H₂)`-labelled induced subgraph pairs in `G`. -/
noncomputable def subgraphPairCount (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℕ
  :=
  (subgraphPairSet H₁ H₂ G).card


/-- The pair density: the probability that a uniformly random ordered choice of
disjoint `|H₁|`- and `|H₂|`-vertex induced subgraphs of `G` yields a copy of `H₁`
and a copy of `H₂` respectively. -/
noncomputable def subgraphPairDensity
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) (G : SimpleGraph W) : ℚ
  :=
  let subgraph_cnt := subgraphPairCount H₁ H₂ G
  let W_card := Fintype.card W
  let V_card := Fintype.card V
  let U_card := Fintype.card U
  let num_of_all_induced_subgraphs := W_card.choose V_card * (W_card - V_card).choose U_card
  subgraph_cnt / num_of_all_induced_subgraphs


omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairSet_card_each
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W}
    {G₁ G₂ : Subgraph G} (h : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G)
    : Fintype.card G₁.verts = Fintype.card U ∧ Fintype.card G₂.verts = Fintype.card V
  := by
  simp [subgraphPairSet] at h
  have ⟨_, h_G₁_H₁, _, h_G₂_H₂, _⟩ := h
  rw [Fintype.card_of_bijective (RelIso.bijective h_G₁_H₁.some)]
  rw [Fintype.card_of_bijective (RelIso.bijective h_G₂_H₂.some)]
  simp only [and_self]


omit [DecidableEq U] [DecidableEq V] in
lemma subgraphPairSet_card_union
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W}
    {G₁ G₂ : Subgraph G} (h : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G)
    : Fintype.card (G₁.verts ∪ G₂.verts).toFinset = Fintype.card U + Fintype.card V
  := by
  let ⟨h_G₁_card, h_G₂_card⟩ := subgraphPairSet_card_each h
  simp [subgraphPairSet] at h
  have ⟨_, _, _, _, h_G₁_G₂_disj⟩ := h
  calc
    Fintype.card (G₁.verts ∪ G₂.verts).toFinset
    _ = (G₁.verts ∪ G₂.verts).toFinset.card :=
          Fintype.card_coe (G₁.verts ∪ G₂.verts).toFinset
    _ = (G₁.verts.toFinset ∪ G₂.verts.toFinset).card := by
          rw [Set.toFinset_union]
    _ =  G₁.verts.toFinset.card + G₂.verts.toFinset.card := by
          rw [Finset.card_union, ← Set.toFinset_inter,
            Set.toFinset_eq_empty.mpr h_G₁_G₂_disj, card_empty, tsub_zero]
    _ = Fintype.card U + Fintype.card V := by
          rw [←h_G₁_card, ←h_G₂_card]
          simp only [Set.toFinset_card]


omit [DecidableEq U] [DecidableEq V] in
lemma subgraphPairSet_card_union_Finset
    {H₁ : SimpleGraph U} {H₂ : SimpleGraph V} {G : SimpleGraph W}
    {G₁ G₂ : Subgraph G} (h : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G)
    : (G₁.verts ∪ G₂.verts).toFinset.card = Fintype.card U + Fintype.card V
  := by
  rw [←Fintype.card_coe (G₁.verts ∪ G₂.verts).toFinset, subgraphPairSet_card_union h]


omit [DecidableEq V] [DecidableEq W] in
/-- Subgraph density is nonnegative. -/
theorem subgraphDensity_ge_0
    (H : SimpleGraph V) (G : SimpleGraph W)
    : 0 ≤ subgraphDensity H G
  := by
  apply div_nonneg <;> norm_num


/-- From a graph isomorphism between a subgraph `G₀` of `G` and `H`, extract the
underlying vertex-set bijection `G₀.verts ≃ V`. -/
noncomputable def vert_iso_from_graph_iso
    (H : SimpleGraph V) (G : SimpleGraph W) (G₀ : G.Subgraph)
    (hG₀_iso : Nonempty (Subgraph.coe G₀ ≃g H))
    : {x // x ∈ G₀.verts } ≃ V
  := by
  let g : Subgraph.coe G₀ ≃g H := Classical.choice hG₀_iso
  let f₀ : {x // x ∈ G₀.verts } → V := g
  have hf₀ : Function.Bijective f₀ := RelIso.bijective g
  exact Equiv.ofBijective f₀ hf₀


omit [DecidableEq V] [DecidableEq W] in
/-- Subgraph density is at most `1` (it is a probability). -/
theorem subgraphDensity_le_1
    (H : SimpleGraph V) (G : SimpleGraph W)
    : subgraphDensity H G ≤ 1
  := by
  dsimp only [subgraphDensity, subgraphCount, subgraphSet]
  apply div_le_one_of_le₀
  . have := combinations_card (univ : Finset W) (univ : Finset V).card
    simp only [card_univ] at this
    rw [←this]
    simp only [Nat.cast_le, ge_iff_le]
    let f : G.Subgraph → Finset W := fun G' => G'.verts.toFinset
    apply Finset.card_le_card_of_injOn f
    . rintro G' h_G'
      dsimp only [combinations, f]
      apply mem_filter.mpr
      refine ⟨by simp only [powerset_univ, mem_univ], ?_⟩
      apply card_eq_of_equiv_fintype
      simp only [Set.toFinset_setOf, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at h_G'
      let ⟨_, hG'_iso⟩ := h_G'
      simp only [Set.mem_toFinset]
      exact vert_iso_from_graph_iso H G G' hG'_iso
    . intro G₁ h_G₁ G₂ h_G₂ h_eq
      dsimp only [f] at h_eq
      simp only [Set.toFinset_setOf, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at h_G₁ h_G₂
      have h_eq_verts : G₁.verts = G₂.verts := Set.toFinset_inj.mp h_eq
      let ⟨h_G₁_ind, _⟩ := h_G₁
      let ⟨h_G₂_ind, _⟩ := h_G₂
      exact h_G₁_ind.eq_of_verts_eq h_G₂_ind h_eq_verts
  . norm_num


omit [Fintype V] [DecidableEq V] [DecidableEq W] [DecidableEq U] in
/-- Subgraph counts depend only on the isomorphism class of the host graph. -/
lemma subgraphCount_eq_of_iso
    (H : SimpleGraph V) {G₀ : SimpleGraph W} {G₁ : SimpleGraph U}
    (h_iso : G₀ ≃g G₁)
    : subgraphCount H G₀ = subgraphCount H G₁
  := by
  let S₀ := { G' : Subgraph G₀ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let S₁ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphIsoH h_iso H
  have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  dsimp only [subgraphCount, subgraphSet]
  simp only [Set.toFinset_card, Set.coe_setOf]
  exact this


omit [DecidableEq V] [DecidableEq W] in
lemma subgraphDensity_respects_eqv_on_G
    (H : SimpleGraph V) {G₀ G₁ : SimpleGraph W} (h_eqv : graph_eqv G₀ G₁)
    : subgraphDensity H G₀ = subgraphDensity H G₁
  := by
  dsimp only [subgraphDensity]
  congr 2
  exact subgraphCount_eq_of_iso H h_eqv.some


/-- `subgraphDensity H` lifted along the host argument to isomorphism classes of
graphs (`QuotSimpleGraph`). -/
noncomputable def subgraphDensityLifted
    (H : SimpleGraph V) : QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift (fun G : SimpleGraph W => subgraphDensity H G)
  intro _ _ h_eqv
  exact subgraphDensity_respects_eqv_on_G H h_eqv


omit [DecidableEq V] in
lemma subgraphDensityLifted_respects_eqv
    (H₀ H₁ : SimpleGraph V) (h_eqv : graph_eqv H₀ H₁) (G : QuotSimpleGraph W)
    : subgraphDensityLifted H₀ G = subgraphDensityLifted H₁ G
  := by
  dsimp only [subgraphDensityLifted]
  congr
  ext Greg
  let φ : H₀ ≃g H₁ := Classical.choice h_eqv
  let S₀ := { G' : Subgraph Greg | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₀) }
  let S₁ := { G' : Subgraph Greg | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H₁) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphInG φ Greg
  have h_count : subgraphDensity H₀ Greg = subgraphDensity H₁ Greg := by
    dsimp only [subgraphDensity, subgraphCount, subgraphSet]
    have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp only [Set.toFinset_card, Set.coe_setOf]
    tauto
  exact h_count


/-- The subgraph density `d(H, G)` as a function of the isomorphism classes of
both `H` and `G`. This is the canonical density on `QuotSimpleGraph`. -/
noncomputable def quotSubgraphDensity
    : QuotSimpleGraph V → QuotSimpleGraph W → ℚ :=
  Quotient.lift subgraphDensityLifted
    fun H₀ H₁ h_eqv => funext fun G => subgraphDensityLifted_respects_eqv H₀ H₁ h_eqv G


/-- The empty graph on `0` vertices occurs exactly once as an induced subgraph
(the empty subgraph). -/
lemma subgraphCount_empty
    (G : SimpleGraph (Fin n))
    : subgraphCount (emptyGraph (Fin 0)) G = 1
  := by
  let S₀ := { G' : Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g (emptyGraph (Fin 0))) }
  let S₁ := { G' : Subgraph G | G' = ⊥ }
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    constructor
    · intro ⟨_, h_iso⟩
      rw [← subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0] at h_iso
      rw [h_iso, Set.mem_setOf_eq]
    · rintro rfl
      refine ⟨fun _ ↦ ?_, subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mp rfl⟩
      simp only [Subgraph.verts_bot, Set.mem_empty_iff_false, IsEmpty.forall_iff]
  calc
    S₀.toFinset.card = S₁.toFinset.card := by
        simp only [h_S₀_S₁, Set.toFinset_card, Fintype.card_ofFinset, Set.setOf_eq_eq_singleton]
    _ = 1 := by
        simp only [Set.setOf_eq_eq_singleton, Set.toFinset_singleton, card_singleton, S₁]

/-- The density of the empty `0`-vertex graph is always `1` (the identity flag). -/
lemma subgraphDensity_empty
    (G : SimpleGraph (Fin n)) : subgraphDensity (emptyGraph (Fin 0)) G = 1
  := by
  simp [subgraphDensity]
  exact subgraphCount_empty G


lemma quotSubgraphDensity_empty
    (G : QuotSimpleGraph (Fin n)) : quotSubgraphDensity ⟦emptyGraph (Fin 0)⟧ G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  apply subgraphDensity_empty


omit [DecidableEq V] in
/-- A graph occurs exactly once as an induced subgraph of itself (the whole
graph `⊤`). -/
lemma subgraphCount_self
    (G : SimpleGraph V) : subgraphCount G G = 1
  := by
  let S₀ := { G' : Subgraph G | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g G) }
  let S₁ : Finset (Subgraph G):= { ⊤ }
  have h_S₀_S₁ : S₀ = S₁ := by
    ext G'
    simp only [Set.mem_setOf_eq, coe_singleton, Set.mem_singleton_iff, S₀, S₁]
    exact induced_subgraph_iso_G_iff_eq_top
  calc
    S₀.toFinset.card = S₁.card := by simp only [h_S₀_S₁, toFinset_coe]
    _ = 1 := by simp only [card_singleton, S₁]


omit [DecidableEq V] in
/-- The density of a graph in itself is `1`. -/
lemma subgraphDensity_self
    (G : SimpleGraph V) : subgraphDensity G G = 1
  := by
  simp [subgraphDensity]
  exact subgraphCount_self G


lemma quotSubgraphDensity_self
    (G : QuotSimpleGraph (Fin n)) : quotSubgraphDensity G G = 1
  := by
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact subgraphDensity_self _


omit [DecidableEq V] in
/-- A graph `G₀` on `|V|` vertices not isomorphic to another graph `G₁` on the
same number of vertices occurs `0` times as an induced subgraph of `G₁`. -/
lemma subgraphCount_other
    {G₀ G₁ : SimpleGraph V} (h_neq : IsEmpty (G₀ ≃g G₁)) : subgraphCount G₀ G₁ = 0
  := by
  rw [←not_nonempty_iff] at h_neq
  let S₀ := { G' : Subgraph G₁ | G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g G₀) }
  show S₀.toFinset.card = 0
  have h_S₀ : S₀ ⊆ ∅ := by
    intro G' ⟨h_ind_G', h_iso_G'⟩
    have f_iso_G₀_G' : G₀ ≃g G'.coe := h_iso_G'.some.symm
    have f_iso_G'_G₁ : G'.coe ≃g G₁ := by
      have : G' = ⊤ := induced_full_subgraph_eq_top ⟨h_ind_G', h_iso_G'⟩
      let g : (⊤ : Subgraph G₁).coe ≃g G₁ := SimpleGraph.Subgraph.topIso
      rw [←this] at g
      exact g
    have f_iso_G₀_G₁ : G₀ ≃g G₁ := Iso.comp f_iso_G'_G₁ f_iso_G₀_G'
    exact h_neq ⟨f_iso_G₀_G₁⟩
  rw [Set.subset_empty_iff] at h_S₀
  simp_rw [h_S₀, Set.toFinset_empty, card_empty]


omit [DecidableEq V] in
/-- Two non-isomorphic graphs on the same vertex count have density `0`. -/
lemma subgraphDensity_other
    {G₀ G₁ : SimpleGraph V} (h_neq : IsEmpty (G₀ ≃g G₁)) : subgraphDensity G₀ G₁ = 0
  := by
  dsimp only [subgraphDensity]
  simp only [Nat.cast_zero, Nat.choose_self, Nat.cast_one, div_one, subgraphCount_other h_neq]


lemma quotSubgraphDensity_other
    {G₀ G₁ : QuotSimpleGraph (Fin n)} (h_neq : G₀ ≠ G₁) : quotSubgraphDensity G₀ G₁ = 0
  := by
  rcases Quotient.exists_rep G₀ with ⟨G₀rep, rfl⟩
  rcases Quotient.exists_rep G₁ with ⟨G₁rep, rfl⟩
  have h_neq' : IsEmpty (G₀rep ≃g G₁rep) := by
    rw [←not_nonempty_iff]
    intro h_iso
    exact h_neq (Quotient.sound h_iso)
  exact subgraphDensity_other h_neq'


/-- Quotient-level density is nonnegative. -/
theorem quotSubgraphDensity_ge_0
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : 0 ≤ quotSubgraphDensity H G
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, rfl⟩
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact subgraphDensity_ge_0 _ _


/-- Quotient-level density is at most `1`. -/
theorem quotSubgraphDensity_le_1
    (H : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : quotSubgraphDensity H G ≤ 1
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, rfl⟩
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact subgraphDensity_le_1 _ _


omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairDensity_respects_eqv_on_G
    (H₁ : SimpleGraph U) (H₂ : SimpleGraph V) {G G' : SimpleGraph W} (h_eqv : graph_eqv G G')
    : subgraphPairDensity H₁ H₂ G = subgraphPairDensity H₁ H₂ G'
  := by
  dsimp only [subgraphPairDensity]
  dsimp only [graph_eqv] at h_eqv
  let φ : G ≃g G' := Classical.choice h_eqv
  let S₀ := { (G₁, G₂) : Subgraph G × Subgraph G |
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅ }
  let S₁ := { (G₁, G₂) : Subgraph G' × Subgraph G' |
    G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁) ∧
    G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂) ∧
    G₁.verts ∩ G₂.verts = ∅ }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedSubgraphPairIsoH φ H₁ H₂
  dsimp only [subgraphPairCount, subgraphPairSet]
  have : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp only [Set.coe_setOf, Set.toFinset_card]; tauto


/-- `subgraphPairDensity H₁ H₂` lifted along the host argument to isomorphism
classes of graphs. -/
noncomputable def subgraphPairDensityLifted
    (H₁ : SimpleGraph V) (H₂ : SimpleGraph U) : QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift (fun G : SimpleGraph W => subgraphPairDensity H₁ H₂ G)
  intro _ _ h_eqv
  exact subgraphPairDensity_respects_eqv_on_G H₁ H₂ h_eqv


omit [DecidableEq U] [DecidableEq V] in
lemma subgraphPairDensityLifted_respects_eqv
    {S₀ : SimpleGraph U} {S₁ : SimpleGraph U} (h_eqv_S : graph_eqv S₀ S₁)
    {H₀ : SimpleGraph V} {H₁ : SimpleGraph V} (h_eqv_H : graph_eqv H₀ H₁)
    (G : QuotSimpleGraph W)
    : subgraphPairDensityLifted S₀ H₀ G = subgraphPairDensityLifted S₁ H₁ G
  := by
  dsimp only [subgraphPairDensityLifted]
  dsimp only [graph_eqv] at h_eqv_S h_eqv_H
  congr
  ext Greg
  let ψ : S₀ ≃g S₁ := Classical.choice h_eqv_S
  let φ : H₀ ≃g H₁ := Classical.choice h_eqv_H
  let X₀ := { (G', G'') : Subgraph Greg × Subgraph Greg |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g S₀) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H₀) ∧
                G'.verts ∩ G''.verts = ∅ }
  let X₁ := { (G', G'') : Subgraph Greg × Subgraph Greg |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g S₁) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H₁) ∧
                G'.verts ∩ G''.verts = ∅ }
  let h_iso_X₀_X₁ : X₀ ≃ X₁ := isoSetOfInducedSubgraphPairInG ψ φ Greg
  dsimp only [subgraphPairDensity, subgraphPairCount, subgraphPairSet]
  have : Fintype.card X₀ = Fintype.card X₁ := Fintype.card_congr h_iso_X₀_X₁
  simp_all only [Set.coe_setOf, Set.toFinset_card, X₀, X₁]


/-- The disjoint-pair density as a function of the isomorphism classes of `H₁`,
`H₂` and the host `G`. -/
noncomputable def quotSubgraphPairDensity
    : QuotSimpleGraph U → QuotSimpleGraph V → QuotSimpleGraph W → ℚ
  := by
  apply Quot.lift₂ subgraphPairDensityLifted
  . intro S _ _ h_eqv_H
    ext G
    exact subgraphPairDensityLifted_respects_eqv (graph_eqv.refl S) h_eqv_H G
  . intro _ _ H h_eqv_S
    ext G
    exact subgraphPairDensityLifted_respects_eqv h_eqv_S (graph_eqv.refl H) G


omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [DecidableEq W] in
lemma subgraphPairCount_comm
    (H : SimpleGraph U) (H' : SimpleGraph V) (G : SimpleGraph W)
    : subgraphPairCount H H' G = subgraphPairCount H' H G
  := by
  dsimp only [subgraphPairCount, subgraphPairSet]
  let S₀ := { (G', G'') : Subgraph G × Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H) ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H') ∧
                G'.verts ∩ G''.verts = ∅ }
  let S₁ := { (G', G'') : Subgraph G × Subgraph G |
                G'.IsInduced ∧ Nonempty (Subgraph.coe G' ≃g H') ∧
                G''.IsInduced ∧ Nonempty (Subgraph.coe G'' ≃g H) ∧
                G'.verts ∩ G''.verts = ∅ }
  have h_iso_S₀_S₁ : S₀ ≃ S₁ := by
    apply Equiv.subtypeEquiv (Equiv.prodComm (Subgraph G) (Subgraph G))
    intro ⟨G', G''⟩
    constructor <;>
    { intro ⟨h₁, h₂, h₃, h₄, h₅⟩
      let h₅' := Set.inter_comm _ _ ▸ h₅
      exact ⟨h₃, h₄, h₁, h₂, h₅'⟩ }
  have h_count : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]


omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- The pair density is symmetric in its two labelled graphs. -/
lemma subgraphPairDensity_comm
    (H : SimpleGraph U) (H' : SimpleGraph V) (G : SimpleGraph W)
    : subgraphPairDensity H H' G = subgraphPairDensity H' H G
  := by
  dsimp only [subgraphPairDensity]
  rw [subgraphPairCount_comm H H' G]
  congr 1
  exact congrArg Nat.cast (choose_pair_comm _ _ _)


/-- Quotient-level pair density is symmetric in its two labelled graphs. -/
lemma quotSubgraphPairDensity_comm
    (H₁ : QuotSimpleGraph U) (H₂ : QuotSimpleGraph V) (G : QuotSimpleGraph W)
    : quotSubgraphPairDensity H₁ H₂ G = quotSubgraphPairDensity H₂ H₁ G
  := by
  rcases Quotient.exists_rep H₁ with ⟨H₁rep, rfl⟩
  rcases Quotient.exists_rep H₂ with ⟨H₂rep, rfl⟩
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact subgraphPairDensity_comm _ _ _


/-- Pairing with the empty `0`-vertex graph degenerates the pair count to the
ordinary subgraph count. -/
lemma subgraphPairCount_empty
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphPairCount (emptyGraph (Fin 0)) H G = subgraphCount H G
  := by
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
      dsimp only [f] at h_eq
      simp_rw [Prod.mk_inj, h_eq, and_true]
      have h_G₀ : G₀ = ⊥ := subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mpr h₂
      have h_G₀' : G'₀ = ⊥ := subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mpr h₂'
      rw [h_G₀, h_G₀']
    have h_f_surj : Set.SurjOn f S₀ S₁ := by
      intro G'' ⟨h₁,h₂⟩
      use ⟨⊥, G''⟩
      have h_bot_isinduced : (⊥ : Subgraph G).IsInduced := by
        intro u h_u
        exact h_u.elim
      have h_bot_iso : Nonempty ((⊥ : Subgraph G).coe ≃g (emptyGraph (Fin 0))) :=
        subgraph_eq_empty_subgraph_iff_iso_empty_graph_on_fin_0.mp rfl
      simp only [Set.mem_setOf_eq, Subgraph.verts_bot, Set.empty_inter, and_true, S₀]
      exact ⟨⟨h_bot_isinduced, h_bot_iso, h₁, h₂⟩, rfl⟩
    exact Set.BijOn.equiv f (Set.BijOn.mk h_f_S₀_S₁ h_f_inj h_f_surj)
  have h_count : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
  simp only [Fintype.card_ofFinset, Set.toFinset_card] at h_count ⊢
  simp only [h_count]


/-- Pairing with the empty `0`-vertex graph degenerates the pair density to the
ordinary subgraph density. -/
lemma subgraphPairDensity_empty
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    : subgraphPairDensity (emptyGraph (Fin 0)) H G  = subgraphDensity H G
  := by
  dsimp only [subgraphPairDensity, subgraphDensity]
  simp only [Fintype.card_fin, Nat.choose_zero_right, tsub_zero, one_mul,
    ← subgraphPairCount_empty H G]


/-- Quotient-level: pairing with the empty `0`-vertex graph degenerates the pair
density to the ordinary density. -/
lemma quotSubgraphPairDensity_empty
    (H : QuotSimpleGraph (Fin n)) (G : QuotSimpleGraph (Fin m))
    : quotSubgraphPairDensity ⟦emptyGraph (Fin 0)⟧ H G = quotSubgraphDensity H G
  := by
  rcases Quotient.exists_rep H with ⟨Hrep, rfl⟩
  rcases Quotient.exists_rep G with ⟨Grep, rfl⟩
  exact subgraphPairDensity_empty _ _


lemma card_eq_imply_set_eq
    (A B : Finset (Fin ℓ)) (h_card_eq : A.card + B.card = ℓ) (h_disj : A ∩ B = ∅)
    : A ∪ B = univ
  := by
  have h_card_A_union_B : (A ∪ B).card = ℓ := by
    have : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr h_disj
    exact Finset.card_union_of_disjoint this ▸ h_card_eq
  apply (compl_eq_empty_iff (A ∪ B)).mp (Finset.card_eq_zero.mp _)
  calc
    (univ \ (A ∪ B)).card
    _ = (univ : Finset (Fin ℓ)).card - (A ∪ B).card := card_sdiff_of_subset (subset_univ (A ∪ B))
    _ = ℓ - (A ∪ B).card := by rw [card_univ, Fintype.card_fin]
    _ = ℓ - ℓ := by rw [h_card_A_union_B]
    _ = 0 := ℓ.sub_self

/-! ## The chain rule: re-expanding densities over intermediate flags -/

/-- The combinatorial bijection underlying the chain rule: disjoint `(H₁, H₂)`
subgraph pairs of `G` together with an enclosing `ℓ₃`-vertex induced subgraph `G₃`
correspond to a choice of an `ℓ₃`-vertex flag `F`, an `(H₁, H₂)` pair inside `F`,
and an embedding of `F` into `G`. -/
noncomputable def subgraphPairSet_iso_union_quotSimpleGraphSet
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ))
    : { (⟨⟨G₁,G₂⟩, _⟩, G₃) : subgraphPairSet H₁ H₂ G × Subgraph G
            | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts }
      ≃
      (F : QuotSimpleGraph (Fin ℓ₃)) × subgraphPairSet H₁ H₂ F.out × subgraphSet F.out G
  := by
  let S := { (⟨⟨G₁,G₂⟩, _⟩, G₃) : subgraphPairSet H₁ H₂ G × Subgraph G
            | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts}

  let S₀' := { (G₁, G₂, G₃) : Subgraph G × Subgraph G × Subgraph G
              | G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁)
                ∧ G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂)
                ∧ G₃.IsInduced ∧ (Fintype.card G₃.verts) = ℓ₃
                ∧ G₁.verts ∩ G₂.verts = ∅
                ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts }

  let S₁' := { (F, G₁, G₂, G₃) : QuotSimpleGraph (Fin ℓ₃) × Subgraph G × Subgraph G × Subgraph G
              | G₁.IsInduced ∧ Nonempty (Subgraph.coe G₁ ≃g H₁)
                ∧ G₂.IsInduced ∧ Nonempty (Subgraph.coe G₂ ≃g H₂)
                ∧ G₃.IsInduced ∧ (Fintype.card G₃.verts) = ℓ₃
                ∧ G₁.verts ∩ G₂.verts = ∅
                ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts
                ∧ Nonempty ((G₃ : Subgraph G).coe ≃g F.out) }

  let S₂' := { ⟨F, K₁, K₂, G₃⟩ : (F : QuotSimpleGraph (Fin ℓ₃)) × Subgraph F.out × Subgraph F.out × Subgraph G
              | K₁.IsInduced ∧ Nonempty (K₁.coe ≃g H₁)
                ∧ K₂.IsInduced ∧ Nonempty (K₂.coe ≃g H₂)
                ∧ G₃.IsInduced ∧ (Fintype.card G₃.verts) = ℓ₃
                ∧ K₁.verts ∩ K₂.verts = ∅
                ∧ Nonempty ((G₃ : Subgraph G).coe ≃g F.out) }

  let S₃' := (F : QuotSimpleGraph (Fin ℓ₃)) × subgraphPairSet H₁ H₂ F.out × subgraphSet F.out G

  let f_S_S₀'_fwd : S → S₀' := by
    intro ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    rw [pair_mem_subgraphPairSet_iff] at h_G₁_G₂
    let ⟨h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₁_G₂_disj⟩ := h_G₁_G₂
    exact ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂_disj, h_G₁_G₂_G₃⟩

  have h_inj_S_S₀' : Function.Injective f_S_S₀'_fwd := by
    intro _ _ h_eq
    simp only [f_S_S₀'_fwd] at h_eq
    repeat split at h_eq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h_eq
    simp only [Set.mem_setOf_eq, h_eq]

  have h_surj_S_S₀' : Function.Surjective f_S_S₀'_fwd := by
    intro ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂_disj, h_G₁_G₂_G₃⟩
    have h_G₁_G₂ : ⟨G₁, G₂⟩ ∈ subgraphPairSet H₁ H₂ G := by
      rw [pair_mem_subgraphPairSet_iff]
      exact ⟨h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₁_G₂_disj⟩
    use ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    simp only [f_S_S₀'_fwd]
    split
    rfl

  let f_S_S₀' : S ≃ S₀' :=
    Equiv.ofBijective f_S_S₀'_fwd ⟨h_inj_S_S₀', h_surj_S_S₀'⟩

  let f_S₀'_S₁'_fwd : S₀' → S₁' :=
    fun ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃⟩ =>
      let ⟨F, f_iso_F_G₃⟩ := getCanonicalQuotSimpleGraph G₃.coe h_G₃_card
      ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, Nonempty.intro f_iso_F_G₃.symm⟩

  have h_inj_S₀'_S₁' : Function.Injective f_S₀'_S₁'_fwd := by
    intro ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃⟩
      ⟨⟨G₁', G₂', G₃'⟩, h_G₁'_ind, h_G₁'_H₁, h_G₂'_ind, h_G₂'_H₂, h_G₃'_ind, h_G₃'_card, h_G₁'_G₂', h_G₁'_G₂'_G₃'⟩
      h_eq
    simp only [← Subtype.val_inj, Prod.mk_inj, f_S₀'_S₁'_fwd] at h_eq ⊢
    tauto

  have h_surj_S₀'_S₁' : Function.Surjective f_S₀'_S₁'_fwd := by
    intro ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, h_G₃_F⟩
    use ⟨⟨G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃⟩
    simp only [← Subtype.val_inj, Prod.mk_inj, and_true, f_S₀'_S₁'_fwd]
    rw [←(getCanonicalQuotSimpleGraph_self F)]
    exact getCanonicalQuotSimpleGraph_iso _ _ _ _ h_G₃_F.some

  let f_S₀'_S₁' : S₀' ≃ S₁' :=
    Equiv.ofBijective f_S₀'_S₁'_fwd ⟨h_inj_S₀'_S₁', h_surj_S₀'_S₁'⟩

  let f_S₁'_S₂'_fwd : S₁' → S₂' := by
    intro ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, h_G₃_F⟩
    let f_G₃_Fout : G₃.coe ≃g F.out := h_G₃_F.some
    have h_G₁_verts_sub_G₃_verts : G₁.verts ⊆ G₃.verts := fun a h_a =>
      h_G₁_G₂_G₃ ((Set.mem_union _ _ _).mpr (.inl h_a))
    have h_G₂_verts_sub_G₃_verts : G₂.verts ⊆ G₃.verts := fun a h_a =>
      h_G₁_G₂_G₃ ((Set.mem_union _ _ _).mpr (.inr h_a))
    have h_G₁_le : G₁ ≤ G₃ := h_G₃_ind.le_of_verts_subset h_G₁_verts_sub_G₃_verts
    have h_G₂_le : G₂ ≤ G₃ := h_G₃_ind.le_of_verts_subset h_G₂_verts_sub_G₃_verts
    let G₁' := subgraphFromOrder h_G₁_le
    let G₂' := subgraphFromOrder h_G₂_le
    let f_iso_G₁_G₁' : G₁.coe ≃g G₁'.coe := isoToSubgraphFromOrder h_G₁_le
    let f_iso_G₂_G₂' : G₂.coe ≃g G₂'.coe := isoToSubgraphFromOrder h_G₂_le
    have h_G₁'_ind : G₁'.IsInduced := subgraphFromOrder_preserve_inducedness h_G₁_le h_G₁_ind
    have h_G₂'_ind : G₂'.IsInduced := subgraphFromOrder_preserve_inducedness h_G₂_le h_G₂_ind
    have h_G₁'_G₂'_disj : G₁'.verts ∩ G₂'.verts = ∅ := subgraphFromOrder_preserve_disjointedness h_G₁_le h_G₂_le h_G₁_G₂
    let K₁ := subgraphFromIso f_G₃_Fout G₁'
    let K₂ := subgraphFromIso f_G₃_Fout G₂'
    let f_iso_G₁'_K₁ : Subgraph.coe G₁' ≃g Subgraph.coe K₁ := isoToSubgraphFromIso f_G₃_Fout G₁'
    let f_iso_G₂'_K₂ : Subgraph.coe G₂' ≃g Subgraph.coe K₂ := isoToSubgraphFromIso f_G₃_Fout G₂'
    have h_K₁_ind : K₁.IsInduced := subgraphFromIso_preserve_inducedness f_G₃_Fout G₁' h_G₁'_ind
    have h_K₂_ind : K₂.IsInduced := subgraphFromIso_preserve_inducedness f_G₃_Fout G₂' h_G₂'_ind
    have h_K₁_K₂_disj : K₁.verts ∩ K₂.verts = ∅ := subgraphFromIso_preserve_disjointedness f_G₃_Fout G₁' G₂' h_G₁'_G₂'_disj
    let f_iso_K₁_H₁ : Subgraph.coe K₁ ≃g H₁ := (f_iso_G₁_G₁'.trans f_iso_G₁'_K₁).symm.trans h_G₁_H₁.some
    let f_iso_K₂_H₂ : Subgraph.coe K₂ ≃g H₂ := (f_iso_G₂_G₂'.trans f_iso_G₂'_K₂).symm.trans h_G₂_H₂.some
    exact ⟨⟨F, K₁, K₂, G₃⟩,
           h_K₁_ind, Nonempty.intro f_iso_K₁_H₁,
           h_K₂_ind, Nonempty.intro f_iso_K₂_H₂,
           h_G₃_ind, h_G₃_card,
           h_K₁_K₂_disj, h_G₃_F⟩

  have h_inj_S₁'_S₂' : Function.Injective f_S₁'_S₂'_fwd := by
    intro ⟨⟨F, G₁, G₂, G₃⟩, h_G₁_ind, h_G₁_H₁, h_G₂_ind, h_G₂_H₂, h_G₃_ind, h_G₃_card, h_G₁_G₂, h_G₁_G₂_G₃, h_G₃_F⟩
      ⟨⟨F', G₁', G₂', G₃'⟩, h_G₁'_ind, h_G₁'_H₁, h_G₂'_ind, h_G₂'_H₂, h_G₃'_ind, h_G₃'_card, h_G₁'_G₂', h_G₁'_G₂'_G₃', h_G₃'_F⟩
      h_eq
    simp [f_S₁'_S₂'_fwd, subgraphFromIso, subgraphFromOrder] at h_eq
    obtain ⟨rfl, h_eq'⟩ := h_eq
    simp only [heq_eq_eq, Prod.mk.injEq, Subgraph.mk.injEq, Subtype.mk.injEq, true_and] at h_eq' ⊢
    have : G₃ = G₃' := h_eq'.2.2
    subst this
    have : h_G₃_F = h_G₃'_F := rfl
    subst this

    have ⟨h_G₁_verts_G₃_verts, h_G₂_verts_G₃_verts⟩ := Set.union_subset_iff.mp h_G₁_G₂_G₃
    have ⟨h_G₁'_verts_G₃_verts, h_G₂'_verts_G₃_verts⟩ := Set.union_subset_iff.mp h_G₁'_G₂'_G₃'
    have h_eq_verts : ∀ (G₀ G₀' : Subgraph G), G₀.verts ⊆ G₃.verts → G₀'.verts ⊆ G₃.verts
                        → h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀.verts} = h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀'.verts}
                        → G₀.verts = G₀'.verts
      := fun G₀ G₀' h_G₀_G₃ h_G₀'_G₃ h_G₀_G₀' =>
      calc
        G₀.verts = {u : G₃.verts | ↑u ∈ G₀.verts} := Eq.symm (Subtype.coe_image_of_subset h_G₀_G₃)
        _ = (h_G₃_F.some.symm ∘ h_G₃_F.some) '' {u : G₃.verts | ↑u ∈ G₀.verts} := by simp
        _ = (h_G₃_F.some.symm '' (h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀.verts})) :=
              congr rfl (Set.image_comp ⇑h_G₃_F.some.symm ⇑h_G₃_F.some {u | ↑u ∈ G₀.verts})
        _ = (h_G₃_F.some.symm '' (h_G₃_F.some '' {u : G₃.verts | ↑u ∈ G₀'.verts})) :=
              congr rfl (congr rfl h_G₀_G₀')
        _ = (h_G₃_F.some.symm ∘ h_G₃_F.some) '' {u : G₃.verts | ↑u ∈ G₀'.verts} :=
              congr rfl (Eq.symm (Set.image_comp ⇑h_G₃_F.some.symm ⇑h_G₃_F.some {u | ↑u ∈ G₀'.verts}))
        _ = {u : G₃.verts | ↑u ∈ G₀'.verts} := by simp
        _ = G₀'.verts := Subtype.coe_image_of_subset h_G₀'_G₃
    have h_G₁_verts_G₁'_verts : G₁.verts = G₁'.verts :=
      h_eq_verts G₁ G₁' h_G₁_verts_G₃_verts h_G₁'_verts_G₃_verts (by simp_all only)
    have h_G₂_verts_G₂'_verts : G₂.verts = G₂'.verts :=
      h_eq_verts G₂ G₂' h_G₂_verts_G₃_verts h_G₂'_verts_G₃_verts (by simp_all only)

    have h_eq_ind_subgraph : ∀ (G₀ G₀' : Subgraph G), G₀.IsInduced → G₀'.IsInduced → G₀.verts = G₀'.verts → G₀ = G₀'
      := fun G₀ G₀' h_G₀_ind h_G₀'_ind h_G₀_G₀' =>
      calc
        G₀ = ↑(⟨G₀, h_G₀_ind⟩ : {G' : Subgraph G | G'.IsInduced}) := rfl
        _  = ↑(⟨(⊤ : G.Subgraph).induce G₀.verts, Subgraph.induce_top_isInduced G G₀.verts⟩ : {G' : Subgraph G | G'.IsInduced}) :=
                congrArg Subtype.val (SetCoe.ext (h_G₀_ind.induce_top_verts).symm)
        _  = ↑(⟨(⊤ : G.Subgraph).induce G₀'.verts, Subgraph.induce_top_isInduced G G₀'.verts⟩ : {G' : Subgraph G | G'.IsInduced})  := by
                rw [←h_G₀_G₀']
        _  = ↑(⟨G₀', h_G₀'_ind⟩ : {G' : Subgraph G | G'.IsInduced}) :=
                congrArg Subtype.val (SetCoe.ext (h_G₀'_ind.induce_top_verts).symm).symm
        _  = G₀' := rfl

    exact ⟨h_eq_ind_subgraph G₁ G₁' h_G₁_ind h_G₁'_ind h_G₁_verts_G₁'_verts,
           h_eq_ind_subgraph G₂ G₂' h_G₂_ind h_G₂'_ind h_G₂_verts_G₂'_verts, rfl⟩

  have h_surj_S₁'_S₂' : Function.Surjective f_S₁'_S₂'_fwd := by
    intro ⟨⟨F, K₁, K₂, G₃⟩,
          h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, h_G₃_card, h_K₁_K₂_disj, h_iso_G₃_Fout⟩
    let f_G₃_Fout : G₃.coe ≃g F.out := h_iso_G₃_Fout.some
    let G₁' := subgraphFromPartialIso f_G₃_Fout.symm K₁
    let G₂' := subgraphFromPartialIso f_G₃_Fout.symm K₂
    let h_G₁'_iso := isoToSubgraphFromPartialIso f_G₃_Fout.symm K₁
    let h_G₂'_iso := isoToSubgraphFromPartialIso f_G₃_Fout.symm K₂
    let h_G₁' : G₁'.coe ≃g H₁ := h_G₁'_iso.symm.trans h_iso_K₁_H₁.some
    let h_G₂' : G₂'.coe ≃g H₂ := h_G₂'_iso.symm.trans h_iso_K₂_H₂.some
    let h_G₁'_ind : G₁'.IsInduced := subgraphFromPartialIso_preserve_inducedness f_G₃_Fout.symm K₁ h_G₃_ind h_K₁_ind
    let h_G₂'_ind : G₂'.IsInduced := subgraphFromPartialIso_preserve_inducedness f_G₃_Fout.symm K₂ h_G₃_ind h_K₂_ind
    let h_G₁'_G₂'_disj : G₁'.verts ∩ G₂'.verts = ∅ := subgraphFromPartialIso_preserve_disjointedness f_G₃_Fout.symm K₁ K₂ h_K₁_K₂_disj
    have h_G₁'_verts_union_G₂'_verts : G₁'.verts ∪ G₂'.verts ⊆ G₃.verts := by
      rw [Set.union_subset_iff]; constructor <;> dsimp only [G₁', G₂'] <;>
      exact Subgraph.verts_mono (subgraphFromPartialIso_le _ _)
    use ⟨⟨F, G₁', G₂', G₃⟩,
          h_G₁'_ind, Nonempty.intro h_G₁', h_G₂'_ind, Nonempty.intro h_G₂',
          h_G₃_ind, h_G₃_card, h_G₁'_G₂'_disj, h_G₁'_verts_union_G₂'_verts, h_iso_G₃_Fout⟩
    simp [G₁', G₂', f_S₁'_S₂'_fwd, subgraphFromPartialIso, subgraphByComposition, subgraphFromIso,
      subgraphFromOrder, Relation.Map]
    constructor <;> ext u v <;> simp [f_G₃_Fout]

  let f_S₁'_S₂' : S₁' ≃ S₂' :=
    Equiv.ofBijective f_S₁'_S₂'_fwd ⟨h_inj_S₁'_S₂', h_surj_S₁'_S₂'⟩

  let f_S₂'_S₃'_fwd : S₂' → S₃' := by
    intro ⟨⟨F, K₁, K₂, G₃⟩,
          h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, _, h_K₁_K₂_disj, h_iso_G₃_Fout⟩
    let h_K₁_K₂_Fout : ⟨K₁, K₂⟩ ∈ subgraphPairSet H₁ H₂ F.out := by
      rw [pair_mem_subgraphPairSet_iff]
      exact ⟨h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_K₁_K₂_disj⟩
    let h_G₃_G : G₃ ∈ subgraphSet F.out G := by
      simp [subgraphSet]
      exact ⟨h_G₃_ind, h_iso_G₃_Fout⟩
    exact ⟨F, ⟨⟨K₁, K₂⟩, h_K₁_K₂_Fout⟩, ⟨G₃, h_G₃_G⟩⟩

  have h_inj_S₂'_S₃' : Function.Injective f_S₂'_S₃'_fwd := by
    intro ⟨⟨F, K₁, K₂, G₃⟩,
          h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, h_G₃_card, h_K₁_K₂_disj, h_iso_G₃_Fout⟩
      ⟨⟨F', K₁', K₂', G₃'⟩,
          h_K₁'_ind, h_iso_K₁'_H₁, h_K₂'_ind, h_iso_K₂'_H₂, h_G₃'_ind, h_G₃'_card, h_K₁'_K₂'_disj, h_iso_G₃'_Fout⟩
      h_eq
    dsimp only [f_S₂'_S₃'_fwd] at h_eq
    rcases h_eq with ⟨h_F_F', h_eq'⟩
    rfl

  have h_surj_S₂'_S₃' : Function.Surjective f_S₂'_S₃'_fwd := by
    intro ⟨F, ⟨⟨K₁, K₂⟩, h_K₁_K₂_Fout⟩, ⟨G₃, h_G₃_G⟩⟩
    simp [subgraphSet] at h_G₃_G
    obtain ⟨h_G₃_ind, h_iso_G₃_Fout⟩ := h_G₃_G
    obtain ⟨h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_K₁_K₂_disj⟩ :=
      pair_mem_subgraphPairSet_iff.mp h_K₁_K₂_Fout
    have h_G₃_card : Fintype.card G₃.verts = ℓ₃ := by
      rw [←Fintype.card_fin ℓ₃]
      exact Fintype.card_of_bijective (RelIso.bijective h_iso_G₃_Fout.some)
    use ⟨⟨F, K₁, K₂, G₃⟩, h_K₁_ind, h_iso_K₁_H₁, h_K₂_ind, h_iso_K₂_H₂, h_G₃_ind, h_G₃_card, h_K₁_K₂_disj, h_iso_G₃_Fout⟩

  let f_S₂'_S₃' : S₂' ≃ S₃' :=
    Equiv.ofBijective f_S₂'_S₃'_fwd ⟨h_inj_S₂'_S₃', h_surj_S₂'_S₃'⟩

  exact (((f_S_S₀'.trans f_S₀'_S₁').trans f_S₁'_S₂').trans f_S₂'_S₃')


/-- The number of labelled graphs on `V` isomorphic to `G` (the size of its
isomorphism class). -/
noncomputable def isoGraphCount (G : SimpleGraph V) : ℕ
  := { G' : SimpleGraph V | Nonempty (G' ≃g G) }.toFinset.card


/-- The number of (labelled) simple graphs on `ℓ` vertices. -/
noncomputable def graphCount (ℓ : ℕ) : ℕ
  := (.univ : Set (SimpleGraph (Fin ℓ))).toFinset.card


lemma graphCount_gt_zero (ℓ : ℕ) : graphCount ℓ > 0
  := by
  simp [graphCount]
  exact NeZero.one_le


lemma graphCount_eq_sum_one (ℓ : ℕ) : graphCount ℓ = ∑ (_ : SimpleGraph (Fin ℓ)), 1
  := by
  simp [graphCount]

-- have ⟨h_G₁_G₃, h_G₂_G₃⟩ : G₁.verts ∩ G₃.verts = ∅ ∧ G₂.verts ∩ G₃.verts = ∅ :=
--     Set.union_empty_iff.mp h_G₁_G₂_G₃
-- have h_G₃_G₁' : G₃.verts ⊆ G₁.vertsᶜ := by
--   have := (Set.inter_subset G₁.verts G₃.verts ∅).mp (by simp [h_G₁_G₃])
--   rw [Set.union_empty] at this
--   apply Set.subset_compl_comm.mp this
-- have h_G₃_G₂' : G₃.verts ⊆ G₂.vertsᶜ := by
--   have := (Set.inter_subset G₂.verts G₃.verts ∅).mp (by simp [h_G₂_G₃])
--   rw [Set.union_empty] at this
--   apply Set.subset_compl_comm.mp this

lemma subset_compl_of_inter_empty {α : Type*} {s t : Set α} (h : s ∩ t = ∅) :
    s ⊆ tᶜ := fun e he ↦
  (Set.mem_compl_iff _ _).mpr fun ht ↦ (Set.ext_iff.mp h e).mp ⟨he, ht⟩

lemma subset_compl_of_inter_empty' {α : Type*} {s t : Set α} (h : s ∩ t = ∅) :
    t ⊆ sᶜ := fun e he ↦
  (Set.mem_compl_iff _ _).mpr fun ht ↦ (Set.ext_iff.mp h e).mp ⟨ht, he⟩

/-- Counting form of the chain rule: the pair count of `(H₁, H₂)` in `G`, scaled
by the number of ways to extend their union to an `ℓ₃`-set, equals the sum over
`ℓ₃`-vertex flags `F` of the `(H₁, H₂)`-pair count in `F` times the count of `F`
in `G`. -/
lemma subgraphPairCount_eq_sum_count_prods
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ)) (hℓ₃_lb : ℓ₁ + ℓ₂ ≤ ℓ₃)
    : subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
      =
      ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G
  := by
  let S₀ := (G_pair : subgraphPairSet H₁ H₂ G)
           × { G₃ : Subgraph G | G₃.IsInduced
                                  ∧ Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂)
                                  ∧ (G_pair.val.1.verts ∪ G_pair.val.2.verts) ∩ G₃.verts = ∅ }
  let S₁ := { (⟨⟨G₁,G₂⟩, _⟩, G₃) : subgraphPairSet H₁ H₂ G × Subgraph G
                | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ ∧ G₁.verts ∪ G₂.verts ⊆ G₃.verts }
  let S₂ := (F : QuotSimpleGraph (Fin ℓ₃)) × subgraphPairSet H₁ H₂ F.out × subgraphSet F.out G

  have fintypeSubgraphG : Fintype (Subgraph G) := subgraphFintype G

  let f_S₀_S₁_fwd : S₀ → S₁ := fun ⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃, _, h_G₃_card, h_G₁_G₂_G₃⟩ =>
    let G₃' := (⊤ : G.Subgraph).induce (G₁.verts ∪ G₂.verts ∪ G₃.verts)
    let h_G₃'_ind : G₃'.IsInduced := Subgraph.induce_top_isInduced G (G₁.verts ∪ G₂.verts ∪ G₃.verts)
    have h_G₃'_card : Fintype.card G₃'.verts = ℓ₃ := by
      calc
        Fintype.card G₃'.verts
        _ = ((G₁.verts ∪ G₂.verts).toFinset ∪ G₃.verts.toFinset).card := by
              rw [← Set.toFinset_card]
              simp only [G₃', Subgraph.induce_verts, Set.toFinset_union, union_assoc]
        _ = (G₁.verts ∪ G₂.verts).toFinset.card + G₃.verts.toFinset.card := by
              have : Disjoint (G₁.verts ∪ G₂.verts).toFinset G₃.verts.toFinset := by
                rw [Finset.disjoint_iff_inter_eq_empty, ←Set.toFinset_inter]
                exact Set.toFinset_eq_empty.mpr h_G₁_G₂_G₃
              exact Finset.card_union_of_disjoint this
        _ = (ℓ₁ + ℓ₂) + Fintype.card G₃.verts := by
              rw [subgraphPairSet_card_union_Finset h_G₁_G₂]
              simp only [Fintype.card_fin, Set.toFinset_card]
        _ = ℓ₃ := by
              rw [h_G₃_card]
              exact (Nat.add_sub_of_le hℓ₃_lb)
    have h_G₁_G₂_G₃' : G₁.verts ∪ G₂.verts ⊆ G₃'.verts := by
      simp only [Subgraph.induce_verts, Set.subset_union_left, G₃']
    ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃'⟩, h_G₃'_ind, h_G₃'_card, h_G₁_G₂_G₃'⟩

  have h_inj_S₀_S₁ : Function.Injective f_S₀_S₁_fwd := by
    intro ⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
      ⟨⟨⟨G₁', G₂'⟩, h_G₁'_G₂'⟩, G₃', h_G₃'_ind, h_G₃'_card, h_G₁'_G₂'_G₃'⟩
      h_eq
    simp [f_S₀_S₁_fwd] at h_eq
    obtain ⟨⟨rfl, rfl⟩, h_ind_ind'⟩ := h_eq
    congr
    apply h_G₃_ind.eq_of_verts_eq h_G₃'_ind
    calc
      G₃.verts
      _ = ((G₁.verts ∪ G₂.verts) ∪ G₃.verts) \ (G₁.verts ∪ G₂.verts) := by
              apply Eq.symm; apply Set.union_diff_cancel_left; simp only [h_G₁_G₂_G₃, subset_refl]
      _ = ((⊤ : G.Subgraph).induce (G₁.verts ∪ G₂.verts ∪ G₃.verts)).verts \ (G₁.verts ∪ G₂.verts) := by
              rw [Subgraph.induce_verts]
      _ = ((⊤ : G.Subgraph).induce (G₁.verts ∪ G₂.verts ∪ G₃'.verts)).verts \ (G₁.verts ∪ G₂.verts) := by
              rw [h_ind_ind']
      _ = ((G₁.verts ∪ G₂.verts) ∪ G₃'.verts) \ (G₁.verts ∪ G₂.verts) := by
              rw [Subgraph.induce_verts]
      _ = G₃'.verts := by
              apply Set.union_diff_cancel_left; simp only [h_G₁'_G₂'_G₃', subset_refl]

  have h_surj_S₀_S₁ : Function.Surjective f_S₀_S₁_fwd := by
    intro ⟨⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃⟩, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
    let G₃' := (⊤ : G.Subgraph).induce (G₃.verts \ (G₁.verts ∪ G₂.verts))
    have h_G₃'_ind : G₃'.IsInduced := Subgraph.induce_top_isInduced G (G₃.verts \ (G₁.verts ∪ G₂.verts))
    have h_G₃'_verts : G₃'.verts = G₃.verts \ (G₁.verts ∪ G₂.verts) := by
      simp only [Subgraph.induce_verts, G₃']
    have h_G₃'_card : Fintype.card G₃'.verts = ℓ₃ - (ℓ₁ + ℓ₂) :=
      calc
        Fintype.card G₃'.verts
        _ = Fintype.card ↑(G₃.verts \ (G₁.verts ∪ G₂.verts)) := by
              simp [h_G₃'_verts]
        _ = (G₃.verts \ (G₁.verts ∪ G₂.verts)).toFinset.card := by
              apply Eq.symm; apply Set.toFinset_card
        _ = (G₃.verts.toFinset \ (G₁.verts ∪ G₂.verts).toFinset).card := by
              simp
        _ = G₃.verts.toFinset.card - (G₁.verts ∪ G₂.verts).toFinset.card := by
              apply Finset.card_sdiff_of_subset
              exact Set.toFinset_subset_toFinset.mpr h_G₁_G₂_G₃
        _ = ℓ₃ - (ℓ₁ + ℓ₂) := by
              rw [subgraphPairSet_card_union_Finset h_G₁_G₂]
              rw [←h_G₃_card]
              simp only [Set.toFinset_card, Fintype.card_ofFinset, Fintype.card_fin]
    have h_G₁_G₂_G₃' : (G₁.verts ∪ G₂.verts) ∩ G₃'.verts = ∅ := by
      simp only [h_G₃'_verts, Set.inter_diff_self]
    use ⟨⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, G₃', h_G₃'_ind, h_G₃'_card, h_G₁_G₂_G₃'⟩
    simp [f_S₀_S₁_fwd]
    have : G₁.verts ∪ G₂.verts ∪ G₃'.verts = G₃.verts := by
      simp [h_G₃'_verts, h_G₁_G₂_G₃]
    rw [this, h_G₃_ind.induce_top_verts]

  let f_S₀_S₁ : S₀ ≃ S₁ := Equiv.ofBijective f_S₀_S₁_fwd ⟨h_inj_S₀_S₁, h_surj_S₀_S₁⟩
  have h_S₀_card_eq_S₁_card : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr f_S₀_S₁

  let f_S₁_S₂ : S₁ ≃ S₂ := subgraphPairSet_iso_union_quotSimpleGraphSet _ _ _
  have h_S₁_card_eq_S₂_card : Fintype.card S₁ = Fintype.card S₂ := Fintype.card_congr f_S₁_S₂

  have h_S₀_card : Fintype.card S₀ = subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
    :=
    let f : subgraphPairSet H₁ H₂ G → ℕ :=
      fun G_pair =>
        Fintype.card { G₃ : Subgraph G |
          G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂)
          ∧ (G_pair.val.1.verts ∪ G_pair.val.2.verts) ∩ G₃.verts = ∅ }
    let g : subgraphPairSet H₁ H₂ G → ℕ :=
      fun _ => (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
    have h : ∀ (G_pair : subgraphPairSet H₁ H₂ G), f G_pair = g G_pair := by
      simp only [Fintype.card_ofFinset, Set.coe_setOf, Subtype.forall, Prod.forall, f, g]
      intro G₁ G₂ h_G₁_G₂
      let S := { G₃ : Subgraph G | G₃.IsInduced ∧ Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂) ∧ (G₁.verts ∪ G₂.verts) ∩ G₃.verts = ∅ }
      let U := (G₁.verts ∪ G₂.verts)ᶜ
      have h_U_size : U.toFinset.card = ℓ - (ℓ₁ + ℓ₂) :=
        calc
          U.toFinset.card
          _ = (G₁.verts ∪ G₂.verts).toFinsetᶜ.card := by
                dsimp only [U]; rw [Set.toFinset_compl]
          _ = (Fintype.card (Fin ℓ)) - (G₁.verts ∪ G₂.verts).toFinset.card :=
                Finset.card_compl (G₁.verts ∪ G₂.verts).toFinset
          _ = ℓ - (ℓ₁ + ℓ₂):= by
                rw [subgraphPairSet_card_union_Finset h_G₁_G₂]
                simp only [Fintype.card_fin]
      let S' := powersetCard (ℓ₃ - (ℓ₁ + ℓ₂)) U.toFinset
      have h_iso_S_S' : S ≃ S' :=
        let f_S_S'_fwd : S → S' := fun ⟨G₃, _, h_G₃_card, h_G₁_G₂_G₃⟩ =>
          have h_G₃_verts_S' : G₃.verts.toFinset ∈ S' := by
            simp [S', U]
            rw [Set.union_inter_distrib_right G₁.verts G₂.verts G₃.verts] at h_G₁_G₂_G₃
            have ⟨h_G₁_G₃, h_G₂_G₃⟩ : G₁.verts ∩ G₃.verts = ∅ ∧ G₂.verts ∩ G₃.verts = ∅ :=
              Set.union_empty_iff.mp h_G₁_G₂_G₃
            have h_G₃_G₁' : G₃.verts ⊆ G₁.vertsᶜ := subset_compl_of_inter_empty' h_G₁_G₃
            have h_G₃_G₂' : G₃.verts ⊆ G₂.vertsᶜ := subset_compl_of_inter_empty' h_G₂_G₃
            refine ⟨⟨h_G₃_G₁', h_G₃_G₂'⟩, ?_⟩
            rw [←h_G₃_card]; simp only [Fintype.card_ofFinset]
          ⟨G₃.verts.toFinset, h_G₃_verts_S'⟩
        have h_S_S'_inj : Function.Injective f_S_S'_fwd := by
          intro ⟨G₃, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
            ⟨G₃', h_G₃'_ind, h_G₃'_card, h_G₁'_G₂'_G₃'⟩
            h_eq
          simp only [← Subtype.val_inj, Set.toFinset_inj, f_S_S'_fwd] at h_eq ⊢
          exact h_G₃_ind.eq_of_verts_eq h_G₃'_ind h_eq
        have h_S_S'_surj : Function.Surjective f_S_S'_fwd := by
          intro ⟨V₀, h₀⟩
          simp only [Set.compl_union, Set.toFinset_inter, Set.toFinset_compl, mem_powersetCard, S',
            U] at h₀
          let ⟨h_V₀_G₁_G₂, h_V₀_card⟩ := h₀
          let G₃ := (⊤ : G.Subgraph).induce V₀
          have h_G₃_ind : G₃.IsInduced := Subgraph.induce_top_isInduced G V₀
          have h_G₃_verts : G₃.verts = V₀ := by
            simp only [Subgraph.induce_verts, G₃]
          have h_G₃_card : Fintype.card G₃.verts = ℓ₃ - (ℓ₁ + ℓ₂) := by
            simp [h_G₃_verts, h_V₀_card]
          have h_G₁_G₂_G₃ : (G₁.verts ∪ G₂.verts) ∩ G₃.verts = ∅ := by
            simp only [h_G₃_verts]
            rw [←Finset.compl_union G₁.verts.toFinset G₂.verts.toFinset] at h_V₀_G₁_G₂
            apply Set.subset_empty_iff.mp
            calc
              (G₁.verts ∪ G₂.verts) ∩ ↑V₀
              _ ⊆ (G₁.verts ∪ G₂.verts) ∩ ↑((G₁.verts.toFinset ∪ G₂.verts.toFinset)ᶜ) :=
                    Set.inter_subset_inter_right _ h_V₀_G₁_G₂
              _ ⊆ (G₁.verts ∪ G₂.verts) ∩ (G₁.verts ∪ G₂.verts)ᶜ := by simp
              _ = ∅ := Set.inter_compl_self (G₁.verts ∪ G₂.verts)
          use ⟨G₃, h_G₃_ind, h_G₃_card, h_G₁_G₂_G₃⟩
          simp only [h_G₃_verts, toFinset_coe, f_S_S'_fwd]
        Equiv.ofBijective f_S_S'_fwd ⟨h_S_S'_inj, h_S_S'_surj⟩
      have h_S_card_eq_S'_card : Fintype.card S = Fintype.card S' := Fintype.card_congr h_iso_S_S'
      have h_S'_card_eq_choose : Fintype.card S' = (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) :=
        calc
          Fintype.card S'
          _ = S'.card := by simp only [Fintype.card_coe]
          _ = (powersetCard (ℓ₃ - (ℓ₁ + ℓ₂)) U.toFinset).card := rfl
          _ = U.toFinset.card.choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by apply card_powersetCard
          _ = (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by simp only [h_U_size]
      rw [←h_S'_card_eq_choose, ←h_S_card_eq_S'_card]
      dsimp only [Set.coe_setOf, S]
      simp only [Fintype.card_ofFinset]
    calc
      Fintype.card S₀
      _ = ∑ (G_pair : subgraphPairSet H₁ H₂ G), f G_pair := by simp only [S₀, f, Fintype.card_sigma]
      _ = ∑ (G_pair : subgraphPairSet H₁ H₂ G), g G_pair := by simp only [h]
      _ = ∑ (_ : subgraphPairSet H₁ H₂ G), (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by simp only [g]
      _ = subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂)) := by simp only [univ_eq_attach,
        sum_const, card_attach, smul_eq_mul, subgraphPairCount]
  have h_S₂_card : Fintype.card S₂ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G
    := by
    simp only [S₂, subgraphPairCount, subgraphCount, Fintype.card_sigma, Fintype.card_coe, Fintype.card_prod]

  rw [←h_S₀_card, ←h_S₂_card, h_S₀_card_eq_S₁_card, h_S₁_card_eq_S₂_card]


/-- Density form of the chain rule: the pair density of `(H₁, H₂)` in `G` equals
the sum over `ℓ₃`-vertex flags `F` of the `(H₁, H₂)`-pair density in `F` times
the density of `F` in `G`. -/
lemma subgraphPairDensity_eq_sum_density_prods
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ))
    (hℓ₃_lb : ℓ₁ + ℓ₂ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ ≤ ℓ)
    : subgraphPairDensity H₁ H₂ G
      =
      ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G
  :=
  let C : ℚ := (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))
  let h_C_gt_0 : C > 0 := by
    simp [C, Nat.choose_pos (Nat.sub_le_sub_right hℓ₃_ub (ℓ₁ + ℓ₂))]
  have h_C_self_div_eq_1 : C / C = 1 :=
    div_self (ne_of_gt h_C_gt_0)
  have h_C : (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C)
              = ((ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₃) : ℚ)
    :=
    calc
      ((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * ((ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))) := by
              simp [C]
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂ * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))) : ℚ) := by
              simp
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂ * ((ℓ - ℓ₁) - ℓ₂).choose ((ℓ₃ - ℓ₁) - ℓ₂)) : ℚ) := by
              have : ℓ - (ℓ₁ + ℓ₂) = (ℓ - ℓ₁) - ℓ₂ := Nat.sub_add_eq ℓ ℓ₁ ℓ₂
              rw [this]
              have : ℓ₃ - (ℓ₁ + ℓ₂) = (ℓ₃ - ℓ₁) - ℓ₂ := Nat.sub_add_eq ℓ₃ ℓ₁ ℓ₂
              rw [this]
      _ = (↑(ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose (ℓ₃ - ℓ₁) * (ℓ₃ - ℓ₁).choose ℓ₂) : ℚ) := by
              rw [mul_assoc, mul_assoc]
              have h₀ : (ℓ₃ - ℓ₁) ≤ (ℓ - ℓ₁) := by apply Nat.sub_le_sub_right hℓ₃_ub
              have h₁ : ℓ₂ ≤ ℓ₃ - ℓ₁ := Nat.le_sub_of_add_le' hℓ₃_lb
              rw [← Nat.choose_mul h₁]
      _ = (↑(ℓ.choose ℓ₃ * ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂) : ℚ) := by
              have h₀ : ℓ₃ ≤ ℓ := hℓ₃_ub
              have h₁ : ℓ₁ ≤ ℓ₃ := by omega
              rw [Nat.choose_mul h₁]
      _ = ((ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₃) : ℚ) := by
              simp only [mul_assoc, Nat.cast_mul, mul_comm]
  calc
    subgraphPairDensity H₁ H₂ G
    _ = ((subgraphPairCount H₁ H₂ G : ℚ) / (ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂)) * 1 := by
              simp [subgraphPairDensity]
    _ = ((subgraphPairCount H₁ H₂ G : ℚ) / (ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂)) * (C / C) := by
              simp [h_C_self_div_eq_1]
    _ = ((subgraphPairCount H₁ H₂ G : ℚ) * C) / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp [div_mul_div_comm (subgraphPairCount H₁ H₂ G : ℚ) ((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) C C]
    _ = (↑(subgraphPairCount H₁ H₂ G * (ℓ - (ℓ₁ + ℓ₂)).choose (ℓ₃ - (ℓ₁ + ℓ₂))) : ℚ)
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp [C]
    _ = ((∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ)
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              simp [subgraphPairCount_eq_sum_count_prods H₁ H₂ G hℓ₃_lb]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₃)), ((subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ))
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := rfl
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)),
          ((subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ)
          / (((ℓ.choose ℓ₁ * (ℓ - ℓ₁).choose ℓ₂) : ℚ) * C) := by
              apply sum_div
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)),
          ((subgraphPairCount H₁ H₂ F.out * subgraphCount F.out G) : ℚ)
          / ((ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₃) : ℚ) := by
              rw [h_C]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)),
          ((subgraphPairCount H₁ H₂ F.out : ℚ) / (ℓ₃.choose ℓ₁ * (ℓ₃ - ℓ₁).choose ℓ₂))
          * ((subgraphCount F.out G : ℚ) / ℓ.choose ℓ₃) := by
              simp only [div_mul_div_comm]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G := by
              simp [subgraphPairDensity, subgraphDensity]


lemma subgraphPairDensityLifted_eq_sum_density_prods
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (G : SimpleGraph (Fin ℓ))
    (hℓ₃_lb : ℓ₁ + ℓ₂ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ ≤ ℓ)
    : subgraphPairDensity H₁ H₂ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * quotSubgraphDensity F ⟦G⟧
  := by

  have h₀ : ∀ {F : QuotSimpleGraph (Fin ℓ₃)}, quotSubgraphDensity F ⟦G⟧ = subgraphDensityLifted F.out ⟦G⟧
    := by
    intro F
    calc
      quotSubgraphDensity F ⟦G⟧
      _ = Quot.lift subgraphDensityLifted ?h F ⟦G⟧ := rfl
      _ = Quot.lift subgraphDensityLifted ?h ⟦F.out⟧ ⟦G⟧ := by simp
      _ = subgraphDensityLifted F.out ⟦G⟧ := rfl
    intro F₀ F₁ h_eqv; ext G''; exact subgraphDensityLifted_respects_eqv F₀ F₁ h_eqv G''
  have h_RHS₀ : ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * quotSubgraphDensity F ⟦G⟧
                = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * subgraphDensityLifted F.out ⟦G⟧
    := by simp only [h₀]
  rw [h_RHS₀]

  have h₁ : ∀ {F : QuotSimpleGraph (Fin ℓ₃)}, subgraphDensityLifted F.out ⟦G⟧ = subgraphDensity F.out G
    := by
    intro F
    calc
      subgraphDensityLifted F.out ⟦G⟧
      _ = @Quot.lift _ graph_eqv _ (subgraphDensity F.out) ?h' ⟦G⟧ := rfl
      _ = subgraphDensity F.out G := rfl
    intro _ _ h_eqv; exact subgraphDensity_respects_eqv_on_G F.out h_eqv
  have h₂ : ∀ {F : QuotSimpleGraph (Fin ℓ₃)}, subgraphPairDensityLifted H₁ H₂ F = subgraphPairDensity H₁ H₂ F.out
    := by
    intro F
    calc
      subgraphPairDensityLifted H₁ H₂ F
      _ = Quot.lift (subgraphPairDensity H₁ H₂) ?h'' F := rfl
      _ = Quot.lift (subgraphPairDensity H₁ H₂) ?h'' ⟦F.out⟧ := by simp
      _ = subgraphPairDensity H₁ H₂ F.out := rfl
    intro F₀ F₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G H₁ H₂ h_eqv
  have h_RHS₁ : ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensityLifted H₁ H₂ F * subgraphDensityLifted F.out ⟦G⟧
                = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G
    := by simp only [h₂, h₁]
  rw [h_RHS₁]

  show subgraphPairDensity H₁ H₂ G
       = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), subgraphPairDensity H₁ H₂ F.out * subgraphDensity F.out G
  exact subgraphPairDensity_eq_sum_density_prods H₁ H₂ G hℓ₃_lb hℓ₃_ub


/-- Chain rule for the quotient-level pair density: expand `d(H₁, H₂; G)` as a
sum over `ℓ₃`-vertex flags. Exported as `density_chain_rule`. -/
theorem quotSubgraphPairDensity_eq_sum_density_prods
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₃ : ℕ} (hℓ₃_lb: ℓ₁ + ℓ₂ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ ≤ ℓ)
    : quotSubgraphPairDensity H₁ H₂ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphDensity F G
  := by
  rcases Quotient.exists_rep H₁ with ⟨H₁rep, hH₁rep⟩
  rcases Quotient.exists_rep H₂ with ⟨H₂rep, hH₂rep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hH₁rep, ← hH₂rep, ← hGrep]
  exact subgraphPairDensityLifted_eq_sum_density_prods H₁rep H₂rep Grep hℓ₃_lb hℓ₃_ub


/-- Chain rule for the ordinary quotient density: `d(H₁; G)` expands as a sum
over `ℓ₂`-vertex flags `F` of `d(H₁; F) · d(F; G)`. Exported as
`density_chain_rule'''`. -/
theorem quotSubgraphDensity_eq_sum_density_prods
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₂ : ℕ} (hℓ₂_lb: ℓ₁ ≤ ℓ₂) (hℓ₂_ub : ℓ₂ ≤ ℓ)
    : quotSubgraphDensity H₁ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphDensity H₁ F * quotSubgraphDensity F G
  := by
  let H₀ : QuotSimpleGraph (Fin 0) := ⟦emptyGraph (Fin 0)⟧
  let h_lb : 0 + ℓ₁ ≤ ℓ₂ := (zero_add ℓ₁).symm ▸ hℓ₂_lb

  have h_LHS : quotSubgraphPairDensity H₀ H₁ G = quotSubgraphDensity H₁ G :=
    quotSubgraphPairDensity_empty H₁ G
  rw [←h_LHS]

  have h : ∀ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphPairDensity H₀ H₁ F = quotSubgraphDensity H₁ F := by
    intro F
    rw [quotSubgraphPairDensity_empty H₁ F]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphDensity H₁ F * quotSubgraphDensity F G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₂)), quotSubgraphPairDensity H₀ H₁ F * quotSubgraphDensity F G := by
    simp only [h]
  rw [h_RHS]

  exact quotSubgraphPairDensity_eq_sum_density_prods H₀ H₁ G h_lb hℓ₂_ub


/- Hongseok: The following definition of the triple density is a hack which would let us proceed but which we should fix at some point. -/
/-- The density of three pairwise-disjoint labelled graphs `H₁, H₂, H₃` in `G`,
defined by averaging the pair densities over an intermediate `(ℓ₂+ℓ₃)`-vertex
flag. -/
noncomputable def quotSubgraphTripleDensity
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph W)
    : ℚ
  :=
  ∑ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G


/-- Triple density with an empty first slot degenerates to the pair density. -/
lemma quotSubgraphTripleDensity_empty
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (G : QuotSimpleGraph (Fin ℓ)) (hℓ : ℓ₁ + ℓ₂ ≤ ℓ)
    : quotSubgraphTripleDensity ⟦emptyGraph (Fin 0)⟧ H₁ H₂ G = quotSubgraphPairDensity H₁ H₂ G
  := by
  let H₀ : QuotSimpleGraph (Fin 0) := ⟦emptyGraph (Fin 0)⟧
  symm
  show quotSubgraphPairDensity H₁ H₂ G
        = ∑ F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity H₀ F G

  have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₀ F G = quotSubgraphDensity F G := by
    intro F
    rw [quotSubgraphPairDensity_empty F]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity H₀ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphDensity F G := by
    simp only [h]
  rw [h_RHS]

  exact quotSubgraphPairDensity_eq_sum_density_prods H₁ H₂ G (Nat.le_refl (ℓ₁ + ℓ₂)) hℓ


/-! ### Associativity of nested pair densities

The next three definitions (`..._step1`, `..._step2`, and their composite
`subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet`) build
the explicit bijection that proves the densities of three labelled graphs may be
nested in either order. `step1` recoordinates a `((H₁,H₂)-in-flag, H₃-in-G)`
configuration as five disjoint vertex blocks `X₁..X₅` of `G`; `step2` performs
the symmetric reverse recoordination for the `(H₂,H₃)`/`H₁` grouping.
-/

-- set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
noncomputable def subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet_step1
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    : { ⟨F, F₁, F₂, G₁, G₂, X⟩ :  (F : QuotSimpleGraph (Fin ℓ₁₂))
                                  × Subgraph F.out × Subgraph F.out
                                  × Subgraph G × Subgraph G
                                  × Finset (Fin ℓ₁₂)
                  | F₁.IsInduced
                  ∧ Nonempty (F₁.coe ≃g H₁)
                  ∧ F₂.IsInduced
                  ∧ Nonempty (F₂.coe ≃g H₂)
                  ∧ F₁.verts ∩ F₂.verts = ∅
                  ∧ G₁.IsInduced
                  ∧ Nonempty (G₁.coe ≃g F.out)
                  ∧ G₂.IsInduced
                  ∧ Nonempty (G₂.coe ≃g H₃)
                  ∧ G₁.verts ∩ G₂.verts = ∅
                  ∧ X.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ X ⊆ (F₁.verts ∪ F₂.verts)ᶜ.toFinset }
      ≃
      { ⟨X₁, X₂, X₃, X₄, X₅⟩ :  Finset (Fin ℓ) × Finset (Fin ℓ)
                                × Finset (Fin ℓ) × Finset (Fin ℓ) × Finset (Fin ℓ)
                  | X₁ ∩ X₂ = ∅
                  ∧ (X₁ ∪ X₂) ∩ X₃ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅
                  ∧ X₁.card = ℓ₁
                  ∧ X₂.card = ℓ₂
                  ∧ X₃.card = ℓ₃
                  ∧ X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃)
                  ∧ X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₁).coe ≃g H₁)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₂).coe ≃g H₂)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₃).coe ≃g H₃) }
  := by

  have h_ℓ_eq₁ : ℓ₁₂ - (ℓ₁ + ℓ₂ + (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega

  let S₁ := { ⟨F, F₁, F₂, G₁, G₂, X⟩ :  (F : QuotSimpleGraph (Fin ℓ₁₂))
                                      × Subgraph F.out × Subgraph F.out
                                      × Subgraph G × Subgraph G
                                      × Finset (Fin ℓ₁₂)
                  | F₁.IsInduced
                  ∧ Nonempty (F₁.coe ≃g H₁)
                  ∧ F₂.IsInduced
                  ∧ Nonempty (F₂.coe ≃g H₂)
                  ∧ F₁.verts ∩ F₂.verts = ∅
                  ∧ G₁.IsInduced
                  ∧ Nonempty (G₁.coe ≃g F.out)
                  ∧ G₂.IsInduced
                  ∧ Nonempty (G₂.coe ≃g H₃)
                  ∧ G₁.verts ∩ G₂.verts = ∅
                  ∧ X.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ X ⊆ (F₁.verts ∪ F₂.verts)ᶜ.toFinset }

  let S₂ := { ⟨X₁, X₂, X₃, X₄, X₅⟩ :  Finset (Fin ℓ) × Finset (Fin ℓ)
                                    × Finset (Fin ℓ) × Finset (Fin ℓ) × Finset (Fin ℓ)
                  | X₁ ∩ X₂ = ∅
                  ∧ (X₁ ∪ X₂) ∩ X₃ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅
                  ∧ X₁.card = ℓ₁
                  ∧ X₂.card = ℓ₂
                  ∧ X₃.card = ℓ₃
                  ∧ X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃)
                  ∧ X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₁).coe ≃g H₁)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₂).coe ≃g H₂)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₃).coe ≃g H₃) }

  let f_S₁_S₂_fwd : S₁ → S₂ := by
    intro ⟨⟨F, F₁, F₂, G₁, G₂, X⟩,
            h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂,
            h_X_card, h_X_F₁_F₂⟩

    let g_F₁_H₁ : F₁.coe ≃g H₁ := h_F₁_H₁.some
    let g_F₂_H₂ : F₂.coe ≃g H₂ := h_F₂_H₂.some

    let g_G₁_Fout : G₁.coe ≃g F.out := h_G₁_Fout.some
    let g_G₂_H₃ : G₂.coe ≃g H₃:= h_G₂_H₃.some

    let g_Fout_to_G : Fin ℓ₁₂ → Fin ℓ := Subtype.val ∘ g_G₁_Fout.symm

    let X₁ : Finset (Fin ℓ) := (g_Fout_to_G '' F₁.verts).toFinset
    let X₂ : Finset (Fin ℓ) := (g_Fout_to_G '' F₂.verts).toFinset
    let X₃ : Finset (Fin ℓ) := G₂.verts.toFinset
    let X₄ : Finset (Fin ℓ) := (g_Fout_to_G '' (F₁.verts ∪ F₂.verts ∪ X)ᶜ).toFinset
    let X₅ : Finset (Fin ℓ) := (g_Fout_to_G '' X).toFinset

    refine ⟨⟨X₁, X₂, X₃, X₄, X₅⟩, ?_⟩

    have h_Fpair_verts_disj_X : (F₁.verts ∪ F₂.verts) ∩ X ⊆ ∅ := by
      rw [←Finset.coe_empty]
      apply Set.toFinset_subset.mp
      calc
        ((F₁.verts ∪ F₂.verts) ∩ ↑↑X).toFinset
        _ ⊆ (F₁.verts ∪ F₂.verts).toFinset ∩ ↑X := by simp [Set.toFinset_inter]
        _ ⊆ (F₁.verts ∪ F₂.verts).toFinset ∩ (F₁.verts ∪ F₂.verts)ᶜ.toFinset :=
                Finset.inter_subset_inter_left h_X_F₁_F₂
        _ = (F₁.verts ∪ F₂.verts).toFinset ∩ (F₁.verts ∪ F₂.verts).toFinsetᶜ := by
                rw [Set.toFinset_compl]
        _ = ∅ := Finset.inter_compl (F₁.verts ∪ F₂.verts).toFinset


    have h_g_Fout_to_G_injective :=  Function.Injective.comp Subtype.val_injective g_G₁_Fout.symm.injective

    have h_image_g_Fout_to_G_subset_G₁_verts : ∀ (V : Set (Fin ℓ₁₂)), g_Fout_to_G '' V ⊆ G₁.verts := by
      intro V
      calc
        (Subtype.val ∘ g_G₁_Fout.symm) '' V
        _ = Subtype.val '' (g_G₁_Fout.symm '' V) := by simp only [Function.comp_apply, Set.image_image]
        _ ⊆ G₁.verts := by simp only [Set.image_subset_iff, Subtype.coe_preimage_self, Set.subset_univ]

    have h_induce_X₃ : (⊤ : G.Subgraph).induce X₃ = G₂ := by
      simp only [X₃, Set.coe_toFinset, h_G₂_ind.induce_top_verts]

    let g_X₁_H₁ : ((⊤ : G.Subgraph).induce X₁).coe ≃g H₁ := by
      have type_eq : X₁ = @Set.toFinset
                            (Fin ℓ)
                            (Subtype.val ∘ ⇑g_G₁_Fout.symm '' F₁.verts)
                            (@Set.fintypeImage
                              (Fin ℓ₁₂) (Fin ℓ)
                              (fun a b ↦ propDecidable (a = b))
                              F₁.verts
                              (Subtype.val ∘ ⇑g_G₁_Fout.symm)
                              (Subtype.fintype (Membership.mem F₁.verts)))
        := by
        congr!
      rw [type_eq]
      exact isoFromInducedSubgraphByPartialIso g_G₁_Fout g_F₁_H₁ h_F₁_ind h_G₁_ind

    let g_X₂_H₂ : ((⊤ : G.Subgraph).induce X₂).coe ≃g H₂ := by
      have type_eq : X₂ = @Set.toFinset
                            (Fin ℓ)
                            (Subtype.val ∘ ⇑g_G₁_Fout.symm '' F₂.verts)
                            (@Set.fintypeImage
                              (Fin ℓ₁₂) (Fin ℓ)
                              (fun a b ↦ propDecidable (a = b))
                              F₂.verts
                              (Subtype.val ∘ ⇑g_G₁_Fout.symm)
                              (Subtype.fintype (Membership.mem F₂.verts)))
        := by
        congr!
      rw [type_eq]
      exact isoFromInducedSubgraphByPartialIso g_G₁_Fout g_F₂_H₂ h_F₂_ind h_G₁_ind

    let g_X₃_H₃ : ((⊤ : G.Subgraph).induce X₃).coe ≃g H₃ := by
      rw [h_induce_X₃]; exact g_G₂_H₃


    have h_X₁_X₂_included_in_G₁_verts : X₁ ∪ X₂ ⊆ G₁.verts.toFinset := by
      rw [←Set.toFinset_union (g_Fout_to_G '' F₁.verts) (g_Fout_to_G '' F₂.verts)]
      apply Set.toFinset_mono
      rw [←Set.image_union g_Fout_to_G F₁.verts F₂.verts]
      exact h_image_g_Fout_to_G_subset_G₁_verts (F₁.verts ∪ F₂.verts)
    have h_X₄_included_in_G₁_verts : X₄ ⊆ G₁.verts.toFinset := by
      apply Set.toFinset_mono
      exact h_image_g_Fout_to_G_subset_G₁_verts (F₁.verts ∪ F₂.verts ∪ X)ᶜ
    have h_X₅_included_in_G₁_verts : X₅ ⊆ G₁.verts.toFinset := by
      apply Set.toFinset_mono
      exact h_image_g_Fout_to_G_subset_G₁_verts X

    have h_X₁_X₂_disj : X₁ ∩ X₂ = ∅ := by
      rw [←Set.toFinset_inter (g_Fout_to_G '' F₁.verts) (g_Fout_to_G '' F₂.verts)]
      apply Set.toFinset_eq_empty.mpr
      apply Set.subset_empty_iff.mp
      rw [←Set.image_inter h_g_Fout_to_G_injective]
      simp [h_F₁_disj_F₂]
    have h_X₁_X₂_X₃_disj : (X₁ ∪ X₂) ∩ X₃ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        (X₁ ∪ X₂) ∩ X₃ ⊆ G₁.verts.toFinset ∩ G₂.verts.toFinset :=
                Finset.inter_subset_inter h_X₁_X₂_included_in_G₁_verts (subset_refl X₃)
        _ = (G₁.verts ∩ G₂.verts).toFinset := by simp only [Eq.symm, Set.toFinset_inter]
        _ = ∅ := by simp only [h_G₁_disj_G₂, Set.toFinset_empty]
    have h_X₁_union_X₂_disj_X₄ : (X₁ ∪ X₂) ∩ X₄ = ∅ := by
      rw [←Set.toFinset_union (g_Fout_to_G '' F₁.verts) (g_Fout_to_G '' F₂.verts),
          ←Set.toFinset_inter
            ((g_Fout_to_G '' F₁.verts) ∪ (g_Fout_to_G '' F₂.verts))
            (g_Fout_to_G '' (F₁.verts ∪ F₂.verts ∪ X)ᶜ)]
      apply Set.toFinset_eq_empty.mpr
      rw [←Set.image_union g_Fout_to_G F₁.verts F₂.verts,
          ←Set.image_inter h_g_Fout_to_G_injective]
      apply Set.image_eq_empty.mpr
      apply Set.subset_empty_iff.mp
      apply (Set.inter_subset (F₁.verts ∪ F₂.verts) (F₁.verts ∪ F₂.verts ∪ X)ᶜ ∅).mpr
      calc
        (F₁.verts ∪ F₂.verts) ⊆ (F₁.verts ∪ F₂.verts ∪ X) := Set.subset_union_left
        _ = (F₁.verts ∪ F₂.verts ∪ X)ᶜᶜ := Eq.symm (compl_compl (F₁.verts ∪ F₂.verts ∪ X))
        _ = (F₁.verts ∪ F₂.verts ∪ X)ᶜᶜ ∪ ∅ := Eq.symm (Set.union_empty (F₁.verts ∪ F₂.verts ∪ X)ᶜᶜ)
    have h_X₃_disj_X₄ : X₃ ∩ X₄ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₃ ∩ X₄ ⊆ G₂.verts.toFinset ∩ G₁.verts.toFinset :=
                Finset.inter_subset_inter (subset_refl X₃) h_X₄_included_in_G₁_verts
        _ = (G₁.verts ∩ G₂.verts).toFinset := by simp only [Eq.symm, Set.toFinset_inter, Finset.inter_comm]
        _ = ∅ := by simp only [h_G₁_disj_G₂, Set.toFinset_empty]
    have h_X₁_X₂_X₃_X₄_disj : (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅ := by
      suffices (X₁ ∪ X₂) ∩ X₄ = ∅ ∧ X₃ ∩ X₄ = ∅ by {
        rw [Finset.union_inter_distrib_right (X₁ ∪ X₂) X₃ X₄]
        exact Finset.union_eq_empty.mpr this
      }
      exact ⟨h_X₁_union_X₂_disj_X₄, h_X₃_disj_X₄⟩
    have h_X₁_union_X₂_disj_X₅ : (X₁ ∪ X₂) ∩ X₅ = ∅ := by
      rw [←Set.toFinset_union (g_Fout_to_G '' F₁.verts) (g_Fout_to_G '' F₂.verts),
          ←Set.toFinset_inter
            ((g_Fout_to_G '' F₁.verts) ∪ (g_Fout_to_G '' F₂.verts))
            (g_Fout_to_G '' X)]
      apply Set.toFinset_eq_empty.mpr
      rw [←Set.image_union g_Fout_to_G F₁.verts F₂.verts,
          ←Set.image_inter h_g_Fout_to_G_injective]
      apply Set.image_eq_empty.mpr
      apply Set.subset_empty_iff.mp
      exact h_Fpair_verts_disj_X
    have h_X₃_disj_X₅ : X₃ ∩ X₅ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₃ ∩ X₅ ⊆ G₂.verts.toFinset ∩ G₁.verts.toFinset :=
                Finset.inter_subset_inter (subset_refl X₃) h_X₅_included_in_G₁_verts
        _ = (G₁.verts ∩ G₂.verts).toFinset := by simp only [Eq.symm, Set.toFinset_inter, Finset.inter_comm]
        _ = ∅ := by simp only [h_G₁_disj_G₂, Set.toFinset_empty]
    have h_X₄_disj_X₅ : X₄ ∩ X₅ = ∅ := by
      rw [←Set.toFinset_inter
            (g_Fout_to_G '' (F₁.verts ∪ F₂.verts ∪ X)ᶜ)
            (g_Fout_to_G '' X)]
      apply Set.toFinset_eq_empty.mpr
      rw [←Set.image_inter h_g_Fout_to_G_injective]
      apply Set.image_eq_empty.mpr
      apply Set.subset_empty_iff.mp
      rw [Set.inter_comm]
      apply (Set.inter_subset X (F₁.verts ∪ F₂.verts ∪ X)ᶜ ∅).mpr
      rw [Set.union_empty, compl_compl]
      simp only [Set.subset_union_right]
    have h_X₁_X₂_X₃_X₄_X₅_disj : (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅ := by
      suffices (X₁ ∪ X₂) ∩ X₅ = ∅ ∧ X₃ ∩ X₅ = ∅ ∧ X₄ ∩ X₅ = ∅ by {
        rw [Finset.union_inter_distrib_right (X₁ ∪ X₂ ∪ X₃) X₄ X₅]
        rw [Finset.union_inter_distrib_right (X₁ ∪ X₂) X₃ X₅]
        simp only [Finset.union_eq_empty, this, and_self]
      }
      exact ⟨h_X₁_union_X₂_disj_X₅, h_X₃_disj_X₅, h_X₄_disj_X₅⟩

    have h_X₁_card : X₁.card = ℓ₁ := by
      simp only [← subgraph_verts_card_from_iso_graph g_X₁_H₁, Subgraph.induce_verts, coe_sort_coe, Fintype.card_coe]
    have h_X₂_card : X₂.card = ℓ₂ := by
      simp only [← subgraph_verts_card_from_iso_graph g_X₂_H₂, Subgraph.induce_verts, coe_sort_coe, Fintype.card_coe]
    have h_X₃_card : X₃.card = ℓ₃ := by
      simp only [← subgraph_verts_card_from_iso_graph g_X₃_H₃, Subgraph.induce_verts, coe_sort_coe, Fintype.card_coe]
    have h_X₄_card : X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃) :=
      calc
        X₄.card
        _  = Fintype.card (g_Fout_to_G '' (F₁.verts ∪ F₂.verts ∪ X)ᶜ) := by
              simp only [Set.toFinset_image, Set.compl_union,
                          Set.toFinset_inter, Set.toFinset_compl, toFinset_coe,
                          inter_assoc, Fintype.card_ofFinset, X₄]
        _ = Fintype.card ↑(F₁.verts ∪ F₂.verts ∪ X)ᶜ :=
              Set.card_image_of_injective (F₁.verts ∪ F₂.verts ∪ X)ᶜ h_g_Fout_to_G_injective
        _ = (F₁.verts ∪ F₂.verts ∪ X)ᶜ.toFinset.card := by
              apply Eq.symm
              apply Set.toFinset_card
        _ = (F₁.verts ∪ F₂.verts ∪ X).toFinsetᶜ.card := by
              simp only [Set.toFinset_compl]
        _ = Fintype.card ↑(Fin ℓ₁₂) - (F₁.verts ∪ F₂.verts ∪ X).toFinset.card := by
              rw [card_compl]
        _ = ℓ₁₂ - (F₁.verts ∪ F₂.verts ∪ X).toFinset.card := by
              simp only [Fintype.card_fin]
        _ = ℓ₁₂ - (F₁.verts.toFinset ∪ F₂.verts.toFinset ∪ X).card := by
              simp only [Set.toFinset_union, toFinset_coe]
        _ = ℓ₁₂ - (Fintype.card F₁.verts + Fintype.card F₂.verts + Fintype.card X) := by
            rw [Finset.card_union (F₁.verts.toFinset ∪ F₂.verts.toFinset) X]
            rw [Finset.card_union F₁.verts.toFinset F₂.verts.toFinset]
            have : (F₁.verts.toFinset ∪ F₂.verts.toFinset) ∩ X = ∅ := by
              have h_Fpair_X_disj : X ⊆ (F₁.verts.toFinset ∪ F₂.verts.toFinset)ᶜ := by
                rw [←Set.toFinset_union F₁.verts F₂.verts]
                rw [←Set.toFinset_compl (F₁.verts ∪ F₂.verts)]
                exact h_X_F₁_F₂
              apply Finset.subset_empty.mp
              calc
                (F₁.verts.toFinset ∪ F₂.verts.toFinset) ∩ X
                _ ⊆ (F₁.verts.toFinset ∪ F₂.verts.toFinset)
                    ∩ (F₁.verts.toFinset ∪ F₂.verts.toFinset)ᶜ :=
                  inter_subset_inter (subset_refl (F₁.verts.toFinset ∪ F₂.verts.toFinset)) h_Fpair_X_disj
                _ = ∅ :=
                  Finset.inter_compl (F₁.verts.toFinset ∪ F₂.verts.toFinset)
            simp only [this, card_empty, tsub_zero]
            have : F₁.verts.toFinset ∩ F₂.verts.toFinset = ∅ := by
              rw [←Set.toFinset_inter F₁.verts F₂.verts]
              simp only [h_F₁_disj_F₂, Set.toFinset_empty]
            simp only [this, card_empty, tsub_zero]
            simp only [Set.toFinset_card, Fintype.card_ofFinset, Fintype.card_coe]
        _ = ℓ₁₂ - (ℓ₁ + ℓ₂ + (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) := by
              rw [Iso.card_eq g_F₁_H₁, Iso.card_eq g_F₂_H₂]
              simp only [Fintype.card_fin, Fintype.card_coe]
              simp only [h_X_card]
        _ = ℓ₂₃ - (ℓ₂ + ℓ₃) := h_ℓ_eq₁
    have h_X₅_card : X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃) :=
      calc
        X₅.card = Fintype.card (g_Fout_to_G '' X) := by simp only [Set.toFinset_image, toFinset_coe, Fintype.card_ofFinset, X₅]
        _ = Fintype.card X := Set.card_image_of_injective X h_g_Fout_to_G_injective
        _ = ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by simp only [Fintype.card_coe, h_X_card]
    exact  ⟨h_X₁_X₂_disj, h_X₁_X₂_X₃_disj, h_X₁_X₂_X₃_X₄_disj, h_X₁_X₂_X₃_X₄_X₅_disj,
            h_X₁_card, h_X₂_card, h_X₃_card, h_X₄_card, h_X₅_card,
            Nonempty.intro g_X₁_H₁, Nonempty.intro g_X₂_H₂, Nonempty.intro g_X₃_H₃⟩

  have h_f_S₁_S₂_inj : Function.Injective f_S₁_S₂_fwd := by
    intro ⟨⟨F, F₁, F₂, G₁, G₂, X⟩,
            h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂,
            h_X_card, h_X_F₁_F₂⟩
      ⟨⟨F', F₁', F₂', G₁', G₂', X'⟩,
            h_F₁'_ind, h_F₁'_H₁, h_F₂'_ind, h_F₂'_H₂, h_F₁'_disj_F₂',
            h_G₁'_ind, h_G₁'_Fout', h_G₂'_ind, h_G₂'_H₃, h_G₁'_disj_G₂',
            h_X'_card, h_X'_F₁'_F₂'⟩
      h_eq
    simp [f_S₁_S₂_fwd] at h_eq
    obtain ⟨h_X₁_eq_X₁', h_X₂_eq_X₂', h_X₃_eq_X₃', h_X₄_eq_X₄', h_X₅_eq_X₅'⟩ := h_eq
    simp only [Subtype.mk.injEq, Sigma.mk.inj_iff]

    have h_G₁_eq_G₁' : G₁ = G₁' := by
      apply h_G₁_ind.eq_of_verts_eq h_G₁'_ind
      calc
        G₁.verts
        _ = Subtype.val '' (⇑h_G₁_Fout.some.symm '' (univ : Finset (Fin ℓ₁₂))) := by
                have : ⇑h_G₁_Fout.some.symm '' (Set.univ : Set (Fin ℓ₁₂))
                        = (Set.univ : Set (G₁.verts))
                  := Set.image_univ_of_surjective h_G₁_Fout.some.symm.surjective
                simp only [this, coe_univ, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
        _ = (Subtype.val ∘ ⇑h_G₁_Fout.some.symm) '' (univ : Finset (Fin ℓ₁₂)) := by
                simp only [Function.comp_apply, Set.image_image]
        _ = (Subtype.val ∘ h_G₁_Fout.some.symm) '' ((F₁.verts.toFinset ∪ F₂.verts.toFinset ∪ X)
                                                    ∪ (F₁.verts.toFinset ∪ F₂.verts.toFinset ∪ X)ᶜ) := by
                simp only [coe_univ, Set.image_univ, Set.coe_toFinset, Set.union_compl_self]
        _ = (Subtype.val ∘ h_G₁_Fout.some.symm) '' (F₁.verts.toFinset ∪ F₂.verts.toFinset ∪ X
                                                    ∪ (F₁.verts.toFinsetᶜ ∩ F₂.verts.toFinsetᶜ ∩ Xᶜ)) := by
                simp only [Set.coe_toFinset, Set.compl_union]
        _ = (Subtype.val ∘ h_G₁_Fout.some.symm) '' (F₁.verts.toFinset ∪ F₂.verts.toFinset ∪ X
                                                    ∪ (F₁.verts.toFinsetᶜ ∩ (F₂.verts.toFinsetᶜ ∩ Xᶜ))) := by
                simp only [Function.comp_apply, Set.coe_toFinset, Set.inter_assoc]
        _ = ((Subtype.val ∘ h_G₁_Fout.some.symm) '' F₁.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁_Fout.some.symm) '' F₂.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁_Fout.some.symm) '' X)
              ∪ ((Subtype.val ∘ h_G₁_Fout.some.symm) '' (F₁.verts.toFinsetᶜ ∩ (F₂.verts.toFinsetᶜ ∩ Xᶜ))) := by
                simp only [Set.image_union (Subtype.val ∘ h_G₁_Fout.some.symm)]
        _ = SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) F₁.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) F₂.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) X)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) (F₁.verts.toFinsetᶜ ∩ (F₂.verts.toFinsetᶜ ∩ Xᶜ))) := by
                simp only [Function.comp_apply, Set.coe_toFinset, coe_image, coe_inter, coe_compl]
        _ = SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) F₁'.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) F₂'.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) X')
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) (F₁'.verts.toFinsetᶜ ∩ (F₂'.verts.toFinsetᶜ ∩ X'ᶜ))) := by
                rw [h_X₁_eq_X₁', h_X₂_eq_X₂', h_X₄_eq_X₄', h_X₅_eq_X₅']
        _ = ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' F₁'.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' F₂'.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X')
              ∪ ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (F₁'.verts.toFinsetᶜ ∩ (F₂'.verts.toFinsetᶜ ∩ X'ᶜ))) := by
                simp only [Function.comp_apply, Set.coe_toFinset, coe_image, coe_inter, coe_compl]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (F₁'.verts.toFinset ∪ F₂'.verts.toFinset ∪ X'
                                                      ∪ (F₁'.verts.toFinsetᶜ ∩ (F₂'.verts.toFinsetᶜ ∩ X'ᶜ))) := by
                simp only [Set.image_union (Subtype.val ∘ h_G₁'_Fout'.some.symm)]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (F₁'.verts.toFinset ∪ F₂'.verts.toFinset ∪ X'
                                                      ∪ (F₁'.verts.toFinsetᶜ ∩ F₂'.verts.toFinsetᶜ ∩ X'ᶜ)) := by
                simp only [Function.comp_apply, Set.coe_toFinset, Set.inter_assoc]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' ((F₁'.verts.toFinset ∪ F₂'.verts.toFinset ∪ X')
                                                      ∪ (F₁'.verts.toFinset ∪ F₂'.verts.toFinset ∪ X')ᶜ) := by
                simp only [Set.coe_toFinset, Set.compl_union]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (univ : Finset (Fin ℓ₁₂)) := by
                simp only [coe_univ, Set.image_univ, Set.coe_toFinset, Set.union_compl_self]
        _ = h_G₁'_Fout'.some.symm '' (univ : Finset (Fin ℓ₁₂)) := by
                simp only [Function.comp_apply, Set.image_image]
        _ = G₁'.verts := by
                have : ⇑h_G₁'_Fout'.some.symm '' (Set.univ : Set (Fin ℓ₁₂))
                        = (Set.univ : Set (G₁'.verts))
                  := Set.image_univ_of_surjective h_G₁'_Fout'.some.symm.surjective
                simp only [this, coe_univ, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
    subst h_G₁_eq_G₁'

    have h_F_eq_F' : F = F' :=
      calc
        F = ⟦F.out⟧ := Eq.symm (Quotient.out_eq F)
        _ = ⟦F'.out⟧ := Quotient.sound (Nonempty.intro (h_G₁_Fout.some.symm.trans h_G₁'_Fout'.some))
        _ = F' := Quotient.out_eq F'
    subst h_F_eq_F'
    simp only [heq_eq_eq, Prod.mk.injEq, true_and]

    have h_G₂_eq_G₂' : G₂ = G₂' := h_G₂_ind.eq_of_verts_eq h_G₂'_ind h_X₃_eq_X₃'
    subst h_G₂_eq_G₂'

    have h_source_eq_from_target_eq :
        ∀ {X₀ X₀' : Finset (Fin ℓ₁₂)},
          image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) X₀ = image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) X₀'
          → X₀ = X₀'
      := by
      intro X₀ X₀' h_X₀_eq_X₀'
      have : (Subtype.val ∘ h_G₁_Fout.some.symm) '' X₀ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀' := by
        calc
          (Subtype.val ∘ h_G₁_Fout.some.symm) '' X₀ = SetLike.coe (image (fun a ↦ ↑(h_G₁_Fout.some.symm a)) X₀) := by
                simp only [Function.comp_apply, coe_image]
          _ = SetLike.coe (image (fun a ↦ ↑(h_G₁'_Fout'.some.symm a)) X₀') := by
                simp only [h_X₀_eq_X₀', coe_image]
          _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀' := by
                simp only [coe_image, Function.comp_apply]
      calc
        X₀ = ((Subtype.val ∘ h_G₁_Fout.some.symm)⁻¹' ((Subtype.val ∘ h_G₁_Fout.some.symm) '' X₀)).toFinset := by
              have : Function.Injective (Subtype.val ∘ h_G₁_Fout.some.symm) :=
                Function.Injective.comp Subtype.val_injective h_G₁_Fout.some.symm.injective
              rw [Function.Injective.preimage_image this X₀]
              simp only [toFinset_coe]
        _ = ((Subtype.val ∘ h_G₁_Fout.some.symm)⁻¹' ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀')).toFinset := by
              rw [this]
        _ = ((Subtype.val ∘ h_G₁'_Fout'.some.symm)⁻¹' ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀')).toFinset := by
              rfl
        _ = X₀' := by
              have : Function.Injective (Subtype.val ∘ h_G₁'_Fout'.some.symm) :=
                Function.Injective.comp Subtype.val_injective h_G₁'_Fout'.some.symm.injective
              rw [Function.Injective.preimage_image this X₀']
              simp only [toFinset_coe]

    have h_ind_subgraph_eq_from_vert_eq :
        ∀ {F₀ F₀' : Subgraph F.out},
          F₀.IsInduced
          → F₀'.IsInduced
          → (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) F₀.verts.toFinset)
            = (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) F₀'.verts.toFinset)
          → F₀ = F₀'
      := by
      intro F₀ F₀' h_F₀_ind h_F₀'_ind h_vert_eq
      apply h_F₀_ind.eq_of_verts_eq h_F₀'_ind
      calc
        F₀.verts = F₀.verts.toFinset := by simp only [Set.coe_toFinset]
        _ = F₀'.verts.toFinset := by rw [h_source_eq_from_target_eq h_vert_eq]
        _ = F₀'.verts := by simp only [Set.coe_toFinset]

    have h_F₁_eq_F₁' : F₁ = F₁' := h_ind_subgraph_eq_from_vert_eq h_F₁_ind h_F₁'_ind h_X₁_eq_X₁'
    subst h_F₁_eq_F₁'

    have h_F₂_eq_F₂' : F₂ = F₂' := h_ind_subgraph_eq_from_vert_eq h_F₂_ind h_F₂'_ind h_X₂_eq_X₂'
    subst h_F₂_eq_F₂'
    simp only [true_and]

    show X = X'
    exact h_source_eq_from_target_eq h_X₅_eq_X₅'

  have h_f_S₁_S₂_surj : Function.Surjective f_S₁_S₂_fwd := by
    intro ⟨⟨X₁, X₂, X₃, X₄, X₅⟩,
            h_X₁_disj_X₂, h_X₁_to_X₂_disj_X₃, h_X₁_to_X₃_disj_X₄, h_X₁_to_X₄_disj_X₅,
            h_X₁_card, h_X₂_card, h_X₃_card, h_X₄_card, h_X₅_card,
            h_X₁_H₁, h_X₂_H₂, h_X₃_H₃⟩

    have h_X₁_X₂_disj_X₄ : (X₁ ∪ X₂) ∩ X₄ = ∅ := by
      suffices (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅ by {
        have h' : X₁ ∪ X₂ ⊆ X₁ ∪ X₂ ∪ X₃ := Finset.subset_union_left
        apply Finset.subset_empty.mp
        calc
          (X₁ ∪ X₂) ∩ X₄ ⊆ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ := Finset.inter_subset_inter_right h'
          _ = ∅ := this
      }
      exact h_X₁_to_X₃_disj_X₄
    have h_X₁_X₂_X₄_disj_X₅ : (X₁ ∪ X₂ ∪ X₄) ∩ X₅ = ∅ := by
      suffices (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅ by {
        have h' : X₁ ∪ X₂ ∪ X₄ ⊆ X₁ ∪ X₂ ∪ X₃ ∪ X₄ :=
          calc
            X₁ ∪ X₂ ∪ X₄ ⊆ X₁ ∪ X₂ ∪ X₄ ∪ X₃ := Finset.subset_union_left
            _ = (X₁ ∪ X₂) ∪ (X₄ ∪ X₃) := Finset.union_assoc _ _ _
            _ = (X₁ ∪ X₂) ∪ (X₃ ∪ X₄) := by nth_rw 3 [Finset.union_comm]
            _ = X₁ ∪ X₂ ∪ X₃ ∪ X₄ := (Finset.union_assoc _ _ _).symm
        apply Finset.subset_empty.mp
        calc
          (X₁ ∪ X₂ ∪ X₄) ∩ X₅ ⊆ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ := Finset.inter_subset_inter_right h'
          _ = ∅ := this
        }
      exact h_X₁_to_X₄_disj_X₅
    have h_X₁_disj_X₅ : X₁ ∩ X₅ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₁ ∩ X₅ ⊆ (X₁ ∪ (X₂ ∪ X₄)) ∩ X₅ := Finset.inter_subset_inter_right (by simp only [Finset.subset_union_left])
        _ = (X₁ ∪ X₂ ∪ X₄) ∩ X₅ := by simp only [Finset.union_assoc]
        _ = ∅ := h_X₁_X₂_X₄_disj_X₅
    have h_X₂_disj_X₅ : X₂ ∩ X₅ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₂ ∩ X₅ ⊆ (X₂ ∪ (X₁ ∪ X₄)) ∩ X₅ := Finset.inter_subset_inter_right (by simp only [Finset.subset_union_left])
        _ = (X₁ ∪ X₂ ∪ X₄) ∩ X₅ := by rw [←Finset.union_assoc X₂ X₁ X₄, Finset.union_comm X₂ X₁]
        _ = ∅ := h_X₁_X₂_X₄_disj_X₅
    have h_X₁_X₂_X₄_X₅_disj_X₃ : (X₁ ∪ X₂ ∪ X₄ ∪ X₅) ∩ X₃ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        (X₁ ∪ X₂ ∪ X₄ ∪ X₅) ∩ X₃
        _ = ((X₁ ∪ X₂) ∩ X₃) ∪ (X₄ ∩ X₃) ∪ (X₅ ∩ X₃) := by simp only [union_assoc, union_inter_distrib_right]
        _ = ((X₁ ∪ X₂) ∩ X₃) ∪ (X₃ ∩ X₄) ∪ (X₃ ∩ X₅) := by simp only [Finset.inter_comm]
        _ ⊆ ((X₁ ∪ X₂) ∩ X₃) ∪ ((X₁ ∪ X₂ ∪ X₃) ∩ X₄) ∪ (X₃ ∩ X₅) := by
                apply Finset.union_subset_union_left
                apply Finset.union_subset_union_right
                apply Finset.inter_subset_inter_right
                apply Finset.subset_union_right
        _ ⊆ ((X₁ ∪ X₂) ∩ X₃) ∪ ((X₁ ∪ X₂ ∪ X₃) ∩ X₄) ∪ ((X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅) := by
                apply Finset.union_subset_union_right
                apply Finset.inter_subset_inter_right
                rw [Finset.union_assoc (X₁ ∪ X₂) X₃ X₄]
                rw [Finset.union_comm X₃ X₄]
                rw [←Finset.union_assoc (X₁ ∪ X₂) X₄ X₃]
                apply Finset.subset_union_right
        _ = (∅ ∪ ∅ ∪ ∅) := by rw [h_X₁_to_X₂_disj_X₃, h_X₁_to_X₃_disj_X₄, h_X₁_to_X₄_disj_X₅]
        _ = ∅ := by simp only [union_idempotent]

    let X_F := X₁ ∪ X₂ ∪ X₄ ∪ X₅
    have h_X_F_disj_X₃ : X_F ∩ X₃ = ∅ := h_X₁_X₂_X₄_X₅_disj_X₃
    have h_X₁_subset_X_F : X₁ ⊆ X_F := by
      dsimp only [X_F]
      rw [Finset.union_assoc (X₁ ∪ X₂) X₄ X₅]
      rw [Finset.union_assoc X₁ X₂ (X₄ ∪ X₅)]
      apply Finset.subset_union_left
    have h_X₂_subset_X_F : X₂ ⊆ X_F := by
      dsimp only [X_F]
      rw [Finset.union_comm X₁ X₂]
      rw [Finset.union_assoc (X₂ ∪ X₁) X₄ X₅]
      rw [Finset.union_assoc X₂ X₁ (X₄ ∪ X₅)]
      apply Finset.subset_union_left
    have h_X₅_subset_X_F : X₅ ⊆ X_F := by
      dsimp only [X_F]
      apply Finset.subset_union_right

    let G₁ := (⊤ : G.Subgraph).induce X_F
    let G₂ := (⊤ : G.Subgraph).induce X₃
    let h_G₁_ind : G₁.IsInduced := Subgraph.induce_top_isInduced G X_F
    let h_G₂_ind : G₂.IsInduced := Subgraph.induce_top_isInduced G X₃
    have h_G₂_H₃ : Nonempty (G₂.coe ≃g H₃) := h_X₃_H₃

    have h_G₁_disj_G₂ : G₁.verts ∩ G₂.verts = ∅ := by
      apply Set.subset_empty_iff.mp
      calc
        G₁.verts ∩ G₂.verts = ↑X_F ∩ ↑X₃ := by rw [Subgraph.induce_verts, Subgraph.induce_verts]
        _ = ↑(X_F ∩ X₃) := by simp only [coe_inter]
        _ ⊆ ∅ := by simp only [h_X_F_disj_X₃, coe_empty, subset_refl]
    have h_G₁_verts_eq_X₁_X₂_X₄_X₅ : G₁.verts = X₁ ∪ X₂ ∪ X₄ ∪ X₅ :=
      Subgraph.induce_verts _ _
    have h_G₂_verts_eq_X₃ : G₂.verts = X₃ :=
      Subgraph.induce_verts _ _
    have h_X₁_subset_G₁_verts : X₁ ⊆ G₁.verts.toFinset := by
      dsimp only [G₁]
      rw [h_G₁_verts_eq_X₁_X₂_X₄_X₅]
      simp only [Finset.toFinset_coe]
      exact h_X₁_subset_X_F
    have h_X₂_subset_G₁_verts : X₂ ⊆ G₁.verts.toFinset := by
      dsimp only [G₁]
      rw [h_G₁_verts_eq_X₁_X₂_X₄_X₅]
      simp only [Finset.toFinset_coe]
      exact h_X₂_subset_X_F

    let G₁₁ := (⊤ : G₁.coe.Subgraph).induce {v : G₁.verts | v.val ∈ X₁}
    let G₁₂ := (⊤ : G₁.coe.Subgraph).induce {v : G₁.verts | v.val ∈ X₂}
    let h_G₁₁_ind : G₁₁.IsInduced := Subgraph.induce_top_isInduced G₁.coe {v : G₁.verts | v.val ∈ X₁}
    let h_G₁₂_ind : G₁₂.IsInduced := Subgraph.induce_top_isInduced G₁.coe {v : G₁.verts | v.val ∈ X₂}
    have h_G₁₁_verts_eq_X₁ : G₁₁.verts = {v : G₁.verts | v.val ∈ X₁} := rfl
    have h_G₁₂_verts_eq_X₂ : G₁₂.verts = {v : G₁.verts | v.val ∈ X₂} := rfl

    have h_G₁₁_disj_G₁₂ : G₁₁.verts ∩ G₁₂.verts = ∅ := by
      apply Set.subset_empty_iff.mp
      calc
        G₁₁.verts ∩ G₁₂.verts = ↑{v : G₁.verts | v.val ∈ X₁} ∩ ↑{v : G₁.verts | v.val ∈ X₂} := rfl
        _ = ↑({v : G₁.verts | v.val ∈ X₁} ∩ {v : G₁.verts | v.val ∈ X₂}) := by simp only
        _ = ↑({v : G₁.verts | v.val ∈ X₁ ∩ X₂}) := by simp only [mem_inter]; exact rfl
        _ ⊆ ∅ := by
          rw [h_X₁_disj_X₂]; simp only [notMem_empty, Set.setOf_false, subset_refl]

    have h_X₁_G₁₁ : (⊤ : G.Subgraph).induce X₁ = subgraphByComposition G₁ G₁₁ :=
      induce_top_eq_subgraphByComposition G₁ h_G₁_ind X₁ h_X₁_subset_G₁_verts
    have h_X₂_G₁₂ : (⊤ : G.Subgraph).induce X₂ = subgraphByComposition G₁ G₁₂ :=
      induce_top_eq_subgraphByComposition G₁ h_G₁_ind X₂ h_X₂_subset_G₁_verts

    have h_G₁_verts_card : Fintype.card G₁.verts = Fintype.card (Fin ℓ₁₂) := by
      rw [h_G₁_verts_eq_X₁_X₂_X₄_X₅]
      rw [Fintype.card_fin]
      suffices (X₁ ∪ X₂ ∪ X₄ ∪ X₅).card = ℓ₁₂ by simp only [coe_sort_coe, Fintype.card_coe, this]
      rw [Finset.card_union (X₁ ∪ X₂ ∪ X₄) X₅, h_X₁_X₂_X₄_disj_X₅]
      rw [Finset.card_union (X₁ ∪ X₂) X₄, h_X₁_X₂_disj_X₄]
      rw [Finset.card_union X₁ X₂, h_X₁_disj_X₂]
      rw [h_X₁_card, h_X₂_card, h_X₄_card, h_X₅_card]
      show ℓ₁ + ℓ₂ + (ℓ₂₃ - (ℓ₂ + ℓ₃)) + (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ₁₂
      omega

    let g_G₁_Finℓ₁₂ : G₁.verts ≃ Fin ℓ₁₂ := Fintype.equivOfCardEq h_G₁_verts_card

    let F₀ : SimpleGraph (Fin ℓ₁₂) := SimpleGraph.map g_G₁_Finℓ₁₂.toEmbedding G₁.coe
    let F : QuotSimpleGraph (Fin ℓ₁₂) := ⟦F₀⟧

    let g_G₁_F₀ : G₁.coe ≃g F₀ := SimpleGraph.Iso.map g_G₁_Finℓ₁₂ G₁.coe
    let g_F₀_Fout : F₀ ≃g F.out := by
      have : graph_eqv F₀ F.out :=
        (@Quotient.mk_eq_iff_out (SimpleGraph (Fin ℓ₁₂)) (graphSetoid (Fin ℓ₁₂)) F₀ ⟦F₀⟧).mp rfl
      dsimp only [graph_eqv] at this
      exact this.some
    have h_G₁_Fout : Nonempty (G₁.coe ≃g F.out) := Nonempty.intro (SimpleGraph.Iso.comp g_F₀_Fout g_G₁_F₀)

    let F₁ : Subgraph F.out := subgraphFromIso h_G₁_Fout.some G₁₁
    let F₂ : Subgraph F.out := subgraphFromIso h_G₁_Fout.some G₁₂

    have h_F₁_ind : F₁.IsInduced := subgraphFromIso_preserve_inducedness h_G₁_Fout.some G₁₁ h_G₁₁_ind
    have h_F₂_ind : F₂.IsInduced := subgraphFromIso_preserve_inducedness h_G₁_Fout.some G₁₂ h_G₁₂_ind

    have h_F₁_H₁ : Nonempty (F₁.coe ≃g H₁) :=
      let g_F₁_G₁₁ : F₁.coe ≃g G₁₁.coe := (isoToSubgraphFromIso h_G₁_Fout.some G₁₁).symm
      let g_G₁₁_X₁ : G₁₁.coe ≃g ((⊤ : G.Subgraph).induce X₁).coe := by
        rw [h_X₁_G₁₁]
        exact isoToSubgraphByComposition G₁ G₁₁
      Nonempty.intro ((g_F₁_G₁₁.trans g_G₁₁_X₁).trans h_X₁_H₁.some)
    have h_F₂_H₂ : Nonempty (F₂.coe ≃g H₂) :=
      let g_F₂_G₁₂ : F₂.coe ≃g G₁₂.coe := (isoToSubgraphFromIso h_G₁_Fout.some G₁₂).symm
      let g_G₁₂_X₂ : G₁₂.coe ≃g ((⊤ : G.Subgraph).induce X₂).coe := by
        rw [h_X₂_G₁₂]
        exact isoToSubgraphByComposition G₁ G₁₂
      Nonempty.intro ((g_F₂_G₁₂.trans g_G₁₂_X₂).trans h_X₂_H₂.some)

    have h_F₁_disj_F₂ : F₁.verts ∩ F₂.verts = ∅ := subgraphFromIso_preserve_disjointedness h_G₁_Fout.some G₁₁ G₁₂ h_G₁₁_disj_G₁₂

    let X : Finset (Fin ℓ₁₂) := (h_G₁_Fout.some '' {v : G₁.verts | v.val ∈ X₅}).toFinset
    have h_X_card : X.card = ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) :=
      calc
        X.card = (h_G₁_Fout.some '' {v : G₁.verts | v.val ∈ X₅}).toFinset.card := by
                rfl
        _ = {v : G₁.verts | v.val ∈ X₅}.toFinset.card := by
                rw [Set.toFinset_card (⇑h_G₁_Fout.some '' {v : G₁.verts | v.val ∈ X₅})]
                rw [Set.card_image_of_injective ({v : G₁.verts | v.val ∈ X₅}) h_G₁_Fout.some.injective]
                rw [←Set.toFinset_card ({v : G₁.verts | v.val ∈ X₅})]
        _ = {v : ↑(X₁ ∪ X₂ ∪ X₄ ∪ X₅) | v.val ∈ X₅}.toFinset.card := by
                rw [h_G₁_verts_eq_X₁_X₂_X₄_X₅]
                simp only [coe_sort_coe, Set.toFinset_setOf, univ_eq_attach]
        _ = Fintype.card {v : ↑(X₁ ∪ X₂ ∪ X₄ ∪ X₅) | v.val ∈ X₅} := by
                rw [Set.toFinset_card]
        _ = Fintype.card X₅ := by
                let g : {v : ↑(X₁ ∪ X₂ ∪ X₄ ∪ X₅) | v.val ∈ X₅ } ≃ X₅ := {
                  toFun := fun v => ⟨v.val.val, v.property⟩
                  invFun := fun u => ⟨⟨u.val, by simp only [union_assoc, mem_union, coe_mem, or_true]⟩, u.property⟩
                  left_inv := by intro u; simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.coe_eta]
                  right_inv := by intro v; simp only [Subtype.coe_eta]
                }
                exact Fintype.card_congr g
        _ = X₅.card := by simp only [Fintype.card_coe]
        _ = ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) := h_X₅_card
    have h_X_subset_compl_F₁_F₂ : X ⊆ (F₁.verts ∪ F₂.verts)ᶜ.toFinset := by
      suffices
        ⇑h_G₁_Fout.some '' {v : G₁.verts | v.val ∈ X₅} ⊆ (⇑h_G₁_Fout.some '' G₁₁.verts ∪ ⇑h_G₁_Fout.some '' G₁₂.verts)ᶜ
      by {
        exact Set.toFinset_mono this
      }
      have h' : {v : G₁.verts | v.val ∈ X₅} ⊆ (G₁₁.verts ∪ G₁₂.verts)ᶜ := by
        intro v h_v_X₅
        simp only [Set.mem_setOf_eq] at h_v_X₅
        simp only [G₁₁, G₁₂, Subgraph.induce_verts]
        simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
        constructor <;> intro h_v_X <;> apply Finset.notMem_empty (↑v : Fin ℓ)
        . rw [← h_X₁_disj_X₅]; exact mem_inter.mpr ⟨h_v_X, h_v_X₅⟩
        . rw [← h_X₂_disj_X₅]; exact mem_inter.mpr ⟨h_v_X, h_v_X₅⟩
      calc
        ⇑h_G₁_Fout.some '' {v : G₁.verts | v.val ∈ X₅}
        _ ⊆ ⇑h_G₁_Fout.some '' ((G₁₁.verts ∪ G₁₂.verts)ᶜ) :=
                Set.image_mono h'
        _ = (⇑h_G₁_Fout.some '' (G₁₁.verts ∪ G₁₂.verts))ᶜ := by
                rw [←Set.image_compl_eq h_G₁_Fout.some.bijective]
        _ = (⇑h_G₁_Fout.some '' G₁₁.verts ∪ ⇑h_G₁_Fout.some '' G₁₂.verts)ᶜ := by
                rw [Set.image_union (⇑h_G₁_Fout.some) G₁₁.verts G₁₂.verts]

    use ⟨⟨F, ⟨F₁, F₂, G₁, G₂, X⟩⟩,
          h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂,
          h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂,
          h_X_card, h_X_subset_compl_F₁_F₂⟩

    dsimp only [f_S₁_S₂_fwd, F₁, F₂, X, subgraphFromIso]
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    rw [h_G₁₁_verts_eq_X₁, h_G₁₂_verts_eq_X₂, h_G₂_verts_eq_X₃]
    simp only [Set.coe_toFinset, Finset.toFinset_coe, true_and]
    simp only [←Set.image_union, ←Set.image_compl_eq h_G₁_Fout.some.bijective]
    simp only [←Set.image_comp]
    have h_fn_eq : (Subtype.val ∘ ⇑h_G₁_Fout.some.symm) ∘ ⇑h_G₁_Fout.some = Subtype.val := by
      ext u
      simp only [Function.comp_apply, RelIso.symm_apply_apply]
    rw [h_fn_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    . ext u
      simp only [Set.toFinset_image, Set.toFinset_setOf,
                  mem_image, mem_filter, mem_univ, true_and,
                  Subtype.exists, exists_and_left, exists_prop',
                  nonempty_prop, exists_eq_right_right, and_iff_left_iff_imp]
      intro h_u_X₁
      exact h_X₁_subset_X_F h_u_X₁
    . ext u
      simp only [Set.toFinset_image, Set.toFinset_setOf,
                  mem_image, mem_filter, mem_univ, true_and,
                  Subtype.exists, exists_and_left, exists_prop',
                  nonempty_prop, exists_eq_right_right, and_iff_left_iff_imp]
      intro h_u_X₂
      exact h_X₂_subset_X_F h_u_X₂
    . ext u
      simp only [Set.compl_union, Set.toFinset_image, Set.toFinset_inter,
            Set.toFinset_compl, Set.toFinset_setOf, compl_filter, inter_assoc,
            mem_image, mem_inter, mem_filter, mem_univ,
            true_and, Subtype.exists, exists_and_left, exists_prop', nonempty_prop, exists_eq_right_right]
      constructor
      . rintro ⟨⟨h_u_not_X₁, h_u_not_X₂, h_u_not_X₅⟩, h_u⟩
        rw [h_G₁_verts_eq_X₁_X₂_X₄_X₅] at h_u
        rw [mem_coe] at h_u
        simp only [union_assoc, mem_union] at h_u
        refine Or.resolve_right (?_ : u ∈ X₄ ∨ u ∈ X₅) h_u_not_X₅
        refine Or.resolve_left (?_ : u ∈ X₂ ∨ u ∈ X₄ ∨ u ∈ X₅) h_u_not_X₂
        exact Or.resolve_left h_u h_u_not_X₁
      . intro h_u_X₄
        rw [h_G₁_verts_eq_X₁_X₂_X₄_X₅, mem_coe]
        simp only [union_assoc, mem_union]
        refine ⟨?_, by simp only [h_u_X₄, true_or, or_true]⟩
        have h_u_not_X₁ : u ∉ X₁ := by
          intro h_u_X₁
          have : u ∈ (X₁ ∪ X₂) ∩ X₄ := Finset.mem_inter.mpr ⟨Finset.subset_union_left h_u_X₁, h_u_X₄⟩
          rw [h_X₁_X₂_disj_X₄] at this
          exact Finset.notMem_empty u this
        have h_u_not_X₂ : u ∉ X₂ := by
          intro h_u_X₂
          have : u ∈ (X₁ ∪ X₂) ∩ X₄ := Finset.mem_inter.mpr ⟨Finset.subset_union_right h_u_X₂, h_u_X₄⟩
          rw [h_X₁_X₂_disj_X₄] at this
          exact Finset.notMem_empty u this
        have h_u_not_X₅ : u ∉ X₅ := by
          intro h_u_X₅
          have : u ∈ (X₁ ∪ X₂ ∪ X₄) ∩ X₅ := Finset.mem_inter.mpr ⟨Finset.subset_union_right h_u_X₄, h_u_X₅⟩
          rw [h_X₁_X₂_X₄_disj_X₅] at this
          exact Finset.notMem_empty u this
        exact ⟨h_u_not_X₁, h_u_not_X₂, h_u_not_X₅⟩
    . ext u
      simp only [Set.toFinset_image, Set.toFinset_setOf,
                  mem_image, mem_filter, mem_univ, true_and,
                  Subtype.exists, exists_and_left, exists_prop',
                  nonempty_prop, exists_eq_right_right, and_iff_left_iff_imp]
      intro h_u_X₅
      exact h_X₅_subset_X_F h_u_X₅

  exact Equiv.ofBijective f_S₁_S₂_fwd ⟨h_f_S₁_S₂_inj, h_f_S₁_S₂_surj⟩


/-- The second recoordination step: a five-block decomposition `X₁..X₅` of `G`
corresponds to a `(H₂,H₃)`-in-flag together with an `H₁`-in-`G` configuration
(the mirror image of `..._step1`). -/
noncomputable def subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet_step2
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    : { ⟨X₁, X₂, X₃, X₄, X₅⟩ :  Finset (Fin ℓ) × Finset (Fin ℓ)
                                    × Finset (Fin ℓ) × Finset (Fin ℓ) × Finset (Fin ℓ)
                  | X₁ ∩ X₂ = ∅
                  ∧ (X₁ ∪ X₂) ∩ X₃ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅
                  ∧ X₁.card = ℓ₁
                  ∧ X₂.card = ℓ₂
                  ∧ X₃.card = ℓ₃
                  ∧ X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃)
                  ∧ X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₁).coe ≃g H₁)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₂).coe ≃g H₂)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₃).coe ≃g H₃) }
      ≃
      { ⟨F, F₁, F₂, G₁, G₂, X⟩ :  (F : QuotSimpleGraph (Fin ℓ₂₃))
                                  × Subgraph F.out × Subgraph F.out
                                  × Subgraph G × Subgraph G
                                  × Finset (Fin ℓ)
                  | F₁.IsInduced
                  ∧ Nonempty (F₁.coe ≃g H₂)
                  ∧ F₂.IsInduced
                  ∧ Nonempty (F₂.coe ≃g H₃)
                  ∧ F₁.verts ∩ F₂.verts = ∅
                  ∧ G₁.IsInduced
                  ∧ Nonempty (G₁.coe ≃g F.out)
                  ∧ G₂.IsInduced
                  ∧ Nonempty (G₂.coe ≃g H₁)
                  ∧ G₁.verts ∩ G₂.verts = ∅
                  ∧ X.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ X ⊆ (G₁.verts ∪ G₂.verts)ᶜ.toFinset }
  := by

  let S₂ := { ⟨X₁, X₂, X₃, X₄, X₅⟩ :  Finset (Fin ℓ) × Finset (Fin ℓ)
                                    × Finset (Fin ℓ) × Finset (Fin ℓ) × Finset (Fin ℓ)
                  | X₁ ∩ X₂ = ∅
                  ∧ (X₁ ∪ X₂) ∩ X₃ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅
                  ∧ X₁.card = ℓ₁
                  ∧ X₂.card = ℓ₂
                  ∧ X₃.card = ℓ₃
                  ∧ X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃)
                  ∧ X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₁).coe ≃g H₁)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₂).coe ≃g H₂)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₃).coe ≃g H₃) }

  let S₃ := { ⟨F, F₁, F₂, G₁, G₂, X⟩ :  (F : QuotSimpleGraph (Fin ℓ₂₃))
                                      × Subgraph F.out × Subgraph F.out
                                      × Subgraph G × Subgraph G
                                      × Finset (Fin ℓ)
                  | F₁.IsInduced
                  ∧ Nonempty (F₁.coe ≃g H₂)
                  ∧ F₂.IsInduced
                  ∧ Nonempty (F₂.coe ≃g H₃)
                  ∧ F₁.verts ∩ F₂.verts = ∅
                  ∧ G₁.IsInduced
                  ∧ Nonempty (G₁.coe ≃g F.out)
                  ∧ G₂.IsInduced
                  ∧ Nonempty (G₂.coe ≃g H₁)
                  ∧ G₁.verts ∩ G₂.verts = ∅
                  ∧ X.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ X ⊆ (G₁.verts ∪ G₂.verts)ᶜ.toFinset }

  let f_S₃_S₂_fwd : S₃ → S₂ := by
    intro ⟨⟨F, F₁, F₂, G₁, G₂, X⟩,
            h_F₁_ind, h_F₁_H₂, h_F₂_ind, h_F₂_H₃, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₁, h_G₁_disj_G₂,
            h_X_card, h_X_G₁_G₂⟩

    let g_F₁_H₂ : F₁.coe ≃g H₂ := h_F₁_H₂.some
    let g_F₂_H₃ : F₂.coe ≃g H₃ := h_F₂_H₃.some

    let g_G₁_Fout : G₁.coe ≃g F.out := h_G₁_Fout.some
    let g_G₂_H₁ : G₂.coe ≃g H₁ := h_G₂_H₁.some

    let g_Fout_to_G : Fin ℓ₂₃ → Fin ℓ := Subtype.val ∘ g_G₁_Fout.symm

    let X₁ : Finset (Fin ℓ) := G₂.verts.toFinset
    let X₂ : Finset (Fin ℓ) := (g_Fout_to_G '' F₁.verts).toFinset
    let X₃ : Finset (Fin ℓ) := (g_Fout_to_G '' F₂.verts).toFinset
    let X₄ : Finset (Fin ℓ) := (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)ᶜ).toFinset
    let X₅ : Finset (Fin ℓ) := X

    refine ⟨⟨X₁, X₂, X₃, X₄, X₅⟩, ?_⟩

    have h_g_Fout_to_G_injective := Function.Injective.comp Subtype.val_injective g_G₁_Fout.symm.injective

    have h_image_g_Fout_to_G_subset_G₁_verts :
        ∀ (V : Set (Fin ℓ₂₃)), g_Fout_to_G '' V ⊆ G₁.verts
      := by
      intro V
      calc
        (Subtype.val ∘ g_G₁_Fout.symm) '' V
        _ = Subtype.val '' (g_G₁_Fout.symm '' V) := by simp only [Function.comp_apply, Set.image_image]
        _ ⊆ G₁.verts := by simp only [Set.image_subset_iff, Subtype.coe_preimage_self, Set.subset_univ]


    have h_induce_X₁ : (⊤ : G.Subgraph).induce X₁ = G₂ := by
      simp only [X₁, Set.coe_toFinset, h_G₂_ind.induce_top_verts]
    let g_X₁_H₁ : ((⊤ : G.Subgraph).induce X₁).coe ≃g H₁ := by
      rw [h_induce_X₁]; exact g_G₂_H₁
    let g_X₂_H₂ : ((⊤ : G.Subgraph).induce X₂).coe ≃g H₂ := by
      have type_eq : X₂ = @Set.toFinset
                            (Fin ℓ)
                            (Subtype.val ∘ ⇑g_G₁_Fout.symm '' F₁.verts)
                            (@Set.fintypeImage
                              (Fin ℓ₂₃) (Fin ℓ)
                              (fun a b ↦ propDecidable (a = b))
                              F₁.verts
                              (Subtype.val ∘ ⇑g_G₁_Fout.symm)
                              (Subtype.fintype (Membership.mem F₁.verts)))
        := by
        congr!
      rw [type_eq]
      exact isoFromInducedSubgraphByPartialIso g_G₁_Fout g_F₁_H₂ h_F₁_ind h_G₁_ind
    let g_X₃_H₃ : ((⊤ : G.Subgraph).induce X₃).coe ≃g H₃ := by
      have type_eq : X₃ = @Set.toFinset
                            (Fin ℓ)
                            (Subtype.val ∘ ⇑g_G₁_Fout.symm '' F₂.verts)
                            (@Set.fintypeImage
                              (Fin ℓ₂₃) (Fin ℓ)
                              (fun a b ↦ propDecidable (a = b))
                              F₂.verts
                              (Subtype.val ∘ ⇑g_G₁_Fout.symm)
                              (Subtype.fintype (Membership.mem F₂.verts)))
        := by
        congr!
      rw [type_eq]
      exact isoFromInducedSubgraphByPartialIso g_G₁_Fout g_F₂_H₃ h_F₂_ind h_G₁_ind

    have h_X₂_X₃_X₄_subset_G₁_verts : X₂ ∪ X₃ ∪ X₄ ⊆ G₁.verts.toFinset := by
      rw [←Set.toFinset_union
            (g_Fout_to_G '' F₁.verts)
            (g_Fout_to_G '' F₂.verts)]
      rw [←Set.toFinset_union
            ((g_Fout_to_G '' F₁.verts) ∪ (g_Fout_to_G '' F₂.verts))
            (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)ᶜ)]
      apply Set.toFinset_mono
      rw [←Set.image_union g_Fout_to_G F₁.verts F₂.verts]
      rw [←Set.image_union g_Fout_to_G (F₁.verts ∪ F₂.verts) (F₁.verts ∪ F₂.verts)ᶜ]
      exact h_image_g_Fout_to_G_subset_G₁_verts ((F₁.verts ∪ F₂.verts) ∪ (F₁.verts ∪ F₂.verts)ᶜ)

    have h_X₁_disj_X₂_X₃_X₄ : X₁ ∩ (X₂ ∪ X₃ ∪ X₄) = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₁ ∩ (X₂ ∪ X₃ ∪ X₄) ⊆ G₂.verts.toFinset ∩ G₁.verts.toFinset :=
                Finset.inter_subset_inter (subset_refl G₂.verts.toFinset) h_X₂_X₃_X₄_subset_G₁_verts
        _ = (G₁.verts ∩ G₂.verts).toFinset := by
                rw [Finset.inter_comm G₂.verts.toFinset G₁.verts.toFinset]
                rw [Set.toFinset_inter G₁.verts G₂.verts]
        _ = ∅ := by
                simp only [h_G₁_disj_G₂, Set.toFinset_empty]
    have h_X₁_disj_X₂ : X₁ ∩ X₂ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₁ ∩ X₂ ⊆ X₁ ∩ (X₂ ∪ X₃ ∪ X₄) := by
                rw [Finset.union_assoc X₂ X₃ X₄]
                exact Finset.inter_subset_inter (subset_refl X₁) Finset.subset_union_left
        _ = ∅ := h_X₁_disj_X₂_X₃_X₄
    have h_X₁_disj_X₃ : X₁ ∩ X₃ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₁ ∩ X₃ ⊆ X₁ ∩ (X₂ ∪ X₃ ∪ X₄) := by
                rw [Finset.union_comm X₂ X₃]
                rw [Finset.union_assoc X₃ X₂ X₄]
                exact Finset.inter_subset_inter (subset_refl X₁) Finset.subset_union_left
        _ = ∅ := h_X₁_disj_X₂_X₃_X₄
    have h_X₁_disj_X₄ : X₁ ∩ X₄ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₁ ∩ X₄ ⊆ X₁ ∩ (X₂ ∪ X₃ ∪ X₄) := Finset.inter_subset_inter (subset_refl X₁) Finset.subset_union_right
        _ = ∅ := h_X₁_disj_X₂_X₃_X₄

    have h_X₂_disj_X₃ : X₂ ∩ X₃ = ∅ := by
      rw [←Set.toFinset_inter (g_Fout_to_G '' F₁.verts) (g_Fout_to_G '' F₂.verts)]
      apply Set.toFinset_eq_empty.mpr
      rw [←Set.image_inter h_g_Fout_to_G_injective]
      rw [Set.image_eq_empty]
      rw [h_F₁_disj_F₂]
    have h_X₁_X₂_disj_X₃ : (X₁ ∪ X₂) ∩ X₃ = ∅ := by
      rw [Finset.union_inter_distrib_right X₁ X₂ X₃]
      rw [h_X₁_disj_X₃, h_X₂_disj_X₃]
      simp only [empty_union]
    have h_X₁_X₂_X₃_disj_X₄ : (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅ := by
      calc
        (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = (X₁ ∩ X₄) ∪ ((X₂ ∪ X₃) ∩ X₄) := by
                rw [Finset.union_inter_distrib_right (X₁ ∪ X₂) X₃ X₄]
                rw [Finset.union_inter_distrib_right X₁ X₂ X₄]
                rw [Finset.union_assoc (X₁ ∩ X₄) (X₂ ∩ X₄) (X₃ ∩ X₄)]
                rw [←Finset.union_inter_distrib_right X₂ X₃ X₄]
        _ = (X₂ ∪ X₃) ∩ X₄ := by simp only [h_X₁_disj_X₄, empty_union]
        _ = (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)).toFinset ∩ X₄ := by
                rw [←Set.toFinset_union (g_Fout_to_G '' F₁.verts) (g_Fout_to_G '' F₂.verts)]
                simp only [Set.toFinset_union, Set.toFinset_image,
                  Set.image_union g_Fout_to_G F₁.verts F₂.verts]
        _ = (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)).toFinset ∩ (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)ᶜ).toFinset := by
                rfl
        _ = ∅ := by
                rw [←Set.toFinset_inter (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)) (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)ᶜ)]
                apply Set.toFinset_eq_empty.mpr
                rw [←Set.image_inter h_g_Fout_to_G_injective]
                rw [Set.image_eq_empty]
                rw [Set.inter_compl_self (F₁.verts ∪ F₂.verts)]
    have h_X₁_X₂_X₃_X₄_disj_X₅ : (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅ := by
      have h' : X₁ ⊆ G₂.verts.toFinset := by dsimp only [X₁]; exact subset_rfl
      have h'' : X₂ ∪ X₃ ∪ X₄ ⊆ G₁.verts.toFinset := h_X₂_X₃_X₄_subset_G₁_verts
      apply Finset.subset_empty.mp
      calc
        (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = (X₁ ∪ (X₂ ∪ X₃ ∪ X₄)) ∩ X₅ := by
                rw [Finset.union_assoc (X₁ ∪ X₂) X₃ X₄]
                rw [Finset.union_assoc X₁ X₂ (X₃ ∪ X₄)]
                rw [←Finset.union_assoc X₂ X₃ X₄]
        _ ⊆ (G₂.verts.toFinset ∪ G₁.verts.toFinset) ∩ X₅ :=
                Finset.inter_subset_inter (Finset.union_subset_union h' h'') (subset_refl X₅)
        _ ⊆ (G₁.verts.toFinset ∪ G₂.verts.toFinset) ∩ (G₁.verts ∪ G₂.verts)ᶜ.toFinset := by
                rw [Finset.union_comm G₂.verts.toFinset G₁.verts.toFinset]
                exact Finset.inter_subset_inter (subset_refl (G₁.verts.toFinset ∪ G₂.verts.toFinset)) h_X_G₁_G₂
        _ = ((G₁.verts ∪ G₂.verts) ∩ (G₁.verts ∪ G₂.verts)ᶜ).toFinset := by
                simp only [Set.compl_union, Set.toFinset_inter, Set.toFinset_compl, Set.toFinset_union]
        _ = ∅ :=
                Set.toFinset_eq_empty.mpr (Set.inter_compl_self (G₁.verts ∪ G₂.verts))

    have h_X₁_card : X₁.card = ℓ₁ := by
      simp only [← subgraph_verts_card_from_iso_graph g_X₁_H₁, Subgraph.induce_verts, coe_sort_coe, Fintype.card_coe]
    have h_X₂_card : X₂.card = ℓ₂ := by
      simp only [←subgraph_verts_card_from_iso_graph g_X₂_H₂, Subgraph.induce_verts, coe_sort_coe, Fintype.card_coe]
    have h_X₃_card : X₃.card = ℓ₃ := by
      simp only [←subgraph_verts_card_from_iso_graph g_X₃_H₃, Subgraph.induce_verts, coe_sort_coe, Fintype.card_coe]
    have h_X₄_card : X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃) :=
      calc
        X₄.card
        _  = Fintype.card (g_Fout_to_G '' (F₁.verts ∪ F₂.verts)ᶜ) := by
              simp only [Set.toFinset_image, Set.compl_union, Set.toFinset_inter,
                Set.toFinset_compl, Fintype.card_ofFinset, X₄]
        _ = Fintype.card ↑(F₁.verts ∪ F₂.verts)ᶜ :=
              Set.card_image_of_injective (F₁.verts ∪ F₂.verts)ᶜ h_g_Fout_to_G_injective
        _ = (F₁.verts ∪ F₂.verts)ᶜ.toFinset.card := by
              apply Eq.symm
              apply Set.toFinset_card
        _ = (F₁.verts ∪ F₂.verts).toFinsetᶜ.card := by
              simp only [Set.toFinset_compl]
        _ = Fintype.card ↑(Fin ℓ₂₃) - (F₁.verts ∪ F₂.verts).toFinset.card := by
              rw [card_compl]
        _ = ℓ₂₃ - (F₁.verts ∪ F₂.verts).toFinset.card := by
              simp only [Fintype.card_fin]
        _ = ℓ₂₃ - (F₁.verts.toFinset ∪ F₂.verts.toFinset).card := by
              simp only [Set.toFinset_union]
        _ = ℓ₂₃ - (Fintype.card F₁.verts + Fintype.card F₂.verts) := by
            rw [Finset.card_union F₁.verts.toFinset F₂.verts.toFinset]
            have : F₁.verts.toFinset ∩ F₂.verts.toFinset = ∅ := by
              rw [←Set.toFinset_inter F₁.verts F₂.verts]
              simp only [h_F₁_disj_F₂, Set.toFinset_empty]
            simp only [this, card_empty, tsub_zero]
            simp only [Set.toFinset_card, Fintype.card_ofFinset]
        _ = ℓ₂₃ - (ℓ₂ + ℓ₃) := by
              rw [Iso.card_eq g_F₁_H₂, Iso.card_eq g_F₂_H₃]
              simp only [Fintype.card_fin]
    have h_X₅_card : X₅.card = ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) := h_X_card

    exact ⟨h_X₁_disj_X₂, h_X₁_X₂_disj_X₃, h_X₁_X₂_X₃_disj_X₄, h_X₁_X₂_X₃_X₄_disj_X₅,
            h_X₁_card, h_X₂_card, h_X₃_card, h_X₄_card, h_X₅_card,
            Nonempty.intro g_X₁_H₁, Nonempty.intro g_X₂_H₂, Nonempty.intro g_X₃_H₃⟩

  have h_f_S₃_S₂_inj : Function.Injective f_S₃_S₂_fwd := by
    intro ⟨⟨F, F₁, F₂, G₁, G₂, X⟩,
            h_F₁_ind, h_F₁_H₂, h_F₂_ind, h_F₂_H₃, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₁, h_G₁_disj_G₂,
            h_X_card, h_X_G₁_G₂⟩
      ⟨⟨F', F₁', F₂', G₁', G₂', X'⟩,
            h_F₁'_ind, h_F₁'_H₂, h_F₂'_ind, h_F₂'_H₃, h_F₁'_disj_F₂',
            h_G₁'_ind, h_G₁'_Fout', h_G₂'_ind, h_G₂'_H₁, h_G₁'_disj_G₂',
            h_X'_card, h_X'_G₁'_G₂'⟩
      h_eq
    simp [f_S₃_S₂_fwd] at h_eq
    obtain ⟨h_X₁_eq_X₁', h_X₂_eq_X₂', h_X₃_eq_X₃', h_X₄_eq_X₄', h_X₅_eq_X₅'⟩ := h_eq
    simp only [Subtype.mk.injEq, Sigma.mk.inj_iff]

    have h_G₁_eq_G₁' : G₁ = G₁' := by
      apply h_G₁_ind.eq_of_verts_eq h_G₁'_ind
      calc
        G₁.verts
        _ = Subtype.val '' (⇑h_G₁_Fout.some.symm '' (univ : Finset (Fin ℓ₂₃))) := by
                have : ⇑h_G₁_Fout.some.symm '' (Set.univ : Set (Fin ℓ₂₃))
                        = (Set.univ : Set (G₁.verts))
                  := Set.image_univ_of_surjective h_G₁_Fout.some.symm.surjective
                simp only [this, coe_univ, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
        _ = (Subtype.val ∘ ⇑h_G₁_Fout.some.symm) '' (univ : Finset (Fin ℓ₂₃)) := by
                simp only [Function.comp_apply, Set.image_image]
        _ = (Subtype.val ∘ h_G₁_Fout.some.symm) '' ((F₁.verts.toFinset ∪ F₂.verts.toFinset)
                                                    ∪ (F₁.verts.toFinset ∪ F₂.verts.toFinset)ᶜ) := by
                simp only [coe_univ, Set.image_univ, Set.coe_toFinset, Set.union_compl_self]
        _ = (Subtype.val ∘ h_G₁_Fout.some.symm) '' (F₁.verts.toFinset ∪ F₂.verts.toFinset
                                                    ∪ (F₁.verts.toFinsetᶜ ∩ F₂.verts.toFinsetᶜ)) := by
                simp only [Set.coe_toFinset, Set.compl_union]
        _ = (Subtype.val ∘ h_G₁_Fout.some.symm) '' (F₁.verts.toFinset ∪ F₂.verts.toFinset
                                                    ∪ (F₁.verts.toFinsetᶜ ∩ (F₂.verts.toFinsetᶜ))) := by
                simp only [Function.comp_apply, Set.coe_toFinset]
        _ = ((Subtype.val ∘ h_G₁_Fout.some.symm) '' F₁.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁_Fout.some.symm) '' F₂.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁_Fout.some.symm) '' (F₁.verts.toFinsetᶜ ∩ (F₂.verts.toFinsetᶜ))) := by
                simp only [Set.image_union (Subtype.val ∘ h_G₁_Fout.some.symm)]
        _ = SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) F₁.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) F₂.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) (F₁.verts.toFinsetᶜ ∩ (F₂.verts.toFinsetᶜ))) := by
                simp only [Function.comp_apply, Set.coe_toFinset, coe_image, coe_inter, coe_compl]
        _ = SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) F₁'.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) F₂'.verts.toFinset)
              ∪ SetLike.coe (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) (F₁'.verts.toFinsetᶜ ∩ (F₂'.verts.toFinsetᶜ))) := by
                rw [h_X₂_eq_X₂', h_X₃_eq_X₃', h_X₄_eq_X₄']
        _ = ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' F₁'.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' F₂'.verts.toFinset)
              ∪ ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (F₁'.verts.toFinsetᶜ ∩ (F₂'.verts.toFinsetᶜ))) := by
                simp only [Function.comp_apply, Set.coe_toFinset, coe_image, coe_inter, coe_compl]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (F₁'.verts.toFinset ∪ F₂'.verts.toFinset
                                                      ∪ (F₁'.verts.toFinsetᶜ ∩ (F₂'.verts.toFinsetᶜ))) := by
                simp only [Set.image_union (Subtype.val ∘ h_G₁'_Fout'.some.symm)]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (F₁'.verts.toFinset ∪ F₂'.verts.toFinset
                                                      ∪ (F₁'.verts.toFinsetᶜ ∩ F₂'.verts.toFinsetᶜ)) := by
                simp only [Function.comp_apply, Set.coe_toFinset]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' ((F₁'.verts.toFinset ∪ F₂'.verts.toFinset)
                                                      ∪ (F₁'.verts.toFinset ∪ F₂'.verts.toFinset)ᶜ) := by
                simp only [Set.coe_toFinset, Set.compl_union]
        _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' (univ : Finset (Fin ℓ₂₃)) := by
                simp only [coe_univ, Set.image_univ, Set.coe_toFinset, Set.union_compl_self]
        _ = h_G₁'_Fout'.some.symm '' (univ : Finset (Fin ℓ₂₃)) := by
                simp only [Function.comp_apply, Set.image_image]
        _ = G₁'.verts := by
                have : ⇑h_G₁'_Fout'.some.symm '' (Set.univ : Set (Fin ℓ₂₃))
                        = (Set.univ : Set (G₁'.verts))
                  := Set.image_univ_of_surjective h_G₁'_Fout'.some.symm.surjective
                simp only [this, coe_univ, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
    subst h_G₁_eq_G₁'

    have h_F_eq_F' : F = F' :=
      calc
        F = ⟦F.out⟧ := Eq.symm (Quotient.out_eq F)
        _ = ⟦F'.out⟧ := Quotient.sound (Nonempty.intro (h_G₁_Fout.some.symm.trans h_G₁'_Fout'.some))
        _ = F' := Quotient.out_eq F'
    subst h_F_eq_F'
    simp only [heq_eq_eq, Prod.mk.injEq, true_and]

    have h_G₂_eq_G₂' : G₂ = G₂' := h_G₂_ind.eq_of_verts_eq h_G₂'_ind h_X₁_eq_X₁'
    subst h_G₂_eq_G₂'

    have h_source_eq_from_target_eq :
        ∀ {X₀ X₀' : Finset (Fin ℓ₂₃)},
          image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) X₀ = image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) X₀'
          → X₀ = X₀'
      := by
      intro X₀ X₀' h_X₀_eq_X₀'
      have : (Subtype.val ∘ h_G₁_Fout.some.symm) '' X₀ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀' := by
        calc
          (Subtype.val ∘ h_G₁_Fout.some.symm) '' X₀ = SetLike.coe (image (fun a ↦ ↑(h_G₁_Fout.some.symm a)) X₀) := by
                simp only [Function.comp_apply, coe_image]
          _ = SetLike.coe (image (fun a ↦ ↑(h_G₁'_Fout'.some.symm a)) X₀') := by
                simp only [h_X₀_eq_X₀', coe_image]
          _ = (Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀' := by
                simp only [coe_image, Function.comp_apply]
      calc
        X₀ = ((Subtype.val ∘ h_G₁_Fout.some.symm)⁻¹' ((Subtype.val ∘ h_G₁_Fout.some.symm) '' X₀)).toFinset := by
              have : Function.Injective (Subtype.val ∘ h_G₁_Fout.some.symm) :=
                Function.Injective.comp Subtype.val_injective h_G₁_Fout.some.symm.injective
              rw [Function.Injective.preimage_image this X₀]
              simp only [toFinset_coe]
        _ = ((Subtype.val ∘ h_G₁_Fout.some.symm)⁻¹' ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀')).toFinset := by
              rw [this]
        _ = ((Subtype.val ∘ h_G₁'_Fout'.some.symm)⁻¹' ((Subtype.val ∘ h_G₁'_Fout'.some.symm) '' X₀')).toFinset := by
              rfl
        _ = X₀' := by
              have : Function.Injective (Subtype.val ∘ h_G₁'_Fout'.some.symm) :=
                Function.Injective.comp Subtype.val_injective h_G₁'_Fout'.some.symm.injective
              rw [Function.Injective.preimage_image this X₀']
              simp only [toFinset_coe]

    have h_ind_subgraph_eq_from_vert_eq :
        ∀ {F₀ F₀' : Subgraph F.out},
          F₀.IsInduced
          → F₀'.IsInduced
          → (image (fun a ↦ Subtype.val (h_G₁_Fout.some.symm a)) F₀.verts.toFinset)
            = (image (fun a ↦ Subtype.val (h_G₁'_Fout'.some.symm a)) F₀'.verts.toFinset)
          → F₀ = F₀'
      := by
      intro F₀ F₀' h_F₀_ind h_F₀'_ind h_vert_eq
      apply h_F₀_ind.eq_of_verts_eq h_F₀'_ind
      calc
        F₀.verts = F₀.verts.toFinset := by simp only [Set.coe_toFinset]
        _ = F₀'.verts.toFinset := by rw [h_source_eq_from_target_eq h_vert_eq]
        _ = F₀'.verts := by simp only [Set.coe_toFinset]


    have h_F₁_eq_F₁' : F₁ = F₁' := h_ind_subgraph_eq_from_vert_eq h_F₁_ind h_F₁'_ind h_X₂_eq_X₂'
    subst h_F₁_eq_F₁'

    have h_F₂_eq_F₂' : F₂ = F₂' := h_ind_subgraph_eq_from_vert_eq h_F₂_ind h_F₂'_ind h_X₃_eq_X₃'
    subst h_F₂_eq_F₂'
    simp only [true_and]

    show X = X'
    exact h_X₅_eq_X₅'

  have h_f_S₃_S₂_surj : Function.Surjective f_S₃_S₂_fwd := by
    intro ⟨⟨X₁, X₂, X₃, X₄, X₅⟩,
            h_X₁_disj_X₂, h_X₁_to_X₂_disj_X₃, h_X₁_to_X₃_disj_X₄, h_X₁_to_X₄_disj_X₅,
            h_X₁_card, h_X₂_card, h_X₃_card, h_X₄_card, h_X₅_card,
            h_X₁_H₁, h_X₂_H₂, h_X₃_H₃⟩

    have h_X₁_disj_X₂_X₃_X₄ : X₁ ∩ (X₂ ∪ X₃ ∪ X₄) = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₁ ∩ (X₂ ∪ X₃ ∪ X₄) = (X₁ ∩ X₂) ∪ (X₁ ∩ X₃) ∪ (X₁ ∩ X₄) := by
                rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left]
        _ ⊆ (X₁ ∩ X₂) ∪ ((X₁ ∪ X₂) ∩ X₃) ∪ ((X₁ ∪ X₂ ∪ X₃) ∩ X₄) :=
                Finset.union_subset_union
                  (Finset.union_subset_union_right (Finset.inter_subset_inter_right Finset.subset_union_left))
                  (by rw [Finset.union_assoc X₁ X₂ X₃]; exact Finset.inter_subset_inter_right Finset.subset_union_left)
        _ = ∅ := by
                rw [h_X₁_disj_X₂, h_X₁_to_X₂_disj_X₃, h_X₁_to_X₃_disj_X₄]
                simp only [union_idempotent]
    have h_X₂_disj_X₃ : X₂ ∩ X₃ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        X₂ ∩ X₃ ⊆ (X₁ ∪ X₂) ∩ X₃ := Finset.inter_subset_inter_right Finset.subset_union_right
        _ = ∅ := h_X₁_to_X₂_disj_X₃
    have h_X₂_X₃_disj_X₄ : (X₂ ∪ X₃) ∩ X₄ = ∅ := by
      apply Finset.subset_empty.mp
      calc
        (X₂ ∪ X₃) ∩ X₄ ⊆ (X₁ ∪ (X₂ ∪ X₃)) ∩ X₄ := Finset.inter_subset_inter_right Finset.subset_union_right
        _ = (X₁ ∪ X₂ ∪ X₃) ∩ X₄ := by rw [Finset.union_assoc]
        _ = ∅ := h_X₁_to_X₃_disj_X₄

    let X₂₃₄ := X₂ ∪ X₃ ∪ X₄
    have h_X₂₃₄_disj_X₁ : X₂₃₄ ∩ X₁ = ∅ := by
      rw [Finset.inter_comm X₂₃₄ X₁]
      exact h_X₁_disj_X₂_X₃_X₄
    have h_X₂_subset_X₂₃₄ : X₂ ⊆ X₂₃₄ := by
      dsimp only [X₂₃₄]
      rw [Finset.union_assoc X₂ X₃ X₄]
      exact Finset.subset_union_left
    have h_X₃_subset_X₂₃₄ : X₃ ⊆ X₂₃₄ := by
      dsimp only [X₂₃₄]
      rw [Finset.union_comm X₂ X₃]
      rw [Finset.union_assoc X₃ X₂ X₄]
      exact Finset.subset_union_left

    let G₁ := (⊤ : G.Subgraph).induce X₂₃₄
    let G₂ := (⊤ : G.Subgraph).induce X₁
    let h_G₁_ind : G₁.IsInduced := Subgraph.induce_top_isInduced G X₂₃₄
    let h_G₂_ind : G₂.IsInduced := Subgraph.induce_top_isInduced G X₁
    have h_G₂_H₁ : Nonempty (G₂.coe ≃g H₁) := h_X₁_H₁

    have h_G₁_disj_G₂ : G₁.verts ∩ G₂.verts = ∅ := by
      apply Set.subset_empty_iff.mp
      calc
        G₁.verts ∩ G₂.verts = ↑X₂₃₄ ∩ ↑X₁ := by rw [Subgraph.induce_verts, Subgraph.induce_verts]
        _ = ↑(X₂₃₄ ∩ X₁) := by simp only [coe_inter]
        _ ⊆ ∅ := by simp only [h_X₂₃₄_disj_X₁, coe_empty, subset_refl]
    have h_G₁_verts_eq_X₂₃₄ : G₁.verts = X₂₃₄ :=
      Subgraph.induce_verts _ _
    have h_G₂_verts_eq_X₁ : G₂.verts = X₁ :=
      Subgraph.induce_verts _ _
    have h_X₂_subset_G₁_verts : X₂ ⊆ G₁.verts.toFinset := by
      rw [h_G₁_verts_eq_X₂₃₄]
      simp only [Finset.toFinset_coe]
      exact h_X₂_subset_X₂₃₄
    have h_X₃_subset_G₁_verts : X₃ ⊆ G₁.verts.toFinset := by
      rw [h_G₁_verts_eq_X₂₃₄]
      simp only [Finset.toFinset_coe]
      exact h_X₃_subset_X₂₃₄

    let G₁₁ := (⊤ : G₁.coe.Subgraph).induce {v : G₁.verts | v.val ∈ X₂}
    let G₁₂ := (⊤ : G₁.coe.Subgraph).induce {v : G₁.verts | v.val ∈ X₃}
    let h_G₁₁_ind : G₁₁.IsInduced := Subgraph.induce_top_isInduced G₁.coe {v : G₁.verts | v.val ∈ X₂}
    let h_G₁₂_ind : G₁₂.IsInduced := Subgraph.induce_top_isInduced G₁.coe {v : G₁.verts | v.val ∈ X₃}
    have h_G₁₁_verts_eq_X₂ : G₁₁.verts = {v : G₁.verts | v.val ∈ X₂} := rfl
    have h_G₁₂_verts_eq_X₃ : G₁₂.verts = {v : G₁.verts | v.val ∈ X₃} := rfl

    have h_G₁₁_disj_G₁₂ : G₁₁.verts ∩ G₁₂.verts = ∅ := by
      apply Set.subset_empty_iff.mp
      calc
        G₁₁.verts ∩ G₁₂.verts = ↑{v : G₁.verts | v.val ∈ X₂} ∩ ↑{v : G₁.verts | v.val ∈ X₃} := rfl
        _ = ↑({v : G₁.verts | v.val ∈ X₂} ∩ {v : G₁.verts | v.val ∈ X₃}) := by simp only
        _ = ↑({v : G₁.verts | v.val ∈ X₂ ∩ X₃}) := by simp only [mem_inter]; exact rfl
        _ ⊆ ∅ := by rw [h_X₂_disj_X₃]; simp only [Finset.notMem_empty, Set.setOf_false, subset_refl]

    have h_X₂_G₁₁ : (⊤ : G.Subgraph).induce X₂ = subgraphByComposition G₁ G₁₁ :=
      induce_top_eq_subgraphByComposition G₁ h_G₁_ind X₂ h_X₂_subset_G₁_verts
    have h_X₃_G₁₂ : (⊤ : G.Subgraph).induce X₃ = subgraphByComposition G₁ G₁₂ :=
      induce_top_eq_subgraphByComposition G₁ h_G₁_ind X₃ h_X₃_subset_G₁_verts

    have h_G₁_verts_card : Fintype.card G₁.verts = Fintype.card (Fin ℓ₂₃) := by
      rw [h_G₁_verts_eq_X₂₃₄, Fintype.card_fin]
      suffices (X₂ ∪ X₃ ∪ X₄).card = ℓ₂₃ by {
        rw [←this, ←Fintype.card_coe (X₂ ∪ X₃ ∪ X₄)]
        congr!
      }
      rw [Finset.card_union (X₂ ∪ X₃) X₄, h_X₂_X₃_disj_X₄]
      rw [Finset.card_union X₂ X₃, h_X₂_disj_X₃]
      rw [h_X₂_card, h_X₃_card, h_X₄_card]
      show ℓ₂ + ℓ₃ + (ℓ₂₃ - (ℓ₂ + ℓ₃)) = ℓ₂₃
      omega

    let g_G₁_Finℓ₂₃ : G₁.verts ≃ Fin ℓ₂₃ := Fintype.equivOfCardEq h_G₁_verts_card

    let F₀ : SimpleGraph (Fin ℓ₂₃) := SimpleGraph.map g_G₁_Finℓ₂₃.toEmbedding G₁.coe
    let F : QuotSimpleGraph (Fin ℓ₂₃) := ⟦F₀⟧

    let g_G₁_F₀ : G₁.coe ≃g F₀ := SimpleGraph.Iso.map g_G₁_Finℓ₂₃ G₁.coe
    let g_F₀_Fout : F₀ ≃g F.out := by
      have : graph_eqv F₀ F.out :=
        (@Quotient.mk_eq_iff_out (SimpleGraph (Fin ℓ₂₃)) (graphSetoid (Fin ℓ₂₃)) F₀ ⟦F₀⟧).mp rfl
      exact this.some
    have h_G₁_Fout : Nonempty (G₁.coe ≃g F.out) := Nonempty.intro (SimpleGraph.Iso.comp g_F₀_Fout g_G₁_F₀)

    let F₁ : Subgraph F.out := subgraphFromIso h_G₁_Fout.some G₁₁
    let F₂ : Subgraph F.out := subgraphFromIso h_G₁_Fout.some G₁₂

    have h_F₁_ind : F₁.IsInduced := subgraphFromIso_preserve_inducedness h_G₁_Fout.some G₁₁ h_G₁₁_ind
    have h_F₂_ind : F₂.IsInduced := subgraphFromIso_preserve_inducedness h_G₁_Fout.some G₁₂ h_G₁₂_ind

    have h_F₁_H₂ : Nonempty (F₁.coe ≃g H₂) :=
      let g_F₁_G₁₁ : F₁.coe ≃g G₁₁.coe := (isoToSubgraphFromIso h_G₁_Fout.some G₁₁).symm
      let g_G₁₁_X₂ : G₁₁.coe ≃g ((⊤ : G.Subgraph).induce X₂).coe := by
        rw [h_X₂_G₁₁]
        exact isoToSubgraphByComposition G₁ G₁₁
      Nonempty.intro ((g_F₁_G₁₁.trans g_G₁₁_X₂).trans h_X₂_H₂.some)
    have h_F₂_H₃ : Nonempty (F₂.coe ≃g H₃) :=
      let g_F₂_G₁₂ : F₂.coe ≃g G₁₂.coe := (isoToSubgraphFromIso h_G₁_Fout.some G₁₂).symm
      let g_G₁₂_X₃ : G₁₂.coe ≃g ((⊤ : G.Subgraph).induce X₃).coe := by
        rw [h_X₃_G₁₂]
        exact isoToSubgraphByComposition G₁ G₁₂
      Nonempty.intro ((g_F₂_G₁₂.trans g_G₁₂_X₃).trans h_X₃_H₃.some)

    have h_F₁_disj_F₂ : F₁.verts ∩ F₂.verts = ∅ := subgraphFromIso_preserve_disjointedness h_G₁_Fout.some G₁₁ G₁₂ h_G₁₁_disj_G₁₂

    let X : Finset (Fin ℓ) := X₅
    have h_X_card : X.card = ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) := h_X₅_card
    have h_X_subset_compl_G₁_G₂ : X ⊆ (G₁.verts ∪ G₂.verts)ᶜ.toFinset := by
      rw [h_G₁_verts_eq_X₂₃₄, h_G₂_verts_eq_X₁]
      simp only [Set.toFinset_union, Set.toFinset_compl, toFinset_coe]
      rw [Finset.union_comm X₂₃₄ X₁]
      rw [←Finset.union_assoc X₁ (X₂ ∪ X₃) X₄]
      rw [←Finset.union_assoc X₁ X₂ X₃]
      intro v h_v_X₅
      rw [Finset.mem_compl]
      intro h_v_X₁_X₂_X₃_X₄
      have : v ∈ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ :=
        Finset.mem_inter.mpr ⟨h_v_X₁_X₂_X₃_X₄, h_v_X₅⟩
      rw [h_X₁_to_X₄_disj_X₅] at this
      exact (Finset.notMem_empty v) this

    use ⟨⟨F, ⟨F₁, F₂, G₁, G₂, X⟩⟩,
          h_F₁_ind, h_F₁_H₂, h_F₂_ind, h_F₂_H₃, h_F₁_disj_F₂,
          h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₁, h_G₁_disj_G₂,
          h_X_card, h_X_subset_compl_G₁_G₂⟩

    dsimp only [f_S₃_S₂_fwd, F₁, F₂, X, subgraphFromIso]
    simp only [Subtype.mk.injEq, Prod.mk.injEq]

    rw [h_G₁₁_verts_eq_X₂]
    rw [h_G₁₂_verts_eq_X₃]
    rw [h_G₂_verts_eq_X₁]
    simp only [Finset.toFinset_coe, true_and]
    simp only [←Set.image_union, ←Set.image_compl_eq h_G₁_Fout.some.bijective]
    simp only [←Set.image_comp]
    have h_fn_eq : (Subtype.val ∘ ⇑h_G₁_Fout.some.symm) ∘ ⇑h_G₁_Fout.some = Subtype.val := by
      ext u
      simp only [Function.comp_apply, RelIso.symm_apply_apply]
    rw [h_fn_eq]
    simp only [and_true]


    refine ⟨?_, ?_, ?_⟩ <;> ext u <;> simp
    . intro h_u_X₂; exact h_X₂_subset_X₂₃₄ h_u_X₂
    . intro h_u_X₃; exact h_X₃_subset_X₂₃₄ h_u_X₃
    . constructor
      . rintro ⟨⟨h_u_not_X₂, h_u_not_X₃⟩, h_u⟩
        rw [h_G₁_verts_eq_X₂₃₄, mem_coe] at h_u
        simp only [union_assoc, mem_union, not_or, X₂₃₄] at h_u
        rcases h_u with ⟨h_u₁ | h_u₁ | h_u₁, h_u₂⟩
        · exact (h_u_not_X₃ h_u₁ h_u_not_X₂).elim
        · exact ((h_u₂ h_u₁).2.1 h_u₁).elim
        · exact h_u₁
      . intro h_u_X₄
        rw [h_G₁_verts_eq_X₂₃₄, mem_coe]
        simp only [X₂₃₄, union_assoc, mem_union]
        refine ⟨?_, ?_⟩
        · have h_u_not_X₂ : u ∉ X₂ := by
            intro h_u_X₂
            have : u ∈ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ := by
              simp only [union_assoc, mem_inter, mem_union,
                h_u_X₂, true_or, or_true, h_u_X₄, and_self]
            rw [h_X₁_to_X₃_disj_X₄] at this
            exact Finset.notMem_empty u this
          have h_u_not_X₃ : u ∉ X₃ := by
            intro h_u_X₃
            have : u ∈ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ := Finset.mem_inter.mpr ⟨Finset.subset_union_right h_u_X₃, h_u_X₄⟩
            rw [h_X₁_to_X₃_disj_X₄] at this
            exact Finset.notMem_empty u this
          exact ⟨.inr (.inr h_u_X₄), by tauto⟩
        · simp only [h_u_X₄, or_true, not_true_eq_false, imp_false, true_and]
          intro h_u_X₃
          suffices h : u ∈ (X₂ ∪ X₃) ∩ X₄ by rw [h_X₂_X₃_disj_X₄] at h; exact notMem_empty _ h
          simp only [mem_inter, mem_union, h_u_X₃, or_true, true_and, h_u_X₄]

  let f_S₃_S₂ : S₃ ≃ S₂ := Equiv.ofBijective f_S₃_S₂_fwd ⟨h_f_S₃_S₂_inj, h_f_S₃_S₂_surj⟩

  exact f_S₃_S₂.symm


/-- The composite bijection (via `step1` and `step2`) witnessing that nesting
`(H₁,H₂)` then `H₃` is equinumerous to nesting `(H₂,H₃)` then `H₁`; the
combinatorial core of pair-density associativity. -/
noncomputable def subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    : (F : QuotSimpleGraph (Fin ℓ₁₂))
        × (Fpair : subgraphPairSet H₁ H₂ F.out)
        × subgraphPairSet F.out H₃ G
        × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset
      ≃
      (F : QuotSimpleGraph (Fin ℓ₂₃))
        × subgraphPairSet H₂ H₃ F.out
        × (Gpair : subgraphPairSet F.out H₁ G)
        × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset
  := by

  let S₀ := (F : QuotSimpleGraph (Fin ℓ₁₂))
              × (Fpair : subgraphPairSet H₁ H₂ F.out)
              × subgraphPairSet F.out H₃ G
              × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset

  let S₁ := { ⟨F, F₁, F₂, G₁, G₂, X⟩ :  (F : QuotSimpleGraph (Fin ℓ₁₂))
                                      × Subgraph F.out × Subgraph F.out
                                      × Subgraph G × Subgraph G
                                      × Finset (Fin ℓ₁₂)
                  | F₁.IsInduced
                  ∧ Nonempty (F₁.coe ≃g H₁)
                  ∧ F₂.IsInduced
                  ∧ Nonempty (F₂.coe ≃g H₂)
                  ∧ F₁.verts ∩ F₂.verts = ∅
                  ∧ G₁.IsInduced
                  ∧ Nonempty (G₁.coe ≃g F.out)
                  ∧ G₂.IsInduced
                  ∧ Nonempty (G₂.coe ≃g H₃)
                  ∧ G₁.verts ∩ G₂.verts = ∅
                  ∧ X.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ X ⊆ (F₁.verts ∪ F₂.verts)ᶜ.toFinset }

  let S₂ := { ⟨X₁, X₂, X₃, X₄, X₅⟩ :  Finset (Fin ℓ) × Finset (Fin ℓ)
                                    × Finset (Fin ℓ) × Finset (Fin ℓ) × Finset (Fin ℓ)
                  | X₁ ∩ X₂ = ∅
                  ∧ (X₁ ∪ X₂) ∩ X₃ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃) ∩ X₄ = ∅
                  ∧ (X₁ ∪ X₂ ∪ X₃ ∪ X₄) ∩ X₅ = ∅
                  ∧ X₁.card = ℓ₁
                  ∧ X₂.card = ℓ₂
                  ∧ X₃.card = ℓ₃
                  ∧ X₄.card = ℓ₂₃ - (ℓ₂ + ℓ₃)
                  ∧ X₅.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₁).coe ≃g H₁)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₂).coe ≃g H₂)
                  ∧ Nonempty (((⊤ : G.Subgraph).induce X₃).coe ≃g H₃) }

  let S₃ := { ⟨F, F₁, F₂, G₁, G₂, X⟩ :  (F : QuotSimpleGraph (Fin ℓ₂₃))
                                      × Subgraph F.out × Subgraph F.out
                                      × Subgraph G × Subgraph G
                                      × Finset (Fin ℓ)
                  | F₁.IsInduced
                  ∧ Nonempty (F₁.coe ≃g H₂)
                  ∧ F₂.IsInduced
                  ∧ Nonempty (F₂.coe ≃g H₃)
                  ∧ F₁.verts ∩ F₂.verts = ∅
                  ∧ G₁.IsInduced
                  ∧ Nonempty (G₁.coe ≃g F.out)
                  ∧ G₂.IsInduced
                  ∧ Nonempty (G₂.coe ≃g H₁)
                  ∧ G₁.verts ∩ G₂.verts = ∅
                  ∧ X.card = (ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)
                  ∧ X ⊆ (G₁.verts ∪ G₂.verts)ᶜ.toFinset }

  let S₄ := (F : QuotSimpleGraph (Fin ℓ₂₃))
              × subgraphPairSet H₂ H₃ F.out
              × (Gpair : subgraphPairSet F.out H₁ G)
              × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset

  let f_S₀_S₁_fwd : S₀ → S₁ := by
    intro ⟨F, ⟨⟨F₁, F₂⟩, h_F₁_F₂⟩, ⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, ⟨X, h_X⟩⟩
    refine ⟨⟨F, F₁, F₂, G₁, G₂, X⟩, ?_⟩
    rw [pair_mem_subgraphPairSet_iff] at h_F₁_F₂
    have ⟨h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂⟩ := h_F₁_F₂
    rw [pair_mem_subgraphPairSet_iff] at h_G₁_G₂
    have ⟨h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂⟩ := h_G₁_G₂
    have ⟨h_X_subset, h_X_card⟩ := Finset.mem_powersetCard.mp h_X
    exact ⟨h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂,
            h_X_card, h_X_subset⟩

  have h_f_S₀_S₁_inj : Function.Injective f_S₀_S₁_fwd := by
    intro ⟨F, ⟨⟨F₁, F₂⟩, h_F₁_F₂⟩, ⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, ⟨X, h_X⟩⟩
      ⟨F', ⟨⟨F₁', F₂'⟩, h_F₁'_F₂'⟩, ⟨⟨G₁', G₂'⟩, h_G₁'_G₂'⟩, ⟨X', h_X'⟩⟩
      h_eq
    simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, f_S₀_S₁_fwd] at h_eq
    obtain ⟨rfl, h_eq_rest⟩ := h_eq
    simp only [heq_eq_eq, Prod.mk.injEq] at h_eq_rest
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h_eq_rest
    rfl

  have h_f_S₀_S₁_surj : Function.Surjective f_S₀_S₁_fwd := by
    intro ⟨⟨F, F₁, F₂, G₁, G₂, X⟩,
            h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂,
            h_X_card, h_X_F₁_F₂⟩
    have h_F₁_F₂ : ⟨F₁, F₂⟩ ∈ subgraphPairSet H₁ H₂ F.out := by
      rw [pair_mem_subgraphPairSet_iff]
      exact ⟨h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂⟩
    have h_G₁_G₂ : ⟨G₁, G₂⟩ ∈ subgraphPairSet F.out H₃ G := by
      rw [pair_mem_subgraphPairSet_iff]
      exact ⟨h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂⟩
    have h_X : X ∈ powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((F₁.verts ∪ F₂.verts)ᶜ).toFinset :=
      Finset.mem_powersetCard.mpr ⟨h_X_F₁_F₂, h_X_card⟩
    use ⟨F, ⟨⟨F₁, F₂⟩, h_F₁_F₂⟩, ⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, ⟨X, h_X⟩⟩

  let f_S₀_S₁ : S₀ ≃ S₁ := Equiv.ofBijective f_S₀_S₁_fwd ⟨h_f_S₀_S₁_inj, h_f_S₀_S₁_surj⟩

  let f_S₁_S₂ : S₁ ≃ S₂ :=
    subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet_step1
      H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h

  let f_S₂_S₃ : S₂ ≃ S₃ :=
    subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet_step2
      H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h

  let f_S₄_S₃_fwd : S₄ → S₃ := by
    intro ⟨F, ⟨⟨F₁, F₂⟩, h_F₁_F₂⟩, ⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, ⟨X, h_X⟩⟩
    refine ⟨⟨F, F₁, F₂, G₁, G₂, X⟩, ?_⟩
    rw [pair_mem_subgraphPairSet_iff] at h_F₁_F₂
    have ⟨h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂⟩ := h_F₁_F₂
    rw [pair_mem_subgraphPairSet_iff] at h_G₁_G₂
    have ⟨h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂⟩ := h_G₁_G₂
    have ⟨h_X_subset, h_X_card⟩ := Finset.mem_powersetCard.mp h_X
    exact ⟨h_F₁_ind, h_F₁_H₁, h_F₂_ind, h_F₂_H₂, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₃, h_G₁_disj_G₂,
            h_X_card, h_X_subset⟩

  have h_f_S₄_S₃_inj : Function.Injective f_S₄_S₃_fwd := by
    intro ⟨F, ⟨⟨F₁, F₂⟩, h_F₁_F₂⟩, ⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, ⟨X, h_X⟩⟩
      ⟨F', ⟨⟨F₁', F₂'⟩, h_F₁'_F₂'⟩, ⟨⟨G₁', G₂'⟩, h_G₁'_G₂'⟩, ⟨X', h_X'⟩⟩
      h_eq
    simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, f_S₄_S₃_fwd] at h_eq
    obtain ⟨rfl, h_eq_rest⟩ := h_eq
    simp only [heq_eq_eq, Prod.mk.injEq] at h_eq_rest
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h_eq_rest
    rfl

  have h_f_S₄_S₃_surj : Function.Surjective f_S₄_S₃_fwd := by
    intro ⟨⟨F, F₁, F₂, G₁, G₂, X⟩,
            h_F₁_ind, h_F₁_H₂, h_F₂_ind, h_F₂_H₃, h_F₁_disj_F₂,
            h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₁, h_G₁_disj_G₂,
            h_X_card, h_X_F₁_F₂⟩
    have h_F₁_F₂ : ⟨F₁, F₂⟩ ∈ subgraphPairSet H₂ H₃ F.out := by
      rw [pair_mem_subgraphPairSet_iff]
      exact ⟨h_F₁_ind, h_F₁_H₂, h_F₂_ind, h_F₂_H₃, h_F₁_disj_F₂⟩
    have h_G₁_G₂ : ⟨G₁, G₂⟩ ∈ subgraphPairSet F.out H₁ G := by
      rw [pair_mem_subgraphPairSet_iff]
      exact ⟨h_G₁_ind, h_G₁_Fout, h_G₂_ind, h_G₂_H₁, h_G₁_disj_G₂⟩
    have h_X : X ∈ powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((G₁.verts ∪ G₂.verts)ᶜ).toFinset :=
      Finset.mem_powersetCard.mpr ⟨h_X_F₁_F₂, h_X_card⟩
    use ⟨F, ⟨⟨F₁, F₂⟩, h_F₁_F₂⟩, ⟨⟨G₁, G₂⟩, h_G₁_G₂⟩, ⟨X, h_X⟩⟩

  let f_S₄_S₃ : S₄ ≃ S₃ := Equiv.ofBijective f_S₄_S₃_fwd ⟨h_f_S₄_S₃_inj, h_f_S₄_S₃_surj⟩

  exact ((f_S₀_S₁.trans f_S₁_S₂).trans f_S₂_S₃).trans f_S₄_S₃.symm


/-- Counting form of pair-density associativity: the two nesting orders of three
labelled graphs give equal weighted sums of pair counts (proved by the composite
bijection above). -/
lemma subgraphPairCount_sum_assoc
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out
          * subgraphPairCount F.out H₃ G
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out
          * subgraphPairCount F.out H₁ G
          * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  := by
  let f_LHS (F : QuotSimpleGraph (Fin ℓ₁₂)) :=
    (Fpair : subgraphPairSet H₁ H₂ F.out)
    × subgraphPairSet F.out H₃ G
    × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset
  let f_RHS (F : QuotSimpleGraph (Fin ℓ₂₃)) :=
    subgraphPairSet H₂ H₃ F.out
    × (Gpair : subgraphPairSet F.out H₁ G)
    × powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset
  have h_iso : (F : QuotSimpleGraph (Fin ℓ₁₂)) × f_LHS F ≃ (F : QuotSimpleGraph (Fin ℓ₂₃)) × f_RHS F :=
    subgraphPairSet_union_quotSimpleGraphSet_iso_union_quotSimpleGraphSet
      H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h

  have h_LHS : ∀ (F : QuotSimpleGraph (Fin ℓ₁₂)),
                Fintype.card (f_LHS F)
                =
                subgraphPairCount H₁ H₂ F.out
                * subgraphPairCount F.out H₃ G
                * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
    := by
    intro F
    have h₁ : ∀ (Fpair : subgraphPairSet H₁ H₂ F.out),
                Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset)
                = (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
      := by
      intro Fpair
      calc
        Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset)
        _ = (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset).card := by
                simp only [Fintype.card_coe]
        _ = ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                apply card_powersetCard
        _ = (Fpair.val.1.verts ∪ Fpair.val.2.verts).toFinsetᶜ.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [Set.toFinset_compl]
        _ = (Fintype.card (Fin ℓ₁₂) - (Fpair.val.1.verts ∪ Fpair.val.2.verts).toFinset.card).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                rw [Finset.card_compl (Fpair.val.1.verts ∪ Fpair.val.2.verts).toFinset]
        _ = (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                rw [subgraphPairSet_card_union_Finset Fpair.property]
                simp only [Fintype.card_fin]
    calc
      Fintype.card (f_LHS F)
      _ = ∑ (Fpair : subgraphPairSet H₁ H₂ F.out),
            Fintype.card (subgraphPairSet F.out H₃ G)
            * Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Fpair.val.1.verts ∪ Fpair.val.2.verts)ᶜ).toFinset) := by
                simp only [f_LHS, Fintype.card_sigma, Fintype.card_prod]
      _ = ∑ (_ : subgraphPairSet H₁ H₂ F.out),
            Fintype.card (subgraphPairSet F.out H₃ G)
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                simp only [h₁]
      _ = Fintype.card (subgraphPairSet H₁ H₂ F.out)
          * (Fintype.card (subgraphPairSet F.out H₃ G) * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) := by
                simp only [univ_eq_attach, Fintype.card_coe, sum_const, card_attach, smul_eq_mul]
      _ = Fintype.card (subgraphPairSet H₁ H₂ F.out)
          * Fintype.card (subgraphPairSet F.out H₃ G)
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                apply Eq.symm; apply mul_assoc
      _ = subgraphPairCount H₁ H₂ F.out
          * subgraphPairCount F.out H₃ G
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                simp only [Fintype.card_coe, subgraphPairCount]

  have h_RHS : ∀ (F : QuotSimpleGraph (Fin ℓ₂₃)),
                Fintype.card (f_RHS F)
                =
                subgraphPairCount H₂ H₃ F.out
                * subgraphPairCount F.out H₁ G
                * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃))
    := by
    intro F
    have h₁' : ∀ (Gpair : subgraphPairSet F.out H₁ G),
                Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset)
                = (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃))
      := by
      rintro ⟨⟨G₁, G₂⟩, Gpair_property⟩
      calc
        Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((G₁.verts ∪ G₂.verts)ᶜ).toFinset)
        _ = (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((G₁.verts ∪ G₂.verts)ᶜ).toFinset).card := by
                simp only [Fintype.card_coe]
        _ = ((G₁.verts ∪ G₂.verts)ᶜ).toFinset.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                apply card_powersetCard
        _ = (G₁.verts ∪ G₂.verts).toFinsetᶜ.card.choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [Set.toFinset_compl]
        _ = (Fintype.card (Fin ℓ) - (G₁.verts ∪ G₂.verts).toFinset.card).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                rw [Finset.card_compl (G₁.verts ∪ G₂.verts).toFinset]
        _ = (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                rw [subgraphPairSet_card_union_Finset Gpair_property]
                simp only [add_comm, Fintype.card_fin]
    calc
      Fintype.card (f_RHS F)
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * ∑ (Gpair : subgraphPairSet F.out H₁ G),
              Fintype.card (powersetCard ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) ((Gpair.val.1.verts ∪ Gpair.val.2.verts)ᶜ).toFinset) := by
                simp only [f_RHS, Fintype.card_sigma, Fintype.card_prod]
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * ∑ (_ : subgraphPairSet F.out H₁ G),
              (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [h₁']
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * (Fintype.card (subgraphPairSet F.out H₁ G) * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃))) := by
                simp only [Fintype.card_coe, univ_eq_attach, sum_const, card_attach, smul_eq_mul]
      _ = Fintype.card (subgraphPairSet H₂ H₃ F.out)
          * Fintype.card (subgraphPairSet F.out H₁ G)
          * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                symm; apply mul_assoc
      _ = subgraphPairCount H₂ H₃ F.out
          * subgraphPairCount F.out H₁ G
          * (ℓ - (ℓ₁ + ℓ₂₃)).choose ((ℓ₁₂ + ℓ₃) - (ℓ₁ + ℓ₂₃)) := by
                simp only [Fintype.card_coe, subgraphPairCount]

  calc
    ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), Fintype.card (f_LHS F) := by
              simp only [h_LHS]
    _ = Fintype.card ((F : QuotSimpleGraph (Fin ℓ₁₂)) × f_LHS F) :=
              Eq.symm Fintype.card_sigma
    _ = Fintype.card ((F : QuotSimpleGraph (Fin ℓ₂₃)) × f_RHS F) :=
              Fintype.card_congr h_iso
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), Fintype.card (f_RHS F) :=
              Fintype.card_sigma
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G
            * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
              simp only [h_RHS]


/-- The binomial coefficient as a rational quotient of factorials, valid because
`k! · (n-k)!` divides `n!`. -/
lemma choose_eq_factorial_div_factorial_rational
    {n k : ℕ} (h_k_n : k ≤ n) :
    (↑(n.choose k) : ℚ) = ((↑n.factorial / (↑k.factorial * ↑(n - k).factorial)) : ℚ)
  :=
  calc
    ↑(n.choose k)
    _ = (↑(n.factorial / (k.factorial * (n - k).factorial)) : ℚ) := by
        rw [Nat.choose_eq_factorial_div_factorial h_k_n]
    _ = (↑n.factorial / (↑k.factorial * ↑(n - k).factorial)) := by
        have h_dvd : (k.factorial * (n - k).factorial) ∣ n.factorial :=
          Nat.factorial_mul_factorial_dvd_factorial h_k_n
        simp only [h_dvd, Nat.cast_div_charZero, Nat.cast_mul]

/-- Density form of pair-density associativity: summing `d(H₁,H₂;F)·d(F,H₃;G)`
over `ℓ₁₂`-flags equals summing `d(H₂,H₃;F)·d(F,H₁;G)` over `ℓ₂₃`-flags. The
factorial bookkeeping is discharged by the custom `simp_choose_eq` tactic. -/
lemma subgraphPairDensity_sum_assoc
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G
  :=
  let C₁₂ : ℕ := (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₁₂_gt_0 : (↑C₁₂ : ℚ) > 0 := by
    have : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ₁₂ - (ℓ₁ + ℓ₂) := by omega
    simp only [gt_iff_lt, Nat.cast_pos, Nat.choose_pos this, C₁₂]
  have h_C₁₂_self_div_eq_1 : (↑C₁₂ : ℚ) / (↑C₁₂ : ℚ) = 1 :=
    div_self (ne_of_gt h_C₁₂_gt_0)

  let C₂₃ : ℕ := (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₂₃_gt_0 : (↑C₂₃ : ℚ) > 0 := by
    have : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ - (ℓ₁ + ℓ₂₃) := Nat.sub_le_sub_right hℓ₁₂_ub (ℓ₁ + ℓ₂₃)
    simp only [gt_iff_lt, Nat.cast_pos, Nat.choose_pos this, C₂₃]
  have h_C₂₃_self_div_eq_1 : (↑C₂₃ : ℚ) / (↑C₂₃ : ℚ) = 1 :=
    div_self (ne_of_gt h_C₂₃_gt_0)

  have h_C₁₂_C₂₃ :
      ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂
      = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃
    := by
    dsimp only [C₁₂, C₂₃]
    simp_choose_eq `h_choose
    rw [h_choose_lhs_0, h_choose_lhs_1, h_choose_lhs_2, h_choose_lhs_3, h_choose_lhs_4]
    rw [h_choose_rhs_0, h_choose_rhs_1, h_choose_rhs_2, h_choose_rhs_3, h_choose_rhs_4]
    ring_nf
    have h₁ : ℓ₁₂ - (ℓ₁ + ℓ₂) = ℓ₁₂ - ℓ₁ - ℓ₂ := by omega
    have h₂ : ℓ₁₂ - ℓ₁ - ℓ₂ - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega
    have h₃ : ℓ - ℓ₂₃ - ℓ₁ = ℓ - (ℓ₁ + ℓ₂₃) := by omega
    have h₄ : ℓ₂₃ - ℓ₂ - ℓ₃ = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega
    have h₅ : ℓ - (ℓ₁ + ℓ₂₃) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ - ℓ₁₂ - ℓ₃ := by omega
    rw [h₁, h₂, h₃, h₄, h₅]
    ring_nf

  calc
    ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairDensity H₁ H₂ F.out
            * subgraphPairDensity F.out H₃ G
            * (C₁₂ / C₁₂) := by
                simp only [h_C₁₂_self_div_eq_1, mul_one]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            (subgraphPairCount H₁ H₂ F.out / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂) : ℚ))
            * (subgraphPairCount F.out H₃ G / ((ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃) : ℚ))
            * (C₁₂ / C₁₂) := by
                simp only [subgraphPairDensity, Fintype.card_fin, Nat.cast_mul]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            (subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G * ↑C₁₂)
            / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                simp only [div_mul_div_comm, mul_assoc]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G * ↑C₁₂)
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                apply Eq.symm; simp only [Nat.cast_sum, Nat.cast_mul, sum_div]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out
            * subgraphPairCount F.out H₃ G
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)))
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
            * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, C₁₂]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G
            * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)))
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
            * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) : ℚ) := by
                rw [subgraphPairCount_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h]
    _  = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
        / (↑(ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, C₂₃, C₁₂]
    _  = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * ↑C₂₃)
        / (↑(ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃) : ℚ) := by
                rw [h_C₁₂_C₂₃]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          (subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
          / (↑(ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, sum_div]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          (subgraphPairCount H₂ H₃ F.out / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃) : ℚ))
          * (subgraphPairCount F.out H₁ G / ((ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁) : ℚ))
          * (C₂₃ / C₂₃) := by
                simp only [mul_assoc, Nat.cast_mul, div_mul_div_comm]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
                simp only [h_C₂₃_self_div_eq_1, mul_one, subgraphPairDensity, Fintype.card_fin, Nat.cast_mul]

/-
 - Hongseok: What follows is the previous proof of subgraphPairDensity_sum_assoc that does not use our custom tactic simp_choose_eq.
 - We keep this old proof since it may be useful for explaining the benefit of our tactic in our future paper or presentation.
 -
lemma subgraphPairDensity_sum_assoc
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G
  :=
  let C₁₂ : ℚ := (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₁₂_gt_0 : C₁₂ > 0 := by
    have : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ₁₂ - (ℓ₁ + ℓ₂) := by omega
    simp only [gt_iff_lt, Nat.cast_pos, Nat.choose_pos this, C₁₂]
  have h_C₁₂_self_div_eq_1 : C₁₂ / C₁₂ = 1 :=
    div_self (ne_of_gt h_C₁₂_gt_0)

  let C₂₃ : ℚ := (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))
  have h_C₂₃_gt_0 : C₂₃ > 0 := by
    have : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ - (ℓ₁ + ℓ₂₃) := Nat.sub_le_sub_right hℓ₁₂_ub (ℓ₁ + ℓ₂₃)
    simp only [gt_iff_lt, Nat.cast_pos, Nat.choose_pos this, C₂₃]
  have h_C₂₃_self_div_eq_1 : C₂₃ / C₂₃ = 1 :=
    div_self (ne_of_gt h_C₂₃_gt_0)

  have h_C₁₂_C₂₃ : ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂
                    = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃ := by
    have h₁ : ℓ₁ ≤ ℓ₁₂ := by linarith
    have h₂ : ℓ₂ ≤ ℓ₁₂ - ℓ₁ := (Nat.le_sub_iff_add_le' h₁).mpr hℓ₁₂_lb
    have h₃ : ℓ₁₂ ≤ ℓ := by linarith
    have h₄ : ℓ₃ ≤ ℓ - ℓ₁₂ := (Nat.le_sub_iff_add_le' h₃).mpr hℓ₁₂_ub
    have h₅ : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ₁₂ - (ℓ₁ + ℓ₂) := by
      apply (Nat.le_sub_iff_add_le' hℓ₁₂_lb).mpr
      rw [←Nat.add_sub_assoc h (ℓ₁ + ℓ₂)]
      apply Nat.sub_le_of_le_add
      linarith
    have h₁' : ℓ₂ ≤ ℓ₂₃ := by linarith
    have h₂' : ℓ₃ ≤ ℓ₂₃ - ℓ₂ := (Nat.le_sub_iff_add_le' h₁').mpr hℓ₂₃_lb
    have h₃' : ℓ₂₃ ≤ ℓ := by linarith
    have h₄' : ℓ₁ ≤ ℓ - ℓ₂₃ := by apply (Nat.le_sub_iff_add_le' h₃').mpr; linarith
    have h₅' : ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃) ≤ ℓ - (ℓ₁ + ℓ₂₃) := by
      apply (Nat.le_sub_iff_add_le' hℓ₂₃_ub).mpr
      rw [←Nat.add_sub_assoc h (ℓ₁ + ℓ₂₃)]
      apply Nat.sub_le_of_le_add
      linarith
    -- simp_choose_eq `h_choose
    calc
      ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂
      _ = ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
          * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃
          * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
                dsimp [C₁₂]
      _ = (↑ℓ₁₂.factorial / (↑ℓ₁.factorial * ↑(ℓ₁₂ - ℓ₁).factorial))
          * (↑(ℓ₁₂ - ℓ₁).factorial / (↑ℓ₂.factorial * ↑(ℓ₁₂ - ℓ₁ - ℓ₂).factorial))
          * (↑ℓ.factorial / (↑ℓ₁₂.factorial * ↑(ℓ - ℓ₁₂).factorial))
          * (↑(ℓ - ℓ₁₂).factorial / (↑ℓ₃.factorial * ↑(ℓ - ℓ₁₂ - ℓ₃).factorial))
          * (↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))).factorial)) := by
                rw [choose_eq_factorial_div_factorial_rational h₁]
                rw [choose_eq_factorial_div_factorial_rational h₂]
                rw [choose_eq_factorial_div_factorial_rational h₃]
                rw [choose_eq_factorial_div_factorial_rational h₄]
                rw [choose_eq_factorial_div_factorial_rational h₅]
      _ = (↑ℓ₁₂.factorial / (↑ℓ₁.factorial * ↑(ℓ₁₂ - ℓ₁).factorial))
          * (↑(ℓ₁₂ - ℓ₁).factorial / (↑ℓ₂.factorial * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial))
          * (↑ℓ.factorial / (↑ℓ₁₂.factorial * ↑(ℓ - ℓ₁₂).factorial))
          * (↑(ℓ - ℓ₁₂).factorial / (↑ℓ₃.factorial * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial))
          * (↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial)) := by
                have : ℓ₁₂ - ℓ₁ - ℓ₂ = ℓ₁₂ - (ℓ₁ + ℓ₂) := by omega
                rw [this]
                have : ℓ - ℓ₁₂ - ℓ₃ = ℓ - (ℓ₁₂ + ℓ₃) := by omega
                rw [this]
                have : ℓ₁₂ - (ℓ₁ + ℓ₂) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega
                rw [this]
      _ = (↑ℓ₁₂.factorial
            * ↑(ℓ₁₂ - ℓ₁).factorial
            * ↑ℓ.factorial
            * ↑(ℓ - ℓ₁₂).factorial
            * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial)
          / (↑ℓ₁.factorial
              * ↑(ℓ₁₂ - ℓ₁).factorial
              * ↑ℓ₂.factorial
              * ↑(ℓ₁₂ - (ℓ₁ + ℓ₂)).factorial
              * ↑ℓ₁₂.factorial
              * ↑(ℓ - ℓ₁₂).factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial) := by
                simp only [div_mul_div_comm, mul_assoc, Nat.cast_mul]
      _ = ↑ℓ.factorial
          / (↑ℓ₁.factorial
              * ↑ℓ₂.factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial) := by
              field_simp
              ring
        _ = ↑ℓ.factorial
          / (↑ℓ₂.factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial
              * ↑ℓ₁.factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial) := by
              ring
      _ = (↑ℓ₂₃.factorial
            * ↑(ℓ₂₃ - ℓ₂).factorial
            * ↑ℓ.factorial
            * ↑(ℓ - ℓ₂₃).factorial
            * ↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial)
          / (↑ℓ₂.factorial
              * ↑(ℓ₂₃ - ℓ₂).factorial
              * ↑ℓ₃.factorial
              * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial
              * ↑ℓ₂₃.factorial
              * ↑(ℓ - ℓ₂₃).factorial
              * ↑ℓ₁.factorial
              * ↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial
              * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial) := by
              field_simp
              ring
      _ = (↑ℓ₂₃.factorial / (↑ℓ₂.factorial * ↑(ℓ₂₃ - ℓ₂).factorial))
          * (↑(ℓ₂₃ - ℓ₂).factorial / (↑ℓ₃.factorial * ↑(ℓ₂₃ - (ℓ₂ + ℓ₃)).factorial))
          * (↑ℓ.factorial / (↑ℓ₂₃.factorial * ↑(ℓ - ℓ₂₃).factorial))
          * (↑(ℓ - ℓ₂₃).factorial / (↑ℓ₁.factorial * ↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial))
          * (↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial * ↑(ℓ - (ℓ₁₂ + ℓ₃)).factorial)) := by
              simp only [div_mul_div_comm, mul_assoc, Nat.cast_mul]
      _ = (↑ℓ₂₃.factorial / (↑ℓ₂.factorial * ↑(ℓ₂₃ - ℓ₂).factorial))
          * (↑(ℓ₂₃ - ℓ₂).factorial / (↑ℓ₃.factorial * ↑(ℓ₂₃ - ℓ₂ - ℓ₃).factorial))
          * (↑ℓ.factorial / (↑ℓ₂₃.factorial * ↑(ℓ - ℓ₂₃).factorial))
          * (↑(ℓ - ℓ₂₃).factorial / (↑ℓ₁.factorial * ↑(ℓ - ℓ₂₃ - ℓ₁).factorial))
          * (↑(ℓ - (ℓ₁ + ℓ₂₃)).factorial / (↑(ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)).factorial * ↑(ℓ - (ℓ₁ + ℓ₂₃) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))).factorial)) := by
              have : ℓ₂₃ - ℓ₂ - ℓ₃ = ℓ₂₃ - (ℓ₂ + ℓ₃) := by omega
              rw [this]
              have : ℓ - ℓ₂₃ - ℓ₁ = ℓ - (ℓ₁ + ℓ₂₃) := by omega
              rw [this]
              have : ℓ - (ℓ₁ + ℓ₂₃) - (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) = ℓ - (ℓ₁₂ + ℓ₃) := by omega
              rw [this]
      _ = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)) := by
              rw [choose_eq_factorial_div_factorial_rational h₁']
              rw [choose_eq_factorial_div_factorial_rational h₂']
              rw [choose_eq_factorial_div_factorial_rational h₃']
              rw [choose_eq_factorial_div_factorial_rational h₄']
              rw [choose_eq_factorial_div_factorial_rational h₅']
      _ = ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃ := by
              dsimp [C₂₃]
  calc
    ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairDensity H₁ H₂ F.out
            * subgraphPairDensity F.out H₃ G
            * (C₁₂ / C₁₂) := by
                simp only [h_C₁₂_self_div_eq_1, mul_one]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            (subgraphPairCount H₁ H₂ F.out / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂) : ℚ))
            * (subgraphPairCount F.out H₃ G / ((ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃) : ℚ))
            * (C₁₂ / C₁₂) := by
                simp only [subgraphPairDensity, Fintype.card_fin, Nat.cast_mul]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            (subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G * C₁₂)
            / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                simp only [div_mul_div_comm, mul_assoc]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out * subgraphPairCount F.out H₃ G * C₁₂)
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                apply Eq.symm; apply sum_div
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
            subgraphPairCount H₁ H₂ F.out
            * subgraphPairCount F.out H₃ G
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)))
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
            * ℓ.choose ℓ₁₂  * (ℓ - ℓ₁₂).choose ℓ₃
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, C₁₂]
    _ = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G
            * (ℓ - (ℓ₁ + ℓ₂₃)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃)))
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂
            * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃
            * (ℓ₁₂ - (ℓ₁ + ℓ₂)).choose (ℓ₁₂ + ℓ₃ - (ℓ₁ + ℓ₂₃))) : ℚ) := by
                rw [subgraphPairCount_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h]
    _  = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
        / ((ℓ₁₂.choose ℓ₁ * (ℓ₁₂ - ℓ₁).choose ℓ₂ * ℓ.choose ℓ₁₂ * (ℓ - ℓ₁₂).choose ℓ₃ * C₁₂) : ℚ) := by
                simp only [Nat.cast_sum, Nat.cast_mul, C₂₃, C₁₂]
    _  = (∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
            subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
        / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃) : ℚ) := by
                rw [h_C₁₂_C₂₃]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          (subgraphPairCount H₂ H₃ F.out * subgraphPairCount F.out H₁ G * C₂₃)
          / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃ * ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁ * C₂₃) : ℚ) := by
                apply sum_div
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          (subgraphPairCount H₂ H₃ F.out / ((ℓ₂₃.choose ℓ₂ * (ℓ₂₃ - ℓ₂).choose ℓ₃) : ℚ))
          * (subgraphPairCount F.out H₁ G / ((ℓ.choose ℓ₂₃ * (ℓ - ℓ₂₃).choose ℓ₁) : ℚ))
          * (C₂₃ / C₂₃) := by
                simp only [div_mul_div_comm, mul_assoc]
    _ = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
                simp only [h_C₂₃_self_div_eq_1, mul_one, subgraphPairDensity, Fintype.card_fin, Nat.cast_mul]
-/


lemma subgraphPairDensityLifted_sum_assoc'
    (H₁ : SimpleGraph (Fin ℓ₁)) (H₂ : SimpleGraph (Fin ℓ₂)) (H₃ : SimpleGraph (Fin ℓ₃)) (G : SimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)),
          subgraphPairDensityLifted H₁ H₂ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)),
          subgraphPairDensityLifted H₂ H₃ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧
  := by
  have h₀ : ∀ {F : QuotSimpleGraph (Fin ℓ₁₂)},
              subgraphPairDensityLifted H₁ H₂ F * subgraphPairDensityLifted F.out H₃ ⟦G⟧
              = subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G := by
    intro F
    calc
      subgraphPairDensityLifted H₁ H₂ F * subgraphPairDensityLifted F.out H₃ ⟦G⟧
      _ = subgraphPairDensityLifted H₁ H₂ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧ := by simp only [Quotient.out_eq]
      _ = @Quot.lift _ graph_eqv _ (subgraphPairDensity H₁ H₂) ?h₀' ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₁ H₂ F.out * subgraphPairDensityLifted F.out H₃ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₁ H₂ F.out * @Quot.lift _ graph_eqv _ (subgraphPairDensity F.out H₃) ?h₀'' ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G := by rfl
    . intro F₀ F₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G H₁ H₂ h_eqv
    . intro G₀ G₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G F.out H₃ h_eqv
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensityLifted H₁ H₂ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₃ ⟦G⟧
              = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), subgraphPairDensity H₁ H₂ F.out * subgraphPairDensity F.out H₃ G := by
    simp only [Quotient.out_eq, h₀]
  rw [h_LHS]

  have h₁ : ∀ {F : QuotSimpleGraph (Fin ℓ₂₃)},
              subgraphPairDensityLifted H₂ H₃ F * subgraphPairDensityLifted F.out H₁ ⟦G⟧
              = subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
    intro F
    calc
      subgraphPairDensityLifted H₂ H₃ F * subgraphPairDensityLifted F.out H₁ ⟦G⟧
      _ = subgraphPairDensityLifted H₂ H₃ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧ := by simp only [Quotient.out_eq]
      _ = @Quot.lift _ graph_eqv _ (subgraphPairDensity H₂ H₃) ?h₁' ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₂ H₃ F.out * subgraphPairDensityLifted F.out H₁ ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₂ H₃ F.out * @Quot.lift _ graph_eqv _ (subgraphPairDensity F.out H₁) ?h₁'' ⟦G⟧ := by rfl
      _ = subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by rfl
    . intro F₀ F₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G H₂ H₃ h_eqv
    . intro G₀ G₁ h_eqv; exact subgraphPairDensity_respects_eqv_on_G F.out H₁ h_eqv
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensityLifted H₂ H₃ ⟦F.out⟧ * subgraphPairDensityLifted F.out H₁ ⟦G⟧
              = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), subgraphPairDensity H₂ H₃ F.out * subgraphPairDensity F.out H₁ G := by
    simp only [Quotient.out_eq, h₁]
  rw [h_RHS]

  exact subgraphPairDensity_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h


lemma quotSubgraphPairDensity_sum_assoc'
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    (h : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity F H₁ G
  := by
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ ⟦F.out⟧ * quotSubgraphPairDensity ⟦F.out⟧ H₃ G
    := by simp
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity F H₁ G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ ⟦F.out⟧ * quotSubgraphPairDensity ⟦F.out⟧ H₁ G
    := by simp
  rw [h_LHS, h_RHS]

  rcases Quotient.exists_rep H₁ with ⟨H₁rep, hH₁rep⟩
  rcases Quotient.exists_rep H₂ with ⟨H₂rep, hH₂rep⟩
  rcases Quotient.exists_rep H₃ with ⟨H₃rep, hH₃rep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  rw [← hH₁rep, ← hH₂rep, ← hH₃rep, ← hGrep]
  exact subgraphPairDensityLifted_sum_assoc' H₁rep H₂rep H₃rep Grep hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h


/-- Quotient-level associativity of pair densities: the value is independent of
which pair of the three labelled graphs is grouped first. -/
lemma quotSubgraphPairDensity_sum_assoc
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    (hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂) (hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ)
    (hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃) (hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ)
    :   ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
  := by
  by_cases h_ge : ℓ₁₂ + ℓ₃ ≥ ℓ₁ + ℓ₂₃
  {
    have h_comm : ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
                  = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity F H₁ G
      := quotSubgraphPairDensity_sum_assoc' H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub h_ge
    rw [h_comm]
    have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₂₃))), quotSubgraphPairDensity F H₁ G = quotSubgraphPairDensity H₁ F G := by
      intro F
      rw [quotSubgraphPairDensity_comm F H₁ G]
    simp only [h]
  }
  {
    have h₀' : ∀ (F : QuotSimpleGraph (Fin (ℓ₂₃))),
               quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
                = quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity F H₁ G := by
        intro F
        rw [quotSubgraphPairDensity_comm F H₁ G, quotSubgraphPairDensity_comm H₂ H₃ F]
    have h_comm₀' :  ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
                   = ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity F H₁ G := by
      simp only [h₀']
    rw [h_comm₀']

    have h₁' : ∀ (F : QuotSimpleGraph (Fin (ℓ₁₂))), quotSubgraphPairDensity H₁ H₂ F = quotSubgraphPairDensity H₂ H₁ F := by
      intro F
      rw [quotSubgraphPairDensity_comm H₁ H₂ F]
    have h_comm₁' :  ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
                   = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₂ H₁ F * quotSubgraphPairDensity F H₃ G := by
      simp only [h₁']
    rw [h_comm₁']

    have h_ge' : ℓ₂₃ + ℓ₁ ≥ ℓ₃ + ℓ₁₂ := by linarith [h_ge]
    have hℓ₃₂_lb : ℓ₃ + ℓ₂ ≤ ℓ₂₃ := by linarith [hℓ₂₃_lb]
    have hℓ₃₂_ub : ℓ₂₃ + ℓ₁ ≤ ℓ := by linarith [hℓ₂₃_ub]
    have hℓ₂₁_lb : ℓ₂ + ℓ₁ ≤ ℓ₁₂ := by linarith [hℓ₁₂_lb]
    have hℓ₂₁_ub : ℓ₃ + ℓ₁₂ ≤ ℓ := by linarith [hℓ₁₂_ub]
    have h_comm₂' :   ∑ (F : QuotSimpleGraph (Fin ℓ₂₃)), quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity F H₁ G
                    = ∑ (F : QuotSimpleGraph (Fin ℓ₁₂)), quotSubgraphPairDensity H₂ H₁ F * quotSubgraphPairDensity F H₃ G
      := quotSubgraphPairDensity_sum_assoc' H₃ H₂ H₁ G hℓ₃₂_lb hℓ₃₂_ub hℓ₂₁_lb hℓ₂₁_ub h_ge'
    rw [h_comm₂']
  }


/-- The triple density is invariant under cyclic permutation of its three
labelled graphs. -/
lemma quotSubgraphTripleDensity_comm
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    (h : ℓ₁ + ℓ₂ + ℓ₃ ≤ ℓ)
    : quotSubgraphTripleDensity H₁ H₂ H₃ G = quotSubgraphTripleDensity H₂ H₃ H₁ G
  := by
  dsimp only [quotSubgraphTripleDensity]

  have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₂ H₃ F = quotSubgraphPairDensity H₃ H₂ F := by
    intro F
    rw [quotSubgraphPairDensity_comm H₂ H₃ F]
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₂ H₃ F * quotSubgraphPairDensity H₁ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₂ + ℓ₃))), quotSubgraphPairDensity H₃ H₂ F * quotSubgraphPairDensity H₁ F G
    := by
    simp only [h]
  rw [h_LHS]

  have h' : ∀ (F : QuotSimpleGraph (Fin (ℓ₃ + ℓ₁))),
              quotSubgraphPairDensity H₃ H₁ F * quotSubgraphPairDensity H₂ F G
              = quotSubgraphPairDensity H₁ H₃ F * quotSubgraphPairDensity F H₂ G
    := by
    intro F
    rw [quotSubgraphPairDensity_comm H₃ H₁ F, quotSubgraphPairDensity_comm H₂ F G]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₃ + ℓ₁))), quotSubgraphPairDensity H₃ H₁ F * quotSubgraphPairDensity H₂ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₃ + ℓ₁))), quotSubgraphPairDensity H₁ H₃ F * quotSubgraphPairDensity F H₂ G
    := by
    simp only [h']
  rw [h_RHS]

  let ℓ₁₃ := ℓ₃ + ℓ₁
  let ℓ₃₂ := ℓ₂ + ℓ₃
  have hℓ₁₃_lb : ℓ₁ + ℓ₃ ≤ ℓ₁₃ := by dsimp only [ℓ₁₃]; linarith [h]
  have hℓ₁₃_ub : ℓ₁₃ + ℓ₂ ≤ ℓ := by dsimp only [ℓ₁₃]; linarith [h]
  have hℓ₃₂_lb : ℓ₃ + ℓ₂ ≤ ℓ₃₂ := by dsimp only [ℓ₃₂]; linarith [h]
  have hℓ₃₂_ub : ℓ₁ + ℓ₃₂ ≤ ℓ := by dsimp only [ℓ₃₂]; linarith [h]
  rw [quotSubgraphPairDensity_sum_assoc H₁ H₃ H₂ G hℓ₁₃_lb hℓ₁₃_ub hℓ₃₂_lb hℓ₃₂_ub]


/-- Chain rule for the triple density: expand it as a sum over `ℓ₄`-vertex flags
of `d(H₁,H₂;F)·d(F,H₃;G)`. Exported as `density_chain_rule''`. -/
theorem quotSubgraphTripleDensity_eq_sum_density_prods
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (H₃ : QuotSimpleGraph (Fin ℓ₃)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₄ : ℕ} (hℓ₄_lb : ℓ₁ + ℓ₂ ≤ ℓ₄) (hℓ₄_ub : ℓ₄ + ℓ₃ ≤ ℓ)
    : quotSubgraphTripleDensity H₁ H₂ H₃ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₄)), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
  := by
  rw [quotSubgraphTripleDensity_comm H₁ H₂ H₃ G (by linarith [hℓ₄_lb, hℓ₄_ub])]
  rw [quotSubgraphTripleDensity_comm H₂ H₃ H₁ G (by linarith [hℓ₄_lb, hℓ₄_ub])]
  dsimp only [quotSubgraphTripleDensity]

  have h : ∀ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₃ F G = quotSubgraphPairDensity F H₃ G := by
    intro F
    rw [quotSubgraphPairDensity_comm H₃ F G]
  have h_LHS :  ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity H₃ F G
              = ∑ (F : QuotSimpleGraph (Fin (ℓ₁ + ℓ₂))), quotSubgraphPairDensity H₁ H₂ F * quotSubgraphPairDensity F H₃ G
    := by
    simp only [h]
  rw [h_LHS]

  let ℓ₁₂ := ℓ₁ + ℓ₂
  have hℓ₁₂_lb : ℓ₁ + ℓ₂ ≤ ℓ₁₂ := by simp only [le_refl, ℓ₁₂]
  have hℓ₁₂_ub : ℓ₁₂ + ℓ₃ ≤ ℓ := by dsimp only [ℓ₁₂]; linarith [hℓ₄_lb, hℓ₄_ub]
  let ℓ₂₃ := ℓ₂ + ℓ₃
  have hℓ₂₃_lb : ℓ₂ + ℓ₃ ≤ ℓ₂₃ := by simp only [le_refl, ℓ₂₃]
  have hℓ₂₃_ub : ℓ₁ + ℓ₂₃ ≤ ℓ := by dsimp only [ℓ₂₃]; linarith [hℓ₄_lb, hℓ₄_ub]
  rw [quotSubgraphPairDensity_sum_assoc H₁ H₂ H₃ G hℓ₁₂_lb hℓ₁₂_ub hℓ₂₃_lb hℓ₂₃_ub]
  rw [quotSubgraphPairDensity_sum_assoc H₁ H₂ H₃ G hℓ₄_lb hℓ₄_ub hℓ₂₃_lb hℓ₂₃_ub]


/-- Variant chain rule: expand the pair density `d(H₁,H₂;G)` by inserting an
intermediate flag on the `H₁` side, as `d(H₁;F)·d(F,H₂;G)`. Exported as
`density_chain_rule'`. -/
theorem quotSubgraphPairDensity_eq_sum_density_prods'
    (H₁ : QuotSimpleGraph (Fin ℓ₁)) (H₂ : QuotSimpleGraph (Fin ℓ₂)) (G : QuotSimpleGraph (Fin ℓ))
    {ℓ₃ : ℕ} (hℓ₃_lb : ℓ₁ ≤ ℓ₃) (hℓ₃_ub : ℓ₃ + ℓ₂ ≤ ℓ)
    : quotSubgraphPairDensity H₁ H₂ G
      = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphDensity H₁ F * quotSubgraphPairDensity F H₂ G
  := by
  let H₀ : QuotSimpleGraph (Fin 0) := ⟦emptyGraph (Fin 0)⟧
  let h_lb : 0 + ℓ₁ ≤ ℓ₃ := by simp only [zero_add, hℓ₃_lb]

  have h_lb' : ℓ₁ + ℓ₂ ≤ ℓ := by linarith [hℓ₃_lb, hℓ₃_ub]
  have h_LHS : quotSubgraphTripleDensity H₀ H₁ H₂ G = quotSubgraphPairDensity H₁ H₂ G :=
    quotSubgraphTripleDensity_empty H₁ H₂ G h_lb'
  rw [←h_LHS]

  have h : ∀ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphPairDensity H₀ H₁ F = quotSubgraphDensity H₁ F := by
    intro F
    rw [quotSubgraphPairDensity_empty H₁ F]
  have h_RHS :  ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphDensity H₁ F * quotSubgraphPairDensity F H₂ G
              = ∑ (F : QuotSimpleGraph (Fin ℓ₃)), quotSubgraphPairDensity H₀ H₁ F * quotSubgraphPairDensity F H₂ G := by
    simp only [h]
  rw [h_RHS]

  exact quotSubgraphTripleDensity_eq_sum_density_prods H₀ H₁ H₂ G h_lb hℓ₃_ub


/-! ## Public chain-rule aliases

Short, stable names for the density chain-rule theorems, consumed by the
FlagAlgebra layer and the end-to-end extremal-bound proofs. -/

alias density_chain_rule := quotSubgraphPairDensity_eq_sum_density_prods
alias density_chain_rule' := quotSubgraphPairDensity_eq_sum_density_prods'
alias density_chain_rule'' := quotSubgraphTripleDensity_eq_sum_density_prods
alias density_chain_rule''' := quotSubgraphDensity_eq_sum_density_prods

end GraphAlgebras
