import «LeanFlagAlgebras».Differential.DeleteFinset

/-! # The hitting estimate (Razborov's (31))

Deleting few vertices barely moves rooted densities: for a `1`-flag `F` on
`k + 1` vertices, a rooted host `(N, v)` on `n` vertices and a set `W` of
`w` deleted vertices (not containing `v`),

`|p(F, (N,v)) − p(F, (N − W, v))| ≤ k·w/(n−1)`.

The proof compares subset counts: the inducing subsets of the deleted host
correspond to the inducing subsets of `(N, v)` avoiding `W`; the number of
*all* `v`-containing `(k+1)`-subsets is the normalising binomial `C(n−1,k)`,
those avoiding `W` number `C(n−1−w,k)`, and
`C(n−1,k) − C(n−1−w,k) ≤ w·C(n−2,k−1) = w·k·C(n−1,k)/(n−1)`. -/

namespace FlagAlgebras
namespace Differential

open Finset
open Classical

/-! ## Counting rooted subsets -/

/-- The number of subsets containing `v` of prescribed size inside
`insert v T` is a binomial coefficient. -/
theorem card_rooted_subsets {V : Type} [Fintype V] [DecidableEq V]
    (v : V) (T : Finset V) (hv : v ∉ T) (ℓ : ℕ)
    : ({S : Set V | v ∈ S ∧ S.toFinset.card = ℓ + 1 ∧ S.toFinset ⊆ insert v T} :
        Set (Set V)).toFinset.card = T.card.choose ℓ
  := by
  rw [← Finset.card_powersetCard ℓ T]
  apply Finset.card_bij (fun (S : Set V) (_ : S ∈ _) => S.toFinset.erase v)
  · intro S hS
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hS
    obtain ⟨hvS, hcard, hsub⟩ := hS
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [Finset.mem_erase] at hx
      have h1 := hsub hx.2
      rw [Finset.mem_insert] at h1
      rcases h1 with h2 | h2
      · exact absurd h2 hx.1
      · exact h2
    · rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hvS), hcard]
      simp only [Nat.add_sub_cancel]
  · intro S₁ h₁ S₂ h₂ heq
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at h₁ h₂
    have h3 : S₁.toFinset = S₂.toFinset := by
      have h4 : insert v (S₁.toFinset.erase v) = insert v (S₂.toFinset.erase v) := by
        rw [heq]
      rwa [Finset.insert_erase (Set.mem_toFinset.mpr h₁.1),
        Finset.insert_erase (Set.mem_toFinset.mpr h₂.1)] at h4
    have h5 := congrArg (fun t : Finset V => (↑t : Set V)) h3
    simpa [Set.coe_toFinset] using h5
  · intro T' hT'
    rw [Finset.mem_powersetCard] at hT'
    obtain ⟨hsub, hcard⟩ := hT'
    have hvT' : v ∉ T' := fun hc => hv (hsub hc)
    refine ⟨(↑(insert v T') : Set V), ?_, ?_⟩
    · simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_insert_self v T')
      · rw [Finset.toFinset_coe, Finset.card_insert_of_notMem hvT', hcard]
      · rw [Finset.toFinset_coe]
        exact Finset.insert_subset_insert v hsub
    · rw [Finset.toFinset_coe, Finset.erase_insert hvT']

/-! ## The binomial difference bound -/

theorem choose_le_choose_sub_add {a w k : ℕ}
    : a.choose (k + 1) ≤ (a - w).choose (k + 1) + w * (a - 1).choose k
  := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hstep : (a - w).choose (k + 1)
        ≤ (a - (w + 1)).choose (k + 1) + (a - 1).choose k := by
      rcases Nat.eq_zero_or_pos (a - w) with h0 | hpos
      · rw [h0]
        have h1 : a - (w + 1) = 0 := by omega
        rw [h1]
        simp
      · obtain ⟨m, hm⟩ : ∃ m, a - w = m + 1 := ⟨a - w - 1, by omega⟩
        rw [hm]
        have h2 : a - (w + 1) = m := by omega
        rw [h2, Nat.choose_succ_succ]
        have h3 : m.choose k ≤ (a - 1).choose k :=
          Nat.choose_le_choose k (by omega)
        calc m.choose k + m.choose (k + 1)
            ≤ (a - 1).choose k + m.choose (k + 1) := Nat.add_le_add_right h3 _
          _ = m.choose (k + 1) + (a - 1).choose k := Nat.add_comm _ _
    calc a.choose (k + 1) ≤ (a - w).choose (k + 1) + w * (a - 1).choose k := ih
      _ ≤ ((a - (w + 1)).choose (k + 1) + (a - 1).choose k) + w * (a - 1).choose k :=
          Nat.add_le_add_right hstep _
      _ = (a - (w + 1)).choose (k + 1) + (w + 1) * (a - 1).choose k := by ring

/-! ## Inducing subsets of the deleted rooted host -/

theorem mem_image_of_rooted_subset {V : Type} (N : LabeledGraph ∅ₜ V) (W : Finset V)
    (v : V) (hv : v ∉ W) (S' : Set {u : V // u ∉ W})
    (hsub' : (rootedAt (deleteFinset N W) ⟨v, hv⟩).type_verts ⊆ S')
    : v ∈ Subtype.val '' S'
  :=
  ⟨⟨v, hv⟩, mem_of_rootedAt_type_verts_subset _ _ hsub', rfl⟩

/-- Induced subgraphs of the deleted rooted host correspond to induced
subgraphs of the original rooted host on the image vertex set. -/
noncomputable def deleteFinset_rooted_induce_iso {V : Type} (N : LabeledGraph ∅ₜ V)
    (W : Finset V) (v : V) (hv : v ∉ W) (S' : Set {u : V // u ∉ W})
    (hsub' : (rootedAt (deleteFinset N W) ⟨v, hv⟩).type_verts ⊆ S')
    : (LabeledSubgraph.inducedLabeledSubgraph (rootedAt (deleteFinset N W) ⟨v, hv⟩) S' hsub').coe
      ≃f (LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) (Subtype.val '' S')
          (rootedAt_type_verts_subset N v
            (mem_image_of_rooted_subset N W v hv S' hsub'))).coe where
  graph_iso := {
    toFun := fun a => ⟨a.val.val, ⟨a.val, a.property, rfl⟩⟩
    invFun := fun b => ⟨⟨b.val, by
        obtain ⟨u, -, huv⟩ := b.property
        rw [← huv]
        exact u.property⟩, by
      obtain ⟨u, hu, huv⟩ := b.property
      have h1 : u = ⟨b.val, by
          obtain ⟨u', -, huv'⟩ := b.property
          rw [← huv']
          exact u'.property⟩ := Subtype.ext huv
      rw [← h1]
      exact hu⟩
    left_inv := fun a => rfl
    right_inv := fun b => rfl
    map_rel_iff' := by
      intro a b
      constructor
      · rintro ⟨_, _, h⟩
        exact ⟨a.property, b.property, h⟩
      · rintro ⟨_, _, h⟩
        exact ⟨⟨a.val, a.property, rfl⟩, ⟨b.val, b.property, rfl⟩, h⟩
  }
  type_preserve := by
    funext t
    rfl

/-- The inducing subsets of the deleted rooted host are exactly the
`W`-avoiding inducing subsets of the original rooted host. -/
theorem card_inducingSubsets_deleteFinset_rooted {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledGraph ∅ₜ V) (W : Finset V) (v : V) (hv : v ∉ W)
    {ℓF : ℕ} (F : FlagWithSize vertexType ℓF)
    : (inducingSubsets F.out (rootedAt (deleteFinset N W) ⟨v, hv⟩)).toFinset.card
      = ((inducingSubsets F.out (rootedAt N v)).toFinset.filter
          (fun S => ∀ x ∈ W, x ∉ S)).card
  := by
  apply Finset.card_bij (fun (S' : Set {u : V // u ∉ W}) (_ : S' ∈ _) => Subtype.val '' S')
  · intro S' hS'
    rw [Set.mem_toFinset] at hS'
    obtain ⟨hsub', ⟨ψ⟩⟩ := hS'
    rw [Finset.mem_filter]
    constructor
    · rw [Set.mem_toFinset]
      exact ⟨rootedAt_type_verts_subset N v (mem_image_of_rooted_subset N W v hv S' hsub'),
        ⟨(deleteFinset_rooted_induce_iso N W v hv S' hsub').symm.trans ψ⟩⟩
    · rintro x hxW ⟨u, -, rfl⟩
      exact u.property hxW
  · intro a _ b _ hab
    exact Set.image_injective.mpr Subtype.val_injective hab
  · intro S hS
    rw [Finset.mem_filter, Set.mem_toFinset] at hS
    obtain ⟨⟨hsub, ⟨ψ₀⟩⟩, havoid⟩ := hS
    have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set {u : V // u ∉ W}) = S := by
      ext u
      constructor
      · rintro ⟨⟨w', hw'⟩, hmem, rfl⟩
        exact hmem
      · intro hu
        have huW : u ∉ W := fun hc => havoid u hc hu
        exact ⟨⟨u, huW⟩, hu, rfl⟩
    have hsub' : (rootedAt (deleteFinset N W) ⟨v, hv⟩).type_verts ⊆
        (Subtype.val ⁻¹' S : Set {u : V // u ∉ W}) := by
      apply rootedAt_type_verts_subset
      show v ∈ S
      exact mem_of_rootedAt_type_verts_subset N v hsub
    refine ⟨Subtype.val ⁻¹' S, ?_, himg⟩
    rw [Set.mem_toFinset]
    refine ⟨hsub', ?_⟩
    have hsets : (LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v)
        (Subtype.val '' (Subtype.val ⁻¹' S : Set {u : V // u ∉ W}))
        (rootedAt_type_verts_subset N v
          (mem_image_of_rooted_subset N W v hv _ hsub')))
        = (LabeledSubgraph.inducedLabeledSubgraph (rootedAt N v) S hsub) := by
      apply labeledSubgraph_eq_from_subgraph_eq
      dsimp only [LabeledSubgraph.inducedLabeledSubgraph]
      rw [himg]
    exact ⟨((deleteFinset_rooted_induce_iso N W v hv _ hsub').trans
      (LabeledGraphIso.labeledSubgraphIso_eq hsets)).trans ψ₀⟩

/-! ## The hitting estimate -/

/-- Every inducing subset of a rooted host is a rooted subset of the right
size. -/
theorem inducingSubsets_rooted_mem {V : Type} [Fintype V] [DecidableEq V]
    (X : LabeledGraph ∅ₜ V) (v : V) {ℓF : ℕ} (F : FlagWithSize vertexType ℓF)
    (S : Set V) (hS : S ∈ inducingSubsets F.out (rootedAt X v))
    : v ∈ S ∧ S.toFinset.card = ℓF ∧ S.toFinset ⊆ insert v (Finset.univ.erase v)
  := by
  obtain ⟨hsub, ⟨ψ⟩⟩ := hS
  refine ⟨mem_of_rootedAt_type_verts_subset X v hsub, ?_, ?_⟩
  · have hsz := labeledGraphIso_size_eq _ _ ψ
    simp only [LabeledGraph.size, Fintype.card_fin] at hsz
    rw [Set.toFinset_card]
    exact hsz
  · intro x _
    rw [Finset.insert_erase (Finset.mem_univ v)]
    exact Finset.mem_univ x

/-- **Razborov's estimate (31)**: deleting `w` vertices (avoiding the root)
from an `n`-vertex rooted host moves the density of any `1`-flag on `k + 1`
vertices by at most `k·w/(n−1)`. -/
theorem hitting_rooted_density {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledGraph ∅ₜ V) (v : V) (W : Finset V) (hv : v ∉ W)
    {ℓF : ℕ} (F : FlagWithSize vertexType ℓF) (hℓF : 1 ≤ ℓF)
    (hfit : ℓF + W.card ≤ Fintype.card V)
    : |(flagDensity₁ F (⟦rootedAt N v⟧ : Flag vertexType V) : ℝ)
        - (flagDensity₁ F (⟦rootedAt (deleteFinset N W) ⟨v, hv⟩⟧
            : Flag vertexType {u : V // u ∉ W}) : ℝ)|
      ≤ ((ℓF : ℝ) - 1) * W.card / ((Fintype.card V : ℝ) - 1)
  := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓF = k + 1 := ⟨ℓF - 1, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hF : F = emptyFlag vertexType := Subsingleton.elim _ _
    rw [hF, flagDensity_empty, flagDensity_empty]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 2 := ⟨Fintype.card V - 2, by omega⟩
  set w := W.card with hw
  have hwk : k' + 1 ≤ m + 1 - w := by omega
  -- densities as counts
  have hp : (flagDensity₁ F (⟦rootedAt N v⟧ : Flag vertexType V) : ℚ)
      = ((inducingSubsets F.out (rootedAt N v)).toFinset.card : ℚ)
        / ((m + 1).choose (k' + 1)) := by
    conv_lhs => rw [← Quotient.out_eq F]
    rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div, hm]
    simp only [Fintype.card_fin, Nat.add_sub_cancel]
    have h9 : m + 2 - 1 = m + 1 := by omega
    rw [h9]
  have hcard_del : Fintype.card {u : V // u ∉ W} = m + 2 - w := by
    rw [card_deleteFinset, hm]
  have hp' : (flagDensity₁ F (⟦rootedAt (deleteFinset N W) ⟨v, hv⟩⟧
        : Flag vertexType {u : V // u ∉ W}) : ℚ)
      = ((inducingSubsets F.out (rootedAt (deleteFinset N W) ⟨v, hv⟩)).toFinset.card : ℚ)
        / ((m + 1 - w).choose (k' + 1)) := by
    conv_lhs => rw [← Quotient.out_eq F]
    rw [flagDensity₁_mk, labeledGraphDensity_eq_card_div, hcard_del]
    simp only [Fintype.card_fin, Nat.add_sub_cancel]
    have h9 : m + 2 - w - 1 = m + 1 - w := by omega
    rw [h9]
  set A : ℕ := (inducingSubsets F.out (rootedAt N v)).toFinset.card with hA
  set A' : ℕ := ((inducingSubsets F.out (rootedAt N v)).toFinset.filter
      (fun S => ∀ x ∈ W, x ∉ S)).card with hA'
  have hAdel : (inducingSubsets F.out (rootedAt (deleteFinset N W) ⟨v, hv⟩)).toFinset.card = A' :=
    card_inducingSubsets_deleteFinset_rooted N W v hv F
  have hA'le : A' ≤ A := Finset.card_filter_le _ _
  -- the counting collections
  have hTall : (Finset.univ.erase v).card = m + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hm]
    omega
  have hWsub : W ⊆ Finset.univ.erase v := by
    intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun hc => hv (hc ▸ hx), Finset.mem_univ x⟩
  have hTavoid : ((Finset.univ.erase v) \ W).card = m + 1 - w := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hWsub, hTall]
  have hALL := card_rooted_subsets v (Finset.univ.erase v)
    (Finset.notMem_erase v _) (k' + 1)
  have hAVOID := card_rooted_subsets v ((Finset.univ.erase v) \ W)
    (fun hc => Finset.notMem_erase v Finset.univ (Finset.mem_sdiff.mp hc).1) (k' + 1)
  rw [hTall] at hALL
  rw [hTavoid] at hAVOID
  -- A' is at most the number of avoiding rooted subsets
  have hA'C : A' ≤ (m + 1 - w).choose (k' + 1) := by
    rw [← hAVOID]
    apply Finset.card_le_card
    intro S hS
    rw [Finset.mem_filter, Set.mem_toFinset] at hS
    obtain ⟨hSmem, hSavoid⟩ := hS
    obtain ⟨hvS, hcard, -⟩ := inducingSubsets_rooted_mem N v F S hSmem
    rw [Set.mem_toFinset]
    refine ⟨hvS, hcard, ?_⟩
    intro x hx
    rw [Set.mem_toFinset] at hx
    rw [Finset.mem_insert]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rw [Finset.mem_sdiff, Finset.mem_erase]
      exact ⟨⟨hxv, Finset.mem_univ x⟩, fun hc => hSavoid x hc hx⟩
  -- A is at most A' plus the number of hitting rooted subsets
  have hAup : A ≤ A' + ((m + 1).choose (k' + 1) - (m + 1 - w).choose (k' + 1)) := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (inducingSubsets F.out (rootedAt N v)).toFinset)
      (fun S => ∀ x ∈ W, x ∉ S)
    have hhit : ((inducingSubsets F.out (rootedAt N v)).toFinset.filter
        (fun S => ¬∀ x ∈ W, x ∉ S)).card
        ≤ (m + 1).choose (k' + 1) - (m + 1 - w).choose (k' + 1) := by
      have hsubset : ((inducingSubsets F.out (rootedAt N v)).toFinset.filter
          (fun S => ¬∀ x ∈ W, x ∉ S))
          ⊆ ({S : Set V | v ∈ S ∧ S.toFinset.card = k' + 1 + 1
              ∧ S.toFinset ⊆ insert v (Finset.univ.erase v)} : Set (Set V)).toFinset
            \ ({S : Set V | v ∈ S ∧ S.toFinset.card = k' + 1 + 1
              ∧ S.toFinset ⊆ insert v ((Finset.univ.erase v) \ W)} : Set (Set V)).toFinset := by
        intro S hS
        rw [Finset.mem_filter, Set.mem_toFinset] at hS
        obtain ⟨hSmem, hShit⟩ := hS
        rw [Finset.mem_sdiff, Set.mem_toFinset, Set.mem_toFinset]
        constructor
        · exact inducingSubsets_rooted_mem N v F S hSmem
        · rintro ⟨-, -, hsubW⟩
          apply hShit
          intro x hxW hxS
          have h1 := hsubW (Set.mem_toFinset.mpr hxS)
          rw [Finset.mem_insert] at h1
          rcases h1 with h2 | h2
          · exact hv (h2 ▸ hxW)
          · exact (Finset.mem_sdiff.mp h2).2 hxW
      have hAVsub : ({S : Set V | v ∈ S ∧ S.toFinset.card = k' + 1 + 1
            ∧ S.toFinset ⊆ insert v ((Finset.univ.erase v) \ W)} : Set (Set V)).toFinset
          ⊆ ({S : Set V | v ∈ S ∧ S.toFinset.card = k' + 1 + 1
            ∧ S.toFinset ⊆ insert v (Finset.univ.erase v)} : Set (Set V)).toFinset := by
        intro S hS
        rw [Set.mem_toFinset] at hS ⊢
        obtain ⟨h1, h2, h3⟩ := hS
        exact ⟨h1, h2, subset_trans h3
          (Finset.insert_subset_insert v (Finset.sdiff_subset))⟩
      calc ((inducingSubsets F.out (rootedAt N v)).toFinset.filter
            (fun S => ¬∀ x ∈ W, x ∉ S)).card
          ≤ (({S : Set V | v ∈ S ∧ S.toFinset.card = k' + 1 + 1
              ∧ S.toFinset ⊆ insert v (Finset.univ.erase v)} : Set (Set V)).toFinset
            \ ({S : Set V | v ∈ S ∧ S.toFinset.card = k' + 1 + 1
              ∧ S.toFinset ⊆ insert v ((Finset.univ.erase v) \ W)} : Set (Set V)).toFinset).card :=
            Finset.card_le_card hsubset
        _ = (m + 1).choose (k' + 1) - (m + 1 - w).choose (k' + 1) := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAVsub, hALL, hAVOID]
    omega
  -- the binomial difference bound
  have hbin : (m + 1).choose (k' + 1) - (m + 1 - w).choose (k' + 1)
      ≤ w * m.choose k' := by
    have h1 := choose_le_choose_sub_add (a := m + 1) (w := w) (k := k')
    have h2 : m + 1 - 1 = m := by omega
    rw [h2] at h1
    omega
  -- the ratio identity
  have hid : (m + 1) * m.choose k' = (m + 1).choose (k' + 1) * (k' + 1) :=
    Nat.add_one_mul_choose_eq m k'
  -- positivity
  have hC1 : 0 < (m + 1).choose (k' + 1) := Nat.choose_pos (by omega)
  have hC2 : 0 < (m + 1 - w).choose (k' + 1) := Nat.choose_pos hwk
  have hC2C1 : (m + 1 - w).choose (k' + 1) ≤ (m + 1).choose (k' + 1) :=
    Nat.choose_le_choose _ (by omega)
  -- rational bounds
  set C₁ : ℚ := (((m + 1).choose (k' + 1) : ℕ) : ℚ) with hC₁
  set C₂ : ℚ := (((m + 1 - w).choose (k' + 1) : ℕ) : ℚ) with hC₂
  have hC₁pos : (0 : ℚ) < C₁ := by rw [hC₁]; exact_mod_cast hC1
  have hC₂pos : (0 : ℚ) < C₂ := by rw [hC₂]; exact_mod_cast hC2
  have hC₂C₁ : C₂ ≤ C₁ := by rw [hC₁, hC₂]; exact_mod_cast hC2C1
  have hkey : |(A : ℚ) / C₁ - (A' : ℚ) / C₂| ≤ (C₁ - C₂) / C₁ := by
    have h6 : (1 : ℚ) - C₂ / C₁ = (C₁ - C₂) / C₁ := by
      rw [sub_div, div_self (ne_of_gt hC₁pos)]
    rw [abs_le]
    constructor
    · -- lower bound
      have h3 : (A' : ℚ) ≤ C₂ := by
        rw [hC₂]
        exact_mod_cast hA'C
      have hinv : (0 : ℚ) ≤ 1 / C₂ - 1 / C₁ := by
        rw [sub_nonneg, div_le_div_iff₀ hC₁pos hC₂pos]
        simpa using hC₂C₁
      have e2 : C₂ * (1 / C₂ - 1 / C₁) = 1 - C₂ / C₁ := by
        rw [mul_sub, mul_one_div, mul_one_div, div_self (ne_of_gt hC₂pos)]
      have h4 : (A' : ℚ) / C₂ - (A' : ℚ) / C₁ ≤ 1 - C₂ / C₁ := by
        rw [← e2]
        have e1 : (A' : ℚ) / C₂ - (A' : ℚ) / C₁ = (A' : ℚ) * (1 / C₂ - 1 / C₁) := by
          ring
        rw [e1]
        exact mul_le_mul_of_nonneg_right h3 hinv
      have h5 : (A' : ℚ) / C₁ ≤ (A : ℚ) / C₁ := by
        rw [div_le_div_iff₀ hC₁pos hC₁pos]
        have h7 : (A' : ℚ) ≤ (A : ℚ) := by exact_mod_cast hA'le
        exact mul_le_mul_of_nonneg_right h7 (le_of_lt hC₁pos)
      linarith [h4, h5, h6.le, h6.ge]
    · -- upper bound
      have h3 : (A : ℚ) ≤ (A' : ℚ) + (C₁ - C₂) := by
        have h7 : (A : ℚ) ≤ (A' : ℚ) + (((m + 1).choose (k' + 1)
            - (m + 1 - w).choose (k' + 1) : ℕ) : ℚ) := by
          exact_mod_cast hAup
        rwa [Nat.cast_sub hC2C1, ← hC₁, ← hC₂] at h7
      have h4 : (A' : ℚ) / C₁ ≤ (A' : ℚ) / C₂ := by
        rw [div_le_div_iff₀ hC₁pos hC₂pos]
        exact mul_le_mul_of_nonneg_left hC₂C₁ (Nat.cast_nonneg A')
      have h5 : (A : ℚ) / C₁ ≤ ((A' : ℚ) + (C₁ - C₂)) / C₁ := by
        rw [div_le_div_iff₀ hC₁pos hC₁pos]
        exact mul_le_mul_of_nonneg_right h3 (le_of_lt hC₁pos)
      have h6' : ((A' : ℚ) + (C₁ - C₂)) / C₁ = (A' : ℚ) / C₁ + (C₁ - C₂) / C₁ :=
        add_div _ _ _
      linarith [h4, h5, h6'.le, h6'.ge]
  have hratio : (C₁ - C₂) / C₁ ≤ ((k' + 1 : ℚ)) * w / (m + 1) := by
    have h3 : C₁ - C₂ ≤ (w : ℚ) * ((m.choose k' : ℕ) : ℚ) := by
      have h7 : (((m + 1).choose (k' + 1) - (m + 1 - w).choose (k' + 1) : ℕ) : ℚ)
          ≤ ((w * m.choose k' : ℕ) : ℚ) := by exact_mod_cast hbin
      rw [Nat.cast_sub hC2C1, Nat.cast_mul] at h7
      rwa [← hC₁, ← hC₂] at h7
    have h8 : ((m : ℚ) + 1) * ((m.choose k' : ℕ) : ℚ) = C₁ * ((k' : ℚ) + 1) := by
      rw [hC₁]
      exact_mod_cast hid
    rw [div_le_div_iff₀ hC₁pos (by positivity : (0 : ℚ) < (m : ℚ) + 1)]
    calc (C₁ - C₂) * ((m : ℚ) + 1)
        ≤ ((w : ℚ) * ((m.choose k' : ℕ) : ℚ)) * ((m : ℚ) + 1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (w : ℚ) * (((m : ℚ) + 1) * ((m.choose k' : ℕ) : ℚ)) := by ring
      _ = (w : ℚ) * (C₁ * ((k' : ℚ) + 1)) := by rw [h8]
      _ = ((k' : ℚ) + 1) * (w : ℚ) * C₁ := by ring
  -- assemble
  have hQ : |(flagDensity₁ F (⟦rootedAt N v⟧ : Flag vertexType V) : ℚ)
      - (flagDensity₁ F (⟦rootedAt (deleteFinset N W) ⟨v, hv⟩⟧
          : Flag vertexType {u : V // u ∉ W}) : ℚ)|
      ≤ ((k' + 1 : ℚ)) * w / (m + 1) := by
    rw [hp, hp', hAdel]
    exact le_trans hkey hratio
  have hRcast : |(flagDensity₁ F (⟦rootedAt N v⟧ : Flag vertexType V) : ℝ)
      - (flagDensity₁ F (⟦rootedAt (deleteFinset N W) ⟨v, hv⟩⟧
          : Flag vertexType {u : V // u ∉ W}) : ℝ)|
      ≤ ((((k' + 1 : ℚ)) * w / (m + 1) : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast hQ
  refine le_trans hRcast (le_of_eq ?_)
  rw [hm]
  push_cast
  ring


/-- Vector version of the hitting estimate: `|p(g,(N,v)) − p(g,(N−W,v))|` is at
most `‖g‖₁ · K · |W| / (n−1)` when every flag in the support of `g` has at most
`K + 1` vertices. -/
theorem hitting_pEval {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledGraph ∅ₜ V) (v : V) (W : Finset V) (hv : v ∉ W)
    (g : FlagVector vertexType) {K : ℕ}
    (hK : ∀ F ∈ g.support, F.1 ≤ K + 1)
    (hfit : K + 1 + W.card ≤ Fintype.card V) (hV : 2 ≤ Fintype.card V)
    : |pEval g N v - pEval g (deleteFinset N W) ⟨v, hv⟩|
      ≤ (∑ F ∈ g.support, |g F|) * K * W.card / ((Fintype.card V : ℝ) - 1)
  := by
  have hden : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by
    have h6 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
    linarith
  dsimp only [pEval, linearExtension]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ F ∈ g.support,
      |g F • ((flagDensity₁ F.2 (⟦rootedAt N v⟧ : Flag vertexType V) : ℝ))
        - g F • ((flagDensity₁ F.2 (⟦rootedAt (deleteFinset N W) ⟨v, hv⟩⟧
            : Flag vertexType {u : V // u ∉ W}) : ℝ))|
      ≤ |g F| * ((K : ℝ) * W.card / ((Fintype.card V : ℝ) - 1)) := by
    intro F hF
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : 1 ≤ F.1 := finFlag_size_ge_n₀ F
    have h2 : F.1 + W.card ≤ Fintype.card V := by
      have h7 := hK F hF
      omega
    have h3 := hitting_rooted_density N v W hv F.2 h1 h2
    refine le_trans h3 ?_
    rw [div_le_div_iff₀ hden hden]
    apply mul_le_mul_of_nonneg_right ?_ (le_of_lt hden)
    apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have h4 : (F.1 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hK F hF
    linarith
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_))
  rw [← Finset.sum_mul]
  ring

end Differential
end FlagAlgebras
