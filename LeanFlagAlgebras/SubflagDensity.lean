import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

variable {T : Type} [Fintype T] {σ : FlagType T}

section

variable {V W T: Type}
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  [Fintype U] [DecidableEq U]

noncomputable def labeledSubgraphCount
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℕ
  :=
  let p (G' : LabeledSubgraph σ G) : Prop := G'.IsInduced ∧ Nonempty (G'.coe ≃f H)
  let S := { G' : LabeledSubgraph σ G | p G' }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card

noncomputable def labeledSubgraphDensity
    (H : LabeledGraph σ V) (G : LabeledGraph σ W) : ℚ
  :=
  let labeledSubgraph_cnt := labeledSubgraphCount H G
  let num_of_all_induced_subgraph := (G.size - σ.size).choose (H.size - σ.size)
  labeledSubgraph_cnt / num_of_all_induced_subgraph

def relOflabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (H₁ : LabeledSubgraph σ G₁) : Prop
  :=
  H₁.subgraph.verts = φ.graph_iso '' H₀.subgraph.verts
  ∧ ∀ (u v : V), H₀.subgraph.Adj u v = H₁.subgraph.Adj (φ.graph_iso.toFun u) (φ.graph_iso.toFun v)
  -- Several conditions will be added

def relOfPredOnlabeledfSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
  := ∀ (H₀: LabeledSubgraph σ G₀) (H₁: LabeledSubgraph σ G₁), (relOflabeledSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def inducedlabeledSubgraph
    {σ : FlagType T} (G : LabeledGraph σ V) (S : Set V) : {G' : LabeledSubgraph σ G // G'.IsInduced}
  :=
  let G' : LabeledSubgraph σ G := {
    subgraph := {
      verts := S ∪ { G.type_embed t | t : T }
      Adj := fun (u v : V) ↦ G.graph.Adj u v ∧ u ∈ S ∪ { G.type_embed t | t : T } ∧ v ∈ S ∪ { G.type_embed t | t : T }
      adj_sub := by
        intro v w h
        simp_all only
      edge_vert := by
        intro v w h
        simp_all only [Set.mem_union, Set.mem_setOf_eq]
      symm := fun u v h ↦ ⟨G.graph.symm h.1, h.2.2, h.2.1⟩
    }
    type_embed := {
      toFun := by
        intro t
        simp_all only
        apply Subtype.mk
        · simp_all only [Set.mem_union, Set.mem_setOf_eq]
          apply Or.inr
          apply Exists.intro
          · rfl
          · exact t
      inj' := by
        intro t₁ t₂ h
        simp_all only [Set.mem_setOf_eq, id_eq, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
      map_rel_iff' := by
        intro t₁ t₂
        simp_all only [Set.mem_setOf_eq, id_eq, Function.Embedding.coeFn_mk, SimpleGraph.Subgraph.coe_adj,
          SimpleGraph.Embedding.map_adj_iff, and_iff_left_iff_imp]
        intro _
        simp_all only [Set.mem_union, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq, or_true, and_self]
    }
    embed_eq := by
      intro t
      simp_all only [Set.mem_setOf_eq, eq_mp_eq_cast, cast_eq, id_eq, RelEmbedding.coe_mk,
        Function.Embedding.coeFn_mk]
  }
  let h_induced : G'.IsInduced := by
    intro u v hu hv huv
    simp_all only [Set.mem_union, Set.mem_setOf_eq, and_self]
  ⟨G', h_induced⟩

lemma inducedlabeledSubgraph_related
    {σ : FlagType T } {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.subgraph.IsInduced)
    : relOflabeledSubgraph φ H₀ (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts))
  := by
  dsimp [relOflabeledSubgraph, inducedlabeledSubgraph]; simp
  apply And.intro
  · intro x hx
    simp
    obtain ⟨t, ht_G₁⟩ := hx
    let x' := G₀.type_embed t
    use x'
    constructor
    · let x'_eq := H₀.type_embed t
      have h_eq : x' = x'_eq := by
        simp [x', x'_eq]
        rw [H₀.embed_eq t]
      rw [h_eq]
      simp
    · simp_all only [x']
      rw [←ht_G₁, ←φ.type_preserve]
      simp
  · intro u v
    constructor
    · intro h_uv_H₀
      have h_uv_G₀ := H₀.subgraph.adj_sub h_uv_H₀
      have h_u_H₀ : u ∈ H₀.subgraph.verts := H₀.subgraph.edge_vert h_uv_H₀
      have h_v_H₀ : v ∈ H₀.subgraph.verts := H₀.subgraph.edge_vert (H₀.subgraph.symm h_uv_H₀)
      constructor
      · simp [φ.graph_iso.map_rel_iff]
        exact h_uv_G₀
      · constructor
        · left; exact h_u_H₀
        · left; exact h_v_H₀
    · rintro ⟨h_uv, h_u, h_v⟩
      cases' h_u with h_u h_u
      · cases' h_v with h_v h_v
        · apply h_ind₀ h_u h_v
          exact (φ.graph_iso.map_rel_iff).mp h_uv
        · sorry
      · cases' h_v with h_v h_v
        · sorry
        · obtain ⟨u_T, h_uG₁⟩ := h_u
          obtain ⟨v_T, h_vG₁⟩ := h_v
          let uG₀ := G₀.type_embed u_T
          let vG₀ := G₀.type_embed v_T
          let uG₁ := G₁.type_embed u_T
          let vG₁ := G₁.type_embed v_T
          have h_uG₀G₁ : uG₁ = φ.graph_iso.toFun uG₀:= by
            dsimp [uG₀, uG₁]
            rw [←φ.type_preserve]
            rfl
          have h_vG₀G₁ : vG₁ = φ.graph_iso.toFun vG₀:= by
            dsimp [vG₀, vG₁]
            rw [←φ.type_preserve]
            rfl
          have u_eq_uG₀ : u = uG₀ := by
            have : φ.graph_iso u = φ.graph_iso uG₀ := by
              dsimp [uG₁] at h_uG₀G₁
              rw [h_uG₀G₁] at h_uG₁
              symm; exact h_uG₁
            simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, EmbeddingLike.apply_eq_iff_eq, uG₀, uG₁, vG₁, vG₀]
          have v_eq_vG₀ : v = vG₀ := by
            have : φ.graph_iso v = φ.graph_iso vG₀ := by
              dsimp [vG₁] at h_vG₀G₁
              rw [h_vG₀G₁] at h_vG₁
              symm; exact h_vG₁
            simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, EmbeddingLike.apply_eq_iff_eq, uG₀, uG₁, vG₁, vG₀]
          let uH₀ := H₀.type_embed u_T
          let vH₀ := H₀.type_embed v_T
          have h_uH₀G₀ : uH₀ = uG₀ := by
            have : H₀.type_embed u_T = uG₀ := H₀.embed_eq u_T
            simp_all only [uH₀, uG₀]
          have h_vH₀G₀ : vH₀ = vG₀ := by
            have : H₀.type_embed v_T = vG₀ := H₀.embed_eq v_T
            simp_all only [vH₀, vG₀]
          have h_uv_G₀ : G₀.graph.Adj u v := by
            rw [u_eq_uG₀, v_eq_vG₀]
            rw [u_eq_uG₀, v_eq_vG₀] at h_uv
            apply φ.graph_iso.map_rel_iff.mp h_uv
          have h_uH₀H₀ : u ∈ H₀.subgraph.verts := by
            rw [u_eq_uG₀, ←h_uH₀G₀]
            simp
          have h_vH₀H₀ : v ∈ H₀.subgraph.verts := by
            rw [v_eq_vG₀, ←h_vH₀G₀]
            simp
          apply h_ind₀ h_uH₀H₀ h_vH₀H₀
          exact h_uv_G₀

noncomputable def isoSetOfInducedlabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
    (h_rel : relOfPredOnlabeledfSubgraph φ p₀ p₁) (h_rel_inv : relOfPredOnlabeledfSubgraph φ.symm p₁ p₀)
    : { G' : LabeledSubgraph σ G₀ | p₀ G' } ≃ { G' : LabeledSubgraph σ G₁ | p₁ G' }
  :=
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  let f (s₀ : S₀) : S₁ := by
    dsimp [S₀] at s₀
    let ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
    let H₁ := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts)).1

    sorry
  sorry

noncomputable def isoSetOfInducedlabeledSubgraphIsoH
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
      ≃
      { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  := sorry

lemma labeledSubgraphDensity_respects_eqv_on_G
    (H : LabeledGraph σ U) {G₀ G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    : labeledSubgraphDensity H G₀ = labeledSubgraphDensity H G₁
  := by
  dsimp [labeledSubgraphDensity]
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  let h_iso_S₀_S₁ : S₀ ≃ S₁ := isoSetOfInducedlabeledSubgraphIsoH φ H
  have hS₀ : Fintype S₀ := Fintype.ofFinite ↑S₀
  have hS₁ : Fintype S₁ := Fintype.ofFinite ↑S₁
  have h_count : labeledSubgraphCount H G₀ = labeledSubgraphCount H G₁ := by
    dsimp only [labeledSubgraphCount]
    have card_eq : Fintype.card S₀ = Fintype.card S₁ := Fintype.card_congr h_iso_S₀_S₁
    simp_all only [Set.coe_setOf, Set.toFinset_card, S₀, S₁]
    sorry
  rw [h_count]
  rfl

noncomputable def labeledSubgraphDensityLifted
    (H : LabeledGraph σ V) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ W => labeledSubgraphDensity H G)
  intro _ _ G_eqv
  exact labeledSubgraphDensity_respects_eqv_on_G H (Classical.choice G_eqv)

lemma labeledSubgraphDensityLifted_respects_eqv
    (H H' : LabeledGraph σ V) (φ : H ≃f H') (G : Flag σ W)
    : labeledSubgraphDensityLifted H G = labeledSubgraphDensityLifted H' G
  :=
  sorry

noncomputable def subflagDensity
    : Flag σ V → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphDensityLifted
  intro H H' H_eqv
  ext G
  exact labeledSubgraphDensityLifted_respects_eqv H H' (Classical.choice H_eqv) G

end

section

variable {t : ℕ} {V : Fin t → Type} [FintypeList V] [DecidableEqList V]
  {W : Type} [Fintype W] [DecidableEq W]
  {U : Type} [Fintype U] [DecidableEq U]
  {U₁ : Type} [Fintype U₁] [DecidableEq U₁]
  {U₂ : Type} [Fintype U₂] [DecidableEq U₂]
  {U₃ : Type} [Fintype U₃] [DecidableEq U₃]

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ t V) (G : LabeledGraph σ W) : ℕ
  :=
  let p₁ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i : Fin t), (Gl i).IsInduced ∧ Nonempty ((Gl i).coe ≃f Hl i)
  let p₂ (Gl : ∀ (_ : Fin t), LabeledSubgraph σ G) : Prop
    := ∀ (i j : Fin t), i ≠ j → (Gl i).subgraph.verts ∩ (Gl j).subgraph.verts = ∅
  let S := { Gl : ∀ (_ : Fin t), LabeledSubgraph σ G | p₁ Gl ∧ p₂ Gl }
  have : Fintype S := Fintype.ofFinite ↑S
  S.toFinset.card

def multinomialCoefficient
    (r_list : Fin t → ℕ) (n : ℕ) : ℕ
  :=
  let r_sum := ∑ i : Fin t, r_list i
  if _ : n ≥ r_sum then
    Nat.factorial n / ((∏ i : Fin t, Nat.factorial (r_list i)) * Nat.factorial (n - r_sum))
  else 0

noncomputable def labeledSubgraphListDensity
    (Hl : LabeledGraphList σ t V) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list := fun (i : Fin t) => (Hl i).size - σ.size
  labeledSubgraphListCount Hl G / multinomialCoefficient r_list (G.size - σ.size)

lemma labeledSubgraphListDensity_respects_eqv_on_G
    (Hl : LabeledGraphList σ t V) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphListDensity Hl G = labeledSubgraphListDensity Hl G'
  :=
  sorry

noncomputable def labeledSubgraphListDensityLifted
    (Hl : LabeledGraphList σ t V) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G => labeledSubgraphListDensity Hl G)
  intro _ _ h_eqv
  exact labeledSubgraphListDensity_respects_eqv_on_G Hl (Classical.choice h_eqv)

lemma labeledSubgraphListDensityLifted_respects_eqv
    (Hl Hl' : LabeledGraphList σ t V) (φ : ∀ (i : Fin t), Hl i ≃f Hl' i) (G : Flag σ W)
    : labeledSubgraphListDensityLifted Hl G = labeledSubgraphListDensityLifted Hl' G
  :=
  sorry

noncomputable def quotLabeledSubgraphListDensity
    : QuotLabeledGraphList σ t V → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphListDensityLifted
  intro Hl Hl' Hl_eqv
  ext G
  have φ : ∀ (i : Fin t), Hl i ≃f Hl' i := by
    intro i
    exact Classical.choice (Hl_eqv i)
  exact labeledSubgraphListDensityLifted_respects_eqv Hl Hl' φ G

noncomputable def flagListDensity
    : FlagList σ t V → Flag σ W → ℚ
  :=
  fun Fl => quotLabeledSubgraphListDensity Fl.coe

example (F : Flag σ U) (G : Flag σ W)
    : subflagDensity F G = flagListDensity [F]ᶠ G
  := by
  rcases Quotient.exists_rep F with ⟨Frep, hFrep⟩
  rcases Quotient.exists_rep G with ⟨Grep, hGrep⟩
  have h_count : labeledSubgraphCount Frep Grep = labeledSubgraphListCount (fun (_ : Fin 1) => Frep) Grep := by
    dsimp [labeledSubgraphCount, labeledSubgraphListCount]
    apply Finset.card_bij
    · intro H hH
      simp at hH
      show (fun (_ : Fin 1) => H) ∈ _
      simp [Set.toFinset_setOf]
      constructor
      · exact hH
      · intro i j hij
        have : i = j := by
          rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
        contradiction
    · intro H _ H' _ h_eq
      calc
        H = (fun (_ : Fin 1) => H) 0 := by simp
        _ = (fun (_ : Fin 1) => H') 0 := by rw [h_eq]
        _ = H' := by simp
    · intro Hl _
      use Hl 0
      simp_all
      ext1 i
      rw [Fin.fin_one_eq_zero i]
  calc
    subflagDensity F G = labeledSubgraphDensity Frep Grep := by
      subst hFrep hGrep
      rfl
    _ = labeledSubgraphListDensity (fun (_ : Fin 1) => Frep) Grep := by
      dsimp [labeledSubgraphDensity, labeledSubgraphListDensity]
      rw [← h_count]
      congr
      dsimp [multinomialCoefficient]
      rw [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Finset.prod_singleton]
      split
      · rw [Nat.choose_eq_factorial_div_factorial (by assumption)]
      · rw [Nat.choose_eq_zero_of_lt (by linarith)]
    _ = quotLabeledSubgraphListDensity [F]ᶠ.coe G := by
      have : [F]ᶠ.coe = ⟦fun (_ : Fin 1) => Frep⟧ := by
        dsimp [eqv_QuotLabeledGraphList_FlagList]
        apply Quotient.sound
        intro i
        simp [flagToList, ← hFrep]
        apply Quotient.mk_out Frep
      rw [this, ← hGrep]
      rfl
    _ = flagListDensity [F]ᶠ G := rfl

noncomputable def flagDensity₁ (F : Flag σ U) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F]ᶠ G

noncomputable def flagDensity₂ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂]ᶠ G

noncomputable def flagDensity₃ (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (F₃ : Flag σ U₃) (G : Flag σ W) : ℚ
  :=
  flagListDensity [F₁, F₂, F₃]ᶠ G

theorem flagDensity_self
    (F : Flag σ W) : flagDensity₁ F F = 1
  :=
  sorry

theorem flagDensity_other
    {F F' : Flag σ W} (h_neq : F ≠ F') : flagDensity₁ F F' = 0
  :=
  sorry

end
