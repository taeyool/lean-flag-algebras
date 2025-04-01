import «LeanFlagAlgebras».FlagDef
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

variable {T : Type} [Fintype T] [DecidableEq T] {σ : FlagType T}

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

def relOfPredOnlabeledSubgraph
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
  := ∀ (H₀: LabeledSubgraph σ G₀) (H₁: LabeledSubgraph σ G₁), (relOflabeledSubgraph φ H₀ H₁) → (p₀ H₀ ↔ p₁ H₁)

def predIsolabeledH
    (H : LabeledGraph σ U) (G : LabeledGraph σ W)
    : LabeledSubgraph σ G → Prop
  := fun G' ↦ Nonempty (G'.coe ≃f H)

lemma predIsolabeldH_related
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : relOfPredOnlabeledSubgraph φ (predIsolabeledH H G₀) (predIsolabeledH H G₁)
  := by sorry

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

lemma relOfTypeVertex
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    {t : T} {v : V} (h_G₁t : G₁.type_embed t = φ.graph_iso v) (H₀ : LabeledSubgraph σ G₀)
    : ∃ (G₀t : V) (G₁t : W) (H₀t : V), G₁t = φ.graph_iso G₀t ∧ v = G₀t ∧ H₀t = G₀t ∧ v ∈ H₀.subgraph.verts
    := by
    let G₀t := G₀.type_embed t
    let G₁t := G₁.type_embed t
    let H₀t := H₀.type_embed t
    have h_eq : G₁t = φ.graph_iso G₀t := by
      dsimp [G₀t, G₁t]
      rw [←φ.type_preserve]
      rfl
    have h_eq' : v = G₀t := by
      have : φ.graph_iso v = φ.graph_iso G₀t := by
        dsimp [G₁t] at h_eq
        rw [h_G₁t] at h_eq
        exact h_eq
      simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, EmbeddingLike.apply_eq_iff_eq, G₀t, G₁t]
    have h_eq'' : H₀t = G₀t := by
      dsimp [H₀t]
      rw [H₀.embed_eq t]
    have h_vert : v ∈ H₀.subgraph.verts := by
      rw [h_eq', ←h_eq'']
      simp
    use G₀t, G₁t, H₀t

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
        · obtain ⟨v_T, h_vG₁⟩ := h_v
          obtain ⟨G₀vt, G₁vt, H₀vt, h_G₀G₁vt, v_eq_G₀vt, G₀vt_eq_H₀vt, h_H₀vt⟩ := relOfTypeVertex φ h_vG₁ H₀
          have h_uv_G₀ : G₀.graph.Adj u v := by
            rw [v_eq_G₀vt]
            rw [v_eq_G₀vt] at h_uv
            apply φ.graph_iso.map_rel_iff.mp h_uv
          apply h_ind₀ h_u h_H₀vt
          exact h_uv_G₀
      · cases' h_v with h_v h_v
        · obtain ⟨u_T, h_uG₁⟩ := h_u
          obtain ⟨G₀ut, G₁ut, H₀ut, h_G₀G₁ut, u_eq_G₀ut, G₀ut_eq_H₀ut, h_H₀ut⟩ := relOfTypeVertex φ h_uG₁ H₀
          have h_uv_G₀ : G₀.graph.Adj u v := by
            rw [u_eq_G₀ut]
            rw [u_eq_G₀ut] at h_uv
            apply φ.graph_iso.map_rel_iff.mp h_uv
          apply h_ind₀ h_H₀ut h_v
          exact h_uv_G₀
        · obtain ⟨u_T, h_uG₀⟩ := h_u
          obtain ⟨G₀ut, G₁ut, H₀ut, h_G₀G₁ut, u_eq_G₀ut, G₀ut_eq_H₀ut, h_H₀ut⟩ := relOfTypeVertex φ h_uG₀ H₀
          obtain ⟨v_T, h_vG₁⟩ := h_v
          obtain ⟨G₀vt, G₁vt, H₀vt, h_G₀G₁vt, v_eq_G₀vt, G₀vt_eq_H₀vt, h_H₀vt⟩ := relOfTypeVertex φ h_vG₁ H₀
          have h_uv_G₀ : G₀.graph.Adj u v := by
            rw [u_eq_G₀ut, v_eq_G₀vt]
            rw [u_eq_G₀ut, v_eq_G₀vt] at h_uv
            apply φ.graph_iso.map_rel_iff.mp h_uv
          apply h_ind₀ h_H₀ut h_H₀vt
          exact h_uv_G₀

noncomputable def isoSetOfInducedlabeledSubgraph
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (p₀ : LabeledSubgraph σ G₀ → Prop) (p₁ : LabeledSubgraph σ G₁ → Prop)
    (h_rel : relOfPredOnlabeledSubgraph φ p₀ p₁) (h_rel_inv : relOfPredOnlabeledSubgraph φ.symm p₁ p₀)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' } ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  :=
  let S₀ := { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ p₀ G' }
  let S₁ := { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ p₁ G' }
  let f (s₀ : S₀) : S₁ := by
    dsimp [S₀] at s₀
    let ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
    let H₁ := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts)).1
    let h_ind₁ : H₁.IsInduced := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts)).2
    have : relOflabeledSubgraph φ H₀ H₁ := inducedlabeledSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let H₀ := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts)).1
    let h_ind₀ : H₀.IsInduced := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts)).2
    have : relOflabeledSubgraph φ.symm H₁ H₀ := inducedlabeledSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
      dsimp [f, f_inv, inducedlabeledSubgraph]
      ext u v
      · simp ; constructor
        · intro h
          cases' h with h1 h2
          · obtain ⟨w, ⟨h_w, h_u⟩⟩ := h1
            cases' h_w with h1 h2
            · obtain ⟨u', ⟨h1_u', h2_u'⟩⟩ := h1
              have u_eq_u' : u = u' := by
                rw [←h2_u'] at h_u
                by_contra t
                push_neg at t
                rw [←h_u] at t
                apply t
                exact φ.graph_iso.left_inv u'
              rw [←u_eq_u'] at h1_u'
              exact h1_u'
            · sorry
          · obtain ⟨u_T', h_u⟩ := h2
            let u' := H₀.type_embed u_T'
            have h_eq : u' = u := by
              simp [u']
              rw [H₀.embed_eq u_T']
              simp [h_u]
            rw [←h_eq]
            simp [h_u]
        · intro h
          left
          let x := φ.graph_iso.toFun u
          use x
          constructor
          · left
            use u
            simp [x]
            exact h
          · simp [x]
            exact φ.graph_iso.left_inv u
      · simp; constructor
        · intro ⟨h1, h2, h3⟩
          -- I expect this can be proven in a similar way to what we've done before.
          sorry
        · intro h
          constructor
          · exact SimpleGraph.Subgraph.Adj.adj_sub h
          · constructor
            · sorry
            · sorry
      · simp
        cases' H₀.type_embed with embed map_rel_iff''
        obtain ⟨toFun', inj''⟩ := embed
        sorry

    have h_rightinv : Function.RightInverse f_inv f := by
      rintro ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
      dsimp [f, f_inv, inducedlabeledSubgraph]
      ext u v
      · simp ; constructor
        · sorry
        · sorry
      · sorry
      · sorry
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

noncomputable def isoSetOfInducedlabeledSubgraphIsoH
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
      ≃
      { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  := by
  let iso := isoSetOfInducedlabeledSubgraph φ
    (predIsolabeledH H G₀)
    (predIsolabeledH H G₁)
    (predIsolabeldH_related φ H)
    (predIsolabeldH_related φ.symm H)
  dsimp [predIsolabeledH] at iso
  exact iso

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

variable {t : ℕ} {Vl : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl]
  {W : Type} [Fintype W] [DecidableEq W]
  {U : Type} [Fintype U] [DecidableEq U]
  {U₁ : Type} [Fintype U₁] [DecidableEq U₁]
  {U₂ : Type} [Fintype U₂] [DecidableEq U₂]
  {U₃ : Type} [Fintype U₃] [DecidableEq U₃]

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℕ
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
    (Hl : LabeledGraphList σ t Vl) (G : LabeledGraph σ W) : ℚ
  :=
  let r_list := fun (i : Fin t) => (Hl i).size - σ.size
  labeledSubgraphListCount Hl G / multinomialCoefficient r_list (G.size - σ.size)

lemma labeledSubgraphListDensity_respects_eqv_on_G
    (Hl : LabeledGraphList σ t Vl) {G G' : LabeledGraph σ W} (φ : G ≃f G')
    : labeledSubgraphListDensity Hl G = labeledSubgraphListDensity Hl G'
  :=
  sorry

noncomputable def labeledSubgraphListDensityLifted
    (Hl : LabeledGraphList σ t Vl) : Flag σ W → ℚ
  := by
  apply Quot.lift (fun G => labeledSubgraphListDensity Hl G)
  intro _ _ h_eqv
  exact labeledSubgraphListDensity_respects_eqv_on_G Hl (Classical.choice h_eqv)

lemma labeledSubgraphListDensityLifted_respects_eqv
    (Hl Hl' : LabeledGraphList σ t Vl) (φ : ∀ (i : Fin t), Hl i ≃f Hl' i) (G : Flag σ W)
    : labeledSubgraphListDensityLifted Hl G = labeledSubgraphListDensityLifted Hl' G
  :=
  sorry

noncomputable def quotLabeledSubgraphListDensity
    : QuotLabeledGraphList σ t Vl → Flag σ W → ℚ
  := by
  apply Quot.lift labeledSubgraphListDensityLifted
  intro Hl Hl' Hl_eqv
  ext G
  have φ : ∀ (i : Fin t), Hl i ≃f Hl' i := by
    intro i
    exact Classical.choice (Hl_eqv i)
  exact labeledSubgraphListDensityLifted_respects_eqv Hl Hl' φ G

noncomputable def flagListDensity
    : FlagList σ t Vl → Flag σ W → ℚ
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

theorem flagDensity_empty
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G = flagListDensity (Fl.insert (emptyFlag σ)) G
  :=
  sorry

theorem flagDensity_permute
    (Fl : FlagList σ t Vl) (G : Flag σ W) (π : Perm t)
    : flagListDensity Fl G = flagListDensity (Fl.permute π) G
  :=
  sorry

theorem FlagListHEq.subst
    {Vl Vl' : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl] [FintypeList Vl'] [DecidableEqList Vl']
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    {p : {Wl : Fin t → Type} → [FintypeList Wl] → [DecidableEqList Wl] → FlagList σ t Wl → Prop}
    (hHEq : HEq Fl Fl') (h : p Fl) : p Fl' :=
  sorry

theorem flagPairDensity_comm
    (F₁ : Flag σ U₁) (F₂ : Flag σ U₂) (G : Flag σ W)
    : flagDensity₂ F₁ F₂ G = flagDensity₂ F₂ F₁ G
  := by
  let Fl₁ := [F₁, F₂]ᶠ
  let Fl₂ := [F₂, F₁]ᶠ
  show flagListDensity Fl₁ G = flagListDensity Fl₂ G
  let π : Perm 2 := by
    let f : Fin 2 → Fin 2 := fun i => match i with | 0 => 1 | 1 => 0
    refine ⟨f, f, ?_, ?_⟩
    · intro i; match i with | 0 => simp | 1 => simp
    · intro i; match i with | 0 => simp | 1 => simp
  rw [flagDensity_permute Fl₁ G π]
  have h_type_eq : FlagList σ 2 (fun i => match i with | 0 => U₂ | 1 => U₁)
      = FlagList σ 2 (listTypePermute (fun i => match i with | 0 => U₁ | 1 => U₂) π) := by
    congr; ext i
    match i with | 0 => simp [listTypePermute] | 1 => simp [listTypePermute]
  have h_eq : Fl₁.permute π = cast h_type_eq Fl₂ := by
    sorry
  have hHEq : HEq Fl₂ (Fl₁.permute π) := by simp [HEq.symm, h_eq, cast_heq]
  have : FintypeList (fun (i : Fin 2) => match i with | 0 => U₂ | 1 => U₁) := fintypePairList
  have : DecidableEqList (fun (i : Fin 2) => match i with | 0 => U₂ | 1 => U₁) := decidableEqPairList
  have : FintypeList (listTypePermute (fun (i : Fin 2) => match i with | 0 => U₁ | 1 => U₂) π) := sorry
  have : DecidableEqList (listTypePermute (fun (i : Fin 2) => match i with | 0 => U₁ | 1 => U₂) π) := sorry
  have tt := @FlagListHEq.subst T _ _ σ 2 (fun i => match i with | 0 => U₂ | 1 => U₁)
              (listTypePermute (fun i => match i with | 0 => U₁ | 1 => U₂) π) _ _ _ _ Fl₂ (Fl₁.permute π)
              (fun Wl => flagListDensity Wl G = flagListDensity Fl₂ G) hHEq
  simp at tt
  have tt' : flagListDensity Fl₂ G = flagListDensity Fl₂ G := rfl
  -- exact tt tt'
  sorry

#check @FlagListHEq.subst

end
