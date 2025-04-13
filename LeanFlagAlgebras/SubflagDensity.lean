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
  := by
    dsimp [predIsolabeledH, relOfPredOnlabeledSubgraph, relOflabeledSubgraph]
    rintro H₀ H₁ ⟨h_vert, h_adj⟩
    constructor
    · rintro ⟨f₀, h_iso₀⟩
      let f₁ (w : H₁.subgraph.verts) : U := f₀ (H₀.subgraph.vert (φ.graph_iso.symm ↑w) (by aesop))
      have h_bij₁ : Function.Bijective f₁ := by
        dsimp [Function.Bijective, f₁]
        constructor
        · intro w₀ w₁ h_eq
          simp_all only [eq_iff_iff, Subtype.forall, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
          obtain ⟨_, property₀⟩ := w₀
          obtain ⟨_, property₁⟩ := w₁
          simp_all only
        · intro u
          let w : H₁.subgraph.verts := H₁.subgraph.vert (φ.graph_iso (f₀.symm u)) (by aesop)
          use w
          simp_all only [eq_iff_iff, LabeledSubgraph.coe_graph, LabeledSubgraph.coe_type_embed, RelIso.symm_apply_apply,
            Subtype.coe_eta, RelIso.apply_symm_apply]
      have h_iso₁ : ∀ {w₀ w₁ : H₁.subgraph.verts}, H.graph.Adj (f₁ w₀) (f₁ w₁) ↔ H₁.subgraph.Adj w₀ w₁ := by
        intro w₀ w₁; dsimp [f₁]
        simp_all only [eq_iff_iff, LabeledSubgraph.coe, Subtype.forall, Multiset.bijective_iff_map_univ_eq_univ, f₁]
        obtain ⟨_, property₀⟩ := w₀
        obtain ⟨_, property₁⟩ := w₁
        simp_all only
        sorry
      sorry
    · sorry

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

def inducedlabeledSubgraph
    {σ : FlagType T} (G : LabeledGraph σ V) (S : Set V) (hS : ∀ t : T, G.type_embed t ∈ S) : {G' : LabeledSubgraph σ G // G'.IsInduced}
  :=
  let G' : LabeledSubgraph σ G := {
    subgraph := {
      verts := S
      Adj := fun (u v : V) ↦ G.graph.Adj u v ∧ u ∈ S ∧ v ∈ S
      adj_sub := by
        intro v w h
        simp_all only [Set.mem_union, Set.mem_setOf_eq]
      edge_vert := by
        intro v w h
        simp_all only
      symm := by
        intro v w H
        simp_all
        exact G.graph.symm H.1
    }
    type_embed := {
      toFun := fun t ↦ ⟨G.type_embed t, hS t⟩
      inj' := by
        intro t₁ t₂ h
        simp at h
        exact h
      map_rel_iff' := by
        intro t₁ t₂
        simp; intro _
        exact ⟨hS t₁, hS t₂⟩
    }
    embed_eq := by
      intro t; simp
  }
  let h_induced : G'.IsInduced := by
    intro v w hv hw hvw
    simp_all [Set.mem_union, Set.mem_setOf_eq]
  ⟨G', h_induced⟩

lemma inducerdlabeledSubgraph_support
    {σ : FlagType T} {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H₀ : LabeledSubgraph σ G₀)
    : ∀ (t : T), G₁.type_embed t ∈ ⇑φ.graph_iso '' H₀.subgraph.verts
  := by
  intro t
  simp_all only [Set.mem_image]
  use G₀.type_embed t
  constructor
  · have : H₀.type_embed t = G₀.type_embed t := H₀.embed_eq t
    rw [←this]
    simp
  · rw [←φ.type_preserve]; simp

lemma inducedlabeledSubgraph_related
    {σ : FlagType T } {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁)
    (H₀ : LabeledSubgraph σ G₀) (h_ind₀ : H₀.subgraph.IsInduced)
    : relOflabeledSubgraph φ H₀ (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀))
  := by
  dsimp [relOflabeledSubgraph, inducedlabeledSubgraph]; simp
  intro u v
  constructor
  · intro u_uv
    constructor
    · have : G₀.graph.Adj u v := SimpleGraph.Subgraph.Adj.adj_sub u_uv
      exact (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mpr this
    · exact ⟨H₀.subgraph.edge_vert u_uv, H₀.subgraph.edge_vert u_uv.symm⟩
  · intro ⟨h_G₁uv, ⟨h_u, h_v⟩⟩
    have h_G₀uv : G₀.graph.Adj u v := (SimpleGraph.Iso.map_adj_iff φ.graph_iso).mp h_G₁uv
    apply h_ind₀ h_u h_v h_G₀uv

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
    let H₁ := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)).1
    let h_ind₁ : H₁.IsInduced := (inducedlabeledSubgraph G₁ (φ.graph_iso '' H₀.subgraph.verts) (inducerdlabeledSubgraph_support φ H₀)).2
    have : relOflabeledSubgraph φ H₀ H₁ := inducedlabeledSubgraph_related φ H₀ h_ind₀
    have h_p₁ : p₁ H₁ := (h_rel H₀ H₁ this).mp h_p₀
    exact ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩
  let f_inv (s₁ : S₁) : S₀ := by
    dsimp [S₁] at s₁
    let ⟨H₁, ⟨h_ind₁, h_p₁⟩⟩ := s₁
    let H₀ := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts) (inducerdlabeledSubgraph_support φ.symm H₁)).1
    let h_ind₀ : H₀.IsInduced := (inducedlabeledSubgraph G₀ (φ.symm.graph_iso '' H₁.subgraph.verts) (inducerdlabeledSubgraph_support φ.symm H₁)).2
    have : relOflabeledSubgraph φ.symm H₁ H₀ := inducedlabeledSubgraph_related φ.symm H₁ h_ind₁
    have h_p₀ : p₀ H₀ := (h_rel_inv H₁ H₀ this).mp h_p₁
    exact ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
  let f_bij : Function.Bijective f := by
    have h_leftinv : Function.LeftInverse f_inv f := by
      rintro ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
      ext u v
      · dsimp [f, f_inv, inducedlabeledSubgraph]
        simp; constructor
        · intro ⟨u', ⟨hu'_vert, hu'_iso⟩⟩
          have : u' = u := by
            rw [←hu'_iso]; symm
            exact φ.graph_iso.left_inv u'
          rw [←this]
          exact hu'_vert
        · intro hu_vert
          use u
          simp_all
          exact φ.graph_iso.left_inv u
      · dsimp [f, f_inv, inducedlabeledSubgraph]
        simp; constructor
        · intro ⟨h_uv, ⟨h_u, h_v⟩⟩
          obtain ⟨u', ⟨hu'_vert, hu'_iso⟩⟩ := h_u
          obtain ⟨v', ⟨hv'_vert, hv'_iso⟩⟩ := h_v
          have : u' = u := by
            rw [←hu'_iso]; symm
            exact φ.graph_iso.left_inv u'
          rw [this] at hu'_vert
          have : v' = v := by
            rw [←hv'_iso]; symm
            exact φ.graph_iso.left_inv v'
          rw [this] at hv'_vert
          apply h_ind₀ hu'_vert hv'_vert h_uv
        · intro h_uv
          constructor
          · exact SimpleGraph.Subgraph.Adj.adj_sub h_uv
          · constructor
            · use u
              have u_vert : u ∈ H₀.subgraph.verts := H₀.subgraph.edge_vert h_uv
              simp_all
              exact φ.graph_iso.left_inv u
            · use v
              have v_vert : v ∈ H₀.subgraph.verts := H₀.subgraph.edge_vert h_uv.symm
              simp_all
              exact φ.graph_iso.left_inv v
      · have f_inv_f : ∀ s₀ : S₀, f_inv (f s₀) = s₀ := by
          intro s₀
          obtain ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩ := s₀
          dsimp [f, f_inv, inducedlabeledSubgraph]
          simp
          ext u v
          · simp; constructor
            · intro h
              obtain ⟨u', ⟨hu'_vert, hu'_iso⟩⟩ := h
              have : u' = u := by
                rw [←hu'_iso]; symm
                exact φ.graph_iso.left_inv u'
              rw [←this]
              exact hu'_vert
            · intro hu
              use u
              simp_all [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
              exact φ.graph_iso.left_inv u
          · simp; constructor
            · intro ⟨h_uv, ⟨h_u, h_v⟩⟩
              obtain ⟨u', ⟨hu'_vert, hu'_iso⟩⟩ := h_u
              obtain ⟨v', ⟨hv'_vert, hv'_iso⟩⟩ := h_v
              have : u' = u := by
                rw [←hu'_iso]; symm
                exact φ.graph_iso.left_inv u'
              rw [this] at hu'_vert
              have : v' = v := by
                rw [←hv'_iso]; symm
                exact φ.graph_iso.left_inv v'
              rw [this] at hv'_vert
              apply h_ind₀ hu'_vert hv'_vert h_uv
            · intro h_uv
              constructor
              · exact SimpleGraph.Subgraph.Adj.adj_sub h_uv
              · constructor
                · use u
                  have u_vert : u ∈ H₀.subgraph.verts := H₀.subgraph.edge_vert h_uv
                  simp_all [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
                  exact φ.graph_iso.left_inv u
                · use v
                  have v_vert : v ∈ H₀.subgraph.verts := H₀.subgraph.edge_vert h_uv.symm
                  simp_all [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
                  exact φ.graph_iso.left_inv v
          · simp_all only
            sorry
        let s₀ : S₀ := ⟨H₀, ⟨h_ind₀, h_p₀⟩⟩
        rw [f_inv_f s₀]
    have h_rightinv : Function.RightInverse f_inv f := by
      sorry
    exact Function.bijective_iff_has_inverse.mpr ⟨f_inv, h_leftinv, h_rightinv⟩
  Equiv.ofBijective f f_bij

#check heq_eq_eq

example {α : Type} {a b : α} (h : a = b) : HEq a b := by
  have h' : HEq a b := by
    exact heq_of_eq h
  exact h'

noncomputable def isoSetOfInducedlabeledSubgraphIsoH
    {G₀ : LabeledGraph σ V} {G₁ : LabeledGraph σ W} (φ : G₀ ≃f G₁) (H : LabeledGraph σ U)
    : { G' : LabeledSubgraph σ G₀ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) } ≃ { G' : LabeledSubgraph σ G₁ | G'.IsInduced ∧ Nonempty (G'.coe ≃f H) }
  := by
  let iso := isoSetOfInducedlabeledSubgraph φ
    (predIsolabeledH H G₀)
    (predIsolabeledH H G₁)
    (predIsolabeldH_related φ H)
    (predIsolabeldH_related φ.symm H)
  dsimp [predIsolabeledH, relOfPredOnlabeledSubgraph] at iso
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
    simp_all only [Set.coe_setOf, Set.toFinset_card]
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

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def labeledSubgraphListCount
    (Hl : LabeledGraphList σ) (G : LabeledGraph σ W) : ℕ
  :=
  let ℓ := Hl.length
  let p₁ (Gl : List (LabeledSubgraph σ G)) : Prop
    := if h : Gl.length = ℓ then ∀ (i : Fin ℓ), Gl[i].IsInduced ∧ Nonempty (Gl[i].coe ≃f Hl[i].2) else false
  let p₂ (Gl : List (LabeledSubgraph σ G)) : Prop
    := ∀ (i j : Fin Gl.length), i ≠ j → Gl[i].subgraph.verts ∩ Gl[j].subgraph.verts = ∅
  let S := { Gl : List (LabeledSubgraph σ G) | p₁ Gl ∧ p₂ Gl }
  have : Fintype S := sorry
  S.toFinset.card

/-
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

inductive FlagListHEq
    : FlagList σ t Vl →
      {Vl' : Fin t → Type} → [FintypeList Vl'] → [DecidableEqList Vl'] → FlagList σ t Vl' → Prop where
  | refl (Fl : FlagList σ t Vl) : FlagListHEq Fl Fl

theorem FlagListHEq.subst
    {Vl Vl' : Fin t → Type} [FintypeList Vl] [DecidableEqList Vl] [FintypeList Vl'] [DecidableEqList Vl']
    {Fl : FlagList σ t Vl} {Fl' : FlagList σ t Vl'}
    (p : {Wl : Fin t → Type} → [FintypeList Wl] → [DecidableEqList Wl] → FlagList σ t Wl → Prop)
    (hHEq : HEq Fl Fl') (h : p Fl) : p Fl' := by
  sorry

-- (hHEq : @FlagListHEq T σ t Vl _ _ Fl Vl' _ _ Fl')

#check @FlagListHEq.subst
#check HEq.subst

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
  have h_list_eq : Fl₁.permute π = cast h_type_eq Fl₂ := by
    sorry
  have hHEq : HEq Fl₂ (Fl₁.permute π) := by simp [HEq.symm, h_list_eq, cast_heq]
  have h_subst := FlagListHEq.subst (fun Wl => flagListDensity Wl G = flagListDensity Fl₂ G) hHEq
  simp at h_subst
  exact h_subst
-/

end
