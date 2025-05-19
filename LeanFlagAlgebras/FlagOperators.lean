import «LeanFlagAlgebras».FlagAlgebra

open FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/- Downward operator from σ-type to the empty type -/

def emptyType : FlagType (Fin 0) := emptyGraph (Fin 0)

notation "∅ₜ" => emptyType

noncomputable def isomorphismCount
    (G : LabeledGraph σ (Fin n)) : ℕ
  :=
  let S := { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H }
  have : FintypeExist S := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S) }
  S.toFinset.card

noncomputable def downwardNormalizingFactor_labeledGraph
    (G : LabeledGraph σ (Fin n)) : ℚ
  :=
  let num_of_all_injections := n.factorial / (n - n₀).factorial
  isomorphismCount G / num_of_all_injections

def isoSetOfIsoLabeledGraphWithSameGraph
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H } ≃ { H : LabeledGraph σ (Fin n) | G'.graph = H.graph ∧ G' ∼f H }
  := by
  sorry

lemma isomorphismCount_respects_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : isomorphismCount G = isomorphismCount G'
  := by
  dsimp [isomorphismCount]
  let S := { H : LabeledGraph σ (Fin n) | G.graph = H.graph ∧ G ∼f H }
  let S' := { H : LabeledGraph σ (Fin n) | G'.graph = H.graph ∧ G' ∼f H }
  have h_iso_S_S' : S ≃ S' := isoSetOfIsoLabeledGraphWithSameGraph h
  have : FintypeExist S := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S) }
  have : FintypeExist S' := { fintype_exist := Nonempty.intro (Fintype.ofFinite ↑S') }
  have := Fintype.card_congr h_iso_S_S'
  simp_all only [Set.toFinset_card, S, S']

lemma downwardNormalizingFactor_labeledGraph_respects_eqv
    {G G' : LabeledGraph σ (Fin n)} (h : G ∼f G')
    : downwardNormalizingFactor_labeledGraph G = downwardNormalizingFactor_labeledGraph G'
  := by
  dsimp [downwardNormalizingFactor_labeledGraph]
  rw [isomorphismCount_respects_eqv h]

noncomputable def downwardNormalizingFactor
    : Flag σ (Fin n) → ℚ
  := by
  apply Quot.lift (fun G : LabeledGraph σ (Fin n) => downwardNormalizingFactor_labeledGraph G)
  intro G G' G_eqv
  exact downwardNormalizingFactor_labeledGraph_respects_eqv G_eqv

def unlabeledGraph {V : Type} (G : LabeledGraph σ V) : LabeledGraph ∅ₜ V where
  graph := G.graph
  type_embed := RelEmbedding.ofIsEmpty ∅ₜ.Adj G.graph.Adj

theorem unlabeledGraph_iso
    (G G' : LabeledGraph σ V) (h : G ∼f G')
    : unlabeledGraph G ∼f unlabeledGraph G'
  := by
  sorry

noncomputable def unlabel {V : Type} (F : Flag σ V) : Flag ∅ₜ V :=
  ⟦unlabeledGraph F.out⟧

noncomputable def downwardFlag (F : Flag σ (Fin n)) : FlagVector ∅ₜ :=
  downwardNormalizingFactor F • unitVector ⟨n, unlabel F⟩

noncomputable def downwardFlagVector (f : FlagVector σ) : FlagVector ∅ₜ :=
  ∑ F in f.support, (f F) • downwardFlag F.2

noncomputable def downwardFlagVectorQuot (f : FlagVector σ) : FlagAlgebra ∅ₜ :=
  ⟦downwardFlagVector f⟧

lemma downwardFlagVectorQuot_respects_eqv
    (f f' : FlagVector σ) (h : f ∼v f')
    : downwardFlagVectorQuot f = downwardFlagVectorQuot f'
  :=
  sorry

noncomputable def downward
    : FlagAlgebra σ → FlagAlgebra ∅ₜ
  := by
  apply Quot.lift (fun g : FlagVector σ => downwardFlagVectorQuot g)
  intro f f' f_eqv
  exact downwardFlagVectorQuot_respects_eqv f f' f_eqv

notation "⟦" f "⟧₀" => (downward f)

theorem downward_add
    (f f' : FlagAlgebra σ)
    : ⟦f + f'⟧₀ = ⟦f⟧₀ + ⟦f'⟧₀
  :=
  sorry

theorem downward_smul
    (f : FlagAlgebra σ) (r : ℝ)
    : ⟦r • f⟧₀ = r • ⟦f⟧₀
  :=
  sorry
