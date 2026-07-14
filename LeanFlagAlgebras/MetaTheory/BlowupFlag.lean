import LeanFlagAlgebras.MetaTheory.Blowup
import LeanFlagAlgebras.FlagAlgebra.FlagDef

/-! # The blow-up as a labelled graph, and the good-event flag isomorphism

We package the base graph `G` (with labelling `θ`) and the independent blow-up `G^{\mathbf m}`
(with the planted labelling `θ̂ : i ↦ ⟨θ i, c i⟩`) as `LabeledGraph`s.  The key structural fact
of the planted estimate (`lem:planted-estimate`, good event) is `blowupGoodIso`: on a vertex set
`S'` meeting each clone class at most once and containing the planted roots, the induced labelled
subgraph of the blow-up on `S'` is `≃f`-isomorphic, via the projection, to the induced labelled
subgraph of the base on `Sigma.fst '' S'`.
-/

namespace FlagAlgebras.MetaTheory

open FlagAlgebras LabeledSubgraph

variable {n k : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}

/-- The base graph `G` with its labelling `θ`, as a labelled graph (flag). -/
def baseLabeledGraph (θ : H ↪g G) : LabeledGraph H (Fin n) where
  graph := G
  type_embed := θ

/-- The independent blow-up with the planted labelling `θ̂ : i ↦ ⟨θ i, c i⟩`, as a labelled
graph (the planted flag `(B_N, θ̂)`). -/
def blowupLabeledGraph (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    LabeledGraph H (Σ v : Fin n, Fin (m v)) where
  graph := independentBlowup G m
  type_embed := blowupPlantedEmb m θ c

/-- The base labelling evaluates to `θ i`. -/
@[simp] lemma baseLabeledGraph_type_embed (θ : H ↪g G) (i : Fin k) :
    (baseLabeledGraph θ).type_embed i = θ i := rfl

/-- The planted labelling evaluates to `⟨θ i, c i⟩`. -/
@[simp] lemma blowupLabeledGraph_type_embed (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (i : Fin k) : (blowupLabeledGraph m θ c).type_embed i = ⟨θ i, c i⟩ := rfl

/-- The projection sends the planted roots onto the base roots. -/
lemma blowupLabeledGraph_type_verts_image (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    Sigma.fst '' (blowupLabeledGraph m θ c).type_verts = (baseLabeledGraph θ).type_verts := by
  ext v
  simp only [LabeledGraph.type_verts, Set.image_univ, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(blowupLabeledGraph m θ c).type_embed i, ⟨i, rfl⟩, rfl⟩

/-- **Good-event flag isomorphism** (`lem:planted-estimate`): on a set `S'` of blow-up vertices
meeting each clone class at most once and containing the planted roots, the induced labelled
subgraph of the blow-up on `S'` is `≃f` the induced labelled subgraph of the base on the
projection `Sigma.fst '' S'`. -/
noncomputable def blowupGoodIso (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    {S' : Set (Σ v : Fin n, Fin (m v))} (hinj : Set.InjOn Sigma.fst S')
    (hroot : (blowupLabeledGraph m θ c).type_verts ⊆ S')
    (hπ : (baseLabeledGraph θ).type_verts ⊆ Sigma.fst '' S') :
    (inducedLabeledSubgraph (blowupLabeledGraph m θ c) S' hroot).coe
      ≃f (inducedLabeledSubgraph (baseLabeledGraph θ) (Sigma.fst '' S') hπ).coe := by
  set Bsub := inducedLabeledSubgraph (blowupLabeledGraph m θ c) S' hroot with hBsub
  set Gsub := inducedLabeledSubgraph (baseLabeledGraph θ) (Sigma.fst '' S') hπ with hGsub
  have hBv : Bsub.subgraph.verts = S' := by
    simp only [hBsub, inducedLabeledSubgraph_verts]
  have hGv : Gsub.subgraph.verts = Sigma.fst '' S' := by
    simp only [hGsub, inducedLabeledSubgraph_verts]
  -- The vertex bijection: projection `Sigma.fst` restricted to `S'`, transported across the
  -- vertex-set equalities so the subtypes line up.
  let e : ↥Bsub.subgraph.verts ≃ ↥Gsub.subgraph.verts :=
    (Equiv.setCongr hBv).trans
      ((Equiv.Set.imageOfInjOn Sigma.fst S' hinj).trans (Equiv.setCongr hGv).symm)
  have he : ∀ u : ↥Bsub.subgraph.verts, (e u).val = (u.val).1 := by
    intro u; rfl
  let graph_iso : Bsub.coe.graph ≃g Gsub.coe.graph :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        rw [coe_adj_iff, coe_adj_iff]
        simp only [hBsub, hGsub, inducedLabeledSubgraph, SimpleGraph.Subgraph.induce,
          baseLabeledGraph, blowupLabeledGraph]
        have hu : (↑u : Σ v : Fin n, Fin (m v)) ∈ S' := hBv ▸ u.property
        have hv : (↑v : Σ v : Fin n, Fin (m v)) ∈ S' := hBv ▸ v.property
        rw [he u, he v]
        constructor
        · rintro ⟨_, _, hadj⟩
          exact ⟨hu, hv, hadj⟩
        · rintro ⟨_, _, hadj⟩
          exact ⟨⟨_, hu, rfl⟩, ⟨_, hv, rfl⟩, hadj⟩ }
  refine { graph_iso := graph_iso, type_preserve := ?_ }
  funext t
  apply Subtype.ext
  show (e (Bsub.coe.type_embed t)).val = (Gsub.coe.type_embed t).val
  rw [he (Bsub.coe.type_embed t)]
  rfl

/-- **Good event preserves the induced flag**: on a good vertex set, the induced labelled
subgraph of the blow-up is `≃f F₀` iff the induced labelled subgraph of the base on the
projection is.  (Immediate from `blowupGoodIso` by composition.) -/
lemma good_event_induces_iff {U : Type} (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    {S' : Set (Σ v : Fin n, Fin (m v))} (hinj : Set.InjOn Sigma.fst S')
    (hroot : (blowupLabeledGraph m θ c).type_verts ⊆ S')
    (hπ : (baseLabeledGraph θ).type_verts ⊆ Sigma.fst '' S') (F₀ : LabeledGraph H U) :
    Nonempty ((inducedLabeledSubgraph (blowupLabeledGraph m θ c) S' hroot).coe ≃f F₀)
      ↔ Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (Sigma.fst '' S') hπ).coe ≃f F₀) := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨(blowupGoodIso m θ c hinj hroot hπ).symm.trans φ⟩
  · rintro ⟨φ⟩
    exact ⟨(blowupGoodIso m θ c hinj hroot hπ).trans φ⟩

end FlagAlgebras.MetaTheory
