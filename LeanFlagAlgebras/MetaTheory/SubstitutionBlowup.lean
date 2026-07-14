import LeanFlagAlgebras.MetaTheory.BlowupFlag

/-! # The generalised (substitution) blow-up (paper §6–§7)

The independent blow-up of §5 replaces each vertex `v` of `G` by an **edgeless** clone class.
Sections 6 and 7 replace it by a **clique** (complete blow-up `G^{m,+}`, `def:complete-blow-up`)
or by an **arbitrary in-class graph** `H_v` (substitution `G[H_v]`, `def:graph-substitution`).
All three share the same *between-class* adjacency, governed by `G`; they differ only **inside**
the clone classes.

This file packages the common generalisation `subBlowup G m W`, with a within-class family
`W : ∀ v, SimpleGraph (Fin (m v))`:

* independent blow-up  = `subBlowup G m (fun _ => ⊥)`,
* complete blow-up     = `subBlowup G m (fun _ => ⊤)`   (`completeBlowup`),
* substitution         = `subBlowup G m W` with `W v = H_v`.

The key structural fact (`subBlowup_adj_of_fst_ne`) is that **off the diagonal** — when the two
base vertices differ — the adjacency is exactly `G.Adj p.1 q.1`, identical to the independent
blow-up.  Consequently, on any vertex set `S'` on which `Sigma.fst` is injective (a *good* set,
meeting each clone class at most once), the induced labelled subgraph of `subBlowup` coincides
with that of `independentBlowup` (`subBlowupToIndepIso`), which by §5's `blowupGoodIso` is `≃f`
the induced labelled subgraph of the base.  This is what lets the §5 planted estimate carry over
unchanged (`good_event_induces_iff_sub`).
-/

namespace FlagAlgebras.MetaTheory

open SimpleGraph FlagAlgebras LabeledSubgraph

section General
variable {V : Type*} {m : V → ℕ}

/-! ## The construction -/

/-- The **generalised blow-up** `subBlowup G W`: vertex set `Σ v, Fin (m v)`; two vertices in
*distinct* clone classes are adjacent iff their base vertices are `G`-adjacent, and two vertices
in the *same* clone class `v` are adjacent according to the within-class graph `W v`.  Encoded with
an existential over the base-equality proof so no `DecidableEq V` is needed. -/
def subBlowup (G : SimpleGraph V) (W : ∀ v, SimpleGraph (Fin (m v))) :
    SimpleGraph (Σ v : V, Fin (m v)) where
  Adj p q := G.Adj p.1 q.1 ∨ ∃ h : q.1 = p.1, (W p.1).Adj p.2 (h ▸ q.2)
  symm := by
    rintro ⟨pv, pi⟩ ⟨qv, qi⟩ (hadj | ⟨h, hadj⟩)
    · exact Or.inl (G.symm hadj)
    · cases h
      exact Or.inr ⟨rfl, (W pv).symm hadj⟩
  loopless := by
    rintro p (hadj | ⟨_, hadj⟩)
    · exact G.loopless p.1 hadj
    · exact (W p.1).loopless p.2 hadj

/-- **Off-diagonal agreement**: when the two base vertices differ, `subBlowup` adjacency is exactly
the base adjacency `G.Adj p.1 q.1` — identical to the independent blow-up.  This is the only fact
about `subBlowup` that the planted estimate ever needs (it always samples good sets). -/
@[simp]
lemma subBlowup_adj_of_fst_ne (G : SimpleGraph V) (W : ∀ v, SimpleGraph (Fin (m v)))
    {p q : Σ v : V, Fin (m v)} (h : q.1 ≠ p.1) :
    (subBlowup G W).Adj p q ↔ G.Adj p.1 q.1 := by
  show (G.Adj p.1 q.1 ∨ ∃ h' : q.1 = p.1, (W p.1).Adj p.2 (h' ▸ q.2)) ↔ G.Adj p.1 q.1
  refine ⟨fun hh => hh.elim id (fun ⟨h', _⟩ => absurd h' h), Or.inl⟩

/-- The complete blow-up `G^{m,+}` (`def:complete-blow-up`): each clone class is a clique
(`W v = ⊤`). -/
abbrev completeBlowup (G : SimpleGraph V) (m : V → ℕ) : SimpleGraph (Σ v : V, Fin (m v)) :=
  subBlowup G (fun _ : V => (⊤ : SimpleGraph (Fin (m _))))

end General

/-! ## The planted labelling and the labelled graph -/

variable {n k : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}

/-- The **planted labelling** as an induced graph embedding into the generalised blow-up: placing
each labelled vertex `i` at the clone `⟨θ i, c i⟩` embeds the type graph `H`.  Distinct labels go
to distinct clone classes (`θ` injective), so their adjacency is the off-diagonal value
`G.Adj (θ i) (θ j) ↔ H.Adj i j`. -/
def subBlowupPlantedEmb (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) (θ : H ↪g G)
    (c : ∀ i, Fin (m (θ i))) : H ↪g subBlowup G W where
  toFun i := ⟨θ i, c i⟩
  inj' i j h := θ.injective (congrArg Sigma.fst h)
  map_rel_iff' := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [SimpleGraph.irrefl]
    · have hθ : (θ b) ≠ (θ a) := fun h => hab (θ.injective h.symm)
      rw [subBlowup_adj_of_fst_ne G W hθ]
      exact θ.map_adj_iff

/-- The generalised blow-up with the planted labelling `θ̂ : i ↦ ⟨θ i, c i⟩`, as a labelled graph.
For `W = fun _ => ⊥` this is §5's `blowupLabeledGraph`; for `W = fun _ => ⊤` it is the planted
complete blow-up; for general `W` it is the planted substitution. -/
def subBlowupLabeledGraph (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) (θ : H ↪g G)
    (c : ∀ i, Fin (m (θ i))) : LabeledGraph H (Σ v : Fin n, Fin (m v)) where
  graph := subBlowup G W
  type_embed := subBlowupPlantedEmb m W θ c

@[simp] lemma subBlowupLabeledGraph_type_embed (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v)))
    (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) (i : Fin k) :
    (subBlowupLabeledGraph m W θ c).type_embed i = ⟨θ i, c i⟩ := rfl

/-- The planted roots of the generalised blow-up are exactly those of the independent blow-up:
`{⟨θ i, c i⟩}` either way (the labelling does not see the within-class structure). -/
lemma subBlowupLabeledGraph_type_verts (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v)))
    (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    (subBlowupLabeledGraph m W θ c).type_verts = (blowupLabeledGraph m θ c).type_verts := by
  ext p
  simp only [LabeledGraph.mem_type_verts, subBlowupLabeledGraph_type_embed,
    blowupLabeledGraph_type_embed]

/-! ## The good-event isomorphism -/

/-- **Agreement on a good set**: on a vertex set `S'` meeting each clone class at most once
(`Sigma.fst` injective) and containing the planted roots, the induced labelled subgraph of the
generalised blow-up coincides — via the identity vertex map — with that of the independent
blow-up.  Indeed any two distinct vertices of `S'` have distinct base vertices, so their adjacency
is the common off-diagonal value `G.Adj`. -/
noncomputable def subBlowupToIndepIso (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v)))
    (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    {S' : Set (Σ v : Fin n, Fin (m v))} (hinj : Set.InjOn Sigma.fst S')
    (hroot : (subBlowupLabeledGraph m W θ c).type_verts ⊆ S')
    (hroot' : (blowupLabeledGraph m θ c).type_verts ⊆ S') :
    (inducedLabeledSubgraph (subBlowupLabeledGraph m W θ c) S' hroot).coe
      ≃f (inducedLabeledSubgraph (blowupLabeledGraph m θ c) S' hroot').coe := by
  set Bsub := inducedLabeledSubgraph (subBlowupLabeledGraph m W θ c) S' hroot with hBsub
  set Gsub := inducedLabeledSubgraph (blowupLabeledGraph m θ c) S' hroot' with hGsub
  have hBv : Bsub.subgraph.verts = S' := by simp only [hBsub, inducedLabeledSubgraph_verts]
  have hGv : Gsub.subgraph.verts = S' := by simp only [hGsub, inducedLabeledSubgraph_verts]
  -- The vertex bijection: the identity on `S'`, transported across the two vertex-set equalities.
  let e : ↥Bsub.subgraph.verts ≃ ↥Gsub.subgraph.verts :=
    (Equiv.setCongr hBv).trans (Equiv.setCongr hGv).symm
  have he : ∀ u : ↥Bsub.subgraph.verts, (e u).val = u.val := fun u => rfl
  let graph_iso : Bsub.coe.graph ≃g Gsub.coe.graph :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        rw [coe_adj_iff, coe_adj_iff]
        simp only [hBsub, hGsub, inducedLabeledSubgraph, SimpleGraph.Subgraph.induce, Subgraph.top_adj]
        have hu : (↑u : Σ v : Fin n, Fin (m v)) ∈ S' := hBv ▸ u.property
        have hv : (↑v : Σ v : Fin n, Fin (m v)) ∈ S' := hBv ▸ v.property
        rw [he u, he v]
        -- Both reduce to `<graph>.Adj u v ∧ u ∈ S' ∧ v ∈ S'`; the side conditions match, so it
        -- remains to compare the two graph adjacencies, which agree off the diagonal.
        refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
        by_cases hfst : (v.val).1 = (u.val).1
        · -- same clone class ⟹ injectivity forces `u = v` ⟹ both adjacencies are `False`.
          have huv : (u.val : Σ v : Fin n, Fin (m v)) = v.val := hinj hu hv hfst.symm
          rw [huv]
          simp only [SimpleGraph.irrefl]
        · show (independentBlowup G m).Adj _ _ ↔ (subBlowup G W).Adj _ _
          rw [independentBlowup_adj, subBlowup_adj_of_fst_ne G W hfst] }
  refine { graph_iso := graph_iso, type_preserve := ?_ }
  funext t
  apply Subtype.ext
  show (e (Bsub.coe.type_embed t)).val = (Gsub.coe.type_embed t).val
  rw [he (Bsub.coe.type_embed t)]
  rfl

/-- **Good event preserves the induced flag** (generalised): on a good vertex set, the induced
labelled subgraph of the generalised blow-up is `≃f F₀` iff the induced labelled subgraph of the
base on the projection is.  This is `BlowupFlag.good_event_induces_iff` carried across
`subBlowupToIndepIso`. -/
lemma good_event_induces_iff_sub {U : Type} (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v)))
    (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    {S' : Set (Σ v : Fin n, Fin (m v))} (hinj : Set.InjOn Sigma.fst S')
    (hroot : (subBlowupLabeledGraph m W θ c).type_verts ⊆ S')
    (hπ : (baseLabeledGraph θ).type_verts ⊆ Sigma.fst '' S') (F₀ : LabeledGraph H U) :
    Nonempty ((inducedLabeledSubgraph (subBlowupLabeledGraph m W θ c) S' hroot).coe ≃f F₀)
      ↔ Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (Sigma.fst '' S') hπ).coe ≃f F₀) := by
  have hroot' : (blowupLabeledGraph m θ c).type_verts ⊆ S' := by
    rw [← subBlowupLabeledGraph_type_verts m W θ c]; exact hroot
  rw [← good_event_induces_iff m θ c hinj hroot' hπ F₀]
  constructor
  · rintro ⟨φ⟩; exact ⟨(subBlowupToIndepIso m W θ c hinj hroot hroot').symm.trans φ⟩
  · rintro ⟨φ⟩; exact ⟨(subBlowupToIndepIso m W θ c hinj hroot hroot').trans φ⟩

end FlagAlgebras.MetaTheory
