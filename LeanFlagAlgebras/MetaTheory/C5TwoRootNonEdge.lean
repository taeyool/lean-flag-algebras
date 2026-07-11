import LeanFlagAlgebras.MetaTheory.C5Free
import LeanFlagAlgebras.MetaTheory.SparseRootRepair

/-! # `C₅`-free root-plantability at the two-root non-edge type (paper §8)

The same local-repair idea works for the two-vertex non-edge type `η`: clone both roots into two
independent clusters with no edges between them, and delete the old edges inside each
root-neighbourhood.  Mixed five-cycles using one clone of each root project back to genuine `C₅`s in
the original graph (using that `rs` is a non-edge); cycles using two clones from the same cluster are
killed by the neighbourhood-edge deletion.

This file builds the two-root non-edge planting `P_L(G,r,s)` and proves it `C₅`-free; the
sparse-root-repair instance, the root-plantability theorem (`thm:c5-nonedge-root`), and the blow-up
comparison (`lem:c5-blowup`) are added once [`SparseRootRepair`](./SparseRootRepair.lean) is
available.
-/

open FlagAlgebras SimpleGraph

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-- The two-root non-edge type: two labelled vertices with no edge between them. -/
abbrev twoNonEdgeType : FlagType (Fin 2) := ⊥

/-- **Two-root non-edge planting** `P_L(G,r,s)` (`def:c5-nonedge-planting`), with `r = θ 0`,
`s = θ 1`.  Two independent clusters `R` (joined to `N(r)`) and `S` (joined to `N(s)`), no edges
between or inside the clusters; inside `U` keep every `G`-edge except those with both endpoints in
`N(r)` or both endpoints in `N(s)`. -/
def twoRootPlant {n : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n)) (L : ℕ) :
    SimpleGraph ({v : Fin n // v ∉ Set.range G.type_embed} ⊕ (Fin 2 × Fin L)) where
  Adj p q :=
    match p, q with
    | Sum.inl u, Sum.inl u' =>
        G.graph.Adj u.1 u'.1 ∧
          ¬ (G.graph.Adj (G.type_embed 0) u.1 ∧ G.graph.Adj (G.type_embed 0) u'.1) ∧
          ¬ (G.graph.Adj (G.type_embed 1) u.1 ∧ G.graph.Adj (G.type_embed 1) u'.1)
    | Sum.inl u, Sum.inr (i, _) => G.graph.Adj (G.type_embed i) u.1
    | Sum.inr (i, _), Sum.inl u => G.graph.Adj (G.type_embed i) u.1
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (u | ⟨i, a⟩) (u' | ⟨j, b⟩) h
    · exact ⟨h.1.symm, fun hc => h.2.1 ⟨hc.2, hc.1⟩, fun hc => h.2.2 ⟨hc.2, hc.1⟩⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    rintro (u | ⟨i, a⟩) h
    · exact G.graph.irrefl h.1
    · exact h

/-- A `C₅`-neighbour of a cluster-`k` position must itself be an `inl` vertex, and its underlying
vertex lies in the `G`-neighbourhood of the labelled root `θ k` (from the `inl`–`inr` adjacency of
the planting). -/
private lemma cluster_nbhd {n L : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (f : C5g →g twoRootPlant G L) {p c : Fin 5} (hpc : C5g.Adj p c)
    {k : Fin 2} {a : Fin L} (hp : f p = Sum.inr (k, a)) :
    ∃ u : {v : Fin n // v ∉ Set.range G.type_embed},
      f c = Sum.inl u ∧ G.graph.Adj (G.type_embed k) u.1 := by
  have h := f.map_adj hpc
  rw [hp] at h
  rcases hfc : f c with u | ⟨k', a'⟩
  · rw [hfc] at h; exact ⟨u, rfl, h⟩
  · rw [hfc] at h; exact h.elim

/-- If two consecutive `inl` positions are each adjacent (in `C₅`) to a cluster-`k` position, both
their underlying vertices lie in `N(θ k)`, so the surviving `inl`–`inl` edge between them violates
the neighbourhood-edge deletion at root `θ k`. -/
private lemma same_cluster_step {n L : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (f : C5g →g twoRootPlant G L) {pc pd c d : Fin 5} (hcd : C5g.Adj c d)
    (hpc : C5g.Adj pc c) (hpd : C5g.Adj pd d)
    {k : Fin 2} {cc cd : Fin L}
    (hfpc : f pc = Sum.inr (k, cc)) (hfpd : f pd = Sum.inr (k, cd)) :
    False := by
  obtain ⟨u, hfc, hu⟩ := cluster_nbhd G f hpc hfpc
  obtain ⟨u', hfd, hu'⟩ := cluster_nbhd G f hpd hfpd
  have h := f.map_adj hcd
  rw [hfc, hfd] at h
  fin_cases k
  · exact h.2.1 ⟨hu, hu'⟩
  · exact h.2.2 ⟨hu, hu'⟩

/-- Two distinct `C₅` positions cannot both map into the *same* cluster.  They are non-adjacent in
`C₅` (clusters are independent), so the cluster positions form an independent set of size `≤ 2`;
hence some consecutive pair of the three remaining positions are both joined to the cluster, and
`same_cluster_step` derives a contradiction with the neighbourhood-edge deletion. -/
private lemma same_cluster_absurd {n L : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (f : C5g →g twoRootPlant G L) {a b : Fin 5} (hab : a ≠ b)
    {k : Fin 2} {ca cb : Fin L} (ha : f a = Sum.inr (k, ca)) (hb : f b = Sum.inr (k, cb)) :
    False := by
  have hnotadj : ¬ C5g.Adj a b := by
    intro hadj
    have h := f.map_adj hadj
    rw [ha, hb] at h; exact h
  fin_cases a <;> fin_cases b <;>
    first
    | (exact absurd rfl hab)
    | (exact absurd (by decide) hnotadj)
    | (first
        | exact same_cluster_step G f (c := 0) (d := 1) (by decide) (by decide) (by decide) ha hb
        | exact same_cluster_step G f (c := 0) (d := 1) (by decide) (by decide) (by decide) hb ha
        | exact same_cluster_step G f (c := 1) (d := 2) (by decide) (by decide) (by decide) ha hb
        | exact same_cluster_step G f (c := 1) (d := 2) (by decide) (by decide) (by decide) hb ha
        | exact same_cluster_step G f (c := 2) (d := 3) (by decide) (by decide) (by decide) ha hb
        | exact same_cluster_step G f (c := 2) (d := 3) (by decide) (by decide) (by decide) hb ha
        | exact same_cluster_step G f (c := 3) (d := 4) (by decide) (by decide) (by decide) ha hb
        | exact same_cluster_step G f (c := 3) (d := 4) (by decide) (by decide) (by decide) hb ha
        | exact same_cluster_step G f (c := 4) (d := 0) (by decide) (by decide) (by decide) ha hb
        | exact same_cluster_step G f (c := 4) (d := 0) (by decide) (by decide) (by decide) hb ha)

/-- The projection sending an `inl` vertex to its underlying vertex of `G` and an `inr` cluster
vertex to its labelled root `θ k`. -/
private noncomputable def twoRootProj {n L : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (p : {v : Fin n // v ∉ Set.range G.type_embed} ⊕ (Fin 2 × Fin L)) : Fin n :=
  Sum.elim (·.1) (fun q => G.type_embed q.1) p

/-- The projection turns every `C₅`-edge of the planting into a genuine `G`-edge: `inl`–`inl` edges
are `G`-edges by the first conjunct, and an `inl`–`inr` edge is exactly an edge to the root `θ k`,
which the projection sends to `θ k`.  (Two cluster positions are never adjacent.) -/
private lemma twoRootProj_edge {n L : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (f : C5g →g twoRootPlant G L) {i j : Fin 5} (hij : C5g.Adj i j) :
    G.graph.Adj (twoRootProj G (f i)) (twoRootProj G (f j)) := by
  have h := f.map_adj hij
  rcases hi : f i with u | ⟨ki, ai⟩ <;> rcases hj : f j with u' | ⟨kj, aj⟩ <;>
    rw [hi, hj] at h <;> simp only [twoRootProj, Sum.elim_inl, Sum.elim_inr]
  · exact h.1
  · exact (show G.graph.Adj (G.type_embed kj) u.1 from h).symm
  · exact (show G.graph.Adj (G.type_embed ki) u'.1 from h)
  · exact h.elim

/-- The projection is injective on distinct `C₅` positions: two `inl`s give distinct underlying
vertices (else `f` would identify them), an `inl` and an `inr` differ because an `inl` vertex is by
construction *not* in the range of `θ`, and two `inr`s in the same cluster are ruled out by
`same_cluster_absurd` (distinct clusters give distinct roots since `θ` is injective). -/
private lemma twoRootProj_ne {n L : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (f : C5g →g twoRootPlant G L) (hf : Function.Injective f)
    {i j : Fin 5} (hij : i ≠ j) : twoRootProj G (f i) ≠ twoRootProj G (f j) := by
  intro heq
  rcases hi : f i with u | ⟨ki, ai⟩ <;> rcases hj : f j with u' | ⟨kj, aj⟩ <;>
    simp only [twoRootProj, hi, hj, Sum.elim_inl, Sum.elim_inr] at heq
  · exact hij (hf (by rw [hi, hj, Subtype.ext heq]))
  · exact u.2 ⟨kj, heq.symm⟩
  · exact u'.2 ⟨ki, heq⟩
  · have hk : ki = kj := G.type_embed.injective heq
    subst hk
    exact same_cluster_absurd G f hij hi hj

/-- **The two-root non-edge planted graph is `C₅`-free** (`lem:c5-nonedge-planting-free`).  If `G` is
`C₅`-free and `rs` is a non-edge, then `P_L(G,r,s)` is `C₅`-free for every `L`.

Given a copy `φ` of `C₅` in the planting, the cluster part is independent (`α(C₅) = 2`), so the
five images project to five vertices of `G` via `twoRootProj` (an `inr` clone goes to its root).
Every consecutive `C₅`-edge becomes a `G`-edge (`twoRootProj_edge`) and the five projections stay
pairwise distinct (`twoRootProj_ne`; the only way distinctness could fail — two clones of the same
root — is killed by the neighbourhood-edge deletion via `same_cluster_absurd`).  This rebuilds a
genuine `C₅` in `G` (`c5_copy_of_pentagon`), contradicting `hG`.  The non-edge hypothesis `hrs` is
not needed: two cluster positions are never adjacent, so a missing `rs`-edge never has to be
supplied. -/
theorem twoRootPlant_c5free {n : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (hG : C5g.Free G.graph) (_hrs : ¬ G.graph.Adj (G.type_embed 0) (G.type_embed 1)) (L : ℕ) :
    C5g.Free (twoRootPlant G L) := by
  rintro ⟨φ⟩
  set f := φ.toHom with hfdef
  have hf : Function.Injective f := φ.injective'
  exact hG (c5_copy_of_pentagon G.graph
    (twoRootProj G (f 0)) (twoRootProj G (f 1)) (twoRootProj G (f 2)) (twoRootProj G (f 3))
    (twoRootProj G (f 4))
    (twoRootProj_edge G f (by decide)) (twoRootProj_edge G f (by decide))
    (twoRootProj_edge G f (by decide)) (twoRootProj_edge G f (by decide))
    (twoRootProj_edge G f (by decide))
    (twoRootProj_ne G f hf (by decide)) (twoRootProj_ne G f hf (by decide))
    (twoRootProj_ne G f hf (by decide)) (twoRootProj_ne G f hf (by decide))
    (twoRootProj_ne G f hf (by decide)) (twoRootProj_ne G f hf (by decide))
    (twoRootProj_ne G f hf (by decide)) (twoRootProj_ne G f hf (by decide))
    (twoRootProj_ne G f hf (by decide)) (twoRootProj_ne G f hf (by decide)))

/-! ## Sparse root-blow-up repairs at the two-root non-edge type -/

/-- **Per-neighbourhood edge bound.**  Any family of non-root pairs whose two endpoints are
`G`-adjacent and both lie in `N_G(w)` injects into the edge set of `G[N(w)]` (the inclusion
`u ↦ ⟨u.1, _⟩` is injective on members), so the family has cardinality at most `e(G[N(w)])`. -/
private lemma neighbourhood_edge_bound {n : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n)) (w : Fin n)
    (P : Sym2 (nonRoot G) → Prop) [DecidablePred P]
    (hP : ∀ (u u' : nonRoot G), P s(u, u') →
        G.graph.Adj u.1 u'.1 ∧ G.graph.Adj w u.1 ∧ G.graph.Adj w u'.1) :
    (Finset.univ.filter P).card ≤ (G.graph.induce (G.graph.neighborSet w)).edgeFinset.card := by
  classical
  rcases (Finset.univ.filter P).eq_empty_or_nonempty with hemp | ⟨p0, hp0⟩
  · rw [hemp]; simp
  · -- A witness vertex in `N(w)`, used as a (never-hit) default for the inclusion.
    have hwit : ∃ x : Fin n, x ∈ G.graph.neighborSet w := by
      rw [Finset.mem_filter] at hp0
      induction p0 using Sym2.ind with
      | _ u u' => exact ⟨u.1, (hP u u' hp0.2).2.1⟩
    obtain ⟨x0, hx0⟩ := hwit
    let incl : nonRoot G → ↥(G.graph.neighborSet w) := fun u =>
      if h : (u.1) ∈ G.graph.neighborSet w then ⟨u.1, h⟩ else ⟨x0, hx0⟩
    have hinclinj : ∀ u u' : nonRoot G, u.1 ∈ G.graph.neighborSet w →
        u'.1 ∈ G.graph.neighborSet w → incl u = incl u' → u = u' := by
      intro u u' hu hu' h
      simp only [incl, hu, hu', dif_pos, Subtype.mk.injEq] at h
      exact Subtype.ext h
    apply Finset.card_le_card_of_injOn (Sym2.map incl)
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      induction p using Sym2.ind with
      | _ u u' =>
        obtain ⟨hg, hwu, hwu'⟩ := hP u u' hp.2
        have hu : u.1 ∈ G.graph.neighborSet w := hwu
        have hu' : u'.1 ∈ G.graph.neighborSet w := hwu'
        simp only [Sym2.map_pair_eq, incl, hu, hu', dif_pos]
        rw [Finset.mem_coe, mem_edgeFinset, mem_edgeSet, comap_adj]
        simpa using hg
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      induction p using Sym2.ind with
      | _ u u' =>
        induction q using Sym2.ind with
        | _ v v' =>
          obtain ⟨_, hwu, hwu'⟩ := hP u u' hp.2
          obtain ⟨_, hwv, hwv'⟩ := hP v v' hq.2
          have hu : u.1 ∈ G.graph.neighborSet w := hwu
          have hu' : u'.1 ∈ G.graph.neighborSet w := hwu'
          have hv : v.1 ∈ G.graph.neighborSet w := hwv
          have hv' : v'.1 ∈ G.graph.neighborSet w := hwv'
          rw [Sym2.map_pair_eq, Sym2.map_pair_eq, Sym2.eq_iff] at hpq
          rw [Sym2.eq_iff]
          rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨hinclinj u v hu hv h1, hinclinj u' v' hu' hv' h2⟩
          · exact Or.inr ⟨hinclinj u v' hu hv' h1, hinclinj u' v hu' hv h2⟩

/-- **Clause (iii) for the two-root non-edge planting** (the sparse-repair bound).  An "altered"
non-root pair (one whose `G`-adjacency the planting changed) is exactly a `G`-edge with both
endpoints in `N(r)` or both endpoints in `N(s)`.  Each family injects into the corresponding
neighbourhood's edge set, of size `≤ |N| ≤ n` (`lem:c5-nbhd`); hence at most `2n` altered pairs. -/
private lemma altered_card_le_two {n : ℕ} (G : LabeledGraph twoNonEdgeType (Fin n))
    (hMem : C5g.Free G.graph) (L : ℕ) :
    ((Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
        ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => (twoRootPlant G L).Adj (Sum.inl u) (Sum.inl u')
              ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p)).card : ℝ)
      ≤ 2 * (n : ℝ) := by
  classical
  set r : Fin n := G.type_embed 0 with hr
  set s : Fin n := G.type_embed 1 with hs
  set Filt : Finset (Sym2 (nonRoot G)) := Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
      ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => (twoRootPlant G L).Adj (Sum.inl u) (Sum.inl u')
            ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p) with hFilt
  set PR : Sym2 (nonRoot G) → Prop := fun p => Sym2.lift
      ⟨fun u u' => G.graph.Adj u.1 u'.1 ∧ G.graph.Adj r u.1 ∧ G.graph.Adj r u'.1,
        by intro u u'; simp only [adj_comm, eq_iff_iff]; tauto⟩ p with hPR
  set PS : Sym2 (nonRoot G) → Prop := fun p => Sym2.lift
      ⟨fun u u' => G.graph.Adj u.1 u'.1 ∧ G.graph.Adj s u.1 ∧ G.graph.Adj s u'.1,
        by intro u u'; simp only [adj_comm, eq_iff_iff]; tauto⟩ p with hPS
  -- Every altered pair is a `G`-edge contained in `N(r)` or in `N(s)`.
  have hsub : Filt ⊆ Finset.univ.filter PR ∪ Finset.univ.filter PS := by
    intro p hp
    induction p using Sym2.ind with
    | _ u u' =>
      rw [hFilt, Finset.mem_filter] at hp
      have halt := hp.2.2
      rw [Sym2.lift_mk] at halt
      replace halt : (twoRootPlant G L).Adj (Sum.inl u) (Sum.inl u') ≠ G.graph.Adj u.1 u'.1 := halt
      have hadj : (twoRootPlant G L).Adj (Sum.inl u) (Sum.inl u')
          = (G.graph.Adj u.1 u'.1 ∧
              ¬ (G.graph.Adj r u.1 ∧ G.graph.Adj r u'.1) ∧
              ¬ (G.graph.Adj s u.1 ∧ G.graph.Adj s u'.1)) := rfl
      rw [hadj] at halt
      have hkey : G.graph.Adj u.1 u'.1 ∧
          ((G.graph.Adj r u.1 ∧ G.graph.Adj r u'.1) ∨ (G.graph.Adj s u.1 ∧ G.graph.Adj s u'.1)) := by
        by_cases hg : G.graph.Adj u.1 u'.1
        · refine ⟨hg, ?_⟩
          by_contra hc
          push_neg at hc
          apply halt
          rw [eq_iff_iff]
          exact ⟨fun _ => hg,
            fun _ => ⟨hg, fun hpr => (hc.1 hpr.1) hpr.2, fun hpr => (hc.2 hpr.1) hpr.2⟩⟩
        · exact absurd (by rw [eq_iff_iff]; exact ⟨fun hh => absurd hh.1 hg, fun hh => absurd hh hg⟩)
            halt
      simp only [Finset.mem_union, Finset.mem_filter, hPR, hPS, Sym2.lift_mk, Finset.mem_univ,
        true_and]
      rcases hkey.2 with hrr | hss
      · exact Or.inl ⟨hkey.1, hrr.1, hrr.2⟩
      · exact Or.inr ⟨hkey.1, hss.1, hss.2⟩
  have hboundR : (Finset.univ.filter PR).card
      ≤ (G.graph.induce (G.graph.neighborSet r)).edgeFinset.card := by
    apply neighbourhood_edge_bound G r PR
    intro u u' hpr; rw [hPR, Sym2.lift_mk] at hpr; exact hpr
  have hboundS : (Finset.univ.filter PS).card
      ≤ (G.graph.induce (G.graph.neighborSet s)).edgeFinset.card := by
    apply neighbourhood_edge_bound G s PS
    intro u u' hps; rw [hPS, Sym2.lift_mk] at hps; exact hps
  have hNr : (G.graph.induce (G.graph.neighborSet r)).edgeFinset.card ≤ n := by
    calc (G.graph.induce (G.graph.neighborSet r)).edgeFinset.card
        ≤ Fintype.card (G.graph.neighborSet r) := c5free_neighborhood_edge_card_le G.graph hMem r
      _ ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
      _ = n := Fintype.card_fin n
  have hNs : (G.graph.induce (G.graph.neighborSet s)).edgeFinset.card ≤ n := by
    calc (G.graph.induce (G.graph.neighborSet s)).edgeFinset.card
        ≤ Fintype.card (G.graph.neighborSet s) := c5free_neighborhood_edge_card_le G.graph hMem s
      _ ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
      _ = n := Fintype.card_fin n
  have hcard : Filt.card ≤ 2 * n := by
    calc Filt.card ≤ (Finset.univ.filter PR ∪ Finset.univ.filter PS).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter PR).card + (Finset.univ.filter PS).card := Finset.card_union_le _ _
      _ ≤ n + n := Nat.add_le_add (hboundR.trans hNr) (hboundS.trans hNs)
      _ = 2 * n := by ring
  calc (Filt.card : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * (n : ℝ) := by push_cast; ring

/-- **Sparse root-blow-up repairs hold for the `C₅`-free class at the two-root non-edge type**
(`def:sparse-root-repair` for this `(K, σ)`).  Given `λ, ρ`, set the cluster size to
`L = ⌊λn⌋ ∈ [λn/2, λn]` and take `H = P_L(G,r,s)`.  Membership is `twoRootPlant_c5free` (the non-edge
`rs` holds because the type is `⊥`); the cross-adjacency clauses (i)/(ii) hold by construction (both
sides of (i) are `False` since the type has no edge; (ii) is definitional); the within-`U` repair
deletes at most `2n ≤ ρn²` old pairs (`altered_card_le_two`, using `n ≥ 2/ρ`). -/
theorem c5FreeClass_sparseRootRepair_twoNonEdge :
    SparseRootRepair c5FreeClass twoNonEdgeType := by
  refine ⟨by norm_num, ?_⟩
  intro lam ρ hlam0 hlam1 hρ0
  refine ⟨max ⌈2 / lam⌉₊ (max ⌈2 / ρ⌉₊ 2), ?_⟩
  intro n G hMem hn
  -- Unpack the threshold into the real inequalities we need.
  have hge_lam : (2 : ℝ) / lam ≤ n := by
    calc (2 : ℝ) / lam ≤ (⌈2 / lam⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hge_ρ : (2 : ℝ) / ρ ≤ n := by
    calc (2 : ℝ) / ρ ≤ (⌈2 / ρ⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  refine ⟨⌊lam * (n : ℝ)⌋₊, twoRootPlant G ⌊lam * (n : ℝ)⌋₊, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- L ≥ λn/2
    have h2 : (2 : ℝ) ≤ lam * n := by rw [div_le_iff₀ hlam0] at hge_lam; linarith
    have hfloor := Nat.lt_floor_add_one (lam * (n : ℝ))
    nlinarith [Nat.floor_le (show (0 : ℝ) ≤ lam * n by positivity)]
  · -- L ≤ λn
    exact Nat.floor_le (by positivity)
  · -- membership: P_L(G,r,s) is `C₅`-free
    have hrs : ¬ G.graph.Adj (G.type_embed 0) (G.type_embed 1) := by
      intro h
      exact absurd ((type_embed_Adj_iff G 0 1).mpr h) (by simp [twoNonEdgeType])
    exact twoRootPlant_c5free G hMem hrs _
  · -- clause (i): cluster-cluster adjacency; both sides are `False` (`⊥`-type)
    intro i j hij a b
    constructor
    · intro h; exact h.elim
    · intro h
      exact absurd ((type_embed_Adj_iff G i j).mpr h) (by simp [twoNonEdgeType])
  · -- clause (ii): cluster-`U` adjacency is definitional
    intro i a u; exact Iff.rfl
  · -- clause (iii): the sparse-repair bound
    calc _ ≤ 2 * (n : ℝ) := altered_card_le_two G hMem _
      _ ≤ ρ * (n : ℝ) ^ 2 := by
          have h2 : (2 : ℝ) ≤ ρ * n := by rw [div_le_iff₀ hρ0] at hge_ρ; linarith
          nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **`C₅`-free root-plantability at the two-root non-edge type** (`thm:c5-nonedge-root`).  Sparse
root-blow-up repairs (`c5FreeClass_sparseRootRepair_twoNonEdge`) give the finite planting property
(`sparseRootRepair_finitePlanting`), which gives root-plantability
(`finitePlanting_root_plantable`). -/
theorem c5free_two_root_nonedge_plantable :
    RootPlantable (c5FreeClass.constraintOf twoNonEdgeType) :=
  finitePlanting_root_plantable c5FreeClass twoNonEdgeType (by norm_num)
    (sparseRootRepair_finitePlanting c5FreeClass twoNonEdgeType
      c5FreeClass_sparseRootRepair_twoNonEdge)

end FlagAlgebras.MetaTheory
