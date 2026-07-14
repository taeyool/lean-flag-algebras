import LeanFlagAlgebras.MetaTheory.EdgeObstruction

/-! # Star and co-star witnesses for the degeneracy obstructions (paper §9 / §9.2)

The abstract obstructions in [`EdgeObstruction`](./EdgeObstruction.lean) reduce
`thm:degenerate-obstruction` (resp. `cor:codegenerate`) to producing a quotient point
`ψ ∈ Q_vtype` of one-root edge density `≠ 0` (resp. `≠ 1`).  Here we build those witnesses:

* a class containing arbitrarily large **stars** `K_{1,n}` (rooted at the centre) yields a limit
  `ψ` with `ψ(e) = 1` — every leaf is adjacent to the root, so `p(e, K_{1,n}) = 1` for all `n`;
* a class containing arbitrarily large **co-stars** `K_{n} ⊎ K_1` (rooted at the isolated vertex)
  yields a limit `ψ` with `ψ(e) = 0` — the root is adjacent to nothing.

The bridge from a finite-flag sequence to a `Q_vtype` point is Razborov 3.3(a)
(`flagSeq_limit_mem_positiveHom`) together with the compactness of `FlagDensitySpace`
(`increasing_flagSeq_contain_convergent_subseq`); the limit lands in `Q_vtype` because every
forbidden flag has density `0` in an in-class flag (`flagDensity_forbidden_eq_zero_of_mem`, the
`σ`-typed analogue of `HeredClass.forbiddenFree_of_mem`).
-/

open SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## A forbidden σ-flag vanishes in an in-class flag -/

/-- **σ-typed forbidden-freeness.**  A `σ`-flag whose underlying graph is in the class has zero
density of every forbidden `σ`-flag (the `σ`-typed analogue of `HeredClass.forbiddenFree_of_mem`).
-/
theorem flagDensity_forbidden_eq_zero_of_mem (hc : HeredClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {N : ℕ} (G : LabeledGraph σ (Fin N)) (hG : hc.Mem G.graph)
    (F : FinFlag σ) (hF : (hc.constraintOf σ).forbσ F) :
    flagDensity₁ F.2 (⟦G⟧ : Flag σ (Fin N)) = 0 := by
  by_contra hne
  -- Replace `F.2` with a chosen representative `Frep := F.2.out`.
  set Frep : LabeledGraph σ (Fin F.1) := F.2.out with hFrep
  have hF2 : F.2 = (⟦Frep⟧ : Flag σ (Fin F.1)) := (Quotient.out_eq F.2).symm
  rw [hF2] at hne
  -- Positive density yields an inducing vertex subset `S ⊇ G.type_verts`.
  obtain ⟨S, hroot, ⟨φ⟩⟩ := exists_inducing_subset_of_flagDensity₁_ne_zero Frep G hne
  -- The labeled iso gives a graph iso of the induced subgraph onto `Frep.graph`.
  let ψ : (LabeledSubgraph.inducedLabeledSubgraph G (↑S) hroot).coe.graph ≃g Frep.graph :=
    φ.graph_iso
  -- The induced subgraph embeds back into `G.graph` (underlying map `Subtype.val`).
  let emb : (LabeledSubgraph.inducedLabeledSubgraph G (↑S) hroot).coe.graph ↪g G.graph :=
    { toFun := fun u => u.val
      inj' := fun u v huv => Subtype.ext huv
      map_rel_iff' := by
        intro u v
        show G.graph.Adj u.val v.val ↔
          (LabeledSubgraph.inducedLabeledSubgraph G (↑S) hroot).coe.graph.Adj u v
        rw [LabeledSubgraph.coe_adj_iff]
        show G.graph.Adj u.val v.val ↔ ((⊤ : G.graph.Subgraph).induce (↑S)).Adj u.val v.val
        simp only [Subgraph.induce_adj, Subgraph.top_adj]
        constructor
        · intro ha
          refine ⟨?_, ?_, ha⟩
          · have := u.property
            simpa only [LabeledSubgraph.inducedLabeledSubgraph_verts] using this
          · have := v.property
            simpa only [LabeledSubgraph.inducedLabeledSubgraph_verts] using this
        · intro ha; exact ha.2.2 }
  -- Compose `Frep.graph ≃g induced.coe.graph ↪g G.graph`.
  have hembed : Frep.graph ↪g G.graph := emb.comp ψ.symm.toEmbedding
  have hmem : hc.Mem Frep.graph := hc.comap hembed hG
  -- This contradicts `F` being forbidden.
  apply hF
  rw [hF2, hc.underlyingMem_unlabel_mk]
  exact hmem

/-! ## From an in-class flag sequence to a quotient point of prescribed edge density -/

/-- **Witness assembly.**  Given an increasing sequence of `vtype`-flags whose underlying graphs are
all in the class and whose one-root edge densities converge to `c`, there is a quotient point
`ψ ∈ Q_vtype` with `ψ(e) = c`. -/
theorem exists_Qσ_point_edge_eq (hc : HeredClass) (s : FlagSeq vtype) (hinc : Increases s)
    (hmem : ∀ n, hc.underlyingMem (unlabel (s n).2))
    (c : ℝ) (hlim : Tendsto (fun n => (flagDensity₁ edgeFF.2 (s n).2 : ℝ)) atTop (𝓝 c)) :
    ∃ ψ ∈ Qσ (hc.constraintOf vtype).forbσ, (PositiveHomSpace.toPosHom ψ) e = c := by
  classical
  -- Pass to a convergent subsequence and realise its limit as a positive homomorphism.
  obtain ⟨a, ϕ, hmono, hconv⟩ := increasing_flagSeq_contain_convergent_subseq s hinc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (s ∘ ϕ) hconv
  set ψ : PositiveHomSpace vtype := posHomPoint φ with hψ
  -- Pointwise convergence of densities of every flag along the subsequence.
  obtain ⟨_, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  -- For each flag, its in-class density tends to its limit `a F`.
  have hclass : ∀ (k : ℕ), hc.Mem ((s (ϕ k)).2.out).graph := by
    intro k
    have hm := hmem (ϕ k)
    rw [← Quotient.out_eq (s (ϕ k)).2, hc.underlyingMem_unlabel_mk] at hm
    exact hm
  refine ⟨ψ, ?_, ?_⟩
  · -- Membership in `Q_vtype`: every forbidden flag has limit density `0`.
    rw [mem_Qσ_iff]
    intro F hF
    -- `ψ.val F = a F`.
    have hψval : ψ.val F = a F := by
      rw [hψ, posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
    rw [hψval]
    -- The subsequence densities of `F` are all `0`, so the limit `a F` is `0`.
    have hzero : ∀ k, (flagDensity₁ F.2 (s (ϕ k)).2 : ℝ) = 0 := by
      intro k
      rw [← Quotient.out_eq (s (ϕ k)).2]
      exact_mod_cast flagDensity_forbidden_eq_zero_of_mem hc _ (hclass k) F hF
    have hF_tendsto : Tendsto (fun k => (flagDensity₁ F.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 (a F)) := hpt F
    have h0 : Tendsto (fun k => (flagDensity₁ F.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 0) := by
      simp only [hzero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hF_tendsto h0
  · -- Value at the edge flag: `(toPosHom ψ) e = a edgeFF = c`.
    have hval : (PositiveHomSpace.toPosHom ψ) e = a edgeFF := by
      show (PositiveHomSpace.toPosHom ψ) ⟦basisVector edgeFF⟧ = a edgeFF
      rw [PositiveHomSpace.toPosHom_basisVector, hψ, posHomPoint_val_apply,
        ← PositiveHom.coe_flag, hφ]
    rw [hval]
    -- Both the subsequence density and `a edgeFF` are limits of the same sequence.
    have h_edge_sub : Tendsto (fun k => (flagDensity₁ edgeFF.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 (a edgeFF)) := hpt edgeFF
    have h_edge_c : Tendsto (fun k => (flagDensity₁ edgeFF.2 (s (ϕ k)).2 : ℝ))
        atTop (𝓝 c) := hlim.comp hmono.tendsto_atTop
    exact tendsto_nhds_unique h_edge_sub h_edge_c

/-! ## The star and the co-star -/

/-- The star `K_{1,n}` rooted at its centre, as a `vtype`-flag on `Fin (n+1)`: vertex `0` is the
root/centre (adjacent to every other vertex), vertices `1,…,n` are leaves (pairwise non-adjacent). -/
def starLabeled (n : ℕ) : LabeledGraph vtype (Fin (n + 1)) where
  graph :=
    { Adj := fun i j => (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0)
      symm := fun i j h => by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
        · exact Or.inl ⟨h2, h1⟩
      loopless := fun i h => by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2 h1
        · exact h1 h2 }
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [vtype, bot_adj]
        constructor
        · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact (h rfl).elim
        · intro h; exact h.elim }

/-- The co-star `K_{n} ⊎ K_1` rooted at the isolated vertex, as a `vtype`-flag on `Fin (n+1)`:
vertex `0` is the root (adjacent to nothing), vertices `1,…,n` form a clique. -/
def coStarLabeled (n : ℕ) : LabeledGraph vtype (Fin (n + 1)) where
  graph :=
    { Adj := fun i j => i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j
      symm := by rintro i j ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun h => h3 h.symm⟩
      loopless := by rintro i ⟨_, _, h⟩; exact h rfl }
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [vtype, bot_adj]
        constructor
        · rintro ⟨h, _, _⟩; exact (h rfl).elim
        · intro h; exact h.elim }

/-! ### Counting the one-root edge density of a centre-rooted graph -/

open LabeledSubgraph in
/-- **Forward iso.**  For a `vtype`-graph `G` on `Fin (n+1)` rooted at `0`, if `0` is adjacent to a
leaf `v ≠ 0`, then the labelled subgraph induced on `{0, v}` is flag-isomorphic to the edge. -/
private theorem edgeIso_fwd (n : ℕ) (G : LabeledGraph vtype (Fin (n + 1)))
    (htype : ∀ t, G.type_embed t = (0 : Fin (n + 1)))
    (v : Fin (n + 1)) (hv : v ≠ 0) (hadj : G.graph.Adj 0 v)
    (h : G.type_verts ⊆ (↑({0, v} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) :
    Nonempty ((inducedLabeledSubgraph G (↑({0, v} : Finset (Fin (n + 1)))) h).coe ≃f edgeLabeled) := by
  set S : Set (Fin (n + 1)) := (↑({0, v} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) with hS
  have h0S : (0 : Fin (n + 1)) ∈ S := by rw [hS]; simp
  have hvS : v ∈ S := by rw [hS]; simp
  set IG := inducedLabeledSubgraph G S h with hIG
  have hverts : IG.subgraph.verts = S := inducedLabeledSubgraph_verts G S h
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ S := fun a => hverts ▸ a.property
  have key : ∀ (a b : ↥IG.subgraph.verts), IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce S).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  let f : Fin 2 → ↥IG.subgraph.verts := fun i =>
    if i = 0 then ⟨0, hverts ▸ h0S⟩ else ⟨v, hverts ▸ hvS⟩
  have hf0 : (f 0).val = (0 : Fin (n + 1)) := by simp [f]
  have hf1 : (f 1).val = v := by simp [f]
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | (exfalso; apply hv;
           have hc := congrArg Subtype.val hab
           simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, hf0, hf1] at hc
           first | exact hc.symm | exact hc)
  have hScard : S.ncard = 2 := by rw [hS, Set.ncard_coe_finset, Finset.card_pair hv.symm]
  have hcard : Fintype.card ↥IG.subgraph.verts = Fintype.card (Fin 2) := by
    rw [Fintype.card_congr (Equiv.setCongr hverts), Fintype.card_fin,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hScard]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard.symm⟩
  let ef : Fin 2 ≃ ↥IG.subgraph.verts := Equiv.ofBijective f hfbij
  refine ⟨LabeledGraphIso.symm ⟨{ toEquiv := ef, map_rel_iff' := ?_ }, ?_⟩⟩
  · intro a b
    show IG.coe.graph.Adj (ef a) (ef b) ↔ edgeLabeled.graph.Adj a b
    rw [key (ef a) (ef b)]
    show G.graph.Adj (f a).val (f b).val ↔ edgeGraph.Adj a b
    simp only [edgeGraph, top_adj, ne_eq]
    fin_cases a <;> fin_cases b <;> simp_all [hadj.symm]
  · funext t
    show ef (edgeLabeled.type_embed t) = IG.coe.type_embed t
    have he : edgeLabeled.type_embed t = (0 : Fin 2) := rfl
    rw [he]
    apply Subtype.ext
    show (f 0).val = (IG.type_embed t).val
    rw [hf0, IG.embed_eq t, htype t]

open LabeledSubgraph in
/-- **Backward iso.**  Conversely, if the labelled subgraph induced on a subset `Sf` is
flag-isomorphic to the edge, then `Sf = {0, v}` for a leaf `v ≠ 0` adjacent to the root `0`. -/
private theorem edgeIso_bwd (n : ℕ) (G : LabeledGraph vtype (Fin (n + 1)))
    (htype : ∀ t, G.type_embed t = (0 : Fin (n + 1)))
    (Sf : Finset (Fin (n + 1))) (h : G.type_verts ⊆ (↑Sf : Set (Fin (n + 1))))
    (hiso : Nonempty ((inducedLabeledSubgraph G (↑Sf) h).coe ≃f edgeLabeled)) :
    ∃ v, v ≠ 0 ∧ Sf = {0, v} ∧ G.graph.Adj 0 v := by
  obtain ⟨φ⟩ := hiso
  set S : Set (Fin (n + 1)) := (↑Sf : Set (Fin (n + 1))) with hS
  set IG := inducedLabeledSubgraph G S h with hIG
  have hverts : IG.subgraph.verts = S := inducedLabeledSubgraph_verts G S h
  have hcard2 : Fintype.card ↥IG.subgraph.verts = 2 := by
    rw [Fintype.card_congr φ.graph_iso.toEquiv]; simp
  have hSfcard : Sf.card = 2 := by
    rw [← hcard2, Fintype.card_congr (Equiv.setCongr hverts), ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, hS, Set.ncard_coe_finset]
  have h0Sf : (0 : Fin (n + 1)) ∈ Sf := by
    have h0tv : (0 : Fin (n + 1)) ∈ G.type_verts := by
      rw [LabeledGraph.mem_type_verts]; exact ⟨0, htype 0⟩
    have := h h0tv; rwa [hS, Finset.mem_coe] at this
  obtain ⟨v, hv0, hSfeq⟩ : ∃ v, v ≠ 0 ∧ Sf = {0, v} := by
    have h1 : (Sf.erase 0).card = 1 := by rw [Finset.card_erase_of_mem h0Sf, hSfcard]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    refine ⟨v, ?_, ?_⟩
    · intro hv0; subst hv0; have := Finset.notMem_erase 0 Sf; rw [hv] at this; simp at this
    · rw [← Finset.insert_erase h0Sf, hv]
  refine ⟨v, hv0, hSfeq, ?_⟩
  have h0S : (0 : Fin (n + 1)) ∈ S := by rw [hS, hSfeq]; simp
  have hvS : v ∈ S := by rw [hS, hSfeq]; simp
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ S := fun a => hverts ▸ a.property
  have key : ∀ (a b : ↥IG.subgraph.verts), IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce S).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  let a0 : ↥IG.subgraph.verts := ⟨0, hverts ▸ h0S⟩
  let av : ↥IG.subgraph.verts := ⟨v, hverts ▸ hvS⟩
  have hne : a0 ≠ av := by
    intro hh; apply hv0; have := congrArg Subtype.val hh; simpa [a0, av] using this.symm
  have hadj_img : edgeLabeled.graph.Adj (φ.graph_iso a0) (φ.graph_iso av) := by
    show edgeGraph.Adj (φ.graph_iso a0) (φ.graph_iso av)
    simp only [edgeGraph, top_adj, ne_eq]
    intro hh; exact hne (φ.graph_iso.injective hh)
  have hadj_pre : IG.coe.graph.Adj a0 av := φ.graph_iso.map_rel_iff.mp hadj_img
  have hfin := (key a0 av).mp hadj_pre
  simpa [a0, av] using hfin

open LabeledSubgraph in
/-- The one-root edge density of a centre-rooted `vtype`-graph on `Fin (n+1)` equals the degree of
the root divided by `n` (the number of one-vertex extensions). -/
private theorem centreRooted_edge_density (n : ℕ) (G : LabeledGraph vtype (Fin (n + 1)))
    (htype : ∀ t, G.type_embed t = (0 : Fin (n + 1))) :
    flagDensity₁ edgeFF.2 (⟦G⟧ : Flag vtype (Fin (n + 1)))
      = ((G.graph.neighborFinset 0).card : ℚ) / n := by
  have hden : flagDensity₁ (⟦edgeLabeled⟧ : Flag vtype (Fin 2)) (⟦G⟧ : Flag vtype (Fin (n + 1)))
      = ((Finset.univ.filter (fun S : Finset (Fin (n + 1)) =>
          ∃ (h : G.type_verts ⊆ (↑S : Set (Fin (n + 1)))),
            Nonempty ((inducedLabeledSubgraph G (↑S) h).coe ≃f edgeLabeled))).card : ℚ)
        / ((G.size - vtype.size).choose (edgeLabeled.size - vtype.size)) :=
    flagDensity₁_eq_subset_count_div edgeLabeled G
  -- The numerator is the degree of the root.
  have hcount : (Finset.univ.filter (fun S : Finset (Fin (n + 1)) =>
        ∃ (h : G.type_verts ⊆ (↑S : Set (Fin (n + 1)))),
          Nonempty ((inducedLabeledSubgraph G (↑S) h).coe ≃f edgeLabeled))).card
      = (G.graph.neighborFinset 0).card := by
    have htv : G.type_verts = ({(0 : Fin (n + 1))} : Set (Fin (n + 1))) := by
      ext x; rw [LabeledGraph.mem_type_verts]
      exact ⟨fun ⟨t, ht⟩ => by rw [← ht, htype t]; rfl,
             fun hx => ⟨0, by rw [htype 0, Set.mem_singleton_iff.mp hx]⟩⟩
    have hsub : ∀ (v : Fin (n + 1)),
        G.type_verts ⊆ (↑({0, v} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
      intro v; rw [htv]; intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp
    have hset : (Finset.univ.filter (fun S : Finset (Fin (n + 1)) =>
          ∃ (h : G.type_verts ⊆ (↑S : Set (Fin (n + 1)))),
            Nonempty ((inducedLabeledSubgraph G (↑S) h).coe ≃f edgeLabeled)))
        = (G.graph.neighborFinset 0).image (fun v => ({0, v} : Finset (Fin (n + 1)))) := by
      ext Sf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨h, hiso⟩
        obtain ⟨v, hv0, hSfeq, hadj⟩ := edgeIso_bwd n G htype Sf h hiso
        exact ⟨v, hadj, hSfeq.symm⟩
      · rintro ⟨v, hadj, rfl⟩
        have hv0 : v ≠ 0 := fun hh => by rw [hh] at hadj; exact (G.graph.loopless 0) hadj
        exact ⟨hsub v, edgeIso_fwd n G htype v hv0 hadj (hsub v)⟩
    rw [hset, Finset.card_image_of_injOn]
    intro a ha b hb hab
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at ha hb
    have ha0 : a ≠ 0 := fun hh => by rw [hh] at ha; exact G.graph.loopless 0 ha
    have hab' : ({0, a} : Finset (Fin (n + 1))) = {0, b} := hab
    have hmem : a ∈ ({0, b} : Finset (Fin (n + 1))) :=
      hab' ▸ (by simp : a ∈ ({0, a} : Finset (Fin (n + 1))))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hh | hh
    · exact absurd hh ha0
    · exact hh
  -- The denominator is `n`.
  have hdenom : ((G.size - vtype.size).choose (edgeLabeled.size - vtype.size) : ℚ) = (n : ℚ) := by
    have : (G.size - vtype.size).choose (edgeLabeled.size - vtype.size) = n := by
      simp only [LabeledGraph.size, FlagType.size, Fintype.card_fin, Nat.add_sub_cancel]
      norm_num
    rw [this]
  show flagDensity₁ (⟦edgeLabeled⟧ : Flag vtype (Fin 2)) (⟦G⟧ : Flag vtype (Fin (n + 1))) = _
  rw [hden, hcount, hdenom]

/-- In a star of `n ≥ 1` leaves the one-root edge density is `1`: every leaf is adjacent to the
root, so all `n` one-vertex extensions induce the edge flag. -/
theorem star_edge_density (n : ℕ) (hn : 1 ≤ n) :
    flagDensity₁ edgeFF.2 (⟦starLabeled n⟧ : Flag vtype (Fin (n + 1))) = 1 := by
  rw [centreRooted_edge_density n (starLabeled n) (fun _ => rfl)]
  -- The root of the star is adjacent to all `n` leaves.
  have hdeg : ((starLabeled n).graph.neighborFinset 0).card = n := by
    have hnb : (starLabeled n).graph.neighborFinset 0
        = (Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0)) := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      show ((0 : Fin (n + 1)) = 0 ∧ v ≠ 0) ∨ ((0 : Fin (n + 1)) ≠ 0 ∧ v = 0) ↔ v ≠ 0
      constructor
      · rintro (⟨_, hv⟩ | ⟨hf, _⟩); exacts [hv, absurd rfl hf]
      · intro hv; exact Or.inl ⟨rfl, hv⟩
    rw [hnb, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  rw [hdeg]
  field_simp

/-- In a co-star the one-root edge density is `0`: the root is adjacent to nothing. -/
theorem coStar_edge_density (n : ℕ) :
    flagDensity₁ edgeFF.2 (⟦coStarLabeled n⟧ : Flag vtype (Fin (n + 1))) = 0 := by
  rw [centreRooted_edge_density n (coStarLabeled n) (fun _ => rfl)]
  -- The root of the co-star is adjacent to nothing.
  have hdeg : ((coStarLabeled n).graph.neighborFinset 0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    exact hv.1 rfl
  rw [hdeg]
  simp

/-! ## The concrete obstruction theorems -/

/-- A bundled index together with a lower bound and a class-membership witness, used to recursively
build a strictly-increasing index sequence of in-class members. -/
private noncomputable def idxStep (P : ℕ → Prop) (prev : ℕ) (h : ∀ N : ℕ, ∃ n, N ≤ n ∧ P n) :
    { n : ℕ // prev < n ∧ P n } :=
  ⟨(h (prev + 1)).choose, by
    have hspec := (h (prev + 1)).choose_spec
    exact ⟨hspec.1, hspec.2⟩⟩

/-- A strictly-increasing index sequence whose every member satisfies `P` and is `≥ 1`, built from a
"`P` holds arbitrarily far out" hypothesis. -/
private noncomputable def idxSeq (P : ℕ → Prop) (h : ∀ N : ℕ, ∃ n, N ≤ n ∧ P n) :
    ℕ → { n : ℕ // 1 ≤ n ∧ P n }
  | 0 => ⟨(h 1).choose, by
      have hspec := (h 1).choose_spec
      exact ⟨hspec.1, hspec.2⟩⟩
  | (k + 1) =>
    let prev := idxSeq P h k
    ⟨(idxStep P prev.1 h).1, by
      have hstep := (idxStep P prev.1 h).2
      exact ⟨le_of_lt (lt_of_le_of_lt prev.2.1 hstep.1), hstep.2⟩⟩

private theorem idxSeq_strictMono (P : ℕ → Prop) (h : ∀ N : ℕ, ∃ n, N ≤ n ∧ P n) :
    StrictMono (fun k => (idxSeq P h k).1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  show (idxSeq P h k).1 < (idxSeq P h (k + 1)).1
  exact (idxStep P (idxSeq P h k).1 h).2.1

/-- **`thm:degenerate-obstruction`.**  An edge-degenerate hereditary class that contains
arbitrarily large stars (rooted at the centre) is not root-plantable at the one-vertex type. -/
theorem degenerate_not_rootPlantable (hc : HeredClass) (hdeg : EdgeDegenerate hc)
    (hstars : ∀ N : ℕ, ∃ n, N ≤ n ∧ hc.Mem (starLabeled n).graph) :
    ¬ RootPlantable (hc.constraintOf vtype) := by
  classical
  -- An increasing star sequence whose every member is in the class.
  set P : ℕ → Prop := fun n => hc.Mem (starLabeled n).graph with hP
  set nseq : ℕ → ℕ := fun k => (idxSeq P hstars k).1 with hnseq
  have hnseq_mono : StrictMono nseq := idxSeq_strictMono P hstars
  have hnseq_ge : ∀ k, 1 ≤ nseq k := fun k => (idxSeq P hstars k).2.1
  have hnseq_mem : ∀ k, hc.Mem (starLabeled (nseq k)).graph := fun k => (idxSeq P hstars k).2.2
  -- The flag sequence of stars.
  set s : FlagSeq vtype := fun k => ⟨nseq k + 1, ⟦starLabeled (nseq k)⟧⟩ with hs
  have hinc : Increases s := by
    apply increases_of_consecutive_lt
    intro k
    show nseq k + 1 < nseq (k + 1) + 1
    exact Nat.add_lt_add_right (hnseq_mono (Nat.lt_succ_self k)) 1
  have hmem : ∀ k, hc.underlyingMem (unlabel (s k).2) := by
    intro k
    show hc.underlyingMem (unlabel (⟦starLabeled (nseq k)⟧ : Flag vtype (Fin (nseq k + 1))))
    rw [hc.underlyingMem_unlabel_mk]
    exact hnseq_mem k
  -- Edge density is constantly `1`.
  have hlim : Tendsto (fun k => (flagDensity₁ edgeFF.2 (s k).2 : ℝ)) atTop (𝓝 1) := by
    have hconst : ∀ k, (flagDensity₁ edgeFF.2 (s k).2 : ℝ) = 1 := by
      intro k
      show (flagDensity₁ edgeFF.2 (⟦starLabeled (nseq k)⟧ : Flag vtype (Fin (nseq k + 1))) : ℝ) = 1
      rw [star_edge_density (nseq k) (hnseq_ge k)]; norm_num
    simp only [hconst]; exact tendsto_const_nhds
  -- Assemble the `Q_vtype` witness with `e`-value `1 ≠ 0`.
  obtain ⟨ψ, hψQ, hψe⟩ := exists_Qσ_point_edge_eq hc s hinc hmem 1 hlim
  exact edgeDegenerate_not_rootPlantable_of_witness hc hdeg
    ⟨ψ, hψQ, by rw [hψe]; norm_num⟩

/-- **`cor:codegenerate` (concrete form).**  A co-edge-degenerate hereditary class that contains
arbitrarily large co-stars (rooted at the isolated vertex) is not root-plantable at the one-vertex
type. -/
theorem coDegenerate_not_rootPlantable (hc : HeredClass) (hdeg : CoEdgeDegenerate hc)
    (hcostars : ∀ N : ℕ, ∃ n, N ≤ n ∧ hc.Mem (coStarLabeled n).graph) :
    ¬ RootPlantable (hc.constraintOf vtype) := by
  classical
  -- An increasing co-star sequence whose every member is in the class.
  set P : ℕ → Prop := fun n => hc.Mem (coStarLabeled n).graph with hP
  set nseq : ℕ → ℕ := fun k => (idxSeq P hcostars k).1 with hnseq
  have hnseq_mono : StrictMono nseq := idxSeq_strictMono P hcostars
  have hnseq_mem : ∀ k, hc.Mem (coStarLabeled (nseq k)).graph := fun k => (idxSeq P hcostars k).2.2
  -- The flag sequence of co-stars.
  set s : FlagSeq vtype := fun k => ⟨nseq k + 1, ⟦coStarLabeled (nseq k)⟧⟩ with hs
  have hinc : Increases s := by
    apply increases_of_consecutive_lt
    intro k
    show nseq k + 1 < nseq (k + 1) + 1
    exact Nat.add_lt_add_right (hnseq_mono (Nat.lt_succ_self k)) 1
  have hmem : ∀ k, hc.underlyingMem (unlabel (s k).2) := by
    intro k
    show hc.underlyingMem (unlabel (⟦coStarLabeled (nseq k)⟧ : Flag vtype (Fin (nseq k + 1))))
    rw [hc.underlyingMem_unlabel_mk]
    exact hnseq_mem k
  -- Edge density is constantly `0`.
  have hlim : Tendsto (fun k => (flagDensity₁ edgeFF.2 (s k).2 : ℝ)) atTop (𝓝 0) := by
    have hconst : ∀ k, (flagDensity₁ edgeFF.2 (s k).2 : ℝ) = 0 := by
      intro k
      show (flagDensity₁ edgeFF.2 (⟦coStarLabeled (nseq k)⟧ : Flag vtype (Fin (nseq k + 1))) : ℝ) = 0
      rw [coStar_edge_density (nseq k)]; norm_num
    simp only [hconst]; exact tendsto_const_nhds
  -- Assemble the `Q_vtype` witness with `e`-value `0 ≠ 1`.
  obtain ⟨ψ, hψQ, hψe⟩ := exists_Qσ_point_edge_eq hc s hinc hmem 0 hlim
  exact coEdgeDegenerate_not_rootPlantable_of_witness hc hdeg
    ⟨ψ, hψQ, by rw [hψe]; norm_num⟩

end FlagAlgebras.MetaTheory
