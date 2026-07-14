import LeanFlagAlgebras.MetaTheory.TuranDirac
import LeanFlagAlgebras.MetaTheory.MantelNotPlantable
import LeanFlagAlgebras.MetaTheory.SliceRecovery
import LeanFlagAlgebras.MetaTheory.LabeledCount

/-! # The Turán slice support identities (paper §11.5, `thm:turan-slice` /
`thm:relative-mantel`, identity halves; §11.7 `cor:parametric-p4-turan-recovery`,
"consequently" clauses)

The relative supports of the balanced complete `r`-partite limit are SINGLE POINTS with
explicit rooted densities: all `σ`-rootings of a Turán graph are one flag (`TuranAut`),
so the extension measures are Dirac (`TuranDirac`), and the pinned values are single-root
extension counts in `turanGraph (r·m) r` —

* one-vertex type: `e = (r-1)/r`;
* ordered edge type `τ` (`FlagType_2_1`): `a_τ = b_τ = 1/r`, `g_τ = (r-2)/r`, `z_τ = 0`;
* ordered non-edge type `η` (`FlagType_2_0`): `z_η = 1/r`, `g_η = (r-1)/r`, `a_η = b_η = 0`.

The singleton claim `Y_Tur = {φ_Tr}` is Erdős–Simonovits stability (classical input,
outside this development); it enters as the explicit hypothesis
`hES : turanSlice r ⊆ {posHomPoint (turanLimit r hr)}`, under which the identities hold on
`S_σ(Y_Tur)` — the full identity halves of `thm:turan-slice`.  At `r = 2` this discharges
`MantelNotPlantable`'s pinning hypothesis, and composed with `parametric_recovery` it
yields the "consequently" clauses of `cor:parametric-p4-turan-recovery`.

All counts use the tail-shifted subsequence (indices `≥ 1`) so every residue class has at
least two vertices (the non-edge type needs it).
-/

open MeasureTheory Filter SimpleGraph CompleteGraphFreeP4
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## Generic rooted-count infrastructure -/

/-- Among three pairwise distinct elements of `Fin 3`, anything distinct from the first
two is the third. -/
private lemma third_unique {e₀ e₁ t₂ : Fin 3} (h01 : e₀ ≠ e₁) (h02 : e₀ ≠ t₂)
    (h12 : e₁ ≠ t₂) : ∀ i : Fin 3, i ≠ e₀ → i ≠ e₁ → i = t₂ := by
  intro i h0 h1
  have hv01 : e₀.val ≠ e₁.val := fun h => h01 (Fin.ext h)
  have hv02 : e₀.val ≠ t₂.val := fun h => h02 (Fin.ext h)
  have hv12 : e₁.val ≠ t₂.val := fun h => h12 (Fin.ext h)
  have hv0 : i.val ≠ e₀.val := fun h => h0 (Fin.ext h)
  have hv1 : i.val ≠ e₁.val := fun h => h1 (Fin.ext h)
  have he0 := e₀.isLt
  have he1 := e₁.isLt
  have ht2 := t₂.isLt
  have hi := i.isLt
  apply Fin.ext
  omega

/-- Instance-free counting bridge: the `ncard` of a set-builder set is the card of the
corresponding filter. -/
private lemma ncard_setOf_eq_filter_card {N : ℕ} (p : Fin N → Prop) [DecidablePred p] :
    Set.ncard {w : Fin N | p w} = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

section TwoRootCounting

variable {σ2 : FlagType (Fin 2)}

private lemma type_embed_ne {N : ℕ} (G : LabeledGraph σ2 (Fin N)) :
    G.type_embed 0 ≠ G.type_embed 1 := by
  intro h
  have h2 := G.type_embed.injective h
  exact absurd h2 (by decide)

private lemma twoRoot_type_verts {N : ℕ} (G : LabeledGraph σ2 (Fin N)) :
    G.type_verts = {G.type_embed 0, G.type_embed 1} := by
  ext x
  rw [LabeledGraph.mem_type_verts]
  constructor
  · rintro ⟨t, rfl⟩
    fin_cases t
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  · rintro (rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

open LabeledSubgraph in
/-- Forward iso: a third vertex `w` with the prescribed adjacency pattern against the two
roots induces (together with the roots) a labelled copy of the three-vertex pattern `H`. -/
private lemma twoRootIso_fwd {N : ℕ} (G : LabeledGraph σ2 (Fin N))
    (H : LabeledGraph σ2 (Fin 3)) (t₂ : Fin 3)
    (ht0 : H.type_embed 0 ≠ t₂) (ht1 : H.type_embed 1 ≠ t₂)
    (w : Fin N) (hw0 : w ≠ G.type_embed 0) (hw1 : w ≠ G.type_embed 1)
    (hadj0 : G.graph.Adj (G.type_embed 0) w ↔ H.graph.Adj (H.type_embed 0) t₂)
    (hadj1 : G.graph.Adj (G.type_embed 1) w ↔ H.graph.Adj (H.type_embed 1) t₂)
    (h : G.type_verts ⊆
      (↑({G.type_embed 0, G.type_embed 1, w} : Finset (Fin N)) : Set (Fin N))) :
    Nonempty ((inducedLabeledSubgraph G
      (↑({G.type_embed 0, G.type_embed 1, w} : Finset (Fin N))) h).coe ≃f H) := by
  classical
  have hu01 : G.type_embed 0 ≠ G.type_embed 1 := type_embed_ne G
  have he01 : H.type_embed 0 ≠ H.type_embed 1 := type_embed_ne H
  set u₀ := G.type_embed 0 with hu₀
  set u₁ := G.type_embed 1 with hu₁
  set S : Set (Fin N) := (↑({u₀, u₁, w} : Finset (Fin N)) : Set (Fin N)) with hS
  have h0S : u₀ ∈ S := by rw [hS]; simp
  have h1S : u₁ ∈ S := by rw [hS]; simp
  have hwS : w ∈ S := by rw [hS]; simp
  set IG := inducedLabeledSubgraph G S h with hIG
  have hverts : IG.subgraph.verts = S := inducedLabeledSubgraph_verts G S h
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ S := fun a => hverts ▸ a.property
  have key : ∀ (a b : ↥IG.subgraph.verts),
      IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce S).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  have hcases : ∀ i : Fin 3, i = H.type_embed 0 ∨ i = H.type_embed 1 ∨ i = t₂ := by
    intro i
    by_cases h0 : i = H.type_embed 0
    · exact Or.inl h0
    by_cases h1 : i = H.type_embed 1
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr (third_unique he01 ht0 ht1 i h0 h1))
  set f : Fin 3 → ↥IG.subgraph.verts := fun i =>
    if i = H.type_embed 0 then ⟨u₀, hverts ▸ h0S⟩
    else if i = H.type_embed 1 then ⟨u₁, hverts ▸ h1S⟩
    else ⟨w, hverts ▸ hwS⟩ with hf
  have hf0 : (f (H.type_embed 0)).val = u₀ := by
    simp only [hf, if_true]
  have hf1 : (f (H.type_embed 1)).val = u₁ := by
    simp only [hf, if_true]
    rw [if_neg (fun hh : H.type_embed 1 = H.type_embed 0 => he01 hh.symm)]
  have hft : (f t₂).val = w := by
    simp only [hf]
    rw [if_neg (fun hh : t₂ = H.type_embed 0 => ht0 hh.symm),
      if_neg (fun hh : t₂ = H.type_embed 1 => ht1 hh.symm)]
  have hfinj : Function.Injective f := by
    intro i j hij
    have hval : (f i).val = (f j).val := congrArg Subtype.val hij
    rcases hcases i with hi | hi | hi <;> rcases hcases j with hj | hj | hj <;>
      rw [hi, hj] at hval ⊢
    · rw [hf0, hf1] at hval; exact absurd hval hu01
    · rw [hf0, hft] at hval; exact absurd hval (fun hh => hw0 hh.symm)
    · rw [hf1, hf0] at hval; exact absurd hval (fun hh => hu01 hh.symm)
    · rw [hf1, hft] at hval; exact absurd hval (fun hh => hw1 hh.symm)
    · rw [hft, hf0] at hval; exact absurd hval hw0
    · rw [hft, hf1] at hval; exact absurd hval hw1
  have hScard : S.ncard = 3 := by
    rw [hS, Set.ncard_coe_finset]
    have h1 : u₁ ∉ ({w} : Finset (Fin N)) := by
      simp only [Finset.mem_singleton]
      exact fun hh => hw1 hh.symm
    have h0 : u₀ ∉ ({u₁, w} : Finset (Fin N)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hu01, fun hh => hw0 hh.symm⟩
    rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h1,
      Finset.card_singleton]
  have hcard : Fintype.card ↥IG.subgraph.verts = Fintype.card (Fin 3) := by
    rw [Fintype.card_congr (Equiv.setCongr hverts), Fintype.card_fin,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hScard]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard.symm⟩
  set ef : Fin 3 ≃ ↥IG.subgraph.verts := Equiv.ofBijective f hfbij with hef
  refine ⟨LabeledGraphIso.symm ⟨{ toEquiv := ef, map_rel_iff' := ?_ }, ?_⟩⟩
  · intro a b
    show IG.coe.graph.Adj (ef a) (ef b) ↔ H.graph.Adj a b
    rw [key (ef a) (ef b)]
    show G.graph.Adj (f a).val (f b).val ↔ H.graph.Adj a b
    rcases hcases a with ha | ha | ha <;> rcases hcases b with hb | hb | hb <;> rw [ha, hb]
    · rw [hf0]; exact iff_of_false (G.graph.loopless u₀) (H.graph.loopless _)
    · rw [hf0, hf1]
      exact (type_embed_Adj_iff G 0 1).symm.trans (type_embed_Adj_iff H 0 1)
    · rw [hf0, hft]; exact hadj0
    · rw [hf1, hf0, G.graph.adj_comm, H.graph.adj_comm]
      exact (type_embed_Adj_iff G 0 1).symm.trans (type_embed_Adj_iff H 0 1)
    · rw [hf1]; exact iff_of_false (G.graph.loopless u₁) (H.graph.loopless _)
    · rw [hf1, hft]; exact hadj1
    · rw [hft, hf0, G.graph.adj_comm, H.graph.adj_comm]; exact hadj0
    · rw [hft, hf1, G.graph.adj_comm, H.graph.adj_comm]; exact hadj1
    · rw [hft]; exact iff_of_false (G.graph.loopless w) (H.graph.loopless _)
  · funext t
    show ef (H.type_embed t) = IG.coe.type_embed t
    apply Subtype.ext
    show (f (H.type_embed t)).val = (IG.type_embed t).val
    fin_cases t
    · show (f (H.type_embed 0)).val = (IG.type_embed 0).val
      rw [hf0]
      exact hu₀.trans (IG.embed_eq 0).symm
    · show (f (H.type_embed 1)).val = (IG.type_embed 1).val
      rw [hf1]
      exact hu₁.trans (IG.embed_eq 1).symm

open LabeledSubgraph in
/-- Backward analysis: an inducing subset for the three-vertex pattern `H` is the two
roots plus a third vertex with the prescribed adjacency pattern. -/
private lemma twoRootIso_bwd {N : ℕ} (G : LabeledGraph σ2 (Fin N))
    (H : LabeledGraph σ2 (Fin 3)) (t₂ : Fin 3)
    (ht0 : H.type_embed 0 ≠ t₂) (ht1 : H.type_embed 1 ≠ t₂)
    (S : Finset (Fin N)) (h : G.type_verts ⊆ (↑S : Set (Fin N)))
    (hiso : Nonempty ((inducedLabeledSubgraph G (↑S) h).coe ≃f H)) :
    ∃ w, w ≠ G.type_embed 0 ∧ w ≠ G.type_embed 1 ∧
      S = {G.type_embed 0, G.type_embed 1, w} ∧
      (G.graph.Adj (G.type_embed 0) w ↔ H.graph.Adj (H.type_embed 0) t₂) ∧
      (G.graph.Adj (G.type_embed 1) w ↔ H.graph.Adj (H.type_embed 1) t₂) := by
  classical
  obtain ⟨φ⟩ := hiso
  have hu01 : G.type_embed 0 ≠ G.type_embed 1 := type_embed_ne G
  have he01 : H.type_embed 0 ≠ H.type_embed 1 := type_embed_ne H
  set u₀ := G.type_embed 0 with hu₀
  set u₁ := G.type_embed 1 with hu₁
  set Sset : Set (Fin N) := (↑S : Set (Fin N)) with hSset
  set IG := inducedLabeledSubgraph G Sset h with hIG
  have hverts : IG.subgraph.verts = Sset := inducedLabeledSubgraph_verts G Sset h
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ Sset := fun a => hverts ▸ a.property
  have key : ∀ (a b : ↥IG.subgraph.verts),
      IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce Sset).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  have h0S : u₀ ∈ S := by
    rw [← Finset.mem_coe]
    exact h (LabeledGraph.mem_type_verts.mpr ⟨0, rfl⟩)
  have h1S : u₁ ∈ S := by
    rw [← Finset.mem_coe]
    exact h (LabeledGraph.mem_type_verts.mpr ⟨1, rfl⟩)
  have hcard3 : Fintype.card ↥IG.subgraph.verts = 3 := by
    rw [Fintype.card_congr φ.graph_iso.toEquiv]
    simp
  have hScard : S.card = 3 := by
    rw [← hcard3, Fintype.card_congr (Equiv.setCongr hverts), ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hSset, Set.ncard_coe_finset]
  have h1mem : u₁ ∈ S.erase u₀ := Finset.mem_erase.mpr ⟨fun hh => hu01 hh.symm, h1S⟩
  obtain ⟨w, hwmem⟩ : ∃ w, (S.erase u₀).erase u₁ = {w} :=
    Finset.card_eq_one.mp (by
      rw [Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem h0S, hScard])
  have hw_in : w ∈ (S.erase u₀).erase u₁ := hwmem ▸ Finset.mem_singleton_self w
  have hwS : w ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw_in)
  have hw1 : w ≠ u₁ := (Finset.mem_erase.mp hw_in).1
  have hw0 : w ≠ u₀ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw_in)).1
  have hSeq : S = {u₀, u₁, w} := by
    have h1 : S.erase u₀ = insert u₁ {w} := by
      rw [← hwmem]
      exact (Finset.insert_erase h1mem).symm
    rw [← Finset.insert_erase h0S, h1]
  have h0S' : u₀ ∈ Sset := Finset.mem_coe.mpr h0S
  have h1S' : u₁ ∈ Sset := Finset.mem_coe.mpr h1S
  have hwS' : w ∈ Sset := Finset.mem_coe.mpr hwS
  set a₀ : ↥IG.subgraph.verts := ⟨u₀, hverts ▸ h0S'⟩ with ha₀
  set a₁ : ↥IG.subgraph.verts := ⟨u₁, hverts ▸ h1S'⟩ with ha₁
  set aw : ↥IG.subgraph.verts := ⟨w, hverts ▸ hwS'⟩ with haw
  have hembed0 : IG.coe.type_embed 0 = a₀ :=
    Subtype.ext ((IG.embed_eq 0).trans hu₀.symm)
  have hembed1 : IG.coe.type_embed 1 = a₁ :=
    Subtype.ext ((IG.embed_eq 1).trans hu₁.symm)
  have himg0 : φ.graph_iso a₀ = H.type_embed 0 := by
    rw [← hembed0]
    exact congrFun φ.type_preserve 0
  have himg1 : φ.graph_iso a₁ = H.type_embed 1 := by
    rw [← hembed1]
    exact congrFun φ.type_preserve 1
  have hawne0 : aw ≠ a₀ := fun hh => hw0 (congrArg Subtype.val hh)
  have hawne1 : aw ≠ a₁ := fun hh => hw1 (congrArg Subtype.val hh)
  have himgw : φ.graph_iso aw = t₂ := by
    apply third_unique he01 ht0 ht1
    · intro hh
      apply hawne0
      apply φ.graph_iso.injective
      rw [hh, himg0]
    · intro hh
      apply hawne1
      apply φ.graph_iso.injective
      rw [hh, himg1]
  refine ⟨w, hw0, hw1, hSeq, ?_, ?_⟩
  · have hstep : G.graph.Adj u₀ w ↔ IG.coe.graph.Adj a₀ aw := (key a₀ aw).symm
    rw [hstep, ← φ.graph_iso.map_rel_iff, himg0, himgw]
  · have hstep : G.graph.Adj u₁ w ↔ IG.coe.graph.Adj a₁ aw := (key a₁ aw).symm
    rw [hstep, ← φ.graph_iso.map_rel_iff, himg1, himgw]

/-- **Two-root density as a single-vertex pattern count**: the density of a three-vertex
pattern `H` in a two-root host `G` counts the third vertices with the matching adjacency
pattern against the roots, over `N - 2`. -/
private lemma twoRoot_density {N : ℕ} (G : LabeledGraph σ2 (Fin N))
    (H : LabeledGraph σ2 (Fin 3)) (t₂ : Fin 3)
    (ht0 : H.type_embed 0 ≠ t₂) (ht1 : H.type_embed 1 ≠ t₂) :
    flagDensity₁ (⟦H⟧ : Flag σ2 (Fin 3)) (⟦G⟧ : Flag σ2 (Fin N))
      = ((Set.ncard {w : Fin N |
            w ≠ G.type_embed 0 ∧ w ≠ G.type_embed 1 ∧
            (G.graph.Adj (G.type_embed 0) w ↔ H.graph.Adj (H.type_embed 0) t₂) ∧
            (G.graph.Adj (G.type_embed 1) w ↔ H.graph.Adj (H.type_embed 1) t₂)}) : ℚ)
        / ((N - 2 : ℕ) : ℚ) := by
  classical
  rw [flagDensity₁_eq_subset_count_div H G]
  rw [ncard_setOf_eq_filter_card]
  have hdenom : (G.size - σ2.size).choose (H.size - σ2.size) = N - 2 := by
    simp only [LabeledGraph.size, FlagType.size, Fintype.card_fin]
    exact Nat.choose_one_right _
  rw [hdenom]
  congr 1
  norm_cast
  symm
  refine Finset.card_bij
    (i := fun w _ => ({G.type_embed 0, G.type_embed 1, w} : Finset (Fin N))) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter] at hw
    obtain ⟨-, hw0, hw1, hp0, hp1⟩ := hw
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsub : G.type_verts ⊆
        (↑({G.type_embed 0, G.type_embed 1, w} : Finset (Fin N)) : Set (Fin N)) := by
      rw [twoRoot_type_verts G]
      rintro x (rfl | rfl)
      · simp
      · simp
    exact ⟨hsub, twoRootIso_fwd G H t₂ ht0 ht1 w hw0 hw1 hp0 hp1 hsub⟩
  · intro w₁ h₁ w₂ h₂ heq
    simp only [Finset.mem_filter] at h₁
    have heq' : ({G.type_embed 0, G.type_embed 1, w₁} : Finset (Fin N))
        = {G.type_embed 0, G.type_embed 1, w₂} := heq
    have hmem : w₁ ∈ ({G.type_embed 0, G.type_embed 1, w₂} : Finset (Fin N)) := by
      rw [← heq']
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hh | hh | hh
    · exact absurd hh h₁.2.1
    · exact absurd hh h₁.2.2.1
    · exact hh
  · intro S hS
    simp only [Finset.mem_filter] at hS
    obtain ⟨-, h, hiso⟩ := hS
    obtain ⟨w, hw0, hw1, hSeq, hp0, hp1⟩ := twoRootIso_bwd G H t₂ ht0 ht1 S h hiso
    refine ⟨w, ?_, hSeq.symm⟩
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw0, hw1, hp0, hp1⟩

end TwoRootCounting

section OneRootCounting

private lemma oneRoot_type_verts {N : ℕ} (G : LabeledGraph vtype (Fin N)) (v₀ : Fin N)
    (htype : ∀ t, G.type_embed t = v₀) : G.type_verts = ({v₀} : Set (Fin N)) := by
  ext x
  rw [LabeledGraph.mem_type_verts]
  constructor
  · rintro ⟨t, rfl⟩
    rw [htype t]
    rfl
  · intro hx
    exact ⟨0, by rw [htype 0, Set.mem_singleton_iff.mp hx]⟩

open LabeledSubgraph in
private lemma oneRootEdgeIso_fwd {N : ℕ} (G : LabeledGraph vtype (Fin N)) (v₀ : Fin N)
    (htype : ∀ t, G.type_embed t = v₀)
    (v : Fin N) (hv : v ≠ v₀) (hadj : G.graph.Adj v₀ v)
    (h : G.type_verts ⊆ (↑({v₀, v} : Finset (Fin N)) : Set (Fin N))) :
    Nonempty ((inducedLabeledSubgraph G (↑({v₀, v} : Finset (Fin N))) h).coe
      ≃f edgeLabeled) := by
  classical
  set S : Set (Fin N) := (↑({v₀, v} : Finset (Fin N)) : Set (Fin N)) with hS
  have h0S : v₀ ∈ S := by rw [hS]; simp
  have hvS : v ∈ S := by rw [hS]; simp
  set IG := inducedLabeledSubgraph G S h with hIG
  have hverts : IG.subgraph.verts = S := inducedLabeledSubgraph_verts G S h
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ S := fun a => hverts ▸ a.property
  have key : ∀ (a b : ↥IG.subgraph.verts),
      IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce S).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  set f : Fin 2 → ↥IG.subgraph.verts := fun i =>
    if i = 0 then ⟨v₀, hverts ▸ h0S⟩ else ⟨v, hverts ▸ hvS⟩ with hf
  have hf0 : (f 0).val = v₀ := by simp [hf]
  have hf1 : (f 1).val = v := by simp [hf]
  have hfinj : Function.Injective f := by
    intro a b hab
    have hval : (f a).val = (f b).val := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b
    · rfl
    · have hval' : (f 0).val = (f 1).val := hval
      rw [hf0, hf1] at hval'
      exact absurd hval' (fun hh => hv hh.symm)
    · have hval' : (f 1).val = (f 0).val := hval
      rw [hf1, hf0] at hval'
      exact absurd hval' hv
    · rfl
  have hScard : S.ncard = 2 := by
    rw [hS, Set.ncard_coe_finset, Finset.card_pair (fun hh => hv hh.symm)]
  have hcard : Fintype.card ↥IG.subgraph.verts = Fintype.card (Fin 2) := by
    rw [Fintype.card_congr (Equiv.setCongr hverts), Fintype.card_fin,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hScard]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard.symm⟩
  set ef : Fin 2 ≃ ↥IG.subgraph.verts := Equiv.ofBijective f hfbij with hef
  refine ⟨LabeledGraphIso.symm ⟨{ toEquiv := ef, map_rel_iff' := ?_ }, ?_⟩⟩
  · intro a b
    show IG.coe.graph.Adj (ef a) (ef b) ↔ edgeLabeled.graph.Adj a b
    rw [key (ef a) (ef b)]
    fin_cases a <;> fin_cases b
    · show G.graph.Adj (f 0).val (f 0).val ↔ edgeGraph.Adj 0 0
      rw [hf0]
      exact iff_of_false (G.graph.loopless v₀) (edgeGraph.loopless 0)
    · show G.graph.Adj (f 0).val (f 1).val ↔ edgeGraph.Adj 0 1
      rw [hf0, hf1]
      exact iff_of_true hadj (by rw [SimpleGraph.top_adj]; decide)
    · show G.graph.Adj (f 1).val (f 0).val ↔ edgeGraph.Adj 1 0
      rw [hf1, hf0]
      exact iff_of_true hadj.symm (by rw [SimpleGraph.top_adj]; decide)
    · show G.graph.Adj (f 1).val (f 1).val ↔ edgeGraph.Adj 1 1
      rw [hf1]
      exact iff_of_false (G.graph.loopless v) (edgeGraph.loopless 1)
  · funext t
    show ef (edgeLabeled.type_embed t) = IG.coe.type_embed t
    have he : edgeLabeled.type_embed t = (0 : Fin 2) := rfl
    rw [he]
    apply Subtype.ext
    show (f 0).val = (IG.type_embed t).val
    rw [hf0, IG.embed_eq t, htype t]

open LabeledSubgraph in
private lemma oneRootEdgeIso_bwd {N : ℕ} (G : LabeledGraph vtype (Fin N)) (v₀ : Fin N)
    (htype : ∀ t, G.type_embed t = v₀)
    (S : Finset (Fin N)) (h : G.type_verts ⊆ (↑S : Set (Fin N)))
    (hiso : Nonempty ((inducedLabeledSubgraph G (↑S) h).coe ≃f edgeLabeled)) :
    ∃ v, v ≠ v₀ ∧ S = {v₀, v} ∧ G.graph.Adj v₀ v := by
  classical
  obtain ⟨φ⟩ := hiso
  set Sset : Set (Fin N) := (↑S : Set (Fin N)) with hSset
  set IG := inducedLabeledSubgraph G Sset h with hIG
  have hverts : IG.subgraph.verts = Sset := inducedLabeledSubgraph_verts G Sset h
  have memS : ∀ (a : ↥IG.subgraph.verts), a.val ∈ Sset := fun a => hverts ▸ a.property
  have key : ∀ (a b : ↥IG.subgraph.verts),
      IG.coe.graph.Adj a b ↔ G.graph.Adj a.val b.val := by
    intro a b
    rw [coe_adj_iff]
    show ((⊤ : G.graph.Subgraph).induce Sset).Adj a.val b.val ↔ G.graph.Adj a.val b.val
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨memS a, memS b, hh⟩⟩
  have h0S : v₀ ∈ S := by
    rw [← Finset.mem_coe]
    exact h (by
      rw [LabeledGraph.mem_type_verts]
      exact ⟨0, htype 0⟩)
  have hcard2 : Fintype.card ↥IG.subgraph.verts = 2 := by
    rw [Fintype.card_congr φ.graph_iso.toEquiv]
    simp
  have hScard : S.card = 2 := by
    rw [← hcard2, Fintype.card_congr (Equiv.setCongr hverts), ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hSset, Set.ncard_coe_finset]
  obtain ⟨v, hvmem⟩ : ∃ v, S.erase v₀ = {v} :=
    Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem h0S, hScard])
  have hv_in : v ∈ S.erase v₀ := hvmem ▸ Finset.mem_singleton_self v
  have hvS : v ∈ S := Finset.mem_of_mem_erase hv_in
  have hv0 : v ≠ v₀ := (Finset.mem_erase.mp hv_in).1
  have hSeq : S = {v₀, v} := by
    rw [← Finset.insert_erase h0S, hvmem]
  have h0S' : v₀ ∈ Sset := Finset.mem_coe.mpr h0S
  have hvS' : v ∈ Sset := Finset.mem_coe.mpr hvS
  set a₀ : ↥IG.subgraph.verts := ⟨v₀, hverts ▸ h0S'⟩ with ha₀
  set av : ↥IG.subgraph.verts := ⟨v, hverts ▸ hvS'⟩ with hav
  have hembed0 : IG.coe.type_embed 0 = a₀ :=
    Subtype.ext ((IG.embed_eq 0).trans (htype 0))
  have himg0 : φ.graph_iso a₀ = (0 : Fin 2) := by
    rw [← hembed0]
    exact congrFun φ.type_preserve 0
  have havne : av ≠ a₀ := fun hh => hv0 (congrArg Subtype.val hh)
  have himgv : φ.graph_iso av = (1 : Fin 2) := by
    by_contra hne
    have h1 : φ.graph_iso av = (0 : Fin 2) := by
      have hlt := (φ.graph_iso av).isLt
      have h0 : (φ.graph_iso av).val ≠ 1 := fun hh => hne (Fin.ext hh)
      apply Fin.ext
      show (φ.graph_iso av).val = 0
      omega
    apply havne
    apply φ.graph_iso.injective
    rw [h1, himg0]
  refine ⟨v, hv0, hSeq, ?_⟩
  have hstep : G.graph.Adj v₀ v ↔ IG.coe.graph.Adj a₀ av := (key a₀ av).symm
  rw [hstep, ← φ.graph_iso.map_rel_iff, himg0, himgv]
  show edgeGraph.Adj 0 1
  rw [SimpleGraph.top_adj]
  decide

/-- The one-root edge density of a `vtype`-graph rooted at `v₀` is the root's degree
(as an `ncard`) over `N - 1`. -/
private lemma oneRoot_edge_density {N : ℕ} (G : LabeledGraph vtype (Fin N)) (v₀ : Fin N)
    (htype : ∀ t, G.type_embed t = v₀) :
    flagDensity₁ edgeFF.2 (⟦G⟧ : Flag vtype (Fin N))
      = ((G.graph.neighborSet v₀).ncard : ℚ) / ((N - 1 : ℕ) : ℚ) := by
  classical
  show flagDensity₁ (⟦edgeLabeled⟧ : Flag vtype (Fin 2)) (⟦G⟧ : Flag vtype (Fin N)) = _
  rw [flagDensity₁_eq_subset_count_div edgeLabeled G]
  rw [show (G.graph.neighborSet v₀).ncard
      = (Finset.univ.filter (fun v : Fin N => G.graph.Adj v₀ v)).card from
    ncard_setOf_eq_filter_card _]
  have hdenom : (G.size - vtype.size).choose (edgeLabeled.size - vtype.size) = N - 1 := by
    simp only [LabeledGraph.size, FlagType.size, Fintype.card_fin]
    exact Nat.choose_one_right _
  rw [hdenom]
  congr 1
  norm_cast
  symm
  refine Finset.card_bij (i := fun v _ => ({v₀, v} : Finset (Fin N))) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hv0 : v ≠ v₀ := fun hh => by rw [hh] at hv; exact G.graph.loopless v₀ hv
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsub : G.type_verts ⊆ (↑({v₀, v} : Finset (Fin N)) : Set (Fin N)) := by
      rw [oneRoot_type_verts G v₀ htype]
      rintro x rfl
      simp
    exact ⟨hsub, oneRootEdgeIso_fwd G v₀ htype v hv0 hv hsub⟩
  · intro v₁ h₁ v₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁
    have hne1 : v₁ ≠ v₀ := fun hh => by rw [hh] at h₁; exact G.graph.loopless v₀ h₁
    have heq' : ({v₀, v₁} : Finset (Fin N)) = {v₀, v₂} := heq
    have hmem : v₁ ∈ ({v₀, v₂} : Finset (Fin N)) := by
      rw [← heq']
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hh | hh
    · exact absurd hh hne1
    · exact hh
  · intro S hS
    simp only [Finset.mem_filter] at hS
    obtain ⟨-, h, hiso⟩ := hS
    obtain ⟨v, hv0, hSeq, hadj⟩ := oneRootEdgeIso_bwd G v₀ htype S h hiso
    exact ⟨v, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hadj,
      hSeq.symm⟩

end OneRootCounting

/-! ## Residue-class counting in `Fin (r·m)` -/

section ResidueCounts

/-- Private copy of `TuranLimit`'s residue-class cardinality (private there): the class of
`i` has exactly `m` elements, via the bijection `j ↦ i + r·j`. -/
private lemma card_residue_class' (r m i : ℕ) (hi : i < r) :
    (Finset.univ.filter (fun v : Fin (r * m) => v.val % r = i)).card = m := by
  have hr : 0 < r := by omega
  have hb : ∀ j : Fin m, i + r * j.val < r * m := by
    intro j
    have hj := j.isLt
    have h1 : r * (j.val + 1) ≤ r * m := Nat.mul_le_mul (Nat.le_refl r) (by omega)
    rw [Nat.mul_succ] at h1
    omega
  have himg : Finset.univ.filter (fun v : Fin (r * m) => v.val % r = i)
      = Finset.univ.image (fun j : Fin m => (⟨i + r * j.val, hb j⟩ : Fin (r * m))) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      have hdiv : v.val / r < m := by
        rw [Nat.div_lt_iff_lt_mul hr]
        calc v.val < r * m := v.isLt
          _ = m * r := Nat.mul_comm r m
      refine ⟨⟨v.val / r, hdiv⟩, ?_⟩
      apply Fin.ext
      show i + r * (v.val / r) = v.val
      rw [← hv]
      exact Nat.mod_add_div v.val r
    · rintro ⟨j, rfl⟩
      show (i + r * j.val) % r = i
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hi
  have hinj : Function.Injective
      (fun j : Fin m => (⟨i + r * j.val, hb j⟩ : Fin (r * m))) := by
    intro j1 j2 hj
    have h1 : i + r * j1.val = i + r * j2.val := congrArg Fin.val hj
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hr (show r * j1.val = r * j2.val by omega))
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

private lemma card_residue_compl (r m i : ℕ) (hi : i < r) :
    (Finset.univ.filter (fun v : Fin (r * m) => v.val % r ≠ i)).card = r * m - m := by
  rw [Finset.filter_not, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin, card_residue_class' r m i hi]

private lemma card_two_residue_compl (r m i j : ℕ) (hi : i < r) (hj : j < r) (hij : i ≠ j) :
    (Finset.univ.filter (fun v : Fin (r * m) => v.val % r ≠ i ∧ v.val % r ≠ j)).card
      = r * m - 2 * m := by
  have hsplit : Finset.univ.filter (fun v : Fin (r * m) => v.val % r ≠ i ∧ v.val % r ≠ j)
      = Finset.univ \ (Finset.univ.filter (fun v : Fin (r * m) => v.val % r = i)
          ∪ Finset.univ.filter (fun v : Fin (r * m) => v.val % r = j)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_union, not_or]
  have hdisj : Disjoint (Finset.univ.filter (fun v : Fin (r * m) => v.val % r = i))
      (Finset.univ.filter (fun v : Fin (r * m) => v.val % r = j)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
    omega
  rw [hsplit, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_union_of_disjoint hdisj, card_residue_class' r m i hi,
    card_residue_class' r m j hj, Finset.card_univ, Fintype.card_fin]
  omega

end ResidueCounts

/-! ## The concrete types and hosts -/

private lemma tau_adj_iff' (a b : Fin 2) : FlagType_2_1.Adj a b ↔ a ≠ b := by
  show (FlagAlgebras.Compute.Sym2FlagType.toFlagType Sym2FlagType_2_1).Adj a b ↔ a ≠ b
  rw [FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff]
  revert a b
  decide

private lemma eta_not_adj' (a b : Fin 2) : ¬ FlagType_2_0.Adj a b := by
  show ¬ (FlagAlgebras.Compute.Sym2FlagType.toFlagType Sym2FlagType_2_0).Adj a b
  rw [FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff]
  revert a b
  decide

private lemma two_le_rN' {r n : ℕ} (hr : 2 ≤ r) : 2 ≤ r * (n + 1) :=
  le_trans hr (Nat.le_mul_of_pos_right r (by omega))

/-! ## Canonical labellings of the Turán terms -/

section Counting

variable (r n : ℕ)

/-- The canonical `vtype`-labelled Turán host: root at vertex `0`. -/
private def turanVtypeLabeled (hr : 2 ≤ r) : LabeledGraph vtype (Fin (r * (n + 1))) where
  graph := turanGraph (r * (n + 1)) r
  type_embed :=
    { toFun := fun _ => ⟨0, by have := two_le_rN' (n := n) hr; omega⟩
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [vtype, SimpleGraph.bot_adj]
        rw [SimpleGraph.turanGraph_adj]
        exact iff_of_false (fun hh => hh rfl) (fun hh => hh) }

/-- The canonical `τ`-labelled Turán host: roots at vertices `0` and `1`. -/
private def turanEdgeLabeled (hr : 2 ≤ r) :
    LabeledGraph FlagType_2_1 (Fin (r * (n + 1))) where
  graph := turanGraph (r * (n + 1)) r
  type_embed :=
    { toFun := fun a => ⟨a.val, by
        have h2 := two_le_rN' (n := n) hr
        have := a.isLt
        omega⟩
      inj' := by
        intro a b hab
        have h := congrArg Fin.val hab
        simp only at h
        exact Fin.ext h
      map_rel_iff' := by
        intro a b
        rw [SimpleGraph.turanGraph_adj, tau_adj_iff']
        show (a.val % r ≠ b.val % r) ↔ a ≠ b
        constructor
        · intro h hab
          subst hab
          exact h rfl
        · intro hab
          fin_cases a <;> fin_cases b
          · exact absurd rfl hab
          · show (0 : ℕ) % r ≠ 1 % r
            rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
            omega
          · show (1 : ℕ) % r ≠ 0 % r
            rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
            omega
          · exact absurd rfl hab }

/-- The canonical `η`-labelled Turán host: roots at vertices `0` and `r` (same residue
class, needs class size `≥ 2`). -/
private def turanNonEdgeLabeled (hr : 2 ≤ r) (hn : 1 ≤ n) :
    LabeledGraph FlagType_2_0 (Fin (r * (n + 1))) where
  graph := turanGraph (r * (n + 1)) r
  type_embed :=
    { toFun := fun a => ⟨a.val * r, by
        have h1 : a.val * r ≤ 1 * r := Nat.mul_le_mul (by have := a.isLt; omega) (le_refl r)
        have h2 : r * 2 ≤ r * (n + 1) := Nat.mul_le_mul (le_refl r) (by omega)
        omega⟩
      inj' := by
        intro a b hab
        have h := congrArg Fin.val hab
        simp only at h
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) h)
      map_rel_iff' := by
        intro a b
        rw [SimpleGraph.turanGraph_adj]
        show ((a.val * r : ℕ) % r ≠ (b.val * r : ℕ) % r) ↔ FlagType_2_0.Adj a b
        rw [Nat.mul_mod_left, Nat.mul_mod_left]
        exact iff_of_false (fun h => h rfl) (eta_not_adj' a b) }

/-- The canonical `vtype`-labelling of the Turán term: root at vertex `0`. -/
noncomputable def turanVtypeFlag (hr : 2 ≤ r) : FlagWithSize vtype (r * (n + 1)) :=
  ⟦turanVtypeLabeled r n hr⟧

/-- The canonical `τ`-labelling: roots `(0, 1)` (adjacent — distinct residues, `r ≥ 2`). -/
noncomputable def turanEdgeFlag (hr : 2 ≤ r) :
    FlagWithSize FlagType_2_1 (r * (n + 1)) :=
  ⟦turanEdgeLabeled r n hr⟧

/-- The canonical `η`-labelling: roots `(0, r)` (non-adjacent — same residue class; needs
class size `≥ 2`, i.e. `n ≥ 1`, and `r < r*(n+1)`). -/
noncomputable def turanNonEdgeFlag (hr : 2 ≤ r) (hn : 1 ≤ n) :
    FlagWithSize FlagType_2_0 (r * (n + 1)) :=
  ⟦turanNonEdgeLabeled r n hr hn⟧

private lemma turanVtypeFlag_unlabel (hr : 2 ≤ r) :
    unlabel (turanVtypeFlag r n hr) = (turanFlagSeq r n).2 := by
  show unlabeledGraphQuot (turanVtypeLabeled r n hr)
    = graphFlag (turanGraph (r * (n + 1)) r)
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

private lemma turanEdgeFlag_unlabel (hr : 2 ≤ r) :
    unlabel (turanEdgeFlag r n hr) = (turanFlagSeq r n).2 := by
  show unlabeledGraphQuot (turanEdgeLabeled r n hr)
    = graphFlag (turanGraph (r * (n + 1)) r)
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

private lemma turanNonEdgeFlag_unlabel (hr : 2 ≤ r) (hn : 1 ≤ n) :
    unlabel (turanNonEdgeFlag r n hr hn) = (turanFlagSeq r n).2 := by
  show unlabeledGraphQuot (turanNonEdgeLabeled r n hr hn)
    = graphFlag (turanGraph (r * (n + 1)) r)
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

/-- Membership in `labelExtensions` (each canonical labelling unlabels to the Turán flag)
— three statements bundled. -/
lemma turan_canonical_mem (hr : 2 ≤ r) (hn : 1 ≤ n) :
    turanVtypeFlag r n hr ∈ labelExtensions ((turanFlagSeq r n).2) vtype ∧
    turanEdgeFlag r n hr ∈ labelExtensions ((turanFlagSeq r n).2) FlagType_2_1 ∧
    turanNonEdgeFlag r n hr hn ∈ labelExtensions ((turanFlagSeq r n).2) FlagType_2_0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [labelExtensions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact turanVtypeFlag_unlabel r n hr
  · simp only [labelExtensions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact turanEdgeFlag_unlabel r n hr
  · simp only [labelExtensions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact turanNonEdgeFlag_unlabel r n hr hn

/-- Per-term type-density positivity (`σ`-pattern exists in the Turán term): the single
vertex always; an edge for `r ≥ 2`; a non-edge for class size `≥ 2`. -/
lemma turan_type_density_pos (hr : 2 ≤ r) (hn : 1 ≤ n) :
    flagDensity₁ (vtype).toEmptyTypeFlag (turanFlagSeq r n).2 > 0 ∧
    flagDensity₁ (FlagType_2_1).toEmptyTypeFlag (turanFlagSeq r n).2 > 0 ∧
    flagDensity₁ (FlagType_2_0).toEmptyTypeFlag (turanFlagSeq r n).2 > 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← turanVtypeFlag_unlabel r n hr]
    exact flagDensity₁_flagType_asEmptyType_pos ⟨r * (n + 1), turanVtypeFlag r n hr⟩
  · rw [← turanEdgeFlag_unlabel r n hr]
    exact flagDensity₁_flagType_asEmptyType_pos ⟨r * (n + 1), turanEdgeFlag r n hr⟩
  · rw [← turanNonEdgeFlag_unlabel r n hr hn]
    exact flagDensity₁_flagType_asEmptyType_pos ⟨r * (n + 1), turanNonEdgeFlag r n hr hn⟩

/-! ## Single-root extension counts

In `turanGraph (r·m) r` with `m := n+1` and `N := r·m`, for a third vertex `w`:
adjacent to a root `u` ⟺ `w % r ≠ u % r`.  Counting the `w`s with each pattern gives the
exact rooted densities below (denominator `(N - 2).choose 1 = N - 2`, resp. `N - 1` at
`vtype`). -/

/-- `vtype`: the rooted edge density at the canonical root is `(r-1)·m / (N-1)`. -/
lemma turanVtypeFlag_edge_density (hr : 2 ≤ r) :
    flagDensity₁ edgeFF.2 (turanVtypeFlag r n hr)
      = ((r - 1) * (n + 1) : ℚ) / (r * (n + 1) - 1) := by
  have h2N := two_le_rN' (n := n) hr
  show flagDensity₁ edgeFF.2
      (⟦turanVtypeLabeled r n hr⟧ : Flag vtype (Fin (r * (n + 1)))) = _
  rw [oneRoot_edge_density (turanVtypeLabeled r n hr) ⟨0, by omega⟩ (fun t => rfl)]
  have hns : ((turanVtypeLabeled r n hr).graph.neighborSet
      (⟨0, by omega⟩ : Fin (r * (n + 1)))).ncard = r * (n + 1) - (n + 1) := by
    have hset : (turanVtypeLabeled r n hr).graph.neighborSet
        (⟨0, by omega⟩ : Fin (r * (n + 1)))
        = {w : Fin (r * (n + 1)) | w.val % r ≠ 0} := by
      ext w
      show (turanGraph (r * (n + 1)) r).Adj ⟨0, by omega⟩ w ↔ _
      rw [SimpleGraph.turanGraph_adj]
      show ((0 : ℕ) % r ≠ w.val % r) ↔ _
      rw [Nat.zero_mod]
      exact ne_comm
    rw [hset, ncard_setOf_eq_filter_card, card_residue_compl r (n + 1) 0 (by omega)]
  rw [hns]
  have hle : n + 1 ≤ r * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  rw [Nat.cast_sub hle]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ r * (n + 1))]
  push_cast
  congr 1
  ring

/-! ### The pattern counts in the two-root hosts -/

private lemma tau_count_TF (hr : 2 ≤ r) (P Q : Prop) (hP : P) (hQ : ¬ Q) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)}
      = n := by
  have hval0 : ((turanEdgeLabeled r n hr).type_embed 0).val = 0 := rfl
  have hval1 : ((turanEdgeLabeled r n hr).type_embed 1).val = 1 := rfl
  have h1r : (1 : ℕ) % r = 1 := Nat.mod_eq_of_lt (by omega)
  rw [ncard_setOf_eq_filter_card]
  have hpe : (Finset.univ.filter (fun w : Fin (r * (n + 1)) =>
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)))
      = (Finset.univ.filter (fun w : Fin (r * (n + 1)) => w.val % r = 1)).erase
          ((turanEdgeLabeled r n hr).type_embed 1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hw0, hw1, hp0, hp1⟩
      refine ⟨hw1, ?_⟩
      have hadj0 : (turanGraph (r * (n + 1)) r).Adj
          ((turanEdgeLabeled r n hr).type_embed 0) w := hp0.mpr hP
      have hnadj1 : ¬ (turanGraph (r * (n + 1)) r).Adj
          ((turanEdgeLabeled r n hr).type_embed 1) w := fun ha => hQ (hp1.mp ha)
      rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod] at hadj0
      rw [SimpleGraph.turanGraph_adj, hval1, h1r] at hnadj1
      omega
    · rintro ⟨hw1, hres⟩
      have hw0 : w ≠ (turanEdgeLabeled r n hr).type_embed 0 := by
        intro hh
        have hv : w.val = 0 := by rw [hh, hval0]
        rw [hv, Nat.zero_mod] at hres
        omega
      refine ⟨hw0, hw1, ?_, ?_⟩
      · refine iff_of_true ?_ hP
        show (turanGraph (r * (n + 1)) r).Adj ((turanEdgeLabeled r n hr).type_embed 0) w
        rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod]
        omega
      · refine iff_of_false ?_ hQ
        show ¬ (turanGraph (r * (n + 1)) r).Adj ((turanEdgeLabeled r n hr).type_embed 1) w
        rw [SimpleGraph.turanGraph_adj, hval1, h1r]
        omega
  rw [hpe, Finset.card_erase_of_mem (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hval1]
      exact h1r),
    card_residue_class' r (n + 1) 1 (by omega)]
  omega

private lemma tau_count_FT (hr : 2 ≤ r) (P Q : Prop) (hP : ¬ P) (hQ : Q) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)}
      = n := by
  have hval0 : ((turanEdgeLabeled r n hr).type_embed 0).val = 0 := rfl
  have hval1 : ((turanEdgeLabeled r n hr).type_embed 1).val = 1 := rfl
  have h1r : (1 : ℕ) % r = 1 := Nat.mod_eq_of_lt (by omega)
  rw [ncard_setOf_eq_filter_card]
  have hpe : (Finset.univ.filter (fun w : Fin (r * (n + 1)) =>
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)))
      = (Finset.univ.filter (fun w : Fin (r * (n + 1)) => w.val % r = 0)).erase
          ((turanEdgeLabeled r n hr).type_embed 0) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hw0, hw1, hp0, hp1⟩
      refine ⟨hw0, ?_⟩
      have hnadj0 : ¬ (turanGraph (r * (n + 1)) r).Adj
          ((turanEdgeLabeled r n hr).type_embed 0) w := fun ha => hP (hp0.mp ha)
      rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod] at hnadj0
      omega
    · rintro ⟨hw0, hres⟩
      have hw1 : w ≠ (turanEdgeLabeled r n hr).type_embed 1 := by
        intro hh
        have hv : w.val = 1 := by rw [hh, hval1]
        rw [hv, h1r] at hres
        omega
      refine ⟨hw0, hw1, ?_, ?_⟩
      · refine iff_of_false ?_ hP
        show ¬ (turanGraph (r * (n + 1)) r).Adj ((turanEdgeLabeled r n hr).type_embed 0) w
        rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod]
        omega
      · refine iff_of_true ?_ hQ
        show (turanGraph (r * (n + 1)) r).Adj ((turanEdgeLabeled r n hr).type_embed 1) w
        rw [SimpleGraph.turanGraph_adj, hval1, h1r]
        omega
  rw [hpe, Finset.card_erase_of_mem (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hval0]
      exact Nat.zero_mod r),
    card_residue_class' r (n + 1) 0 (by omega)]
  omega

private lemma tau_count_TT (hr : 2 ≤ r) (P Q : Prop) (hP : P) (hQ : Q) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)}
      = r * (n + 1) - 2 * (n + 1) := by
  have hval0 : ((turanEdgeLabeled r n hr).type_embed 0).val = 0 := rfl
  have hval1 : ((turanEdgeLabeled r n hr).type_embed 1).val = 1 := rfl
  have h1r : (1 : ℕ) % r = 1 := Nat.mod_eq_of_lt (by omega)
  rw [ncard_setOf_eq_filter_card]
  have hpe : (Finset.univ.filter (fun w : Fin (r * (n + 1)) =>
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)))
      = Finset.univ.filter
          (fun w : Fin (r * (n + 1)) => w.val % r ≠ 0 ∧ w.val % r ≠ 1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw0, hw1, hp0, hp1⟩
      have hadj0 : (turanGraph (r * (n + 1)) r).Adj
          ((turanEdgeLabeled r n hr).type_embed 0) w := hp0.mpr hP
      have hadj1 : (turanGraph (r * (n + 1)) r).Adj
          ((turanEdgeLabeled r n hr).type_embed 1) w := hp1.mpr hQ
      rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod] at hadj0
      rw [SimpleGraph.turanGraph_adj, hval1, h1r] at hadj1
      omega
    · rintro ⟨hres0, hres1⟩
      have hw0 : w ≠ (turanEdgeLabeled r n hr).type_embed 0 := by
        intro hh
        have hv : w.val = 0 := by rw [hh, hval0]
        rw [hv, Nat.zero_mod] at hres0
        omega
      have hw1 : w ≠ (turanEdgeLabeled r n hr).type_embed 1 := by
        intro hh
        have hv : w.val = 1 := by rw [hh, hval1]
        rw [hv, h1r] at hres1
        omega
      refine ⟨hw0, hw1, ?_, ?_⟩
      · refine iff_of_true ?_ hP
        show (turanGraph (r * (n + 1)) r).Adj ((turanEdgeLabeled r n hr).type_embed 0) w
        rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod]
        omega
      · refine iff_of_true ?_ hQ
        show (turanGraph (r * (n + 1)) r).Adj ((turanEdgeLabeled r n hr).type_embed 1) w
        rw [SimpleGraph.turanGraph_adj, hval1, h1r]
        omega
  rw [hpe, card_two_residue_compl r (n + 1) 0 1 (by omega) (by omega) (by omega)]

private lemma tau_count_FF (hr : 2 ≤ r) (P Q : Prop) (hP : ¬ P) (hQ : ¬ Q) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanEdgeLabeled r n hr).type_embed 0 ∧
      w ≠ (turanEdgeLabeled r n hr).type_embed 1 ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 0) w ↔ P) ∧
      ((turanEdgeLabeled r n hr).graph.Adj ((turanEdgeLabeled r n hr).type_embed 1) w ↔ Q)}
      = 0 := by
  have hval0 : ((turanEdgeLabeled r n hr).type_embed 0).val = 0 := rfl
  have hval1 : ((turanEdgeLabeled r n hr).type_embed 1).val = 1 := rfl
  have h1r : (1 : ℕ) % r = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Set.ncard_eq_zero]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hw0, hw1, hp0, hp1⟩
  have hnadj0 : ¬ (turanGraph (r * (n + 1)) r).Adj
      ((turanEdgeLabeled r n hr).type_embed 0) w := fun ha => hP (hp0.mp ha)
  have hnadj1 : ¬ (turanGraph (r * (n + 1)) r).Adj
      ((turanEdgeLabeled r n hr).type_embed 1) w := fun ha => hQ (hp1.mp ha)
  rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod] at hnadj0
  rw [SimpleGraph.turanGraph_adj, hval1, h1r] at hnadj1
  omega

private lemma eta_count_FF (hr : 2 ≤ r) (hn : 1 ≤ n) (P Q : Prop) (hP : ¬ P) (hQ : ¬ Q) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 ∧
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 1 ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 0) w ↔ P) ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 1) w ↔ Q)}
      = n - 1 := by
  have hval0 : ((turanNonEdgeLabeled r n hr hn).type_embed 0).val = 0 := Nat.zero_mul r
  have hval1 : ((turanNonEdgeLabeled r n hr hn).type_embed 1).val = r := Nat.one_mul r
  have hrr : (r : ℕ) % r = 0 := Nat.mod_self r
  rw [ncard_setOf_eq_filter_card]
  have hpe : (Finset.univ.filter (fun w : Fin (r * (n + 1)) =>
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 ∧
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 1 ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 0) w ↔ P) ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 1) w ↔ Q)))
      = ((Finset.univ.filter (fun w : Fin (r * (n + 1)) => w.val % r = 0)).erase
          ((turanNonEdgeLabeled r n hr hn).type_embed 0)).erase
          ((turanNonEdgeLabeled r n hr hn).type_embed 1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hw0, hw1, hp0, hp1⟩
      refine ⟨hw1, hw0, ?_⟩
      have hnadj0 : ¬ (turanGraph (r * (n + 1)) r).Adj
          ((turanNonEdgeLabeled r n hr hn).type_embed 0) w := fun ha => hP (hp0.mp ha)
      rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod] at hnadj0
      omega
    · rintro ⟨hw1, hw0, hres⟩
      refine ⟨hw0, hw1, ?_, ?_⟩
      · refine iff_of_false ?_ hP
        show ¬ (turanGraph (r * (n + 1)) r).Adj
          ((turanNonEdgeLabeled r n hr hn).type_embed 0) w
        rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod]
        omega
      · refine iff_of_false ?_ hQ
        show ¬ (turanGraph (r * (n + 1)) r).Adj
          ((turanNonEdgeLabeled r n hr hn).type_embed 1) w
        rw [SimpleGraph.turanGraph_adj, hval1, hrr]
        omega
  have hmem0 : (turanNonEdgeLabeled r n hr hn).type_embed 0
      ∈ Finset.univ.filter (fun w : Fin (r * (n + 1)) => w.val % r = 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval0]
    exact Nat.zero_mod r
  have hne01 : (turanNonEdgeLabeled r n hr hn).type_embed 1
      ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hval0, hval1] at hv
    omega
  have hmem1 : (turanNonEdgeLabeled r n hr hn).type_embed 1
      ∈ (Finset.univ.filter (fun w : Fin (r * (n + 1)) => w.val % r = 0)).erase
          ((turanNonEdgeLabeled r n hr hn).type_embed 0) := by
    rw [Finset.mem_erase]
    refine ⟨hne01, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval1]
    exact hrr
  rw [hpe, Finset.card_erase_of_mem hmem1, Finset.card_erase_of_mem hmem0,
    card_residue_class' r (n + 1) 0 (by omega)]
  omega

private lemma eta_count_TT (hr : 2 ≤ r) (hn : 1 ≤ n) (P Q : Prop) (hP : P) (hQ : Q) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 ∧
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 1 ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 0) w ↔ P) ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 1) w ↔ Q)}
      = r * (n + 1) - (n + 1) := by
  have hval0 : ((turanNonEdgeLabeled r n hr hn).type_embed 0).val = 0 := Nat.zero_mul r
  have hval1 : ((turanNonEdgeLabeled r n hr hn).type_embed 1).val = r := Nat.one_mul r
  have hrr : (r : ℕ) % r = 0 := Nat.mod_self r
  rw [ncard_setOf_eq_filter_card]
  have hpe : (Finset.univ.filter (fun w : Fin (r * (n + 1)) =>
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 ∧
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 1 ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 0) w ↔ P) ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 1) w ↔ Q)))
      = Finset.univ.filter (fun w : Fin (r * (n + 1)) => w.val % r ≠ 0) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw0, hw1, hp0, hp1⟩
      have hadj0 : (turanGraph (r * (n + 1)) r).Adj
          ((turanNonEdgeLabeled r n hr hn).type_embed 0) w := hp0.mpr hP
      rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod] at hadj0
      omega
    · intro hres
      have hw0 : w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 := by
        intro hh
        have hv : w.val = 0 := by rw [hh, hval0]
        rw [hv, Nat.zero_mod] at hres
        omega
      have hw1 : w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 1 := by
        intro hh
        have hv : w.val = r := by rw [hh, hval1]
        rw [hv, hrr] at hres
        omega
      refine ⟨hw0, hw1, ?_, ?_⟩
      · refine iff_of_true ?_ hP
        show (turanGraph (r * (n + 1)) r).Adj
          ((turanNonEdgeLabeled r n hr hn).type_embed 0) w
        rw [SimpleGraph.turanGraph_adj, hval0, Nat.zero_mod]
        omega
      · refine iff_of_true ?_ hQ
        show (turanGraph (r * (n + 1)) r).Adj
          ((turanNonEdgeLabeled r n hr hn).type_embed 1) w
        rw [SimpleGraph.turanGraph_adj, hval1, hrr]
        omega
  rw [hpe, card_residue_compl r (n + 1) 0 (by omega)]

private lemma eta_count_mixed (hr : 2 ≤ r) (hn : 1 ≤ n) (P Q : Prop)
    (hPQ : ¬ (P ↔ Q)) :
    Set.ncard {w : Fin (r * (n + 1)) |
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 0 ∧
      w ≠ (turanNonEdgeLabeled r n hr hn).type_embed 1 ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 0) w ↔ P) ∧
      ((turanNonEdgeLabeled r n hr hn).graph.Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 1) w ↔ Q)}
      = 0 := by
  have hval0 : ((turanNonEdgeLabeled r n hr hn).type_embed 0).val = 0 := Nat.zero_mul r
  have hval1 : ((turanNonEdgeLabeled r n hr hn).type_embed 1).val = r := Nat.one_mul r
  have hrr : (r : ℕ) % r = 0 := Nat.mod_self r
  rw [Set.ncard_eq_zero]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hw0, hw1, hp0, hp1⟩
  have hadj_iff : (turanGraph (r * (n + 1)) r).Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 0) w
      ↔ (turanGraph (r * (n + 1)) r).Adj
        ((turanNonEdgeLabeled r n hr hn).type_embed 1) w := by
    rw [SimpleGraph.turanGraph_adj, SimpleGraph.turanGraph_adj, hval0, hval1,
      Nat.zero_mod, hrr]
  exact hPQ ((hp0.symm.trans hadj_iff).trans hp1)

/-- `τ`: the four rooted 3-vertex densities at roots `(0,1)`:
`a_τ = b_τ = n/(N-2)`, `g_τ = (r-2)(n+1)/(N-2)`, `z_τ = 0`. -/
lemma turanEdgeFlag_densities (hr : 2 ≤ r) :
    flagDensity₁ (⟨3, Flag_3_2_1_1⟩ : FinFlag FlagType_2_1).2 (turanEdgeFlag r n hr)
        = (n : ℚ) / (r * (n + 1) - 2) ∧
    flagDensity₁ (⟨3, Flag_3_2_1_2⟩ : FinFlag FlagType_2_1).2 (turanEdgeFlag r n hr)
        = (n : ℚ) / (r * (n + 1) - 2) ∧
    flagDensity₁ (⟨3, Flag_3_2_1_3⟩ : FinFlag FlagType_2_1).2 (turanEdgeFlag r n hr)
        = ((r - 2) * (n + 1) : ℚ) / (r * (n + 1) - 2) ∧
    flagDensity₁ (⟨3, Flag_3_2_1_0⟩ : FinFlag FlagType_2_1).2 (turanEdgeFlag r n hr)
        = 0 := by
  have h2N := two_le_rN' (n := n) hr
  have hcastden : ((r * (n + 1) - 2 : ℕ) : ℚ) = (r : ℚ) * ((n : ℚ) + 1) - 2 := by
    push_cast [Nat.cast_sub h2N]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- a_τ: third vertex adjacent to root 0 only
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_1⟧ :
          Flag FlagType_2_1 (Fin 3))
        (⟦turanEdgeLabeled r n hr⟧ : Flag FlagType_2_1 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanEdgeLabeled r n hr)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_1) 2
      (by decide) (by decide)]
    rw [tau_count_TF r n hr _ _
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)]
    rw [hcastden]
  · -- b_τ: third vertex adjacent to root 1 only
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_2⟧ :
          Flag FlagType_2_1 (Fin 3))
        (⟦turanEdgeLabeled r n hr⟧ : Flag FlagType_2_1 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanEdgeLabeled r n hr)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_2) 2
      (by decide) (by decide)]
    rw [tau_count_FT r n hr _ _
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)]
    rw [hcastden]
  · -- g_τ: third vertex adjacent to both roots
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_3⟧ :
          Flag FlagType_2_1 (Fin 3))
        (⟦turanEdgeLabeled r n hr⟧ : Flag FlagType_2_1 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanEdgeLabeled r n hr)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_3) 2
      (by decide) (by decide)]
    rw [tau_count_TT r n hr _ _
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)]
    rw [hcastden]
    have hle : 2 * (n + 1) ≤ r * (n + 1) := Nat.mul_le_mul hr (le_refl (n + 1))
    rw [Nat.cast_sub hle]
    push_cast
    congr 1
    ring
  · -- z_τ: third vertex adjacent to neither root
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_0⟧ :
          Flag FlagType_2_1 (Fin 3))
        (⟦turanEdgeLabeled r n hr⟧ : Flag FlagType_2_1 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanEdgeLabeled r n hr)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_1_0) 2
      (by decide) (by decide)]
    rw [tau_count_FF r n hr _ _
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)]
    norm_num

/-- `η`: the four rooted densities at roots `(0, r)`:
`z_η = (n-1)/(N-2)`, `g_η = (r-1)(n+1)/(N-2)`, `a_η = b_η = 0`. -/
lemma turanNonEdgeFlag_densities (hr : 2 ≤ r) (hn : 1 ≤ n) :
    flagDensity₁ (⟨3, Flag_3_2_0_0⟩ : FinFlag FlagType_2_0).2 (turanNonEdgeFlag r n hr hn)
        = ((n : ℚ) - 1) / (r * (n + 1) - 2) ∧
    flagDensity₁ (⟨3, Flag_3_2_0_3⟩ : FinFlag FlagType_2_0).2 (turanNonEdgeFlag r n hr hn)
        = ((r - 1) * (n + 1) : ℚ) / (r * (n + 1) - 2) ∧
    flagDensity₁ (⟨3, Flag_3_2_0_1⟩ : FinFlag FlagType_2_0).2 (turanNonEdgeFlag r n hr hn)
        = 0 ∧
    flagDensity₁ (⟨3, Flag_3_2_0_2⟩ : FinFlag FlagType_2_0).2 (turanNonEdgeFlag r n hr hn)
        = 0 := by
  have h2N := two_le_rN' (n := n) hr
  have hcastden : ((r * (n + 1) - 2 : ℕ) : ℚ) = (r : ℚ) * ((n : ℚ) + 1) - 2 := by
    push_cast [Nat.cast_sub h2N]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- z_η: third vertex adjacent to neither root
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_0⟧ :
          Flag FlagType_2_0 (Fin 3))
        (⟦turanNonEdgeLabeled r n hr hn⟧ : Flag FlagType_2_0 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanNonEdgeLabeled r n hr hn)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_0) 2
      (by decide) (by decide)]
    rw [eta_count_FF r n hr hn _ _
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)]
    rw [hcastden, Nat.cast_sub hn]
    push_cast
    ring_nf
  · -- g_η: third vertex adjacent to both roots
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_3⟧ :
          Flag FlagType_2_0 (Fin 3))
        (⟦turanNonEdgeLabeled r n hr hn⟧ : Flag FlagType_2_0 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanNonEdgeLabeled r n hr hn)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_3) 0
      (by decide) (by decide)]
    rw [eta_count_TT r n hr hn _ _
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)
      (by rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide)]
    rw [hcastden]
    have hle : n + 1 ≤ r * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.cast_sub hle]
    push_cast
    congr 1
    ring
  · -- a_η: third vertex adjacent to root 0 only (impossible: same class)
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_1⟧ :
          Flag FlagType_2_0 (Fin 3))
        (⟦turanNonEdgeLabeled r n hr hn⟧ : Flag FlagType_2_0 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanNonEdgeLabeled r n hr hn)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_1) 1
      (by decide) (by decide)]
    rw [eta_count_mixed r n hr hn _ _ (by
      rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff,
        FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]
      decide)]
    norm_num
  · -- b_η: third vertex adjacent to root 1 only (impossible: same class)
    show flagDensity₁
        (⟦FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_2⟧ :
          Flag FlagType_2_0 (Fin 3))
        (⟦turanNonEdgeLabeled r n hr hn⟧ : Flag FlagType_2_0 (Fin (r * (n + 1)))) = _
    rw [twoRoot_density (turanNonEdgeLabeled r n hr hn)
      (FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph Sym2LabeledGraph_3_2_0_2) 1
      (by decide) (by decide)]
    rw [eta_count_mixed r n hr hn _ _ (by
      rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff,
        FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]
      decide)]
    norm_num

end Counting

/-! ## The single-point relative supports of the Turán limit -/

/-- `ConvergesTo` is stable under composition with a strictly monotone index map
(private mirror of `RelativePlanted`'s helper). -/
private lemma convergesTo_comp_strictMono' {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {s : FlagSeq σ} {a : FinFlag σ → ℝ} {ϕ : ℕ → ℕ} (hϕ : StrictMono ϕ)
    (h : ConvergesTo s a) : ConvergesTo (s ∘ ϕ) a :=
  ⟨h.1.comp hϕ, h.2.comp hϕ.tendsto_atTop⟩

/-- Each tail-shifted subsequence index is at least `1`. -/
private lemma turan_tail_subseq_ge (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    1 ≤ turanSubseq r hr (k + 1) := by
  have h : k + 1 ≤ turanSubseq r hr (k + 1) := (turanLimit_spec r hr).1.id_le (k + 1)
  omega

/-- The assembly package: unique labellings + type positivity make the relative support of
the singleton a single point, with coordinatewise convergence of the canonical labellings'
densities along the tail-shifted subsequence. -/
private lemma turan_dirac_package (r : ℕ) (hr : 2 ≤ r) {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    (hσ : (turanLimit r hr) ⟨σ⟩₀ > 0)
    (Gsel : ∀ m : ℕ, 1 ≤ m → FlagWithSize σ (r * (m + 1)))
    (hGsel : ∀ m (hm : 1 ≤ m), Gsel m hm ∈ labelExtensions ((turanFlagSeq r m).2) σ)
    (hsing : ∀ m : ℕ, ∀ G₁ ∈ labelExtensions ((turanFlagSeq r m).2) σ,
      ∀ G₂ ∈ labelExtensions ((turanFlagSeq r m).2) σ, G₁ = G₂)
    (hpos : ∀ m : ℕ, 1 ≤ m → flagDensity₁ σ.toEmptyTypeFlag ((turanFlagSeq r m).2) > 0) :
    ∃ χ : PositiveHomSpace σ,
      relSσ {posHomPoint (turanLimit r hr)} σ = {χ} ∧
      ∀ F : FinFlag σ,
        Tendsto (fun k => (flagDensity₁ F.2
          (Gsel (turanSubseq r hr (k + 1)) (turan_tail_subseq_ge r hr k)) : ℝ))
          atTop (𝓝 (χ.val F)) := by
  obtain ⟨hmono, hconv, hmem, hρ⟩ := turanLimit_spec r hr
  have hshift : StrictMono (fun k : ℕ => k + 1) := fun a b h => Nat.add_lt_add_right h 1
  have hconv' : ConvergesTo ((turanFlagSeq r ∘ turanSubseq r hr) ∘ (fun k : ℕ => k + 1))
      (turanLimit r hr).coe := convergesTo_comp_strictMono' hshift hconv
  obtain ⟨χ, hdirac, hcoord⟩ := extend_eq_dirac_of_labelExtensions_subsingleton
    (s := (turanFlagSeq r ∘ turanSubseq r hr) ∘ (fun k : ℕ => k + 1)) hconv' hσ
    (fun k => hpos _ (turan_tail_subseq_ge r hr k))
    (fun k => Gsel _ (turan_tail_subseq_ge r hr k))
    (fun k => hGsel _ _)
    (fun k => hsing _)
  exact ⟨χ, relSσ_singleton_of_extend_dirac hσ hdirac, hcoord⟩

/-- The scalar limit `(a·(m+1) + b)/(c·(m+1) + d) → a/c` (all coefficients real, `c > 0`). -/
private lemma tendsto_linear_ratio {a b c d : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (a * (m + 1) + b) / (c * (m + 1) + d)) atTop (𝓝 (a / c)) := by
  have hb : Tendsto (fun m : ℕ => (a + b) / m) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (a + b)
  have hd : Tendsto (fun m : ℕ => (c + d) / m) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (c + d)
  have h1 : Tendsto (fun m : ℕ => a + (a + b) / m) atTop (𝓝 a) := by
    have h := (tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ))).add hb
    simpa using h
  have h2 : Tendsto (fun m : ℕ => c + (c + d) / m) atTop (𝓝 c) := by
    have h := (tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ))).add hd
    simpa using h
  have h3 : Tendsto (fun m : ℕ => (a + (a + b) / m) / (c + (c + d) / m)) atTop
      (𝓝 (a / c)) := h1.div h2 (ne_of_gt hc)
  refine h3.congr' ?_
  have hden : Tendsto (fun m : ℕ => c * ((m : ℝ) + 1) + d) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact Tendsto.const_mul_atTop hc
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1, hden.eventually_gt_atTop 0] with m hm hpos
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hy : c + (c + d) / m ≠ 0 := by
    have hxy : c + (c + d) / m = (c * ((m : ℝ) + 1) + d) / m := by
      field_simp
      ring
    rw [hxy]
    exact ne_of_gt (div_pos hpos (by linarith))
  rw [div_eq_div_iff hy (ne_of_gt hpos)]
  field_simp
  ring

/-- The chosen limit's coordinate at the two-vertex unlabelled edge flag is `(r-1)/r`. -/
private lemma turanLimit_edge_basis (r : ℕ) (hr : 2 ≤ r) :
    (turanLimit r hr) (⟦basisVector ⟨2, unlabelledEdgeFlag⟩⟧ : FlagAlgebra ∅ₜ)
      = ((r : ℝ) - 1) / r := by
  obtain ⟨hmono, hconv, -, -⟩ := turanLimit_spec r hr
  rw [← PositiveHom.coe_flag]
  have h1 := (flagSeq_convergesTo_iff.mp hconv).2 ⟨2, unlabelledEdgeFlag⟩
  have h2 : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ turanSubseq r hr) k
      ⟨2, unlabelledEdgeFlag⟩) atTop (𝓝 (((r : ℝ) - 1) / r)) :=
    (turanFlagSeq_edge_density_tendsto r hr).comp hmono.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-- The tail-shifted subsequence tends to infinity. -/
private lemma turan_tail_tendsto (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun k => turanSubseq r hr (k + 1)) atTop atTop :=
  ((turanLimit_spec r hr).1.comp
    (fun _ _ h => Nat.add_lt_add_right h 1 : StrictMono fun k : ℕ => k + 1)).tendsto_atTop

/-- The edge type equals the two-vertex complete graph. -/
private lemma tau_type_eq_top : FlagType_2_1 = edgeGraph := by
  ext a b
  rw [tau_adj_iff', SimpleGraph.top_adj]

/-- The non-edge type equals the two-vertex empty graph. -/
private lemma eta_type_eq_bot : FlagType_2_0 = (⊥ : SimpleGraph (Fin 2)) := by
  ext a b
  rw [SimpleGraph.bot_adj]
  exact iff_of_false (eta_not_adj' a b) not_false

private lemma tau_toEmptyTypeFlag : FlagType_2_1.toEmptyTypeFlag = unlabelledEdgeFlag := by
  rw [tau_type_eq_top]
  show (⟦_⟧ : Flag ∅ₜ (Fin 2)) = ⟦_⟧
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

private lemma eta_toEmptyTypeFlag :
    FlagType_2_0.toEmptyTypeFlag = graphFlag (⊥ : SimpleGraph (Fin 2)) := by
  rw [eta_type_eq_bot]
  show (⟦_⟧ : Flag ∅ₜ (Fin 2)) = ⟦_⟧
  apply Quotient.sound
  exact ⟨{ graph_iso := SimpleGraph.Iso.refl,
           type_preserve := funext fun t => Fin.elim0 t }⟩

/-- Every two-vertex `∅ₜ`-flag is the edge or the non-edge (local re-derivation of
`SinglePoint`'s classification, which lies outside this module's import closure). -/
private lemma flagWithSize_two_cases (D : FlagWithSize ∅ₜ 2) :
    D = unlabelledEdgeFlag ∨ D = graphFlag (⊥ : SimpleGraph (Fin 2)) := by
  induction D using Quotient.inductionOn with
  | _ L =>
  have hquot : ∀ (G' : SimpleGraph (Fin 2)), L.graph = G' →
      (⟦L⟧ : FlagWithSize ∅ₜ 2) = graphFlag G' := by
    intro G' hG'
    apply Quotient.sound
    exact ⟨{ graph_iso := hG' ▸ SimpleGraph.Iso.refl,
             type_preserve := funext fun t => Fin.elim0 t }⟩
  by_cases hadj : L.graph.Adj 0 1
  · left
    apply hquot
    ext a b
    rw [SimpleGraph.top_adj]
    constructor
    · exact fun h => h.ne
    · intro hab
      rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with ha | ha <;>
        rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;> rw [ha, hb]
      · exact absurd (ha.trans hb.symm) hab
      · exact hadj
      · exact hadj.symm
      · exact absurd (ha.trans hb.symm) hab
  · right
    apply hquot
    ext a b
    rw [SimpleGraph.bot_adj, iff_false]
    intro hab
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with ha | ha <;>
      rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;> rw [ha, hb] at hab
    · exact L.graph.irrefl hab
    · exact hadj hab
    · exact hadj hab.symm
    · exact L.graph.irrefl hab

private lemma edge_ne_nonedge :
    unlabelledEdgeFlag ≠ graphFlag (⊥ : SimpleGraph (Fin 2)) := by
  intro hEq
  obtain ⟨ψ⟩ := Quotient.exact hEq
  have hadj : edgeGraph.Adj 0 1 := by
    rw [SimpleGraph.top_adj]
    decide
  have hbot : (⊥ : SimpleGraph (Fin 2)).Adj (ψ.graph_iso 0) (ψ.graph_iso 1) :=
    ψ.graph_iso.map_rel_iff.mpr hadj
  exact hbot

/-- The two-vertex flags are exactly the edge and the non-edge. -/
private lemma flagWithSize_two_univ :
    (Finset.univ : Finset (FlagWithSize ∅ₜ 2))
      = {unlabelledEdgeFlag, graphFlag (⊥ : SimpleGraph (Fin 2))} := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intro D
  rcases flagWithSize_two_cases D with hD | hD
  · rw [hD]
    exact Finset.mem_insert_self _ _
  · rw [hD]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- `vtype`: `S_vtype({φ_Tr})` is a single point with rooted edge density `(r-1)/r`. -/
theorem turanLimit_relSσ_vtype (r : ℕ) (hr : 2 ≤ r) :
    ∃ χ : PositiveHomSpace vtype,
      relSσ {posHomPoint (turanLimit r hr)} vtype = {χ} ∧
      (PositiveHomSpace.toPosHom χ) e = ((r : ℝ) - 1) / r := by
  have hσ : (turanLimit r hr) ⟨vtype⟩₀ > 0 := by
    rw [vtype_asEmptyTypeAlgebra_eq_one, PositiveHom.map_one]
    exact one_pos
  obtain ⟨χ, hsingleton, hcoord⟩ := turan_dirac_package r hr hσ
    (fun m _ => turanVtypeFlag r m hr)
    (fun m hm => (turan_canonical_mem r m hr hm).1)
    (fun m => labelExtensions_turan_vtype_subsingleton r m hr)
    (fun m hm => (turan_type_density_pos r m hr hm).1)
  refine ⟨χ, hsingleton, ?_⟩
  show (PositiveHomSpace.toPosHom χ) ⟦basisVector edgeFF⟧ = ((r : ℝ) - 1) / r
  rw [PositiveHomSpace.toPosHom_basisVector]
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  refine tendsto_nhds_unique (hcoord edgeFF) ?_
  have hlim : Tendsto (fun m : ℕ =>
      (((r : ℝ) - 1) * ((m : ℝ) + 1) + 0) / ((r : ℝ) * ((m : ℝ) + 1) + (-1)))
      atTop (𝓝 (((r : ℝ) - 1) / r)) :=
    tendsto_linear_ratio hrpos
  refine (hlim.comp (turan_tail_tendsto r hr)).congr ?_
  intro k
  simp only [Function.comp_apply]
  show _ = (flagDensity₁ edgeFF.2 (turanVtypeFlag r (turanSubseq r hr (k + 1)) hr) : ℝ)
  rw [turanVtypeFlag_edge_density r (turanSubseq r hr (k + 1)) hr]
  push_cast
  congr 1
  ring

/-- `τ`: `S_τ({φ_Tr})` is a single point with `a_τ = b_τ = 1/r`, `g_τ = (r-2)/r`,
`z_τ = 0`. -/
theorem turanLimit_relSσ_edge (r : ℕ) (hr : 2 ≤ r) :
    ∃ χ : PositiveHomSpace FlagType_2_1,
      relSσ {posHomPoint (turanLimit r hr)} FlagType_2_1 = {χ} ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1 = 1 / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2 = 1 / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 = ((r : ℝ) - 2) / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_0 = 0 := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hσ : (turanLimit r hr) ⟨FlagType_2_1⟩₀ > 0 := by
    show (turanLimit r hr) ⟦basisVector ⟨2, FlagType_2_1.toEmptyTypeFlag⟩⟧ > 0
    rw [tau_toEmptyTypeFlag, turanLimit_edge_basis r hr]
    have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    apply div_pos <;> linarith
  obtain ⟨χ, hsingleton, hcoord⟩ := turan_dirac_package r hr hσ
    (fun m hm => turanEdgeFlag r m hr)
    (fun m hm => (turan_canonical_mem r m hr hm).2.1)
    (fun m => labelExtensions_turan_edge_subsingleton r m hr)
    (fun m hm => (turan_type_density_pos r m hr hm).2.1)
  refine ⟨χ, hsingleton, ?_, ?_, ?_, ?_⟩
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_1_1⟩⟧ = 1 / r
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_1_1⟩) ?_
    have hlim : Tendsto (fun m : ℕ =>
        ((1 : ℝ) * ((m : ℝ) + 1) + (-1)) / ((r : ℝ) * ((m : ℝ) + 1) + (-2)))
        atTop (𝓝 ((1 : ℝ) / r)) := tendsto_linear_ratio hrpos
    refine (hlim.comp (turan_tail_tendsto r hr)).congr ?_
    intro k
    simp only [Function.comp_apply]
    show _ = (flagDensity₁ (⟨3, Flag_3_2_1_1⟩ : FinFlag FlagType_2_1).2
      (turanEdgeFlag r (turanSubseq r hr (k + 1)) hr) : ℝ)
    rw [(turanEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr).1]
    push_cast
    congr 1
    ring
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_1_2⟩⟧ = 1 / r
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_1_2⟩) ?_
    have hlim : Tendsto (fun m : ℕ =>
        ((1 : ℝ) * ((m : ℝ) + 1) + (-1)) / ((r : ℝ) * ((m : ℝ) + 1) + (-2)))
        atTop (𝓝 ((1 : ℝ) / r)) := tendsto_linear_ratio hrpos
    refine (hlim.comp (turan_tail_tendsto r hr)).congr ?_
    intro k
    simp only [Function.comp_apply]
    show _ = (flagDensity₁ (⟨3, Flag_3_2_1_2⟩ : FinFlag FlagType_2_1).2
      (turanEdgeFlag r (turanSubseq r hr (k + 1)) hr) : ℝ)
    rw [(turanEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr).2.1]
    push_cast
    congr 1
    ring
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_1_3⟩⟧ = ((r : ℝ) - 2) / r
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_1_3⟩) ?_
    have hlim : Tendsto (fun m : ℕ =>
        (((r : ℝ) - 2) * ((m : ℝ) + 1) + 0) / ((r : ℝ) * ((m : ℝ) + 1) + (-2)))
        atTop (𝓝 (((r : ℝ) - 2) / r)) := tendsto_linear_ratio hrpos
    refine (hlim.comp (turan_tail_tendsto r hr)).congr ?_
    intro k
    simp only [Function.comp_apply]
    show _ = (flagDensity₁ (⟨3, Flag_3_2_1_3⟩ : FinFlag FlagType_2_1).2
      (turanEdgeFlag r (turanSubseq r hr (k + 1)) hr) : ℝ)
    rw [(turanEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr).2.2.1]
    push_cast
    congr 1
    ring
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_1_0⟩⟧ = 0
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_1_0⟩) ?_
    have hzero : ∀ k, (flagDensity₁ (⟨3, Flag_3_2_1_0⟩ : FinFlag FlagType_2_1).2
        (turanEdgeFlag r (turanSubseq r hr (k + 1)) hr) : ℝ) = 0 := by
      intro k
      rw [(turanEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr).2.2.2]
      norm_num
    refine (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ))).congr ?_
    intro k
    exact (hzero k).symm

/-- `η`: `S_η({φ_Tr})` is a single point with `z_η = 1/r`, `g_η = (r-1)/r`,
`a_η = b_η = 0`. -/
theorem turanLimit_relSσ_nonEdge (r : ℕ) (hr : 2 ≤ r) :
    ∃ χ : PositiveHomSpace FlagType_2_0,
      relSσ {posHomPoint (turanLimit r hr)} FlagType_2_0 = {χ} ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0 = 1 / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 = ((r : ℝ) - 1) / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_1 = 0 ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_2 = 0 := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hσ : (turanLimit r hr) ⟨FlagType_2_0⟩₀ > 0 := by
    show (turanLimit r hr) ⟦basisVector ⟨2, FlagType_2_0.toEmptyTypeFlag⟩⟧ > 0
    rw [eta_toEmptyTypeFlag]
    have hsum := sum_positiveHom_basisVector_flagWithSize_eq_one (turanLimit r hr) 2
      (by omega)
    rw [flagWithSize_two_univ, Finset.sum_pair edge_ne_nonedge] at hsum
    have hedge := turanLimit_edge_basis r hr
    have hlt : ((r : ℝ) - 1) / r < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  obtain ⟨χ, hsingleton, hcoord⟩ := turan_dirac_package r hr hσ
    (fun m hm => turanNonEdgeFlag r m hr hm)
    (fun m hm => (turan_canonical_mem r m hr hm).2.2)
    (fun m => labelExtensions_turan_nonEdge_subsingleton r m hr)
    (fun m hm => (turan_type_density_pos r m hr hm).2.2)
  refine ⟨χ, hsingleton, ?_, ?_, ?_, ?_⟩
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_0_0⟩⟧ = 1 / r
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_0_0⟩) ?_
    have hlim : Tendsto (fun m : ℕ =>
        ((1 : ℝ) * ((m : ℝ) + 1) + (-2)) / ((r : ℝ) * ((m : ℝ) + 1) + (-2)))
        atTop (𝓝 ((1 : ℝ) / r)) := tendsto_linear_ratio hrpos
    refine (hlim.comp (turan_tail_tendsto r hr)).congr ?_
    intro k
    simp only [Function.comp_apply]
    show _ = (flagDensity₁ (⟨3, Flag_3_2_0_0⟩ : FinFlag FlagType_2_0).2
      (turanNonEdgeFlag r (turanSubseq r hr (k + 1)) hr
        (turan_tail_subseq_ge r hr k)) : ℝ)
    rw [(turanNonEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr
      (turan_tail_subseq_ge r hr k)).1]
    push_cast
    congr 1
    ring
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_0_3⟩⟧ = ((r : ℝ) - 1) / r
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_0_3⟩) ?_
    have hlim : Tendsto (fun m : ℕ =>
        (((r : ℝ) - 1) * ((m : ℝ) + 1) + 0) / ((r : ℝ) * ((m : ℝ) + 1) + (-2)))
        atTop (𝓝 (((r : ℝ) - 1) / r)) := tendsto_linear_ratio hrpos
    refine (hlim.comp (turan_tail_tendsto r hr)).congr ?_
    intro k
    simp only [Function.comp_apply]
    show _ = (flagDensity₁ (⟨3, Flag_3_2_0_3⟩ : FinFlag FlagType_2_0).2
      (turanNonEdgeFlag r (turanSubseq r hr (k + 1)) hr
        (turan_tail_subseq_ge r hr k)) : ℝ)
    rw [(turanNonEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr
      (turan_tail_subseq_ge r hr k)).2.1]
    push_cast
    congr 1
    ring
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_0_1⟩⟧ = 0
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_0_1⟩) ?_
    refine (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ))).congr ?_
    intro k
    rw [(turanNonEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr
      (turan_tail_subseq_ge r hr k)).2.2.1]
    norm_num
  · show (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨3, Flag_3_2_0_2⟩⟧ = 0
    rw [PositiveHomSpace.toPosHom_basisVector]
    refine tendsto_nhds_unique (hcoord ⟨3, Flag_3_2_0_2⟩) ?_
    refine (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ))).congr ?_
    intro k
    rw [(turanNonEdgeFlag_densities r (turanSubseq r hr (k + 1)) hr
      (turan_tail_subseq_ge r hr k)).2.2.2]
    norm_num

/-! ## The Turán slice identities under Erdős–Simonovits (`thm:turan-slice`,
`thm:relative-mantel`) -/

section SliceIdentities

variable {r : ℕ} (hr : 2 ≤ r)
  (hES : turanSlice r ⊆ {posHomPoint (turanLimit r hr)})

include hr hES in
/-- **`thm:turan-slice` (i)** under the Erdős–Simonovits uniqueness hypothesis: on
`S_vtype(Y_Tur)`, the rooted edge density is pinned to `(r-1)/r`. -/
theorem turan_slice_identity_vtype :
    ∀ χ ∈ relSσ (turanSlice r) vtype,
      (PositiveHomSpace.toPosHom χ) e = ((r : ℝ) - 1) / r := by
  intro χ hχ
  obtain ⟨χ₀, hsingleton, hval⟩ := turanLimit_relSσ_vtype r hr
  have hmem : χ ∈ relSσ {posHomPoint (turanLimit r hr)} vtype := relSσ_mono hES vtype hχ
  rw [hsingleton, Set.mem_singleton_iff] at hmem
  rw [hmem]
  exact hval

include hr hES in
/-- **`thm:turan-slice` (ii)** under Erdős–Simonovits: the `τ`-identities on `S_τ(Y_Tur)`. -/
theorem turan_slice_identity_edge :
    ∀ χ ∈ relSσ (turanSlice r) FlagType_2_1,
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1 = 1 / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2 = 1 / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 = ((r : ℝ) - 2) / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_0 = 0 := by
  intro χ hχ
  obtain ⟨χ₀, hsingleton, hval⟩ := turanLimit_relSσ_edge r hr
  have hmem : χ ∈ relSσ {posHomPoint (turanLimit r hr)} FlagType_2_1 :=
    relSσ_mono hES FlagType_2_1 hχ
  rw [hsingleton, Set.mem_singleton_iff] at hmem
  rw [hmem]
  exact hval

include hr hES in
/-- **`thm:turan-slice` (iii)** under Erdős–Simonovits: the `η`-identities on
`S_η(Y_Tur)`. -/
theorem turan_slice_identity_nonEdge :
    ∀ χ ∈ relSσ (turanSlice r) FlagType_2_0,
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0 = 1 / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 = ((r : ℝ) - 1) / r ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_1 = 0 ∧
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_2 = 0 := by
  intro χ hχ
  obtain ⟨χ₀, hsingleton, hval⟩ := turanLimit_relSσ_nonEdge r hr
  have hmem : χ ∈ relSσ {posHomPoint (turanLimit r hr)} FlagType_2_0 :=
    relSσ_mono hES FlagType_2_0 hχ
  rw [hsingleton, Set.mem_singleton_iff] at hmem
  rw [hmem]
  exact hval

end SliceIdentities

/-- **`thm:relative-mantel` (i)** under Erdős–Simonovits at `r = 2`: the Mantel-slice
support pins the rooted edge density to `1/2` — exactly `MantelNotPlantable`'s `hpin`. -/
theorem relative_mantel_vtype
    (hES : mantelSlice ⊆ {posHomPoint (turanLimit 2 (le_refl 2))}) :
    ∀ χ ∈ relSσ mantelSlice vtype, (PositiveHomSpace.toPosHom χ) e = 1 / 2 := by
  intro χ hχ
  have h := turan_slice_identity_vtype (le_refl 2) hES χ hχ
  rw [h]
  norm_num

/-- **`prop:mantel-not-plantable`, pinning discharged**: under Erdős–Simonovits uniqueness
of the Mantel-extremal limit, the strict inclusion holds with no further input. -/
theorem mantel_not_relatively_plantable_of_uniqueness
    (hES : mantelSlice ⊆ {posHomPoint (turanLimit 2 (le_refl 2))}) :
    relSσ mantelSlice vtype
      ⊂ relQσ (cliqueFreeClass 3).toHeredClass mantelSlice vtype :=
  mantel_not_relatively_plantable (relative_mantel_vtype hES)

/-- **`cor:parametric-p4-turan-recovery`, "consequently" clauses**: under the Zykov
hypotheses with the balanced `r`-partite limit as the recovered point, the relative
supports of the parametric `P₄` slice satisfy the explicit labelled identities.
(Tier-2 axioms: inherits the certificate provenance through `parametric_recovery`.) -/
theorem parametric_recovery_identities {r : ℕ} (hr3 : 3 ≤ r)
    (hZykov : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 ≤ ((r : ℝ) ^ 3 - 6 * r ^ 2 + 11 * r - 6) / (r : ℝ) ^ 3)
    (hZykEq : ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ (krFreeForb0 r) →
      φ₀ FlagAlgebra_4_0_0_10 = ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 →
      posHomPoint φ₀ = posHomPoint (turanLimit r (by omega))) :
    (∀ χ ∈ relSσ (parametricP4Slice r) vtype,
        (PositiveHomSpace.toPosHom χ) e = ((r : ℝ) - 1) / r) ∧
    (∀ χ ∈ relSσ (parametricP4Slice r) FlagType_2_1,
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1 = 1 / r ∧
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2 = 1 / r ∧
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 = ((r : ℝ) - 2) / r ∧
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_0 = 0) ∧
    (∀ χ ∈ relSσ (parametricP4Slice r) FlagType_2_0,
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0 = 1 / r ∧
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 = ((r : ℝ) - 1) / r ∧
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_1 = 0 ∧
        (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_2 = 0) := by
  have hr2 : 2 ≤ r := by omega
  have hsub : parametricP4Slice r ⊆ {posHomPoint (turanLimit r hr2)} :=
    parametric_recovery hr3 hZykov hZykEq
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨χ₀, hsingleton, hval⟩ := turanLimit_relSσ_vtype r hr2
    have hmem : χ ∈ relSσ {posHomPoint (turanLimit r hr2)} vtype :=
      relSσ_mono hsub vtype hχ
    rw [hsingleton, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hval
  · intro χ hχ
    obtain ⟨χ₀, hsingleton, hval⟩ := turanLimit_relSσ_edge r hr2
    have hmem : χ ∈ relSσ {posHomPoint (turanLimit r hr2)} FlagType_2_1 :=
      relSσ_mono hsub FlagType_2_1 hχ
    rw [hsingleton, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hval
  · intro χ hχ
    obtain ⟨χ₀, hsingleton, hval⟩ := turanLimit_relSσ_nonEdge r hr2
    have hmem : χ ∈ relSσ {posHomPoint (turanLimit r hr2)} FlagType_2_0 :=
      relSσ_mono hsub FlagType_2_0 hχ
    rw [hsingleton, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hval

end FlagAlgebras.MetaTheory
