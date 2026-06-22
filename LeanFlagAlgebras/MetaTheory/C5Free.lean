import LeanFlagAlgebras.MetaTheory.HeredClass
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # The `C₅`-free hereditary class and the neighbourhood structure lemma (paper §8)

The `C₅`-free graphs are the first natural test of root-plantability beyond the global blow-up
closure theorem: they are dense and *not* blow-up-closed (a naive blow-up creates 5-cycles), so the
clone-based theorems do not apply.  The repair is local, and the finite-planting criterion of
[`SparseRootRepair`](./SparseRootRepair.lean) does.

Here `C₅`-free means containing no `C₅` as a *(not necessarily induced)* subgraph — Mathlib's
`SimpleGraph.Free`/`IsContained` (`⊑`).  This file provides:

* `c5FreeClass` — the `C₅`-free class as a [`HeredClass`](./HeredClass.lean) (heredity is just that a
  copy of `C₅` in an induced subgraph lifts to a copy in the host).
* `lem:c5-nbhd` (`c5free_neighborhood_edge_card_le`) — the strong local constraint: in a `C₅`-free
  graph the induced subgraph on any neighbourhood `G[N(v)]` is `P₄`-subgraph-free, hence each
  component is a star or a triangle, hence it has at most as many edges as vertices,
  `e(G[N(v)]) ≤ |N(v)|`.  This is what makes the deleted neighbourhood-edge set sparse in the
  `C₅`-free planting constructions.
-/

open FlagAlgebras SimpleGraph

open scoped Finset

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-- The 5-cycle `C₅`, as Mathlib's `cycleGraph 5` on `Fin 5`. -/
abbrev C5g : SimpleGraph (Fin 5) := cycleGraph 5

/-- **The `C₅`-free hereditary class.**  A graph is in the class iff it contains no copy of `C₅`
(not necessarily induced).  Heredity: a copy of `C₅` in an induced subgraph `H ↪g G` composes to a
copy in `G`, so `C₅`-freeness of `G` passes to `H`. -/
def c5FreeClass : HeredClass where
  Mem {_V} _ _ G := C5g.Free G
  comap {_V _W} _ _ _ _ {_G} {_H} e hG := fun hc5 => hG (hc5.trans ⟨e.toCopy⟩)

/-! ## The neighbourhood structure lemma (`lem:c5-nbhd`) -/

/-- A combinatorial `P₄`: four distinct vertices forming a path `a - x - y - b`
(three consecutive edges).  A graph is "`P₄`-subgraph-free" exactly when no such configuration
exists. -/
private def HasP4 {W : Type} (H : SimpleGraph W) : Prop :=
  ∃ a x y b : W, a ≠ x ∧ a ≠ y ∧ a ≠ b ∧ x ≠ y ∧ x ≠ b ∧ y ≠ b ∧
    H.Adj a x ∧ H.Adj x y ∧ H.Adj y b

/-- **Bridge.**  If `H` has no `P₄`, then every path in `H` has length at most `2`: a path of
length `3` would expose four distinct vertices with three consecutive edges, i.e. a `P₄`. -/
private lemma no_long_path {W : Type} (H : SimpleGraph W) (hH : ¬ HasP4 H)
    {a b : W} (p : H.Walk a b) (hp : p.IsPath) : p.length ≤ 2 := by
  by_contra hlen
  push_neg at hlen
  match p, hp, hlen with
  | .cons (u := a) (v := x) hax (.cons (v := y) hxy (.cons (v := b') hyb q)), hp, _ =>
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨hp2, ha_notin⟩ := hp
    rw [Walk.cons_isPath_iff] at hp2
    obtain ⟨hp3, hx_notin⟩ := hp2
    rw [Walk.cons_isPath_iff] at hp3
    obtain ⟨_, hy_notin⟩ := hp3
    have hax' : a ≠ x := hax.ne
    have hxy' : x ≠ y := hxy.ne
    have hyb' : y ≠ b' := hyb.ne
    simp only [Walk.support_cons, List.mem_cons] at ha_notin hx_notin
    push_neg at ha_notin hx_notin
    have hay' : a ≠ y := ha_notin.2.1
    have hab' : a ≠ b' := fun h => ha_notin.2.2 (h ▸ Walk.start_mem_support q)
    have hxb' : x ≠ b' := fun h => hx_notin.2 (h ▸ Walk.start_mem_support q)
    exact hH ⟨a, x, y, b', hax', hay', hab', hxy', hxb', hyb', hax, hxy, hyb⟩

/-- `P₄`-freeness is inherited by induced subgraphs. -/
private lemma not_hasP4_induce {W : Type} (H : SimpleGraph W) (hH : ¬ HasP4 H) (s : Set W) :
    ¬ HasP4 (H.induce s) := by
  rintro ⟨a, x, y, b, hax, hay, hab, hxy, hxb, hyb, e1, e2, e3⟩
  rw [induce_adj] at e1 e2 e3
  exact hH ⟨a, x, y, b,
    fun h => hax (Subtype.ext h), fun h => hay (Subtype.ext h), fun h => hab (Subtype.ext h),
    fun h => hxy (Subtype.ext h), fun h => hxb (Subtype.ext h), fun h => hyb (Subtype.ext h),
    e1, e2, e3⟩

/-- **The connected case.**  A connected `P₄`-free graph has at most as many edges as vertices: if
acyclic it is a tree (`#edges = #vertices - 1`); otherwise its shortest cycle is a triangle and the
whole graph has at most three vertices. -/
private lemma connected_p4free_edge_le_vert {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : ¬ HasP4 H) (hc : H.Connected) :
    H.edgeFinset.card ≤ Fintype.card W := by
  by_cases hac : H.IsAcyclic
  · -- tree case
    have htree : H.IsTree := ⟨hc, hac⟩
    have := htree.card_edgeFinset
    omega
  · -- cyclic case: girth = 3, so there's a triangle; whole graph has ≤ 3 vertices.
    obtain ⟨v, w, hcyc, hlen⟩ := (exists_girth_eq_length (G := H)).mpr hac
    have h3 : 3 ≤ H.girth := three_le_girth hac
    rw [hlen] at h3
    have hlen3 : w.length = 3 := by
      match w, hcyc, h3 with
      | .cons (v := x) hvx p, hcyc, h3 =>
        rw [Walk.cons_isCycle_iff] at hcyc
        obtain ⟨hpath, _⟩ := hcyc
        have := no_long_path H hH p hpath
        rw [Walk.length_cons] at h3 ⊢
        omega
    match w, hcyc, hlen3 with
    | .cons (u := vv) (v := x) hvx (.cons (v := y) hxy (.cons hyv Walk.nil)), hcyc, _ =>
      rw [Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff] at hcyc
      obtain ⟨⟨⟨_, hy_notin⟩, hx_notin⟩, _⟩ := hcyc
      have hvx_ne : vv ≠ x := hvx.ne
      have hxy_ne : x ≠ y := hxy.ne
      have hvy_ne : vv ≠ y := by
        simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil] at hy_notin
        push_neg at hy_notin
        exact fun h => hy_notin.1 h.symm
      have eVX : H.Adj vv x := hvx
      have eXY : H.Adj x y := hxy
      have eYV : H.Adj y vv := hyv
      have hmem : ∀ u : W, u = vv ∨ u = x ∨ u = y := by
        intro u
        by_contra hu
        push_neg at hu
        obtain ⟨hu1, hu2, hu3⟩ := hu
        obtain ⟨P, hP⟩ := (hc vv u).exists_isPath
        have hPlen := no_long_path H hH P hP
        match P, hP, hPlen with
        | .nil, _, _ =>
          exact hu1 rfl
        | .cons hvu Walk.nil, _, _ =>
          have eUV : H.Adj u vv := hvu.symm
          exact hH ⟨u, vv, x, y, hu1, hu2, hu3, hvx_ne, hvy_ne, hxy_ne, eUV, eVX, eXY⟩
        | .cons (v := m) hvm (.cons hmu Walk.nil), hP, _ =>
          have hvm_ne : vv ≠ m := hvm.ne
          have hmu_ne : m ≠ u := hmu.ne
          have eVM : H.Adj vv m := hvm
          have eMU : H.Adj m u := hmu
          by_cases hmx : m = x
          · subst hmx
            exact hH ⟨u, m, vv, y, fun h => hmu_ne h.symm, hu1, hu3,
              fun h => hvm_ne h.symm, hxy_ne, hvy_ne, eMU.symm, eVM.symm, eYV.symm⟩
          · by_cases hmy : m = y
            · subst hmy
              exact hH ⟨u, m, vv, x, fun h => hmu_ne h.symm, hu1, hu2,
                fun h => hvm_ne h.symm, hxy_ne.symm, hvx_ne, eMU.symm, eVM.symm, eVX⟩
            · exact hH ⟨u, m, vv, x, fun h => hmu_ne h.symm, hu1, hu2,
                fun h => hvm_ne h.symm, hmx, hvx_ne, eMU.symm, eVM.symm, eVX⟩
      have hcard : Fintype.card W ≤ 3 := by
        have hsub : (Finset.univ : Finset W) ⊆ {vv, x, y} := by
          intro u _
          rcases hmem u with h | h | h <;> simp [h]
        calc Fintype.card W = (Finset.univ : Finset W).card := (Finset.card_univ).symm
          _ ≤ ({vv, x, y} : Finset W).card := Finset.card_le_card hsub
          _ ≤ 3 := by
            apply le_trans (Finset.card_insert_le _ _)
            apply Nat.succ_le_succ
            apply le_trans (Finset.card_insert_le _ _)
            simp
      have hchoose := H.card_edgeFinset_le_card_choose_two
      have hcw : (Fintype.card W).choose 2 ≤ Fintype.card W := by
        have hc3 : Fintype.card W ≤ 3 := hcard
        revert hc3
        generalize Fintype.card W = n
        intro hc3
        match n, hc3 with
        | 0, _ => decide
        | 1, _ => decide
        | 2, _ => decide
        | 3, _ => decide
      omega

/-- A walk that stays inside `s` lifts to a reachability in the induced subgraph `H[s]`. -/
private lemma reachable_induce_of_walk {W : Type} (H : SimpleGraph W) (s : Set W) :
    ∀ {a b : W} (p : H.Walk a b), (∀ u ∈ p.support, u ∈ s) →
      ∀ (ha : a ∈ s) (hb : b ∈ s),
      (H.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b p
  induction p with
  | nil =>
    intro _ ha hb
    exact Reachable.refl _
  | @cons a c b hadj q ih =>
    intro hsup ha hb
    have hc : c ∈ s := hsup c (by simp [Walk.support_cons])
    have hstep : (H.induce s).Adj ⟨a, ha⟩ ⟨c, hc⟩ := by
      rw [induce_adj]; exact hadj
    have hrest : (H.induce s).Reachable ⟨c, hc⟩ ⟨b, hb⟩ := by
      apply ih
      intro u hu
      exact hsup u (by simp [Walk.support_cons]; right; exact hu)
    exact (Adj.reachable hstep).trans hrest

/-- The edge count of an induced subgraph on the coercion of a `Finset` `t` equals the number of
edges of `H` with both endpoints in `t`. -/
private lemma card_edgeFinset_induce_coe {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (t : Finset W) :
    #(H.induce (↑t : Set W)).edgeFinset = #(H.edgeFinset.filter (· ∈ t.sym2)) := by
  have hmap := map_edgeFinset_induce (G := H) (s := (↑t : Set W))
  have hc := congrArg Finset.card hmap
  rw [Finset.card_map, Finset.toFinset_coe] at hc
  rw [Finset.filter_mem_eq_inter]
  convert hc using 3

/-- **Step B — counting.**  A finite `P₄`-subgraph-free graph has at most as many edges as
vertices.  Every connected component is a tree (hence `#edges = #vertices - 1`) or a single
triangle (`#edges = #vertices = 3`); summing gives `#edges ≤ #vertices`. -/
private lemma p4free_edge_le_vert {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : ¬ HasP4 H) :
    H.edgeFinset.card ≤ Fintype.card W := by
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  subst hn
  rcases isEmpty_or_nonempty W with hW | hW
  · have : Fintype.card W = 0 := Fintype.card_eq_zero
    have hempty : H.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e with
      | h a b => exact (hW.elim a)
    rw [hempty, Finset.card_empty]
    omega
  · obtain ⟨v₀⟩ := hW
    set T : Finset W := Finset.univ.filter (fun w => H.Reachable v₀ w) with hT
    have hmemT : ∀ w : W, w ∈ T ↔ H.Reachable v₀ w := by
      intro w; rw [hT]; simp
    have hv0T : v₀ ∈ T := (hmemT v₀).mpr (Reachable.refl v₀)
    have hclosed : ∀ a b : W, H.Adj a b → (a ∈ T ↔ b ∈ T) := by
      intro a b hab
      rw [hmemT, hmemT]
      constructor
      · intro ha; exact ha.trans hab.reachable
      · intro hb; exact hb.trans hab.symm.reachable
    have hSconn : (H.induce (↑T : Set W)).Connected := by
      rw [connected_iff_exists_forall_reachable]
      have hv0S : v₀ ∈ (↑T : Set W) := hv0T
      refine ⟨⟨v₀, hv0S⟩, ?_⟩
      rintro ⟨w, hw⟩
      have hwR : H.Reachable v₀ w := (hmemT w).mp hw
      obtain ⟨p, hp⟩ := hwR.exists_isPath
      have hsub : ∀ u ∈ p.support, u ∈ (↑T : Set W) := by
        intro u hu
        show u ∈ T
        rw [hmemT]
        exact ⟨p.takeUntil u hu⟩
      exact reachable_induce_of_walk H (↑T : Set W) p hsub hv0S hw
    have hSfree : ¬ HasP4 (H.induce (↑T : Set W)) := not_hasP4_induce H hH _
    have hScfree : ¬ HasP4 (H.induce (↑(Tᶜ) : Set W)) := not_hasP4_induce H hH _
    have hsplit : H.edgeFinset.card
        = #(H.induce (↑T : Set W)).edgeFinset + #(H.induce (↑(Tᶜ) : Set W)).edgeFinset := by
      have hfeq : H.edgeFinset.filter (· ∈ Tᶜ.sym2)
          = H.edgeFinset.filter (fun a => ¬ (a ∈ T.sym2)) := by
        apply Finset.filter_congr
        intro e he
        induction e with
        | h a b =>
          rw [mem_edgeFinset, mem_edgeSet] at he
          simp only [Finset.mk_mem_sym2_iff, Finset.mem_compl]
          have := hclosed a b he
          tauto
      rw [card_edgeFinset_induce_coe, card_edgeFinset_induce_coe, hfeq,
        Finset.card_filter_add_card_filter_not (s := H.edgeFinset) (· ∈ T.sym2)]
    have hcardT : Fintype.card (↑T : Set W) = T.card := by
      rw [← Set.toFinset_card]
      simp [Finset.toFinset_coe]
    have hcardTc : Fintype.card (↑(Tᶜ) : Set W) = Tᶜ.card := by
      rw [← Set.toFinset_card]
      simp [Finset.toFinset_coe]
    have hcardsplit : Fintype.card W = T.card + Tᶜ.card := by
      rw [Finset.card_add_card_compl]
    have hSbound : #(H.induce (↑T : Set W)).edgeFinset ≤ Fintype.card (↑T : Set W) :=
      connected_p4free_edge_le_vert (H.induce (↑T : Set W)) hSfree hSconn
    have hScard_lt : Fintype.card (↑(Tᶜ) : Set W) < Fintype.card W := by
      have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨v₀, hv0T⟩
      rw [hcardTc, hcardsplit]
      omega
    have hScbound : #(H.induce (↑(Tᶜ) : Set W)).edgeFinset ≤ Fintype.card (↑(Tᶜ) : Set W) :=
      ih (Fintype.card (↑(Tᶜ) : Set W)) hScard_lt (H.induce (↑(Tᶜ) : Set W)) hScfree rfl
    rw [hcardT] at hSbound
    rw [hsplit, hcardsplit, hcardT, hcardTc] at *
    omega

/-- **Pentagon ⟹ `C₅` copy.**  Five vertices of `G` with the five consecutive edges of a `5`-cycle,
all `10` pairwise distinct, give a copy of `C₅` in `G`.  (Reused by the `C₅`-free planting
constructions to reconstruct a `5`-cycle in the base graph.) -/
lemma c5_copy_of_pentagon {V : Type} (G : SimpleGraph V) (w₀ w₁ w₂ w₃ w₄ : V)
    (e₀₁ : G.Adj w₀ w₁) (e₁₂ : G.Adj w₁ w₂) (e₂₃ : G.Adj w₂ w₃)
    (e₃₄ : G.Adj w₃ w₄) (e₄₀ : G.Adj w₄ w₀)
    (h₀₁ : w₀ ≠ w₁) (h₀₂ : w₀ ≠ w₂) (h₀₃ : w₀ ≠ w₃) (h₀₄ : w₀ ≠ w₄)
    (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃) (h₁₄ : w₁ ≠ w₄)
    (h₂₃ : w₂ ≠ w₃) (h₂₄ : w₂ ≠ w₄) (h₃₄ : w₃ ≠ w₄) :
    C5g ⊑ G := by
  refine ⟨Hom.toCopy ⟨![w₀, w₁, w₂, w₃, w₄], ?_⟩ ?_⟩
  · -- `map_rel'`: the only adjacent index pairs in `C₅` are the five consecutive ones.
    intro i j hij
    rw [C5g, cycleGraph_adj] at hij
    fin_cases i <;> fin_cases j <;>
      first
      | (exfalso; revert hij; decide)
      | exact e₀₁ | exact e₀₁.symm
      | exact e₁₂ | exact e₁₂.symm
      | exact e₂₃ | exact e₂₃.symm
      | exact e₃₄ | exact e₃₄.symm
      | exact e₄₀ | exact e₄₀.symm
  · -- Injectivity from the ten pairwise-distinctness facts.
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij h₀₁ | exact absurd hij.symm h₀₁
      | exact absurd hij h₀₂ | exact absurd hij.symm h₀₂
      | exact absurd hij h₀₃ | exact absurd hij.symm h₀₃
      | exact absurd hij h₀₄ | exact absurd hij.symm h₀₄
      | exact absurd hij h₁₂ | exact absurd hij.symm h₁₂
      | exact absurd hij h₁₃ | exact absurd hij.symm h₁₃
      | exact absurd hij h₁₄ | exact absurd hij.symm h₁₄
      | exact absurd hij h₂₃ | exact absurd hij.symm h₂₃
      | exact absurd hij h₂₄ | exact absurd hij.symm h₂₄
      | exact absurd hij h₃₄ | exact absurd hij.symm h₃₄

/-- **Step A — a `P₄` in a neighbourhood gives a `C₅`.**  If `G[N(v)]` has a `P₄`, then `G` has a
`C₅` (extend by `v`).  Contrapositive: `C₅`-free implies `G[N(v)]` is `P₄`-free. -/
private lemma c5free_nbhd_p4free {V : Type} (G : SimpleGraph V) (hG : C5g.Free G) (v : V) :
    ¬ HasP4 (G.induce (G.neighborSet v)) := by
  rintro ⟨a, x, y, b, hax', hay', hab', hxy', hxb', hyb', hAax, hAxy, hAyb⟩
  -- Endpoints lie in `N(v)`: they are neighbours of `v`, and the induced edges are `G`-edges.
  have eva : G.Adj v (a : V) := a.2
  have evb : G.Adj v (b : V) := b.2
  have eax : G.Adj (a : V) (x : V) := hAax
  have exy : G.Adj (x : V) (y : V) := hAxy
  have eyb : G.Adj (y : V) (b : V) := hAyb
  -- `v ∉ N(v)`, so `v` differs from `a, x, y, b`.
  have hvne : ∀ w : G.neighborSet v, v ≠ (w : V) := by
    intro w h
    have hw : G.Adj v (w : V) := w.2
    rw [← h] at hw
    exact (G.loopless v) hw
  -- Distinctness of `a, x, y, b` in `V` from the subtype inequalities.
  have dax : (a : V) ≠ (x : V) := fun h => hax' (Subtype.ext h)
  have day : (a : V) ≠ (y : V) := fun h => hay' (Subtype.ext h)
  have dab : (a : V) ≠ (b : V) := fun h => hab' (Subtype.ext h)
  have dxy : (x : V) ≠ (y : V) := fun h => hxy' (Subtype.ext h)
  have dxb : (x : V) ≠ (b : V) := fun h => hxb' (Subtype.ext h)
  have dyb : (y : V) ≠ (b : V) := fun h => hyb' (Subtype.ext h)
  -- The pentagon `v - a - x - y - b - v`.
  exact hG (c5_copy_of_pentagon G v a x y b eva eax exy eyb evb.symm
    (hvne a) (hvne x) (hvne y) (hvne b) dax day dab dxy dxb dyb)

/-- **Neighbourhoods in `C₅`-free graphs** (`lem:c5-nbhd`).  If `G` is `C₅`-free, then the induced
subgraph on any neighbourhood `G[N(v)]` has at most as many edges as vertices:
`e(G[N(v)]) ≤ |N(v)|`.  (Via: `G[N(v)]` contains no path on four vertices, so every connected
component is a star or a triangle, each with `#edges ≤ #vertices`.) -/
theorem c5free_neighborhood_edge_card_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : C5g.Free G) (v : V) :
    (G.induce (G.neighborSet v)).edgeFinset.card ≤ Fintype.card (G.neighborSet v) :=
  p4free_edge_le_vert _ (c5free_nbhd_p4free G hG v)

end FlagAlgebras.MetaTheory
