module

public import LeanFlagAlgebras.FlagAlgebra.Compute.IsoInvariants
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.FinRange
public import Init.Data.List.Find

@[expose] public section

/-! # Fast graph-isomorphism checking for flags

Computable, decidable isomorphism tests for `Sym2Graph`/`Sym2LabeledGraph`
representations of flags, used by the Flags loader macros at elaboration time
to canonicalize and deduplicate flags.

The core idea: search over vertex permutations (respecting the type embedding
for labeled graphs) and check edge-set agreement, then prove the resulting
`Bool` test sound and complete against the semantic flag equivalence `∼sf`.
These proofs feed the high-priority `Decidable`/`DecidableEq`/`Fintype`
instances that make flag enumeration tractable. -/

namespace FlagAlgebras.Compute

/-- The list of all potential (non-loop) edges on `Fin n`, one `Sym2` per
unordered pair `i < j`; used to range over candidate edges during iso checks. -/
def allEdges (n : Nat) : List (Sym2 (Fin n)) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if i.val < j.val then some (Sym2.mk (i, j)) else none

/-- Helper to map an edge under a permutation array (List of size n) -/
def applyPermEdge {n : Nat} (perm : List (Fin n)) (e : Sym2 (Fin n)) : Sym2 (Fin n) :=
  Sym2.map (fun v => (perm[v.val]?).getD v) e

/-- Computable first-occurrence lookup: returns `some (i + offset)` for the
position of `a` in the list (counting from the given starting `offset`). -/
def myIndexOf {α : Type} [BEq α] (a : α) : List α → Nat → Option Nat
  | [], _ => none
  | x::xs, i => if x == a then some i else myIndexOf a xs (i+1)

lemma myIndexOf_some_of_mem_from
    {n : Nat} (a : Fin n) :
    (l : List (Fin n)) → (i : Nat) → a ∈ l → ∃ idx, myIndexOf a l i = some idx
  | [], _, h => by cases h
  | x :: xs, i, hmem => by
      by_cases hxa : x = a
      · refine ⟨i, ?_⟩
        simp [myIndexOf, hxa]
      · have hmem_xs : a ∈ xs := by
          have hm : a = x ∨ a ∈ xs := List.mem_cons.mp hmem
          cases hm with
          | inl hx =>
              exfalso
              exact hxa hx.symm
          | inr hx =>
              exact hx
        rcases myIndexOf_some_of_mem_from a xs (i + 1) hmem_xs with ⟨idx, hidx⟩
        refine ⟨idx, ?_⟩
        simp [myIndexOf, hxa, hidx]

lemma myIndexOf_ne_none_of_mem
    {n : Nat} (a : Fin n) (l : List (Fin n)) (i : Nat) (hmem : a ∈ l) :
    myIndexOf a l i ≠ none := by
  rcases myIndexOf_some_of_mem_from a l i hmem with ⟨idx, hidx⟩
  intro hnone
  rw [hnone] at hidx
  cases hidx

lemma myIndexOf_eq_some_implies_mem
    {n : Nat} (a : Fin n) :
    (l : List (Fin n)) → (i idx : Nat) → myIndexOf a l i = some idx → a ∈ l
  | [], _, _, h => by
      simp [myIndexOf] at h
  | x :: xs, i, idx, h => by
      by_cases hxa : x = a
      · simp [hxa]
      · simp [myIndexOf, hxa] at h
        exact List.mem_cons_of_mem _ (myIndexOf_eq_some_implies_mem a xs (i + 1) idx h)

lemma myIndexOf_eq_some_implies_lt_from
    {n : Nat} (a : Fin n) :
    (l : List (Fin n)) → (i idx : Nat) → myIndexOf a l i = some idx → idx < i + l.length
  | [], _, _, h => by
      simp [myIndexOf] at h
  | x :: xs, i, idx, h => by
      by_cases hxa : x == a
      · simp [myIndexOf, hxa] at h
        cases h
        simp
      · simp [myIndexOf, hxa] at h
        have hlt := myIndexOf_eq_some_implies_lt_from a xs (i + 1) idx h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt

lemma myIndexOf_eq_some_implies_lt_length
    {n : Nat} (a : Fin n) (l : List (Fin n)) (idx : Nat)
    (hidx : myIndexOf a l 0 = some idx) :
    idx < l.length := by
  simpa using myIndexOf_eq_some_implies_lt_from a l 0 idx hidx

lemma myIndexOf_eq_some_implies_ge_from
    {n : Nat} (a : Fin n) :
    (l : List (Fin n)) → (i idx : Nat) → myIndexOf a l i = some idx → i ≤ idx
  | [], _, _, h => by
      simp [myIndexOf] at h
  | x :: xs, i, idx, h => by
      by_cases hxa : x == a
      · simp [myIndexOf, hxa] at h
        cases h
        exact Nat.le_refl i
      · simp [myIndexOf, hxa] at h
        have hge : i + 1 ≤ idx := myIndexOf_eq_some_implies_ge_from a xs (i + 1) idx h
        exact Nat.le_trans (Nat.le_succ i) hge

lemma myIndexOf_eq_some_same_index_implies_eq_from
    {n : Nat} (l : List (Fin n)) (i idx : Nat) {a b : Fin n}
    (hnodup : l.Nodup)
    (ha : myIndexOf a l i = some idx)
    (hb : myIndexOf b l i = some idx) :
    a = b := by
  induction l generalizing i idx a b with
  | nil =>
      simp [myIndexOf] at ha
  | cons x xs ih =>
      cases hnodup with
      | @cons _ _ hx_notmem hxs_nodup =>
          by_cases hxa : x == a
          · by_cases hxb : x == b
            · simp [myIndexOf, hxa, hxb] at ha hb
              cases ha
              cases hb
              have hxa' : x = a := by simpa [beq_iff_eq] using hxa
              have hxb' : x = b := by simpa [beq_iff_eq] using hxb
              exact hxa'.symm.trans hxb'
            · simp [myIndexOf, hxa, hxb] at ha hb
              cases ha
              have hge : i + 1 ≤ i := myIndexOf_eq_some_implies_ge_from b xs (i + 1) i hb
              exact False.elim ((Nat.not_succ_le_self i) hge)
          · by_cases hxb : x == b
            · simp [myIndexOf, hxa, hxb] at ha hb
              cases hb
              have hge : i + 1 ≤ i := myIndexOf_eq_some_implies_ge_from a xs (i + 1) i ha
              exact False.elim ((Nat.not_succ_le_self i) hge)
            · simp [myIndexOf, hxa, hxb] at ha hb
              exact ih (i := i + 1) (idx := idx) (a := a) (b := b) hxs_nodup ha hb

lemma myIndexOf_eq_some_same_index_implies_eq
    {n : Nat} (l : List (Fin n)) (idx : Nat) {a b : Fin n}
    (hnodup : l.Nodup)
    (ha : myIndexOf a l 0 = some idx)
    (hb : myIndexOf b l 0 = some idx) :
    a = b :=
  myIndexOf_eq_some_same_index_implies_eq_from l 0 idx hnodup ha hb
lemma myIndexOf_get?_gen {n : Nat} (a : Fin n) (l : List (Fin n)) (i idx : Nat)
    (h : myIndexOf a l i = some idx) :
    i ≤ idx ∧ l[idx - i]? = some a := by
  induction l generalizing i with
  | nil =>
    cases h
  | cons x xs ih =>
    unfold myIndexOf at h
    split at h
    · next heq =>
      simp only [Option.some.injEq] at h
      subst h
      have hxa : x = a := by simpa [beq_iff_eq] using heq
      exact ⟨Nat.le_refl _, by simp [hxa]⟩
    · next hneq =>
      have ⟨hle, hget⟩ := ih (i + 1) h
      refine ⟨Nat.le_trans (Nat.le_succ _) hle, ?_⟩
      have hsub : idx - i = idx - (i + 1) + 1 := by omega
      rw [hsub]
      exact hget

lemma myIndexOf_get_zero {n : Nat} (a : Fin n) (l : List (Fin n)) (idx : Nat)
    (h : myIndexOf a l 0 = some idx) :
    l[idx]? = some a := by
  have ⟨_, hget⟩ := myIndexOf_get?_gen a l 0 idx h
  rwa [Nat.sub_zero] at hget

/-- Assembles a full vertex map on `Fin n` from a chosen permutation `p2` of
the non-type vertices: type vertices are sent via `embed2 ∘ embed1⁻¹`
(preserving the type σ), while remaining vertices follow `p2`. -/
def buildFullMap (n k : Nat) (embed1 embed2 : Fin k → Fin n)
    (nonType1 p2 : List (Fin n)) : List (Fin n) :=
  (List.finRange n).map fun v =>
    let typeHit := (List.finRange k).find? fun i => v.val == (embed1 i).val
    match typeHit with
    | some i => embed2 i
    | none =>
      match myIndexOf v nonType1 0 with
      | some idx => (p2[idx]?).getD v
      | none => v

/-- The vertices of `Fin n` not in the image of the type embedding `embed`;
these are the vertices a flag isomorphism is free to permute. -/
def getNonTypeVerts (n k : Nat) (embed : Fin k → Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v =>
    (List.finRange k).all fun i => v.val != (embed i).val

lemma mem_getNonTypeVerts_of_find_eq_none
    {n k : Nat} (embed : Fin k → Fin n) (v : Fin n)
    (hfind : List.find? (fun i => v.val == (embed i).val) (List.finRange k) = none) :
    v ∈ getNonTypeVerts n k embed := by
  dsimp [getNonTypeVerts]
  refine List.mem_filter.mpr ?_
  constructor
  · simp only [List.mem_finRange]
  · rw [List.all_eq_true]
    intro i hi
    have hnone := (List.find?_eq_none.mp hfind) i hi
    simpa [beq_iff_eq] using hnone

lemma getNonTypeVerts_nodup {n k : Nat} (embed : Fin k → Fin n) :
    (getNonTypeVerts n k embed).Nodup := by
  simpa [getNonTypeVerts] using (List.nodup_finRange n).filter
    (fun v : Fin n => (List.finRange k).all fun i => v.val != (embed i).val)

lemma mem_getNonTypeVerts_iff_vals
    {n k : Nat} (embed : Fin k → Fin n) (v : Fin n) :
    v ∈ getNonTypeVerts n k embed ↔ ∀ i : Fin k, v.val ≠ (embed i).val := by
  constructor
  · intro hv i hEq
    have hall : ((List.finRange k).all fun j => v.val != (embed j).val) = true :=
      (List.mem_filter.mp hv).2
    have hi : (v.val != (embed i).val) = true :=
      (List.all_eq_true.mp hall) i (by simp)
    simp [hEq] at hi
  · intro hv
    refine List.mem_filter.mpr ?_
    constructor
    · simp [List.mem_finRange]
    · refine List.all_eq_true.mpr ?_
      intro i hi
      by_cases hEq : v.val = (embed i).val
      · exact False.elim (hv i hEq)
      · simp [hEq]

lemma getNonTypeVerts_length
    {n k : Nat} (embed : Fin k → Fin n) (hinj : Function.Injective embed) :
    (getNonTypeVerts n k embed).length = n - k := by
  have hnod : (getNonTypeVerts n k embed).Nodup := getNonTypeVerts_nodup embed
  rw [← List.toFinset_card_of_nodup hnod]
  have hset :
      (getNonTypeVerts n k embed).toFinset
        = (Finset.univ \ Finset.image embed (Finset.univ : Finset (Fin k))) := by
    ext v
    constructor
    · intro hv
      refine Finset.mem_sdiff.mpr ?_
      constructor
      · simp
      · intro himg
        rcases Finset.mem_image.mp himg with ⟨i, _, hi⟩
        have hvals := (mem_getNonTypeVerts_iff_vals embed v).1 (List.mem_toFinset.mp hv)
        exact hvals i (by simpa using (congrArg Fin.val hi).symm)
    · intro hv
      have hnotimg : v ∉ Finset.image embed (Finset.univ : Finset (Fin k)) :=
        (Finset.mem_sdiff.mp hv).2
      have hvals : ∀ i : Fin k, v.val ≠ (embed i).val := by
        intro i hEq
        apply hnotimg
        refine Finset.mem_image.mpr ⟨i, by simp, ?_⟩
        exact (Fin.ext hEq).symm
      exact List.mem_toFinset.mpr ((mem_getNonTypeVerts_iff_vals embed v).2 hvals)
  rw [hset, Finset.card_sdiff]
  have himage :
      (Finset.image embed (Finset.univ : Finset (Fin k))).card = k := by
    simpa using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin k))) hinj
  simp [himage]

lemma perm_length_of_mem_getNonTypeVerts_permutations
    {n k : Nat} {embed : Fin k → Fin n} {π : List (Fin n)}
    (hπ : π ∈ (getNonTypeVerts n k embed).permutations') :
    π.length = (getNonTypeVerts n k embed).length := by
  exact (List.mem_permutations'.mp hπ).length_eq

lemma perm_nodup_of_mem_getNonTypeVerts_permutations
    {n k : Nat} {embed : Fin k → Fin n} {π : List (Fin n)}
    (hπ : π ∈ (getNonTypeVerts n k embed).permutations') :
    π.Nodup := by
  exact (List.mem_permutations'.mp hπ).nodup_iff.mpr (getNonTypeVerts_nodup embed)

/-- A computable fast isomorphism check for two Sym2Graphs (empty typed) -/
def isEmptyIsoFast_bool {n : Nat} (G₁ G₂ : Sym2Graph n) : Bool :=
  if G₁.edges.card != G₂.edges.card then false
  else
    -- `permutations'` (structural recursion) rather than `permutations`
    -- (well-founded recursion): the kernel cannot reduce `Acc.rec`, so the
    -- WF version blocks `decide +kernel` on every iso check.
    let perms := (List.finRange n).permutations'
    let edges := allEdges n
    perms.any fun perm =>
      edges.all fun e =>
        let e1_in := decide (e ∈ G₁.edges)
        let e2_in := decide ((applyPermEdge perm e) ∈ G₂.edges)
        e1_in == e2_in

/-- Soundness: a `true` result from the empty-typed fast check witnesses a
genuine flag equivalence `G₁ ∼sf G₂`. -/
theorem isEmptyIsoFast_bool_true_correct
    {n : ℕ} {G₁ G₂ : Sym2Graph n} (h : isEmptyIsoFast_bool G₁ G₂ = true)
    : G₁ ∼sf G₂
  := by
  simp [isEmptyIsoFast_bool] at h
  obtain ⟨_, π, hπ, h⟩ := h
  have hlen : π.length = n := by
    simpa using hπ.length_eq
  have hnodup : π.Nodup :=
    hπ.nodup_iff.mpr (List.nodup_finRange n)
  apply Nonempty.intro
  refine { graph_iso := ?_, type_preserve := ?_ }
  · simp [Sym2Graph.toLabeledGraph]
    refine graphEmbedIso ?_
    let f : Fin n → Fin n := fun v => (π[v.val]?).getD v
    have hf : Function.Injective f := by
      intro a b h_eq
      have h_getD_eq_get (v : Fin n) :
          (π[v.val]?).getD v = π.get ⟨v.val, by rw [hlen]; exact v.isLt⟩ := by
        have hv : v.val < π.length := by
          rw [hlen]
          exact v.isLt
        rw [List.getElem?_eq_getElem hv]
        simp [List.get_eq_getElem]
      dsimp [f] at h_eq
      rw [h_getD_eq_get, h_getD_eq_get, List.Nodup.get_inj_iff hnodup] at h_eq
      simp only [Fin.mk.injEq] at h_eq
      exact Fin.eq_of_val_eq h_eq
    refine ⟨⟨f, hf⟩, ?_⟩
    intro u v
    by_cases u_neq_v : u = v
    · rw [u_neq_v]
      simp only [Function.Embedding.coeFn_mk, SimpleGraph.irrefl]
    let e := s(u, v)
    have he : e ∈ allEdges n := by
      simp [e, allEdges]
      by_cases huv : u.val < v.val
      · use u
        use v
        simp_all only [Fin.val_fin_lt, and_self, true_or, f]
      · use v
        use u
        simp_all only [Fin.val_fin_lt, not_lt, and_self, or_true, and_true, f]
        exact Std.lt_of_le_of_ne huv (id (Ne.symm u_neq_v))
    simp only [Function.Embedding.coeFn_mk, SimpleGraph.fromEdgeSet_adj, SetLike.mem_coe, ne_eq]
    constructor
    · intro ⟨h₁, h₂⟩
      constructor
      · exact (h e he).mpr h₁
      · exact Ne.intro fun a ↦ h₂ (congrArg f a)
    · intro ⟨h₁, h₂⟩
      constructor
      · exact (h e he).mp h₁
      · exact Ne.intro fun a ↦ h₂ (hf a)
  · ext z
    exact Fin.elim0 z

/-- Completeness: a `false` result from the empty-typed fast check rules out
any flag equivalence `G₁ ∼sf G₂`. -/
theorem isEmptyIsoFast_bool_false_correct
    {n : Nat} {G₁ G₂ : Sym2Graph n} (h : isEmptyIsoFast_bool G₁ G₂ = false)
    : ¬ (G₁ ∼sf G₂)
  := by
  contrapose h
  have φ := h.some.graph_iso
  simp [isEmptyIsoFast_bool]
  refine ⟨edgeCount_eq_of_eqv h, ?_⟩
  simp [Sym2Graph.toLabeledGraph] at φ
  refine ⟨(List.finRange n).map φ.toEquiv, ?_, ?_⟩
  · simpa using (Equiv.Perm.map_finRange_perm φ.toEquiv)
  · intro e he
    have hEdge :
        e ∈ G₁.edges ↔ e.map φ.toEquiv ∈ G₂.edges := by
      constructor
      · intro he1
        have he1' : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₁.edges)).edgeSet := by
          simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
            (And.intro he1 (G₁.edges_valid e he1))
        have he2' : e.map φ.toEquiv ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₂.edges)).edgeSet :=
          (φ.map_mem_edgeSet_iff).2 he1'
        exact (by
          have : e.map φ.toEquiv ∈ G₂.edges ∧ ¬(e.map φ.toEquiv).IsDiag := by
            simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using he2'
          exact this.1)
      · intro he2
        have he2' : e.map φ.toEquiv ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₂.edges)).edgeSet := by
          simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
            (And.intro he2 (G₂.edges_valid (e.map φ.toEquiv) he2))
        have he1' : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₁.edges)).edgeSet :=
          (φ.map_mem_edgeSet_iff).1 he2'
        exact (by
          have : e ∈ G₁.edges ∧ ¬e.IsDiag := by
            simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using he1'
          exact this.1)
    simpa [applyPermEdge] using hEdge

/-! ## Degree-filtered fast isomorphism check (lower kernel-reduction memory)

`isEmptyIsoFastDeg_bool` is a value-identical, lower-memory replacement for
`isEmptyIsoFast_bool`: it extracts each graph's edge list once (`edgesNat`) and
generates only degree-compatible vertex maps (`dPerms`) instead of all `n!`
permutations, cutting the `decide +kernel` memory of flag enumeration. Proven
equivalent to `∼sf` (`isEmptyIsoFastDeg_bool_eq_true_iff`). -/

/-- Edge as ordered nat pair (min,max). Inlined copy of `edgeToPair`. -/
@[expose] def edgeNatPair {n : ℕ} (e : Sym2 (Fin n)) : ℕ × ℕ :=
  Sym2.lift ⟨fun a b => (min a.val b.val, max a.val b.val), fun a b => by
    show (min a.val b.val, max a.val b.val) = (min b.val a.val, max b.val a.val)
    rw [min_comm, max_comm]⟩ e

@[expose] def edgesNat {n : ℕ} (G : Sym2Graph n) : List (ℕ × ℕ) :=
  ((allEdges n).filter (fun e => decide (e ∈ G.edges))).map edgeNatPair

@[expose] def permPair (p : List ℕ) (ep : ℕ × ℕ) : ℕ × ℕ :=
  let a := p.getD ep.1 0; let b := p.getD ep.2 0; (min a b, max a b)

@[expose] def degAtL (edges : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (edges.filter (fun e => e.1 == v || e.2 == v)).length

@[expose] def dPerms (n : ℕ) (d1 d2 : List ℕ) : List (List ℕ) :=
  (List.range n).foldl (fun partials i => partials.flatMap (fun used =>
      ((List.range n).filter (fun j => d2.getD j 0 == d1.getD i 0 && !used.contains j)).map
        (fun j => used ++ [j]))) [[]]

@[expose] def isEmptyIsoFastDeg_bool {n : ℕ} (G1 G2 : Sym2Graph n) : Bool :=
  let e1 := edgesNat G1; let e2 := edgesNat G2
  let d1 := (List.range n).map (degAtL e1); let d2 := (List.range n).map (degAtL e2)
  let eps := (allEdges n).map edgeNatPair
  (dPerms n d1 d2).any fun p => eps.all fun ep => e1.contains ep == e2.contains (permPair p ep)

/-! ### Basic bridges -/

@[simp] theorem edgeNatPair_mk {n : ℕ} (u v : Fin n) :
    edgeNatPair (Sym2.mk (u, v)) = (min u.val v.val, max u.val v.val) := rfl

theorem edgeNatPair_injective {n : ℕ} : Function.Injective (edgeNatPair (n := n)) := by
  intro x y h
  induction x using Sym2.ind with | _ a b =>
  induction y using Sym2.ind with | _ c d =>
  rw [edgeNatPair_mk, edgeNatPair_mk, Prod.mk.injEq] at h
  obtain ⟨hmin, hmax⟩ := h
  rw [Sym2.eq_iff]
  have : (a.val = c.val ∧ b.val = d.val) ∨ (a.val = d.val ∧ b.val = c.val) := by omega
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Fin.val_injective h1, Fin.val_injective h2⟩
  · exact Or.inr ⟨Fin.val_injective h1, Fin.val_injective h2⟩

theorem permPair_edgeNatPair {n : ℕ} (p : List ℕ) (u v : Fin n) :
    permPair p (edgeNatPair (Sym2.mk (u, v)))
      = (min (p.getD u.val 0) (p.getD v.val 0), max (p.getD u.val 0) (p.getD v.val 0)) := by
  rw [edgeNatPair_mk]
  unfold permPair
  rcases le_total u.val v.val with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, min_comm, max_comm]

theorem not_isDiag_of_mem_allEdges {n : ℕ} {e : Sym2 (Fin n)} (h : e ∈ allEdges n) :
    ¬ e.IsDiag := by
  rw [allEdges, List.mem_flatMap] at h
  obtain ⟨i, _, hj⟩ := h
  rw [List.mem_filterMap] at hj
  obtain ⟨j, _, hij⟩ := hj
  by_cases hlt : i.val < j.val
  · rw [if_pos hlt] at hij
    rw [Option.some.injEq] at hij
    subst hij
    rw [Sym2.mk_isDiag_iff]
    intro he
    rw [he] at hlt
    exact (lt_irrefl _ hlt)
  · rw [if_neg hlt] at hij
    exact absurd hij (by simp)

theorem mem_allEdges_of_not_isDiag' {n : ℕ} {e : Sym2 (Fin n)} (h : ¬ e.IsDiag) :
    e ∈ allEdges n := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Sym2.mk_isDiag_iff] at h
    rw [allEdges, List.mem_flatMap]
    rcases Nat.lt_or_ge u.val v.val with hlt | hge
    · refine ⟨u, List.mem_finRange u, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨v, List.mem_finRange v, by rw [if_pos hlt]⟩
    · have hlt' : v.val < u.val :=
        Nat.lt_of_le_of_ne hge (fun he => h (Fin.ext he.symm))
      refine ⟨v, List.mem_finRange v, ?_⟩
      rw [List.mem_filterMap]
      refine ⟨u, List.mem_finRange u, ?_⟩
      rw [if_pos hlt']
      exact congrArg some Sym2.eq_swap

theorem allEdges_nodup {n : ℕ} : (allEdges n).Nodup := by
  rw [allEdges, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    apply List.Nodup.filterMap _ (List.nodup_finRange n)
    intro a a' b hb hb'
    by_cases ha : i.val < a.val
    · by_cases ha' : i.val < a'.val
      · rw [if_pos ha, Option.mem_def, Option.some.injEq] at hb
        rw [if_pos ha', Option.mem_def, Option.some.injEq] at hb'
        have hs : (Sym2.mk (i, a) : Sym2 (Fin n)) = Sym2.mk (i, a') := hb.trans hb'.symm
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2
        · exfalso; rw [h1] at ha'; exact lt_irrefl _ ha'
      · rw [if_neg ha'] at hb'; exact absurd hb' (by simp)
    · rw [if_neg ha] at hb; exact absurd hb (by simp)
  · refine (List.nodup_finRange n).imp ?_
    intro i i' hne
    simp only [Function.onFun]
    intro e he he'
    rw [List.mem_filterMap] at he he'
    obtain ⟨j, _, hj⟩ := he
    obtain ⟨j', _, hj'⟩ := he'
    by_cases hij : i.val < j.val
    · by_cases hij' : i'.val < j'.val
      · rw [if_pos hij, Option.some.injEq] at hj
        rw [if_pos hij', Option.some.injEq] at hj'
        have hs : (Sym2.mk (i, j) : Sym2 (Fin n)) = Sym2.mk (i', j') := hj.trans hj'.symm
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact hne h1
        · exfalso; rw [h1] at hij; rw [h2] at hij; omega
      · rw [if_neg hij'] at hj'; exact absurd hj' (by simp)
    · rw [if_neg hij] at hj; exact absurd hj (by simp)

/-! ### contains bridge -/

theorem mem_edgesNat_iff {n : ℕ} (G : Sym2Graph n) {e : Sym2 (Fin n)} (he : e ∈ allEdges n) :
    edgeNatPair e ∈ edgesNat G ↔ e ∈ G.edges := by
  unfold edgesNat
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', heq⟩
    rw [List.mem_filter] at he'
    have hee : e' = e := edgeNatPair_injective heq
    rw [hee] at he'
    exact of_decide_eq_true he'.2
  · intro hmem
    exact ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true hmem⟩, rfl⟩

theorem edgesNat_contains {n : ℕ} (G : Sym2Graph n) {e : Sym2 (Fin n)} (he : e ∈ allEdges n) :
    (edgesNat G).contains (edgeNatPair e) = decide (e ∈ G.edges) := by
  rw [List.contains_eq_mem, decide_eq_decide]
  exact mem_edgesNat_iff G he

/-! ### degree bridge -/

theorem endpoint_bridge {n : ℕ} (w : Fin n) (e : Sym2 (Fin n)) :
    ((edgeNatPair e).1 == w.val || (edgeNatPair e).2 == w.val) = decide (w ∈ e) := by
  induction e using Sym2.ind with | _ u v =>
  rw [edgeNatPair_mk, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_iff, Sym2.mem_iff, Fin.ext_iff]
  omega

theorem degAtL_edgesNat {n : ℕ} (G : Sym2Graph n) (w : Fin n) :
    degAtL (edgesNat G) w.val = degree G w := by
  unfold degAtL edgesNat degree
  rw [← List.countP_eq_length_filter, List.countP_map]
  have hpred : ((fun e : ℕ × ℕ => e.1 == w.val || e.2 == w.val) ∘ edgeNatPair)
      = (fun e : Sym2 (Fin n) => decide (w ∈ e)) := by
    funext e; exact endpoint_bridge w e
  rw [hpred, List.countP_filter, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (allEdges_nodup.filter _)]
  congr 1
  ext e
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, hw, hG⟩; exact ⟨hG, hw⟩
  · rintro ⟨hG, hw⟩
    exact ⟨mem_allEdges_of_not_isDiag' (G.edges_valid e hG), hw, hG⟩

/-! ### dPerms characterization -/

theorem mem_dPermsAux_iff (n : ℕ) (d1 d2 : List ℕ) :
    ∀ (m : ℕ) (p : List ℕ),
      p ∈ (List.range m).foldl (fun partials i => partials.flatMap (fun used =>
        ((List.range n).filter (fun j => d2.getD j 0 == d1.getD i 0 && !used.contains j)).map
          (fun j => used ++ [j]))) [[]]
      ↔ (p.length = m ∧ (∀ i, i < m → p.getD i 0 < n) ∧ p.Nodup ∧
          (∀ i, i < m → d2.getD (p.getD i 0) 0 = d1.getD i 0)) := by
  intro m
  induction m with
  | zero =>
    intro p
    simp only [List.range_zero, List.foldl_nil, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i), List.nodup_nil,
        fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · rintro ⟨hlen, _, _, _⟩; exact hlen
  | succ m ih =>
    intro p
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_range, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨used, hused, j, ⟨hjlt, hjdeg, hjcont⟩, hp⟩
      obtain ⟨hulen, hult, hund, hudeg⟩ := (ih used).mp hused
      have hjnotin : j ∉ used := by simpa [List.contains_eq_mem] using hjcont
      subst hp
      have hgetlt : ∀ i, i < m → (used ++ [j]).getD i 0 = used.getD i 0 := by
        intro i hi
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [hulen]; omega)]
      have hgetm : (used ++ [j]).getD m 0 = j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq hulen)]
        simp [hulen]
      refine ⟨by simp [hulen], ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hgetlt i hi']; exact hult i hi'
        · rw [hgetm]; exact hjlt
      · refine List.nodup_append.mpr ⟨hund, List.nodup_singleton j, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb; subst hb
        intro heq; exact hjnotin (heq ▸ ha)
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hgetlt i hi']; exact hudeg i hi'
        · rw [hgetm]; exact hjdeg
    · rintro ⟨hlen, hlt, hnd, hdeg⟩
      have hsplit : p = p.take m ++ [p.getD m 0] := by
        conv_lhs => rw [← List.take_length (l := p)]
        rw [hlen, List.take_add_one]
        congr 1
        rw [List.getElem?_eq_getElem (by omega), Option.toList_some, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]
        simp
      have htlen : (p.take m).length = m := by rw [List.length_take, hlen]; omega
      have hnd' : (p.take m ++ [p.getD m 0]).Nodup := hsplit ▸ hnd
      obtain ⟨htnd, _, htdisj⟩ := List.nodup_append.mp hnd'
      have hjni : p.getD m 0 ∉ p.take m := fun hj =>
        htdisj (p.getD m 0) hj (p.getD m 0) (List.mem_singleton.mpr rfl) rfl
      have hgetlt : ∀ i, i < m → (p.take m).getD i 0 = p.getD i 0 := by
        intro i hi
        conv_rhs => rw [hsplit]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [htlen]; omega)]
      refine ⟨p.take m, ?_, p.getD m 0, ⟨?_, ?_, ?_⟩, ?_⟩
      · refine (ih (p.take m)).mpr ⟨htlen, ?_, htnd, ?_⟩
        · intro i hi; rw [hgetlt i hi]; exact hlt i (by omega)
        · intro i hi; rw [hgetlt i hi]; exact hdeg i (by omega)
      · exact hlt m (by omega)
      · exact hdeg m (by omega)
      · simpa [List.contains_eq_mem] using hjni
      · exact hsplit.symm

theorem mem_dPerms_iff (n : ℕ) (d1 d2 : List ℕ) (p : List ℕ) :
    p ∈ dPerms n d1 d2 ↔ (p.length = n ∧ (∀ i, i < n → p.getD i 0 < n) ∧ p.Nodup ∧
        (∀ i, i < n → d2.getD (p.getD i 0) 0 = d1.getD i 0)) :=
  mem_dPermsAux_iff n d1 d2 n p

/-! ### assembly helpers -/

theorem map_isDiag_iff {n : ℕ} (φ : Fin n ≃ Fin n) (e : Sym2 (Fin n)) :
    (Sym2.map φ e).IsDiag ↔ e.IsDiag := by
  induction e using Sym2.ind with | _ a b =>
  rw [Sym2.map_pair_eq, Sym2.mk_isDiag_iff, Sym2.mk_isDiag_iff, φ.injective.eq_iff]

theorem permPair_edgeNatPair_eq {n : ℕ} (p : List ℕ) (φ : Fin n ≃ Fin n)
    (hp : ∀ w : Fin n, p.getD w.val 0 = (φ w).val) (e : Sym2 (Fin n)) :
    permPair p (edgeNatPair e) = edgeNatPair (Sym2.map φ e) := by
  induction e using Sym2.ind with | _ u v =>
  rw [permPair_edgeNatPair, hp u, hp v, Sym2.map_pair_eq, edgeNatPair_mk]

theorem map_range_getD {α : Type*} (f : ℕ → α) (d : α) {i n : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  have hlen : i < ((List.range n).map f).length := by
    rw [List.length_map, List.length_range]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

theorem map_finRange_getD {n : ℕ} {α : Type*} (f : Fin n → α) (d : α) {i : ℕ} (hi : i < n) :
    ((List.finRange n).map f).getD i d = f ⟨i, hi⟩ := by
  have hlen : i < ((List.finRange n).map f).length := by
    rw [List.length_map, List.length_finRange]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

theorem isEmptyIsoFastDeg_bool_eq {n : ℕ} (G1 G2 : Sym2Graph n) :
    isEmptyIsoFastDeg_bool G1 G2 =
      (dPerms n ((List.range n).map (degAtL (edgesNat G1)))
          ((List.range n).map (degAtL (edgesNat G2)))).any
        (fun p => ((allEdges n).map edgeNatPair).all
          (fun ep => (edgesNat G1).contains ep == (edgesNat G2).contains (permPair p ep))) := rfl

/-! ### master iff and correctness -/

theorem isEmptyIsoFastDeg_bool_eq_true_iff {n : ℕ} (G1 G2 : Sym2Graph n) :
    isEmptyIsoFastDeg_bool G1 G2 = true ↔ G1 ∼sf G2 := by
  rw [isEmptyIsoFastDeg_bool_eq, List.any_eq_true]
  constructor
  · rintro ⟨p, hp_mem, hall⟩
    rw [List.all_eq_true] at hall
    rw [mem_dPerms_iff] at hp_mem
    obtain ⟨hplen, hplt, hpnd, _⟩ := hp_mem
    set f : Fin n → Fin n := fun w => ⟨p.getD w.val 0, hplt w.val w.isLt⟩ with hf_def
    have hf_inj : Function.Injective f := by
      intro a b hab
      have h1 : p.getD a.val 0 = p.getD b.val 0 := congrArg Fin.val hab
      have ha : a.val < p.length := by rw [hplen]; exact a.isLt
      have hb : b.val < p.length := by rw [hplen]; exact b.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb] at h1
      simp only [Option.getD_some] at h1
      exact Fin.ext ((hpnd.getElem_inj_iff).mp h1)
    let φ : Fin n ≃ Fin n := Equiv.ofBijective f hf_inj.bijective_of_finite
    have hpφ : ∀ w : Fin n, p.getD w.val 0 = (φ w).val := fun w => rfl
    apply sym2GraphEqv_of_equiv φ
    intro e
    by_cases hd : e.IsDiag
    · have h1 : e ∉ G1.edges := fun he => G1.edges_valid e he hd
      have hd2 : (Sym2.map φ e).IsDiag := (map_isDiag_iff φ e).mpr hd
      have h2 : Sym2.map φ e ∉ G2.edges := fun he => G2.edges_valid _ he hd2
      exact ⟨fun he => absurd he h1, fun he => absurd he h2⟩
    · have he_all : e ∈ allEdges n := mem_allEdges_of_not_isDiag' hd
      have hmap_all : Sym2.map φ e ∈ allEdges n :=
        mem_allEdges_of_not_isDiag' (fun hdd => hd ((map_isDiag_iff φ e).mp hdd))
      have hc := hall (edgeNatPair e) (List.mem_map.mpr ⟨e, he_all, rfl⟩)
      rw [beq_iff_eq, edgesNat_contains G1 he_all, permPair_edgeNatPair_eq p φ hpφ e,
          edgesNat_contains G2 hmap_all] at hc
      rw [← decide_eq_decide]
      exact hc
  · intro h
    obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv h
    set p := (List.finRange n).map (fun w => (φ w).val) with hp_def
    have hpget : ∀ i (hi : i < n), p.getD i 0 = (φ ⟨i, hi⟩).val := by
      intro i hi
      rw [hp_def]
      exact map_finRange_getD (fun w => (φ w).val) 0 hi
    have hpφ : ∀ w : Fin n, p.getD w.val 0 = (φ w).val := by
      intro w; rw [hpget w.val w.isLt]
    refine ⟨p, ?_, ?_⟩
    · rw [mem_dPerms_iff]
      refine ⟨by rw [hp_def, List.length_map, List.length_finRange], ?_, ?_, ?_⟩
      · intro i hi; rw [hpget i hi]; exact (φ ⟨i, hi⟩).isLt
      · rw [hp_def]
        exact (List.nodup_finRange n).map (fun a b hab => φ.injective (Fin.val_injective hab))
      · intro i hi
        rw [hpget i hi, map_range_getD _ _ ((φ ⟨i, hi⟩).isLt), map_range_getD _ _ hi]
        have hd1 : degAtL (edgesNat G1) i = degree G1 ⟨i, hi⟩ := degAtL_edgesNat G1 ⟨i, hi⟩
        have hd2 : degAtL (edgesNat G2) (φ ⟨i, hi⟩).val = degree G2 (φ ⟨i, hi⟩) :=
          degAtL_edgesNat G2 (φ ⟨i, hi⟩)
        rw [hd1, hd2]
        exact (degree_eq_of_eqv φ hφ ⟨i, hi⟩).symm
    · rw [List.all_eq_true]
      intro ep hep
      rw [List.mem_map] at hep
      obtain ⟨e, he_all, rfl⟩ := hep
      have hmap_all : Sym2.map φ e ∈ allEdges n :=
        mem_allEdges_of_not_isDiag' (fun hdd =>
          not_isDiag_of_mem_allEdges he_all ((map_isDiag_iff φ e).mp hdd))
      rw [beq_iff_eq, edgesNat_contains G1 he_all, permPair_edgeNatPair_eq p φ hpφ e,
          edgesNat_contains G2 hmap_all, decide_eq_decide]
      exact hφ e

theorem isEmptyIsoFastDeg_bool_true_correct {n : ℕ} {G1 G2 : Sym2Graph n}
    (h : isEmptyIsoFastDeg_bool G1 G2 = true) : G1 ∼sf G2 :=
  (isEmptyIsoFastDeg_bool_eq_true_iff G1 G2).mp h

theorem isEmptyIsoFastDeg_bool_false_correct {n : ℕ} {G1 G2 : Sym2Graph n}
    (h : isEmptyIsoFastDeg_bool G1 G2 = false) : ¬ (G1 ∼sf G2) := by
  intro hiso
  rw [(isEmptyIsoFastDeg_bool_eq_true_iff G1 G2).mpr hiso] at h
  exact Bool.noConfusion h

theorem isEmptyIsoFastDeg_bool_complete {n : ℕ} {G G' : Sym2Graph n} (h : G ∼sf G') :
    isEmptyIsoFastDeg_bool G G' = true :=
  (isEmptyIsoFastDeg_bool_eq_true_iff G G').mpr h

/-- High-priority decision procedure for empty-typed flag equivalence,
backed by `isEmptyIsoFast_bool` and its soundness/completeness proofs. -/
instance (priority := high) fastDecidableSym2GraphEqv
    {n : Nat} (G₁ G₂ : Sym2Graph n) : Decidable (G₁ ∼sf G₂) :=
  if h : isEmptyIsoFastDeg_bool G₁ G₂ = true then
    isTrue (isEmptyIsoFastDeg_bool_true_correct h)
  else
    isFalse (isEmptyIsoFastDeg_bool_false_correct (eq_false_of_ne_true h))

/-- Finiteness of empty-typed flags, obtained by quotienting `Sym2Graph n`
under the fast-decidable equivalence; enables flag enumeration. -/
instance (priority := high) fastFintypeSym2EmptyTypedFlag
    {n : ℕ} : Fintype (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.fintype _ _ (Sym2GraphSetoid n) ?_
  intro G G'
  exact fastDecidableSym2GraphEqv G G'

/-- Decidable equality on empty-typed flags via the fast iso check, used to
deduplicate flags in the loader macros. -/
instance (priority := high) fastDecidableSym2EmptyTypedFlagEqv
    {n : ℕ} : DecidableEq (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  exact fastDecidableSym2GraphEqv G G'

/-- A computable fast isomorphism check for two Sym2LabeledGraphs -/
def isIsoFast_bool {k n : Nat} {σ : Sym2FlagType k} (G₁ G₂ : Sym2LabeledGraph σ n) : Bool :=
  if G₁.edges.card != G₂.edges.card then false
  else
    let nonType1 := getNonTypeVerts n k G₁.type_embed
    let nonType2 := getNonTypeVerts n k G₂.type_embed
    let L2_perms := nonType2.permutations'
    let edges := allEdges n
    L2_perms.any fun p2 =>
      let fullMap := buildFullMap n k G₁.type_embed G₂.type_embed nonType1 p2
      edges.all fun e =>
        let e1_in := decide (e ∈ G₁.edges)
        let e2_in := decide ((applyPermEdge fullMap e) ∈ G₂.edges)
        e1_in == e2_in

/-- Soundness of the typed fast check: a `true` result yields a flag
equivalence `G₁ ∼sf G₂` whose isomorphism preserves the type embedding. -/
theorem isIsoFast_bool_true_correct
    {k n : ℕ} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : isIsoFast_bool G₁ G₂ = true) : G₁ ∼sf G₂
  := by
  simp [isIsoFast_bool] at h
  obtain ⟨_, π, hπ, h⟩ := h
  let nonType := getNonTypeVerts n k G₁.type_embed
  let fullMap := buildFullMap n k G₁.type_embed G₂.type_embed nonType π
  apply Nonempty.intro
  refine { graph_iso := ?_, type_preserve := ?_ }
  · refine graphEmbedIso ?_
    let f : Fin n → Fin n := fun v => (fullMap[v.val]?).getD v
    have hf : Function.Injective f := by
      intro a b h_eq
      dsimp [f, fullMap, buildFullMap] at h_eq
      set ta := List.find? (fun i => a.val == (G₁.type_embed i).val) (List.finRange k) with hta
      set tb := List.find? (fun i => b.val == (G₁.type_embed i).val) (List.finRange k) with htb
      cases hta' : ta <;> cases htb' : tb
      · -- ta = none, tb = none
        set ia := myIndexOf a nonType 0 with hia
        set ib := myIndexOf b nonType 0 with hib
        cases hia' : ia <;> cases hib' : ib
        · -- ia = none, ib = none
          simp only [List.length_map, List.length_finRange, Fin.is_lt, getElem?_pos,
            List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta, hta', hia',
            Option.getD_some, htb', hib', tb, ib, ta, ia] at h_eq
          exact h_eq
        · -- ia = none, ib = some _
          exfalso
          symm at hta
          rw [hta'] at hta
          have ha_mem : a ∈ nonType := by
            dsimp [nonType, getNonTypeVerts]
            refine List.mem_filter.mpr ?_
            constructor
            · simp only [List.mem_finRange]
            · rw [List.all_eq_true]
              intro i hi
              have hnone := (List.find?_eq_none.mp hta) i hi
              simpa [beq_iff_eq] using hnone
          have hidx_ne_none : myIndexOf a nonType 0 ≠ none :=
            myIndexOf_ne_none_of_mem a nonType 0 ha_mem
          have hidx_none : myIndexOf a nonType 0 = none := by
            simpa [ia] using hia'
          exact hidx_ne_none hidx_none
        · -- ia = some _, ib = none
          exfalso
          symm at htb
          rw [htb'] at htb
          have hb_mem : b ∈ nonType := by
            dsimp [nonType, getNonTypeVerts]
            refine List.mem_filter.mpr ?_
            constructor
            · simp only [List.mem_finRange]
            · rw [List.all_eq_true]
              intro i hi
              have hnone := (List.find?_eq_none.mp htb) i hi
              simpa [beq_iff_eq] using hnone
          have hidx_ne_none : myIndexOf b nonType 0 ≠ none :=
            myIndexOf_ne_none_of_mem b nonType 0 hb_mem
          have hidx_none : myIndexOf b nonType 0 = none := by
            simpa [ib] using hib'
          exact hidx_ne_none hidx_none
        · -- ia = some _, ib = some _
          rename_i i j
          simp [ta, tb, ia, ib, hta', htb', hia', hib'] at h_eq
          symm at hia hib
          rw [hia'] at hia
          rw [hib'] at hib
          have hlen_pi : π.length = n - k := by
            rw [hπ.length_eq]
            exact getNonTypeVerts_length G₂.type_embed G₂.type_embed.injective
          have hi : i < π.length := by
            rw [hlen_pi, ← getNonTypeVerts_length G₁.type_embed G₁.type_embed.injective]
            exact myIndexOf_eq_some_implies_lt_length a nonType i hia
          have hj : j < π.length := by
            rw [hlen_pi, ← getNonTypeVerts_length G₁.type_embed G₁.type_embed.injective]
            exact myIndexOf_eq_some_implies_lt_length b nonType j hib
          rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h_eq
          have hget : π.get ⟨i, hi⟩ = π.get ⟨j, hj⟩ := by simpa only [List.get_eq_getElem]
          have hij_fin : (⟨i, hi⟩ : Fin π.length) = ⟨j, hj⟩ :=
            (List.Nodup.get_inj_iff (hπ.nodup_iff.mpr (getNonTypeVerts_nodup G₂.type_embed))).1 hget
          rw [← Fin.mk.inj_iff.mp hij_fin] at hib
          exact myIndexOf_eq_some_same_index_implies_eq nonType i (getNonTypeVerts_nodup G₁.type_embed) hia hib
      · -- ta = none, tb = some _
        rename_i j
        exfalso
        have ha_mem : a ∈ nonType := by
          dsimp [nonType, getNonTypeVerts]
          refine List.mem_filter.mpr ?_
          constructor
          · simp [List.mem_finRange]
          · rw [List.all_eq_true]
            intro i hi
            have hnone := (List.find?_eq_none.mp hta') i hi
            simpa [beq_iff_eq] using hnone
        have hidx_ne_none : myIndexOf a nonType 0 ≠ none := myIndexOf_ne_none_of_mem a nonType 0 ha_mem
        cases hidx : myIndexOf a nonType 0 with
        | none =>
            exact hidx_ne_none hidx
        | some idx =>
            have hlen_pi : π.length = n - k := by
              rw [hπ.length_eq]
              exact getNonTypeVerts_length G₂.type_embed G₂.type_embed.injective
            have hidx_lt_pi : idx < π.length := by
              rw [hlen_pi, ← getNonTypeVerts_length G₁.type_embed G₁.type_embed.injective]
              exact myIndexOf_eq_some_implies_lt_length a nonType idx hidx
            simp [ta, tb, hta', htb', hidx] at h_eq
            have hget : π.get ⟨idx, hidx_lt_pi⟩ = G₂.type_embed j := by
              rw [List.getElem?_eq_getElem hidx_lt_pi] at h_eq
              exact Fin.eq_of_val_eq (congrArg Fin.val h_eq)
            exact (mem_getNonTypeVerts_iff_vals G₂.type_embed (G₂.type_embed j)).1 ((hπ.mem_iff).1 (List.mem_of_getElem hget)) j rfl
      · -- ta = some _, tb = none
        rename_i i
        exfalso
        have hb_mem : b ∈ nonType := by
          dsimp [nonType, getNonTypeVerts]
          refine List.mem_filter.mpr ?_
          constructor
          · simp [List.mem_finRange]
          · rw [List.all_eq_true]
            intro t ht
            have hnone := (List.find?_eq_none.mp htb') t ht
            simpa [beq_iff_eq] using hnone
        have hidx_ne_none : myIndexOf b nonType 0 ≠ none :=
          myIndexOf_ne_none_of_mem b nonType 0 hb_mem
        cases hidx : myIndexOf b nonType 0 with
        | none =>
            exact hidx_ne_none hidx
        | some idx =>
            have hlen_pi : π.length = n - k := by
              rw [hπ.length_eq]
              exact getNonTypeVerts_length G₂.type_embed G₂.type_embed.injective
            have hidx_lt_pi : idx < π.length := by
              rw [hlen_pi, ← getNonTypeVerts_length G₁.type_embed G₁.type_embed.injective]
              exact myIndexOf_eq_some_implies_lt_length b nonType idx hidx
            simp [ta, tb, hta', htb', hidx] at h_eq
            have hget : π.get ⟨idx, hidx_lt_pi⟩ = G₂.type_embed i := by
              rw [List.getElem?_eq_getElem hidx_lt_pi, ] at h_eq
              exact Fin.eq_of_val_eq (congrArg Fin.val (id (Eq.symm h_eq)))
            exact (mem_getNonTypeVerts_iff_vals G₂.type_embed (G₂.type_embed i)).1 ((hπ.mem_iff).1 (List.mem_of_getElem hget)) i rfl
      · -- ta = some _, tb = some _
        simp [ta, tb, hta', htb'] at h_eq
        symm at hta htb
        rw [hta', List.find?_eq_some_iff_append] at hta
        rw [htb', List.find?_eq_some_iff_append] at htb
        have ha := hta.1
        have hb := htb.1
        simp only [beq_iff_eq, Fin.val_eq_val] at ha hb
        rw [ha, hb, h_eq]
    refine ⟨⟨f, hf⟩, ?_⟩
    simp [Sym2LabeledGraph.toLabeledGraph]
    intro u v
    by_cases u_neq_v : u = v
    · rw [u_neq_v]
      simp only [not_true_eq_false, and_false]
    let e := s(u, v)
    have he : e ∈ allEdges n := by
      simp [e, allEdges]
      by_cases huv : u.val < v.val
      · use u
        use v
        simp_all only [Fin.val_fin_lt, and_self, true_or, f]
      · use v
        use u
        simp_all only [Fin.val_fin_lt, not_lt, and_self, or_true, and_true, f]
        exact Std.lt_of_le_of_ne huv (id (Ne.symm u_neq_v))
    constructor
    · intro ⟨h₁, h₂⟩
      constructor
      · exact (h e he).mpr h₁
      · exact Ne.intro u_neq_v
    · intro ⟨h₁, h₂⟩
      constructor
      · exact (h e he).mp h₁
      · exact Ne.intro fun a ↦ u_neq_v (hf a)
  · ext t
    have hfind :
      List.find? (fun i => (G₁.type_embed t).val == (G₁.type_embed i).val) (List.finRange k) = some t := by
      rw [List.find?_eq_some_iff_append]
      constructor
      · simp only [BEq.rfl]
      · use (List.finRange k).take t.val
        use (List.finRange k).drop (t.val + 1)
        constructor
        · nth_rw 1 [← List.take_append_drop t (List.finRange k)]
          rw [List.drop_eq_getElem_cons (by simp only [List.length_finRange, Fin.is_lt])]
          simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
        · intro i hi
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq, Fin.val_eq_val]
          intro h
          have t_lt_i : i < t := by
            rw [List.mem_iff_getElem] at hi
            obtain ⟨j, ⟨h1, h2⟩⟩ := hi
            simp only [List.length_take, List.length_finRange, Fin.is_le', inf_of_le_left,
              List.getElem_take, List.getElem_finRange, Fin.cast_mk] at h1 h2
            subst h2
            simp_all only [EmbeddingLike.apply_eq_iff_eq, lt_self_iff_false]
          rw [G₁.type_embed.injective h] at t_lt_i
          exact (lt_self_iff_false i).mp t_lt_i
    simp [fullMap, buildFullMap, hfind, graphEmbedIso, Sym2LabeledGraph.toLabeledGraph]

/-- From a flag equivalence, the underlying isomorphism maps `G₁`'s non-type
vertices onto a permutation of `G₂`'s; supplies the permutation witness for
the completeness direction of `isIsoFast_bool`. -/
lemma nonType_perm_witness_of_eqv
    {k n : Nat} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : G₁ ∼sf G₂) :
    ((getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso).Perm
      (getNonTypeVerts n k G₂.type_embed) := by
  have hnod1 : ((getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso).Nodup := by
    have hnodNT1 : (getNonTypeVerts n k G₁.type_embed).Nodup := by
      dsimp [getNonTypeVerts]
      exact (List.nodup_finRange n).filter _
    exact hnodNT1.map h.some.graph_iso.injective
  have hnod2 : (getNonTypeVerts n k G₂.type_embed).Nodup := by
    dsimp [getNonTypeVerts]
    exact (List.nodup_finRange n).filter _
  rw [List.perm_ext_iff_of_nodup hnod1 hnod2]
  intro v
  constructor
  · intro hv
    simp only [getNonTypeVerts, List.mem_filter, List.mem_finRange, true_and]
    rcases List.mem_map.mp hv with ⟨u, hu, rfl⟩
    have hu' : ∀ i : Fin k, (u.val != (G₁.type_embed i).val) = true := by
      have huAll : ((List.finRange k).all fun i => u.val != (G₁.type_embed i).val) = true :=
        (List.mem_filter.mp hu).2
      intro i
      exact (List.all_eq_true.mp huAll) i (by simp)
    refine List.all_eq_true.mpr ?_
    intro i
    have hti : h.some.graph_iso (G₁.type_embed i) = G₂.type_embed i := by
      simpa [Function.comp_apply, Sym2LabeledGraph.toLabeledGraph] using congrFun h.some.type_preserve i
    by_contra hEq
    have huEq : h.some.graph_iso u = h.some.graph_iso (G₁.type_embed i) := by
      apply Fin.ext
      simpa [hti] using hEq
    have uEq : u = G₁.type_embed i := h.some.graph_iso.injective huEq
    have : (u.val != (G₁.type_embed i).val) = true := hu' i
    simp [uEq] at this
  · intro hv
    simp only [getNonTypeVerts, List.mem_filter, List.mem_finRange, true_and] at hv
    let u : Fin n := h.some.graph_iso.symm v
    have hu_nonType : ∀ i : Fin k, u.val ≠ (G₁.type_embed i).val := by
      intro i hEq
      have hti : h.some.graph_iso (G₁.type_embed i) = G₂.type_embed i := by
        simpa [Function.comp_apply, Sym2LabeledGraph.toLabeledGraph] using congrFun h.some.type_preserve i
      have hvEq : v = G₂.type_embed i := by
        calc
          v = h.some.graph_iso u := by simp [u]
          _ = h.some.graph_iso (G₁.type_embed i) := by
                apply congrArg h.some.graph_iso
                exact Fin.ext hEq
          _ = G₂.type_embed i := hti
      have hv' : ∀ j : Fin k, (v.val != (G₂.type_embed j).val) = true := by
        intro j
        exact (List.all_eq_true.mp hv) j (by simp)
      have : (v.val != (G₂.type_embed i).val) = true := hv' i
      simp [hvEq] at this
    have hu_mem : u ∈ getNonTypeVerts n k G₁.type_embed := by
      simp [getNonTypeVerts, hu_nonType]
    have hmap : h.some.graph_iso u = v := by simp [u]
    exact List.mem_map.mpr ⟨u, hu_mem, hmap⟩

lemma my_find_some {α} (l : List α) (p : α → Bool) (x : α)
    (hx : x ∈ l) (hp : p x) (huniq : ∀ y ∈ l, p y → y = x) : List.find? p l = some x := by
  induction l with
  | nil =>
    cases hx
  | cons a as ih =>
    cases hx with
    | head _ =>
      simp [List.find?, hp]
    | tail _ hx_tail =>
      simp [List.find?]
      cases hpa : p a
      · simp [ih hx_tail (fun y hy hpy => huniq y (List.Mem.tail _ hy) hpy)]
      · have : a = x := huniq a (List.Mem.head _) hpa
        rw [this]

lemma find_eq_some {k n : Nat} {σ : Sym2FlagType k} (G₁ : Sym2LabeledGraph σ n)
    (v : Fin n) (i : Fin k) (hi : v = G₁.type_embed i) :
    List.find? (fun i => v.val == (G₁.type_embed i).val) (List.finRange k) = some i := by
  have h1 : (fun j : Fin k => v.val == (G₁.type_embed j).val) i = true := by
    simp [hi]
  have h2 : ∀ j ∈ List.finRange k, (fun j : Fin k => v.val == (G₁.type_embed j).val) j = true → j = i := by
    intro j _ hj
    simp only [beq_iff_eq] at hj
    have hj' : v = G₁.type_embed j := Fin.ext hj
    rw [hi] at hj'
    exact G₁.type_embed.injective hj'.symm
  exact my_find_some _ _ _ (List.mem_finRange _) h1 h2

lemma find_eq_none {k n : Nat} {σ : Sym2FlagType k} (G₁ : Sym2LabeledGraph σ n)
    (v : Fin n) (hn : ∀ i, v ≠ G₁.type_embed i) :
    List.find? (fun i => v.val == (G₁.type_embed i).val) (List.finRange k) = none := by
  apply List.find?_eq_none.mpr
  intro x _
  have h_neq := hn x
  simp only [beq_iff_eq]
  intro h_eq
  apply h_neq
  apply Fin.ext
  exact h_eq

lemma mem_getNonTypeVerts_comp {n k : Nat} {embed : Fin k → Fin n} (v : Fin n)
    (hn : ∀ i, v ≠ embed i) : v ∈ getNonTypeVerts n k embed := by
  simp [getNonTypeVerts, List.mem_filter]
  intro i
  exact Fin.val_ne_of_ne (hn i)

/-- From a flag equivalence, the `buildFullMap` reconstructed from the
isomorphism agrees with it on edges; supplies the edge-preservation witness
for the completeness direction of `isIsoFast_bool`. -/
lemma buildFullMap_edge_witness_of_eqv
    {k n : Nat} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : G₁ ∼sf G₂) :
    ∀ e ∈ allEdges n,
      e ∈ G₁.edges ↔
        applyPermEdge
          (buildFullMap n k G₁.type_embed G₂.type_embed
            (getNonTypeVerts n k G₁.type_embed)
            ((getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso)) e ∈ G₂.edges := by
  intro e _
  let φ := h.some.graph_iso
  have hEdge : e ∈ G₁.edges ↔ e.map φ ∈ G₂.edges := by
    constructor
    · intro he
      have he_G₁ : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₁.edges)).edgeSet := by
        simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
          (And.intro he (G₁.edges_valid e he))
      have he_G₂ : e.map φ ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₂.edges)).edgeSet :=
        (φ.map_mem_edgeSet_iff).2 he_G₁
      simp [SimpleGraph.edgeSet_fromEdgeSet] at he_G₂
      exact he_G₂.1
    · intro he
      have he_G₂ : e.map φ ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₂.edges)).edgeSet := by
        simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
          (And.intro he (G₂.edges_valid (e.map φ) he))
      have he_G₁ : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₁.edges)).edgeSet :=
        (φ.map_mem_edgeSet_iff).1 he_G₂
      simp [SimpleGraph.edgeSet_fromEdgeSet] at he_G₁
      exact he_G₁.1
  have hMapEq :
      applyPermEdge
        (buildFullMap n k G₁.type_embed G₂.type_embed
          (getNonTypeVerts n k G₁.type_embed)
          ((getNonTypeVerts n k G₁.type_embed).map φ)) e
      = e.map φ := by
    dsimp [applyPermEdge]
    congr 1
    ext v
    simp [buildFullMap]
    have h_cases : (∃ i, v = G₁.type_embed i) ∨ (¬ ∃ i, v = G₁.type_embed i) := by
      exact Classical.em _
    rcases h_cases with ⟨i, hi⟩ | hn
    · -- v = G₁.type_embed i
      have h_find : List.find? (fun i => v.val == (G₁.type_embed i).val) (List.finRange k) = some i := by
        exact find_eq_some G₁ v i hi
      simp [h_find]
      have h_type_eq : G₂.type_embed i = φ (G₁.type_embed i) := by
        have ht := h.some.type_preserve
        have ht' := congr_fun ht i
        exact ht'.symm
      rw [hi]
      rw [h_type_eq]
    · -- v ≠ G₁.type_embed i
      have hn' : ∀ i, v ≠ G₁.type_embed i := by
        intro i hi
        exact hn ⟨i, hi⟩
      have h_find : List.find? (fun i => v.val == (G₁.type_embed i).val) (List.finRange k) = none := by
        exact find_eq_none G₁ v hn'
      simp [h_find]
      have h_mem : v ∈ getNonTypeVerts n k G₁.type_embed := by
        exact mem_getNonTypeVerts_comp v hn'
      have ⟨idx, hidx⟩ : ∃ idx, myIndexOf v (getNonTypeVerts n k G₁.type_embed) 0 = some idx := by
        have h_idx_neq := myIndexOf_ne_none_of_mem v (getNonTypeVerts n k G₁.type_embed) 0 h_mem
        cases hidx_case : myIndexOf v (getNonTypeVerts n k G₁.type_embed) 0
        · contradiction
        · exact ⟨_, rfl⟩
      simp [hidx]
      have h_getElem : (getNonTypeVerts n k G₁.type_embed)[idx]? = some v :=
        myIndexOf_get_zero v (getNonTypeVerts n k G₁.type_embed) idx hidx
      simp [h_getElem]
  simp only [hEdge, ← hMapEq, φ]

/-- Completeness of the typed fast check: a `false` result rules out any
type-preserving flag equivalence `G₁ ∼sf G₂`. -/
theorem isIsoFast_bool_false_correct
    {k n : Nat} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : isIsoFast_bool G₁ G₂ = false) : ¬ (G₁ ∼sf G₂)
  := by
  contrapose h
  have φ := h.some
  have φg := φ.graph_iso
  simp [isIsoFast_bool]
  refine ⟨labeledEdgeCount_eq_of_eqv h, ?_⟩
  use (getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso
  exact ⟨nonType_perm_witness_of_eqv h, buildFullMap_edge_witness_of_eqv h⟩

/-! ## Degree-filtered typed fast isomorphism check (lower kernel-reduction memory)

`isIsoFastDeg_bool` is a value-identical, lower-memory replacement for
`isIsoFast_bool`: it extracts each underlying graph's edge list once (`edgesNat`)
and enumerates only the vertex maps that fix the type embedding and are
degree-compatible on the underlying graph (via `dPerms` filtered by the type
pins), instead of all permutations of the non-type vertices; edge preservation is
checked with `List.contains` over `edgesNat` rather than `Finset` membership,
cutting `decide +kernel` memory.  Proven equivalent to `∼sf`
(`isIsoFastDeg_bool_eq_true_iff`). -/

/-- A vertex permutation that preserves underlying-edge membership *and* the type
embedding induces a labeled `∼sf` equivalence.  (Labeled analogue of
`sym2GraphEqv_of_equiv`.) -/
theorem sym2LabeledGraphEqv_of_equiv {k n : ℕ} {σ : Sym2FlagType k}
    {G1 G2 : Sym2LabeledGraph σ n} (φ : Fin n ≃ Fin n)
    (hedge : ∀ e : Sym2 (Fin n), e ∈ G1.edges ↔ Sym2.map φ e ∈ G2.edges)
    (htype : ∀ t : Fin k, φ (G1.type_embed t) = G2.type_embed t) :
    G1 ∼sf G2 := by
  refine Nonempty.intro { graph_iso := ?_, type_preserve := ?_ }
  · refine { toEquiv := φ, map_rel_iff' := ?_ }
    intro a b
    rw [Sym2LabeledGraph.toLabeledGraph_adj_iff, Sym2LabeledGraph.toLabeledGraph_adj_iff]
    have he := hedge s(a, b)
    rw [Sym2.map_pair_eq] at he
    exact he.symm
  · funext t
    simpa only [Function.comp_apply, Sym2LabeledGraph.toLabeledGraph] using htype t

/-- Conversely, a labeled `∼sf` equivalence yields a single permutation that
preserves both underlying-edge membership and the type embedding.  (Labeled
analogue of `edge_mem_iff_of_eqv`, keeping the *same* `φ` for both facts.) -/
theorem exists_equiv_of_sym2LabeledGraphEqv {k n : ℕ} {σ : Sym2FlagType k}
    {G1 G2 : Sym2LabeledGraph σ n} (h : G1 ∼sf G2) :
    ∃ φ : Fin n ≃ Fin n,
      (∀ e : Sym2 (Fin n), e ∈ G1.edges ↔ Sym2.map φ e ∈ G2.edges) ∧
      (∀ t : Fin k, φ (G1.type_embed t) = G2.type_embed t) := by
  obtain ⟨iso⟩ := h
  refine ⟨iso.graph_iso.toEquiv, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with | _ a b =>
      rw [Sym2.map_pair_eq]
      simp only [← Sym2LabeledGraph.toLabeledGraph_adj_iff]
      exact (iso.graph_iso.map_adj_iff).symm
  · intro t
    have ht := congr_fun iso.type_preserve t
    simpa only [Function.comp_apply, Sym2LabeledGraph.toLabeledGraph,
      RelIso.coe_fn_toEquiv] using ht

/-- Degree-filtered typed fast isomorphism check: like `isIsoFast_bool`, but only
enumerates degree-compatible vertex maps of the underlying graphs that fix the
type embedding, and checks edge preservation via `edgesNat`/`List.contains`. -/
@[expose] def isIsoFastDeg_bool {k n : ℕ} {σ : Sym2FlagType k}
    (G1 G2 : Sym2LabeledGraph σ n) : Bool :=
  let e1 := edgesNat ⟨G1.edges, G1.edges_valid⟩
  let e2 := edgesNat ⟨G2.edges, G2.edges_valid⟩
  let d1 := (List.range n).map (degAtL e1)
  let d2 := (List.range n).map (degAtL e2)
  let eps := (allEdges n).map edgeNatPair
  ((dPerms n d1 d2).filter (fun p =>
      (List.finRange k).all (fun t => p.getD (G1.type_embed t).val 0 == (G2.type_embed t).val)))
    |>.any (fun p => eps.all (fun ep => e1.contains ep == e2.contains (permPair p ep)))

theorem isIsoFastDeg_bool_eq {k n : ℕ} {σ : Sym2FlagType k} (G1 G2 : Sym2LabeledGraph σ n) :
    isIsoFastDeg_bool G1 G2 =
      ((dPerms n ((List.range n).map (degAtL (edgesNat ⟨G1.edges, G1.edges_valid⟩)))
          ((List.range n).map (degAtL (edgesNat ⟨G2.edges, G2.edges_valid⟩)))).filter
          (fun p => (List.finRange k).all
            (fun t => p.getD (G1.type_embed t).val 0 == (G2.type_embed t).val))).any
        (fun p => ((allEdges n).map edgeNatPair).all
          (fun ep => (edgesNat ⟨G1.edges, G1.edges_valid⟩).contains ep
            == (edgesNat ⟨G2.edges, G2.edges_valid⟩).contains (permPair p ep))) := rfl

/-- Master correctness: the degree-filtered typed check decides `∼sf`. -/
theorem isIsoFastDeg_bool_eq_true_iff {k n : ℕ} {σ : Sym2FlagType k}
    (G1 G2 : Sym2LabeledGraph σ n) :
    isIsoFastDeg_bool G1 G2 = true ↔ G1 ∼sf G2 := by
  rw [isIsoFastDeg_bool_eq, List.any_eq_true]
  constructor
  · rintro ⟨p, hp_mem, hall⟩
    rw [List.all_eq_true] at hall
    rw [List.mem_filter] at hp_mem
    obtain ⟨hp_dperms, hp_type⟩ := hp_mem
    rw [mem_dPerms_iff] at hp_dperms
    obtain ⟨hplen, hplt, hpnd, _⟩ := hp_dperms
    set f : Fin n → Fin n := fun w => ⟨p.getD w.val 0, hplt w.val w.isLt⟩ with hf_def
    have hf_inj : Function.Injective f := by
      intro a b hab
      have h1 : p.getD a.val 0 = p.getD b.val 0 := congrArg Fin.val hab
      have ha : a.val < p.length := by rw [hplen]; exact a.isLt
      have hb : b.val < p.length := by rw [hplen]; exact b.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb] at h1
      simp only [Option.getD_some] at h1
      exact Fin.ext ((hpnd.getElem_inj_iff).mp h1)
    let φ : Fin n ≃ Fin n := Equiv.ofBijective f hf_inj.bijective_of_finite
    have hpφ : ∀ w : Fin n, p.getD w.val 0 = (φ w).val := fun w => rfl
    have hedge : ∀ e : Sym2 (Fin n), e ∈ G1.edges ↔ Sym2.map φ e ∈ G2.edges := by
      intro e
      by_cases hd : e.IsDiag
      · have h1 : e ∉ G1.edges := fun he => G1.edges_valid e he hd
        have hd2 : (Sym2.map φ e).IsDiag := (map_isDiag_iff φ e).mpr hd
        have h2 : Sym2.map φ e ∉ G2.edges := fun he => G2.edges_valid _ he hd2
        exact ⟨fun he => absurd he h1, fun he => absurd he h2⟩
      · have he_all : e ∈ allEdges n := mem_allEdges_of_not_isDiag' hd
        have hmap_all : Sym2.map φ e ∈ allEdges n :=
          mem_allEdges_of_not_isDiag' (fun hdd => hd ((map_isDiag_iff φ e).mp hdd))
        have hc := hall (edgeNatPair e) (List.mem_map.mpr ⟨e, he_all, rfl⟩)
        rw [beq_iff_eq, edgesNat_contains ⟨G1.edges, G1.edges_valid⟩ he_all,
            permPair_edgeNatPair_eq p φ hpφ e,
            edgesNat_contains ⟨G2.edges, G2.edges_valid⟩ hmap_all] at hc
        rw [← decide_eq_decide]
        exact hc
    have htype : ∀ t : Fin k, φ (G1.type_embed t) = G2.type_embed t := by
      intro t
      have hpt := (List.all_eq_true.mp hp_type) t (by simp)
      rw [beq_iff_eq] at hpt
      apply Fin.ext
      rw [← hpφ (G1.type_embed t)]
      exact hpt
    exact sym2LabeledGraphEqv_of_equiv φ hedge htype
  · intro h
    obtain ⟨φ, hedge, htype⟩ := exists_equiv_of_sym2LabeledGraphEqv h
    set p := (List.finRange n).map (fun w => (φ w).val) with hp_def
    have hpget : ∀ i (hi : i < n), p.getD i 0 = (φ ⟨i, hi⟩).val := by
      intro i hi
      rw [hp_def]
      exact map_finRange_getD (fun w => (φ w).val) 0 hi
    have hpφ : ∀ w : Fin n, p.getD w.val 0 = (φ w).val := by
      intro w; rw [hpget w.val w.isLt]
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_dPerms_iff]
        refine ⟨by rw [hp_def, List.length_map, List.length_finRange], ?_, ?_, ?_⟩
        · intro i hi; rw [hpget i hi]; exact (φ ⟨i, hi⟩).isLt
        · rw [hp_def]
          exact (List.nodup_finRange n).map (fun a b hab => φ.injective (Fin.val_injective hab))
        · intro i hi
          rw [hpget i hi, map_range_getD _ _ ((φ ⟨i, hi⟩).isLt), map_range_getD _ _ hi]
          have hd1 : degAtL (edgesNat ⟨G1.edges, G1.edges_valid⟩) i
              = degree ⟨G1.edges, G1.edges_valid⟩ ⟨i, hi⟩ :=
            degAtL_edgesNat ⟨G1.edges, G1.edges_valid⟩ ⟨i, hi⟩
          have hd2 : degAtL (edgesNat ⟨G2.edges, G2.edges_valid⟩) (φ ⟨i, hi⟩).val
              = degree ⟨G2.edges, G2.edges_valid⟩ (φ ⟨i, hi⟩) :=
            degAtL_edgesNat ⟨G2.edges, G2.edges_valid⟩ (φ ⟨i, hi⟩)
          rw [hd1, hd2]
          exact (degree_eq_of_eqv φ hedge ⟨i, hi⟩).symm
      · rw [List.all_eq_true]
        intro t _
        rw [beq_iff_eq, hpφ (G1.type_embed t), htype t]
    · rw [List.all_eq_true]
      intro ep hep
      rw [List.mem_map] at hep
      obtain ⟨e, he_all, rfl⟩ := hep
      have hmap_all : Sym2.map φ e ∈ allEdges n :=
        mem_allEdges_of_not_isDiag' (fun hdd =>
          not_isDiag_of_mem_allEdges he_all ((map_isDiag_iff φ e).mp hdd))
      rw [beq_iff_eq, edgesNat_contains ⟨G1.edges, G1.edges_valid⟩ he_all,
          permPair_edgeNatPair_eq p φ hpφ e,
          edgesNat_contains ⟨G2.edges, G2.edges_valid⟩ hmap_all, decide_eq_decide]
      exact hedge e

theorem isIsoFastDeg_bool_true_correct {k n : ℕ} {σ : Sym2FlagType k}
    {G1 G2 : Sym2LabeledGraph σ n} (h : isIsoFastDeg_bool G1 G2 = true) : G1 ∼sf G2 :=
  (isIsoFastDeg_bool_eq_true_iff G1 G2).mp h

theorem isIsoFastDeg_bool_false_correct {k n : ℕ} {σ : Sym2FlagType k}
    {G1 G2 : Sym2LabeledGraph σ n} (h : isIsoFastDeg_bool G1 G2 = false) : ¬ (G1 ∼sf G2) := by
  intro hiso
  rw [(isIsoFastDeg_bool_eq_true_iff G1 G2).mpr hiso] at h
  exact Bool.noConfusion h

theorem isIsoFastDeg_bool_complete {k n : ℕ} {σ : Sym2FlagType k}
    {G G' : Sym2LabeledGraph σ n} (h : G ∼sf G') : isIsoFastDeg_bool G G' = true :=
  (isIsoFastDeg_bool_eq_true_iff G G').mpr h

/-- High-priority decision procedure for typed flag equivalence, backed by
`isIsoFastDeg_bool` and its soundness/completeness proofs. -/
instance (priority := high) fastDecidableSym2LabeledGraphEqv {k n : Nat} {σ : Sym2FlagType k} (G₁ G₂ : Sym2LabeledGraph σ n) : Decidable (G₁ ∼sf G₂) :=
  if h : isIsoFastDeg_bool G₁ G₂ = true then
    isTrue (isIsoFastDeg_bool_true_correct h)
  else
    isFalse (isIsoFastDeg_bool_false_correct (eq_false_of_ne_true h))

/-- Finiteness of typed flags `Sym2Flag σ n`, obtained by quotienting under
the fast-decidable equivalence; enables typed flag enumeration. -/
instance (priority := high) fastFintypeSym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    Fintype (Sym2Flag σ n)
  := by
  refine @Quotient.fintype _ _ (sym2LabeledGraphSetoid σ n) ?_
  intro G G'
  exact fastDecidableSym2LabeledGraphEqv G G'

/-- Decidable equality on typed flags via the fast iso check, used to
deduplicate typed flags in the loader macros. -/
instance (priority := high) fastDecidableSym2FlagEqv
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    DecidableEq (Sym2Flag σ n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  exact fastDecidableSym2LabeledGraphEqv G G'

end FlagAlgebras.Compute
