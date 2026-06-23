import LeanFlagAlgebras.FlagAlgebra.Compute.IsoInvariants
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange
import Init.Data.List.Find

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
    (hπ : π ∈ (getNonTypeVerts n k embed).permutations) :
    π.length = (getNonTypeVerts n k embed).length := by
  exact (List.mem_permutations.mp hπ).length_eq

lemma perm_nodup_of_mem_getNonTypeVerts_permutations
    {n k : Nat} {embed : Fin k → Fin n} {π : List (Fin n)}
    (hπ : π ∈ (getNonTypeVerts n k embed).permutations) :
    π.Nodup := by
  exact (List.mem_permutations.mp hπ).nodup_iff.mpr (getNonTypeVerts_nodup embed)

/-- A computable fast isomorphism check for two Sym2Graphs (empty typed) -/
def isEmptyIsoFast_bool {n : Nat} (G₁ G₂ : Sym2Graph n) : Bool :=
  if G₁.edges.card != G₂.edges.card then false
  else
    let perms := (List.finRange n).permutations
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

/-- High-priority decision procedure for empty-typed flag equivalence,
backed by `isEmptyIsoFast_bool` and its soundness/completeness proofs. -/
instance (priority := high) fastDecidableSym2GraphEqv
    {n : Nat} (G₁ G₂ : Sym2Graph n) : Decidable (G₁ ∼sf G₂) :=
  if h : isEmptyIsoFast_bool G₁ G₂ = true then
    isTrue (isEmptyIsoFast_bool_true_correct h)
  else
    isFalse (isEmptyIsoFast_bool_false_correct (eq_false_of_ne_true h))

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
    let L2_perms := nonType2.permutations
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

/-- High-priority decision procedure for typed flag equivalence, backed by
`isIsoFast_bool` and its soundness/completeness proofs. -/
instance (priority := high) fastDecidableSym2LabeledGraphEqv {k n : Nat} {σ : Sym2FlagType k} (G₁ G₂ : Sym2LabeledGraph σ n) : Decidable (G₁ ∼sf G₂) :=
  if h : isIsoFast_bool G₁ G₂ = true then
    isTrue (isIsoFast_bool_true_correct h)
  else
    isFalse (isIsoFast_bool_false_correct (eq_false_of_ne_true h))

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
