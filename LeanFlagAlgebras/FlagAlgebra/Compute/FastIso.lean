import LeanFlagAlgebras.FlagAlgebra.Compute.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange

namespace FlagAlgebras.Compute

def allEdges (n : Nat) : List (Sym2 (Fin n)) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if i.val < j.val then some (Sym2.mk (i, j)) else none

/-- Helper to map an edge under a permutation array (List of size n) -/
def applyPermEdge {n : Nat} (perm : List (Fin n)) (e : Sym2 (Fin n)) : Sym2 (Fin n) :=
  Sym2.map (fun v => (perm[v.val]?).getD v) e

def myIndexOf {α : Type} [BEq α] (a : α) : List α → Nat → Option Nat
  | [], _ => none
  | x::xs, i => if x == a then some i else myIndexOf a xs (i+1)

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

def getNonTypeVerts (n k : Nat) (embed : Fin k → Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v =>
    (List.finRange k).all fun i => v.val != (embed i).val

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

theorem isEmptyIsoFast_bool_true_correct
    {n : ℕ} {G₁ G₂ : Sym2Graph n} (h : isEmptyIsoFast_bool G₁ G₂ = true)
    : G₁ ∼sf G₂
  := by
  simp [isEmptyIsoFast_bool] at h
  obtain ⟨_, π, hπ, h⟩ := h
  apply Nonempty.intro
  refine { graph_iso := ?_, type_preserve := ?_ }
  · simp [Sym2Graph.toLabeledGraph]
    sorry
  · sorry

theorem isEmptyIsoFast_bool_false_correct
    {n : Nat} {G₁ G₂ : Sym2Graph n} (h : isEmptyIsoFast_bool G₁ G₂ = false)
    : ¬ (G₁ ∼sf G₂)
  := by
  contrapose h
  have φ := h.some.graph_iso
  simp [isEmptyIsoFast_bool]
  refine ⟨sym2Graph_card_edges_eq_of_eqv h, ?_⟩
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

instance (priority := high) fastDecidableSym2GraphEqv
    {n : Nat} (G₁ G₂ : Sym2Graph n) : Decidable (G₁ ∼sf G₂) :=
  if h : isEmptyIsoFast_bool G₁ G₂ = true then
    isTrue (isEmptyIsoFast_bool_true_correct h)
  else
    isFalse (isEmptyIsoFast_bool_false_correct (eq_false_of_ne_true h))

instance (priority := high) fastFintypeSym2EmptyTypedFlag
    {n : ℕ} : Fintype (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.fintype _ _ (Sym2GraphSetoid n) ?_
  intro G G'
  exact fastDecidableSym2GraphEqv G G'

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

theorem isIsoFast_bool_true_correct
    {k n : ℕ} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : isIsoFast_bool G₁ G₂ = true) : G₁ ∼sf G₂
  := by
  sorry

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

lemma buildFullMap_edge_witness_of_eqv
    {k n : Nat} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : G₁ ∼sf G₂) :
    ∀ e ∈ allEdges n,
      e ∈ G₁.edges ↔
        applyPermEdge
          (buildFullMap n k G₁.type_embed G₂.type_embed
            (getNonTypeVerts n k G₁.type_embed)
            ((getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso)) e ∈ G₂.edges := by
  intro e he
  have hEdge : e ∈ G₁.edges ↔ e.map h.some.graph_iso ∈ G₂.edges := by
    constructor
    · intro he1
      have he1' : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₁.edges)).edgeSet := by
        simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
          (And.intro he1 (G₁.edges_valid e he1))
      have he2' : e.map h.some.graph_iso.toEquiv ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₂.edges)).edgeSet :=
        (h.some.graph_iso.map_mem_edgeSet_iff).2 he1'
      exact (by
        have : e.map h.some.graph_iso.toEquiv ∈ G₂.edges ∧ ¬(e.map h.some.graph_iso.toEquiv).IsDiag := by
          simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using he2'
        exact this.1)
    · intro he2
      have he2' : e.map h.some.graph_iso.toEquiv ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₂.edges)).edgeSet := by
        simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
          (And.intro he2 (G₂.edges_valid (e.map h.some.graph_iso.toEquiv) he2))
      have he1' : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G₁.edges)).edgeSet :=
        (h.some.graph_iso.map_mem_edgeSet_iff).1 he2'
      exact (by
        have : e ∈ G₁.edges ∧ ¬e.IsDiag := by
          simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using he1'
        exact this.1)
  have hfull : ∀ v : Fin n,
      ((buildFullMap n k G₁.type_embed G₂.type_embed
        (getNonTypeVerts n k G₁.type_embed)
        ((getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso))[v.val]?).getD v
      = h.some.graph_iso v := by
    intro v
    simp [buildFullMap]
    sorry
  have hMapEq :
      applyPermEdge
        (buildFullMap n k G₁.type_embed G₂.type_embed
          (getNonTypeVerts n k G₁.type_embed)
          ((getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso)) e
      = e.map h.some.graph_iso.toEquiv := by
    simp [applyPermEdge, hfull]
  simpa [hMapEq] using hEdge

theorem isIsoFast_bool_false_correct
    {k n : Nat} {σ : Sym2FlagType k} {G₁ G₂ : Sym2LabeledGraph σ n}
    (h : isIsoFast_bool G₁ G₂ = false) : ¬ (G₁ ∼sf G₂)
  := by
  contrapose h
  have φ := h.some
  have φg := φ.graph_iso
  simp [isIsoFast_bool]
  refine ⟨sym2LabeledGraph_card_edges_eq_of_eqv h, ?_⟩
  use (getNonTypeVerts n k G₁.type_embed).map h.some.graph_iso
  exact ⟨nonType_perm_witness_of_eqv h, buildFullMap_edge_witness_of_eqv h⟩

instance (priority := high) fastDecidableSym2LabeledGraphEqv {k n : Nat} {σ : Sym2FlagType k} (G₁ G₂ : Sym2LabeledGraph σ n) : Decidable (G₁ ∼sf G₂) :=
  if h : isIsoFast_bool G₁ G₂ = true then
    isTrue (isIsoFast_bool_true_correct h)
  else
    isFalse (isIsoFast_bool_false_correct (eq_false_of_ne_true h))

instance (priority := high) fastFintypeSym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    Fintype (Sym2Flag σ n)
  := by
  refine @Quotient.fintype _ _ (sym2LabeledGraphSetoid σ n) ?_
  intro G G'
  exact fastDecidableSym2LabeledGraphEqv G G'

instance (priority := high) fastDecidableSym2FlagEqv
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    DecidableEq (Sym2Flag σ n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  exact fastDecidableSym2LabeledGraphEqv G G'

end FlagAlgebras.Compute
