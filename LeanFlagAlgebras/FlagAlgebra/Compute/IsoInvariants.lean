module

public import LeanFlagAlgebras.FlagAlgebra.Compute.Basic
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.Sort

@[expose] public section

/-! # Isomorphism invariants for computable graph encodings

This module collects small, computable invariants and edge-transport lemmas used
to avoid unnecessary isomorphism searches.  `FastIso` uses the edge-count part
as an early exit for a single pair of graphs, while `FlagEnumeration` caches the
stronger degree key across a whole deduplication fold.
-/

namespace FlagAlgebras.Compute

open List

/-- `Sym2.map` of an injective function is injective. -/
theorem sym2_map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro x y
  induction x using Sym2.ind with | _ a b =>
  induction y using Sym2.ind with | _ c d =>
  intro h
  rw [Sym2.map_pair_eq, Sym2.map_pair_eq, Sym2.eq_iff] at h
  rw [Sym2.eq_iff]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hf h1, hf h2⟩
  · exact Or.inr ⟨hf h1, hf h2⟩

/-- A vertex permutation that preserves edge membership induces a `∼sf` equivalence. -/
theorem sym2GraphEqv_of_equiv {n : ℕ} {G R : Sym2Graph n} (φ : Fin n ≃ Fin n)
    (h : ∀ e : Sym2 (Fin n), e ∈ G.edges ↔ Sym2.map φ e ∈ R.edges) : G ∼sf R := by
  refine Nonempty.intro { graph_iso := ?_, type_preserve := ?_ }
  · refine { toEquiv := φ, map_rel_iff' := ?_ }
    intro a b
    rw [Sym2Graph.toLabeledGraph_adj_iff, Sym2Graph.toLabeledGraph_adj_iff]
    have he := h s(a, b)
    rw [Sym2.map_pair_eq] at he
    exact he.symm
  · ext z
    exact Fin.elim0 z

/-- Conversely, a `∼sf` equivalence yields an edge-membership-preserving permutation. -/
theorem edge_mem_iff_of_eqv {n : ℕ} {G R : Sym2Graph n} (h : G ∼sf R) :
    ∃ φ : Fin n ≃ Fin n, ∀ e : Sym2 (Fin n), e ∈ G.edges ↔ Sym2.map φ e ∈ R.edges := by
  have φ := h.some.graph_iso
  simp only [Sym2Graph.toLabeledGraph] at φ
  refine ⟨φ.toEquiv, ?_⟩
  intro e
  constructor
  · intro he1
    have he1' : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).edgeSet := by
      simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
        (And.intro he1 (G.edges_valid e he1))
    have he2' : Sym2.map φ.toEquiv e ∈
        (SimpleGraph.fromEdgeSet (SetLike.coe R.edges)).edgeSet :=
      (φ.map_mem_edgeSet_iff).2 he1'
    have : Sym2.map φ.toEquiv e ∈ R.edges ∧ ¬(Sym2.map φ.toEquiv e).IsDiag := by
      simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using he2'
    exact this.1
  · intro he2
    have he2' : Sym2.map φ.toEquiv e ∈
        (SimpleGraph.fromEdgeSet (SetLike.coe R.edges)).edgeSet := by
      simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using
        (And.intro he2 (R.edges_valid (Sym2.map φ.toEquiv e) he2))
    have he1' : e ∈ (SimpleGraph.fromEdgeSet (SetLike.coe G.edges)).edgeSet :=
      (φ.map_mem_edgeSet_iff).1 he2'
    have : e ∈ G.edges ∧ ¬e.IsDiag := by
      simpa [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet_iff_isDiag] using he1'
    exact this.1

/-! ### Kernel-reducible insertion sort

`decide +kernel` in a downstream `module` file cannot reduce Mathlib's
`List.insertionSort`/`List.orderedInsert`: those ship with `hasValue = false`
(their bodies are not exposed across the module boundary), so kernel reduction
gets stuck the moment the enumeration sorts anything.  `native_decide` sidesteps
this by running compiled code, but that adds the `Lean.ofReduceBool`/
`Lean.trustCompiler` axioms.  To keep the flag enumeration kernel-reducible (and
hence `decide +kernel`-provable with no compiled-evaluation axioms), we use an
**exposed** copy of insertion sort here — identical to `List.insertionSort`, but
with a body the kernel can unfold in importing modules. -/

/-- Kernel-reducible ordered insertion: an `@[expose]` copy of
`List.orderedInsert`. -/
@[expose] def korderedInsert {α : Type _} (r : α → α → Prop) [DecidableRel r] (a : α) :
    List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: korderedInsert r a l

/-- Kernel-reducible insertion sort: an `@[expose]` copy of `List.insertionSort`
(see the note above on why Mathlib's is unusable under `decide +kernel`). -/
@[expose] def ksort {α : Type _} (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | b :: l => korderedInsert r b (ksort r l)

theorem korderedInsert_perm {α} (r : α → α → Prop) [DecidableRel r] (a : α) :
    ∀ l, korderedInsert r a l ~ a :: l
  | [] => List.Perm.refl _
  | b :: l => by
    unfold korderedInsert
    by_cases h : r a b
    · simp [h]
    · simp only [h, if_false]
      exact ((korderedInsert_perm r a l).cons b).trans (List.Perm.swap a b l)

/-- `ksort` is a permutation of its input (as `List.insertionSort` is). -/
theorem ksort_perm {α} (r : α → α → Prop) [DecidableRel r] :
    ∀ l : List α, ksort r l ~ l
  | [] => List.Perm.refl _
  | b :: l => by
    unfold ksort
    exact (korderedInsert_perm r b (ksort r l)).trans ((ksort_perm r l).cons b)

theorem korderedInsert_sorted {α} (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (a : α) {l : List α} (hl : List.Pairwise r l) :
    List.Pairwise r (korderedInsert r a l) := by
  induction l with
  | nil => simp [korderedInsert]
  | cons b t ih =>
    unfold korderedInsert
    by_cases h : r a b
    · rw [if_pos h]
      refine List.Pairwise.cons (fun x hx => ?_) hl
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h
      · exact _root_.trans h (List.rel_of_pairwise_cons hl hx)
    · rw [if_neg h]
      have ih' := ih (List.pairwise_cons.mp hl).2
      have hba : r b a := (Std.Total.total a b).resolve_left h
      have hmem : ∀ x, x ∈ korderedInsert r a t → x = a ∨ x ∈ t :=
        fun x hx => List.mem_cons.mp ((korderedInsert_perm r a t).mem_iff.mp hx)
      refine List.Pairwise.cons (fun x hx => ?_) ih'
      rcases hmem x hx with rfl | hx'
      · exact hba
      · exact List.rel_of_pairwise_cons hl hx'

/-- `ksort` produces a sorted list (as `List.insertionSort` does), for a total,
transitive decidable relation. -/
theorem ksort_sorted {α} (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r] :
    ∀ l : List α, List.Pairwise r (ksort r l)
  | [] => List.Pairwise.nil
  | b :: l => korderedInsert_sorted r b (ksort_sorted r l)

/-- The degree of vertex `v` in `G`: the number of edges incident to `v`. -/
def degree {n : ℕ} (G : Sym2Graph n) (v : Fin n) : ℕ :=
  (G.edges.filter (fun e => v ∈ e)).card

/-- The sorted degree sequence of `G`. -/
def degSeq {n : ℕ} (G : Sym2Graph n) : List ℕ :=
  ksort (· ≤ ·) ((List.finRange n).map (degree G))

/-- A cheap, computable isomorphism invariant: edge count and sorted degree sequence. -/
def degKey {n : ℕ} (G : Sym2Graph n) : ℕ × List ℕ :=
  (G.edges.card, degSeq G)

/-- The cheap labeled key is the underlying graph's `degKey`. -/
def labeledDegKey {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    (G : Sym2LabeledGraph σ n) : ℕ × List ℕ :=
  degKey ⟨G.edges, G.edges_valid⟩

/-- Vertex membership transports along `Sym2.map` of an equivalence. -/
theorem mem_map_equiv_iff {n : ℕ} (φ : Fin n ≃ Fin n) (v : Fin n) (e : Sym2 (Fin n)) :
    φ v ∈ Sym2.map φ e ↔ v ∈ e := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨a, hae, hav⟩
    rwa [φ.injective hav] at hae
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Degrees transport along an edge-membership-preserving permutation. -/
theorem degree_eq_of_eqv {n : ℕ} {G H : Sym2Graph n} (φ : Fin n ≃ Fin n)
    (h : ∀ e : Sym2 (Fin n), e ∈ G.edges ↔ Sym2.map φ e ∈ H.edges) (v : Fin n) :
    degree G v = degree H (φ v) := by
  have hset : H.edges.filter (fun e => φ v ∈ e)
      = (G.edges.filter (fun e => v ∈ e)).image (Sym2.map φ) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨he'H, hφv⟩
      refine ⟨Sym2.map φ.symm e', ⟨?_, ?_⟩, ?_⟩
      · have he : Sym2.map φ (Sym2.map φ.symm e') = e' := by rw [Sym2.map_map]; simp
        rw [h (Sym2.map φ.symm e'), he]; exact he'H
      · have hh := mem_map_equiv_iff φ.symm (φ v) e'
        rw [Equiv.symm_apply_apply] at hh
        exact hh.mpr hφv
      · rw [Sym2.map_map]; simp
    · rintro ⟨e, ⟨heG, hve⟩, rfl⟩
      exact ⟨(h e).mp heG, (mem_map_equiv_iff φ v e).mpr hve⟩
  unfold degree
  rw [hset, Finset.card_image_of_injective _ (sym2_map_injective φ.injective)]

/-- Edge counts agree under an edge-membership-preserving permutation. -/
theorem edges_card_eq_of_eqv {n : ℕ} {G H : Sym2Graph n} (φ : Fin n ≃ Fin n)
    (h : ∀ e : Sym2 (Fin n), e ∈ G.edges ↔ Sym2.map φ e ∈ H.edges) :
    G.edges.card = H.edges.card := by
  have hset : H.edges = G.edges.image (Sym2.map φ) := by
    ext e'
    simp only [Finset.mem_image]
    constructor
    · intro he'H
      refine ⟨Sym2.map φ.symm e', ?_, ?_⟩
      · have he : Sym2.map φ (Sym2.map φ.symm e') = e' := by rw [Sym2.map_map]; simp
        rw [h (Sym2.map φ.symm e'), he]; exact he'H
      · rw [Sym2.map_map]; simp
    · rintro ⟨e, heG, rfl⟩
      exact (h e).mp heG
  rw [hset, Finset.card_image_of_injective _ (sym2_map_injective φ.injective)]

/-- Sorted degree sequences agree under iso (their multisets coincide). -/
theorem degSeq_eq_of_eqv {n : ℕ} {G H : Sym2Graph n} (φ : Fin n ≃ Fin n)
    (h : ∀ e : Sym2 (Fin n), e ∈ G.edges ↔ Sym2.map φ e ∈ H.edges) :
    degSeq G = degSeq H := by
  have hperm : (List.finRange n).map (degree G) ~ (List.finRange n).map (degree H) := by
    have hfun : degree G = fun v => degree H (φ v) := by
      funext v; exact degree_eq_of_eqv φ h v
    rw [hfun]
    simpa [List.map_map, Function.comp_def] using
      (Equiv.Perm.map_finRange_perm (φ : Equiv.Perm (Fin n))).map (degree H)
  unfold degSeq
  exact List.Perm.eq_of_pairwise' (ksort_sorted _ _)
    (ksort_sorted _ _)
    ((ksort_perm _ _).trans (hperm.trans (ksort_perm _ _).symm))

/-- The cheap graph key is an isomorphism invariant. -/
theorem degKey_iso_invariant {n : ℕ} {G H : Sym2Graph n} (hh : G ∼sf H) :
    degKey G = degKey H := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv hh
  unfold degKey
  rw [edges_card_eq_of_eqv φ hφ, degSeq_eq_of_eqv φ hφ]

/-- The edge-count part of `degKey` is an isomorphism invariant. -/
theorem edgeCount_eq_of_eqv {n : ℕ} {G H : Sym2Graph n} (hh : G ∼sf H) :
    G.edges.card = H.edges.card :=
  congrArg Prod.fst (degKey_iso_invariant hh)

/-- A labeled `∼sf` restricts to an `∼sf` of the underlying empty-typed graphs. -/
theorem underlying_eqv_of_labeled_eqv {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G H : Sym2LabeledGraph σ n} (h : G ∼sf H) :
    (⟨G.edges, G.edges_valid⟩ : Sym2Graph n) ∼sf ⟨H.edges, H.edges_valid⟩ :=
  ⟨{ graph_iso := h.some.graph_iso
     type_preserve := by ext z; exact Fin.elim0 z }⟩

/-- The cheap labeled key is an isomorphism invariant. -/
theorem labeledDegKey_iso_invariant {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G H : Sym2LabeledGraph σ n} (hh : G ∼sf H) :
    labeledDegKey G = labeledDegKey H :=
  degKey_iso_invariant (underlying_eqv_of_labeled_eqv hh)

/-- The edge-count part of `labeledDegKey` is an isomorphism invariant. -/
theorem labeledEdgeCount_eq_of_eqv {k : ℕ} {σ : Sym2FlagType k} {n : ℕ}
    {G H : Sym2LabeledGraph σ n} (hh : G ∼sf H) :
    G.edges.card = H.edges.card :=
  edgeCount_eq_of_eqv (underlying_eqv_of_labeled_eqv hh)

end FlagAlgebras.Compute
