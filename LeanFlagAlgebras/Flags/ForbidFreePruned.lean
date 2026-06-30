import LeanFlagAlgebras.FlagAlgebra.Compute.FlagEnumeration
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

/-! # Genuine pruned augmentation (K₃-free, empty-typed graph level)

A *true* pruned augmentation: it builds the triangle-free `n`-vertex graphs by
augmenting only triangle-free `(n-1)`-vertex representatives and keeping only the
triangle-free results, so the forbidden (triangle-containing) graphs are **never
generated**. Contrast with the filter-based forbid-free generator in
`ForbidFreeGenerator.lean`, which computes the full enumeration and filters it.

We use a *combinatorial* triangle predicate `hasTri` (decidable), for which the two
facts the completeness induction needs — isomorphism invariance and monotonicity
under vertex deletion (`restrict`) — are clean to prove. The remaining step needed to
plug this into the forbid bridges, namely `triFree G ↔ flagDensity₁ K3 (unlabel ⟦G⟧) = 0`
(combinatorial vs. analytic forbid-freeness), is **not** proved here; see the note at
the end of the file.
-/

namespace FlagAlgebras.Compute

variable {n : ℕ}

/-- `G` contains a triangle: three distinct, pairwise-adjacent vertices. -/
def hasTri (G : Sym2Graph n) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    s(a, b) ∈ G.edges ∧ s(a, c) ∈ G.edges ∧ s(b, c) ∈ G.edges

instance (G : Sym2Graph n) : Decidable (hasTri G) := by unfold hasTri; infer_instance

/-- Boolean triangle-free test. -/
def triFreeB (G : Sym2Graph n) : Bool := !decide (hasTri G)

theorem triFreeB_eq_true {G : Sym2Graph n} : triFreeB G = true ↔ ¬ hasTri G := by
  simp [triFreeB]

/-- All triangle-free one-vertex augmentations of `G`. -/
def augmentAllTriFree (G : Sym2Graph n) : List (Sym2Graph (n + 1)) :=
  (augmentAll G).filter triFreeB

/-- Pruned augmentation generator: augment only triangle-free representatives and keep
only the triangle-free augmentations. Never builds a triangle-containing graph. -/
def augRepsTriFree : (n : ℕ) → List (Sym2Graph n)
  | 0 => [⟨∅, by simp⟩]
  | n + 1 => ((augRepsTriFree n).flatMap augmentAllTriFree).foldl dedupStep []

/-- `hasTri` is an isomorphism invariant: a triangle transports along the edge-preserving
permutation given by `G ∼sf R`. -/
theorem hasTri_of_eqv {G R : Sym2Graph n} (h : G ∼sf R) (hG : hasTri G) : hasTri R := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv h
  obtain ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩ := hG
  refine ⟨φ a, φ b, φ c,
    fun he => hab (φ.injective he), fun he => hac (φ.injective he),
    fun he => hbc (φ.injective he), ?_, ?_, ?_⟩
  · have := (hφ s(a, b)).mp eab; rwa [Sym2.map_pair_eq] at this
  · have := (hφ s(a, c)).mp eac; rwa [Sym2.map_pair_eq] at this
  · have := (hφ s(b, c)).mp ebc; rwa [Sym2.map_pair_eq] at this

/-- **Vertex-deletion monotonicity.** A triangle in the restriction (first `n` vertices)
is a triangle in the whole graph; contrapositively, triangle-freeness is preserved by
`restrict`. This is the key fact that lets the pruned recursion never look at the
forbidden graphs. -/
theorem hasTri_of_restrict {H : Sym2Graph (n + 1)} (h : hasTri (restrict H)) : hasTri H := by
  obtain ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩ := h
  refine ⟨Fin.castSucc a, Fin.castSucc b, Fin.castSucc c,
    fun he => hab (Fin.castSucc_injective n he),
    fun he => hac (Fin.castSucc_injective n he),
    fun he => hbc (Fin.castSucc_injective n he), ?_, ?_, ?_⟩
  · have := ((mem_restrict_edges H _).mp eab).2; rwa [Sym2.map_pair_eq] at this
  · have := ((mem_restrict_edges H _).mp eac).2; rwa [Sym2.map_pair_eq] at this
  · have := ((mem_restrict_edges H _).mp ebc).2; rwa [Sym2.map_pair_eq] at this

/-- **Completeness of the pruned generator.** Every triangle-free graph is `∼sf` to a
representative produced by `augRepsTriFree` — even though the generator never enumerated
the triangle-containing graphs. Mirrors `augReps_complete`, using monotonicity to descend
to the restriction and iso-invariance to keep the matched augmentation triangle-free. -/
theorem augRepsTriFree_complete : ∀ (n : ℕ) (G : Sym2Graph n), ¬ hasTri G →
    ∃ R ∈ augRepsTriFree n, G ∼sf R
  | 0 => by
    intro G _
    haveI : IsEmpty (Sym2 (Fin 0)) :=
      ⟨fun e => by induction e using Sym2.ind with | _ a b => exact a.elim0⟩
    refine ⟨⟨∅, by simp⟩, List.mem_cons_self, ?_⟩
    exact sym2GraphEqv_of_equiv (Equiv.refl (Fin 0)) (fun e => isEmptyElim e)
  | n + 1 => by
    intro H hH
    have hRestr : ¬ hasTri (restrict H) := fun htri => hH (hasTri_of_restrict htri)
    obtain ⟨R₀, hR₀mem, hR₀iso⟩ := augRepsTriFree_complete n (restrict H) hRestr
    obtain ⟨S', hS'⟩ := augment_transport hR₀iso (neighborsOfLast H)
    have hHiso : H ∼sf augment R₀ S' := by rw [augment_restrict_eq H]; exact hS'
    have hAug : ¬ hasTri (augment R₀ S') :=
      fun htri => hH (hasTri_of_eqv (Sym2GraphEqv.symm hHiso) htri)
    have hmemFilt : augment R₀ S' ∈ augmentAllTriFree R₀ := by
      rw [augmentAllTriFree]
      exact List.mem_filter.mpr ⟨mem_augmentAll R₀ S', triFreeB_eq_true.mpr hAug⟩
    have hmemFlat : augment R₀ S' ∈ (augRepsTriFree n).flatMap augmentAllTriFree :=
      List.mem_flatMap.mpr ⟨R₀, hR₀mem, hmemFilt⟩
    obtain ⟨R, hRmem, hRiso⟩ :=
      foldl_dedupStep_complete ((augRepsTriFree n).flatMap augmentAllTriFree) []
        (augment R₀ S') hmemFlat
    exact ⟨R, hRmem, Sym2GraphEqv.trans hHiso hRiso⟩

-- Correctness validation (each reduces only the pruned generation, never the full
-- enumeration): the pruned generator produces exactly the known K₃-free class counts
-- (7 of 11 at n=4, 14 of 34 at n=5, 38 of 156 at n=6).
example : (augRepsTriFree 4).length = 7 := by native_decide
example : (augRepsTriFree 5).length = 14 := by native_decide
example : (augRepsTriFree 6).length = 38 := by native_decide

/-! ## K₃ density bridge (Task 1)

The bridge connecting the *combinatorial* triangle predicate `hasTri` to the *analytic*
(induced) K₃-density used by the forbid-free framework:

  `hasTri G ↔ sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ ⟦G⟧ ≠ 0`.

The density `sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ ⟦G⟧` is `count / C(n,3)`, where
`count` is the number of induced subgraphs of `G` isomorphic to the triangle; the heart
of the proof is that such an induced copy exists iff `G` has three pairwise-adjacent
vertices. -/

/-- The triangle `K₃` as a computable graph on `Fin 3` (all three edges). -/
def triangleGraph : Sym2Graph 3 where
  edges := {s(0, 1), s(0, 2), s(1, 2)}
  edges_valid := by decide

/-- `triangleGraph` decodes to the complete graph on `Fin 3`: adjacency is `≠`. -/
theorem triangleGraph_adj_iff (u v : Fin 3) :
    triangleGraph.toLabeledGraph.graph.Adj u v ↔ u ≠ v := by
  rw [Sym2Graph.toLabeledGraph_adj_iff]
  fin_cases u <;> fin_cases v <;> decide

/-- Adjacency in the induced subgraph picked out by `H` is exactly edge-membership in
`G` (both endpoints already lie in `H.verts`). -/
theorem inducedSubgraph_coe_adj_iff {n : ℕ} {G : Sym2Graph n} (H : Sym2InducedSubgraph G)
    (x y : H.toLabeledSubgraph.subgraph.verts) :
    H.toLabeledSubgraph.coe.graph.Adj x y ↔ s(x.val, y.val) ∈ G.edges := by
  rw [LabeledSubgraph.coe_adj_iff]
  show s(x.val, y.val) ∈ Sym2InducedSubgraph.edges H ↔ s(x.val, y.val) ∈ G.edges
  rw [Sym2InducedSubgraph.edges, Finset.mem_filter]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro w hw
  rw [Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · exact Finset.mem_coe.mp x.property
  · exact Finset.mem_coe.mp y.property

/-- A complete graph on a 3-element vertex type is isomorphic to `triangleGraph`'s
decoded graph. Any vertex bijection works, since both graphs have adjacency `= (· ≠ ·)`. -/
theorem nonempty_iso_triangleGraph {V : Type} [Fintype V] (Γ : SimpleGraph V)
    (hcard : Fintype.card V = 3) (hcomplete : ∀ x y : V, Γ.Adj x y ↔ x ≠ y) :
    Nonempty (Γ ≃g triangleGraph.toLabeledGraph.graph) := by
  let e : V ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨e, ?_⟩⟩
  intro x y
  rw [triangleGraph_adj_iff, hcomplete x y]
  exact e.injective.ne_iff

/-- **Heart of the K₃ bridge.** `G` has an induced subgraph isomorphic to the triangle
iff `G` has three distinct pairwise-adjacent vertices. -/
theorem exists_triangleIso_iff {n : ℕ} (G : Sym2Graph n) :
    (∃ H : Sym2InducedSubgraph G,
        Nonempty (H.toLabeledSubgraph.coe ≃f triangleGraph.toLabeledGraph)) ↔ hasTri G := by
  constructor
  · -- (→) an induced triangle yields three pairwise-adjacent vertices
    rintro ⟨H, ⟨φ⟩⟩
    set g := φ.graph_iso with hg
    refine ⟨(g.symm 0).val, (g.symm 1).val, (g.symm 2).val, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (g.symm.injective (Subtype.ext h))
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (g.symm.injective (Subtype.ext h))
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (g.symm.injective (Subtype.ext h))
    · rw [← inducedSubgraph_coe_adj_iff H (g.symm 0) (g.symm 1)]
      exact (g.symm.map_rel_iff).mpr ((triangleGraph_adj_iff 0 1).mpr (by decide))
    · rw [← inducedSubgraph_coe_adj_iff H (g.symm 0) (g.symm 2)]
      exact (g.symm.map_rel_iff).mpr ((triangleGraph_adj_iff 0 2).mpr (by decide))
    · rw [← inducedSubgraph_coe_adj_iff H (g.symm 1) (g.symm 2)]
      exact (g.symm.map_rel_iff).mpr ((triangleGraph_adj_iff 1 2).mpr (by decide))
  · -- (←) three pairwise-adjacent vertices yield an induced triangle on `{a, b, c}`
    rintro ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩
    have hdiag : ∀ v : Fin n, s(v, v) ∉ G.edges := fun v hv =>
      G.edges_valid _ hv (by rw [Sym2.mk_isDiag_iff])
    have hba : s(b, a) ∈ G.edges := by rw [Sym2.eq_swap]; exact eab
    have hca : s(c, a) ∈ G.edges := by rw [Sym2.eq_swap]; exact eac
    have hcb : s(c, b) ∈ G.edges := by rw [Sym2.eq_swap]; exact ebc
    have hba' : b ≠ a := hab.symm
    have hca' : c ≠ a := hac.symm
    have hcb' : c ≠ b := hbc.symm
    refine ⟨⟨{a, b, c}⟩, ?_⟩
    -- An explicit vertex bijection `↥{a,b,c} ≃ Fin 3` (any enumeration works).
    have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 :=
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    let e : ↥({a, b, c} : Finset (Fin n)) ≃ Fin 3 := (Finset.equivFin _).trans (finCongr hcard3)
    refine ⟨{ graph_iso := ⟨e, ?_⟩, type_preserve := by funext i; exact i.elim0 }⟩
    -- `map_rel_iff'`: both graphs are complete, so adjacency ↔ distinctness on `{a,b,c}`.
    intro x y
    rw [triangleGraph_adj_iff, inducedSubgraph_coe_adj_iff]
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff]
    have hx : x.val = a ∨ x.val = b ∨ x.val = c := by
      have hp := x.property
      simpa only [Sym2InducedSubgraph.toLabeledSubgraph, Finset.coe_insert,
        Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using hp
    have hy : y.val = a ∨ y.val = b ∨ y.val = c := by
      have hp := y.property
      simpa only [Sym2InducedSubgraph.toLabeledSubgraph, Finset.coe_insert,
        Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using hp
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] <;> simp_all

/-- The triangle-placement count is positive iff `G` has a triangle. (For `t = 1` the
placement predicate is just "an induced subgraph isomorphic to the triangle exists".) -/
theorem triangleCount_pos_iff {n : ℕ} (G : Sym2Graph n) :
    0 < sym2InducedSubgraphListCount (sym2GraphToList triangleGraph) G ↔ hasTri G := by
  unfold sym2InducedSubgraphListCount
  rw [Finset.card_pos, ← exists_triangleIso_iff]
  constructor
  · rintro ⟨Gl, hGl⟩
    simp only [finsetOfSym2InducedSubgraphListIsoHl, Finset.mem_filter, Finset.mem_univ,
      true_and] at hGl
    exact ⟨Gl 0, hGl.1 0⟩
  · rintro ⟨H, hH⟩
    refine ⟨fun _ => H, ?_⟩
    simp only [finsetOfSym2InducedSubgraphListIsoHl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => hH, fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- **K₃ density bridge.** `G` has a triangle iff its induced K₃-density is nonzero.
This is the analytic counterpart of the combinatorial `hasTri` predicate, and the lemma
that lets the genuine-pruning generator plug into the analytic forbid-free framework. -/
theorem hasTri_iff_triangleDensity_ne_zero {n : ℕ} (G : Sym2Graph n) :
    hasTri G ↔ sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ ⟦G⟧ ≠ 0 := by
  rw [← sym2InducedSubgraphListDensity_eq_sym2EmptyTypeFlagDensity₁]
  simp only [sym2InducedSubgraphListDensity]
  constructor
  · intro hG
    obtain ⟨a, b, c, hab, hac, hbc, _, _, _⟩ := hG
    have hn3 : 3 ≤ n := by
      have h := Finset.card_le_univ ({a, b, c} : Finset (Fin n))
      rwa [Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩, Fintype.card_fin] at h
    have hmc : multinomialCoefficient (fun _ : Fin 1 => 3) n ≠ 0 := by
      have := multinomialCoefficient_pos (fun _ : Fin 1 => 3) n (by simpa using hn3)
      omega
    have hcount : sym2InducedSubgraphListCount (sym2GraphToList triangleGraph) G ≠ 0 :=
      ((triangleCount_pos_iff G).mpr ⟨a, b, c, hab, hac, hbc, ‹_›, ‹_›, ‹_›⟩).ne'
    exact div_ne_zero (Nat.cast_ne_zero.mpr hcount) (Nat.cast_ne_zero.mpr hmc)
  · intro hne
    by_contra hG
    have hcount : sym2InducedSubgraphListCount (sym2GraphToList triangleGraph) G = 0 := by
      by_contra hc
      exact hG ((triangleCount_pos_iff G).mp (Nat.pos_of_ne_zero hc))
    rw [hcount] at hne
    simp at hne

/-- The `= 0` form of the K₃ density bridge: triangle-freeness iff zero induced K₃-density. -/
theorem not_hasTri_iff_triangleDensity_eq_zero {n : ℕ} (G : Sym2Graph n) :
    ¬ hasTri G ↔ sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ ⟦G⟧ = 0 := by
  rw [hasTri_iff_triangleDensity_ne_zero]
  exact not_ne_iff

/-! ## Wiring: the pruned generator produces exactly the analytic K₃-free flags (Task 2)

The end-to-end statement connecting the genuine-pruning generator (`augRepsTriFree`, which
never builds a triangle) to the analytic forbid-free set the framework uses — via the Task-1
bridge. A pruning-based forbid-free generation cites this in place of the full-enumeration
completeness: note it mentions neither a canonical forbidden flag nor the full enumeration. -/

/-- `dedupStep` keeps only graphs drawn from `acc` or the new graph `x`. -/
theorem dedupStep_subset {n : ℕ} (acc : List (Sym2Graph n)) (x G : Sym2Graph n) :
    G ∈ dedupStep acc x → G ∈ acc ++ [x] := by
  unfold dedupStep
  split <;> intro h
  · exact List.mem_append_left _ h
  · exact h

/-- Survivors of the `dedupStep` fold come from the input list. -/
theorem foldl_dedupStep_subset {n : ℕ} (xs : List (Sym2Graph n)) :
    ∀ (acc : List (Sym2Graph n)) (G : Sym2Graph n),
      G ∈ xs.foldl dedupStep acc → G ∈ acc ++ xs := by
  induction xs with
  | nil => intro acc G h; simpa using h
  | cons x rest ih =>
    intro acc G h
    simp only [List.foldl_cons] at h
    have h2 := ih (dedupStep acc x) G h
    rw [List.mem_append] at h2
    rcases h2 with h2 | h2
    · have h3 := dedupStep_subset acc x G h2
      rw [List.mem_append, List.mem_singleton] at h3
      rcases h3 with h3 | h3
      · exact List.mem_append_left _ h3
      · exact h3 ▸ List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)

/-- Every representative produced by the pruned generator is triangle-free. -/
theorem augRepsTriFree_triFree : ∀ (n : ℕ), ∀ R ∈ augRepsTriFree n, ¬ hasTri R := by
  intro n
  cases n with
  | zero => intro R _ htri; obtain ⟨a, _⟩ := htri; exact a.elim0
  | succ m =>
    intro R hR
    have hsub := foldl_dedupStep_subset ((augRepsTriFree m).flatMap augmentAllTriFree) [] R hR
    rw [List.nil_append, List.mem_flatMap] at hsub
    obtain ⟨_, _, hRG⟩ := hsub
    rw [augmentAllTriFree, List.mem_filter] at hRG
    exact triFreeB_eq_true.mp hRG.2

/-- The empty-typed flags produced by genuine pruning: the quotient classes of the
triangle-free representatives. -/
def prunedTriFreeFlags (n : ℕ) : List (Sym2EmptyTypedFlag n) :=
  (augRepsTriFree n).map (Quotient.mk (Sym2GraphSetoid n))

/-- **Genuine pruning is correct w.r.t. the analytic K₃-density.** The pruned generator
produces exactly the empty-typed flags of zero induced K₃-density — never enumerating any
triangle-containing graph, and without reference to any canonical forbidden flag. This is the
lemma a pruning-based `flagSetHfree_…_eq` would cite instead of the full-enumeration
`native_decide`. -/
theorem prunedTriFreeFlags_toFinset_eq (n : ℕ) :
    (prunedTriFreeFlags n).toFinset
      = Finset.univ.filter (fun S => sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ S = 0) := by
  apply Finset.ext
  intro S
  simp only [prunedTriFreeFlags, List.mem_toFinset, List.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and]
  obtain ⟨G, rfl⟩ := Quotient.exists_rep S
  rw [← not_hasTri_iff_triangleDensity_eq_zero]
  constructor
  · rintro ⟨R, hRmem, hRG⟩ htri
    exact augRepsTriFree_triFree n R hRmem
      (hasTri_of_eqv (Sym2GraphEqv.symm (Quotient.exact hRG)) htri)
  · intro hG
    obtain ⟨R, hRmem, hRiso⟩ := augRepsTriFree_complete n G hG
    exact ⟨R, hRmem, Quotient.sound (Sym2GraphEqv.symm hRiso)⟩

/-! ## Status: the combinatorial↔analytic bridge is proved (Task 1)

`not_hasTri_iff_triangleDensity_eq_zero` is the bridge between the *combinatorial* predicate
`hasTri` (used by the pruned generator) and the *analytic* induced K₃-density (used by the
forbid-free framework):

  `¬ hasTri G ↔ sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ ⟦G⟧ = 0`

(`hasTri_iff_triangleDensity_ne_zero` is the `≠ 0` form). Together with `augRepsTriFree` /
`augRepsTriFree_complete` this supplies everything needed to route the genuine-pruning
generator into the analytic completeness.

What remains (Task 2) is the *wiring*: replace the filter-based `genFlagsHfree` with the
pruned generator inside `flagSetHfree_…_eq`, identifying the pruning predicate `triFreeB`
with the framework's `isHfreeGraph` via this bridge (and the canonical K₃ flag
`⟦triangleGraph⟧ = Sym2Flag_3_0_0_3` by `Quotient.sound`). The general arbitrary-`F` lift is
Tasks 3–5 in `FORBID_PRUNING_ROADMAP.md`. -/

/-! ## Generic combinatorial core (Task 3)

A general *induced*-containment predicate `inducedContains F G`, and a pruned generator
`augRepsFreeB` that is **generic in the (Bool) H-free predicate** `q`, with its completeness
and soundness. The single forbidden graph instantiates `q := qFree F`; a finite family would
instantiate `q := fun _ G => decide (∀ F ∈ Fs, ¬ inducedContains F G)` (per D3). This
generalizes `hasTri` / `augRepsTriFree` and is the foundation for the arbitrary-`F` bridge
(Task 4) and wiring (Task 5). -/

/-- `G` contains `F` as an *induced* subgraph: an injection of `F`'s vertices into `G`'s
preserving adjacency *and* non-adjacency (the `↔`). -/
def inducedContains {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) : Prop :=
  ∃ f : Fin m ↪ Fin n, ∀ i j : Fin m, (s(f i, f j) ∈ G.edges ↔ s(i, j) ∈ F.edges)

instance {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) : Decidable (inducedContains F G) := by
  unfold inducedContains; infer_instance

/-- Induced containment is an isomorphism invariant (transport the embedding along the
edge-preserving permutation from `G ∼sf G'`). -/
theorem inducedContains_of_eqv {m n : ℕ} {F : Sym2Graph m} {G G' : Sym2Graph n}
    (h : G ∼sf G') (hG : inducedContains F G) : inducedContains F G' := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv h
  obtain ⟨f, hf⟩ := hG
  refine ⟨f.trans φ.toEmbedding, fun i j => ?_⟩
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  rw [← hf i j, hφ s(f i, f j), Sym2.map_pair_eq]

/-- **Vertex-deletion monotonicity.** An induced copy of `F` in `restrict H` is an induced
copy in `H`; contrapositively, `F`-freeness is preserved by `restrict`. -/
theorem inducedContains_of_restrict {m n : ℕ} {F : Sym2Graph m} {H : Sym2Graph (n + 1)}
    (h : inducedContains F (restrict H)) : inducedContains F H := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.trans ⟨Fin.castSucc, Fin.castSucc_injective n⟩, fun i j => ?_⟩
  simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
  rw [← hf i j, mem_restrict_edges, Sym2.map_pair_eq]
  constructor
  · intro hmem
    refine ⟨fun hd => ?_, hmem⟩
    rw [Sym2.mk_isDiag_iff] at hd
    exact H.edges_valid _ hmem (by rw [Sym2.mk_isDiag_iff]; exact congrArg Fin.castSucc hd)
  · exact fun h => h.2

/-- All `q`-free one-vertex augmentations of `G` (generic in the Bool predicate `q`). -/
def augmentAllFreeB (q : (k : ℕ) → Sym2Graph k → Bool) {n : ℕ} (G : Sym2Graph n) :
    List (Sym2Graph (n + 1)) :=
  (augmentAll G).filter (fun H => q (n + 1) H)

/-- Predicate-generic pruned generator: augment only `q`-free representatives, keep only the
`q`-free augmentations, dedup. With `q := qFree F` this never builds an `F`-containing graph;
a finite family of forbidden graphs is another instance of `q`. -/
def augRepsFreeB (q : (k : ℕ) → Sym2Graph k → Bool) : (n : ℕ) → List (Sym2Graph n)
  | 0 => [⟨∅, by simp⟩]
  | n + 1 => ((augRepsFreeB q n).flatMap (augmentAllFreeB q)).foldl dedupStep []

/-- **Completeness of the generic pruned generator.** If `q` is iso-invariant and preserved
by `restrict`, every `q`-free graph is `∼sf` to a representative produced by `augRepsFreeB q`.
Mirrors `augRepsTriFree_complete`. -/
theorem augRepsFreeB_complete (q : (k : ℕ) → Sym2Graph k → Bool)
    (hq_iso : ∀ {k : ℕ} {G G' : Sym2Graph k}, G ∼sf G' → q k G = q k G')
    (hq_restrict : ∀ {k : ℕ} {H : Sym2Graph (k + 1)}, q (k + 1) H = true → q k (restrict H) = true) :
    ∀ (n : ℕ) (G : Sym2Graph n), q n G = true → ∃ R ∈ augRepsFreeB q n, G ∼sf R
  | 0 => by
    intro G _
    haveI : IsEmpty (Sym2 (Fin 0)) :=
      ⟨fun e => by induction e using Sym2.ind with | _ a b => exact a.elim0⟩
    refine ⟨⟨∅, by simp⟩, List.mem_cons_self, ?_⟩
    exact sym2GraphEqv_of_equiv (Equiv.refl (Fin 0)) (fun e => isEmptyElim e)
  | n + 1 => by
    intro H hH
    have hRestr : q n (restrict H) = true := hq_restrict hH
    obtain ⟨R₀, hR₀mem, hR₀iso⟩ := augRepsFreeB_complete q hq_iso hq_restrict n (restrict H) hRestr
    obtain ⟨S', hS'⟩ := augment_transport hR₀iso (neighborsOfLast H)
    have hHiso : H ∼sf augment R₀ S' := by rw [augment_restrict_eq H]; exact hS'
    have hAug : q (n + 1) (augment R₀ S') = true := by rw [← hq_iso hHiso]; exact hH
    have hmemFilt : augment R₀ S' ∈ augmentAllFreeB q R₀ :=
      List.mem_filter.mpr ⟨mem_augmentAll R₀ S', hAug⟩
    have hmemFlat : augment R₀ S' ∈ (augRepsFreeB q n).flatMap (augmentAllFreeB q) :=
      List.mem_flatMap.mpr ⟨R₀, hR₀mem, hmemFilt⟩
    obtain ⟨R, hRmem, hRiso⟩ :=
      foldl_dedupStep_complete ((augRepsFreeB q n).flatMap (augmentAllFreeB q)) []
        (augment R₀ S') hmemFlat
    exact ⟨R, hRmem, Sym2GraphEqv.trans hHiso hRiso⟩

/-- **Soundness of the generic pruned generator.** Every representative it produces is
`q`-free, provided the empty base graph is (`hq0`). -/
theorem augRepsFreeB_free (q : (k : ℕ) → Sym2Graph k → Bool)
    (hq0 : q 0 (⟨∅, by simp⟩ : Sym2Graph 0) = true) :
    ∀ (n : ℕ) (R : Sym2Graph n), R ∈ augRepsFreeB q n → q n R = true := by
  intro n
  cases n with
  | zero =>
    intro R hR
    change R ∈ [(⟨∅, by simp⟩ : Sym2Graph 0)] at hR
    rw [List.mem_singleton] at hR
    subst hR
    exact hq0
  | succ m =>
    intro R hR
    have hsub := foldl_dedupStep_subset ((augRepsFreeB q m).flatMap (augmentAllFreeB q)) [] R hR
    rw [List.nil_append, List.mem_flatMap] at hsub
    obtain ⟨_, _, hRG⟩ := hsub
    rw [augmentAllFreeB, List.mem_filter] at hRG
    exact hRG.2

/-! ### Keyed (degree-prefiltered) runtime form of the pruned generator (Task 9a)

`augRepsFreeB` deduplicates with the unkeyed `dedupStep`, which iso-checks each new graph against
*all* survivors (`O(g(n)²)` `isEmptyIsoFast_bool` calls). At high `n` this dominates pruned
generation. `augRepsFreeBDeg` is the pruned analogue of `augRepsDeg` (vs `augReps`): each candidate
carries its precomputed cheap key `degKey`, and `dedupStepDeg` runs the `O(n!)` iso test only on
cheap-key collisions. The first component equals `augRepsFreeB q n` (`augRepsFreeBDeg_fst_eq`), so
all soundness/completeness reasoning stays on the unkeyed spec. -/

/-- Keyed (degree-prefiltered) runtime form of `augRepsFreeB`: identical structure, but each
candidate carries its precomputed `degKey` and the dedup prefilters by it. The first component
equals `augRepsFreeB q n` (`augRepsFreeBDeg_fst_eq`). -/
def augRepsFreeBDeg (q : (k : ℕ) → Sym2Graph k → Bool) :
    (n : ℕ) → List (Sym2Graph n × (ℕ × List ℕ))
  | 0 => [withDegKey ⟨∅, by simp⟩]
  | n + 1 =>
      ((((augRepsFreeBDeg q n).map Prod.fst).flatMap (augmentAllFreeB q)).map withDegKey).foldl
        dedupStepDeg []

/-- The keyed pruned generator's first components agree with the spec `augRepsFreeB`. Mirrors
`augRepsDeg_fst_eq`, reusing the same fold-simulation lemma `foldl_dedupStepDeg_sim` (the cheap key
`degKey` is an iso invariant, so keyed and naive dedup make identical keep/drop decisions). -/
theorem augRepsFreeBDeg_fst_eq (q : (k : ℕ) → Sym2Graph k → Bool) (n : ℕ) :
    (augRepsFreeBDeg q n).map Prod.fst = augRepsFreeB q n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show (((((augRepsFreeBDeg q m).map Prod.fst).flatMap (augmentAllFreeB q)).map withDegKey).foldl
        dedupStepDeg []).map Prod.fst
      = ((augRepsFreeB q m).flatMap (augmentAllFreeB q)).foldl dedupStep []
    rw [ih]
    exact (foldl_dedupStepDeg_sim ((augRepsFreeB q m).flatMap (augmentAllFreeB q)) [] [] rfl
      (by simp)).1

/-! ### Single forbidden graph: instantiate the generic generator with `q := qFree F`. -/

/-- The single-forbidden-graph H-free Bool predicate: `F`-free iff no induced copy of `F`. -/
def qFree {m : ℕ} (F : Sym2Graph m) : (k : ℕ) → Sym2Graph k → Bool :=
  fun _ G => !decide (inducedContains F G)

theorem qFree_eq_true {m k : ℕ} (F : Sym2Graph m) (G : Sym2Graph k) :
    qFree F k G = true ↔ ¬ inducedContains F G := by
  simp [qFree]

theorem qFree_iso {m k : ℕ} (F : Sym2Graph m) {G G' : Sym2Graph k} (h : G ∼sf G') :
    qFree F k G = qFree F k G' := by
  unfold qFree
  congr 1
  exact decide_eq_decide.mpr ⟨inducedContains_of_eqv h, inducedContains_of_eqv (Sym2GraphEqv.symm h)⟩

theorem qFree_restrict {m k : ℕ} (F : Sym2Graph m) {H : Sym2Graph (k + 1)}
    (hH : qFree F (k + 1) H = true) : qFree F k (restrict H) = true := by
  rw [qFree_eq_true] at hH ⊢
  exact mt inducedContains_of_restrict hH

/-- Completeness for a single forbidden graph: every `F`-free graph is `∼sf` a pruned rep. -/
theorem augRepsFreeB_qFree_complete {m : ℕ} (F : Sym2Graph m) (n : ℕ) (G : Sym2Graph n)
    (hG : ¬ inducedContains F G) : ∃ R ∈ augRepsFreeB (qFree F) n, G ∼sf R :=
  augRepsFreeB_complete (qFree F) (qFree_iso F) (fun {_ _} h => qFree_restrict F h) n G
    ((qFree_eq_true F G).mpr hG)

/-- Soundness for a single (nonempty) forbidden graph: every pruned rep is `F`-free. -/
theorem augRepsFreeB_qFree_free {m : ℕ} (F : Sym2Graph m) (hm : 0 < m)
    (n : ℕ) (R : Sym2Graph n) (hR : R ∈ augRepsFreeB (qFree F) n) : ¬ inducedContains F R := by
  rw [← qFree_eq_true]
  refine augRepsFreeB_free (qFree F) ?_ n R hR
  rw [qFree_eq_true]
  rintro ⟨f, _⟩
  exact (f ⟨0, hm⟩).elim0

/-! ### Finite family of forbidden graphs (per D3): another instance of the same generator. -/

/-- H-free Bool predicate for a finite family `Fs`: free of *every* `Fp ∈ Fs` (induced). The
graphs may have different sizes (`Σ m, Sym2Graph m`). -/
def qFreeFamily (Fs : List (Σ m : ℕ, Sym2Graph m)) : (k : ℕ) → Sym2Graph k → Bool :=
  fun _ G => decide (∀ Fp ∈ Fs, ¬ inducedContains Fp.2 G)

theorem qFreeFamily_iso (Fs : List (Σ m : ℕ, Sym2Graph m)) {k : ℕ} {G G' : Sym2Graph k}
    (h : G ∼sf G') : qFreeFamily Fs k G = qFreeFamily Fs k G' := by
  simp only [qFreeFamily, decide_eq_decide]
  constructor
  · exact fun hG Fp hFp => mt (inducedContains_of_eqv (Sym2GraphEqv.symm h)) (hG Fp hFp)
  · exact fun hG' Fp hFp => mt (inducedContains_of_eqv h) (hG' Fp hFp)

theorem qFreeFamily_restrict (Fs : List (Σ m : ℕ, Sym2Graph m)) {k : ℕ} {H : Sym2Graph (k + 1)}
    (hH : qFreeFamily Fs (k + 1) H = true) : qFreeFamily Fs k (restrict H) = true := by
  simp only [qFreeFamily, decide_eq_true_eq] at hH ⊢
  exact fun Fp hFp => mt inducedContains_of_restrict (hH Fp hFp)

/-- Completeness for a finite family: every graph free of all `Fp ∈ Fs` is a pruned rep. -/
theorem augRepsFreeB_qFreeFamily_complete (Fs : List (Σ m : ℕ, Sym2Graph m)) (n : ℕ)
    (G : Sym2Graph n) (hG : ∀ Fp ∈ Fs, ¬ inducedContains Fp.2 G) :
    ∃ R ∈ augRepsFreeB (qFreeFamily Fs) n, G ∼sf R :=
  augRepsFreeB_complete (qFreeFamily Fs) (qFreeFamily_iso Fs)
    (fun {_ _} h => qFreeFamily_restrict Fs h) n G
    (by simp only [qFreeFamily, decide_eq_true_eq]; exact hG)

/-! ### Validation: the pruned generator agrees with the filter (for K₄, C₄, C₅). -/

/-- `K₄` as a computable graph. -/
def K4graph : Sym2Graph 4 where
  edges := {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)}
  edges_valid := by decide

/-- The 4-cycle `C₄` as a computable graph. -/
def C4graph : Sym2Graph 4 where
  edges := {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}
  edges_valid := by decide

/-- The 5-cycle `C₅` as a computable graph. -/
def C5graph : Sym2Graph 5 where
  edges := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}
  edges_valid := by decide

-- The pruned `F`-free representative count matches the count obtained by filtering the full
-- representative list `augReps` — i.e. the generic pruning is sound and complete on these.
example : (augRepsFreeB (qFree K4graph) 4).length
    = ((augReps 4).filter (qFree K4graph 4)).length := by native_decide
example : (augRepsFreeB (qFree K4graph) 5).length
    = ((augReps 5).filter (qFree K4graph 5)).length := by native_decide
example : (augRepsFreeB (qFree C4graph) 4).length
    = ((augReps 4).filter (qFree C4graph 4)).length := by native_decide
example : (augRepsFreeB (qFree C4graph) 5).length
    = ((augReps 5).filter (qFree C4graph 5)).length := by native_decide
example : (augRepsFreeB (qFree C5graph) 5).length
    = ((augReps 5).filter (qFree C5graph 5)).length := by native_decide

-- Family: simultaneously forbidding `K₄` and `C₄` (the multi-graph instance of D3).
example : (augRepsFreeB (qFreeFamily [⟨4, K4graph⟩, ⟨4, C4graph⟩]) 5).length
    = ((augReps 5).filter (qFreeFamily [⟨4, K4graph⟩, ⟨4, C4graph⟩] 5)).length := by native_decide

/-! ## Generalized bridge (Task 4): `inducedContains F G ↔ density ≠ 0` for arbitrary `F`.

The arbitrary-`F` analogue of the Task-1 K₃ bridge: the combinatorial induced-containment
predicate equals positivity of the analytic induced `F`-density. The K₃ case is the instance
`F := triangleGraph`. The family version is the conjunction (no new bridge math). -/

/-- **General heart.** `G` has an induced subgraph isomorphic to `F` iff `G` contains `F` as
an induced subgraph (the combinatorial embedding). -/
theorem existsInducedIso_iff {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) :
    (∃ H : Sym2InducedSubgraph G, Nonempty (H.toLabeledSubgraph.coe ≃f F.toLabeledGraph))
      ↔ inducedContains F G := by
  constructor
  · -- (→) destruct the iso into an induced embedding
    rintro ⟨H, ⟨φ⟩⟩
    refine ⟨⟨fun i => (φ.graph_iso.symm i).val,
        fun a b hab => φ.graph_iso.symm.injective (Subtype.ext hab)⟩, fun i j => ?_⟩
    simp only [Function.Embedding.coeFn_mk]
    rw [← inducedSubgraph_coe_adj_iff H (φ.graph_iso.symm i) (φ.graph_iso.symm j),
        ← Sym2Graph.toLabeledGraph_adj_iff]
    exact φ.graph_iso.symm.map_rel_iff
  · -- (←) build the induced subgraph on the embedding's image, and the iso to `F`
    rintro ⟨f, hf⟩
    have hmem : ∀ i : Fin m,
        f i ∈ (⟨Finset.image f Finset.univ⟩ : Sym2InducedSubgraph G).toLabeledSubgraph.subgraph.verts := by
      intro i
      simp only [Sym2InducedSubgraph.toLabeledSubgraph, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_range]
      exact ⟨i, rfl⟩
    have hbij : Function.Bijective
        (fun i : Fin m => (⟨f i, hmem i⟩ :
          ↥((⟨Finset.image f Finset.univ⟩ : Sym2InducedSubgraph G).toLabeledSubgraph.subgraph.verts))) := by
      refine ⟨fun i j hij => f.injective (Subtype.ext_iff.mp hij), ?_⟩
      rintro ⟨v, hv⟩
      simp only [Sym2InducedSubgraph.toLabeledSubgraph, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_range] at hv
      obtain ⟨i, hi⟩ := hv
      exact ⟨i, Subtype.ext hi⟩
    refine ⟨⟨Finset.image f Finset.univ⟩, ⟨{
      graph_iso := (RelIso.mk (Equiv.ofBijective _ hbij) ?_).symm
      type_preserve := by funext i; exact i.elim0 }⟩⟩
    intro i j
    rw [inducedSubgraph_coe_adj_iff]
    show s(f i, f j) ∈ G.edges ↔ F.toLabeledGraph.graph.Adj i j
    rw [hf i j, Sym2Graph.toLabeledGraph_adj_iff]

/-- The induced-`F` placement count is positive iff `G` contains `F` as an induced subgraph.
(`sym2GraphToList F` is the length-1 list `[F]`, so this is just the heart re-expressed via
the count.) The arbitrary-`F` analogue of `triangleCount_pos_iff`. -/
theorem inducedContainsCount_pos_iff {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) :
    0 < sym2InducedSubgraphListCount (sym2GraphToList F) G ↔ inducedContains F G := by
  unfold sym2InducedSubgraphListCount
  rw [Finset.card_pos, ← existsInducedIso_iff]
  constructor
  · rintro ⟨Gl, hGl⟩
    simp only [finsetOfSym2InducedSubgraphListIsoHl, Finset.mem_filter, Finset.mem_univ,
      true_and] at hGl
    exact ⟨Gl 0, hGl.1 0⟩
  · rintro ⟨H, hH⟩
    refine ⟨fun _ => H, ?_⟩
    simp only [finsetOfSym2InducedSubgraphListIsoHl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => hH, fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- **General induced-`F` density bridge.** `G` contains `F` as an induced subgraph iff its
analytic induced `F`-density is nonzero — the arbitrary-`F` analogue of
`hasTri_iff_triangleDensity_ne_zero`. The `n < m` denominator-zero case cannot arise: an induced
containment supplies an embedding `Fin m ↪ Fin n`, hence `m ≤ n`. -/
theorem inducedContains_iff_density_ne_zero {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) :
    inducedContains F G ↔ sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧ ≠ 0 := by
  rw [← sym2InducedSubgraphListDensity_eq_sym2EmptyTypeFlagDensity₁]
  simp only [sym2InducedSubgraphListDensity]
  constructor
  · intro hG
    have hmn : m ≤ n := by
      obtain ⟨f, _⟩ := hG
      simpa using Fintype.card_le_of_embedding f
    have hmc : multinomialCoefficient (fun _ : Fin 1 => m) n ≠ 0 := by
      have := multinomialCoefficient_pos (fun _ : Fin 1 => m) n (by simpa using hmn)
      omega
    have hcount : sym2InducedSubgraphListCount (sym2GraphToList F) G ≠ 0 :=
      ((inducedContainsCount_pos_iff F G).mpr hG).ne'
    exact div_ne_zero (Nat.cast_ne_zero.mpr hcount) (Nat.cast_ne_zero.mpr hmc)
  · intro hne
    by_contra hG
    have hcount : sym2InducedSubgraphListCount (sym2GraphToList F) G = 0 := by
      by_contra hc
      exact hG ((inducedContainsCount_pos_iff F G).mp (Nat.pos_of_ne_zero hc))
    rw [hcount] at hne
    simp at hne

/-- The `= 0` form of the general bridge: `F`-freeness (no induced `F`) iff zero induced
`F`-density. This is what the genuine-pruning predicate `qFree F` plugs into. -/
theorem not_inducedContains_iff_density_eq_zero {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) :
    ¬ inducedContains F G ↔ sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧ = 0 := by
  rw [inducedContains_iff_density_ne_zero]
  exact not_ne_iff

/-- `qFree F` as the analytic density test (Bool form), via the Task-4 bridge. Lets the genuine-pruning
σ-typed wiring match the combinatorial generator predicate `qFree F` against the density-based
`isHfree` (their `hcompat`). -/
theorem qFree_eq_density_decide {m k : ℕ} (F : Sym2Graph m) (G : Sym2Graph k) :
    qFree F k G = decide (sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧ = 0) := by
  simp only [qFree, ← not_inducedContains_iff_density_eq_zero, decide_not]

/-- `qFree F` holds at the empty base for a nonempty `F` (`0 < m`): no nonempty `F` embeds in the
empty 0-vertex graph. The `hq0` hypothesis `augRepsFreeB_complete`/`genFlagsHfreePruned_toFinset_eq`
need. -/
theorem qFree_hq0 {m : ℕ} (F : Sym2Graph m) (hm : 0 < m) :
    qFree F 0 (⟨∅, by simp⟩ : Sym2Graph 0) = true := by
  rw [qFree_eq_true]
  rintro ⟨f, _⟩
  exact (f ⟨0, hm⟩).elim0

/-- **Family bridge** (per D3): `G` is free of *every* `Fp ∈ Fs` iff every induced `Fp`-density
vanishes. Just the conjunction of the single-graph bridge — no new bridge math. -/
theorem forall_not_inducedContains_iff_forall_density_eq_zero
    (Fs : List (Σ m : ℕ, Sym2Graph m)) {n : ℕ} (G : Sym2Graph n) :
    (∀ Fp ∈ Fs, ¬ inducedContains Fp.2 G)
      ↔ (∀ Fp ∈ Fs, sym2EmptyTypeFlagDensity₁ ⟦Fp.2⟧ ⟦G⟧ = 0) :=
  forall_congr' fun Fp => imp_congr_right fun _ => not_inducedContains_iff_density_eq_zero Fp.2 G

/-! ## Subgraph (non-induced) containment — arbitrary-`F` *subgraph* forbidding (Route B / G1)

`inducedContains` above forbids `F` as an **induced** pattern (adjacency `↔`). For the standard
extremal/Turán notion — forbidding `F` as a **(not necessarily induced) subgraph** — we need the
one-directional analogue: an injection preserving `F`'s edges into `G` (the host may carry extra
edges among the image). This mirrors the `inducedContains` infrastructure with `↔` weakened to `→`,
and feeds the same generic pruned generator (`augRepsFreeB`) via `qSubgraphFree`. The bridge to the
framework's `SimpleGraph.IsContained` / `forbiddenFlags` lives in `Forbid/Basic.lean` (G2). -/

/-- `G` contains `F` as a *(not necessarily induced)* subgraph: an injection of `F`'s vertices into
`G`'s that preserves `F`'s edges (only the `→` direction — contrast `inducedContains`'s `↔`). -/
def subgraphContains {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) : Prop :=
  ∃ f : Fin m ↪ Fin n, ∀ i j : Fin m, s(i, j) ∈ F.edges → s(f i, f j) ∈ G.edges

instance {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) : Decidable (subgraphContains F G) := by
  unfold subgraphContains; infer_instance

/-- Subgraph containment is an isomorphism invariant (transport the embedding along the
edge-preserving permutation from `G ∼sf G'`). Mirrors `inducedContains_of_eqv`. -/
theorem subgraphContains_of_eqv {m n : ℕ} {F : Sym2Graph m} {G G' : Sym2Graph n}
    (h : G ∼sf G') (hG : subgraphContains F G) : subgraphContains F G' := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv h
  obtain ⟨f, hf⟩ := hG
  refine ⟨f.trans φ.toEmbedding, fun i j hij => ?_⟩
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  have := (hφ s(f i, f j)).mp (hf i j hij)
  rwa [Sym2.map_pair_eq] at this

/-- **Vertex-deletion monotonicity.** A subgraph copy of `F` in `restrict H` is one in `H`;
contrapositively, subgraph-`F`-freeness is preserved by `restrict`. Mirrors
`inducedContains_of_restrict`. -/
theorem subgraphContains_of_restrict {m n : ℕ} {F : Sym2Graph m} {H : Sym2Graph (n + 1)}
    (h : subgraphContains F (restrict H)) : subgraphContains F H := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.trans ⟨Fin.castSucc, Fin.castSucc_injective n⟩, fun i j hij => ?_⟩
  simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
  have := ((mem_restrict_edges H _).mp (hf i j hij)).2
  rwa [Sym2.map_pair_eq] at this

/-- The single-forbidden-graph *subgraph*-H-free Bool predicate: free iff no subgraph copy of `F`. -/
def qSubgraphFree {m : ℕ} (F : Sym2Graph m) : (k : ℕ) → Sym2Graph k → Bool :=
  fun _ G => !decide (subgraphContains F G)

theorem qSubgraphFree_eq_true {m k : ℕ} (F : Sym2Graph m) (G : Sym2Graph k) :
    qSubgraphFree F k G = true ↔ ¬ subgraphContains F G := by simp [qSubgraphFree]

theorem qSubgraphFree_iso {m k : ℕ} (F : Sym2Graph m) {G G' : Sym2Graph k} (h : G ∼sf G') :
    qSubgraphFree F k G = qSubgraphFree F k G' := by
  unfold qSubgraphFree
  congr 1
  exact decide_eq_decide.mpr
    ⟨subgraphContains_of_eqv h, subgraphContains_of_eqv (Sym2GraphEqv.symm h)⟩

theorem qSubgraphFree_restrict {m k : ℕ} (F : Sym2Graph m) {H : Sym2Graph (k + 1)}
    (hH : qSubgraphFree F (k + 1) H = true) : qSubgraphFree F k (restrict H) = true := by
  rw [qSubgraphFree_eq_true] at hH ⊢
  exact mt subgraphContains_of_restrict hH

/-- `qSubgraphFree F` holds at the empty base for a nonempty `F` (`0 < m`). Mirrors `qFree_hq0`. -/
theorem qSubgraphFree_hq0 {m : ℕ} (F : Sym2Graph m) (hm : 0 < m) :
    qSubgraphFree F 0 (⟨∅, by simp⟩ : Sym2Graph 0) = true := by
  rw [qSubgraphFree_eq_true]
  rintro ⟨f, _⟩
  exact (f ⟨0, hm⟩).elim0

/-- Completeness: every subgraph-`F`-free graph is `∼sf` a pruned `qSubgraphFree`-rep. Mirrors
`augRepsFreeB_qFree_complete`. -/
theorem augRepsFreeB_qSubgraphFree_complete {m : ℕ} (F : Sym2Graph m) (n : ℕ) (G : Sym2Graph n)
    (hG : ¬ subgraphContains F G) : ∃ R ∈ augRepsFreeB (qSubgraphFree F) n, G ∼sf R :=
  augRepsFreeB_complete (qSubgraphFree F) (qSubgraphFree_iso F)
    (fun {_ _} h => qSubgraphFree_restrict F h) n G ((qSubgraphFree_eq_true F G).mpr hG)

/-- Soundness: every pruned `qSubgraphFree`-rep is subgraph-`F`-free (for nonempty `F`). Mirrors
`augRepsFreeB_qFree_free`. -/
theorem augRepsFreeB_qSubgraphFree_free {m : ℕ} (F : Sym2Graph m) (hm : 0 < m)
    (n : ℕ) (R : Sym2Graph n) (hR : R ∈ augRepsFreeB (qSubgraphFree F) n) :
    ¬ subgraphContains F R := by
  rw [← qSubgraphFree_eq_true]
  refine augRepsFreeB_free (qSubgraphFree F) ?_ n R hR
  rw [qSubgraphFree_eq_true]
  rintro ⟨f, _⟩
  exact (f ⟨0, hm⟩).elim0

/-- **G2 bridge (graph level).** Our combinatorial `subgraphContains F G` agrees with Mathlib's
`SimpleGraph.IsContained` between the underlying simple graphs. `IsContained A B = Nonempty (Copy A B)`
and a `Copy` is exactly an injective adjacency-preserving map `A →g B` — which, read through
`Sym2Graph.toLabeledGraph_adj_iff`, is our edge-preserving injection. This is what connects the
subgraph-free generator to the framework's `forbiddenFlags` (whose membership is `IsContained`). -/
theorem subgraphContains_iff_isContained {m n : ℕ} (F : Sym2Graph m) (G : Sym2Graph n) :
    subgraphContains F G
      ↔ SimpleGraph.IsContained F.toLabeledGraph.graph G.toLabeledGraph.graph := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨{ toHom := ⟨f, ?_⟩, injective' := f.injective }⟩
    intro a b hab
    rw [Sym2Graph.toLabeledGraph_adj_iff] at hab ⊢
    exact hf a b hab
  · rintro ⟨c⟩
    refine ⟨⟨c, c.injective⟩, fun i j hij => ?_⟩
    have hadj : G.toLabeledGraph.graph.Adj (c i) (c j) :=
      c.toHom.map_adj ((Sym2Graph.toLabeledGraph_adj_iff F i j).mpr hij)
    rwa [Sym2Graph.toLabeledGraph_adj_iff] at hadj

/-- **Edge-superset ⇒ subgraph containment** (same vertex count, via the identity embedding). The
building block for the supergraph family: any `G ⊇ H` (edge-superset on `Fin m`) subgraph-contains `H`.
This is what makes the supergraphs of `H` lie in `forbiddenFlags H` (G4). -/
theorem subgraphContains_of_edges_subset {m : ℕ} {H G : Sym2Graph m}
    (hsub : H.edges ⊆ G.edges) : subgraphContains H G := by
  refine ⟨Function.Embedding.refl (Fin m), fun i j hij => ?_⟩
  simpa using hsub hij

/-- All non-diagonal edges of `Fin m`, **computably** — the base for the supergraph enumeration,
built from `List` primitives so it avoids the noncomputable `Finset.toList`. Lives here (the
computable `Sym2` layer) so the forbid-free generator can reference it; `supergraphFamily` (the
`FinFlag`-side image) is built on top in `Forbid/CommonGraphs.lean`. -/
def allEdgesList (m : ℕ) : List (Sym2 (Fin m)) :=
  (((List.finRange m).flatMap (fun i => (List.finRange m).map (fun j => s(i, j)))).filter
    (fun e => !decide e.IsDiag)).dedup

/-- **Computable** Sym2-side supergraph list of `H`: edge-supersets `H.edges ∪ S` over sublists `S`
of the non-`H` edges. Genuinely executable (`List.sublists` / `List.map` / `Finset.union`), so the
generator can `native_decide` the subgraph-`H`-free split and the survivor filter. -/
def supergraphSym2List {m : ℕ} (H : Sym2Graph m) : List (Sym2EmptyTypedFlag m) :=
  ((allEdgesList m).filter (fun e => !decide (e ∈ H.edges))).sublists.map (fun S =>
    ⟦{ edges := H.edges ∪ (S.toFinset.filter (fun e => ¬ e.IsDiag))
       edges_valid := fun e he => by
         rcases Finset.mem_union.mp he with h | h
         · exact H.edges_valid e h
         · exact (Finset.mem_filter.mp h).2 }⟧)

/-- The **supergraph family** of `H` as a **computable** `List (FinFlag ∅ₜ)` (the `toFlag`-image of
`supergraphSym2List`). A `List` (not `Finset`) needs no `DecidableEq (FinFlag)`, and being built from
`List` primitives it stays `native_decide`-able. The finite `Fs` fed to the G3 family expansions; the
`hmem`/capstone wrappers live in `Forbid/CommonGraphs.lean`. -/
def supergraphFamily {m : ℕ} (H : Sym2Graph m) : List (FinFlag ∅ₜ) :=
  (supergraphSym2List H).map (fun s => ⟨m, s.toFlag⟩)

/-- `supergraphFamily` is the `toFlag`-image of `supergraphSym2List` — definitional. -/
theorem supergraphFamily_eq_map {m : ℕ} (H : Sym2Graph m) :
    supergraphFamily H = (supergraphSym2List H).map (fun s => (⟨m, s.toFlag⟩ : FinFlag ∅ₜ)) := rfl

/-- **Computable form of the capstone's survivor filter** (empty-typed host flags). The `FinFlag`-side
`supergraphFamily` density condition equals the fully computable `Sym2EmptyTypedFlag` one, so the
generator can decide it by `native_decide` (via `flagDensity₁_eq_sym2EmptyTypeFlagDensity₁`). -/
theorem supergraphFamily_filter_iff {m ℓ : ℕ} (H : Sym2Graph m) (F' : Sym2EmptyTypedFlag ℓ) :
    (∀ D ∈ supergraphFamily H, flagDensity₁ D.2 F'.toFlag = 0)
      ↔ (∀ s ∈ supergraphSym2List H, sym2EmptyTypeFlagDensity₁ s F' = 0) := by
  simp only [supergraphFamily, List.forall_mem_map]
  refine forall_congr' (fun s => imp_congr_right (fun _ => ?_))
  show flagDensity₁ s.toFlag F'.toFlag = 0 ↔ _
  rw [flagDensity₁_eq_sym2EmptyTypeFlagDensity₁]

/-- Consistency with Task 1: the general predicate at `F := triangleGraph` is exactly `hasTri`,
so the general bridge subsumes the K₃ bridge `not_hasTri_iff_triangleDensity_eq_zero`. -/
theorem inducedContains_triangleGraph_iff_hasTri {n : ℕ} (G : Sym2Graph n) :
    inducedContains triangleGraph G ↔ hasTri G :=
  (inducedContainsCount_pos_iff triangleGraph G).symm.trans (triangleCount_pos_iff G)

/-! ## Generic wiring (Task 5): the pruned generator produces exactly the analytic `F`-free flags.

The arbitrary-`F` analogue of the Task-2 wiring `prunedTriFreeFlags_toFinset_eq`: the genuine
pruned generator `augRepsFreeB (qFree F)` (which never builds a graph containing an induced `F`)
produces *exactly* the empty-typed flags of zero induced `F`-density — no full enumeration and no
canonical forbidden flag. This is the lemma the edge-based forbid-free commands cite. The family
version covers simultaneous forbidding (D3). The remaining command-surface work — making the
`generate_forbid_free_*` commands accept a `Sym2Graph m` term and route through these — is Task 5b. -/

/-- Soundness for a finite family of (nonempty) forbidden graphs: every pruned representative is
free of every `Fp ∈ Fs`. (The family analogue of `augRepsFreeB_qFree_free`.) -/
theorem augRepsFreeB_qFreeFamily_free (Fs : List (Σ m : ℕ, Sym2Graph m))
    (hFs : ∀ Fp ∈ Fs, 0 < Fp.1) (n : ℕ) (R : Sym2Graph n)
    (hR : R ∈ augRepsFreeB (qFreeFamily Fs) n) : ∀ Fp ∈ Fs, ¬ inducedContains Fp.2 R := by
  have hq0 : qFreeFamily Fs 0 (⟨∅, by simp⟩ : Sym2Graph 0) = true := by
    simp only [qFreeFamily, decide_eq_true_eq]
    rintro Fp hFp ⟨f, _⟩
    exact (f ⟨0, hFs Fp hFp⟩).elim0
  have h := augRepsFreeB_free (qFreeFamily Fs) hq0 n R hR
  simpa only [qFreeFamily, decide_eq_true_eq] using h

/-- The empty-typed flags produced by genuine pruning for a single forbidden graph `F`: the
quotient classes of the `F`-free representatives. -/
def prunedFreeFlags {m : ℕ} (F : Sym2Graph m) (n : ℕ) : List (Sym2EmptyTypedFlag n) :=
  ((augRepsFreeBDeg (qFree F) n).map Prod.fst).map (Quotient.mk (Sym2GraphSetoid n))

/-- **Genuine pruning is correct w.r.t. the analytic induced `F`-density** (single `F`). The
pruned generator produces exactly the empty-typed flags of zero induced `F`-density — never
enumerating any graph that contains an induced `F`, and with no reference to a canonical forbidden
flag. The arbitrary-`F` analogue of `prunedTriFreeFlags_toFinset_eq`. -/
theorem prunedFreeFlags_toFinset_eq {m : ℕ} (F : Sym2Graph m) (hm : 0 < m) (n : ℕ) :
    (prunedFreeFlags F n).toFinset
      = Finset.univ.filter (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) := by
  apply Finset.ext
  intro S
  simp only [prunedFreeFlags, augRepsFreeBDeg_fst_eq, List.mem_toFinset, List.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨G, rfl⟩ := Quotient.exists_rep S
  rw [← not_inducedContains_iff_density_eq_zero]
  constructor
  · rintro ⟨R, hRmem, hRG⟩ hcon
    exact augRepsFreeB_qFree_free F hm n R hRmem
      (inducedContains_of_eqv (Sym2GraphEqv.symm (Quotient.exact hRG)) hcon)
  · intro hG
    obtain ⟨R, hRmem, hRiso⟩ := augRepsFreeB_qFree_complete F n G hG
    exact ⟨R, hRmem, Quotient.sound (Sym2GraphEqv.symm hRiso)⟩

/-- The empty-typed flags produced by genuine pruning for a finite family `Fs`. -/
def prunedFreeFamilyFlags (Fs : List (Σ m : ℕ, Sym2Graph m)) (n : ℕ) :
    List (Sym2EmptyTypedFlag n) :=
  ((augRepsFreeBDeg (qFreeFamily Fs) n).map Prod.fst).map (Quotient.mk (Sym2GraphSetoid n))

/-- **Genuine pruning is correct for a finite family** (per D3): the pruned generator produces
exactly the empty-typed flags whose induced `Fp`-density vanishes for every `Fp ∈ Fs`. -/
theorem prunedFreeFamilyFlags_toFinset_eq (Fs : List (Σ m : ℕ, Sym2Graph m))
    (hFs : ∀ Fp ∈ Fs, 0 < Fp.1) (n : ℕ) :
    (prunedFreeFamilyFlags Fs n).toFinset
      = Finset.univ.filter (fun S => ∀ Fp ∈ Fs, sym2EmptyTypeFlagDensity₁ ⟦Fp.2⟧ S = 0) := by
  apply Finset.ext
  intro S
  simp only [prunedFreeFamilyFlags, augRepsFreeBDeg_fst_eq, List.mem_toFinset, List.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨G, rfl⟩ := Quotient.exists_rep S
  rw [← forall_not_inducedContains_iff_forall_density_eq_zero]
  constructor
  · rintro ⟨R, hRmem, hRG⟩ Fp hFp hcon
    exact augRepsFreeB_qFreeFamily_free Fs hFs n R hRmem Fp hFp
      (inducedContains_of_eqv (Sym2GraphEqv.symm (Quotient.exact hRG)) hcon)
  · intro hall
    obtain ⟨R, hRmem, hRiso⟩ := augRepsFreeB_qFreeFamily_complete Fs n G hall
    exact ⟨R, hRmem, Quotient.sound (Sym2GraphEqv.symm hRiso)⟩

/-! ## Task 8a: cheap clique check for complete-graph forbids

For a *complete-graph* forbid `K_r`, induced `K_r`-containment is just "`G` has an `r`-clique".
The generic `inducedContains (completeSym2Graph r)` decides this by enumerating embeddings
`Fin r ↪ Fin n` (expensive); `hasClique r` decides it by enumerating vertex *subsets* (cheap,
the generalization of the K₃-specific `hasTri`). Routing complete-graph forbids through `qCliqueFree`
keeps the generic path for non-complete `F` while restoring the pruning speed-up at high `n`. -/

/-- `G` has an `r`-clique: an `r`-element vertex set, pairwise adjacent. Decided by enumerating
subsets (cheap), unlike `inducedContains` which enumerates embeddings. Generalizes `hasTri`. -/
def hasClique (r : ℕ) (G : Sym2Graph n) : Prop :=
  ∃ s : Finset (Fin n), s.card = r ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → s(a, b) ∈ G.edges

instance (r : ℕ) (G : Sym2Graph n) : Decidable (hasClique r G) := by
  unfold hasClique; infer_instance

/-- `hasClique` is an isomorphism invariant (transport the clique set along the iso permutation). -/
theorem hasClique_of_eqv {r : ℕ} {G R : Sym2Graph n} (h : G ∼sf R) (hG : hasClique r G) :
    hasClique r R := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv h
  obtain ⟨s, hcard, hadj⟩ := hG
  refine ⟨s.image φ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ φ.injective]; exact hcard
  · intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have h2 := (hφ s(a', b')).mp (hadj a' ha' b' hb' (fun he => hab (by rw [he])))
    rwa [Sym2.map_pair_eq] at h2

/-- **Vertex-deletion monotonicity** for cliques (mirrors `hasTri_of_restrict`). -/
theorem hasClique_of_restrict {r : ℕ} {H : Sym2Graph (n + 1)} (h : hasClique r (restrict H)) :
    hasClique r H := by
  obtain ⟨s, hcard, hadj⟩ := h
  refine ⟨s.image Fin.castSucc, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]; exact hcard
  · intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have h2 := ((mem_restrict_edges H _).mp (hadj a' ha' b' hb' (fun he => hab (by rw [he])))).2
    rwa [Sym2.map_pair_eq] at h2

/-- **Clique = induced complete-graph containment.** For any `F : Sym2Graph r` that is complete
(every off-diagonal pair is an edge), `inducedContains F G ↔ hasClique r G`. This lets the cheap
subset-based clique check stand in for the generic embedding-based `inducedContains`. -/
theorem inducedContains_iff_hasClique {r : ℕ} (F : Sym2Graph r)
    (hF : ∀ i j : Fin r, s(i, j) ∈ F.edges ↔ i ≠ j) (G : Sym2Graph n) :
    inducedContains F G ↔ hasClique r G := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    · intro a ha b hb hab
      rw [Finset.mem_image] at ha hb
      obtain ⟨i, _, rfl⟩ := ha
      obtain ⟨j, _, rfl⟩ := hb
      rw [hf i j, hF i j]
      exact fun he => hab (by rw [he])
  · rintro ⟨s, hcard, hadj⟩
    let e : Fin r ≃ {x // x ∈ s} := (finCongr hcard.symm).trans s.equivFin.symm
    refine ⟨⟨fun i => (e i).val, fun i j hij => e.injective (Subtype.ext hij)⟩, fun i j => ?_⟩
    simp only [Function.Embedding.coeFn_mk]
    rw [hF i j]
    by_cases h : i = j
    · subst h
      refine iff_of_false (fun hmem => ?_) (not_not_intro rfl)
      exact absurd (Sym2.mk_isDiag_iff.mpr rfl) (G.edges_valid _ hmem)
    · exact iff_of_true
        (hadj _ (e i).property _ (e j).property (fun he => h (e.injective (Subtype.ext he)))) h

/-- The cheap `q`-predicate for an `r`-clique (complete-graph) forbid: `K_r`-free iff no `r`-clique. -/
def qCliqueFree (r : ℕ) : (k : ℕ) → Sym2Graph k → Bool :=
  fun _ G => !decide (hasClique r G)

/-- `qCliqueFree r` is exactly `qFree F` for any complete `F : Sym2Graph r` — so the cheap generator
produces the same set, and the Task-5a wiring applies verbatim. -/
theorem qCliqueFree_eq_qFree {r : ℕ} (F : Sym2Graph r)
    (hF : ∀ i j : Fin r, s(i, j) ∈ F.edges ↔ i ≠ j) : qCliqueFree r = qFree F := by
  funext k G
  simp only [qCliqueFree, qFree]
  congr 1
  exact decide_eq_decide.mpr (inducedContains_iff_hasClique F hF G).symm

/-- The empty-typed flags produced by the *cheap* clique-pruned generator. -/
def prunedCliqueFreeFlags (r n : ℕ) : List (Sym2EmptyTypedFlag n) :=
  ((augRepsFreeBDeg (qCliqueFree r) n).map Prod.fst).map (Quotient.mk (Sym2GraphSetoid n))

/-- **The cheap clique-pruned generator is correct** w.r.t. the analytic complete-graph density:
for any complete `F : Sym2Graph r` (`0 < r`), it produces exactly the empty-typed flags of zero
induced `F`-density — at the cost of a subset scan rather than an embedding search. -/
theorem prunedCliqueFreeFlags_toFinset_eq {r : ℕ} (F : Sym2Graph r)
    (hF : ∀ i j : Fin r, s(i, j) ∈ F.edges ↔ i ≠ j) (hr : 0 < r) (n : ℕ) :
    (prunedCliqueFreeFlags r n).toFinset
      = Finset.univ.filter (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) := by
  unfold prunedCliqueFreeFlags
  rw [qCliqueFree_eq_qFree F hF]
  exact prunedFreeFlags_toFinset_eq F hr n

-- Correctness: the cheap clique generator reproduces the K₃-free class counts (7/14/38), matching
-- `augRepsTriFree` — and reduces by the cheap subset scan, not the generic embedding search.
example : (augRepsFreeB (qCliqueFree 3) 4).length = 7 := by native_decide
example : (augRepsFreeB (qCliqueFree 3) 5).length = 14 := by native_decide
example : (augRepsFreeB (qCliqueFree 3) 6).length = 38 := by native_decide

end FlagAlgebras.Compute
