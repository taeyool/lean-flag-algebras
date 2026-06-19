import LeanFlagAlgebras.FlagAlgebra.Compute.Generate
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
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

end FlagAlgebras.Compute
