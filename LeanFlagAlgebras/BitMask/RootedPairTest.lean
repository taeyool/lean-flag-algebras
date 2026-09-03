import LeanFlagAlgebras.BitMask.RootedCount
import LeanFlagAlgebras.BitMask.CanonSmall

/-! # Regression test: kernel-only σ-typed densities at example scale

The `K3freeC6` shape: type = an edge (`2:12`), patterns = 4-vertex
2-rooted flags, host = the certificate's 6-vertex target graph rooted at
its `{0,1}` edge. Validates the single density and two pair densities
(one zero, one not) against the native evaluation — every value proved
by kernel computation, 3-axiom.

The representative distinctness for the `(2,4)` combination is checked
**at the mask level, for all type graphs at once** (`rdist24_check`):
by the converse transport `bits_of_labeledEqv`, no labeled isomorphism
search is ever run in the kernel. -/

namespace RootedPairTest

open FlagAlgebras.Compute FlagAlgebras.Compute.BitMask

/-- The edge type (`2:12`). -/
def sig2e : Sym2FlagType 2 := ⟨{s(0, 1)}, by decide⟩

/-- The `K3freeC6` target graph, rooted at its edge `{0, 1}`. -/
def targetC6r : Sym2LabeledGraph sig2e 6 where
  edges := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  edges_valid := by decide
  type_embed :=
    { toFun := Fin.castLE (by omega)
      inj' := Fin.castLE_injective _
      map_rel_iff' := by
        intro i j
        rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
        simp only [Finset.mem_coe]
        fin_cases i <;> fin_cases j <;> decide }

/-- A 4-vertex 2-rooted flag: the root edge plus a pendant at root 0. -/
def F0 : Sym2LabeledGraph sig2e 4 where
  edges := {s(0, 1), s(0, 2)}
  edges_valid := by decide
  type_embed :=
    { toFun := Fin.castLE (by omega)
      inj' := Fin.castLE_injective _
      map_rel_iff' := by
        intro i j
        rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
        simp only [Finset.mem_coe]
        fin_cases i <;> fin_cases j <;> decide }

/-- A 4-vertex 2-rooted flag: the root edge plus a pendant at root 1. -/
def F1 : Sym2LabeledGraph sig2e 4 where
  edges := {s(0, 1), s(1, 3)}
  edges_valid := by decide
  type_embed :=
    { toFun := Fin.castLE (by omega)
      inj' := Fin.castLE_injective _
      map_rel_iff' := by
        intro i j
        rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
        simp only [Finset.mem_coe]
        fin_cases i <;> fin_cases j <;> decide }

/-! ## The `(2, 4)` accept apparatus -/

set_option maxRecDepth 65536 in
/-- Mask-level distinctness of the 40 rooted representatives — one
kernel check for **every** type graph. -/
lemma rdist24_check : ∀ p ∈ RCanon2_4.rreps2_4, ∀ q ∈ RCanon2_4.rreps2_4,
    (∃ f : Fin 4 → Fin 4, Function.Injective f
      ∧ (∀ i : Fin 2, f (Fin.castLE (by omega) i) = Fin.castLE (by omega) i)
      ∧ ∀ a b : Fin 4, a < b →
          p.testBit (pairIdx 4 a.val b.val)
            = q.testBit (pairIdx 4 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) → p = q := by
  decide +kernel

/-- The `(2, 4)` accept for a pattern `F`. -/
theorem racc24_spec (F : Sym2LabeledGraph sig2e 4) :
    ∀ x, x < 2 ^ 6 → ∀ hx : RootsMatch sig2e 4 x,
      ((RCanon2_4.canonImage x
          == RCanon2_4.canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask sig2e 4 (by omega) x hx ∼sf F) :=
  racc_spec_of (by omega) Canon4.finPairs4_rank_inj Canon4.finPairs4_rank_lt
    (fun x hx' hx => RCanon2_4.rleaf_reflect hx' hx)
    (rdist_of_maskCheck (by omega) rdist24_check) F

/-! ## The values (native cross-checks: `1/6`, `0`, `1/6`) -/

set_option maxRecDepth 65536 in
/-- The `F0`-density of the rooted target is `1/6` — σ-typed, kernel. -/
theorem pair_density₁_val :
    sym2FlagDensity₁ (⟦F0⟧ : Sym2Flag sig2e 4)
        (⟦targetC6r⟧ : Sym2Flag sig2e 6) = 1 / 6 := by
  rw [sym2FlagDensity₁_eq_rmaskCount (by omega)
      Canon6.finPairs6_rank_inj Canon4.finPairs4_rank_inj
      Canon4.finPairs4_rank_lt F0 (racc24_spec F0)]
  decide +kernel

set_option maxRecDepth 65536 in
/-- The `F0·F0` pair density of the rooted target is `0` (no disjoint
pair of placements) — kernel-checked rejection. -/
theorem pair_density₂_zero_val :
    sym2FlagDensity₂ (⟦F0⟧ : Sym2Flag sig2e 4) (⟦F0⟧ : Sym2Flag sig2e 4)
        (⟦targetC6r⟧ : Sym2Flag sig2e 6) = 0 := by
  rw [sym2FlagDensity₂_eq_rmaskCount₂ (by omega) (by omega)
      Canon6.finPairs6_rank_inj Canon4.finPairs4_rank_inj
      Canon4.finPairs4_rank_inj Canon4.finPairs4_rank_lt
      Canon4.finPairs4_rank_lt F0 F0 (racc24_spec F0) (racc24_spec F0)]
  decide +kernel

set_option maxRecDepth 65536 in
/-- The `F0·F1` pair density of the rooted target is `1/6` — the
σ-typed pair density at `K3freeC6` scale, computed by the kernel. -/
theorem pair_density₂_val :
    sym2FlagDensity₂ (⟦F0⟧ : Sym2Flag sig2e 4) (⟦F1⟧ : Sym2Flag sig2e 4)
        (⟦targetC6r⟧ : Sym2Flag sig2e 6) = 1 / 6 := by
  rw [sym2FlagDensity₂_eq_rmaskCount₂ (by omega) (by omega)
      Canon6.finPairs6_rank_inj Canon4.finPairs4_rank_inj
      Canon4.finPairs4_rank_inj Canon4.finPairs4_rank_lt
      Canon4.finPairs4_rank_lt F0 F1 (racc24_spec F0) (racc24_spec F1)]
  decide +kernel

end RootedPairTest
