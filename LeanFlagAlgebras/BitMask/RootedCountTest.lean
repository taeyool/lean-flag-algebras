import LeanFlagAlgebras.BitMask.RootedCount
import LeanFlagAlgebras.BitMask.CanonSmall

/-! # Regression test: kernel-only σ-typed density values

End-to-end validation of the rooted pipeline at the smallest real
combination — flags with one root on two vertices (`(k, m) = (1, 2)`,
Mantel's flag sizes): the σ-typed density of the rooted edge flag in a
rooted `K₃` host is `1`, proved entirely by kernel computation.
`#print axioms` on `rdensity_val` shows
`[propext, Classical.choice, Quot.sound]`. -/

namespace RootedCountTest

open FlagAlgebras.Compute FlagAlgebras.Compute.BitMask

/-- The unique 1-vertex type graph. -/
def sig1 : Sym2FlagType 1 := ⟨∅, by simp⟩

/-- `K₃` with its root at vertex `0`. -/
def hostK3r : Sym2LabeledGraph sig1 3 where
  edges := {s(0, 1), s(0, 2), s(1, 2)}
  edges_valid := by decide
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro i j
        constructor
        · intro h
          exact absurd rfl h.ne
        · intro h
          exact absurd (Subsingleton.elim i j) h.ne }

/-- The rooted edge flag (`2:12(1)`). -/
def edgeFlagR : Sym2LabeledGraph sig1 2 where
  edges := {s(0, 1)}
  edges_valid := by decide
  type_embed :=
    { toFun := fun _ => 0
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro i j
        constructor
        · intro h
          exact absurd rfl h.ne
        · intro h
          exact absurd (Subsingleton.elim i j) h.ne }

/-! ## The `(1, 2)` accept apparatus -/

set_option maxRecDepth 8192 in
/-- The two rooted representatives are non-equivalent (kernel-checked;
`RootsMatch` is vacuous at one root, so fixed proofs suffice — any
others agree by proof irrelevance). -/
lemma rdist12_core : ∀ p ∈ RCanon1_2.rreps1_2, ∀ q ∈ RCanon1_2.rreps1_2,
    labeledGraphOfMask sig1 2 (by omega) p (rootsMatch_one sig1 2 p)
      ∼sf labeledGraphOfMask sig1 2 (by omega) q (rootsMatch_one sig1 2 q)
    → p = q := by
  decide +kernel

lemma rdist12 : ∀ p ∈ RCanon1_2.rreps1_2, ∀ q ∈ RCanon1_2.rreps1_2,
    ∀ (hp : RootsMatch sig1 2 p) (hq : RootsMatch sig1 2 q),
      labeledGraphOfMask sig1 2 (by omega) p hp
        ∼sf labeledGraphOfMask sig1 2 (by omega) q hq → p = q :=
  fun p hp q hq _ _ h => rdist12_core p hp q hq h

/-- The canonical-form accept decides labeled membership in the class
of `F` on two-vertex rooted masks. -/
theorem racc12_spec (F : Sym2LabeledGraph sig1 2) :
    ∀ x, x < 2 ^ 1 → ∀ hx : RootsMatch sig1 2 x,
      ((RCanon1_2.canonImage x
          == RCanon1_2.canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask sig1 2 (by omega) x hx ∼sf F) := by
  intro x hx' hx
  rw [beq_iff_eq]
  have hFm : rootedMaskOf F < 2 ^ 1 :=
    rootedExtractMask_lt Canon2.finPairs2_rank_lt _ _ _
  have hFr : RootsMatch sig1 2 (rootedMaskOf F) := rootsMatch_one _ _ _
  have hFe := eqv_decode_rootedMaskOf Canon2.finPairs2_rank_inj F
    (by omega) hFr
  rw [← eqv_iff_rcanonImage_eq (by omega)
    (fun x hx' hx => RCanon1_2.rleaf_reflect hx' hx) rdist12
    hx' hFm hx hFr]
  constructor
  · intro h
    exact h.trans (sym2LabeledGraphEqv.symm hFe)
  · intro h
    exact h.trans hFe

/-! ## The value -/

set_option maxRecDepth 65536 in
lemma rcount_val : rmaskCount hostK3r 2
    (fun x => RCanon1_2.canonImage x
      == RCanon1_2.canonImage (rootedMaskOf edgeFlagR))
    (maskOfGraph₂ (underlyingGraph hostK3r)) = 2 := by decide +kernel

set_option maxRecDepth 8192 in
lemma rcoeff_val :
    multinomialCoefficient (fun _ : Fin 1 => 2 - 1) (3 - 1) = 2 := by
  decide +kernel

/-- **The rooted edge density of rooted `K₃` is `1`** — the σ-typed
flag density, computed by the kernel. -/
theorem rdensity_val :
    sym2FlagDensity₁ (⟦edgeFlagR⟧ : Sym2Flag sig1 2)
        (⟦hostK3r⟧ : Sym2Flag sig1 3) = 1 := by
  rw [sym2FlagDensity₁_eq_rmaskCount (by omega)
      Canon3.finPairs3_rank_inj Canon2.finPairs2_rank_inj
      Canon2.finPairs2_rank_lt edgeFlagR (racc12_spec edgeFlagR),
    rcount_val, rcoeff_val]
  norm_num

/-! ## The pair density -/

set_option maxRecDepth 65536 in
/-- **The rooted edge·edge pair density of rooted `K₃` is `1`** — the
σ-typed pair density `sym2FlagDensity₂` (the quantity the mul-theorem
layer consumes), computed by the kernel: the pair count over the 64
subset pairs, the coefficient, and the rational arithmetic all reduce
in one `decide +kernel`. -/
theorem rdensity₂_val :
    sym2FlagDensity₂ (⟦edgeFlagR⟧ : Sym2Flag sig1 2)
        (⟦edgeFlagR⟧ : Sym2Flag sig1 2)
        (⟦hostK3r⟧ : Sym2Flag sig1 3) = 1 := by
  rw [sym2FlagDensity₂_eq_rmaskCount₂ (by omega) (by omega)
      Canon3.finPairs3_rank_inj Canon2.finPairs2_rank_inj
      Canon2.finPairs2_rank_inj Canon2.finPairs2_rank_lt
      Canon2.finPairs2_rank_lt edgeFlagR edgeFlagR
      (racc12_spec edgeFlagR) (racc12_spec edgeFlagR)]
  decide +kernel

end RootedCountTest
