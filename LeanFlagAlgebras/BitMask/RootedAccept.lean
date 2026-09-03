import LeanFlagAlgebras.BitMask.RootedCount
import LeanFlagAlgebras.BitMask.CanonSmall

/-! # Per-combination accept apparatus

For each rooted combination `(k, m)`, the mask-level representative
distinctness check (`rdist_check`, kernel, one check for **every** type
graph via the converse transport) and the σ-generic packaged accept
`racc_spec` — under uniform names, so the pair-density generator command
can cite them by interpolation
(`FlagAlgebras.Compute.BitMask.RCanon{k}_{m}.racc_spec`). -/

namespace FlagAlgebras.Compute.BitMask

namespace RCanon1_2

set_option maxRecDepth 65536 in
/-- Mask-level distinctness of the rooted representatives. -/
lemma rdist_check : ∀ p ∈ rreps1_2, ∀ q ∈ rreps1_2,
    (∃ f : Fin 2 → Fin 2, Function.Injective f
      ∧ (∀ i : Fin 1, f (Fin.castLE (by omega) i) = Fin.castLE (by omega) i)
      ∧ ∀ a b : Fin 2, a < b →
          p.testBit (pairIdx 2 a.val b.val)
            = q.testBit (pairIdx 2 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) → p = q := by
  decide +kernel

/-- σ-generic accept: canonical-form comparison decides labeled class
membership at `(k, m) = (1, 2)`. -/
theorem racc_spec {σr : Sym2FlagType 1} (F : Sym2LabeledGraph σr 2) :
    ∀ x, x < 2 ^ 1 → ∀ hx : RootsMatch σr 2 x,
      ((canonImage x == canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask σr 2 (by omega) x hx ∼sf F) :=
  racc_spec_of (by omega) Canon2.finPairs2_rank_inj
    Canon2.finPairs2_rank_lt
    (fun x hx' hx => rleaf_reflect hx' hx)
    (rdist_of_maskCheck (by omega) rdist_check) F

end RCanon1_2

namespace RCanon1_3

set_option maxRecDepth 65536 in
/-- Mask-level distinctness of the rooted representatives. -/
lemma rdist_check : ∀ p ∈ rreps1_3, ∀ q ∈ rreps1_3,
    (∃ f : Fin 3 → Fin 3, Function.Injective f
      ∧ (∀ i : Fin 1, f (Fin.castLE (by omega) i) = Fin.castLE (by omega) i)
      ∧ ∀ a b : Fin 3, a < b →
          p.testBit (pairIdx 3 a.val b.val)
            = q.testBit (pairIdx 3 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) → p = q := by
  decide +kernel

/-- σ-generic accept: canonical-form comparison decides labeled class
membership at `(k, m) = (1, 3)`. -/
theorem racc_spec {σr : Sym2FlagType 1} (F : Sym2LabeledGraph σr 3) :
    ∀ x, x < 2 ^ 3 → ∀ hx : RootsMatch σr 3 x,
      ((canonImage x == canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask σr 3 (by omega) x hx ∼sf F) :=
  racc_spec_of (by omega) Canon3.finPairs3_rank_inj
    Canon3.finPairs3_rank_lt
    (fun x hx' hx => rleaf_reflect hx' hx)
    (rdist_of_maskCheck (by omega) rdist_check) F

end RCanon1_3

namespace RCanon2_3

set_option maxRecDepth 65536 in
/-- Mask-level distinctness of the rooted representatives. -/
lemma rdist_check : ∀ p ∈ rreps2_3, ∀ q ∈ rreps2_3,
    (∃ f : Fin 3 → Fin 3, Function.Injective f
      ∧ (∀ i : Fin 2, f (Fin.castLE (by omega) i) = Fin.castLE (by omega) i)
      ∧ ∀ a b : Fin 3, a < b →
          p.testBit (pairIdx 3 a.val b.val)
            = q.testBit (pairIdx 3 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) → p = q := by
  decide +kernel

/-- σ-generic accept: canonical-form comparison decides labeled class
membership at `(k, m) = (2, 3)`. -/
theorem racc_spec {σr : Sym2FlagType 2} (F : Sym2LabeledGraph σr 3) :
    ∀ x, x < 2 ^ 3 → ∀ hx : RootsMatch σr 3 x,
      ((canonImage x == canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask σr 3 (by omega) x hx ∼sf F) :=
  racc_spec_of (by omega) Canon3.finPairs3_rank_inj
    Canon3.finPairs3_rank_lt
    (fun x hx' hx => rleaf_reflect hx' hx)
    (rdist_of_maskCheck (by omega) rdist_check) F

end RCanon2_3

namespace RCanon2_4

set_option maxRecDepth 65536 in
/-- Mask-level distinctness of the rooted representatives. -/
lemma rdist_check : ∀ p ∈ rreps2_4, ∀ q ∈ rreps2_4,
    (∃ f : Fin 4 → Fin 4, Function.Injective f
      ∧ (∀ i : Fin 2, f (Fin.castLE (by omega) i) = Fin.castLE (by omega) i)
      ∧ ∀ a b : Fin 4, a < b →
          p.testBit (pairIdx 4 a.val b.val)
            = q.testBit (pairIdx 4 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) → p = q := by
  decide +kernel

/-- σ-generic accept: canonical-form comparison decides labeled class
membership at `(k, m) = (2, 4)`. -/
theorem racc_spec {σr : Sym2FlagType 2} (F : Sym2LabeledGraph σr 4) :
    ∀ x, x < 2 ^ 6 → ∀ hx : RootsMatch σr 4 x,
      ((canonImage x == canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask σr 4 (by omega) x hx ∼sf F) :=
  racc_spec_of (by omega) Canon4.finPairs4_rank_inj
    Canon4.finPairs4_rank_lt
    (fun x hx' hx => rleaf_reflect hx' hx)
    (rdist_of_maskCheck (by omega) rdist_check) F

end RCanon2_4

namespace RCanon3_4

set_option maxRecDepth 65536 in
/-- Mask-level distinctness of the rooted representatives. -/
lemma rdist_check : ∀ p ∈ rreps3_4, ∀ q ∈ rreps3_4,
    (∃ f : Fin 4 → Fin 4, Function.Injective f
      ∧ (∀ i : Fin 3, f (Fin.castLE (by omega) i) = Fin.castLE (by omega) i)
      ∧ ∀ a b : Fin 4, a < b →
          p.testBit (pairIdx 4 a.val b.val)
            = q.testBit (pairIdx 4 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) → p = q := by
  decide +kernel

/-- σ-generic accept: canonical-form comparison decides labeled class
membership at `(k, m) = (3, 4)`. -/
theorem racc_spec {σr : Sym2FlagType 3} (F : Sym2LabeledGraph σr 4) :
    ∀ x, x < 2 ^ 6 → ∀ hx : RootsMatch σr 4 x,
      ((canonImage x == canonImage (rootedMaskOf F)) = true
        ↔ labeledGraphOfMask σr 4 (by omega) x hx ∼sf F) :=
  racc_spec_of (by omega) Canon4.finPairs4_rank_inj
    Canon4.finPairs4_rank_lt
    (fun x hx' hx => rleaf_reflect hx' hx)
    (rdist_of_maskCheck (by omega) rdist_check) F

end RCanon3_4

end FlagAlgebras.Compute.BitMask
