import LeanFlagAlgebras.BitMask.Density

/-! # Six-vertex pattern densities

The canon apparatus and kernel-computable density instance at pattern
size 6 — the size of `K3freeC6`-class objectives (`C₆`). Kept in its own
file: the distinctness check runs the permutation search on the degree-
key collisions among the 156 representatives, a heavy (~9 min) one-time
kernel computation. (Pattern size 7 would need the same over 1044
representatives — deferred until a need arises.) -/

namespace FlagAlgebras.Compute.BitMask

namespace Canon6

set_option maxRecDepth 8192 in
/-- Every bit position below 15 is a six-vertex pair rank. -/
lemma finPairs6_rank_cover : ∀ i < 15, ∃ p ∈ finPairs 6,
    pairIdx 6 p.1.val p.2.val = i := by decide

set_option maxRecDepth 65536 in
/-- The 156 representatives are pairwise non-equivalent (kernel-checked,
degree-key-bucketed). -/
lemma reps6_distinct_bool : (reps6.all fun p => reps6.all fun q =>
    p == q
      || decide (degKey (graphOfMask₂ 6 p) ≠ degKey (graphOfMask₂ 6 q))
      || !isEmptyIsoFast_bool (graphOfMask₂ 6 p) (graphOfMask₂ 6 q))
      = true := by
  decide +kernel

/-- The 156 representatives are pairwise non-equivalent. -/
lemma reps6_distinct : ∀ p ∈ reps6, ∀ q ∈ reps6,
    graphOfMask₂ 6 p ∼sf graphOfMask₂ 6 q → p = q :=
  distinct_of_bool_deg reps6_distinct_bool

/-- Kernel-computable density of any 6-vertex pattern. -/
theorem density₁_eq_maskCount6 {N : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2Graph 6) (G : Sym2Graph N) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N 6 (fun x => canonImage x == canonOf F)
            (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => 6) N :=
  density₁_eq_maskCount_canon canonOf hinjN (fun _ => rfl) canonOf_spec
    reps6_distinct finPairs6_rank_inj finPairs6_rank_lt
    finPairs6_rank_cover F G

end Canon6

end FlagAlgebras.Compute.BitMask
