import LeanFlagAlgebras.BitMask.CanonSmall
import LeanFlagAlgebras.BitMask.Density6

/-! # Regression test: kernel-only density values

End-to-end validation of the bit-level density pipeline (`Density.lean`)
at pattern size 5: a density value lemma proved entirely by kernel
computation — the mask count by `decide +kernel`, closed by the count
bridge. `#print axioms` on `density_val` shows
`[propext, Classical.choice, Quot.sound]` — no `native_decide`.

Checked against the native evaluation
(`#eval sym2EmptyTypeFlagDensity₁ …` gives `1/6`). -/

open FlagAlgebras.Compute FlagAlgebras.Compute.BitMask

namespace BitMaskDensityTest

/-- The 5-cycle pattern. -/
def C5p : Sym2Graph 5 where
  edges := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(0, 4)}
  edges_valid := by decide

/-- A 6-vertex host: the 5-cycle plus an isolated vertex. -/
def host6 : Sym2Graph 6 where
  edges := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(0, 4)}
  edges_valid := by decide

set_option maxRecDepth 65536 in
lemma count_val : maskCount 6 5
    (fun x => Canon5.canonImage x == Canon5.canonOf C5p)
    (maskOfGraph₂ host6) = 1 := by decide +kernel

set_option maxRecDepth 8192 in
lemma coeff_val : multinomialCoefficient (fun _ : Fin 1 => 5) 6 = 6 := by
  decide +kernel

/-- The C₅-density of C₅-plus-a-vertex is `1/6` — kernel-computed. -/
theorem density_val :
    sym2EmptyTypeFlagDensity₁ ⟦C5p⟧ (⟦host6⟧ : Sym2EmptyTypedFlag 6)
      = 1 / 6 := by
  rw [Canon5.density₁_eq_maskCount5 Canon6.finPairs6_rank_inj C5p host6,
    count_val, coeff_val]
  norm_num

/-! Small pattern sizes: the edge density of the 5-cycle is `1/2`, and
the triangle density of `K₄` is `1`. -/

/-- A single edge, as a 2-vertex pattern. -/
def edge2 : Sym2Graph 2 where
  edges := {s(0, 1)}
  edges_valid := by decide

/-- The 5-cycle as its own host. -/
def hostC5 : Sym2Graph 5 where
  edges := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(0, 4)}
  edges_valid := by decide

set_option maxRecDepth 65536 in
lemma edge_count_val : maskCount 5 2
    (fun x => Canon2.canonImage x == Canon2.canonOf edge2)
    (maskOfGraph₂ hostC5) = 5 := by decide +kernel

set_option maxRecDepth 8192 in
lemma coeff2_val : multinomialCoefficient (fun _ : Fin 1 => 2) 5 = 10 := by
  decide +kernel

/-- The edge density of `C₅` is `1/2` — kernel-computed. -/
theorem edge_density_val :
    sym2EmptyTypeFlagDensity₁ ⟦edge2⟧ (⟦hostC5⟧ : Sym2EmptyTypedFlag 5)
      = 1 / 2 := by
  rw [Canon2.density₁_eq_maskCount2 Canon5.finPairs5_rank_inj edge2 hostC5,
    edge_count_val, coeff2_val]
  norm_num

/-- The triangle. -/
def tri3 : Sym2Graph 3 where
  edges := {s(0, 1), s(0, 2), s(1, 2)}
  edges_valid := by decide

/-- `K₄`. -/
def hostK4 : Sym2Graph 4 where
  edges := {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)}
  edges_valid := by decide

set_option maxRecDepth 65536 in
lemma tri_count_val : maskCount 4 3
    (fun x => Canon3.canonImage x == Canon3.canonOf tri3)
    (maskOfGraph₂ hostK4) = 4 := by decide +kernel

set_option maxRecDepth 8192 in
lemma coeff3_val : multinomialCoefficient (fun _ : Fin 1 => 3) 4 = 4 := by
  decide +kernel

/-- The triangle density of `K₄` is `1` — kernel-computed. -/
theorem tri_density_val :
    sym2EmptyTypeFlagDensity₁ ⟦tri3⟧ (⟦hostK4⟧ : Sym2EmptyTypedFlag 4)
      = 1 := by
  rw [Canon3.density₁_eq_maskCount3 Canon4.finPairs4_rank_inj tri3 hostK4,
    tri_count_val, coeff3_val]
  norm_num

/-! Pattern size 6 (`K3freeC6`-class objectives): the C₆-density of the
`K3freeC6` target graph (a relabeled 6-cycle) is `1`. -/

/-- The 6-cycle pattern. -/
def C6p : Sym2Graph 6 where
  edges := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(0, 5)}
  edges_valid := by decide

/-- The `K3freeC6` certificate's target graph (canonical labeling). -/
def targetC6 : Sym2Graph 6 where
  edges := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  edges_valid := by decide

set_option maxRecDepth 65536 in
lemma c6_count_val : maskCount 6 6
    (fun x => Canon6.canonImage x == Canon6.canonOf C6p)
    (maskOfGraph₂ targetC6) = 1 := by decide +kernel

set_option maxRecDepth 8192 in
lemma coeff6_val : multinomialCoefficient (fun _ : Fin 1 => 6) 6 = 1 := by
  decide +kernel

/-- The C₆-density of the `K3freeC6` target graph is `1` —
kernel-computed. -/
theorem c6_density_val :
    sym2EmptyTypeFlagDensity₁ ⟦C6p⟧ (⟦targetC6⟧ : Sym2EmptyTypedFlag 6)
      = 1 := by
  rw [Canon6.density₁_eq_maskCount6 Canon6.finPairs6_rank_inj C6p targetC6,
    c6_count_val, coeff6_val]
  norm_num

end BitMaskDensityTest
