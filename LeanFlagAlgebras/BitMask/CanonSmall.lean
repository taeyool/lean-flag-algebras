import LeanFlagAlgebras.BitMask.Canon2Data
import LeanFlagAlgebras.BitMask.Canon3Data
import LeanFlagAlgebras.BitMask.Canon4Data
import LeanFlagAlgebras.BitMask.Density

/-! # Canonicalization at pattern sizes 2, 3, 4

The tiny sweeps (2 / 8 / 64 masks; 2 / 4 / 11 representatives) with
their canon apparatus and kernel-computable density instances, mirroring
`Canon5`. These are the pattern sizes of the common objectives and
forbids (edge, path, triangle, `K₄`, `C₄`), so with them every pattern
size `2 ≤ m ≤ 5` has a bit-level density lemma. -/

namespace FlagAlgebras.Compute.BitMask

/-! ## Two vertices -/

namespace Canon2

def getPerm (i : ℕ) : ℕ := perms2.getD i 0
def getRank (i : ℕ) : ℕ := rankMaps2.getD i 0

/-- Witness permutation index (3 bits per mask). -/
def pidx (m : ℕ) : ℕ := ((wChunks2.getD 0 0) >>> (3 * m)) &&& 7

def canonImage (m : ℕ) : ℕ := rankApply 1 (getRank (pidx m)) m

def leaf2 (m : ℕ) : Bool :=
  decide (pidx m < 2)
    && decide (canonImage m ∈ reps2)
    && scanOK 1 m (getRank (pidx m)) (canonImage m)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 2).all
    (fun i => permConsistent 2 (getPerm i) (getRank i)) = true := by
  decide +kernel

lemma perm2Consistent_of_lt {i : ℕ} (hi : i < 2) :
    permConsistent 2 (getPerm i) (getRank i) = true :=
  List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)

lemma pairIdx2_lt : ∀ a b : Fin 2, a < b → pairIdx 2 a.val b.val < 1 := by
  decide

set_option maxRecDepth 8192 in
lemma sweep2 : sweepMasks leaf2 1 0 = true := by decide +kernel

theorem leaf2_reflect {m : ℕ} (hm : m < 2 ^ 1) :
    canonImage m ∈ reps2
      ∧ graphOfMask₂ 2 m ∼sf graphOfMask₂ 2 (canonImage m) := by
  have hleaf : leaf2 m = true := by
    have h := sweepMasks_spec leaf2 1 0 sweep2 m hm
    rwa [zero_mul, zero_add] at h
  unfold leaf2 at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  exact ⟨of_decide_eq_true hmem,
    leafParts_eqv pairIdx2_lt
      (perm2Consistent_of_lt (of_decide_eq_true hpidx)) hscan⟩

set_option maxRecDepth 8192 in
lemma finPairs2_rank_inj : ∀ p₁ ∈ finPairs 2, ∀ p₂ ∈ finPairs 2,
    pairIdx 2 p₁.1.val p₁.2.val = pairIdx 2 p₂.1.val p₂.2.val → p₁ = p₂ := by
  decide

set_option maxRecDepth 8192 in
lemma finPairs2_rank_lt :
    ∀ p ∈ finPairs 2, pairIdx 2 p.1.val p.2.val < 1 := by decide

set_option maxRecDepth 8192 in
lemma finPairs2_rank_cover : ∀ i < 1, ∃ p ∈ finPairs 2,
    pairIdx 2 p.1.val p.2.val = i := by decide

def canonOf (G : Sym2Graph 2) : ℕ := canonImage (maskOfGraph₂ G)

theorem canonOf_spec (G : Sym2Graph 2) :
    canonOf G ∈ reps2 ∧ G ∼sf graphOfMask₂ 2 (canonOf G) := by
  have hm : maskOfGraph₂ G < 2 ^ 1 :=
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 1) finPairs2_rank_lt
  obtain ⟨hmem, heqv⟩ := leaf2_reflect hm
  rw [graphOfMask₂_maskOfGraph₂ finPairs2_rank_inj G] at heqv
  exact ⟨hmem, heqv⟩

set_option maxRecDepth 8192 in
lemma reps2_distinct_bool : (reps2.all fun p => reps2.all fun q =>
    p == q || !isEmptyIsoFast_bool (graphOfMask₂ 2 p) (graphOfMask₂ 2 q))
      = true := by
  decide +kernel

lemma reps2_distinct : ∀ p ∈ reps2, ∀ q ∈ reps2,
    graphOfMask₂ 2 p ∼sf graphOfMask₂ 2 q → p = q :=
  distinct_of_bool reps2_distinct_bool

/-- Kernel-computable density of any 2-vertex pattern. -/
theorem density₁_eq_maskCount2 {N : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2Graph 2) (G : Sym2Graph N) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N 2 (fun x => canonImage x == canonOf F)
            (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => 2) N :=
  density₁_eq_maskCount_canon canonOf hinjN (fun _ => rfl) canonOf_spec
    reps2_distinct finPairs2_rank_inj finPairs2_rank_lt
    finPairs2_rank_cover F G

end Canon2

/-! ## Three vertices -/

namespace Canon3

def getPerm (i : ℕ) : ℕ := perms3.getD i 0
def getRank (i : ℕ) : ℕ := rankMaps3.getD i 0

/-- Witness permutation index (3 bits per mask). -/
def pidx (m : ℕ) : ℕ := ((wChunks3.getD 0 0) >>> (3 * m)) &&& 7

def canonImage (m : ℕ) : ℕ := rankApply 3 (getRank (pidx m)) m

def leaf3 (m : ℕ) : Bool :=
  decide (pidx m < 6)
    && decide (canonImage m ∈ reps3)
    && scanOK 3 m (getRank (pidx m)) (canonImage m)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 6).all
    (fun i => permConsistent 3 (getPerm i) (getRank i)) = true := by
  decide +kernel

lemma perm3Consistent_of_lt {i : ℕ} (hi : i < 6) :
    permConsistent 3 (getPerm i) (getRank i) = true :=
  List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)

lemma pairIdx3_lt : ∀ a b : Fin 3, a < b → pairIdx 3 a.val b.val < 3 := by
  decide

set_option maxRecDepth 8192 in
lemma sweep3 : sweepMasks leaf3 3 0 = true := by decide +kernel

theorem leaf3_reflect {m : ℕ} (hm : m < 2 ^ 3) :
    canonImage m ∈ reps3
      ∧ graphOfMask₂ 3 m ∼sf graphOfMask₂ 3 (canonImage m) := by
  have hleaf : leaf3 m = true := by
    have h := sweepMasks_spec leaf3 3 0 sweep3 m hm
    rwa [zero_mul, zero_add] at h
  unfold leaf3 at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  exact ⟨of_decide_eq_true hmem,
    leafParts_eqv pairIdx3_lt
      (perm3Consistent_of_lt (of_decide_eq_true hpidx)) hscan⟩

set_option maxRecDepth 8192 in
lemma finPairs3_rank_inj : ∀ p₁ ∈ finPairs 3, ∀ p₂ ∈ finPairs 3,
    pairIdx 3 p₁.1.val p₁.2.val = pairIdx 3 p₂.1.val p₂.2.val → p₁ = p₂ := by
  decide

set_option maxRecDepth 8192 in
lemma finPairs3_rank_lt :
    ∀ p ∈ finPairs 3, pairIdx 3 p.1.val p.2.val < 3 := by decide

set_option maxRecDepth 8192 in
lemma finPairs3_rank_cover : ∀ i < 3, ∃ p ∈ finPairs 3,
    pairIdx 3 p.1.val p.2.val = i := by decide

def canonOf (G : Sym2Graph 3) : ℕ := canonImage (maskOfGraph₂ G)

theorem canonOf_spec (G : Sym2Graph 3) :
    canonOf G ∈ reps3 ∧ G ∼sf graphOfMask₂ 3 (canonOf G) := by
  have hm : maskOfGraph₂ G < 2 ^ 3 :=
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 3) finPairs3_rank_lt
  obtain ⟨hmem, heqv⟩ := leaf3_reflect hm
  rw [graphOfMask₂_maskOfGraph₂ finPairs3_rank_inj G] at heqv
  exact ⟨hmem, heqv⟩

set_option maxRecDepth 8192 in
lemma reps3_distinct_bool : (reps3.all fun p => reps3.all fun q =>
    p == q || !isEmptyIsoFast_bool (graphOfMask₂ 3 p) (graphOfMask₂ 3 q))
      = true := by
  decide +kernel

lemma reps3_distinct : ∀ p ∈ reps3, ∀ q ∈ reps3,
    graphOfMask₂ 3 p ∼sf graphOfMask₂ 3 q → p = q :=
  distinct_of_bool reps3_distinct_bool

/-- Kernel-computable density of any 3-vertex pattern. -/
theorem density₁_eq_maskCount3 {N : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2Graph 3) (G : Sym2Graph N) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N 3 (fun x => canonImage x == canonOf F)
            (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => 3) N :=
  density₁_eq_maskCount_canon canonOf hinjN (fun _ => rfl) canonOf_spec
    reps3_distinct finPairs3_rank_inj finPairs3_rank_lt
    finPairs3_rank_cover F G

end Canon3

/-! ## Four vertices -/

namespace Canon4

def getPerm (i : ℕ) : ℕ := perms4.getD i 0
def getRank (i : ℕ) : ℕ := rankMaps4.getD i 0

/-- Witness permutation index (5 bits per mask). -/
def pidx (m : ℕ) : ℕ := ((wChunks4.getD 0 0) >>> (5 * m)) &&& 31

def canonImage (m : ℕ) : ℕ := rankApply 6 (getRank (pidx m)) m

def leaf4 (m : ℕ) : Bool :=
  decide (pidx m < 24)
    && decide (canonImage m ∈ reps4)
    && scanOK 6 m (getRank (pidx m)) (canonImage m)

set_option maxRecDepth 8192 in
lemma rowsConsistent : (List.range 24).all
    (fun i => permConsistent 4 (getPerm i) (getRank i)) = true := by
  decide +kernel

lemma perm4Consistent_of_lt {i : ℕ} (hi : i < 24) :
    permConsistent 4 (getPerm i) (getRank i) = true :=
  List.all_eq_true.mp rowsConsistent i (List.mem_range.mpr hi)

lemma pairIdx4_lt : ∀ a b : Fin 4, a < b → pairIdx 4 a.val b.val < 6 := by
  decide

set_option maxRecDepth 65536 in
lemma sweep4 : sweepMasks leaf4 6 0 = true := by decide +kernel

theorem leaf4_reflect {m : ℕ} (hm : m < 2 ^ 6) :
    canonImage m ∈ reps4
      ∧ graphOfMask₂ 4 m ∼sf graphOfMask₂ 4 (canonImage m) := by
  have hleaf : leaf4 m = true := by
    have h := sweepMasks_spec leaf4 6 0 sweep4 m hm
    rwa [zero_mul, zero_add] at h
  unfold leaf4 at hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := hleaf
  exact ⟨of_decide_eq_true hmem,
    leafParts_eqv pairIdx4_lt
      (perm4Consistent_of_lt (of_decide_eq_true hpidx)) hscan⟩

set_option maxRecDepth 8192 in
lemma finPairs4_rank_inj : ∀ p₁ ∈ finPairs 4, ∀ p₂ ∈ finPairs 4,
    pairIdx 4 p₁.1.val p₁.2.val = pairIdx 4 p₂.1.val p₂.2.val → p₁ = p₂ := by
  decide

set_option maxRecDepth 8192 in
lemma finPairs4_rank_lt :
    ∀ p ∈ finPairs 4, pairIdx 4 p.1.val p.2.val < 6 := by decide

set_option maxRecDepth 8192 in
lemma finPairs4_rank_cover : ∀ i < 6, ∃ p ∈ finPairs 4,
    pairIdx 4 p.1.val p.2.val = i := by decide

def canonOf (G : Sym2Graph 4) : ℕ := canonImage (maskOfGraph₂ G)

theorem canonOf_spec (G : Sym2Graph 4) :
    canonOf G ∈ reps4 ∧ G ∼sf graphOfMask₂ 4 (canonOf G) := by
  have hm : maskOfGraph₂ G < 2 ^ 6 :=
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 6) finPairs4_rank_lt
  obtain ⟨hmem, heqv⟩ := leaf4_reflect hm
  rw [graphOfMask₂_maskOfGraph₂ finPairs4_rank_inj G] at heqv
  exact ⟨hmem, heqv⟩

set_option maxRecDepth 65536 in
lemma reps4_distinct_bool : (reps4.all fun p => reps4.all fun q =>
    p == q || !isEmptyIsoFast_bool (graphOfMask₂ 4 p) (graphOfMask₂ 4 q))
      = true := by
  decide +kernel

lemma reps4_distinct : ∀ p ∈ reps4, ∀ q ∈ reps4,
    graphOfMask₂ 4 p ∼sf graphOfMask₂ 4 q → p = q :=
  distinct_of_bool reps4_distinct_bool

/-- Kernel-computable density of any 4-vertex pattern. -/
theorem density₁_eq_maskCount4 {N : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2Graph 4) (G : Sym2Graph N) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ ⟦G⟧
      = (maskCount N 4 (fun x => canonImage x == canonOf F)
            (maskOfGraph₂ G) : ℚ)
          / multinomialCoefficient (fun _ : Fin 1 => 4) N :=
  density₁_eq_maskCount_canon canonOf hinjN (fun _ => rfl) canonOf_spec
    reps4_distinct finPairs4_rank_inj finPairs4_rank_lt
    finPairs4_rank_cover F G

end Canon4

end FlagAlgebras.Compute.BitMask
