import LeanFlagAlgebras.BitMask.Canon5
import LeanFlagAlgebras.BitMask.Canon6
import LeanFlagAlgebras.Flags.ForbidFreePruned

/-! # From canonicalization sweeps to the forbid-free pipeline

Bridges the kernel-checked sweep completeness (`canon5_complete` /
`canon6_complete`) into the shapes the forbid-free framework consumes:

* `maskRepFlags_toFinset_eq_univ` — the listed representative decodings
  are **all** empty-typed flags (the mask analogue of
  `genEmptyTypedFlagSet n = univ`);
* `maskFreeFlags_toFinset_eq` — for **any** forbidden graph `F`,
  filtering the representatives by (decidable) induced-`F`-freeness
  yields exactly `univ.filter (sym2EmptyTypeFlagDensity₁ ⟦F⟧ · = 0)` —
  the same right-hand side as `prunedFreeFlags_toFinset_eq`, so this is
  a drop-in replacement for the completeness fact the pruned generator
  cites, with **no enumeration and no `native_decide`**.

Both are generic in the representative list, parameterized by a sweep
completeness hypothesis; the `Canon5`/`Canon6` sections instantiate
them. One sweep serves every forbid: the forbid enters only as a filter
over the (34 or 156) representatives, decided per representative by the
kernel. -/

namespace FlagAlgebras.Compute.BitMask

/-! ## Generic bridges -/

/-- The empty-typed flags named by a representative mask list. -/
def maskRepFlags (reps : List ℕ) (n : ℕ) : List (Sym2EmptyTypedFlag n) :=
  reps.map (fun h => ⟦graphOfMask₂ n h⟧)

/-- A complete representative list decodes to **all** empty-typed
flags. -/
theorem maskRepFlags_toFinset_eq_univ {n : ℕ} {reps : List ℕ}
    (hcomplete : ∀ G : Sym2Graph n, ∃ h ∈ reps, G ∼sf graphOfMask₂ n h) :
    (maskRepFlags reps n).toFinset = Finset.univ := by
  apply Finset.ext
  intro S
  simp only [maskRepFlags, List.mem_toFinset, List.mem_map, Finset.mem_univ,
    iff_true]
  obtain ⟨G, rfl⟩ := Quotient.exists_rep S
  obtain ⟨h, hmem, heqv⟩ := hcomplete G
  exact ⟨h, hmem, (Quotient.sound heqv).symm⟩

/-- The `F`-free empty-typed flags named by a representative mask list:
filter the representatives by decidable induced-`F`-freeness of their
decodings. -/
def maskFreeFlags {m : ℕ} (F : Sym2Graph m) (reps : List ℕ) (n : ℕ) :
    List (Sym2EmptyTypedFlag n) :=
  (reps.filter fun h => !decide (inducedContains F (graphOfMask₂ n h))).map
    (fun h => ⟦graphOfMask₂ n h⟧)

/-- **The sweep-to-pipeline bridge.** For a complete representative
list, the filtered decodings are exactly the flags of zero induced
`F`-density — the same statement as `prunedFreeFlags_toFinset_eq`, but
resting on the kernel sweep instead of the pruned generator. -/
theorem maskFreeFlags_toFinset_eq {m : ℕ} (F : Sym2Graph m) {n : ℕ}
    {reps : List ℕ}
    (hcomplete : ∀ G : Sym2Graph n, ∃ h ∈ reps, G ∼sf graphOfMask₂ n h) :
    (maskFreeFlags F reps n).toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) := by
  apply Finset.ext
  intro S
  simp only [maskFreeFlags, List.mem_toFinset, List.mem_map, List.mem_filter,
    Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true',
    decide_eq_false_iff_not]
  obtain ⟨G, rfl⟩ := Quotient.exists_rep S
  rw [← not_inducedContains_iff_density_eq_zero]
  constructor
  · rintro ⟨h, ⟨hmem, hfree⟩, hGh⟩ hcon
    exact hfree
      (inducedContains_of_eqv (Sym2GraphEqv.symm (Quotient.exact hGh)) hcon)
  · intro hG
    obtain ⟨h, hmem, heqv⟩ := hcomplete G
    refine ⟨h, ⟨hmem, fun hcon =>
      hG (inducedContains_of_eqv (Sym2GraphEqv.symm heqv) hcon)⟩, ?_⟩
    exact (Quotient.sound heqv).symm

/-! ## Command-facing wiring

The shape the `generate_forbid_free_empty_typed_flags` command needs: its
emitted literal graph list is exactly the `F`-free flags, given a
canonicalization map into a complete representative list plus two
**decidable** side conditions (per-graph freeness; coverage of every free
representative), which a command discharges by kernel computation. This
replaces the `native_decide` against the pruned generator — the iso-dedup
that made `flagGen.kernelDecide` infeasible beyond tiny `n` never runs. -/

/-- The flag classes named by a literal graph list. -/
def emittedFlags {n : ℕ} (Gs : List (Sym2Graph n)) :
    List (Sym2EmptyTypedFlag n) :=
  Gs.map (fun G => ⟦G⟧)

/-- An emitted list of literal graphs names exactly the `F`-free
empty-typed flags. `canonOf` sends every graph to a listed representative
of its class (`hspec`, supplied per vertex count from the sweep);
`hfree`/`hcover` are the kernel-checkable side conditions. -/
theorem emittedFreeFlags_toFinset_eq {n m : ℕ} (F : Sym2Graph m)
    {reps : List ℕ} (canonOf : Sym2Graph n → ℕ)
    (hspec : ∀ G : Sym2Graph n,
      canonOf G ∈ reps ∧ G ∼sf graphOfMask₂ n (canonOf G))
    (Gs : List (Sym2Graph n))
    (hfree : ∀ G ∈ Gs, ¬ inducedContains F G)
    (hcover : ∀ h ∈ reps, ¬ inducedContains F (graphOfMask₂ n h) →
      h ∈ Gs.map canonOf) :
    (emittedFlags Gs).toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) := by
  apply Finset.ext
  intro S
  simp only [emittedFlags, List.mem_toFinset, List.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and]
  obtain ⟨G', rfl⟩ := Quotient.exists_rep S
  rw [← not_inducedContains_iff_density_eq_zero]
  constructor
  · rintro ⟨G, hG, hGS⟩ hcon
    exact hfree G hG
      (inducedContains_of_eqv (Sym2GraphEqv.symm (Quotient.exact hGS)) hcon)
  · intro hfreeG'
    obtain ⟨hmem, heqv⟩ := hspec G'
    have hfreeh : ¬ inducedContains F (graphOfMask₂ n (canonOf G')) :=
      fun hcon => hfreeG' (inducedContains_of_eqv (Sym2GraphEqv.symm heqv) hcon)
    obtain ⟨G, hG, hGh⟩ := List.mem_map.mp (hcover (canonOf G') hmem hfreeh)
    refine ⟨G, hG, ?_⟩
    have h1 := (hspec G).2
    rw [hGh] at h1
    exact Quotient.sound (h1.trans (Sym2GraphEqv.symm heqv))

/-- A 3-vertex graph whose adjacency is `≠` **is** `triangleGraph` (its
edge finsets agree), letting the triangle-specific lemmas apply to any
user-supplied K₃ term (e.g. `completeSym2Graph 3`). -/
theorem eq_triangleGraph {F : Sym2Graph 3}
    (hF : ∀ i j : Fin 3, s(i, j) ∈ F.edges ↔ i ≠ j) : F = triangleGraph := by
  refine Sym2Graph.ext ?_
  ext e
  induction e using Sym2.ind with | _ i j =>
  rw [hF i j]
  fin_cases i <;> fin_cases j <;> decide

/-! ## Bit-level triangle detection

The generic `decide (inducedContains …)` filter above is what the bridge
theorem states, but deciding it in the kernel costs an embedding search
per representative — fine at `n = 5`, marginal at `n = 6`, prohibitive
at `n = 7`. For the triangle (the most common forbid) we provide a
bit-level test in the sweep style: a precomputed table lists, for each
sorted vertex triple, the three pair ranks; the mask is triangle-free
iff no listed triple has all three bits set. Correctness is
parameterized by two kernel-checkable table hypotheses, so the same
lemma serves every vertex count. -/

/-- The sorted triples of `Fin n`, in lexicographic order. -/
def finTriples (n : ℕ) : List (Fin n × Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).flatMap fun b =>
      (List.finRange n).filterMap fun c =>
        if a < b ∧ b < c then some (a, b, c) else none

/-- The three pair ranks of each sorted vertex triple. -/
def triTable (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (finTriples n).map fun t =>
    (pairIdx n t.1.val t.2.1.val, pairIdx n t.1.val t.2.2.val,
     pairIdx n t.2.1.val t.2.2.val)

/-- Bit-level triangle-freeness: no listed triple has all three of its
pairs present. -/
def triFreeMask (ts : List (ℕ × ℕ × ℕ)) (m : ℕ) : Bool :=
  ts.all fun t => !(m.testBit t.1 && m.testBit t.2.1 && m.testBit t.2.2)

/-- `hasTri` with a sorted witness: three distinct pairwise-adjacent
vertices can always be listed in increasing order (the three unordered
pairs are unchanged). -/
lemma hasTri_iff_sorted {n : ℕ} {G : Sym2Graph n} :
    hasTri G ↔ ∃ a b c : Fin n, a < b ∧ b < c
      ∧ s(a, b) ∈ G.edges ∧ s(a, c) ∈ G.edges ∧ s(b, c) ∈ G.edges := by
  constructor
  · rintro ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩
    rcases lt_or_gt_of_ne hab with h1 | h1
    · rcases lt_or_gt_of_ne hbc with h2 | h2
      · exact ⟨a, b, c, h1, h2, eab, eac, ebc⟩
      · rcases lt_or_gt_of_ne hac with h3 | h3
        · exact ⟨a, c, b, h3, h2, eac, eab, Sym2.eq_swap ▸ ebc⟩
        · exact ⟨c, a, b, h3, h1, Sym2.eq_swap ▸ eac, Sym2.eq_swap ▸ ebc, eab⟩
    · rcases lt_or_gt_of_ne hac with h2 | h2
      · exact ⟨b, a, c, h1, h2, Sym2.eq_swap ▸ eab, ebc, eac⟩
      · rcases lt_or_gt_of_ne hbc with h3 | h3
        · exact ⟨b, c, a, h3, h2, ebc, Sym2.eq_swap ▸ eab, Sym2.eq_swap ▸ eac⟩
        · exact ⟨c, b, a, h3, h1, Sym2.eq_swap ▸ ebc, Sym2.eq_swap ▸ eac,
            Sym2.eq_swap ▸ eab⟩
  · rintro ⟨a, b, c, hab, hbc, eab, eac, ebc⟩
    exact ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, eab, eac, ebc⟩

/-- The bit-level test says exactly: the decoded graph has no triangle.
The table hypotheses (cover: every sorted triple's rank tuple is
listed; soundness: every listed tuple comes from a sorted triple) are
kernel-checkable per vertex count. -/
theorem triFreeMask_iff {n : ℕ} {ts : List (ℕ × ℕ × ℕ)} {m : ℕ}
    (hcover : ∀ a b c : Fin n, a < b → b < c →
      (pairIdx n a.val b.val, pairIdx n a.val c.val, pairIdx n b.val c.val)
        ∈ ts)
    (hsound : ∀ t ∈ ts, ∃ a b c : Fin n, a < b ∧ b < c
      ∧ t = (pairIdx n a.val b.val, pairIdx n a.val c.val,
             pairIdx n b.val c.val)) :
    triFreeMask ts m = true ↔ ¬ hasTri (graphOfMask₂ n m) := by
  unfold triFreeMask
  rw [List.all_eq_true, hasTri_iff_sorted]
  constructor
  · rintro hall ⟨a, b, c, hab, hbc, eab, eac, ebc⟩
    have h1 := (testBit_iff_mem_edges₂ hab).mpr eab
    have h2 := (testBit_iff_mem_edges₂ (hab.trans hbc)).mpr eac
    have h3 := (testBit_iff_mem_edges₂ hbc).mpr ebc
    have hfalse := hall _ (hcover a b c hab hbc)
    simp [h1, h2, h3] at hfalse
  · intro hno t ht
    obtain ⟨a, b, c, hab, hbc, rfl⟩ := hsound t ht
    cases h1 : m.testBit (pairIdx n a.val b.val) <;>
      cases h2 : m.testBit (pairIdx n a.val c.val) <;>
        cases h3 : m.testBit (pairIdx n b.val c.val) <;> simp
    exact hno ⟨a, b, c, hab, hbc,
      (testBit_iff_mem_edges₂ hab).mp h1,
      (testBit_iff_mem_edges₂ (hab.trans hbc)).mp h2,
      (testBit_iff_mem_edges₂ hbc).mp h3⟩

/-! ### Bool-form side conditions for the command wiring

The generator command discharges the freeness/coverage side conditions
of `emittedFreeFlags_toFinset_eq` by kernel computation. Prop-level
`∀ _ ∈ _` decidable instances are an order of magnitude slower to reduce
than one `List.all` Boolean (measured ~90 s vs ~5 s at `n = 6`), so the
kernel-facing statements are Bool `all`s over bit-level tests — the
sweep-leaf style — and these converters lift them to the Prop forms the
bridge consumes. Triangle forbids only for now; `K_r` tables generalize
the same way. -/

/-- Freeness from the bit-level test on each emitted graph's own mask. -/
theorem hfree_of_triFreeMask {n : ℕ} {F : Sym2Graph 3}
    (hF : ∀ i j : Fin 3, s(i, j) ∈ F.edges ↔ i ≠ j)
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (hc : ∀ a b c : Fin n, a < b → b < c →
      (pairIdx n a.val b.val, pairIdx n a.val c.val, pairIdx n b.val c.val)
        ∈ triTable n)
    (hs : ∀ t ∈ triTable n, ∃ a b c : Fin n, a < b ∧ b < c
      ∧ t = (pairIdx n a.val b.val, pairIdx n a.val c.val,
             pairIdx n b.val c.val))
    {Gs : List (Sym2Graph n)}
    (h : (Gs.all fun G => triFreeMask (triTable n) (maskOfGraph₂ G)) = true) :
    ∀ G ∈ Gs, ¬ inducedContains F G := by
  intro G hG
  rw [eq_triangleGraph hF, inducedContains_triangleGraph_iff_hasTri]
  have h2 := (triFreeMask_iff hc hs).mp (List.all_eq_true.mp h G hG)
  rwa [graphOfMask₂_maskOfGraph₂ hinj G] at h2

/-- Coverage from the bit-level test on each representative. -/
theorem hcover_of_triFreeMask {n : ℕ} {F : Sym2Graph 3}
    (hF : ∀ i j : Fin 3, s(i, j) ∈ F.edges ↔ i ≠ j)
    (hc : ∀ a b c : Fin n, a < b → b < c →
      (pairIdx n a.val b.val, pairIdx n a.val c.val, pairIdx n b.val c.val)
        ∈ triTable n)
    (hs : ∀ t ∈ triTable n, ∃ a b c : Fin n, a < b ∧ b < c
      ∧ t = (pairIdx n a.val b.val, pairIdx n a.val c.val,
             pairIdx n b.val c.val))
    {reps L : List ℕ}
    (h : (reps.all fun h' =>
      !triFreeMask (triTable n) h' || decide (h' ∈ L)) = true) :
    ∀ h' ∈ reps, ¬ inducedContains F (graphOfMask₂ n h') → h' ∈ L := by
  intro h' hmem hfree
  rw [eq_triangleGraph hF, inducedContains_triangleGraph_iff_hasTri] at hfree
  have htf : triFreeMask (triTable n) h' = true :=
    (triFreeMask_iff hc hs).mpr hfree
  have hb := List.all_eq_true.mp h h' hmem
  rw [htf, Bool.not_true, Bool.false_or] at hb
  exact of_decide_eq_true hb

/-! ## Five-vertex instances -/

namespace Canon5

/-- All 5-vertex empty-typed flags, as the 34 representative
decodings. -/
theorem maskRepFlags5_toFinset_eq_univ :
    (maskRepFlags reps5 5).toFinset = Finset.univ :=
  maskRepFlags_toFinset_eq_univ canon5_complete

/-- The `F`-free 5-vertex flags, for any forbidden `F` — kernel-only
replacement for the pruned generator's completeness at `n = 5`. -/
theorem maskFreeFlags5_toFinset_eq {m : ℕ} (F : Sym2Graph m) :
    (maskFreeFlags F reps5 5).toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) :=
  maskFreeFlags_toFinset_eq F canon5_complete

/-- Canonicalize a 5-vertex graph: encode it and look up its canonical
representative through the witness tables. -/
def canonOf (G : Sym2Graph 5) : ℕ := canonImage (maskOfGraph₂ G)

/-- `canonOf` lands in the representative list and preserves the flag
class — the sweep fact the command-facing wiring consumes. -/
theorem canonOf_spec (G : Sym2Graph 5) :
    canonOf G ∈ reps5 ∧ G ∼sf graphOfMask₂ 5 (canonOf G) := by
  have hm : maskOfGraph₂ G < 2 ^ 10 :=
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 10) finPairs5_rank_lt
  obtain ⟨hmem, heqv⟩ := leaf5_reflect hm
  rw [graphOfMask₂_maskOfGraph₂ finPairs5_rank_inj G] at heqv
  exact ⟨hmem, heqv⟩

set_option maxRecDepth 8192 in
lemma triTable5_cover : ∀ a b c : Fin 5, a < b → b < c →
    (pairIdx 5 a.val b.val, pairIdx 5 a.val c.val, pairIdx 5 b.val c.val)
      ∈ triTable 5 := by decide

set_option maxRecDepth 8192 in
lemma triTable5_sound : ∀ t ∈ triTable 5, ∃ a b c : Fin 5, a < b ∧ b < c
    ∧ t = (pairIdx 5 a.val b.val, pairIdx 5 a.val c.val,
           pairIdx 5 b.val c.val) := by decide

/-- The triangle-free 5-vertex representatives, by the bit-level
test. -/
def k3FreeReps5 : List ℕ := reps5.filter (triFreeMask (triTable 5))

set_option maxRecDepth 8192 in
/-- 14 triangle-free classes on five vertices (kernel-checked). -/
example : k3FreeReps5.length = 14 := by decide +kernel

/-- The bit-level filter agrees with the generic induced-containment
filter. -/
theorem k3FreeReps5_filter_eq :
    k3FreeReps5 = reps5.filter
      (fun h => !decide (inducedContains triangleGraph (graphOfMask₂ 5 h))) :=
  List.filter_congr fun h _ => by
    rw [Bool.eq_iff_iff, triFreeMask_iff triTable5_cover triTable5_sound,
      Bool.not_eq_true', decide_eq_false_iff_not,
      inducedContains_triangleGraph_iff_hasTri]

/-- The 14 triangle-free 5-vertex flags. -/
def k3FreeFlags5 : List (Sym2EmptyTypedFlag 5) :=
  k3FreeReps5.map (fun h => ⟦graphOfMask₂ 5 h⟧)

/-- **Kernel-only K₃-free completeness at `n = 5`**: the 14 filtered
representative decodings are exactly the flags of zero triangle
density. -/
theorem k3FreeFlags5_toFinset_eq :
    k3FreeFlags5.toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ S = 0) := by
  have heq : k3FreeFlags5 = maskFreeFlags triangleGraph reps5 5 := by
    unfold k3FreeFlags5 maskFreeFlags
    rw [k3FreeReps5_filter_eq]
  rw [heq]
  exact maskFreeFlags5_toFinset_eq triangleGraph

end Canon5

/-! ## Six-vertex instances -/

namespace Canon6

/-- All 6-vertex empty-typed flags, as the 156 representative
decodings. -/
theorem maskRepFlags6_toFinset_eq_univ :
    (maskRepFlags reps6 6).toFinset = Finset.univ :=
  maskRepFlags_toFinset_eq_univ canon6_complete

/-- The `F`-free 6-vertex flags, for any forbidden `F` — kernel-only
replacement for the pruned generator's completeness at `n = 6`. -/
theorem maskFreeFlags6_toFinset_eq {m : ℕ} (F : Sym2Graph m) :
    (maskFreeFlags F reps6 6).toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦F⟧ S = 0) :=
  maskFreeFlags_toFinset_eq F canon6_complete

/-- Canonicalize a 6-vertex graph: encode it and look up its canonical
representative through the witness tables. -/
def canonOf (G : Sym2Graph 6) : ℕ := canonImage (maskOfGraph₂ G)

/-- `canonOf` lands in the representative list and preserves the flag
class — the sweep fact the command-facing wiring consumes. -/
theorem canonOf_spec (G : Sym2Graph 6) :
    canonOf G ∈ reps6 ∧ G ∼sf graphOfMask₂ 6 (canonOf G) := by
  have hm : maskOfGraph₂ G < 2 ^ 15 :=
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 15) finPairs6_rank_lt
  obtain ⟨hmem, heqv⟩ := leaf6_reflect hm
  rw [graphOfMask₂_maskOfGraph₂ finPairs6_rank_inj G] at heqv
  exact ⟨hmem, heqv⟩

set_option maxRecDepth 8192 in
lemma triTable6_cover : ∀ a b c : Fin 6, a < b → b < c →
    (pairIdx 6 a.val b.val, pairIdx 6 a.val c.val, pairIdx 6 b.val c.val)
      ∈ triTable 6 := by decide

set_option maxRecDepth 8192 in
lemma triTable6_sound : ∀ t ∈ triTable 6, ∃ a b c : Fin 6, a < b ∧ b < c
    ∧ t = (pairIdx 6 a.val b.val, pairIdx 6 a.val c.val,
           pairIdx 6 b.val c.val) := by decide

/-- The triangle-free 6-vertex representatives, by the bit-level
test. -/
def k3FreeReps6 : List ℕ := reps6.filter (triFreeMask (triTable 6))

set_option maxRecDepth 8192 in
/-- 38 triangle-free classes on six vertices (kernel-checked). -/
example : k3FreeReps6.length = 38 := by decide +kernel

/-- The bit-level filter agrees with the generic induced-containment
filter. -/
theorem k3FreeReps6_filter_eq :
    k3FreeReps6 = reps6.filter
      (fun h => !decide (inducedContains triangleGraph (graphOfMask₂ 6 h))) :=
  List.filter_congr fun h _ => by
    rw [Bool.eq_iff_iff, triFreeMask_iff triTable6_cover triTable6_sound,
      Bool.not_eq_true', decide_eq_false_iff_not,
      inducedContains_triangleGraph_iff_hasTri]

/-- The 38 triangle-free 6-vertex flags. -/
def k3FreeFlags6 : List (Sym2EmptyTypedFlag 6) :=
  k3FreeReps6.map (fun h => ⟦graphOfMask₂ 6 h⟧)

/-- **Kernel-only K₃-free completeness at `n = 6`**: the 38 filtered
representative decodings are exactly the flags of zero triangle
density — the statement `K3freeC6`-style examples need from their
flag generation, with no `native_decide`. -/
theorem k3FreeFlags6_toFinset_eq :
    k3FreeFlags6.toFinset
      = Finset.univ.filter
          (fun S => sym2EmptyTypeFlagDensity₁ ⟦triangleGraph⟧ S = 0) := by
  have heq : k3FreeFlags6 = maskFreeFlags triangleGraph reps6 6 := by
    unfold k3FreeFlags6 maskFreeFlags
    rw [k3FreeReps6_filter_eq]
  rw [heq]
  exact maskFreeFlags6_toFinset_eq triangleGraph

end Canon6

end FlagAlgebras.Compute.BitMask
