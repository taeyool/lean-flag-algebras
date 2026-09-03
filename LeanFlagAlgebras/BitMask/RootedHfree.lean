import LeanFlagAlgebras.BitMask.RootedCount
import LeanFlagAlgebras.BitMask.MaskBridge
import LeanFlagAlgebras.BitMask.CanonSmall
import LeanFlagAlgebras.BitMask.Density6

/-! # Forbid-filtered typed flag sets, kernel route

The completeness fact the **pruned** typed generator
(`generate_forbid_free_flags`) needs: the emitted forbid-free σ-typed
flags are exactly `univ.filter isHfree`. The bit-level forbid test `q`
(e.g. `triFreeMask`) enters through a per-class compatibility
hypothesis, so one theorem serves every forbidden graph with a mask
test; soundness of the emitted list and coverage of the `q`-free
representatives are kernel Bool side conditions, as in the unrooted
Task-4b wiring. Distinctness reuses `labeledEmitted_nodup_direct`. -/

namespace FlagAlgebras.Compute.BitMask

/-- Generic bridge from a two-sided list membership test to
`toFinset = univ.filter`, stated over an abstract `α` so instance
resolution happens at the call site (where `Sym2Flag`-headed instances
apply). -/
theorem toFinset_eq_filter_of_mem_iff {α : Type _} [Fintype α]
    [DecidableEq α] {l : List α} {p : α → Prop} [DecidablePred p]
    (h : ∀ x : α, x ∈ l ↔ p x) :
    l.toFinset = Finset.univ.filter p := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

/-- Zero triangle density of a decoded class is the bit-level test on
its own mask — the per-class compatibility the typed forbid-free
wiring feeds to `labeledEmittedHfree_mem_iff`. -/
theorem density_zero_iff_triFreeMask {mr : ℕ} {F : Sym2Graph 3}
    (hF : ∀ i j : Fin 3, s(i, j) ∈ F.edges ↔ i ≠ j)
    (hinj : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hc : ∀ a b c : Fin mr, a < b → b < c →
      (pairIdx mr a.val b.val, pairIdx mr a.val c.val, pairIdx mr b.val c.val)
        ∈ triTable mr)
    (hs : ∀ t ∈ triTable mr, ∃ a b c : Fin mr, a < b ∧ b < c
      ∧ t = (pairIdx mr a.val b.val, pairIdx mr a.val c.val,
             pairIdx mr b.val c.val))
    (G : Sym2Graph mr) :
    sym2EmptyTypeFlagDensity₁ ⟦F⟧ (⟦G⟧ : Sym2EmptyTypedFlag mr) = 0
      ↔ triFreeMask (triTable mr) (maskOfGraph₂ G) = true := by
  rw [← not_inducedContains_iff_density_eq_zero, eq_triangleGraph hF,
    inducedContains_triangleGraph_iff_hasTri,
    triFreeMask_iff hc hs, graphOfMask₂_maskOfGraph₂ hinj G]

/-- **Emitted forbid-free typed flags are exactly the `q`-free
classes** (membership form). `q` is a bit-level forbid-freeness test on
identity-order underlying masks, tied to the class predicate `p` (the
generator's density-based `isHfree`) by `hpq`; `hsound`/`hcover` are
the kernel side conditions. Representative distinctness is not
needed. -/
theorem labeledEmittedHfree_mem_iff {kr mr c : ℕ} {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr) {rreps : List ℕ} {canonImage : ℕ → ℕ}
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val < c)
    (hbitcover : ∀ i < c, ∃ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val = i)
    (hreflect : ∀ x, x < 2 ^ c → ∀ hx : RootsMatch σr mr x,
      canonImage x ∈ rreps
        ∧ ∃ hy : RootsMatch σr mr (canonImage x),
            labeledGraphOfMask σr mr hkm x hx
              ∼sf labeledGraphOfMask σr mr hkm (canonImage x) hy)
    (hrepsLt : ∀ h ∈ rreps, h < 2 ^ c)
    {q : ℕ → Bool} {p : Sym2Flag σr mr → Prop}
    (hpq : ∀ L : Sym2LabeledGraph σr mr,
      p ⟦L⟧ ↔ q (maskOfGraph₂ (underlyingGraph L)) = true)
    (Ls : List (Sym2LabeledGraph σr mr))
    (hsound : (Ls.all fun L => q (maskOfGraph₂ (underlyingGraph L))) = true)
    (hcover : ∀ h ∈ rreps, RootsMatch σr mr h → q h = true →
      h ∈ Ls.map (fun L => canonImage (rootedMaskOf L))) :
    ∀ S : Sym2Flag σr mr,
      S ∈ Ls.map (fun L => (⟦L⟧ : Sym2Flag σr mr)) ↔ p S := by
  intro S
  constructor
  · intro hS
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hS
    exact (hpq L).mpr (List.all_eq_true.mp hsound L hL)
  · intro hpS
    rw [List.mem_map]
    obtain ⟨G, rfl⟩ := Quotient.exists_rep S
    have hbG : rootedMaskOf G < 2 ^ c := rootedExtractMask_lt hboundm _ _ _
    have hrG : RootsMatch σr mr (rootedMaskOf G) :=
      rootedExtractMask_rootsMatch hkm hinjm hinjm G Finset.univ
    obtain ⟨hmem, hyc, hye⟩ := hreflect (rootedMaskOf G) hbG hrG
    have hSeq : (⟦G⟧ : Sym2Flag σr mr)
        = ⟦labeledGraphOfMask σr mr hkm
            (canonImage (rootedMaskOf G)) hyc⟧ :=
      Quotient.sound ((eqv_decode_rootedMaskOf hinjm G hkm hrG).trans hye)
    have hq : q (canonImage (rootedMaskOf G)) = true := by
      have hp' : p ⟦labeledGraphOfMask σr mr hkm
          (canonImage (rootedMaskOf G)) hyc⟧ := by
        rw [← hSeq]
        exact hpS
      have hmask := (hpq _).mp hp'
      rwa [show underlyingGraph (labeledGraphOfMask σr mr hkm
              (canonImage (rootedMaskOf G)) hyc)
            = graphOfMask₂ mr (canonImage (rootedMaskOf G)) from rfl,
        maskOfGraph₂_graphOfMask₂ hinjm hboundm hbitcover
          (hrepsLt _ hmem)] at hmask
    obtain ⟨L, hL, hLc⟩ := List.mem_map.mp (hcover _ hmem hyc hq)
    refine ⟨L, hL, ?_⟩
    have hbL : rootedMaskOf L < 2 ^ c := rootedExtractMask_lt hboundm _ _ _
    have hrL : RootsMatch σr mr (rootedMaskOf L) :=
      rootedExtractMask_rootsMatch hkm hinjm hinjm L Finset.univ
    obtain ⟨-, hyL, hyeL⟩ := hreflect (rootedMaskOf L) hbL hrL
    have heq : labeledGraphOfMask σr mr hkm
        (canonImage (rootedMaskOf L)) hyL
          = labeledGraphOfMask σr mr hkm
              (canonImage (rootedMaskOf G)) hyc := by
      congr 1
    have hmid : labeledGraphOfMask σr mr hkm
        (canonImage (rootedMaskOf L)) hyL
          ∼sf labeledGraphOfMask σr mr hkm
              (canonImage (rootedMaskOf G)) hyc := by
      rw [heq]
      exact sym2LabeledGraphEqv.refl _
    exact Quotient.sound
      ((((eqv_decode_rootedMaskOf hinjm L hkm hrL).trans hyeL).trans
          hmid).trans
        (sym2LabeledGraphEqv.symm
          ((eqv_decode_rootedMaskOf hinjm G hkm hrG).trans hye)))

/-! ## Invariant-guarded distinctness

The direct pairwise distinctness check enumerates all `mr ^ mr` vertex
maps per pair of distinct emitted masks — infeasible at `mr = 6`
(`6^6` candidates, ~12 s **per pair**). The **unrooted canonical form**
(an O(1) witness-table lookup) is invariant under any injective
bit-correspondence, so guarding the enumeration with it prunes every
pair of non-isomorphic underlying graphs; the expensive check runs only
on same-graph re-rootings. -/

/-- Unrooted canonical forms agree across any injective
bit-correspondence (packaged over the unrooted canon apparatus). -/
theorem unrootedCanonImage_eq_of_eqv {n k : ℕ} {reps : List ℕ}
    {canonImage : ℕ → ℕ} (canonOf : Sym2Graph n → ℕ)
    (hci : ∀ G : Sym2Graph n, canonOf G = canonImage (maskOfGraph₂ G))
    (hspec : ∀ G : Sym2Graph n,
      canonOf G ∈ reps ∧ G ∼sf graphOfMask₂ n (canonOf G))
    (hdist : ∀ p ∈ reps, ∀ q ∈ reps,
      graphOfMask₂ n p ∼sf graphOfMask₂ n q → p = q)
    (hinj : ∀ p₁ ∈ finPairs n, ∀ p₂ ∈ finPairs n,
      pairIdx n p₁.1.val p₁.2.val = pairIdx n p₂.1.val p₂.2.val → p₁ = p₂)
    (hbound : ∀ p ∈ finPairs n, pairIdx n p.1.val p.2.val < k)
    (hcover : ∀ i < k, ∃ p ∈ finPairs n, pairIdx n p.1.val p.2.val = i)
    {p q : ℕ} (hp : p < 2 ^ k) (hq : q < 2 ^ k)
    (h : graphOfMask₂ n p ∼sf graphOfMask₂ n q) :
    canonImage p = canonImage q := by
  have h1 := (acc_canon_spec canonOf hci hspec hdist hinj hbound hcover
    (graphOfMask₂ n q) p hp).mpr h
  rw [beq_iff_eq] at h1
  rw [h1, hci, maskOfGraph₂_graphOfMask₂ hinj hbound hcover hq]

/-- Extend a map on the non-root positions to a root-fixing vertex map.
Quantifying the distinctness check over `g : Fin (mr − kr) → Fin mr`
instead of full vertex maps shrinks the kernel enumeration from
`mr ^ mr` to `mr ^ (mr − kr)` candidates **and** keeps the `Fintype`
universe construction shallow (the `Fin mr → Fin mr` pi-universe at
`mr = 6` is a 46656-element structure whose evaluation is both slow and
C-stack-deep). -/
def rootExtend {kr mr : ℕ} (hkm : kr ≤ mr)
    (g : Fin (mr - kr) → Fin mr) : Fin mr → Fin mr :=
  fun v => if h : v.val < kr then v else g ⟨v.val - kr, by omega⟩

/-- Every root-fixing vertex map is a `rootExtend` (of its non-root
part). -/
theorem rootExtend_eq_of_fixes {kr mr : ℕ} (hkm : kr ≤ mr)
    {f : Fin mr → Fin mr}
    (hfix : ∀ i : Fin kr, f (Fin.castLE hkm i) = Fin.castLE hkm i) :
    rootExtend hkm (fun j => f ⟨kr + j.val, by omega⟩) = f := by
  funext v
  by_cases h : v.val < kr
  · have h2 : f v = v := by
      have h3 := hfix ⟨v.val, h⟩
      rwa [show Fin.castLE hkm ⟨v.val, h⟩ = v from Fin.ext rfl] at h3
    simp only [rootExtend, dif_pos h]
    exact h2.symm
  · simp only [rootExtend, dif_neg h]
    congr 1
    exact Fin.ext (by simp; omega)

/-- **Emitted typed flags are distinct, invariant-guarded**: like
`labeledEmitted_nodup_direct`, but the kernel check (a) may skip the
vertex-map enumeration whenever the (cheap) invariant `inv` — e.g. the
unrooted canonical form — separates the two masks, and (b) enumerates
only the root-fixing maps, via `rootExtend`. -/
theorem labeledEmitted_nodup_inv {kr mr c' : ℕ} {σr : Sym2FlagType kr}
    (hkm : kr ≤ mr)
    (hinjm : ∀ p₁ ∈ finPairs mr, ∀ p₂ ∈ finPairs mr,
      pairIdx mr p₁.1.val p₁.2.val = pairIdx mr p₂.1.val p₂.2.val → p₁ = p₂)
    (hboundm : ∀ p ∈ finPairs mr, pairIdx mr p.1.val p.2.val < c')
    (inv : ℕ → ℕ)
    (hinv : ∀ p q : ℕ, p < 2 ^ c' → q < 2 ^ c' →
      (∃ f : Fin mr → Fin mr, Function.Injective f
        ∧ ∀ a b : Fin mr, a < b →
            p.testBit (pairIdx mr a.val b.val)
              = q.testBit (pairIdx mr (sort2 (f a) (f b)).1.val
                  (sort2 (f a) (f b)).2.val)) → inv p = inv q)
    (Ls : List (Sym2LabeledGraph σr mr))
    (hcheck : ((Ls.map (fun L => rootedMaskOf L)).all (fun p =>
        (Ls.map (fun L => rootedMaskOf L)).all (fun q =>
          p == q
            || !(inv p == inv q)
            || !(decide (∃ g : Fin (mr - kr) → Fin mr,
                Function.Injective (rootExtend hkm g)
                ∧ ∀ a b : Fin mr, a < b →
                    p.testBit (pairIdx mr a.val b.val)
                      = q.testBit (pairIdx mr
                          (sort2 (rootExtend hkm g a) (rootExtend hkm g b)).1.val
                          (sort2 (rootExtend hkm g a) (rootExtend hkm g b)).2.val))))))
        = true)
    (hnodup : (Ls.map (fun L => rootedMaskOf L)).Nodup) :
    (Ls.map (fun L => (⟦L⟧ : Sym2Flag σr mr))).Nodup := by
  have hinjOn := List.inj_on_of_nodup_map hnodup
  refine (List.Nodup.of_map _ hnodup).map_on ?_
  intro a ha b hb hEq
  refine hinjOn ha hb ?_
  have hra : RootsMatch σr mr (rootedMaskOf a) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm a Finset.univ
  have hrb : RootsMatch σr mr (rootedMaskOf b) :=
    rootedExtractMask_rootsMatch hkm hinjm hinjm b Finset.univ
  have hab : a ∼sf b := Quotient.exact hEq
  have hchain : labeledGraphOfMask σr mr hkm (rootedMaskOf a) hra
      ∼sf labeledGraphOfMask σr mr hkm (rootedMaskOf b) hrb :=
    ((sym2LabeledGraphEqv.symm
        (eqv_decode_rootedMaskOf hinjm a hkm hra)).trans hab).trans
      (eqv_decode_rootedMaskOf hinjm b hkm hrb)
  obtain ⟨f, hf, hfix, hbits⟩ := bits_of_labeledEqv hkm hchain
  have hpa : rootedMaskOf a ∈ Ls.map (fun L => rootedMaskOf L) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hpb : rootedMaskOf b ∈ Ls.map (fun L => rootedMaskOf L) :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  have h2 := List.all_eq_true.mp
    (List.all_eq_true.mp hcheck _ hpa) _ hpb
  have hbnot : ∀ b' : Bool, (!b') = true → b' = false := by decide
  have hfeq := rootExtend_eq_of_fixes hkm hfix
  rw [Bool.or_eq_true, Bool.or_eq_true] at h2
  rcases h2 with (h2 | h2) | h2
  · exact beq_iff_eq.mp h2
  · exact absurd
      ((hbnot _ h2).symm.trans
        (beq_iff_eq.mpr (hinv _ _
          (rootedExtractMask_lt hboundm _ _ _)
          (rootedExtractMask_lt hboundm _ _ _) ⟨f, hf, hbits⟩)))
      Bool.false_ne_true
  · refine absurd ⟨fun j => f ⟨kr + j.val, by omega⟩, ?_, ?_⟩
      (of_decide_eq_false (hbnot _ h2))
    · rw [hfeq]
      exact hf
    · intro a' b' hab'
      rw [hfeq]
      exact hbits a' b' hab'

/-! ## Small-size triangle-table instances

The typed forbid-free layers at sizes 2–4 (Mantel's and `K3freeC6`'s
typed flags) need the triangle-table facts below the sizes the unrooted
`Canon5`/`Canon6` sections of `MaskBridge` instantiated. -/

namespace Canon2

lemma triTable2_cover : ∀ a b c : Fin 2, a < b → b < c →
    (pairIdx 2 a.val b.val, pairIdx 2 a.val c.val, pairIdx 2 b.val c.val)
      ∈ triTable 2 := by decide

lemma triTable2_sound : ∀ t ∈ triTable 2, ∃ a b c : Fin 2, a < b ∧ b < c
    ∧ t = (pairIdx 2 a.val b.val, pairIdx 2 a.val c.val,
           pairIdx 2 b.val c.val) := by decide

end Canon2

namespace Canon3

lemma triTable3_cover : ∀ a b c : Fin 3, a < b → b < c →
    (pairIdx 3 a.val b.val, pairIdx 3 a.val c.val, pairIdx 3 b.val c.val)
      ∈ triTable 3 := by decide

lemma triTable3_sound : ∀ t ∈ triTable 3, ∃ a b c : Fin 3, a < b ∧ b < c
    ∧ t = (pairIdx 3 a.val b.val, pairIdx 3 a.val c.val,
           pairIdx 3 b.val c.val) := by decide

end Canon3

namespace Canon4

lemma triTable4_cover : ∀ a b c : Fin 4, a < b → b < c →
    (pairIdx 4 a.val b.val, pairIdx 4 a.val c.val, pairIdx 4 b.val c.val)
      ∈ triTable 4 := by decide

lemma triTable4_sound : ∀ t ∈ triTable 4, ∃ a b c : Fin 4, a < b ∧ b < c
    ∧ t = (pairIdx 4 a.val b.val, pairIdx 4 a.val c.val,
           pairIdx 4 b.val c.val) := by decide

end Canon4

/-! ## Per-size unrooted-canon invariance instances

`Canon{n}.rmaskCanonInv` — the `hinv` argument of
`labeledEmitted_nodup_inv`, instantiated with each size's unrooted
canonical apparatus. -/

namespace Canon2

lemma rmaskCanonInv : ∀ p q : ℕ, p < 2 ^ 1 → q < 2 ^ 1 →
    (∃ f : Fin 2 → Fin 2, Function.Injective f
      ∧ ∀ a b : Fin 2, a < b →
          p.testBit (pairIdx 2 a.val b.val)
            = q.testBit (pairIdx 2 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) →
    canonImage p = canonImage q := by
  rintro p q hp hq ⟨f, hf, hbits⟩
  exact unrootedCanonImage_eq_of_eqv canonOf (fun _ => rfl) canonOf_spec
    reps2_distinct finPairs2_rank_inj finPairs2_rank_lt finPairs2_rank_cover
    hp hq (graphOfMask₂_eqv_of_bits hf hbits)

end Canon2

namespace Canon3

lemma rmaskCanonInv : ∀ p q : ℕ, p < 2 ^ 3 → q < 2 ^ 3 →
    (∃ f : Fin 3 → Fin 3, Function.Injective f
      ∧ ∀ a b : Fin 3, a < b →
          p.testBit (pairIdx 3 a.val b.val)
            = q.testBit (pairIdx 3 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) →
    canonImage p = canonImage q := by
  rintro p q hp hq ⟨f, hf, hbits⟩
  exact unrootedCanonImage_eq_of_eqv canonOf (fun _ => rfl) canonOf_spec
    reps3_distinct finPairs3_rank_inj finPairs3_rank_lt finPairs3_rank_cover
    hp hq (graphOfMask₂_eqv_of_bits hf hbits)

end Canon3

namespace Canon4

lemma rmaskCanonInv : ∀ p q : ℕ, p < 2 ^ 6 → q < 2 ^ 6 →
    (∃ f : Fin 4 → Fin 4, Function.Injective f
      ∧ ∀ a b : Fin 4, a < b →
          p.testBit (pairIdx 4 a.val b.val)
            = q.testBit (pairIdx 4 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) →
    canonImage p = canonImage q := by
  rintro p q hp hq ⟨f, hf, hbits⟩
  exact unrootedCanonImage_eq_of_eqv canonOf (fun _ => rfl) canonOf_spec
    reps4_distinct finPairs4_rank_inj finPairs4_rank_lt finPairs4_rank_cover
    hp hq (graphOfMask₂_eqv_of_bits hf hbits)

end Canon4

namespace Canon5

lemma rmaskCanonInv : ∀ p q : ℕ, p < 2 ^ 10 → q < 2 ^ 10 →
    (∃ f : Fin 5 → Fin 5, Function.Injective f
      ∧ ∀ a b : Fin 5, a < b →
          p.testBit (pairIdx 5 a.val b.val)
            = q.testBit (pairIdx 5 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) →
    canonImage p = canonImage q := by
  rintro p q hp hq ⟨f, hf, hbits⟩
  exact unrootedCanonImage_eq_of_eqv canonOf (fun _ => rfl) canonOf_spec
    reps5_distinct finPairs5_rank_inj finPairs5_rank_lt finPairs5_rank_cover
    hp hq (graphOfMask₂_eqv_of_bits hf hbits)

end Canon5

namespace Canon6

lemma rmaskCanonInv : ∀ p q : ℕ, p < 2 ^ 15 → q < 2 ^ 15 →
    (∃ f : Fin 6 → Fin 6, Function.Injective f
      ∧ ∀ a b : Fin 6, a < b →
          p.testBit (pairIdx 6 a.val b.val)
            = q.testBit (pairIdx 6 (sort2 (f a) (f b)).1.val
                (sort2 (f a) (f b)).2.val)) →
    canonImage p = canonImage q := by
  rintro p q hp hq ⟨f, hf, hbits⟩
  exact unrootedCanonImage_eq_of_eqv canonOf (fun _ => rfl) canonOf_spec
    reps6_distinct finPairs6_rank_inj finPairs6_rank_lt finPairs6_rank_cover
    hp hq (graphOfMask₂_eqv_of_bits hf hbits)

end Canon6

end FlagAlgebras.Compute.BitMask
