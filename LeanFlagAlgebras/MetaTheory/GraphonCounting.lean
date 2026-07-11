import LeanFlagAlgebras.MetaTheory.GraphonStep
import LeanFlagAlgebras.FlagAlgebra.FlagSequence

/-! # The step-graphon counting lemma and density of the graphon range

The induced-density profile of a step graphon approximates the finite flag density with the
**explicit error `n(n−1)/N`**, and consequently every unlabelled limit functional is a limit
of graphon-hom points — **the range of `graphonHomPoint` is dense in `X_∅`**.

* `descFactorial_div_pow_le_one` / `one_sub_choose_div_le_descFactorial_div_pow` — the
  sampling-with-vs-without-replacement bounds `1 − C(n,2)/N ≤ (N)ₙ/Nⁿ ≤ 1`.
* `graphonProfileFun_stepGraphon_sub_le` — **the counting lemma**: for `G` on `Fin N` and a
  test flag `F` of size `n`,
  `|graphonProfileFun (stepGraphon hN G) F − flagDensity₁ F.2 (graphFlag G)| ≤ n(n−1)/N`.
  (Injective cell tuples reproduce the subset count of `flagDensity₁_graphFlag` times `n!`;
  non-injective tuples have mass at most `C(n,2)/N` by the union bound; the falling-factorial
  defect contributes the other `C(n,2)/N`.)
* `tendsto_graphonHomPoint_stepGraphon` — along a flag sequence converging to `φ`, the step
  graphons' hom points converge to `posHomPoint φ` (sizes grow by `Increases`, so the error
  vanishes; convergence is pointwise on the profile space).
* `exists_graphonHomPoint_seq_tendsto` — **density**: every `φ : PositiveHom ∅ₜ` is the
  limit of graphon-hom points (`positiveHom_as_flagSeq_limit` supplies the sequence).

The sole remaining piece of `exists_graphon_rep` beyond this file's results is
`IsClosed (Set.range graphonHomPoint)`.

Everything is Tier-1.
-/

open MeasureTheory unitInterval Finset Filter
open scoped Classical Topology

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-! ## The replacement bounds -/

theorem descFactorial_div_pow_le_one (N n : ℕ) :
    (N.descFactorial n : ℝ) / (N : ℝ) ^ n ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.descFactorial_le_pow N n) (by positivity)

/-- Pascal's identity specialised to `choose 2`, used to unfold `(n+1).choose 2` in the
induction below. -/
private lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  have h := Nat.choose_succ_succ' n 1
  simpa [Nat.choose_one_right] using h

/-- Sampling without replacement differs from with replacement by at most the birthday
bound: `1 − C(n,2)/N ≤ (N)ₙ/Nⁿ` (the standard product inequality
`∏_{i<n} (1 − i/N) ≥ 1 − Σ_{i<n} i/N`). -/
theorem one_sub_choose_div_le_descFactorial_div_pow (N n : ℕ) (hN : N ≠ 0) :
    1 - (n.choose 2 : ℝ) / N ≤ (N.descFactorial n : ℝ) / (N : ℝ) ^ n := by
  have hNR : (0 : ℝ) < N := by
    have : (0 : ℕ) < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  induction n with
  | zero => simp
  | succ n ih =>
    have hpascal : (((n + 1).choose 2 : ℕ) : ℝ) = (n : ℝ) + (n.choose 2 : ℝ) := by
      exact_mod_cast choose_two_succ n
    rcases le_or_gt n N with hle | hlt
    · -- `n ≤ N`: the falling-factorial recursion with the exact real difference.
      have hcast : ((N - n : ℕ) : ℝ) = (N : ℝ) - n := Nat.cast_sub hle
      have hdN_nonneg : (0 : ℝ) ≤ ((N : ℝ) - n) / N := by
        rw [← hcast]; positivity
      have hdN_le_one : ((N : ℝ) - n) / N ≤ 1 := by
        rw [div_le_one hNR]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hkey : (N.descFactorial (n + 1) : ℝ) / (N : ℝ) ^ (n + 1)
          = (((N : ℝ) - n) / N) * ((N.descFactorial n : ℝ) / (N : ℝ) ^ n) := by
        rw [Nat.descFactorial_succ]
        push_cast
        rw [hcast]
        rw [pow_succ]
        field_simp
      rw [hkey]
      have hchoose_nonneg : (0 : ℝ) ≤ (n.choose 2 : ℝ) / N := by positivity
      have hmul : (((N : ℝ) - n) / N) * (1 - (n.choose 2 : ℝ) / N)
          ≤ (((N : ℝ) - n) / N) * ((N.descFactorial n : ℝ) / (N : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih hdN_nonneg
      refine le_trans ?_ hmul
      rw [hpascal]
      have hN2 : (N:ℝ) * N ≠ 0 := by positivity
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
      field_simp
      nlinarith [mul_nonneg hchoose_nonneg (sub_nonneg.mpr hdN_le_one), sq_nonneg ((N:ℝ) - n)]
    · -- `N < n`, hence also `N < n + 1`: the falling factorial vanishes.
      have hlt1 : N < n + 1 := Nat.lt_succ_of_lt hlt
      have hzero : N.descFactorial (n + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hlt1
      rw [hzero]
      simp only [Nat.cast_zero, zero_div]
      rw [hpascal]
      have hnN : (N : ℝ) < n := by exact_mod_cast hlt
      have hchoose_nonneg : (0 : ℝ) ≤ (n.choose 2 : ℝ) := by positivity
      have hone_le : (1 : ℝ) ≤ ((n : ℝ) + (n.choose 2 : ℝ)) / N := by
        rw [le_div_iff₀ hNR]; nlinarith
      linarith

/-! ## Nat-arithmetic helpers for the counting lemma -/

/-- `n*(n-1) + n = n*n`, a trunc-subtraction identity used to unfold Pascal's rule. -/
private lemma n_mul_pred_add_self (n : ℕ) : n * (n - 1) + n = n * n := by
  cases n with
  | zero => simp
  | succ m => simp [Nat.mul_succ]

/-- `2 * C(n,2) = n*(n-1)`, the doubled binomial identity. -/
private lemma two_mul_choose_two : ∀ n : ℕ, 2 * n.choose 2 = n * (n - 1)
  | 0 => rfl
  | (n + 1) => by
      have ih := two_mul_choose_two n
      have hpred := n_mul_pred_add_self n
      rw [choose_two_succ, Nat.succ_sub_one, Nat.mul_add, ih]
      have heq : (n + 1) * n = n * n + n := by ring
      rw [heq]
      linarith

/-- The strictly-increasing pairs of `Fin n` number exactly `C(n,2)` (the other half of
`Fin n × Fin n`'s off-diagonal, split by the `Prod.swap` bijection). -/
private lemma card_belowDiagPairs (n : ℕ) : (belowDiagPairs n).card = n.choose 2 := by
  classical
  set A := belowDiagPairs n with hA
  set B := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1) with hB
  have hswap : A.card = B.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      rw [hA, mem_belowDiagPairs] at hp
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp⟩
    · intro p1 hp1 p2 hp2 heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      exact Prod.ext h2 h1
    · intro q hq
      rw [hB, Finset.mem_filter] at hq
      refine ⟨(q.2, q.1), ?_, by ext <;> simp⟩
      rw [hA, mem_belowDiagPairs]
      exact hq.2
  have hunion : A ∪ B = (Finset.univ : Finset (Fin n)).offDiag := by
    ext p
    simp only [Finset.mem_union, hA, hB, mem_belowDiagPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_offDiag]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    rw [hA, mem_belowDiagPairs] at hpA
    rw [hB, Finset.mem_filter] at hpB
    exact absurd hpA (asymm hpB.2)
  have hcardunion : A.card + B.card = (Finset.univ : Finset (Fin n)).offDiag.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcardunion
  have h2A : 2 * A.card = n * n - n := by rw [← hcardunion, hswap]; ring
  have hchoose : 2 * n.choose 2 = n * n - n := by
    have h := two_mul_choose_two n
    have hid : n * (n - 1) = n * n - n := by
      cases n with
      | zero => simp
      | succ m => rw [Nat.succ_sub_one, Nat.mul_succ]; omega
    rwa [hid] at h
  omega

/-! ## The cylinder-decomposition change of variables -/

/-- The cylinder of samples realising a fixed cell tuple `t`: literally the product of the
`n` cell fibres. -/
private lemma cylinder_eq_pi {n N : ℕ} (hN : N ≠ 0) (t : Fin n → Fin N) :
    {c : Fin n → unitInterval | cellIdx N hN ∘ c = t}
      = Set.pi Set.univ (fun i => cellIdx N hN ⁻¹' {t i}) := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_preimage,
    Set.mem_singleton_iff]
  rw [funext_iff]
  rfl

/-- The volume of a cell-tuple cylinder is exactly `1/N^n` (independence of the `n`
coordinates plus `volume_cellIdx_preimage`). -/
private lemma volume_cylinder {n N : ℕ} (hN : N ≠ 0) (t : Fin n → Fin N) :
    volume {c : Fin n → unitInterval | cellIdx N hN ∘ c = t} = ((N : ENNReal) ^ n)⁻¹ := by
  rw [cylinder_eq_pi hN t, volume_pi_pi]
  simp_rw [volume_cellIdx_preimage N hN]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.inv_pow]

/-- The cell-tuple cylinders are measurable. -/
private lemma measurableSet_cylinder {n N : ℕ} (hN : N ≠ 0) (t : Fin n → Fin N) :
    MeasurableSet {c : Fin n → unitInterval | cellIdx N hN ∘ c = t} := by
  rw [cylinder_eq_pi hN t]
  exact MeasurableSet.univ_pi
    (fun i => (measurable_cellIdx N hN) (measurableSet_singleton (t i)))

/-- **The cylinder-decomposition change of variables**: integrating a function of the cell
tuple against the sample measure amounts to averaging its (finitely many) values over the
uniform cell tuples. -/
private lemma integral_comp_cellIdx {n N : ℕ} (hN : N ≠ 0) (f : (Fin n → Fin N) → ℝ) :
    ∫ c : Fin n → unitInterval, f (cellIdx N hN ∘ c)
      = (∑ t : Fin n → Fin N, f t) / (N : ℝ) ^ n := by
  classical
  have hpt : ∀ c : Fin n → unitInterval, f (cellIdx N hN ∘ c)
      = ∑ t : Fin n → Fin N,
          {c : Fin n → unitInterval | cellIdx N hN ∘ c = t}.indicator (fun _ => f t) c := by
    intro c
    simp_rw [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq Finset.univ (cellIdx N hN ∘ c) f, if_pos (Finset.mem_univ _)]
  simp_rw [hpt]
  rw [integral_finset_sum]
  · have hterm : ∀ t : Fin n → Fin N,
        ∫ c : Fin n → unitInterval,
            {c : Fin n → unitInterval | cellIdx N hN ∘ c = t}.indicator (fun _ => f t) c
          = f t / (N : ℝ) ^ n := by
      intro t
      rw [integral_indicator_const (f t) (measurableSet_cylinder hN t)]
      rw [smul_eq_mul, measureReal_def, volume_cylinder hN t]
      rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, div_eq_inv_mul]
    simp_rw [hterm, Finset.sum_div]
  · intro t _
    exact (integrable_const (f t)).indicator (measurableSet_cylinder hN t)

/-- **The profile-as-tuple-count identity**: the `stepGraphon` profile of `F2` is the exact
probability that a uniform cell tuple realises the flag class `F2`. -/
private lemma profile_eq_tupleCount {N n : ℕ} (hN : N ≠ 0) (G : SimpleGraph (Fin N))
    (F2 : Flag ∅ₜ (Fin n)) :
    graphonProfileFun (stepGraphon hN G) ⟨n, F2⟩
      = ((Finset.univ.filter (fun t : Fin n → Fin N => graphFlag (G.comap t) = F2)).card : ℝ)
        / (N : ℝ) ^ n := by
  classical
  show (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => graphFlag H = F2),
      graphonFlagDensity (stepGraphon hN G) H) = _
  unfold graphonFlagDensity
  rw [← integral_finset_sum _ (fun H _ => integrable_inducedWeight (stepGraphon hN G) H)]
  have hpt : ∀ c : Fin n → unitInterval,
      (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => graphFlag H = F2),
        inducedWeight (stepGraphon hN G) H c)
        = (if graphFlag (G.comap (cellIdx N hN ∘ c)) = F2 then (1 : ℝ) else 0) := by
    intro c
    simp_rw [inducedWeight_stepGraphon]
    by_cases hclass : graphFlag (G.comap (cellIdx N hN ∘ c)) = F2
    · rw [if_pos hclass,
        Finset.sum_eq_single (G.comap (cellIdx N hN ∘ c))]
      · rw [if_pos rfl]
      · intro H _ hne
        rw [if_neg (Ne.symm hne)]
      · intro hnotmem
        exact absurd (Finset.mem_filter.mpr
          (⟨Finset.mem_univ (G.comap (cellIdx N hN ∘ c)), hclass⟩ :
            G.comap (cellIdx N hN ∘ c) ∈ Finset.univ
              ∧ graphFlag (G.comap (cellIdx N hN ∘ c)) = F2)) hnotmem
    · rw [if_neg hclass]
      apply Finset.sum_eq_zero
      intro H hH
      apply if_neg
      intro heq
      exact hclass (heq ▸ (Finset.mem_filter.mp hH).2)
  simp_rw [hpt]
  rw [integral_comp_cellIdx hN (fun t : Fin n → Fin N => if graphFlag (G.comap t) = F2 then (1:ℝ) else 0)]
  congr 1
  exact Finset.sum_boole _ _

/-! ## Injective tuples: the subset-times-`n!` count -/

/-- A tuple whose image (as a `Finset`) has the full expected cardinality `n` is injective. -/
private lemma injective_of_mem_fiber {n N : ℕ} {S : Finset (Fin N)} {t : Fin n → Fin N}
    (hS : S.card = n) (ht : Finset.image t Finset.univ = S) : Function.Injective t := by
  classical
  have hcard : (Finset.image t (Finset.univ : Finset (Fin n))).card
      = (Finset.univ : Finset (Fin n)).card := by
    rw [ht, hS, Finset.card_univ, Fintype.card_fin]
  have hinj := Finset.injOn_of_card_image_eq hcard
  intro a b hab
  exact hinj (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab

/-- The tuples realising a fixed `n`-element image `S`, packaged as an equivalence with
`Fin n ≃ ↥S`: an injective tuple with range `S` is exactly a bijection onto `S`. -/
private noncomputable def fiberEquiv {n N : ℕ} (S : Finset (Fin N)) (hS : S.card = n) :
    {t : Fin n → Fin N // t ∈ Finset.univ.filter (fun t => Finset.image t Finset.univ = S)}
      ≃ (Fin n ≃ (S : Finset (Fin N))) where
  toFun t :=
    have ht : Finset.image t.1 Finset.univ = S := (Finset.mem_filter.mp t.2).2
    have hmem : ∀ i : Fin n, t.1 i ∈ S := by
      intro i
      have h1 : t.1 i ∈ Finset.image t.1 Finset.univ :=
        Finset.mem_image_of_mem t.1 (Finset.mem_univ i)
      rwa [ht] at h1
    Equiv.ofBijective (fun i => (⟨t.1 i, hmem i⟩ : (S : Finset (Fin N))))
      ⟨fun a b hab => injective_of_mem_fiber hS ht (Subtype.ext_iff.mp hab),
        fun y => by
          have hy : y.1 ∈ Finset.image t.1 Finset.univ := by rw [ht]; exact y.2
          obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
          exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨fun i => (e i : Fin N), by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
  left_inv t := by ext i; rfl
  right_inv e := by ext i; rfl

/-- The number of tuples realising a fixed `n`-element image is `n!`. -/
private lemma card_fiber_eq_factorial {n N : ℕ} (S : Finset (Fin N)) (hS : S.card = n) :
    (Finset.univ.filter (fun t : Fin n → Fin N => Finset.image t Finset.univ = S)).card
      = n.factorial := by
  classical
  have hcardS : Fintype.card (Fin n) = Fintype.card (S : Finset (Fin N)) := by
    rw [Fintype.card_fin, Fintype.card_coe, hS]
  have hcongr := Fintype.card_congr (fiberEquiv S hS)
  rw [Fintype.card_coe, Fintype.card_equiv (Fintype.equivOfCardEq hcardS), Fintype.card_fin]
    at hcongr
  exact hcongr

/-- Two injective tuples with the same image give the same `graphFlag` of the comapped graph
(they differ by a domain permutation of `Fin n`, and relabelling does not change the flag
class). -/
private lemma graphFlag_comap_eq_of_image_eq {n N : ℕ} (G : SimpleGraph (Fin N))
    {S : Finset (Fin N)} (hS : S.card = n) {t1 t2 : Fin n → Fin N}
    (ht1 : Finset.image t1 Finset.univ = S) (ht2 : Finset.image t2 Finset.univ = S) :
    graphFlag (G.comap t1) = graphFlag (G.comap t2) := by
  set e1 := (fiberEquiv S hS) ⟨t1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1⟩⟩ with he1
  set e2 := (fiberEquiv S hS) ⟨t2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2⟩⟩ with he2
  have ht1' : ∀ i, t1 i = (e1 i : Fin N) := fun i => rfl
  have ht2' : ∀ i, t2 i = (e2 i : Fin N) := fun i => rfl
  set pm : Fin n ≃ Fin n := e2.trans e1.symm with hpm
  have hcomp : t2 = t1 ∘ ⇑pm := by
    funext i
    show t2 i = t1 (pm i)
    rw [ht2' i, ht1' (pm i)]
    congr 1
    rw [hpm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hcomp, ← SimpleGraph.comap_comap pm t1]
  exact (graphFlag_comap_equiv pm (G.comap t1)).symm

/-- Vertex subsets inducing a copy of an `n`-vertex graph have cardinality `n`. -/
private lemma card_eq_of_induce_iso' {N n : ℕ} {G : SimpleGraph (Fin N)} {Frep : SimpleGraph (Fin n)}
    {S : Finset (Fin N)} (e : Nonempty (G.induce (↑S : Set (Fin N)) ≃g Frep)) : S.card = n := by
  obtain ⟨f⟩ := e
  have hc := f.card_eq
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

/-- The class-membership condition for the canonical increasing embedding of `S` agrees with
the subset-induced-iso condition. -/
private lemma induce_iso_iff_comap_eq' {N n : ℕ} (G : SimpleGraph (Fin N))
    {F2 : Flag ∅ₜ (Fin n)} {Frep : SimpleGraph (Fin n)} (hFrep : graphFlag Frep = F2)
    (S : Finset (Fin N)) (hS : S.card = n) :
    Nonempty (G.induce (↑S : Set (Fin N)) ≃g Frep)
      ↔ graphFlag (G.comap ⇑(S.orderEmbOfFin hS).toEmbedding) = F2 := by
  obtain ⟨e⟩ := comap_iso_induce_range G (S.orderEmbOfFin hS).toEmbedding
  rw [RelEmbedding.coe_toEmbedding, Finset.range_orderEmbOfFin] at e
  rw [← hFrep, graphFlag_eq_iff]
  constructor
  · rintro ⟨f⟩; exact ⟨e.trans f⟩
  · rintro ⟨g⟩; exact ⟨e.symm.trans g⟩

/-- An embedding's image `Finset` (via `Finset.image`) is the subset it's the canonical
increasing enumeration of. -/
private lemma image_orderEmbOfFin {N n : ℕ} (S : Finset (Fin N)) (hS : S.card = n) :
    Finset.image (⇑(S.orderEmbOfFin hS).toEmbedding) Finset.univ = S := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact Finset.range_orderEmbOfFin S hS

/-- **The injective-tuple count**: the number of injective tuples realising the flag class
`F2` is `n!` times the number of vertex subsets realising it. -/
private lemma injSet_card_eq {N n : ℕ} (G : SimpleGraph (Fin N)) (F2 : Flag ∅ₜ (Fin n)) :
    (Finset.univ.filter
        (fun t : Fin n → Fin N => Function.Injective t ∧ graphFlag (G.comap t) = F2)).card
      = n.factorial *
        (Finset.univ.filter
          (fun S : Finset (Fin N) => Nonempty (G.induce (↑S : Set (Fin N)) ≃g F2.out.graph))).card := by
  classical
  set Frep : SimpleGraph (Fin n) := F2.out.graph with hFrepdef
  have hFrep : graphFlag Frep = F2 := graphFlag_out F2
  set injSet : Finset (Fin n → Fin N) :=
      Finset.univ.filter (fun t => Function.Injective t ∧ graphFlag (G.comap t) = F2)
    with hinjSetdef
  have hcardsum : injSet.card
      = ∑ S : Finset (Fin N), (injSet.filter (fun t => Finset.image t Finset.univ = S)).card :=
    Finset.card_eq_sum_card_fiberwise (fun t _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [hcardsum]
  have hterm : ∀ S : Finset (Fin N),
      (injSet.filter (fun t => Finset.image t Finset.univ = S)).card
        = if Nonempty (G.induce (↑S : Set (Fin N)) ≃g Frep) then n.factorial else 0 := by
    intro S
    by_cases hSc : S.card = n
    · have hrefimg := image_orderEmbOfFin S hSc
      by_cases hiso : Nonempty (G.induce (↑S : Set (Fin N)) ≃g Frep)
      · rw [if_pos hiso]
        have hrefclass : graphFlag (G.comap ⇑(S.orderEmbOfFin hSc).toEmbedding) = F2 :=
          (induce_iso_iff_comap_eq' G hFrep S hSc).mp hiso
        have heq : injSet.filter (fun t => Finset.image t Finset.univ = S)
            = Finset.univ.filter (fun t : Fin n → Fin N => Finset.image t Finset.univ = S) := by
          ext t
          simp only [hinjSetdef, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨_, himg⟩; exact himg
          · intro himg
            refine ⟨⟨injective_of_mem_fiber hSc himg, ?_⟩, himg⟩
            rw [graphFlag_comap_eq_of_image_eq G hSc himg hrefimg]
            exact hrefclass
        rw [heq, card_fiber_eq_factorial S hSc]
      · rw [if_neg hiso]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro t ht himg
        apply hiso
        simp only [hinjSetdef, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        have hclasseq : graphFlag (G.comap t)
            = graphFlag (G.comap ⇑(S.orderEmbOfFin hSc).toEmbedding) :=
          graphFlag_comap_eq_of_image_eq G hSc himg hrefimg
        exact (induce_iso_iff_comap_eq' G hFrep S hSc).mpr (hclasseq ▸ ht.2)
    · rw [if_neg (fun hiso => hSc (card_eq_of_induce_iso' hiso))]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro t ht himg
      apply hSc
      rw [hinjSetdef, Finset.mem_filter] at ht
      rw [← himg, Finset.card_image_of_injective _ ht.2.1, Finset.card_univ, Fintype.card_fin]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## Non-injective tuples: the union bound -/

/-- Fixing a coordinate collision `t i = t j` (`i ≠ j`) leaves at most `N^(n-1)` tuples: the
value at `j` is forced by the value at `i`, so the whole tuple is determined by its
restriction to `Fin n \ {j}`. -/
private lemma card_collision_le (n N : ℕ) {i j : Fin n} (hij : i ≠ j) :
    (Finset.univ.filter (fun t : Fin n → Fin N => t i = t j)).card ≤ N ^ (n - 1) := by
  classical
  have hcardsub : Fintype.card {k : Fin n // k ≠ j} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hle : (Finset.univ.filter (fun t : Fin n → Fin N => t i = t j)).card
      ≤ (Finset.univ : Finset ({k : Fin n // k ≠ j} → Fin N)).card := by
    apply Finset.card_le_card_of_injOn (fun t k => t k.1)
      (fun t _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    intro t1 ht1 t2 ht2 heq
    have hmem1 : t1 i = t1 j := (Finset.mem_filter.mp ht1).2
    have hmem2 : t2 i = t2 j := (Finset.mem_filter.mp ht2).2
    funext k
    by_cases hk : k = j
    · subst hk
      rw [← hmem1, ← hmem2]
      exact congrFun heq ⟨i, hij⟩
    · exact congrFun heq ⟨k, hk⟩
  rwa [Finset.card_univ, Fintype.card_fun, hcardsub, Fintype.card_fin] at hle

/-- **The union bound**: the non-injective tuples have relative mass at most `C(n,2)/N`. -/
private lemma card_nonInjective_le {n N : ℕ} (hN : N ≠ 0) :
    ((Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card : ℝ)
      / (N : ℝ) ^ n ≤ (n.choose 2 : ℝ) / N := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hempty : (Finset.univ.filter
        (fun t : Fin 0 → Fin N => ¬ Function.Injective t)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t _ hninj
      exact hninj (fun a => a.elim0)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity
  · have hsub : (Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t))
        ⊆ (belowDiagPairs n).biUnion
          (fun p => Finset.univ.filter (fun t : Fin n → Fin N => t p.1 = t p.2)) := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have hninj : ¬ Function.Injective t := ht.2
      rw [Function.not_injective_iff] at hninj
      obtain ⟨a, b, hab, hne⟩ := hninj
      rw [Finset.mem_biUnion]
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨(a, b), mem_belowDiagPairs.mpr hlt, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
      · exact ⟨(b, a), mem_belowDiagPairs.mpr hlt,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩⟩
    have hcard_le : (Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card
        ≤ (n.choose 2) * N ^ (n - 1) := by
      calc (Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card
          ≤ ((belowDiagPairs n).biUnion
              (fun p => Finset.univ.filter (fun t : Fin n → Fin N => t p.1 = t p.2))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ p ∈ belowDiagPairs n,
              (Finset.univ.filter (fun t : Fin n → Fin N => t p.1 = t p.2)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ belowDiagPairs n, N ^ (n - 1) :=
            Finset.sum_le_sum (fun p hp => card_collision_le n N (ne_of_lt (mem_belowDiagPairs.mp hp)))
        _ = (n.choose 2) * N ^ (n - 1) := by
            rw [Finset.sum_const, card_belowDiagPairs, smul_eq_mul]
    have hNR : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [div_le_div_iff₀ (by positivity) hNR]
    have hpow : (N:ℝ) ^ n = (N:ℝ) ^ (n - 1) * N := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    have : ((Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card : ℝ)
        ≤ ((n.choose 2) * N ^ (n - 1) : ℕ) := by exact_mod_cast hcard_le
    calc ((Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card : ℝ) * N
        ≤ ((n.choose 2 : ℕ) * N ^ (n - 1) : ℕ) * N := by
          apply mul_le_mul_of_nonneg_right this (le_of_lt hNR)
      _ = (n.choose 2 : ℝ) * ((N:ℝ) ^ (n - 1) * N) := by push_cast; ring

/-! ## The counting lemma -/

/-- **The step-graphon counting lemma**: the graphon profile of `stepGraphon G` at a test
flag `F` of size `n` agrees with the finite flag density of `F` in `G` up to `n(n−1)/N`.

Proof route: by `inducedWeight_stepGraphon` the profile is the probability that a uniform
cell tuple `c : Fin n → Fin N` (each coordinate an independent uniform cell, by
`volume_cellIdx_preimage`) realises a member of the class of `F`; split on injectivity of
the tuple.  Injective tuples with image `S` realise a class member iff `G.induce ↑S` is a
copy (`comap_iso_induce_range` + `graphFlag_eq_iff`), and each such `S` carries exactly `n!`
tuples, so the injective mass is `flagDensity₁ F.2 (graphFlag G) · (N)ₙ/Nⁿ`
(`flagDensity₁_graphFlag` supplies the subset count over `C(N, n)`).  Non-injective tuples
have mass `≤ C(n,2)/N` (union bound over coordinate collisions, each of probability `1/N`);
the falling-factorial defect is `≤ C(n,2)/N` by
`one_sub_choose_div_le_descFactorial_div_pow`; and `n(n−1) = 2·C(n,2)`. -/
theorem graphonProfileFun_stepGraphon_sub_le {N : ℕ} (hN : N ≠ 0)
    (G : SimpleGraph (Fin N)) (F : FinFlag ∅ₜ) :
    |graphonProfileFun (stepGraphon hN G) F - (flagDensity₁ F.2 (graphFlag G) : ℝ)|
      ≤ ((F.1 * (F.1 - 1) : ℕ) : ℝ) / N := by
  classical
  obtain ⟨n, F2⟩ := F
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNRpow : (0 : ℝ) < (N : ℝ) ^ n := by positivity
  have hFrep : graphFlag (F2.out.graph) = F2 := graphFlag_out F2
  have hdensity_nonneg : 0 ≤ (flagDensity₁ F2 (graphFlag G) : ℝ) := by
    exact_mod_cast flagListDensity₁_ge_zero F2 (graphFlag G)
  have hdensity_le_one : (flagDensity₁ F2 (graphFlag G) : ℝ) ≤ 1 := by
    exact_mod_cast flagListDensity₁_le_one F2 (graphFlag G)
  show |graphonProfileFun (stepGraphon hN G) ⟨n, F2⟩ - (flagDensity₁ F2 (graphFlag G) : ℝ)| ≤ _
  rw [profile_eq_tupleCount hN G F2]
  set injSet : Finset (Fin n → Fin N) :=
      Finset.univ.filter (fun t => Function.Injective t ∧ graphFlag (G.comap t) = F2)
    with hinjdef
  set nonInjClassSet : Finset (Fin n → Fin N) :=
      Finset.univ.filter (fun t => ¬ Function.Injective t ∧ graphFlag (G.comap t) = F2)
    with hnonInjClassdef
  set subsetSet : Finset (Finset (Fin N)) :=
      Finset.univ.filter (fun S => Nonempty (G.induce (↑S : Set (Fin N)) ≃g F2.out.graph))
    with hsubsetdef
  have hsplit : (Finset.univ.filter (fun t : Fin n → Fin N => graphFlag (G.comap t) = F2)).card
      = injSet.card + nonInjClassSet.card := by
    have heq1 : (Finset.univ.filter (fun t : Fin n → Fin N => graphFlag (G.comap t) = F2)).filter
        Function.Injective = injSet := by
      rw [hinjdef]; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    have heq2 : (Finset.univ.filter (fun t : Fin n → Fin N => graphFlag (G.comap t) = F2)).filter
        (fun t => ¬ Function.Injective t) = nonInjClassSet := by
      rw [hnonInjClassdef]; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [← heq1, ← heq2]
    exact (Finset.card_filter_add_card_filter_not Function.Injective).symm
  have hnonInj_le : nonInjClassSet.card
      ≤ (Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card := by
    apply Finset.card_le_card
    rw [hnonInjClassdef]
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht.1
  have hinjcard : injSet.card = n.factorial * subsetSet.card := by
    rw [hinjdef, hsubsetdef]; exact injSet_card_eq G F2
  have hchoose_eq : (subsetSet.card : ℝ)
      = (flagDensity₁ F2 (graphFlag G) : ℝ) * (N.choose n : ℝ) := by
    rcases le_or_gt n N with hle | hlt
    · have hchpos : 0 < N.choose n := Nat.choose_pos hle
      have hchne : (N.choose n : ℚ) ≠ 0 := by exact_mod_cast hchpos.ne'
      have hden := flagDensity₁_graphFlag F2.out.graph G
      rw [hFrep] at hden
      rw [eq_div_iff hchne] at hden
      rw [hsubsetdef]
      exact_mod_cast hden.symm
    · have hch0 : N.choose n = 0 := Nat.choose_eq_zero_of_lt hlt
      have hsc0 : subsetSet.card = 0 := by
        rw [hsubsetdef]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro S _ hiso
        have hScard := card_eq_of_induce_iso' hiso
        have hSleN : S.card ≤ N := by
          have hc := Finset.card_le_card (Finset.subset_univ S)
          rwa [Finset.card_univ, Fintype.card_fin] at hc
        omega
      rw [hsc0, hch0]; push_cast; ring
  have hdescFact_eq : (N.descFactorial n : ℝ) = (n.factorial : ℝ) * (N.choose n : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose N n
  have hinj_eq : (injSet.card : ℝ)
      = (flagDensity₁ F2 (graphFlag G) : ℝ) * (N.descFactorial n : ℝ) := by
    rw [hinjcard]
    push_cast
    rw [hchoose_eq, hdescFact_eq]
    ring
  set x : ℝ := (N.descFactorial n : ℝ) / (N : ℝ) ^ n with hxdef
  have hx_le_one : x ≤ 1 := descFactorial_div_pow_le_one N n
  have hx_ge : 1 - (n.choose 2 : ℝ) / N ≤ x := one_sub_choose_div_le_descFactorial_div_pow N n hN
  have hnonInjTotal_le :
      ((Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card : ℝ)
        / (N : ℝ) ^ n ≤ (n.choose 2 : ℝ) / N := card_nonInjective_le hN
  have hy_nonneg : (0 : ℝ) ≤ (nonInjClassSet.card : ℝ) / (N : ℝ) ^ n := by positivity
  have hnonInjClass_le : (nonInjClassSet.card : ℝ) / (N : ℝ) ^ n ≤ (n.choose 2 : ℝ) / N := by
    have h1 : (nonInjClassSet.card : ℝ)
        ≤ ((Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card : ℝ) := by
      exact_mod_cast hnonInj_le
    calc (nonInjClassSet.card : ℝ) / (N : ℝ) ^ n
        ≤ ((Finset.univ.filter (fun t : Fin n → Fin N => ¬ Function.Injective t)).card : ℝ)
            / (N : ℝ) ^ n :=
          div_le_div_of_nonneg_right h1 (le_of_lt hNRpow)
      _ ≤ (n.choose 2 : ℝ) / N := hnonInjTotal_le
  have hchoose2_nonneg : (0 : ℝ) ≤ (n.choose 2 : ℝ) := Nat.cast_nonneg _
  have htotal_eq : ((injSet.card + nonInjClassSet.card : ℕ) : ℝ) / (N : ℝ) ^ n
      = (flagDensity₁ F2 (graphFlag G) : ℝ) * x + (nonInjClassSet.card : ℝ) / (N : ℝ) ^ n := by
    push_cast
    rw [add_div, hxdef, hinj_eq]
    ring
  rw [hsplit, htotal_eq]
  have hbound_eq : ((n * (n - 1) : ℕ) : ℝ) / N = 2 * ((n.choose 2 : ℝ) / N) := by
    have hnn := two_mul_choose_two n
    have hcast : ((n * (n - 1) : ℕ) : ℝ) = 2 * (n.choose 2 : ℝ) := by exact_mod_cast hnn.symm
    rw [hcast]; ring
  rw [hbound_eq, abs_le]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hdensity_le_one) (sub_nonneg.mpr hx_le_one),
      hnonInjClass_le, hy_nonneg, hx_ge, hchoose2_nonneg, hNR]
  · nlinarith [mul_nonneg hdensity_nonneg (sub_nonneg.mpr hx_le_one),
      hnonInjClass_le, hy_nonneg, hchoose2_nonneg, hNR]

/-- The value of `graphonHomPoint W` at a flag `F` is exactly `graphonProfileFun W F`. -/
private lemma graphonHomPoint_val_apply (W : Graphon) (F : FinFlag ∅ₜ) :
    (graphonHomPoint W).val F = graphonProfileFun W F := by
  show (posHomPoint (graphonHom W)).val F = graphonProfileFun W F
  rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, graphonHom_coe]

/-- The value of `posHomPoint φ` at a flag `F` is exactly `φ.coe F`. -/
private lemma posHomPoint_val_eq_coe (φ : PositiveHom ∅ₜ) (F : FinFlag ∅ₜ) :
    (posHomPoint φ).val F = φ.coe F := by
  rw [posHomPoint_val_apply, ← PositiveHom.coe_flag]

/-! ## Density of the graphon-hom range -/

/-- Along a flag sequence converging to `φ`, the step-graphon hom points converge to the
point of `φ` (in `X_∅`, i.e. pointwise on profiles: combine the counting lemma with
`ConvergesTo`'s per-flag density convergence and `Increases`' size growth, plus
`graphFlag_out` to identify `graphFlag ((s n).2.out.graph) = (s n).2`). -/
theorem tendsto_graphonHomPoint_stepGraphon {s : FlagSeq ∅ₜ} {φ : PositiveHom ∅ₜ}
    (hs : ConvergesTo s φ.coe) (hpos : ∀ n, (s n).1 ≠ 0) :
    Tendsto (fun n => graphonHomPoint (stepGraphon (hpos n) ((s n).2.out.graph)))
      atTop (𝓝 (posHomPoint φ)) := by
  rw [tendsto_subtype_rng, tendsto_subtype_rng, tendsto_pi_nhds]
  intro F
  show Tendsto (fun n => (graphonHomPoint (stepGraphon (hpos n) ((s n).2.out.graph))).val F)
    atTop (𝓝 ((posHomPoint φ).val F))
  simp only [graphonHomPoint_val_apply, posHomPoint_val_eq_coe]
  obtain ⟨hinc, hlim⟩ := hs
  have hlimF : Tendsto (fun n => flagDensitySeq s n F) atTop (𝓝 (φ.coe F)) :=
    tendsto_pi_nhds.mp hlim F
  have hgraphFlag : ∀ n, graphFlag ((s n).2.out.graph) = (s n).2 := fun n => graphFlag_out (s n).2
  have hdensity_eq : ∀ n, flagDensitySeq s n F
      = (flagDensity₁ F.2 (graphFlag ((s n).2.out.graph)) : ℝ) := by
    intro n; rw [hgraphFlag n]; rfl
  have hbound : ∀ n, |graphonProfileFun (stepGraphon (hpos n) ((s n).2.out.graph)) F
      - flagDensitySeq s n F| ≤ ((F.1 * (F.1 - 1) : ℕ) : ℝ) / (s n).1 := by
    intro n
    rw [hdensity_eq n]
    exact graphonProfileFun_stepGraphon_sub_le (hpos n) ((s n).2.out.graph) F
  have hsize_tendsto : Tendsto (fun n => ((s n).1 : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => (s n).1) atTop atTop :=
      tendsto_atTop_mono (fun n => hinc.id_le n) tendsto_id
    exact tendsto_natCast_atTop_atTop.comp h1
  have herr_tendsto : Tendsto
      (fun n => ((F.1 * (F.1 - 1) : ℕ) : ℝ) / ((s n).1 : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => ((s n).1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsize_tendsto
    have := hinv.const_mul (((F.1 * (F.1 - 1) : ℕ) : ℝ))
    simpa [div_eq_mul_inv] using this
  have hsqueeze : Tendsto
      (fun n => |graphonProfileFun (stepGraphon (hpos n) ((s n).2.out.graph)) F
        - flagDensitySeq s n F|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound herr_tendsto
  have hdiff_tendsto : Tendsto
      (fun n => graphonProfileFun (stepGraphon (hpos n) ((s n).2.out.graph)) F
        - flagDensitySeq s n F) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hsqueeze
  have hfinal := hdiff_tendsto.add hlimF
  simpa using hfinal

/-- **Density of the graphon-hom range in `X_∅`**: every unlabelled limit functional is a
limit of graphon points.  (From `positiveHom_as_flagSeq_limit`; the finitely many
zero-size terms of the sequence, if any, are re-indexed away using `Increases`.) -/
theorem exists_graphonHomPoint_seq_tendsto (φ : PositiveHom ∅ₜ) :
    ∃ V : ℕ → Graphon,
      Tendsto (fun n => graphonHomPoint (V n)) atTop (𝓝 (posHomPoint φ)) := by
  obtain ⟨s, hs⟩ := positiveHom_as_flagSeq_limit φ
  set s' : FlagSeq ∅ₜ := fun n => s (n + 1) with hs'def
  have hinc' : Increases s' := by
    intro a b hab
    show (s (a + 1)).1 < (s (b + 1)).1
    exact hs.1 (by omega)
  have hlim' : Tendsto (flagDensitySeq s') atTop (𝓝 (φ.coe : FinFlag ∅ₜ → ℝ)) := by
    have heq : flagDensitySeq s' = fun n => flagDensitySeq s (n + 1) := rfl
    rw [heq]
    exact (tendsto_add_atTop_iff_nat 1).mpr hs.2
  have hsConv : ConvergesTo s' φ.coe := ⟨hinc', hlim'⟩
  have hpos' : ∀ n, (s' n).1 ≠ 0 := by
    intro n
    show (s (n + 1)).1 ≠ 0
    have hle : n + 1 ≤ (s (n + 1)).1 := hs.1.id_le (n + 1)
    omega
  exact ⟨fun n => stepGraphon (hpos' n) ((s' n).2.out.graph),
    tendsto_graphonHomPoint_stepGraphon hsConv hpos'⟩

end FlagAlgebras.MetaTheory
