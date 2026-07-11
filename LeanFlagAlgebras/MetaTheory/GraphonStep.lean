import LeanFlagAlgebras.MetaTheory.GraphonHom

/-! # Step graphons

The finite-to-graphon functor: a graph `G` on `Fin N` becomes the **step graphon**
`stepGraphon hN G` — the `{0,1}`-valued kernel that is `1` on the cell pair `(i, j)`
exactly when `G.Adj i j`, for the equal `N`-cell interval partition of `I` given by
`cellIdx`.

* `cellIdx N hN : I → Fin N` — the cell map `x ↦ ⌊N·x⌋` (clamped at the single endpoint
  `x = 1`), measurable, with every fibre of volume exactly `1/N`.
* `stepGraphon hN G : Graphon` — the indicator kernel.
* `inducedWeight_stepGraphon` — the **pointwise indicator identity**: the induced weight of
  a test graph `H` on `Fin n` at samples `c` is the indicator of the *literal* graph
  equality `G.comap (cellIdx N hN ∘ c) = H` (every factor of the weight product is `0` or
  `1`, and the product is `1` exactly when the cell tuple realises `H`'s adjacency pattern
  on the nose — note: literal equality on the common vertex set `Fin n`, NOT flag-class
  equality).  This identity underlies the counting lemma relating hom-density in `G` to
  induced weight in `stepGraphon hN G`.

Everything is Tier-1; no certificate material.
-/

open MeasureTheory unitInterval Finset
open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-! ## The cell map -/

/-- The equal-`N`-cell map: `x ↦ ⌊N·x⌋`, clamped to `N − 1` at the endpoint `x = 1`. -/
noncomputable def cellIdx (N : ℕ) (hN : N ≠ 0) (x : I) : Fin N :=
  ⟨min (N - 1) ⌊(N : ℝ) * (x : ℝ)⌋₊, by
    have : N - 1 < N := Nat.sub_lt (Nat.pos_of_ne_zero hN) one_pos
    omega⟩

/-- The cell boundary point `m/N : I`, for `m ≤ N`. -/
private noncomputable def cellPoint {N : ℕ} (hN : N ≠ 0) (m : ℕ) (hm : m ≤ N) : I :=
  ⟨(m : ℝ) / (N : ℝ), by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hm⟩

private lemma cellPoint_coe {N : ℕ} (hN : N ≠ 0) (m : ℕ) (hm : m ≤ N) :
    (cellPoint hN m hm : ℝ) = (m : ℝ) / (N : ℝ) := rfl

private lemma cellIdx_eq_iff {N : ℕ} (hN : N ≠ 0) (x : I) (k : Fin N) :
    cellIdx N hN x = k ↔ min (N - 1) ⌊(N : ℝ) * (x : ℝ)⌋₊ = (k : ℕ) := by
  simp [cellIdx, Fin.ext_iff]

/-- The fibre of a non-last cell is the half-open interval `[k/N, (k+1)/N)`. -/
private lemma cellIdx_preimage_of_lt {N : ℕ} (hN : N ≠ 0) (k : Fin N) (hk : (k : ℕ) + 1 < N) :
    cellIdx N hN ⁻¹' {k}
      = Set.Ico (cellPoint hN k (by omega)) (cellPoint hN ((k : ℕ) + 1) (by omega)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  ext x
  have hxnn : (0 : ℝ) ≤ (N : ℝ) * (x : ℝ) := mul_nonneg (Nat.cast_nonneg N) (unitInterval.nonneg x)
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico, cellIdx_eq_iff,
    ← Subtype.coe_le_coe, ← Subtype.coe_lt_coe, cellPoint_coe]
  have hmin : min (N - 1) ⌊(N : ℝ) * (x : ℝ)⌋₊ = (k : ℕ) ↔ ⌊(N : ℝ) * (x : ℝ)⌋₊ = (k : ℕ) := by
    omega
  rw [hmin, Nat.floor_eq_iff hxnn, div_le_iff₀' hNpos, lt_div_iff₀' hNpos]
  push_cast
  tauto

/-- The fibre of the last cell is the closed interval `[(N−1)/N, 1]` (the clamp). -/
private lemma cellIdx_preimage_of_eq {N : ℕ} (hN : N ≠ 0) (k : Fin N) (hk : (k : ℕ) + 1 = N) :
    cellIdx N hN ⁻¹' {k} = Set.Ici (cellPoint hN k (by omega)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  ext x
  have hxnn : (0 : ℝ) ≤ (N : ℝ) * (x : ℝ) := mul_nonneg (Nat.cast_nonneg N) (unitInterval.nonneg x)
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ici, cellIdx_eq_iff,
    ← Subtype.coe_le_coe, cellPoint_coe]
  have hmin : min (N - 1) ⌊(N : ℝ) * (x : ℝ)⌋₊ = (k : ℕ) ↔ (k : ℕ) ≤ ⌊(N : ℝ) * (x : ℝ)⌋₊ := by
    omega
  rw [hmin, Nat.le_floor_iff hxnn, div_le_iff₀' hNpos]

theorem measurable_cellIdx (N : ℕ) (hN : N ≠ 0) : Measurable (cellIdx N hN) := by
  apply measurable_to_countable'
  intro k
  have hkN : (k : ℕ) < N := k.isLt
  by_cases hk : (k : ℕ) + 1 < N
  · rw [cellIdx_preimage_of_lt hN k hk]
    exact measurableSet_Ico
  · have hk' : (k : ℕ) + 1 = N := by omega
    rw [cellIdx_preimage_of_eq hN k hk']
    exact measurableSet_Ici

/-- Every cell has volume exactly `1/N` (the fibres are the intervals
`[k/N, (k+1)/N)`, with the last one closed — a null boundary adjustment on the atomless
`unitInterval`). -/
theorem volume_cellIdx_preimage (N : ℕ) (hN : N ≠ 0) (k : Fin N) :
    volume (cellIdx N hN ⁻¹' {k}) = (N : ENNReal)⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hkN : (k : ℕ) < N := k.isLt
  by_cases hk : (k : ℕ) + 1 < N
  · rw [cellIdx_preimage_of_lt hN k hk, unitInterval.volume_Ico]
    simp only [cellPoint_coe]
    push_cast
    rw [show ((k : ℝ) + 1) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) by ring,
      one_div, ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  · have hk' : (k : ℕ) + 1 = N := by omega
    rw [cellIdx_preimage_of_eq hN k hk', unitInterval.volume_Ici, cellPoint_coe]
    have hk'' : (k : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hk'
    have heq : (1 : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
      rw [eq_div_iff hNpos.ne', sub_mul, div_mul_cancel₀ _ hNpos.ne', one_mul]
      linarith [hk'']
    rw [heq, one_div, ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]

/-! ## The step graphon -/

/-- **The step graphon** of a graph on `Fin N`: the indicator kernel of the adjacency of the
cells. -/
noncomputable def stepGraphon {N : ℕ} (hN : N ≠ 0) (G : SimpleGraph (Fin N)) : Graphon where
  W x y := if G.Adj (cellIdx N hN x) (cellIdx N hN y) then 1 else 0
  measurable := by
    -- indicator of a measurable set: the adjacency preimage under the (measurable) pair of
    -- cell maps; `G.Adj` on `Fin N × Fin N` is a decidable predicate on a finite discrete
    -- space.
    haveI : MeasurableSingletonClass (Fin N) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
    have hset : MeasurableSet {q : Fin N × Fin N | G.Adj q.1 q.2} :=
      Set.Finite.measurableSet (Set.toFinite _)
    have hpair : Measurable (fun p : I × I => (cellIdx N hN p.1, cellIdx N hN p.2)) :=
      ((measurable_cellIdx N hN).comp measurable_fst).prodMk
        ((measurable_cellIdx N hN).comp measurable_snd)
    have hcond : MeasurableSet {p : I × I | G.Adj (cellIdx N hN p.1) (cellIdx N hN p.2)} :=
      hpair hset
    exact Measurable.ite hcond measurable_const measurable_const
  symm := fun x y => by
    by_cases h : G.Adj (cellIdx N hN x) (cellIdx N hN y)
    · rw [if_pos h, if_pos (G.symm h)]
    · rw [if_neg h, if_neg (fun h' => h (G.symm h'))]
  nonneg := fun x y => by split_ifs <;> norm_num
  le_one := fun x y => by split_ifs <;> norm_num

@[simp]
theorem stepGraphon_W_apply {N : ℕ} (hN : N ≠ 0) (G : SimpleGraph (Fin N)) (x y : I) :
    (stepGraphon hN G).W x y
      = if G.Adj (cellIdx N hN x) (cellIdx N hN y) then 1 else 0 := rfl

/-! ## The pointwise indicator identity -/

/-- The product of `{0,1}`-valued `if`-indicators over a finset is the indicator of the
conjunction. -/
private lemma prod_ite_eq_one_iff {ι : Type*} (s : Finset ι) (q : ι → Prop) [DecidablePred q] :
    ∏ p ∈ s, (if q p then (1 : ℝ) else 0) = if ∀ p ∈ s, q p then 1 else 0 := by
  by_cases h : ∀ p ∈ s, q p
  · rw [if_pos h]
    exact Finset.prod_eq_one fun p hp => if_pos (h p hp)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p, hp, hpq⟩ := h
    exact Finset.prod_eq_zero hp (if_neg hpq)

/-- Each `adjWeight` factor of the step graphon's induced weight is `1` if the tested
adjacency `b` matches the cells' `G`-adjacency, and `0` otherwise. -/
private lemma adjWeight_stepGraphon_eq {N : ℕ} (hN : N ≠ 0) (G : SimpleGraph (Fin N)) (b : Prop)
    (u v : I) :
    adjWeight (stepGraphon hN G) b u v
      = if (b ↔ G.Adj (cellIdx N hN u) (cellIdx N hN v)) then 1 else 0 := by
  unfold adjWeight
  by_cases hb : b <;> by_cases hadj : G.Adj (cellIdx N hN u) (cellIdx N hN v) <;>
    simp [hb, hadj, stepGraphon_W_apply]

/-- **The pointwise indicator identity**: the induced weight of `H` in the step graphon of
`G` at samples `c` is `1` exactly when the cell tuple realises `H` — literally,
`G.comap (cellIdx N hN ∘ c) = H` as graphs on `Fin n` (`SimpleGraph.comap` needs no
injectivity; colliding cells simply produce non-edges).

Proof route: each `adjWeight` factor is `1` if `H`'s adjacency at that pair matches the
comap's and `0` otherwise (four `if` cases); the product over `belowDiagPairs n` is `1` iff
all pairs match, which by `SimpleGraph.ext` (+ symmetry and irreflexivity for the off-order
and diagonal pairs) is the literal equality. -/
theorem inducedWeight_stepGraphon {N n : ℕ} (hN : N ≠ 0) (G : SimpleGraph (Fin N))
    (H : SimpleGraph (Fin n)) (c : Fin n → I) :
    inducedWeight (stepGraphon hN G) H c
      = if G.comap (cellIdx N hN ∘ c) = H then 1 else 0 := by
  unfold inducedWeight
  simp_rw [adjWeight_stepGraphon_eq]
  rw [prod_ite_eq_one_iff]
  congr 1
  apply propext
  constructor
  · intro hall
    apply SimpleGraph.ext
    funext a b
    by_cases hab : a = b
    · subst hab
      apply propext
      simp only [Function.comp_apply, SimpleGraph.comap_adj]
      exact ⟨fun h => absurd h G.irrefl, fun h => absurd h H.irrefl⟩
    · rcases lt_or_gt_of_ne hab with h1 | h1
      · have h := hall (a, b) (mem_belowDiagPairs.mpr h1)
        -- h : H.Adj a b ↔ G.Adj (cellIdx N hN (c a)) (cellIdx N hN (c b))
        apply propext
        simp only [Function.comp_apply, SimpleGraph.comap_adj]
        exact h.symm
      · have h := hall (b, a) (mem_belowDiagPairs.mpr h1)
        -- h : H.Adj b a ↔ G.Adj (cellIdx N hN (c b)) (cellIdx N hN (c a))
        apply propext
        simp only [Function.comp_apply, SimpleGraph.comap_adj]
        rw [SimpleGraph.adj_comm G, SimpleGraph.adj_comm H]
        exact h.symm
  · intro heq p hp
    have hp' : p.1 < p.2 := mem_belowDiagPairs.mp hp
    rw [← heq]
    simp [SimpleGraph.comap_adj]

end FlagAlgebras.MetaTheory
