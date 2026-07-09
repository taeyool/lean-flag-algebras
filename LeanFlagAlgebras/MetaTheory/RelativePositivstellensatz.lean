import LeanFlagAlgebras.MetaTheory.CertificateCones

/-! # The relative Positivstellensatz (paper §11.4, `thm:relative-positivstellensatz`)

Every density inequality valid on an equality slice
`Y = {φ₀ ∈ Q₀ : φ₀ (gs j) = 0 for all j}` is provable, up to an arbitrarily small shift
`ε·1₀` of the constant term, by an inequality valid on the WHOLE class augmented by a single
penalty `M·∑ g_{j_i}²` over finitely many constraints:

* `relative_positivstellensatz` — the two conditions are equivalent
  (compactness of `Q₀` + a finite-intersection argument on the sublevel sets
  `K_n = {φ₀ : φ₀(g_{j_i})² ≤ 1/(n+1)}`);
* `relative_positivstellensatz_closure` — the cone form: the `Y`-non-negative elements are
  exactly the `‖·‖_{Q₀}`-closure of `C_{Q₀} + span{g_j²}`.

Both hold for `Y = ∅` as well (then every `f` qualifies).  The slice `φ₀(h) = c` enters with
`g := h - c•1₀`.
-/

open Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ}

/-! ## The penalty form -/

/-- Evaluation of the shifted and penalised element through a positive homomorphism:
`φ₀ (f + ε•1 + M•∑ hᵢ²) = φ₀ f + ε + M·∑ (φ₀ hᵢ)²`. -/
private lemma eval_shift_penalty (φ₀ : PositiveHom ∅ₜ) (f : FlagAlgebra ∅ₜ) (ε M : ℝ)
    {N : ℕ} (hs : Fin N → FlagAlgebra ∅ₜ) :
    φ₀ (f + ε • (1 : FlagAlgebra ∅ₜ) + M • ∑ i : Fin N, hs i * hs i)
      = φ₀ f + ε + M * ∑ i : Fin N, φ₀ (hs i) * φ₀ (hs i) := by
  simp only [PositiveHom.map_add, PositiveHom.map_smul, PositiveHom.map_sum,
    PositiveHom.map_mul, PositiveHom.map_one, mul_one]

/-- The sublevel set `K_n ⊆ Q₀`: constrained limits whose first `n+1` constraint values
have squares at most `1/(n+1)`. -/
private def Kset (forb0 : FinFlag ∅ₜ → Prop) (g : ℕ → FlagAlgebra ∅ₜ) (n : ℕ) :
    Set (PositiveHomSpace ∅ₜ) :=
  {χ | χ ∈ Qσ forb0 ∧
    ∀ i ≤ n, ((PositiveHomSpace.toPosHom χ) (g i)) ^ 2 ≤ 1 / ((n : ℝ) + 1)}

private lemma mem_Kset {forb0 : FinFlag ∅ₜ → Prop} {g : ℕ → FlagAlgebra ∅ₜ} {n : ℕ}
    {χ : PositiveHomSpace ∅ₜ} :
    χ ∈ Kset forb0 g n ↔ χ ∈ Qσ forb0 ∧
      ∀ i ≤ n, ((PositiveHomSpace.toPosHom χ) (g i)) ^ 2 ≤ 1 / ((n : ℝ) + 1) :=
  Iff.rfl

/-- `K_n` is closed: an intersection of `Q₀` with finitely many sublevel sets of the
continuous squared evaluations. -/
private lemma Kset_isClosed (forb0 : FinFlag ∅ₜ → Prop) (g : ℕ → FlagAlgebra ∅ₜ) (n : ℕ) :
    IsClosed (Kset forb0 g n) := by
  have hrw : Kset forb0 g n = Qσ forb0 ∩ ⋂ i, ⋂ (_ : i ≤ n),
      {χ : PositiveHomSpace ∅ₜ |
        ((PositiveHomSpace.toPosHom χ) (g i)) ^ 2 ≤ 1 / ((n : ℝ) + 1)} := by
    ext χ
    simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hrw]
  exact (Qσ_isClosed forb0).inter <| isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_le ((continuous_eval (g i)).pow 2) continuous_const

/-- The sublevel sets decrease: `K_{n+1}` has more indices and a smaller bound. -/
private lemma Kset_succ_subset (forb0 : FinFlag ∅ₜ → Prop) (g : ℕ → FlagAlgebra ∅ₜ)
    (n : ℕ) : Kset forb0 g (n + 1) ⊆ Kset forb0 g n := by
  intro χ hχ
  obtain ⟨hQ, hb⟩ := mem_Kset.mp hχ
  refine mem_Kset.mpr ⟨hQ, fun i hi => (hb i (hi.trans n.le_succ)).trans ?_⟩
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  exact one_div_le_one_div_of_le h1 h2

/-- The set `C_n = K_n ∩ {φ₀ f ≤ -ε/2}` whose eventual emptiness produces the finite
subfamily of the penalty form. -/
private def Cset (forb0 : FinFlag ∅ₜ → Prop) (g : ℕ → FlagAlgebra ∅ₜ)
    (f : FlagAlgebra ∅ₜ) (ε : ℝ) (n : ℕ) : Set (PositiveHomSpace ∅ₜ) :=
  Kset forb0 g n ∩ {χ | (PositiveHomSpace.toPosHom χ) f ≤ -(ε / 2)}

private lemma mem_Cset {forb0 : FinFlag ∅ₜ → Prop} {g : ℕ → FlagAlgebra ∅ₜ}
    {f : FlagAlgebra ∅ₜ} {ε : ℝ} {n : ℕ} {χ : PositiveHomSpace ∅ₜ} :
    χ ∈ Cset forb0 g f ε n ↔ χ ∈ Kset forb0 g n ∧
      (PositiveHomSpace.toPosHom χ) f ≤ -(ε / 2) :=
  Iff.rfl

private lemma Cset_isClosed (forb0 : FinFlag ∅ₜ → Prop) (g : ℕ → FlagAlgebra ∅ₜ)
    (f : FlagAlgebra ∅ₜ) (ε : ℝ) (n : ℕ) : IsClosed (Cset forb0 g f ε n) :=
  (Kset_isClosed forb0 g n).inter (isClosed_le (continuous_eval f) continuous_const)

private lemma Cset_succ_subset (forb0 : FinFlag ∅ₜ → Prop) (g : ℕ → FlagAlgebra ∅ₜ)
    (f : FlagAlgebra ∅ₜ) (ε : ℝ) (n : ℕ) :
    Cset forb0 g f ε (n + 1) ⊆ Cset forb0 g f ε n := fun _ hχ =>
  mem_Cset.mpr ⟨Kset_succ_subset forb0 g n (mem_Cset.mp hχ).1, (mem_Cset.mp hχ).2⟩

/-- **Relative Positivstellensatz** (`thm:relative-positivstellensatz`): for a countable
family of equality constraints `gs` cutting the slice `Y ⊆ Q₀`, non-negativity of `f` on `Y`
is equivalent to, for every `ε > 0`, non-negativity of `f + ε•1 + M•∑ g_{j_i}²` on ALL of
`Q₀` for some finite subfamily and some penalty weight `M ≥ 0`. -/
theorem relative_positivstellensatz (forb0 : FinFlag ∅ₜ → Prop) {J : Type} [Countable J]
    (gs : J → FlagAlgebra ∅ₜ) (f : FlagAlgebra ∅ₜ) :
    (∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ forb0 → (∀ j, φ₀ (gs j) = 0) → 0 ≤ φ₀ f)
      ↔
    (∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (js : Fin N → J) (M : ℝ), 0 ≤ M ∧
      ∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ forb0 →
        0 ≤ φ₀ (f + ε • (1 : FlagAlgebra ∅ₜ)
              + M • ∑ i : Fin N, gs (js i) * gs (js i))) := by
  -- (⇐): evaluate at `φ₀ ∈ Y`; `φ₀ (g*g) = (φ₀ g)² = 0` by `PositiveHom.map_mul`, so
  --   `0 ≤ φ₀ f + ε` for every `ε > 0` (`PositiveHom.map_add`/`map_smul`/`map_one`/`map_sum`);
  --   conclude with `le_of_forall_pos_le_add`-style reasoning.
  -- (⇒): three preliminary case splits keep the main argument clean:
  --   * `Qσ forb0 = ∅` (no admissible base limit): pick `N := 0`, `M := 0`; the conclusion is
  --     vacuous.  (Test emptiness via `Classical`/`Set.eq_empty_or_nonempty`.)
  --   * `IsEmpty J` (no constraints, `Y = Q₀`): pick `N := 0`, `M := 0`; then
  --     `f + ε•1` evaluates to `φ₀ f + ε ≥ ε > 0` by the hypothesis (which now reads
  --     `0 ≤ φ₀ f` on `Q₀`, the `∀ j` being vacuous).
  --   * otherwise `Nonempty J`: obtain a surjective enumeration `e : ℕ → J`
  --     (`Countable` + `Nonempty` — e.g. `exists_surjective_nat` or via
  --     `Encodable`/`Denumerable` tooling; any surjection works).
  -- Main argument (fix `ε > 0`):
  --   * `K n := {χ ∈ Qσ forb0 | ∀ i ≤ n, ((PositiveHomSpace.toPosHom χ) (gs (e i)))^2 ≤ 1/(n+1)}`
  --     — closed (`continuous_eval`, finite intersections, `isClosed_le`) subsets of the
  --     compact `Qσ forb0` (`Qσ_isClosed` + ambient `CompactSpace (PositiveHomSpace ∅ₜ)`),
  --     decreasing (more indices + smaller bound), with
  --     `⋂ n, K n = {χ ∈ Qσ forb0 | ∀ j, eval (gs j) χ = 0}` (surjectivity of `e`; a value
  --     with square `≤ 1/(n+1)` for all large `n` is `0`).
  --   * `C n := K n ∩ {χ | (toPosHom χ) f ≤ -ε/2}` — compact, closed, decreasing, and
  --     `⋂ n, C n = ∅` (a common point lies in `Y` where `0 ≤ f`, contradicting `≤ -ε/2`).
  --     By the finite-intersection property (Mathlib:
  --     `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`, taken in
  --     contrapositive), some `C N = ∅`; i.e. `-ε/2 < (toPosHom χ) f` on `K N`.
  --   * `B := sup |eval f|` on the compact nonempty `Qσ forb0`
  --     (`IsCompact.exists_isMaxOn` applied to `|eval f|`, continuous).  Set
  --     `M := B * (N+1)` and `js i := e i` for `i : Fin (N+1)`.
  --   * For `φ₀` with `posHomPoint φ₀ ∈ Qσ forb0`: if `posHomPoint φ₀ ∈ K N`, then
  --     `φ₀ f + ε + M·(∑ nonneg) ≥ -ε/2 + ε ≥ ε/2 > 0`; otherwise some `i ≤ N` has
  --     `(φ₀ (gs (e i)))² > 1/(N+1)`, so the penalty sum exceeds `1/(N+1)` and
  --     `φ₀ f + ε + M/(N+1) ≥ -B + ε + B = ε > 0`.  Push the evaluation through
  --     `map_add`/`map_smul`/`map_sum`/`map_mul` and mind the `posHomPoint`/`toPosHom`
  --     roundtrips (`toPosHom_posHomPoint`, `posHomPoint_toPosHom`).
  constructor
  · intro hY ε hε
    rcases Set.eq_empty_or_nonempty (Qσ forb0) with hQ | hQne
    · -- no admissible base limit: the conclusion is vacuous
      refine ⟨0, Fin.elim0, 0, le_rfl, fun φ₀ hφ₀ => ?_⟩
      rw [hQ] at hφ₀
      simp at hφ₀
    rcases isEmpty_or_nonempty J with hJ | hJ
    · -- no constraints: the hypothesis already gives non-negativity on all of `Q₀`
      refine ⟨0, Fin.elim0, 0, le_rfl, fun φ₀ hφ₀ => ?_⟩
      have hf0 : 0 ≤ φ₀ f := hY φ₀ hφ₀ fun j => (hJ.false j).elim
      rw [eval_shift_penalty, zero_mul, add_zero]
      linarith
    · -- main compactness argument
      obtain ⟨e, he⟩ := exists_surjective_nat J
      -- some sublevel set `K N` forces `f` above `-ε/2`
      have hKbig : ∃ N, ∀ χ ∈ Kset forb0 (fun i => gs (e i)) N,
          -(ε / 2) < (PositiveHomSpace.toPosHom χ) f := by
        by_contra hcon
        push_neg at hcon
        -- every `C n` is then nonempty ...
        have hne : ∀ n, (Cset forb0 (fun i => gs (e i)) f ε n).Nonempty := by
          intro n
          obtain ⟨χ, hχK, hχf⟩ := hcon n
          exact ⟨χ, mem_Cset.mpr ⟨hχK, hχf⟩⟩
        -- ... so by Cantor's intersection theorem they have a common point `χ`
        obtain ⟨χ, hχ⟩ :=
          IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
            (Cset forb0 (fun i => gs (e i)) f ε)
            (fun n => Cset_succ_subset forb0 (fun i => gs (e i)) f ε n) hne
            ((Cset_isClosed forb0 (fun i => gs (e i)) f ε 0).isCompact)
            (fun n => Cset_isClosed forb0 (fun i => gs (e i)) f ε n)
        simp only [Set.mem_iInter] at hχ
        have hχ0 := mem_Cset.mp (hχ 0)
        have hχQ : χ ∈ Qσ forb0 := (mem_Kset.mp hχ0.1).1
        have hχf : (PositiveHomSpace.toPosHom χ) f ≤ -(ε / 2) := hχ0.2
        -- `χ` kills every constraint: its squares are below every `1/(n+1)`
        have hzero : ∀ j, (PositiveHomSpace.toPosHom χ) (gs j) = 0 := by
          intro j
          obtain ⟨i, rfl⟩ := he j
          have hsq : ((PositiveHomSpace.toPosHom χ) (gs (e i))) ^ 2 ≤ 0 := by
            refine ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_
            filter_upwards [eventually_ge_atTop i] with n hn
            exact (mem_Kset.mp (mem_Cset.mp (hχ n)).1).2 i hn
          exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
        -- so `χ ∈ Y`, where `f` is non-negative: contradiction with `φ₀ f ≤ -ε/2`
        have h0f := hY (PositiveHomSpace.toPosHom χ)
          (by rw [posHomPoint_toPosHom]; exact hχQ) hzero
        linarith
      obtain ⟨N, hKN⟩ := hKbig
      -- the uniform bound `B` on `|eval f|` over the compact nonempty `Q₀`
      obtain ⟨χB, hχBQ, hχBmax⟩ :=
        ((Qσ_isClosed forb0).isCompact).exists_isMaxOn hQne
          ((continuous_eval f).abs.continuousOn)
      set B : ℝ := |(PositiveHomSpace.toPosHom χB) f| with hBdef
      have hB0 : 0 ≤ B := abs_nonneg _
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      refine ⟨N + 1, fun i => e i.val, B * ((N : ℝ) + 1), mul_nonneg hB0 hN1.le,
        fun φ₀ hφ₀ => ?_⟩
      rw [eval_shift_penalty]
      have hSnn : 0 ≤ ∑ i : Fin (N + 1), φ₀ (gs (e i.val)) * φ₀ (gs (e i.val)) :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg _
      by_cases hK : posHomPoint φ₀ ∈ Kset forb0 (fun i => gs (e i)) N
      · -- inside `K N`: `f` is above `-ε/2` and the penalty is non-negative
        have hf2 := hKN _ hK
        rw [toPosHom_posHomPoint] at hf2
        have hMS : 0 ≤ B * ((N : ℝ) + 1) *
            ∑ i : Fin (N + 1), φ₀ (gs (e i.val)) * φ₀ (gs (e i.val)) :=
          mul_nonneg (mul_nonneg hB0 hN1.le) hSnn
        linarith
      · -- outside `K N`: some constraint is badly violated, the penalty dominates `B`
        have hbad : ∃ i ≤ N, 1 / ((N : ℝ) + 1) < (φ₀ (gs (e i))) ^ 2 := by
          by_contra hcon
          push_neg at hcon
          refine hK (mem_Kset.mpr ⟨hφ₀, fun i hi => ?_⟩)
          rw [toPosHom_posHomPoint]
          exact hcon i hi
        obtain ⟨i, hiN, hisq⟩ := hbad
        have hterm : φ₀ (gs (e i)) * φ₀ (gs (e i))
            ≤ ∑ k : Fin (N + 1), φ₀ (gs (e k.val)) * φ₀ (gs (e k.val)) :=
          Finset.single_le_sum
            (f := fun k : Fin (N + 1) => φ₀ (gs (e k.val)) * φ₀ (gs (e k.val)))
            (fun k _ => mul_self_nonneg _)
            (Finset.mem_univ (⟨i, Nat.lt_succ_of_le hiN⟩ : Fin (N + 1)))
        rw [pow_two] at hisq
        have h1 : 1 / ((N : ℝ) + 1)
            ≤ ∑ k : Fin (N + 1), φ₀ (gs (e k.val)) * φ₀ (gs (e k.val)) :=
          hisq.le.trans hterm
        have hfB : -B ≤ φ₀ f := by
          have hb := isMaxOn_iff.mp hχBmax _ hφ₀
          rw [toPosHom_posHomPoint] at hb
          exact (abs_le.mp hb).1
        have h2 : B * ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1))
            ≤ B * ((N : ℝ) + 1) *
              ∑ k : Fin (N + 1), φ₀ (gs (e k.val)) * φ₀ (gs (e k.val)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hB0 hN1.le)
        have h3 : B * ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = B := by
          rw [mul_one_div, mul_div_assoc, div_self hN1.ne', mul_one]
        linarith
  · -- (⇐): evaluate at a point of `Y` and let `ε → 0`
    intro hpen φ₀ hφ₀ hzero
    by_contra hneg
    push_neg at hneg
    obtain ⟨N, js, M, hM0, h⟩ := hpen (-(φ₀ f) / 2) (by linarith)
    have hval := h φ₀ hφ₀
    rw [eval_shift_penalty] at hval
    have hS : ∑ i : Fin N, φ₀ (gs (js i)) * φ₀ (gs (js i)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero (js i), zero_mul]
    rw [hS, mul_zero, add_zero] at hval
    linarith

/-! ## The cone form -/

/-- **Relative Positivstellensatz, cone form**: the `Y`-non-negative empty-type elements are
exactly the `‖·‖_{Q₀}`-closure of the semantic cone of the class plus the span of the squared
constraints. -/
theorem relative_positivstellensatz_closure (forb0 : FinFlag ∅ₜ → Prop) {J : Type}
    [Countable J] (gs : J → FlagAlgebra ∅ₜ) (f : FlagAlgebra ∅ₜ) :
    (∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ forb0 → (∀ j, φ₀ (gs j) = 0) → 0 ≤ φ₀ f)
      ↔
    MemQ0Closure forb0
      {u | ∃ v w : FlagAlgebra ∅ₜ,
        (∀ φ₀ : PositiveHom ∅ₜ, posHomPoint φ₀ ∈ Qσ forb0 → 0 ≤ φ₀ v) ∧
        w ∈ Submodule.span ℝ (Set.range fun j => gs j * gs j) ∧ u = v + w} f := by
  -- (→): given `ε`, `relative_positivstellensatz` provides `N, js, M`; take
  --   `v := f + ε•1 + M•∑ gs(js i) * gs(js i)` (in the semantic cone of the class by the
  --   penalty conclusion) and `w := (-M)•∑ gs(js i) * gs(js i) ∈ span` (finite sums of the
  --   generators; `Submodule.sum_mem`, `smul_mem`).  Then `v + w = f + ε•1` and
  --   `|φ₀ f - φ₀ (f + ε•1)| = ε ≤ ε` (`Q0Within`).
  -- (←): an approximant `u = v + w` has `φ₀ u ≥ 0` for `φ₀ ∈ Y`: `φ₀ v ≥ 0` since `Y ⊆ Q₀`,
  --   and `φ₀ w = 0` by `Submodule.span_induction` (each generator `gs j * gs j` evaluates to
  --   `(φ₀ (gs j))² = 0` on `Y`; evaluation is linear).  Then `Q0Within` gives
  --   `φ₀ f ≥ φ₀ u - ε ≥ -ε` for every `ε > 0`.
  constructor
  · intro hY ε hε
    obtain ⟨N, js, M, hM0, hpos⟩ := (relative_positivstellensatz forb0 gs f).mp hY ε hε
    refine ⟨f + ε • (1 : FlagAlgebra ∅ₜ),
      ⟨f + ε • (1 : FlagAlgebra ∅ₜ) + M • ∑ i : Fin N, gs (js i) * gs (js i),
        (-M) • ∑ i : Fin N, gs (js i) * gs (js i), hpos, ?_, ?_⟩, ?_⟩
    · -- the compensating term lies in the span of the squared constraints
      exact Submodule.smul_mem _ (-M) (Submodule.sum_mem _ fun i _ =>
        Submodule.subset_span ⟨js i, rfl⟩)
    · -- the two pieces recombine to `f + ε•1`
      rw [neg_smul, add_neg_cancel_right]
    · -- `f` and `f + ε•1` are within `ε` in the `Q₀`-seminorm
      intro φ₀ hφ₀
      have hval : φ₀ (f + ε • (1 : FlagAlgebra ∅ₜ)) = φ₀ f + ε := by
        rw [PositiveHom.map_add, PositiveHom.map_smul, PositiveHom.map_one, mul_one]
      rw [hval, show φ₀ f - (φ₀ f + ε) = -ε by ring, abs_neg]
      exact le_of_eq (abs_of_pos hε)
  · intro hcl φ₀ hφ₀ hzero
    by_contra hneg
    push_neg at hneg
    obtain ⟨u, hu, hwithin⟩ := hcl (-(φ₀ f) / 2) (by linarith)
    obtain ⟨v, w, hv, hw, rfl⟩ := hu
    -- the span of the squared constraints evaluates to `0` at `φ₀ ∈ Y`
    have hspan : ∀ x ∈ Submodule.span ℝ (Set.range fun j => gs j * gs j), φ₀ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        show φ₀ (gs j * gs j) = 0
        rw [PositiveHom.map_mul, hzero j, zero_mul]
      | zero => exact PositiveHom.map_zero φ₀
      | add y z _ _ ihy ihz => rw [PositiveHom.map_add, ihy, ihz, add_zero]
      | smul a y _ ih => rw [PositiveHom.map_smul, ih, mul_zero]
    have hφw : φ₀ w = 0 := hspan w hw
    have hφv : 0 ≤ φ₀ v := hv φ₀ hφ₀
    have habs := hwithin φ₀ hφ₀
    rw [PositiveHom.map_add, hφw, add_zero] at habs
    have hab := abs_le.mp habs
    linarith [hab.1, hab.2]

end FlagAlgebras.MetaTheory
