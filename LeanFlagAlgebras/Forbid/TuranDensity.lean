import LeanFlagAlgebras.GraphAlgebra.SubgraphDensity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

open GraphAlgebras
open Asymptotics Filter Finset Fintype Topology

variable {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/--
`generalizedExtremalNumber n H F` is the maximum number of induced copies of `F`
among all `H`-free graphs on `n` vertices.

This generalizes `extremalNumber n H`, where the optimized statistic is the edge count.
-/
noncomputable def generalizedExtremalNumber (n : ℕ) (H : SimpleGraph U) (F : SimpleGraph W) : ℕ
  := by
  classical
  exact sup { G : SimpleGraph (Fin n) | H.Free G }
    (fun (G : SimpleGraph (Fin n)) ↦ GraphAlgebras.subgraphCount F G)

omit [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] in
/--
`generalizedExtremalNumber n H F` is at most `m` if and only if every `H`-free graph on `n`
vertices has at most `m` induced copies of `F`.
-/
theorem generalizedExtremalNumber_le_iff
  (n : ℕ) (H : SimpleGraph U) (F : SimpleGraph W) (m : ℕ) :
    generalizedExtremalNumber n H F ≤ m ↔
    ∀ ⦃G : SimpleGraph (Fin n)⦄,
        H.Free G → GraphAlgebras.subgraphCount F G ≤ m
  := by
  simp [generalizedExtremalNumber]

omit [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] in
@[inherit_doc generalizedExtremalNumber_le_iff]
theorem generalizedExtremalNumber_le_iff_of_nonneg
    (n : ℕ) (H : SimpleGraph U) (F : SimpleGraph W) {m : ℝ} (h : 0 ≤ m) :
    generalizedExtremalNumber n H F ≤ m ↔
    ∀ ⦃G : SimpleGraph (Fin n)⦄,
        H.Free G → (GraphAlgebras.subgraphCount F G : ℝ) ≤ m
  := by
  simp_rw [← Nat.le_floor_iff h]
  exact generalizedExtremalNumber_le_iff n H F ⌊m⌋₊

/--
The generalized Turán density associated to a forbidden graph `H` and a target graph `F`.

It is defined as the limit of
`generalizedExtremalNumber n H F / n.choose (Fintype.card W)` as `n → ∞`.
-/
noncomputable def generalizedTuranDensity (H : SimpleGraph U) (F : SimpleGraph W) : ℝ :=
  limUnder atTop fun n ↦
    (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ)

lemma choose_succ_div_choose
    {n m : ℕ} (h : m ≤ n) :
    ((n + 1).choose m / n.choose m : ℝ) = ((n + 1 : ℕ) / (n - m + 1 : ℕ) : ℝ)
  := by
  rw [Nat.cast_choose ℝ (by linarith), Nat.cast_choose ℝ (by linarith)]
  simp only [← div_mul, ← div_div]
  rw [mul_assoc, mul_comm]
  simp only [mul_div]
  rw [mul_assoc, mul_comm, ← mul_div, div_self (by positivity), mul_one]
  rw [mul_comm, ← mul_div, Nat.sub_add_comm h, Nat.factorial_succ (n - m), mul_comm (n - m + 1),
    Nat.cast_mul, ← div_div, div_self (by positivity), mul_div, mul_one]
  rw [div_div, mul_comm, ← div_div, Nat.factorial_succ n, Nat.cast_mul, ← mul_div,
    div_self (by positivity), mul_one]

open Classical in
lemma subgraphSet_deleteIncidenceSet_eq_filter
    {n : ℕ} (F : SimpleGraph W) (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    #{E ∈ subgraphSet F G | v ∉ E.verts} = subgraphCount F (G.deleteIncidenceSet v)
  := by
  sorry

lemma subgraphCount_deleteIncidenceSet_le_generalizedExtremalNumber
    {n : ℕ} {H : SimpleGraph U} {F : SimpleGraph W}
    {G : SimpleGraph (Fin (n + 1))} (hG_free : H.Free G) (v : Fin (n + 1)) :
    subgraphCount F (G.deleteIncidenceSet v) ≤ generalizedExtremalNumber n H F
  := by
  sorry

theorem antitoneOn_generalizedExtremalNumber_div_choose
    (H : SimpleGraph U) (F : SimpleGraph W) :
    AntitoneOn
      (fun n ↦ (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ))
      (Set.Ici (Fintype.card W))
  := by
  classical
  let m := Fintype.card W
  show AntitoneOn (fun n ↦ (generalizedExtremalNumber n H F / n.choose m : ℝ)) (Set.Ici m)
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    generalizedExtremalNumber_le_iff_of_nonneg (n + 1) H F (by positivity)]
  intro G hG_free
  rw [mul_comm, mul_div, mul_comm, ← mul_div, choose_succ_div_choose hn, mul_div, mul_comm,
    le_div_iff₀ (by positivity), ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
  suffices hdc :
      #(GraphAlgebras.subgraphSet F G) • (n - m + 1)
        ≤ #(Finset.univ : Finset (Fin (n + 1))) • generalizedExtremalNumber n H F by
    simpa [GraphAlgebras.subgraphCount, nsmul_eq_mul, Nat.mul_comm] using hdc
  apply (card_nsmul_le_card_nsmul' (r := fun v H' => v ∉ H'.verts))
  · intro E hE
    simp [subgraphSet] at hE
    rcases hE with ⟨hE_ind, ⟨φ⟩⟩
    have hcardE : Fintype.card E.verts = m := by
      simpa [m] using Fintype.card_congr φ.toEquiv
    have hcard_filter :
        #(Finset.filter (Membership.mem E.verts) (Finset.univ : Finset (Fin (n + 1)))) = m := by
      rw [← hcardE]
      simp only [card_ofFinset]
    simp [bipartiteBelow, filter_not]
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hcard_filter, Fintype.card_fin]
    omega
  · intro v hv
    simp [bipartiteAbove]
    simpa [subgraphSet_deleteIncidenceSet_eq_filter]
      using subgraphCount_deleteIncidenceSet_le_generalizedExtremalNumber hG_free v

/--
The generalized Turán density is well-defined as the limit of the normalized generalized
extremal numbers.
-/
theorem tendsto_generalizedTuranDensity
  {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
  (H : SimpleGraph U) (F : SimpleGraph W) :
    Tendsto
      (fun n ↦ (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ))
      atTop (𝓝 (generalizedTuranDensity H F)) := by
  have hmono := antitoneOn_generalizedExtremalNumber_div_choose H F
  let f := fun n ↦ (generalizedExtremalNumber n H F / n.choose (Fintype.card W) : ℝ)
  suffices h : ∃ x, Tendsto (fun n ↦ f (n + Fintype.card W)) atTop (𝓝 x) by
    obtain ⟨_, h⟩ := by simpa [tendsto_add_atTop_iff_nat (Fintype.card W)] using h
    simpa [generalizedTuranDensity, f, ← Tendsto.limUnder_eq h] using h
  use ⨅ n, f (n + Fintype.card W)
  apply tendsto_atTop_ciInf
  · rw [antitone_add_nat_iff_antitoneOn_nat_Ici]
    simpa [f] using hmono
  · use 0
    intro n ⟨_, hn⟩
    rw [← hn]
    positivity
