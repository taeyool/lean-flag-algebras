import LeanFlagAlgebras.GraphAlgebra.SubgraphDensity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

/-! # Generalized Turán numbers and densities

Generalized Turán-type extremal quantities: `generalizedExtremalNumber n H F` is the
maximum number of induced copies of `F` over all `H`-free graphs on `n` vertices, and
`generalizedTuranDensity H F` is the limit of the normalized extremal numbers. The file
establishes the basic characterizations, monotonicity of the normalized sequence, and
that the limit defining the density is well-defined (`tendsto_generalizedTuranDensity`).
-/

open GraphAlgebras
open Asymptotics Filter Finset Fintype Topology SimpleGraph

variable {U V W : Type}
  [Fintype U] [DecidableEq U]
  [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

open Classical in
/--
`generalizedExtremalNumber n H F` is the maximum number of induced copies of `F`
among all `H`-free graphs on `n` vertices.

This generalizes `extremalNumber n H`, where the optimized statistic is the edge count.
-/
noncomputable def generalizedExtremalNumber (n : ℕ) (H : SimpleGraph U) (F : SimpleGraph W) : ℕ :=
  sup { G : SimpleGraph (Fin n) | H.Free G }
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

omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
open Classical in
theorem generalizedExtremalNumber_of_fintypeCard_eq
    {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (H : SimpleGraph U) (F : SimpleGraph W) (hc : card X = n) :
    generalizedExtremalNumber n H F =
      sup { G : SimpleGraph X | H.Free G } (fun G => subgraphCount F G) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [generalizedExtremalNumber, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
    rw [Finset.sup_le_iff]
    intro G h
    let G' := G.map e.toEmbedding
    have h' : G' ∈ univ.filter (H.Free ·) := by
      rw [mem_filter, ← free_congr .refl (.map e G)]
      simpa using h
    rw [subgraphCount_eq_of_iso F (.map e G)]
    convert @le_sup _ _ _ _ { G | H.Free G } (fun G => subgraphCount F G) G' h'

omit [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] in
/-- If `G` is `H`-free, then `G` has at most `generalizedExtremalNumber (card V) H F`
induced copies of `F`. -/
theorem subgraphCount_le_generalizedExtremalNumber
    {H : SimpleGraph U} {F : SimpleGraph W} {G : SimpleGraph V} (h : H.Free G) :
    subgraphCount F G ≤ generalizedExtremalNumber (card V) H F := by
  rw [generalizedExtremalNumber_of_fintypeCard_eq H F rfl]
  convert @le_sup _ _ _ _ { G : SimpleGraph V | H.Free G } (fun G => subgraphCount F G) G
    (by simpa using h)

omit [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] in
@[inherit_doc generalizedExtremalNumber_le_iff]
theorem generalizedExtremalNumber_le_iff_of_nonneg
    (n : ℕ) (H : SimpleGraph U) (F : SimpleGraph W) {m : ℝ} (h : 0 ≤ m) :
    generalizedExtremalNumber n H F ≤ m ↔
    ∀ ⦃G : SimpleGraph (Fin n)⦄,
        H.Free G → (subgraphCount F G : ℝ) ≤ m
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

omit [Fintype W] [DecidableEq W] in
open Classical in
lemma card_subgraphSet_filter_notMem_eq_subgraphCount_induce_compl
    {n : ℕ} (F : SimpleGraph W) (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    #{E ∈ subgraphSet F G | v ∉ E.verts} = subgraphCount F (G.induce {v}ᶜ)
  := by
  let emb : G.induce {v}ᶜ ↪g G := {
      toEmbedding := Function.Embedding.subtype ({v}ᶜ : Set (Fin (n + 1)))
      map_rel_iff' := by intros; rfl
  }
  symm
  refine Finset.card_bij (fun E _ => E.map emb.toHom) ?_ ?_ ?_
  · intro E hE
    rcases (mem_subgraphSet_iff.mp hE) with ⟨hE_ind, hE_iso⟩
    rw [Finset.mem_filter]
    constructor
    · rw [mem_subgraphSet_iff]
      constructor
      · rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩ hxy
        refine ⟨x', y', ?_, rfl, rfl⟩
        exact hE_ind hx' hy' ((emb.map_rel_iff).1 hxy)
      · exact ⟨(emb.toCopy.isoSubgraphMap E).symm.trans hE_iso.some⟩
    · rintro ⟨x, hx, hxeq⟩
      exact x.2 (by simpa using hxeq)
  · intro E₁ hE₁ E₂ hE₂ hEq
    have hle_of_map_eq :
        ∀ {A B : Subgraph (G.induce {v}ᶜ)},
          A.map emb.toHom = B.map emb.toHom → A ≤ B := by
      intro A B hAB
      constructor
      · intro x hx
        have hxmap : emb x ∈ (A.map emb.toHom).verts := ⟨x, hx, rfl⟩
        have hxmap' : emb x ∈ (B.map emb.toHom).verts := by simpa [hAB] using hxmap
        rcases hxmap' with ⟨x', hx', hx'eq⟩
        simpa [emb.injective hx'eq] using hx'
      · intro x y hxy
        have hxyMap : (A.map emb.toHom).Adj (emb x) (emb y) := ⟨x, y, hxy, rfl, rfl⟩
        have hxyMap' : (B.map emb.toHom).Adj (emb x) (emb y) := by simpa [hAB] using hxyMap
        rcases hxyMap' with ⟨x', y', hxy', hx'eq, hy'eq⟩
        have hx' : x' = x := emb.injective (by simpa using hx'eq)
        have hy' : y' = y := emb.injective (by simpa using hy'eq)
        simpa [hx', hy'] using hxy'
    exact le_antisymm (hle_of_map_eq hEq) (hle_of_map_eq hEq.symm)
  · intro E hE
    rcases Finset.mem_filter.mp hE with ⟨hE_sub, hE_notv⟩
    let A : Subgraph (G.induce {v}ᶜ) := E.comap emb.toHom
    have hmap : A.map emb.toHom = E := by
      apply le_antisymm
      · constructor
        · rintro x ⟨u, hu, rfl⟩
          exact hu
        · rintro x y ⟨u, w, huw, rfl, rfl⟩
          exact huw.2
      · constructor
        · intro x hx
          refine ⟨⟨x, ?_⟩, hx, rfl⟩
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          exact hE_notv (h ▸ hx)
        · intro x y hxy
          refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩, ?_, rfl, rfl⟩
          · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            exact hE_notv (h ▸ E.edge_vert hxy)
          · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            exact hE_notv (h ▸ E.edge_vert hxy.symm)
          · refine ⟨(emb.map_rel_iff).2 (E.adj_sub hxy), hxy⟩
    have hA_mem : A ∈ subgraphSet F (G.induce {v}ᶜ) := by
      rcases (mem_subgraphSet_iff.mp hE_sub) with ⟨hE_ind, hE_iso⟩
      rw [mem_subgraphSet_iff]
      constructor
      · intro x hx y hy hxy
        refine ⟨hxy, ?_⟩
        exact hE_ind hx hy ((emb.map_rel_iff).1 hxy)
      · have hE_iso_map : Nonempty ((A.map emb.toHom).coe ≃g F) := hmap ▸ hE_iso
        exact ⟨(emb.toCopy.isoSubgraphMap A).trans hE_iso_map.some⟩
    refine ⟨A, hA_mem, ?_⟩
    simpa [A] using hmap

omit [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] in
lemma subgraphCount_induce_compl_le_generalizedExtremalNumber
    {n : ℕ} {H : SimpleGraph U} {F : SimpleGraph W}
    {G : SimpleGraph (Fin (n + 1))} (hG_free : H.Free G) (v : Fin (n + 1)) :
    subgraphCount F (G.induce {v}ᶜ) ≤ generalizedExtremalNumber n H F
  := by
  have h_ind_free : H.Free (G.induce {v}ᶜ) := by
    contrapose! hG_free
    exact hG_free.trans ⟨Copy.induce G ({v}ᶜ : Set (Fin (n + 1)))⟩
  have h_card : card ({v}ᶜ : Set (Fin (n + 1))) = n := by
    rw [card_ofFinset, Set.filter_mem_univ_eq_toFinset]
    simp [card_compl, Fintype.card_fin, card_singleton]
  simp_rw [← h_card]
  exact subgraphCount_le_generalizedExtremalNumber h_ind_free

omit [Fintype U] [DecidableEq U] [DecidableEq W] in
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
    rw [card_subgraphSet_filter_notMem_eq_subgraphCount_induce_compl]
    exact subgraphCount_induce_compl_le_generalizedExtremalNumber hG_free v

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
