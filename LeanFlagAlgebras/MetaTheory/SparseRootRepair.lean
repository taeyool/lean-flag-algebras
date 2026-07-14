import LeanFlagAlgebras.MetaTheory.FinitePlanting

/-! # Sparse root-blow-up repairs imply finite planting (paper §8)

This is the Lean counterpart of paper §8's concrete, checkable criterion: `def:sparse-root-repair`
and `thm:sparse-repair-planting`.

A hereditary class `K` has **sparse root-blow-up repairs at `σ`** if every large in-class `σ`-flag
`(G, θ)` can be turned into an in-class graph `H` by blowing up *only* the `k = n₀` labelled
vertices into positive-density independent root clusters `R₁,…,R_k` (each of size
`L ∈ [λn/2, λn]`), leaving the non-root vertices `U = V(G) ∖ im θ` as singletons, and repairing only
a *sparse* (at most `ρn²`) set of old–old edges.  The cross-adjacencies are prescribed exactly:
between clusters by the root adjacency (clause (i)), and between a cluster and `U` by the original
root's adjacency to `U` (clause (ii)); the within-`U` part may differ from `G[U]` on at most `ρn²`
unordered pairs (clause (iii)).

`sparseRootRepair_finitePlanting` (`thm:sparse-repair-planting`): sparse root-blow-up repairs imply
the finite planting property (taking `Θ = R₁ × ⋯ × R_k`, one vertex per cluster), via a two-event
sampling estimate — a uniformly random `(ℓ−k)`-subset of the non-roots is unlikely to meet the
clusters (`≤ 2mkλ`) or to span an altered old pair (`≤ 4m²ρ`), so the rooted `σ`-flag densities up
to size `m` shift by less than `ε`.  Composed with
[`finitePlanting_root_plantable`](./FinitePlanting.lean), this gives root-plantability.
-/

open FlagAlgebras SimpleGraph

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- The non-root vertices of a `σ`-flag presented on `Fin n` — the vertex set `U = V(G) ∖ im θ`. -/
abbrev nonRoot {n : ℕ} (G : LabeledGraph σ (Fin n)) : Type :=
  {v : Fin n // v ∉ Set.range G.type_embed}

/-- **Sparse root-blow-up repairs** (`def:sparse-root-repair`).  For `k = n₀ ≥ 1` labelled vertices:
for every `0 < λ ≤ 1` and `ρ > 0` there is a threshold `n_0` such that every in-class `σ`-flag
`(G, θ)` on `Fin n` with `n ≥ n_0` admits a cluster size `L ∈ [λn/2, λn]` and an in-class graph `H`
on `U ⊕ (Fin n₀ × Fin L)` (`U` the non-roots) with:

* (i) clusters `Rᵢ, Rⱼ` (`i ≠ j`) complete/empty according to the root adjacency `θ(i)θ(j)`;
* (ii) every cluster vertex of `Rᵢ` adjacent to `u ∈ U` iff `θ(i)` is adjacent to `u` in `G`;
* (iii) the within-`U` adjacency differs from `G[U]` on at most `ρn²` unordered pairs. -/
def SparseRootRepair (hc : HeredClass) (σ : FlagType (Fin n₀)) : Prop :=
  1 ≤ n₀ ∧
  ∀ (lam ρ : ℝ), 0 < lam → lam ≤ 1 → 0 < ρ →
    ∃ n_0 : ℕ, ∀ (n : ℕ) (G : LabeledGraph σ (Fin n)), hc.Mem G.graph → n_0 ≤ n →
      ∃ (L : ℕ) (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))),
        (lam * n / 2 ≤ (L : ℝ)) ∧ ((L : ℝ) ≤ lam * n) ∧ hc.Mem H ∧
        (∀ (i j : Fin n₀), i ≠ j → ∀ (a b : Fin L),
            (H.Adj (Sum.inr (i, a)) (Sum.inr (j, b))
              ↔ G.graph.Adj (G.type_embed i) (G.type_embed j))) ∧
        (∀ (i : Fin n₀) (a : Fin L) (u : nonRoot G),
            (H.Adj (Sum.inr (i, a)) (Sum.inl u) ↔ G.graph.Adj (G.type_embed i) u.1)) ∧
        ((Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
            ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => H.Adj (Sum.inl u) (Sum.inl u')
                  ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p)).card : ℝ)
          ≤ ρ * (n : ℝ) ^ 2

/-! ## Private counting infrastructure for the planting estimate -/

open Finset in
/-- Real-arithmetic core of the coupling bound (`thm:sparse-repair-planting`): a three-term
triangle-inequality split of `p_H − p_G`. -/
private lemma coupling_real_bound (nUH nUG nNot nBad nExtra CW CU : ℝ)
    (hCWpos : 0 < CW) (hCUpos : 0 < CU) (hCUleCW : CU ≤ CW)
    (hnNot_real : nNot = CW - CU)
    (hExtra_le : nExtra ≤ nNot) (hExtra0 : 0 ≤ nExtra)
    (hnUG0 : 0 ≤ nUG) (_hnBad0 : 0 ≤ nBad)
    (hUHUG : nUH ≤ nUG + nBad) (hUGUH : nUG ≤ nUH + nBad)
    (hpG_le1 : nUG ≤ CU) :
    |(nUH + nExtra)/CW - nUG / CU|
      ≤ 2 * nNot / CW + nBad / CW := by
  have hCWne : CW ≠ 0 := ne_of_gt hCWpos
  have hCUne : CU ≠ 0 := ne_of_gt hCUpos
  have key : (nUH + nExtra) / CW - nUG / CU
      = nExtra/CW + (nUH - nUG)/CW + nUG * (1/CW - 1/CU) := by field_simp; ring
  rw [key]
  have hT1 : |nExtra/CW| ≤ nNot/CW := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_div_iff_of_pos_right hCWpos).mpr hExtra_le
  have hT2 : |(nUH - nUG)/CW| ≤ nBad/CW := by
    rw [abs_div, abs_of_pos hCWpos]
    apply (div_le_div_iff_of_pos_right hCWpos).mpr
    rw [abs_le]; constructor <;> linarith
  have hT3 : |nUG * (1/CW - 1/CU)| ≤ nNot/CW := by
    have hval : nUG * (1/CW - 1/CU) = - (nUG * (CW - CU) / (CU * CW)) := by field_simp; ring
    rw [hval, abs_neg]
    have h0 : 0 ≤ nUG * (CW - CU) / (CU * CW) := by
      apply div_nonneg; · apply mul_nonneg hnUG0; linarith
      · positivity
    rw [abs_of_nonneg h0]
    rw [hnNot_real, div_le_div_iff₀ (by positivity) hCWpos]
    have hd : 0 ≤ CW - CU := by linarith
    nlinarith [mul_nonneg hd (le_of_lt hCWpos), mul_nonneg (mul_nonneg hnUG0 hd) (le_of_lt hCWpos)]
  have htri : |nExtra/CW + (nUH - nUG)/CW + nUG * (1/CW - 1/CU)|
      ≤ |nExtra/CW| + |(nUH - nUG)/CW| + |nUG * (1/CW - 1/CU)| := by
    have h1 := abs_add_le (nExtra/CW + (nUH - nUG)/CW) (nUG * (1/CW - 1/CU))
    have h2 := abs_add_le (nExtra/CW) ((nUH - nUG)/CW)
    linarith
  have hfin : |nExtra/CW| + |(nUH - nUG)/CW| + |nUG * (1/CW - 1/CU)| ≤ 2 * nNot / CW + nBad / CW := by
    have h2 : (2:ℝ) * nNot / CW = nNot/CW + nNot/CW := by ring
    rw [h2]; linarith
  linarith

open Finset in
/-- **Coupling-free combinatorial bound.**  For a uniform `q`-sample drawn from a finite pool
`Vall`, with `Uf ⊆ Vall` the "good" part: if events `AH` and `AG` agree on samples inside `Uf` that
avoid `Bad`, then the two sampling probabilities differ by at most twice the chance of leaving `Uf`
plus the chance of hitting `Bad` inside `Uf`. -/
private lemma counting_coupling_bound {W : Type} [DecidableEq W] (Vall Uf : Finset W) (q : ℕ)
    (hUf : Uf ⊆ Vall)
    (AH AG Bad : Finset W → Prop) [DecidablePred AH] [DecidablePred AG] [DecidablePred Bad]
    (hCU : 0 < (Uf.powersetCard q).card)
    (hgood : ∀ S ∈ Vall.powersetCard q, S ⊆ Uf → ¬ Bad S → (AH S ↔ AG S)) :
    |((Vall.powersetCard q).filter AH).card / ((Vall.powersetCard q).card : ℝ)
        - ((Uf.powersetCard q).filter AG).card / ((Uf.powersetCard q).card : ℝ)|
      ≤ 2 * ((Vall.powersetCard q).filter (fun S => ¬ S ⊆ Uf)).card
            / ((Vall.powersetCard q).card : ℝ)
        + ((Vall.powersetCard q).filter (fun S => S ⊆ Uf ∧ Bad S)).card
            / ((Vall.powersetCard q).card : ℝ) := by
  classical
  set PW := Vall.powersetCard q with hPW
  set PU := PW.filter (· ⊆ Uf) with hPUdef
  have hPU : Uf.powersetCard q = PU := by
    ext S
    simp only [hPUdef, hPW, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hSUf, hcard⟩; exact ⟨⟨hSUf.trans hUf, hcard⟩, hSUf⟩
    · rintro ⟨⟨_, hcard⟩, hSUf⟩; exact ⟨hSUf, hcard⟩
  set nH : ℕ := (PW.filter AH).card with hnH
  set nUH : ℕ := (PU.filter AH).card with hnUH
  set nUG : ℕ := (PU.filter AG).card with hnUG
  set nNot : ℕ := (PW.filter (fun S => ¬ S ⊆ Uf)).card with hnNot
  set nBad : ℕ := (PW.filter (fun S => S ⊆ Uf ∧ Bad S)).card with hnBad
  have hnBad_eq : nBad = (PU.filter Bad).card := by rw [hnBad, hPUdef, Finset.filter_filter]
  have hCU_eq : (Uf.powersetCard q).card = PU.card := by rw [hPU]
  have hPUleC : PU.card ≤ PW.card := by rw [hPUdef]; exact Finset.card_filter_le _ _
  have hCWnat_pos : 0 < PW.card := by rw [hCU_eq] at hCU; omega
  have hnNot_real : (nNot : ℝ) = (PW.card : ℝ) - (PU.card : ℝ) := by
    have hadd := Finset.card_filter_add_card_filter_not (s := PW) (p := fun S => S ⊆ Uf)
    rw [hnNot, hPUdef]
    rw [show (PW.filter (fun S => ¬ S ⊆ Uf)).card = PW.card - (PW.filter (· ⊆ Uf)).card by
      rw [hPUdef] at hPUleC; omega]
    rw [Nat.cast_sub (by rw [hPUdef] at hPUleC; exact hPUleC)]
  set nExtra : ℕ := (PW.filter (fun S => AH S ∧ ¬ S ⊆ Uf)).card with hnExtra
  have hsplit : nH = nUH + nExtra := by
    rw [hnH, ← Finset.card_filter_add_card_filter_not (s := PW.filter AH) (p := fun S => S ⊆ Uf)]
    have e1 : (PW.filter AH).filter (fun S => S ⊆ Uf) = PU.filter AH := by
      rw [hPUdef, Finset.filter_filter, Finset.filter_filter]; ext S
      simp only [Finset.mem_filter]; tauto
    have e2 : (PW.filter AH).filter (fun S => ¬ S ⊆ Uf) = PW.filter (fun S => AH S ∧ ¬ S ⊆ Uf) := by
      rw [Finset.filter_filter]
    rw [e1, e2, hnUH, hnExtra]
  have hExtra_le : nExtra ≤ nNot := by
    rw [hnExtra, hnNot]; apply Finset.card_le_card
    intro S hS; rw [Finset.mem_filter] at hS ⊢; exact ⟨hS.1, hS.2.2⟩
  have hT2_aux : ∀ (P Q : Finset W → Prop) [DecidablePred P] [DecidablePred Q],
      (∀ S ∈ PW, S ⊆ Uf → ¬ Bad S → (P S ↔ Q S)) →
      (PU.filter P).card ≤ (PU.filter Q).card + (PU.filter Bad).card := by
    intro P Q _ _ hPQ
    have hsub : PU.filter P ⊆ PU.filter Q ∪ PU.filter Bad := by
      intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hSPU, hP⟩ := hS
      have hSmem : S ∈ PW ∧ S ⊆ Uf := by rw [hPUdef, Finset.mem_filter] at hSPU; exact hSPU
      rw [Finset.mem_union]
      by_cases hBad : Bad S
      · right; rw [Finset.mem_filter]; exact ⟨hSPU, hBad⟩
      · left; rw [Finset.mem_filter]; exact ⟨hSPU, (hPQ S hSmem.1 hSmem.2 hBad).mp hP⟩
    calc (PU.filter P).card ≤ (PU.filter Q ∪ PU.filter Bad).card := Finset.card_le_card hsub
      _ ≤ (PU.filter Q).card + (PU.filter Bad).card := Finset.card_union_le _ _
  have hUHUG : nUH ≤ nUG + nBad := by rw [hnUH, hnUG, hnBad_eq]; exact hT2_aux AH AG hgood
  have hUGUH : nUG ≤ nUH + nBad := by
    rw [hnUG, hnUH, hnBad_eq]; exact hT2_aux AG AH (fun S hS h1 h2 => (hgood S hS h1 h2).symm)
  have hpG_le1 : nUG ≤ PU.card := by rw [hnUG]; exact Finset.card_filter_le _ _
  rw [hPU]
  show |(nH : ℝ) / (PW.card : ℝ) - (nUG : ℝ) / (PU.card : ℝ)|
      ≤ 2 * (nNot : ℝ) / (PW.card : ℝ) + (nBad : ℝ) / (PW.card : ℝ)
  rw [hsplit]; push_cast
  apply coupling_real_bound (nUH : ℝ) (nUG : ℝ) (nNot : ℝ) (nBad : ℝ) (nExtra : ℝ)
    (PW.card : ℝ) (PU.card : ℝ)
  · exact_mod_cast hCWnat_pos
  · rw [hCU_eq] at hCU; exact_mod_cast hCU
  · exact_mod_cast hPUleC
  · exact hnNot_real
  · exact_mod_cast hExtra_le
  · positivity
  · positivity
  · positivity
  · exact_mod_cast hUHUG
  · exact_mod_cast hUGUH
  · exact_mod_cast hpG_le1

open Finset in
/-- The number of size-`q` supersets of `R` inside an ambient pool `Vall` is `C(|Vall|−|R|, q−|R|)`. -/
private lemma superset_count_amb {W : Type} [DecidableEq W] (Vall R : Finset W) (q : ℕ)
    (hR : R ⊆ Vall) (hr : R.card ≤ q) :
    ((Vall.powersetCard q).filter (fun S => R ⊆ S)).card
      = (Vall.card - R.card).choose (q - R.card) := by
  classical
  rw [show (Vall.card - R.card).choose (q - R.card)
        = ((Vall \ R).powersetCard (q - R.card)).card by
        rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hR]]
  apply Finset.card_nbij' (i := fun S => S \ R) (j := fun Q => Q ∪ R)
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hSsub, hcard⟩, hRS⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx; rw [Finset.mem_sdiff] at hx ⊢; exact ⟨hSsub hx.1, hx.2⟩
    · rw [Finset.card_sdiff_of_subset hRS, hcard]
  · intro Q hQ
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hQ
    obtain ⟨hQsub, hQcard⟩ := hQ
    have hdisj : Disjoint Q R := by
      rw [Finset.disjoint_right]; intro x hxR hxQ
      have := hQsub hxQ; rw [Finset.mem_sdiff] at this; exact this.2 hxR
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.subset_union_right⟩
    · apply Finset.union_subset (hQsub.trans Finset.sdiff_subset) hR
    · rw [Finset.card_union_of_disjoint hdisj, hQcard]; omega
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    exact Finset.sdiff_union_of_subset hS.2
  · intro Q hQ
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hQ
    have hdisj : Disjoint Q R := by
      rw [Finset.disjoint_right]; intro x hxR hxQ
      have := hQ.1 hxQ; rw [Finset.mem_sdiff] at this; exact this.2 hxR
    exact Finset.union_sdiff_cancel_right hdisj

/-- `m · C(m−1, q−1) = q · C(m, q)`. -/
private lemma choose_mul_eq (m q : ℕ) (hm : 1 ≤ m) (hq : 1 ≤ q) :
    m * (m - 1).choose (q - 1) = q * m.choose q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [Nat.add_sub_cancel_left]
  have h := Nat.add_one_mul_choose_eq n k
  rw [Nat.add_comm 1 n, Nat.add_comm 1 k, h]; ring

/-- `m · (m−1) · C(m−2, q−2) = q · (q−1) · C(m, q)`. -/
private lemma choose_mul_pair_eq (m q : ℕ) (hm : 2 ≤ m) (hq : 2 ≤ q) :
    m * (m - 1) * (m - 2).choose (q - 2) = q * (q - 1) * m.choose q := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hq1 : 1 ≤ q - 1 := by omega
  have h2 := choose_mul_eq (m-1) (q-1) hm1 hq1
  have h1 := choose_mul_eq m q (by omega) (by omega)
  rw [show m - 1 - 1 = m - 2 by omega, show q - 1 - 1 = q - 2 by omega] at h2
  calc m * (m - 1) * (m - 2).choose (q - 2)
      = m * ((m - 1) * (m - 2).choose (q - 2)) := by ring
    _ = m * ((q - 1) * (m - 1).choose (q - 1)) := by rw [h2]
    _ = (q - 1) * (m * (m - 1).choose (q - 1)) := by ring
    _ = (q - 1) * (q * m.choose q) := by rw [h1]
    _ = q * (q - 1) * m.choose q := by ring

open Finset in
/-- **Meets-`Uf`ᶜ bound** (the "sample leaves the pool" event), cross-multiplied: the number of
`q`-samples not contained in `Uf`, times `|Vall|`, is at most `|Vall∖Uf| · q · C(|Vall|, q)`. -/
private lemma meets_R_nat {W : Type} [DecidableEq W] (Vall Uf : Finset W) (q : ℕ)
    (_hUf : Uf ⊆ Vall) :
    ((Vall.powersetCard q).filter (fun S => ¬ S ⊆ Uf)).card * Vall.card
      ≤ (Vall \ Uf).card * q * Vall.card.choose q := by
  classical
  set m := Vall.card with hm
  have hub : ((Vall.powersetCard q).filter (fun S => ¬ S ⊆ Uf)).card
      ≤ ∑ a ∈ Vall \ Uf, ((Vall.powersetCard q).filter (fun S => a ∈ S)).card := by
    have hsub : (Vall.powersetCard q).filter (fun S => ¬ S ⊆ Uf)
        ⊆ (Vall \ Uf).biUnion (fun a => (Vall.powersetCard q).filter (fun S => a ∈ S)) := by
      intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hSpc, hSnsub⟩ := hS
      rw [Finset.mem_powersetCard] at hSpc
      rw [Finset.mem_biUnion]
      rw [Finset.not_subset] at hSnsub
      obtain ⟨a, haS, haUf⟩ := hSnsub
      refine ⟨a, Finset.mem_sdiff.mpr ⟨hSpc.1 haS, haUf⟩, ?_⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]; exact ⟨hSpc, haS⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · subst hq0
    have hX0 : ((Vall.powersetCard 0).filter (fun S => ¬ S ⊆ Uf)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      have : S = ∅ := Finset.card_eq_zero.mp hS.2
      simp [this]
    rw [hX0]; simp
  · have hsummand : ∀ a ∈ Vall \ Uf,
        ((Vall.powersetCard q).filter (fun S => a ∈ S)).card = (m - 1).choose (q - 1) := by
      intro a ha
      have haVall : a ∈ Vall := (Finset.mem_sdiff.mp ha).1
      have heq : (Vall.powersetCard q).filter (fun S => a ∈ S)
          = (Vall.powersetCard q).filter (fun S => {a} ⊆ S) := by
        apply Finset.filter_congr; intro S _; simp [Finset.singleton_subset_iff]
      rw [heq, superset_count_amb Vall {a} q (by simpa using haVall) (by simpa using hqpos)]
      simp [hm]
    rw [Finset.sum_congr rfl hsummand, Finset.sum_const, smul_eq_mul] at hub
    calc ((Vall.powersetCard q).filter (fun S => ¬ S ⊆ Uf)).card * m
        ≤ ((Vall \ Uf).card * (m - 1).choose (q - 1)) * m := Nat.mul_le_mul_right m hub
      _ = (Vall \ Uf).card * (m * (m - 1).choose (q - 1)) := by ring
      _ = (Vall \ Uf).card * (q * m.choose q) := by
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · have hVU : (Vall \ Uf).card = 0 := by
              have : (Vall \ Uf).card ≤ Vall.card := Finset.card_le_card Finset.sdiff_subset
              rw [← hm] at this; omega
            rw [Finset.card_eq_zero.mp hVU]; simp
          · rw [choose_mul_eq m q hmpos hqpos]
      _ = (Vall \ Uf).card * q * m.choose q := by ring

open Finset in
/-- **Spans-a-pair bound** (the "sample contains an altered pair" event), cross-multiplied: the
number of `q`-samples spanning some pair of `D`, times `|Vall|·(|Vall|−1)`, is at most
`|D| · q·(q−1) · C(|Vall|, q)`. -/
private lemma spans_pair_nat {W : Type} [DecidableEq W] (Vall : Finset W) (D : Finset (Sym2 W))
    (q : ℕ) (hD : ∀ p ∈ D, ¬ p.IsDiag) (hDV : ∀ p ∈ D, p.toFinset ⊆ Vall) :
    ((Vall.powersetCard q).filter (fun S => ∃ p ∈ D, p.toFinset ⊆ S)).card
        * (Vall.card * (Vall.card - 1))
      ≤ D.card * (q * (q - 1)) * Vall.card.choose q := by
  classical
  set m := Vall.card with hm
  have hub : ((Vall.powersetCard q).filter (fun S => ∃ p ∈ D, p.toFinset ⊆ S)).card
      ≤ ∑ p ∈ D, ((Vall.powersetCard q).filter (fun S => p.toFinset ⊆ S)).card := by
    have hsub : (Vall.powersetCard q).filter (fun S => ∃ p ∈ D, p.toFinset ⊆ S)
        ⊆ D.biUnion (fun p => (Vall.powersetCard q).filter (fun S => p.toFinset ⊆ S)) := by
      intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hSpc, p, hpD, hpsub⟩ := hS
      rw [Finset.mem_biUnion]
      exact ⟨p, hpD, Finset.mem_filter.mpr ⟨hSpc, hpsub⟩⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have hY0 : ((Vall.powersetCard q).filter (fun S => ∃ p ∈ D, p.toFinset ⊆ S)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      rintro ⟨p, hpD, hpsub⟩
      have hpc : p.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag p (hD p hpD)
      have : p.toFinset.card ≤ S.card := Finset.card_le_card hpsub
      omega
    rw [hY0]; simp
  · have hsummand : ∀ p ∈ D,
        ((Vall.powersetCard q).filter (fun S => p.toFinset ⊆ S)).card = (m - 2).choose (q - 2) := by
      intro p hpD
      have hpc : p.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag p (hD p hpD)
      rw [superset_count_amb Vall p.toFinset q (hDV p hpD) (by rw [hpc]; omega), hpc, hm]
    rw [Finset.sum_congr rfl hsummand, Finset.sum_const, smul_eq_mul] at hub
    calc ((Vall.powersetCard q).filter (fun S => ∃ p ∈ D, p.toFinset ⊆ S)).card * (m * (m - 1))
        ≤ (D.card * (m - 2).choose (q - 2)) * (m * (m - 1)) := Nat.mul_le_mul_right _ hub
      _ = D.card * (m * (m - 1) * (m - 2).choose (q - 2)) := by ring
      _ = D.card * (q * (q - 1) * m.choose q) := by
          rcases Nat.lt_or_ge m 2 with hm2 | hm2
          · have hcz : m.choose q = 0 := Nat.choose_eq_zero_of_lt (by omega)
            have hlz : m * (m - 1) = 0 := by interval_cases m <;> rfl
            rw [hcz, hlz]; ring
          · rw [choose_mul_pair_eq m q hm2 hq2]
      _ = D.card * (q * (q - 1)) * m.choose q := by ring

open LabeledSubgraph in
/-- The non-root vertex count of a `σ'`-flag is `n₀`. -/
private lemma type_verts_toFinset_card {n₀ : ℕ} {σ' : FlagType (Fin n₀)} {V : Type} [Fintype V]
    [DecidableEq V] (LG : LabeledGraph σ' V) :
    LG.type_verts.toFinset.card = n₀ := by
  rw [Set.toFinset_card, LG.type_verts_card_eq]; simp [FlagType.size]

open LabeledSubgraph in
/-- A vertex set inducing a flag `≃f Hrep` (with `Hrep` on `Fin ℓ`) has cardinality `ℓ`. -/
private lemma induced_iso_card' {n₀ : ℕ} {σ' : FlagType (Fin n₀)} {V : Type} [Fintype V]
    [DecidableEq V] {ℓ : ℕ} (LG : LabeledGraph σ' V) (Hrep : LabeledGraph σ' (Fin ℓ)) (T : Finset V)
    (hroot : LG.type_verts ⊆ (↑T : Set V))
    (hiso : Nonempty ((inducedLabeledSubgraph LG (↑T) hroot).coe ≃f Hrep)) :
    T.card = ℓ := by
  obtain ⟨φ⟩ := hiso
  have hsz := labeledGraphIso_size_eq _ _ φ
  have hcoe : (inducedLabeledSubgraph LG (↑T) hroot).coe.size
      = (inducedLabeledSubgraph LG (↑T) hroot).size := rfl
  rw [hcoe, inducedLabeledSubgraph_size] at hsz
  simp only [LabeledGraph.size, Fintype.card_fin] at hsz
  rw [← hsz, ← Set.toFinset_card, Finset.toFinset_coe]

open Finset LabeledSubgraph in
/-- **Density as a pool `q`-subset count.**  If `ι : W → V` is injective on a pool `Pool ⊆ W` with
image the non-root vertices of `LG`, then the flag density of `Hrep` in `LG` equals the fraction of
size-`(ℓ−n₀)` subsets `S ⊆ Pool` whose `ι`-image together with the roots induces a copy of `Hrep`. -/
private lemma pool_count_bij {n₀ : ℕ} {σ' : FlagType (Fin n₀)} {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {ℓ : ℕ} (Hrep : LabeledGraph σ' (Fin ℓ)) (LG : LabeledGraph σ' V)
    (Pool : Finset W) (ι : W → V)
    (hinj : Set.InjOn ι Pool)
    (himg : Pool.image ι = LG.type_verts.toFinsetᶜ) :
    (Finset.univ.filter (fun T : Finset V =>
        ∃ (h : LG.type_verts ⊆ (↑T : Set V)),
          Nonempty ((inducedLabeledSubgraph LG (↑T) h).coe ≃f Hrep))).card
      = ((Pool.powersetCard (ℓ - n₀)).filter (fun S =>
          ∃ (h : LG.type_verts ⊆ (↑(S.image ι ∪ LG.type_verts.toFinset) : Set V)),
            Nonempty ((inducedLabeledSubgraph LG (↑(S.image ι ∪ LG.type_verts.toFinset)) h).coe ≃f Hrep))).card := by
  classical
  set R := LG.type_verts.toFinset with hR
  have hRcoe : (↑R : Set V) = LG.type_verts := Set.coe_toFinset _
  have hRcard : R.card = n₀ := type_verts_toFinset_card LG
  have hcompl : ∀ v : V, v ∉ R → ∃ w ∈ Pool, ι w = v := by
    intro v hv
    have : v ∈ Pool.image ι := by rw [himg, Finset.mem_compl]; exact hv
    rw [Finset.mem_image] at this; obtain ⟨w, hwP, hwv⟩ := this; exact ⟨w, hwP, hwv⟩
  have himg_mem : ∀ w ∈ Pool, ι w ∉ R := by
    intro w hw
    have : ι w ∈ Pool.image ι := Finset.mem_image_of_mem ι hw
    rw [himg, Finset.mem_compl] at this; exact this
  apply Finset.card_nbij'
    (i := fun T => Pool.filter (fun w => ι w ∈ T))
    (j := fun S => S.image ι ∪ R)
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hroots, hiso⟩ := hT
    have hRsubT : R ⊆ T := by
      rw [← Finset.coe_subset, hRcoe]; exact hroots
    have hTcard : T.card = ℓ := induced_iso_card' LG Hrep T hroots hiso
    set S := Pool.filter (fun w => ι w ∈ T) with hS
    have hSimg : S.image ι = T \ R := by
      ext v
      simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨w, ⟨hwP, hwT⟩, rfl⟩; exact ⟨hwT, himg_mem w hwP⟩
      · rintro ⟨hvT, hvR⟩; obtain ⟨w, hwP, rfl⟩ := hcompl v hvR; exact ⟨w, ⟨hwP, hvT⟩, rfl⟩
    have hScard : S.card = ℓ - n₀ := by
      have : (S.image ι).card = S.card := Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
      rw [← this, hSimg, Finset.card_sdiff_of_subset hRsubT, hTcard, hRcard]
    have hSunion : S.image ι ∪ R = T := by
      rw [hSimg, Finset.sdiff_union_of_subset hRsubT]
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.filter_subset _ _, hScard⟩, ?_⟩
    rw [hSunion]; exact ⟨hroots, hiso⟩
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    obtain ⟨_, hpred⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hroots, _⟩ := hT
    show (Pool.filter (fun w => ι w ∈ T)).image ι ∪ R = T
    have hRsubT : R ⊆ T := by rw [← Finset.coe_subset, hRcoe]; exact hroots
    have hSimg : (Pool.filter (fun w => ι w ∈ T)).image ι = T \ R := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨w, ⟨hwP, hwT⟩, rfl⟩; exact ⟨hwT, himg_mem w hwP⟩
      · rintro ⟨hvT, hvR⟩; obtain ⟨w, hwP, rfl⟩ := hcompl v hvR; exact ⟨w, ⟨hwP, hvT⟩, rfl⟩
    rw [hSimg, Finset.sdiff_union_of_subset hRsubT]
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    have hSP : S ⊆ Pool := by
      rcases hS with ⟨⟨hSP, _⟩, _⟩; exact hSP
    show Pool.filter (fun w => ι w ∈ S.image ι ∪ R) = S
    ext w
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hwP, hor⟩
      rcases hor with ⟨w', hw'S, hw'eq⟩ | hwR
      · have : w' = w := hinj (hSP hw'S) hwP hw'eq
        rwa [← this]
      · exact absurd hwR (himg_mem w hwP)
    · intro hwS
      exact ⟨hSP hwS, Or.inl ⟨w, hwS, rfl⟩⟩

open Finset LabeledSubgraph in
/-- **Density as a pool `q`-subset count** (ratio form). -/
private lemma flagDensity_eq_pool_count {n₀ : ℕ} {σ' : FlagType (Fin n₀)} {V W : Type} [Fintype V]
    [DecidableEq V] [Fintype W] [DecidableEq W] {ℓ : ℕ} (Hrep : LabeledGraph σ' (Fin ℓ))
    (LG : LabeledGraph σ' V) (Pool : Finset W) (ι : W → V)
    (hinj : Set.InjOn ι Pool)
    (himg : Pool.image ι = LG.type_verts.toFinsetᶜ) :
    flagDensity₁ (⟦Hrep⟧ : Flag σ' (Fin ℓ)) (⟦LG⟧ : Flag σ' V)
      = ((Pool.powersetCard (ℓ - n₀)).filter (fun S =>
          ∃ (h : LG.type_verts ⊆ (↑(S.image ι ∪ LG.type_verts.toFinset) : Set V)),
            Nonempty ((inducedLabeledSubgraph LG (↑(S.image ι ∪ LG.type_verts.toFinset)) h).coe ≃f Hrep))).card
        / ((Pool.card).choose (ℓ - n₀)) := by
  rw [flagDensity₁_eq_subset_count_div Hrep LG, pool_count_bij Hrep LG Pool ι hinj himg]
  have hden1 : LG.size - σ'.size = Pool.card := by
    rw [show LG.size = Fintype.card V from rfl]
    have hcard : Pool.card = (LG.type_verts.toFinsetᶜ).card := by
      rw [← himg, Finset.card_image_of_injOn hinj]
    rw [hcard, Finset.card_compl, type_verts_toFinset_card LG]
    simp only [FlagType.size, Fintype.card_fin]
  have hden2 : Hrep.size - σ'.size = ℓ - n₀ := by
    simp only [LabeledGraph.size, Fintype.card_fin, FlagType.size, Fintype.card_fin]
  rw [hden1, hden2]


open LabeledSubgraph in
/-- **The planted labelled graph** (`thm:sparse-repair-planting`): the repaired host graph `H` on
`U ⊕ (Fin n₀ × Fin L)`, labelled by `i ↦ Sum.inr (i, c i)` — one chosen representative `c i` per root
cluster `Rᵢ`.  Clause (i) of the repair (`hclI`) makes this a valid `σ`-labelling. -/
noncomputable def plantedLabeled {n L : ℕ} (G : LabeledGraph σ (Fin n))
    (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))) (c : Fin n₀ → Fin L)
    (hclI : ∀ (i j : Fin n₀), i ≠ j → ∀ (a b : Fin L),
        (H.Adj (Sum.inr (i, a)) (Sum.inr (j, b)) ↔ G.graph.Adj (G.type_embed i) (G.type_embed j))) :
    LabeledGraph σ (nonRoot G ⊕ (Fin n₀ × Fin L)) where
  graph := H
  type_embed := {
    toFun := fun i => Sum.inr (i, c i)
    inj' := by intro i j h; simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact h.1
    map_rel_iff' := by
      intro i j
      simp only [Function.Embedding.coeFn_mk]
      by_cases hij : i = j
      · subst hij
        constructor
        · intro hadj; exact absurd hadj (H.loopless _)
        · intro hadj; exact absurd hadj (σ.loopless _)
      · rw [hclI i j hij (c i) (c j), ← type_embed_Adj_iff G i j]
  }

/-- The planted labelling sends root `i` to its cluster representative `Sum.inr (i, c i)`. -/
@[simp] lemma plantedLabeled_type_embed {n L : ℕ} (G : LabeledGraph σ (Fin n))
    (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))) (c : Fin n₀ → Fin L) (hclI) (i : Fin n₀) :
    (plantedLabeled G H c hclI).type_embed i = Sum.inr (i, c i) := rfl

/-- The planted labelled graph carries the repaired host graph `H`. -/
@[simp] lemma plantedLabeled_graph {n L : ℕ} (G : LabeledGraph σ (Fin n))
    (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))) (c : Fin n₀ → Fin L) (hclI) :
    (plantedLabeled G H c hclI).graph = H := rfl

/-- Collapses the planted vertex set `U ⊕ (Fin n₀ × Fin L)` onto `Fin n`: a non-root vertex maps to
itself and a cluster vertex `(i, a)` to the labelled root `G.type_embed i`. -/
def iotaG {n L : ℕ} (G : LabeledGraph σ (Fin n)) : (nonRoot G ⊕ (Fin n₀ × Fin L)) → Fin n :=
  Sum.elim Subtype.val (fun p => G.type_embed p.1)

open LabeledSubgraph in
private lemma adj_match {n L : ℕ} (G : LabeledGraph σ (Fin n))
    (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))) (c : Fin n₀ → Fin L)
    (Dalt : Finset (Sym2 (nonRoot G)))
    (hDalt : Dalt = Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
        ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => H.Adj (Sum.inl u) (Sum.inl u')
              ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p))
    (hclI : ∀ (i j : Fin n₀), i ≠ j → ∀ (a b : Fin L),
        (H.Adj (Sum.inr (i, a)) (Sum.inr (j, b)) ↔ G.graph.Adj (G.type_embed i) (G.type_embed j)))
    (hclII : ∀ (i : Fin n₀) (a : Fin L) (u : nonRoot G),
        (H.Adj (Sum.inr (i, a)) (Sum.inl u) ↔ G.graph.Adj (G.type_embed i) u.1))
    (a b : nonRoot G ⊕ (Fin n₀ × Fin L))
    (ha : (∃ u, a = Sum.inl u) ∨ (∃ i, a = Sum.inr (i, c i)))
    (hb : (∃ u, b = Sum.inl u) ∨ (∃ i, b = Sum.inr (i, c i)))
    (hgoodpair : ∀ u u', a = Sum.inl u → b = Sum.inl u' → s(u, u') ∉ Dalt) :
    (H.Adj a b ↔ G.graph.Adj (iotaG G a) (iotaG G b)) := by
  rcases ha with ⟨u, rfl⟩ | ⟨i, rfl⟩ <;> rcases hb with ⟨u', rfl⟩ | ⟨j, rfl⟩
  · simp only [iotaG, Sum.elim_inl]
    by_cases huu : u = u'
    · subst huu
      constructor
      · intro hadj; exact absurd hadj (H.loopless _)
      · intro hadj; exact absurd hadj (G.graph.loopless _)
    · have hnotD : s(u, u') ∉ Dalt := hgoodpair u u' rfl rfl
      rw [hDalt] at hnotD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hnotD
      have hdiag : ¬ (s(u, u') : Sym2 (nonRoot G)).IsDiag := by
        simp only [Sym2.isDiag_iff_proj_eq]; exact huu
      have hmatch := hnotD hdiag
      simp only [Sym2.lift_mk] at hmatch
      rw [not_not] at hmatch
      rw [hmatch]
  · simp only [iotaG, Sum.elim_inl, Sum.elim_inr]
    rw [adj_comm, hclII j (c j) u, adj_comm]
  · simp only [iotaG, Sum.elim_inl, Sum.elim_inr]
    rw [hclII i (c i) u']
  · simp only [iotaG, Sum.elim_inr]
    by_cases hij : i = j
    · subst hij
      constructor
      · intro hadj; exact absurd hadj (H.loopless _)
      · intro hadj; exact absurd hadj (G.graph.loopless _)
    · exact hclI i j hij (c i) (c j)

-- characterize membership in the H-roots finset and G-roots finset
open LabeledSubgraph in
private lemma planted_type_verts_toFinset {n L : ℕ} (G : LabeledGraph σ (Fin n))
    (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))) (c : Fin n₀ → Fin L) (hclI) :
    (plantedLabeled G H c hclI).type_verts.toFinset
      = Finset.univ.image (fun i : Fin n₀ => (Sum.inr (i, c i) : nonRoot G ⊕ (Fin n₀ × Fin L))) := by
  ext a
  simp only [Set.mem_toFinset, LabeledGraph.mem_type_verts, Finset.mem_image, Finset.mem_univ,
    true_and, plantedLabeled_type_embed]

open LabeledSubgraph in
private lemma G_type_verts_toFinset {n : ℕ} (G : LabeledGraph σ (Fin n)) :
    G.type_verts.toFinset = Finset.univ.image (fun i : Fin n₀ => G.type_embed i) := by
  ext v
  simp only [Set.mem_toFinset, LabeledGraph.mem_type_verts, Finset.mem_image, Finset.mem_univ,
    true_and]

-- Membership facts for SH and SG, used to build the bijection.
open LabeledSubgraph in
private noncomputable def induced_iso_match {n L : ℕ} (G : LabeledGraph σ (Fin n))
    (H : SimpleGraph (nonRoot G ⊕ (Fin n₀ × Fin L))) (c : Fin n₀ → Fin L)
    (Dalt : Finset (Sym2 (nonRoot G)))
    (hDalt : Dalt = Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
        ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => H.Adj (Sum.inl u) (Sum.inl u')
              ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p))
    (hclI : ∀ (i j : Fin n₀), i ≠ j → ∀ (a b : Fin L),
        (H.Adj (Sum.inr (i, a)) (Sum.inr (j, b)) ↔ G.graph.Adj (G.type_embed i) (G.type_embed j)))
    (hclII : ∀ (i : Fin n₀) (a : Fin L) (u : nonRoot G),
        (H.Adj (Sum.inr (i, a)) (Sum.inl u) ↔ G.graph.Adj (G.type_embed i) u.1))
    (S : Finset (nonRoot G ⊕ (Fin n₀ × Fin L)))
    (hSinl : ∀ x ∈ S, ∃ u, x = Sum.inl u)
    (hSgood : ∀ u u', Sum.inl u ∈ S → Sum.inl u' ∈ S → s(u, u') ∉ Dalt)
    (SH : Set (nonRoot G ⊕ (Fin n₀ × Fin L)))
    (hSH : SH = ↑(S ∪ (plantedLabeled G H c hclI).type_verts.toFinset))
    (hrootH : (plantedLabeled G H c hclI).type_verts ⊆ SH)
    (SG : Set (Fin n))
    (hSG : SG = ↑(S.image (iotaG G) ∪ G.type_verts.toFinset))
    (hrootG : G.type_verts ⊆ SG) :
    (inducedLabeledSubgraph (plantedLabeled G H c hclI) SH hrootH).coe
      ≃f (inducedLabeledSubgraph G SG hrootG).coe := by
  set LH := plantedLabeled G H c hclI with hLH
  -- membership characterizations
  have hmemSH : ∀ a, a ∈ SH ↔ (a ∈ S ∨ ∃ i, a = Sum.inr (i, c i)) := by
    intro a
    rw [hSH, Finset.mem_coe, Finset.mem_union, planted_type_verts_toFinset]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]
  have hmemSG : ∀ v, v ∈ SG ↔ ((∃ x ∈ S, iotaG G x = v) ∨ ∃ i, v = G.type_embed i) := by
    intro v
    rw [hSG, Finset.mem_coe, Finset.mem_union, Finset.mem_image, G_type_verts_toFinset]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]
  -- each a ∈ SH is inl-or-root
  have hcase : ∀ a ∈ SH, (∃ u, a = Sum.inl u) ∨ (∃ i, a = Sum.inr (i, c i)) := by
    intro a ha
    rcases (hmemSH a).mp ha with hS | hr
    · exact Or.inl (hSinl a hS)
    · exact Or.inr hr
  -- ιG maps SH into SG
  have hmaps : ∀ a ∈ SH, iotaG G a ∈ SG := by
    intro a ha
    rw [hmemSG]
    rcases (hmemSH a).mp ha with hS | ⟨i, rfl⟩
    · exact Or.inl ⟨a, hS, rfl⟩
    · right; exact ⟨i, by simp [iotaG]⟩
  -- the forward map on subtypes
  let f : ↑SH → ↑SG := fun a => ⟨iotaG G a.1, hmaps a.1 a.2⟩
  -- injective on SH
  have hinj : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hfab
    simp only [f, Subtype.mk.injEq] at hfab
    -- iotaG G a = iotaG G b
    apply Subtype.ext
    rcases hcase a ha with ⟨ua, rfl⟩ | ⟨ia, rfl⟩ <;> rcases hcase b hb with ⟨ub, rfl⟩ | ⟨ib, rfl⟩
    · simp only [iotaG, Sum.elim_inl] at hfab
      exact congrArg Sum.inl (Subtype.ext hfab)
    · exfalso; simp only [iotaG, Sum.elim_inl, Sum.elim_inr] at hfab
      exact ua.2 ⟨ib, hfab.symm⟩
    · exfalso; simp only [iotaG, Sum.elim_inl, Sum.elim_inr] at hfab
      exact ub.2 ⟨ia, hfab⟩
    · simp only [iotaG, Sum.elim_inr] at hfab
      have hiaib : ia = ib := G.type_embed.injective hfab
      subst hiaib; rfl
  -- surjective onto SG
  have hsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rcases (hmemSG v).mp hv with ⟨x, hxS, hxv⟩ | ⟨i, rfl⟩
    · refine ⟨⟨x, (hmemSH x).mpr (Or.inl hxS)⟩, ?_⟩
      simp only [f, Subtype.mk.injEq]; exact hxv
    · refine ⟨⟨Sum.inr (i, c i), (hmemSH _).mpr (Or.inr ⟨i, rfl⟩)⟩, ?_⟩
      simp only [f, iotaG, Sum.elim_inr]
  let e : ↑SH ≃ ↑SG := Equiv.ofBijective f ⟨hinj, hsurj⟩
  -- the graph iso
  refine ⟨⟨e, ?_⟩, ?_⟩
  · -- adjacency
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    show (inducedLabeledSubgraph G SG hrootG).coe.graph.Adj (e ⟨a, ha⟩) (e ⟨b, hb⟩)
        ↔ (inducedLabeledSubgraph LH SH hrootH).coe.graph.Adj ⟨a, ha⟩ ⟨b, hb⟩
    rw [LabeledSubgraph.coe_adj_iff, LabeledSubgraph.coe_adj_iff]
    simp only [inducedLabeledSubgraph, SimpleGraph.Subgraph.induce, e, Equiv.ofBijective_apply, f]
    -- reduce to H.Adj a b ↔ G.Adj (ιG a) (ιG b)
    have hH : LH.graph.Adj a b ↔ G.graph.Adj (iotaG G a) (iotaG G b) := by
      rw [plantedLabeled_graph]
      apply adj_match G H c Dalt hDalt hclI hclII a b (hcase a ha) (hcase b hb)
      intro u u' hau hbu'
      apply hSgood u u'
      · rw [← hau]; rcases (hmemSH a).mp ha with h | ⟨i, hi⟩
        · exact h
        · rw [hi] at hau; exact absurd hau (by simp)
      · rw [← hbu']; rcases (hmemSH b).mp hb with h | ⟨i, hi⟩
        · exact h
        · rw [hi] at hbu'; exact absurd hbu' (by simp)
    constructor
    · rintro ⟨_, _, hadj⟩; exact ⟨ha, hb, hH.mpr hadj⟩
    · rintro ⟨_, _, hadj⟩; exact ⟨hmaps a ha, hmaps b hb, hH.mp hadj⟩
  · -- type_preserve
    funext t
    apply Subtype.ext
    show iotaG G (LH.type_embed t) = G.type_embed t
    rw [hLH, plantedLabeled_type_embed]
    rfl

private lemma meets_ratio_le (X CW Vc Vsub qn : ℕ)
    (hnat : X * Vc ≤ Vsub * qn * CW)
    (nv lam m n₀ : ℝ)
    (hVcpos : 0 < (Vc:ℝ)) (hVc_ge : nv ≤ (Vc:ℝ)) (hnvpos : 0 < nv)
    (hVsub : (Vsub:ℝ) ≤ n₀ * lam * (2 * nv)) (hqm : (qn:ℝ) ≤ m)
    (hlam0 : 0 ≤ lam) (hm0 : 0 ≤ m) (hn₀0 : 0 ≤ n₀) :
    (X:ℝ) / (CW:ℝ) ≤ 2 * m * n₀ * lam := by
  have hr : (X:ℝ)/(CW:ℝ) ≤ ((Vsub * qn : ℕ):ℝ)/(Vc:ℝ) := by
    rcases Nat.eq_zero_or_pos CW with hCW0 | hCWp
    · subst hCW0; simp; positivity
    · have hCWR : (0:ℝ) < CW := by exact_mod_cast hCWp
      rw [div_le_div_iff₀ hCWR hVcpos]
      have : (X:ℝ) * Vc ≤ ((Vsub*qn:ℕ):ℝ) * CW := by exact_mod_cast hnat
      linarith
  refine le_trans hr ?_
  rw [div_le_iff₀ hVcpos]
  push_cast
  have h1 : (Vsub:ℝ) * qn ≤ (n₀ * lam * (2 * nv)) * m :=
    mul_le_mul hVsub hqm (by positivity) (by positivity)
  have h2 : (n₀ * lam * (2 * nv)) * m ≤ 2 * m * n₀ * lam * Vc := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hn₀0 hlam0) hm0) (le_of_lt hVcpos), hVc_ge, hlam0]
  linarith

private lemma spans_ratio_le (Y CW Vc Dc qn : ℕ)
    (hnat : Y * (Vc * (Vc - 1)) ≤ Dc * (qn * (qn - 1)) * CW)
    (nv _lam m ρ : ℝ)
    (hVc_ge : nv/2 ≤ (Vc:ℝ)) (hnvpos : 0 < nv)
    (hq2 : 2 ≤ qn) (hqVc : qn ≤ Vc) (hqm : (qn:ℝ) ≤ m)
    (hDc : (Dc:ℝ) ≤ ρ * nv^2)
    (hρ0 : 0 ≤ ρ) (hm0 : 0 ≤ m) :
    (Y:ℝ) / (CW:ℝ) ≤ 4 * m^2 * ρ := by
  have hVc2 : 2 ≤ Vc := le_trans hq2 hqVc
  have hVcR2 : (2:ℝ) ≤ Vc := by exact_mod_cast hVc2
  have hdenpos : (0:ℝ) < (Vc:ℝ) * ((Vc:ℝ) - 1) := by nlinarith
  have hr : (Y:ℝ)/(CW:ℝ) ≤ ((Dc*(qn*(qn-1)):ℕ):ℝ)/((Vc:ℝ)*((Vc:ℝ)-1)) := by
    rcases Nat.eq_zero_or_pos CW with hCW0 | hCWp
    · subst hCW0; simp; positivity
    · have hCWR : (0:ℝ) < CW := by exact_mod_cast hCWp
      rw [div_le_div_iff₀ hCWR hdenpos]
      have heq : ((Vc:ℝ)*((Vc:ℝ)-1)) = ((Vc*(Vc-1):ℕ):ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      rw [heq]
      have : (Y:ℝ) * ((Vc*(Vc-1):ℕ):ℝ) ≤ ((Dc*(qn*(qn-1)):ℕ):ℝ) * CW := by exact_mod_cast hnat
      linarith
  refine le_trans hr ?_
  rw [div_le_iff₀ hdenpos]
  -- Dc*(q(q-1)) ≤ (4 m^2 ρ)·(Vc(Vc-1))
  set qr : ℝ := (qn:ℝ) with hqr
  have hqcast : ((Dc*(qn*(qn-1)):ℕ):ℝ) = (Dc:ℝ) * (qr * (qr - 1)) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hqcast]
  -- key: nv^2 * (q(q-1)) ≤ 4 m^2 * (Vc(Vc-1))
  have hqr2 : (2:ℝ) ≤ qr := by rw [hqr]; exact_mod_cast hq2
  have hqrVc : qr ≤ Vc := by rw [hqr]; exact_mod_cast hqVc
  have hqrm : qr ≤ m := by rw [hqr]; exact hqm
  have hnvVc : nv ≤ 2 * Vc := by linarith [hVc_ge]
  have hVcpos : 0 < (Vc:ℝ) := by linarith
  have hkey : nv^2 * (qr * (qr - 1)) ≤ 4 * m^2 * ((Vc:ℝ) * ((Vc:ℝ) - 1)) := by
    have hstep1 : qr*(qr-1)*Vc ≤ qr^2*((Vc:ℝ)-1) := by nlinarith [hqrVc, hqr2]
    have hnv2 : nv^2 ≤ 4 * (Vc:ℝ)^2 := by nlinarith [hnvVc, hnvpos.le, hVcpos.le]
    have hq2sq : qr^2 ≤ m^2 := by nlinarith [hqrm, hqr2, hm0]
    have hnvq : nv^2 * qr^2 ≤ 4 * m^2 * (Vc:ℝ)^2 := by
      calc nv^2 * qr^2 ≤ (4*(Vc:ℝ)^2) * m^2 :=
            mul_le_mul hnv2 hq2sq (by positivity) (by positivity)
        _ = 4 * m^2 * (Vc:ℝ)^2 := by ring
    have hVc1 : (0:ℝ) ≤ (Vc:ℝ) - 1 := by linarith
    have hchain : nv^2 * (qr*(qr-1)) * Vc ≤ 4 * m^2 * (Vc:ℝ)^2 * ((Vc:ℝ)-1) := by
      calc nv^2 * (qr*(qr-1)) * Vc = nv^2 * (qr*(qr-1)*Vc) := by ring
        _ ≤ nv^2 * (qr^2*((Vc:ℝ)-1)) := by apply mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = (nv^2*qr^2) * ((Vc:ℝ)-1) := by ring
        _ ≤ (4*m^2*(Vc:ℝ)^2) * ((Vc:ℝ)-1) := by apply mul_le_mul_of_nonneg_right hnvq hVc1
        _ = 4*m^2*(Vc:ℝ)^2*((Vc:ℝ)-1) := by ring
    have hfin : nv^2 * (qr*(qr-1)) ≤ 4 * m^2 * (Vc:ℝ) * ((Vc:ℝ)-1) := by
      rw [show 4*m^2*(Vc:ℝ)^2*((Vc:ℝ)-1) = (4*m^2*(Vc:ℝ)*((Vc:ℝ)-1))*Vc by ring] at hchain
      exact le_of_mul_le_mul_right hchain hVcpos
    nlinarith [hfin]
  -- now Dc*(q(q-1)) ≤ ρ nv^2 (q(q-1)) ≤ ρ · 4 m^2 (Vc(Vc-1))  → reorganize to 4 m^2 ρ (Vc(Vc-1))
  have hqq0 : (0:ℝ) ≤ qr * (qr - 1) := by nlinarith [hqr2]
  have h1 : (Dc:ℝ) * (qr*(qr-1)) ≤ (ρ * nv^2) * (qr*(qr-1)) :=
    mul_le_mul_of_nonneg_right hDc hqq0
  have h2 : (ρ * nv^2) * (qr*(qr-1)) = ρ * (nv^2 * (qr*(qr-1))) := by ring
  have h3 : ρ * (nv^2 * (qr*(qr-1))) ≤ ρ * (4 * m^2 * ((Vc:ℝ) * ((Vc:ℝ) - 1))) :=
    mul_le_mul_of_nonneg_left hkey hρ0
  have h4 : ρ * (4 * m^2 * ((Vc:ℝ) * ((Vc:ℝ) - 1))) = 4 * m^2 * ρ * ((Vc:ℝ) * ((Vc:ℝ) - 1)) := by ring
  linarith [h1, h3]

private lemma final_lt (a b XC YC ε Cm lam ρ m n₀ : ℝ)
    (hb : |a - b| ≤ 2 * XC + YC)
    (hX : XC ≤ 2 * m * n₀ * lam) (hY : YC ≤ 4 * m^2 * ρ)
    (hCm : Cm = 4 * m^2) (hn₀m : n₀ ≤ m) (hlam0 : 0 ≤ lam)
    (hm0 : 0 ≤ m) (_hρ0 : 0 ≤ ρ)
    (hconst : Cm * lam + Cm * ρ < ε) : |a - b| < ε := by
  have hmeets : 2 * (2 * m * n₀ * lam) ≤ Cm * lam := by
    rw [hCm]
    have hprod : 0 ≤ m * lam * (m - n₀) := by
      apply mul_nonneg (mul_nonneg hm0 hlam0); linarith
    nlinarith [hprod]
  have hspans : 4 * m^2 * ρ = Cm * ρ := by rw [hCm]
  have hsum : 2 * XC + YC ≤ Cm * lam + Cm * ρ := by
    have h2X : 2 * XC ≤ 2 * (2 * m * n₀ * lam) := by linarith [hX]
    linarith [h2X, hmeets, hY, hspans]
  linarith [hb, hsum, hconst]

set_option maxHeartbeats 1000000 in
open LabeledSubgraph Finset in
/-- **Sparse root repairs imply finite planting** (`thm:sparse-repair-planting`).  If the hereditary
class `hc` has sparse root-blow-up repairs at the non-degenerate type `σ`, then it has the finite
planting property at `σ` (hence, by `finitePlanting_root_plantable`, is root-plantable at `σ`). -/
theorem sparseRootRepair_finitePlanting (hc : HeredClass) (σ : FlagType (Fin n₀))
    (hsr : SparseRootRepair hc σ) : FinitePlanting hc σ := by
  obtain ⟨hk1, hsr'⟩ := hsr
  intro m ε hmn₀ hε
  -- Fix constants from `m, ε`.
  set Cm : ℝ := 4 * (m : ℝ) ^ 2 with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set ρ : ℝ := ε / (2 * Cm + 1) with hρ
  have hdenrho : (0:ℝ) < 2 * Cm + 1 := by positivity
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  set lam : ℝ := min 1 (ε / (4 * Cm + 1)) with hlam
  have hdenlam : (0:ℝ) < 4 * Cm + 1 := by positivity
  have hlampos : 0 < lam := by rw [hlam]; exact lt_min (by norm_num) (by positivity)
  have hlamle1 : lam ≤ 1 := min_le_left _ _
  -- The key constant inequality `Cm·lam + Cm·ρ < ε`.
  have hconst : Cm * lam + Cm * ρ < ε := by
    have h1 : lam ≤ ε / (4 * Cm + 1) := min_le_right _ _
    have hClam : Cm * lam ≤ ε / 4 := by
      have hb : Cm * lam ≤ Cm * (ε / (4 * Cm + 1)) := mul_le_mul_of_nonneg_left h1 hCm0
      have hb2 : Cm * (ε / (4 * Cm + 1)) ≤ ε / 4 := by
        rw [show Cm * (ε / (4 * Cm + 1)) = (Cm * ε) / (4 * Cm + 1) by rw [mul_div_assoc]]
        rw [div_le_div_iff₀ hdenlam (by norm_num)]
        nlinarith [mul_nonneg hCm0 hε.le]
      linarith
    have hCρ : Cm * ρ ≤ ε / 2 := by
      rw [hρ, show Cm * (ε / (2 * Cm + 1)) = (Cm * ε) / (2 * Cm + 1) by rw [mul_div_assoc]]
      rw [div_le_div_iff₀ hdenrho (by norm_num)]
      nlinarith [mul_nonneg hCm0 hε.le]
    linarith
  -- The density `δ`.
  set δ : ℝ := (lam / (2 * (1 + (n₀ : ℝ) * lam))) ^ n₀ with hδ
  have hden_lam : (0:ℝ) < 2 * (1 + (n₀ : ℝ) * lam) := by
    have : (0:ℝ) ≤ (n₀ : ℝ) * lam := mul_nonneg (by positivity) hlampos.le
    linarith
  have hδpos : 0 < δ := by
    rw [hδ]; exact pow_pos (div_pos hlampos hden_lam) n₀
  -- The repair threshold.
  obtain ⟨n_0, hrep⟩ := hsr' lam ρ hlampos hlamle1 hρpos
  -- The planting threshold `n₁`.
  set n₁ : ℕ := max m (max (2 * n₀) (max ⌈(2:ℝ) / lam⌉₊ n_0)) with hn₁
  refine ⟨n₁, δ, le_max_left _ _, hδpos, ?_⟩
  intro n G hGmem hn₁n
  -- Threshold consequences.
  have hn_m : m ≤ n := le_trans (le_max_left _ _) hn₁n
  have hn_2n₀ : 2 * n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn₁n
  have hn_ceil : ⌈(2:ℝ) / lam⌉₊ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn₁n
  have hn_n0 : n_0 ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn₁n
  have hn₀1 : 1 ≤ n₀ := hk1
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn_2n₀
  -- `n ≥ 2/lam`, hence `lam * n / 2 ≥ 1`.
  have hlamn : (1:ℝ) ≤ lam * n / 2 := by
    have h2lam : (2:ℝ) / lam ≤ n := by
      calc (2:ℝ) / lam ≤ ⌈(2:ℝ) / lam⌉₊ := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn_ceil
    rw [div_le_iff₀ hlampos] at h2lam
    rw [le_div_iff₀ (by norm_num)]
    linarith
  -- The repair output.
  obtain ⟨L, H, hLlb, hLub, hHmem, hclI, hclII, hclIII⟩ := hrep n G hGmem hn_n0
  -- `L ≥ 1`.
  have hLpos : 1 ≤ L := by
    have : (1:ℝ) ≤ (L:ℝ) := le_trans hlamn hLlb
    exact_mod_cast this
  -- The host vertex type and its presentation on `Fin N`.
  have hnonRoot_card : Fintype.card (nonRoot G) = n - n₀ := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin]
    congr 1
    rw [← Set.toFinset_card, Set.toFinset_range,
      Finset.card_image_of_injective _ G.type_embed.injective, Finset.card_univ, Fintype.card_fin]
  set N : ℕ := Fintype.card (nonRoot G ⊕ (Fin n₀ × Fin L)) with hN
  have hNval : N = (n - n₀) + n₀ * L := by
    rw [hN, Fintype.card_sum, hnonRoot_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  set e : (nonRoot G ⊕ (Fin n₀ × Fin L)) ≃ Fin N := Fintype.equivFin _ with he
  set Hfin : SimpleGraph (Fin N) := SimpleGraph.map e.toEmbedding H with hHfin
  set eiso : H ≃g Hfin := SimpleGraph.Iso.map e H with heiso
  -- `Hfin ∈ hc`.
  have hHfinMem : hc.Mem Hfin := hc.comap eiso.symm.toEmbedding hHmem
  -- `n ≤ N`.
  have hnN : n ≤ N := by
    rw [hNval]
    have : n₀ ≤ n₀ * L := by nlinarith [hLpos]
    omega
  -- The planted labelled graph and the transported embedding for each choice `c`.
  set LHc : (Fin n₀ → Fin L) → LabeledGraph σ (nonRoot G ⊕ (Fin n₀ × Fin L)) :=
    fun c => plantedLabeled G H c hclI with hLHc
  set Lθ : (Fin n₀ → Fin L) → LabeledGraph σ (Fin N) :=
    fun c => transportLabeled (G := LHc c) eiso with hLθ
  set θ_of : (Fin n₀ → Fin L) → (σ ↪g Hfin) := fun c => (Lθ c).type_embed with hθof
  -- `Θ`, the set of planted embeddings.
  set Θ : Finset (σ ↪g Hfin) := Finset.univ.image θ_of with hΘ
  refine ⟨N, Hfin, Θ, hHfinMem, hnN, ?_, ?_⟩
  · -- clause (ii): `δ · N^{n₀} ≤ |Θ|`
    -- the embedding sends `i ↦ e (Sum.inr (i, c i))`.
    have hθ_app : ∀ (c : Fin n₀ → Fin L) (i : Fin n₀), θ_of c i = e (Sum.inr (i, c i)) := by
      intro c i
      show (Lθ c).type_embed i = e (Sum.inr (i, c i))
      rw [hLθ]
      show (transportLabeled (G := LHc c) eiso).type_embed i = e (Sum.inr (i, c i))
      simp only [transportLabeled, SimpleGraph.Embedding.coe_comp,
        Function.comp_apply, SimpleGraph.Iso.toEmbedding, RelIso.coe_toRelEmbedding]
      show eiso ((plantedLabeled G H c hclI).type_embed i) = e (Sum.inr (i, c i))
      rw [plantedLabeled_type_embed]
      rw [heiso, SimpleGraph.Iso.map_apply]
    -- `θ_of` is injective.
    have hθ_inj : Function.Injective θ_of := by
      intro c c' hcc'
      funext i
      have := congrFun (congrArg (fun (em : σ ↪g Hfin) => (em : Fin n₀ → Fin N)) hcc') i
      simp only [hθ_app] at this
      have h2 := e.injective this
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h2
      exact h2.2
    -- `|Θ| = L ^ n₀`.
    have hΘcard : Θ.card = L ^ n₀ := by
      rw [hΘ, Finset.card_image_of_injective _ hθ_inj, Finset.card_univ]
      simp only [Fintype.card_fun, Fintype.card_fin]
    rw [hΘcard]
    -- `δ · N^{n₀} ≤ L^{n₀}` from `L ≥ lam n / 2` and `N ≤ (1 + n₀ lam) n`.
    have hNbound : (N : ℝ) ≤ (1 + (n₀ : ℝ) * lam) * n := by
      rw [hNval]
      have hnn₀ : ((n - n₀ : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n - n₀ : ℕ) ≤ n := Nat.sub_le _ _
        exact_mod_cast this
      have hcl : ((n₀ * L : ℕ) : ℝ) ≤ (n₀ : ℝ) * lam * n := by
        push_cast
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hLub
      push_cast at hnn₀ hcl ⊢
      nlinarith [hnn₀, hcl]
    have hLbound : lam * n / 2 ≤ (L : ℝ) := hLlb
    -- δ · N^{n₀} ≤ (lam/(2(1+n₀ lam)))^{n₀} · ((1+n₀ lam) n)^{n₀} = (lam n / 2)^{n₀} ≤ L^{n₀}
    have hNpos : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hbase_le : δ * (N : ℝ) ^ n₀ ≤ (lam * n / 2) ^ n₀ := by
      rw [hδ]
      have hfac : (lam / (2 * (1 + (n₀:ℝ) * lam))) ^ n₀ * (N : ℝ) ^ n₀
          = (lam / (2 * (1 + (n₀:ℝ) * lam)) * N) ^ n₀ := by rw [← mul_pow]
      rw [hfac]
      apply pow_le_pow_left₀
      · positivity
      · rw [div_mul_eq_mul_div, div_le_iff₀ hden_lam]
        have hfactor : (0:ℝ) ≤ lam := hlampos.le
        calc lam * (N : ℝ) ≤ lam * ((1 + (n₀:ℝ) * lam) * n) :=
              mul_le_mul_of_nonneg_left hNbound hfactor
          _ = lam * n / 2 * (2 * (1 + (n₀:ℝ) * lam)) := by ring
    have hLpow : (lam * n / 2) ^ n₀ ≤ (L : ℝ) ^ n₀ :=
      pow_le_pow_left₀ (by linarith [hlamn]) hLbound n₀
    calc δ * (N : ℝ) ^ n₀ ≤ (lam * n / 2) ^ n₀ := hbase_le
      _ ≤ (L : ℝ) ^ n₀ := hLpow
      _ = ((L ^ n₀ : ℕ) : ℝ) := by push_cast; ring
  · -- clause (iii): the density bound
    intro θ' hθ'mem F hFm
    -- `θ' = θ_of c` for some `c`.
    rw [hΘ, Finset.mem_image] at hθ'mem
    obtain ⟨c, _, hceq⟩ := hθ'mem
    subst hceq
    -- Reduce the `Hfin`-density to the `LHc c`-density via the transport iso.
    have hisoF : LHc c ≃f (⟨Hfin, θ_of c⟩ : LabeledGraph σ (Fin N)) := by
      have h := transportLabeled_iso (G := LHc c) eiso
      exact h
    have hpH : flagDensity₁ F.2 (⟦(⟨Hfin, θ_of c⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N))
        = flagDensity₁ F.2 (⟦LHc c⟧ : Flag σ (nonRoot G ⊕ (Fin n₀ × Fin L))) :=
      (flagDensity₁_respect_eqv F hisoF).symm
    rw [hpH]
    -- The flag representative.
    set Frep : LabeledGraph σ (Fin F.1) := F.2.out with hFrep
    have hFrep_eq : (⟦Frep⟧ : Flag σ (Fin F.1)) = F.2 := Quotient.out_eq F.2
    set q : ℕ := F.1 - n₀ with hq
    -- The sampling pool `Vall` (non-roots of `LHc c`) and the "good" subpool `Uf` (the `inl` part).
    set Vall : Finset (nonRoot G ⊕ (Fin n₀ × Fin L)) := (LHc c).type_verts.toFinsetᶜ with hVall
    set Uf : Finset (nonRoot G ⊕ (Fin n₀ × Fin L)) :=
      Finset.univ.image (Sum.inl : nonRoot G → nonRoot G ⊕ (Fin n₀ × Fin L)) with hUf
    -- `Uf ⊆ Vall`.
    have hUfV : Uf ⊆ Vall := by
      intro x hx
      rw [hUf, Finset.mem_image] at hx
      obtain ⟨u, _, rfl⟩ := hx
      rw [hVall, Finset.mem_compl, Set.mem_toFinset, LabeledGraph.mem_type_verts]
      rintro ⟨i, hi⟩
      rw [hLHc, plantedLabeled_type_embed] at hi
      exact absurd hi (by simp)
    -- `himg`/`hinj` for the H pool count (`ι = id`).
    have himgH : Vall.image id = (LHc c).type_verts.toFinsetᶜ := by
      rw [Finset.image_id]
    have hinjH : Set.InjOn id (Vall : Set (nonRoot G ⊕ (Fin n₀ × Fin L))) :=
      Function.injective_id.injOn
    -- `himg`/`hinj` for the G pool count (`ι = iotaG G`).
    have hinjG : Set.InjOn (iotaG G) (Uf : Set (nonRoot G ⊕ (Fin n₀ × Fin L))) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, hUf, Finset.mem_image] at hx hy
      obtain ⟨u, _, rfl⟩ := hx
      obtain ⟨v, _, rfl⟩ := hy
      simp only [iotaG, Sum.elim_inl] at hxy
      rw [Subtype.ext hxy]
    have himgG : Uf.image (iotaG G) = G.type_verts.toFinsetᶜ := by
      ext w
      rw [hUf, Finset.mem_compl, Set.mem_toFinset, LabeledGraph.mem_type_verts, Finset.mem_image]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        rintro ⟨i, hi⟩
        simp only [iotaG, Sum.elim_inl] at hi
        exact u.2 ⟨i, hi⟩
      · intro hw
        refine ⟨Sum.inl ⟨w, fun ⟨i, hi⟩ => hw ⟨i, hi⟩⟩, ⟨⟨w, _⟩, rfl⟩, rfl⟩
    -- Rewrite both densities via the pool-count bridge.
    rw [← hFrep_eq]
    rw [flagDensity_eq_pool_count Frep (LHc c) Vall id hinjH himgH,
        flagDensity_eq_pool_count Frep G Uf (iotaG G) hinjG himgG]
    -- Pool cardinalities.
    have hVcard : Vall.card = N - n₀ := by
      rw [hVall, Finset.card_compl, type_verts_toFinset_card (LHc c)]
    have hUcard : Uf.card = n - n₀ := by
      rw [hUf, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, hnonRoot_card]
    -- Push the rational casts inside the divisions, and convert the choose-denominators.
    simp only [Rat.cast_div, Rat.cast_natCast]
    rw [← Finset.card_powersetCard q Vall, ← Finset.card_powersetCard q Uf]
    -- Abbreviate the three sampling predicates.
    set AH : Finset (nonRoot G ⊕ (Fin n₀ × Fin L)) → Prop := fun S =>
      ∃ (h : (LHc c).type_verts ⊆ (↑(S.image id ∪ (LHc c).type_verts.toFinset) : Set _)),
        Nonempty ((inducedLabeledSubgraph (LHc c) (↑(S.image id ∪ (LHc c).type_verts.toFinset)) h).coe
          ≃f Frep) with hAH
    set AG : Finset (nonRoot G ⊕ (Fin n₀ × Fin L)) → Prop := fun S =>
      ∃ (h : G.type_verts ⊆ (↑(S.image (iotaG G) ∪ G.type_verts.toFinset) : Set _)),
        Nonempty ((inducedLabeledSubgraph G (↑(S.image (iotaG G) ∪ G.type_verts.toFinset)) h).coe
          ≃f Frep) with hAG
    -- The altered-pair set, lifted to `Sym2 (nonRoot G ⊕ …)` via `inl`.
    set Dalt : Finset (Sym2 (nonRoot G)) := Finset.univ.filter (fun p : Sym2 (nonRoot G) =>
        ¬ p.IsDiag ∧ Sym2.lift ⟨fun u u' => H.Adj (Sum.inl u) (Sum.inl u')
              ≠ G.graph.Adj u.1 u'.1, by intro u u'; simp [adj_comm]⟩ p) with hDalt
    set Dmap : Finset (Sym2 (nonRoot G ⊕ (Fin n₀ × Fin L))) :=
      Dalt.image (Sym2.map Sum.inl) with hDmap
    set Bad : Finset (nonRoot G ⊕ (Fin n₀ × Fin L)) → Prop := fun S =>
      ∃ p ∈ Dmap, p.toFinset ⊆ S with hBad
    -- `q ≤ n - n₀`, hence the `Uf`-powerset is nonempty.
    have hF1_ge : n₀ ≤ F.1 := by
      have := finFlag_size_ge_n₀ F; exact this
    have hqle : q ≤ n - n₀ := by rw [hq]; omega
    have hCU : 0 < (Uf.powersetCard q).card := by
      rw [Finset.card_powersetCard, hUcard]
      exact Nat.choose_pos hqle
    -- The adjacency-matching `hgood`.
    have hgood : ∀ S ∈ Vall.powersetCard q, S ⊆ Uf → ¬ Bad S → (AH S ↔ AG S) := by
      intro S _ hSUf hSnotBad
      -- every element of `S` is `inl`.
      have hSinl : ∀ x ∈ S, ∃ u, x = Sum.inl u := by
        intro x hx
        have := hSUf hx
        rw [hUf, Finset.mem_image] at this
        obtain ⟨u, _, rfl⟩ := this
        exact ⟨u, rfl⟩
      -- `S` spans no altered pair.
      have hSgood : ∀ u u', Sum.inl u ∈ S → Sum.inl u' ∈ S → s(u, u') ∉ Dalt := by
        intro u u' hu hu' hmem
        apply hSnotBad
        rw [hBad]
        refine ⟨Sym2.map Sum.inl s(u, u'), ?_, ?_⟩
        · rw [hDmap, Finset.mem_image]; exact ⟨s(u, u'), hmem, rfl⟩
        · rw [Sym2.map_pair_eq]
          intro x hx
          rw [Sym2.mem_toFinset, Sym2.mem_iff] at hx
          rcases hx with rfl | rfl <;> assumption
      -- The flag-iso between the two induced subgraphs.
      have hrootH : (LHc c).type_verts ⊆ (↑(S.image id ∪ (LHc c).type_verts.toFinset) : Set _) := by
        intro x hx
        rw [Finset.coe_union, Set.mem_union]; right
        rw [Finset.mem_coe, Set.mem_toFinset]; exact hx
      have hrootG : G.type_verts ⊆ (↑(S.image (iotaG G) ∪ G.type_verts.toFinset) : Set _) := by
        intro x hx
        rw [Finset.coe_union, Set.mem_union]; right
        rw [Finset.mem_coe, Set.mem_toFinset]; exact hx
      have hSimage_id : S.image id = S := Finset.image_id
      have hφ := induced_iso_match G H c Dalt hDalt hclI hclII S hSinl hSgood
        (↑(S.image id ∪ (LHc c).type_verts.toFinset)) (by rw [hSimage_id]) hrootH
        (↑(S.image (iotaG G) ∪ G.type_verts.toFinset)) rfl hrootG
      -- `AH S ↔ AG S` via composing with `hφ`.
      rw [hAH, hAG]
      constructor
      · rintro ⟨_, ⟨ψ⟩⟩; exact ⟨hrootG, ⟨hφ.symm.trans ψ⟩⟩
      · rintro ⟨_, ⟨ψ⟩⟩; exact ⟨hrootH, ⟨hφ.trans ψ⟩⟩
    -- Apply the coupling bound, then bound the two bad events.
    have hbound := counting_coupling_bound Vall Uf q hUfV AH AG Bad hCU hgood
    set X : ℕ := ((Vall.powersetCard q).filter (fun S => ¬ S ⊆ Uf)).card with hX
    set Y : ℕ := ((Vall.powersetCard q).filter (fun S => S ⊆ Uf ∧ Bad S)).card with hY
    set CW : ℕ := (Vall.powersetCard q).card with hCWdef
    -- Drop the (large) definitional hypotheses that the remaining arithmetic does not need.
    clear hgood hisoF hpH himgH hinjH hinjG himgG
    -- pool/card facts
    have hVge_nat : n - n₀ ≤ Vall.card := by rw [hVcard]; omega
    have hVcard_ge : (n : ℝ) / 2 ≤ (Vall.card : ℝ) := by
      have h1R : ((n - n₀ : ℕ) : ℝ) ≤ (Vall.card : ℝ) := by exact_mod_cast hVge_nat
      have h2 : ((n - n₀ : ℕ) : ℝ) = (n : ℝ) - n₀ := by rw [Nat.cast_sub (by omega)]
      have hn2 : (2 * n₀ : ℝ) ≤ n := by exact_mod_cast hn_2n₀
      rw [h2] at h1R; linarith
    have hnpR : (0:ℝ) < n := by exact_mod_cast hnpos
    have hVcardR_pos : (0:ℝ) < (Vall.card : ℝ) := by linarith
    have hqVall : q ≤ Vall.card := by rw [hVcard]; omega
    have hqm : q ≤ m := by rw [hq]; omega
    -- `|Vall ∖ Uf| ≤ n₀ * L`.
    have hVsubUf : (Vall \ Uf).card ≤ n₀ * L := by
      have hsub : (Vall \ Uf).card = Vall.card - Uf.card :=
        Finset.card_sdiff_of_subset hUfV
      rw [hsub, hVcard, hUcard]; omega
    -- The meets-`Uf`ᶜ ratio bound `X / CW ≤ 2 m n₀ lam`.
    have hXbound : (X : ℝ) / (CW : ℝ) ≤ 2 * m * n₀ * lam := by
      have hnat : X * Vall.card ≤ (Vall \ Uf).card * q * CW := by
        rw [hX, hCWdef, Finset.card_powersetCard]; exact meets_R_nat Vall Uf q hUfV
      have hVsubR : ((Vall \ Uf).card : ℝ) ≤ (n₀:ℝ) * lam * (2 * ((n:ℝ)/2)) := by
        have h1 : ((Vall \ Uf).card : ℝ) ≤ ((n₀ * L : ℕ) : ℝ) := by exact_mod_cast hVsubUf
        push_cast at h1
        have hLn : (n₀:ℝ) * L ≤ (n₀:ℝ) * (lam * n) :=
          mul_le_mul_of_nonneg_left hLub (by positivity)
        have heq : (n₀:ℝ) * lam * (2 * ((n:ℝ)/2)) = (n₀:ℝ) * (lam * n) := by ring
        rw [heq]; linarith
      exact meets_ratio_le X CW Vall.card (Vall \ Uf).card q hnat ((n:ℝ)/2) lam m n₀
        hVcardR_pos hVcard_ge (by positivity) hVsubR (by exact_mod_cast hqm)
        hlampos.le (by positivity) (by positivity)
    -- `Dmap` non-diagonal and contained in `Vall`; and `|Dmap| ≤ ρ n²`.
    have hDmap_nd : ∀ p ∈ Dmap, ¬ p.IsDiag := by
      intro p hp
      rw [hDmap, Finset.mem_image] at hp
      obtain ⟨p0, hp0, rfl⟩ := hp
      rw [hDalt, Finset.mem_filter] at hp0
      induction p0 with
      | _ a b =>
        simp only [Sym2.map_pair_eq, Sym2.isDiag_iff_proj_eq]
        intro hab
        have hnd := hp0.2.1
        simp only [Sym2.isDiag_iff_proj_eq] at hnd
        exact hnd (Sum.inl_injective hab)
    have hDmap_V : ∀ p ∈ Dmap, p.toFinset ⊆ Vall := by
      intro p hp
      rw [hDmap, Finset.mem_image] at hp
      obtain ⟨p0, _, rfl⟩ := hp
      induction p0 with
      | _ a b =>
        rw [Sym2.map_pair_eq]
        intro x hx
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;>
          exact hUfV (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have hDmap_card : (Dmap : Finset _).card ≤ Dalt.card := by
      rw [hDmap]; exact Finset.card_image_le
    have hDalt_card : (Dalt.card : ℝ) ≤ ρ * (n:ℝ)^2 := by
      rw [hDalt]; exact hclIII
    have hDmap_le : (Dmap.card : ℝ) ≤ ρ * (n:ℝ)^2 :=
      le_trans (by exact_mod_cast hDmap_card) hDalt_card
    -- The spans-a-pair ratio bound `Y / CW ≤ 4 m² ρ`.
    have hYbound : (Y : ℝ) / (CW : ℝ) ≤ 4 * (m:ℝ)^2 * ρ := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · -- `q < 2`: no q-subset spans a non-diagonal pair, so `Y = 0`.
        have hY0 : Y = 0 := by
          rw [hY, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          rintro ⟨_, p, hpD, hpsub⟩
          have hpc : p.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag p (hDmap_nd p hpD)
          have hle : p.toFinset.card ≤ S.card := Finset.card_le_card hpsub
          omega
        rw [hY0]; simp; positivity
      · -- `Y ≤ #{S : spans a pair}`, then the spans count bound.
        have hYle : Y ≤ ((Vall.powersetCard q).filter (fun S => ∃ p ∈ Dmap, p.toFinset ⊆ S)).card := by
          rw [hY]; apply Finset.card_le_card
          intro S hS; rw [Finset.mem_filter] at hS ⊢
          exact ⟨hS.1, hS.2.2⟩
        have hnat : Y * (Vall.card * (Vall.card - 1)) ≤ Dmap.card * (q * (q - 1)) * CW := by
          calc Y * (Vall.card * (Vall.card - 1))
              ≤ ((Vall.powersetCard q).filter (fun S => ∃ p ∈ Dmap, p.toFinset ⊆ S)).card
                  * (Vall.card * (Vall.card - 1)) := Nat.mul_le_mul_right _ hYle
            _ ≤ Dmap.card * (q * (q - 1)) * CW := by
                rw [hCWdef, Finset.card_powersetCard]; exact spans_pair_nat Vall Dmap q hDmap_nd hDmap_V
        exact spans_ratio_le Y CW Vall.card Dmap.card q hnat (n:ℝ) lam m ρ
          hVcard_ge hnpR hq2 hqVall (by exact_mod_cast hqm) hDmap_le hρpos.le (by positivity)
    -- Combine: `< ε`.
    have hbound' : |(((Vall.powersetCard q).filter AH).card : ℝ) / ((Vall.powersetCard q).card : ℝ)
            - ((Uf.powersetCard q).filter AG).card / ((Uf.powersetCard q).card : ℝ)|
        ≤ 2 * ((X : ℝ) / (CW : ℝ)) + (Y : ℝ) / (CW : ℝ) := by
      have heq : 2 * ((X : ℝ) / (CW : ℝ)) = 2 * (X : ℝ) / (CW : ℝ) := by ring
      rw [heq]; exact hbound
    have hn₀m : (n₀ : ℝ) ≤ m := by exact_mod_cast hmn₀
    exact final_lt _ _ ((X:ℝ)/(CW:ℝ)) ((Y:ℝ)/(CW:ℝ)) ε Cm lam ρ m n₀
      hbound' hXbound hYbound hCm hn₀m hlampos.le (by positivity) hρpos.le hconst

end FlagAlgebras.MetaTheory
