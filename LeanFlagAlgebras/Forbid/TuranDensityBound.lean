import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.Forbid.TuranDensity

open FlagAlgebras Filter Topology SimpleGraph

namespace Forbid

def _root_.SimpleGraph.toFinFlag
    {n : ℕ} (G : SimpleGraph (Fin n)) : FinFlag ∅ₜ
  :=
  let F : FlagWithSize ∅ₜ n := ⟦{
    graph := G,
    type_embed := RelEmbedding.ofIsEmpty _ _
  }⟧
  ⟨n, F⟩

noncomputable def _root_.SimpleGraph.toFlagAlgebra
    {n : ℕ} (G : SimpleGraph (Fin n)) : FlagAlgebra ∅ₜ
  :=
  ⟦unitVector G.toFinFlag⟧

lemma exists_graphSeq_of_densityLowerBound
    {n m : ℕ} (H : SimpleGraph (Fin n)) (F : SimpleGraph (Fin m))
    {c : ℝ} (hc : 0 ≤ c)
    (a : ℕ → ℕ)
    (hm_le_a : ∀ k : ℕ, m ≤ a k)
    (ha_gt : ∀ k : ℕ, c < (generalizedExtremalNumber (a k) H F / (a k).choose m : ℝ)) :
    ∃ Gseq : (k : ℕ) → SimpleGraph (Fin (a k)),
      (∀ k : ℕ, H.Free (Gseq k)) ∧
      (∀ k : ℕ, c * (a k).choose m
          < GraphAlgebras.subgraphCount F (Gseq k)) := by
  have ha_gt_mul : ∀ k : ℕ,
      c * (a k).choose m < generalizedExtremalNumber (a k) H F := by
    intro k
    have hden_pos : (0 : ℝ) < ((a k).choose m : ℝ) := by
      exact_mod_cast Nat.choose_pos (hm_le_a k)
    exact (lt_div_iff₀ hden_pos).mp (ha_gt k)
  have hnonneg : ∀ k : ℕ, 0 ≤ c * ((a k).choose m : ℝ) := by
    intro k
    exact mul_nonneg hc (by exact_mod_cast Nat.zero_le ((a k).choose m))
  have hGk : ∀ k : ℕ,
      ∃ G : SimpleGraph (Fin (a k)),
        H.Free G ∧
        c * ((a k).choose m : ℝ) < (GraphAlgebras.subgraphCount F G : ℝ) := by
    intro k
    let x : ℝ := c * ((a k).choose m : ℝ)
    have hx_floor_lt : Nat.floor x < generalizedExtremalNumber (a k) H F := by
      exact (Nat.floor_lt (hnonneg k)).2 (by simpa [x] using ha_gt_mul k)
    rw [generalizedExtremalNumber] at hx_floor_lt
    rcases Finset.lt_sup_iff.mp hx_floor_lt with ⟨G, hG_mem, hG_lt⟩
    have hG_free : H.Free G := by
      simpa [Finset.mem_filter] using hG_mem
    refine ⟨G, hG_free, ?_⟩
    have hx_lt_floor_succ : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    have hfloor_succ_le_count :
        (Nat.floor x : ℝ) + 1 ≤ (GraphAlgebras.subgraphCount F G : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hG_lt
    exact by
      simpa [x] using lt_of_lt_of_le hx_lt_floor_succ hfloor_succ_le_count
  choose Gseq hG_free hG_gt using hGk
  exact ⟨Gseq, hG_free, hG_gt⟩

theorem generalizedTuranDensity_le_of_forbidLE
    {n m : ℕ} (H : SimpleGraph (Fin n)) (F : SimpleGraph (Fin m))
  {c : ℝ} (hc : 0 ≤ c) (h : F.toFlagAlgebra ≤[H.toFinFlag] c • 1)
    : generalizedTuranDensity H F ≤ c
  := by
  rw [← forbidLE_emptyType_iff_forbidLE] at h
  dsimp [forbidLE_emptyType] at h

  let f_den : ℕ → ℝ := fun k ↦ (generalizedExtremalNumber k H F / k.choose m : ℝ)
  suffices hε : ∀ ε > 0, ∀ᶠ k in atTop, f_den k ≤ c + ε by
    refine le_iff_forall_pos_le_add.mpr ?_
    intro ε hε_pos
    refine le_of_tendsto_of_tendsto ?_ (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c + ε) atTop (𝓝 (c + ε))) (hε ε hε_pos)
    simpa [f_den] using (tendsto_generalizedTuranDensity H F)

  contrapose h
  push_neg at h ⊢
  obtain ⟨ε, hε_pos, hε⟩ := h
  obtain ⟨a₀, ha₀_inc, ha_gt₀⟩ := extraction_of_frequently_atTop hε
  let a : ℕ → ℕ := fun k ↦ a₀ (k + m)
  have ha_inc : StrictMono a := by
    intro k l hkl
    exact ha₀_inc (Nat.add_lt_add_right hkl m)
  have ha_gt : ∀ k : ℕ, c + ε < f_den (a k) := by
    intro k
    simpa [a] using (ha_gt₀ (k + m))
  have hm_le_a : ∀ k : ℕ, m ≤ a k := by
    intro k
    exact le_trans (Nat.le_add_left m k) (ha₀_inc.id_le (k + m))
  clear hε ha₀_inc ha_gt₀

  have hcε : 0 ≤ c + ε := add_nonneg hc (le_of_lt hε_pos)
  obtain ⟨Gseq, hG_free, hG_gt⟩ := exists_graphSeq_of_densityLowerBound H F hcε a hm_le_a ha_gt
  let gseq : FlagSeq ∅ₜ := fun k ↦ (Gseq k).toFinFlag
  have hgseq_inc : Increases gseq := by
    intro k l hkl
    simp [gseq, toFinFlag]
    exact Nat.lt_of_succ_le (ha_inc hkl)
  obtain ⟨x, ϕ, hϕ_mono, hϕ_conv'⟩ := increasing_flagSeq_contain_convergent_subseq gseq hgseq_inc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (gseq ∘ ϕ) hϕ_conv'
  obtain ⟨hϕ_inc, hϕ_conv⟩ := flagSeq_convergesTo_iff.mp hϕ_conv'
  clear hcε hgseq_inc hϕ_inc hϕ_conv'

  use φ
  constructor
  · sorry
  · simp [PositiveHom.map_smul]
    sorry

example (a b c : ℝ) (H : c < a / b) (hb : b > 0) : c * b < a := by
  exact (lt_div_iff₀ hb).mp H

end Forbid
