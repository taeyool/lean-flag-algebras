import LeanFlagAlgebras.MetaTheory.CloneCount

/-! # Total clone count

Summing the clone-fiber count `clone_fiber_card` over all base sets `W ⊆ S₀` of
size `r` gives the total number of `Sigma.fst`-injective clone subsets projecting
into `S₀` with image of size `r`.  The fiberwise decomposition
(`Finset.card_eq_sum_card_fiberwise`) along `Q ↦ Q.image Sigma.fst` reduces the
total count to the elementary-symmetric sum `∑_{W ⊆ S₀, |W| = r} ∏_{v ∈ W} m v`,
and the equal-clone specialisation collapses this to `(|S₀| choose r) · M^r`. -/

open Classical

namespace FlagAlgebras.MetaTheory

variable {n : ℕ} {m : Fin n → ℕ}

/-- **Total clone count**: the number of subsets `Q` of the blow-up vertex set
`Σ v, Fin (m v)` that project `Sigma.fst`-injectively into a base set `S₀` with image of
size `r` equals the elementary-symmetric sum `∑_{W ⊆ S₀, |W| = r} ∏_{v ∈ W} m v`. -/
theorem clone_total_card (S₀ : Finset (Fin n)) (r : ℕ) :
    (Finset.univ.filter (fun Q : Finset (Σ v : Fin n, Fin (m v)) =>
      Set.InjOn Sigma.fst (↑Q : Set (Σ v : Fin n, Fin (m v))) ∧
        Q.image Sigma.fst ⊆ S₀ ∧ Q.card = r)).card
      = ∑ W ∈ S₀.powersetCard r, ∏ v ∈ W, m v := by
  classical
  -- Decompose the filter set fiberwise along `Q ↦ Q.image Sigma.fst`, landing in
  -- `S₀.powersetCard r` (image `⊆ S₀` of card `r`).
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun Q : Finset (Σ v : Fin n, Fin (m v)) => Q.image Sigma.fst)
        (t := S₀.powersetCard r) ?_]
  · -- Each fiber over `W` has the clone-fiber cardinality `∏ v ∈ W, m v`.
    refine Finset.sum_congr rfl ?_
    intro W hW
    rw [Finset.mem_powersetCard] at hW
    obtain ⟨hWS, hWr⟩ := hW
    rw [← clone_fiber_card (m := m) W]
    -- Rewrite the fiber `{Q ∈ filterSet | Q.image fst = W}` as `clone_fiber_card`'s LHS.
    congr 1
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hinj, _, _⟩, himg⟩
      exact ⟨hinj, himg⟩
    · rintro ⟨hinj, himg⟩
      refine ⟨⟨hinj, ?_, ?_⟩, himg⟩
      · rw [himg]; exact hWS
      · -- `Q.card = (Q.image fst).card = W.card = r` via injectivity.
        rw [← Finset.card_image_of_injOn hinj, himg, hWr]
  · -- maps-in: an injective clone with image `⊆ S₀` of card `r` lands in `S₀.powersetCard r`.
    intro Q hQ
    rw [Finset.mem_coe, Finset.mem_filter] at hQ
    obtain ⟨_, hinj, hsub, hcard⟩ := hQ
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨hsub, ?_⟩
    rw [Finset.card_image_of_injOn hinj, hcard]

/-- Equal-clones specialisation: if every clone class meeting `S₀` has size `M`, the total count
is `(S₀.card).choose r * M ^ r`. -/
theorem clone_total_card_const (S₀ : Finset (Fin n)) (r M : ℕ) (hM : ∀ v ∈ S₀, m v = M) :
    (Finset.univ.filter (fun Q : Finset (Σ v : Fin n, Fin (m v)) =>
      Set.InjOn Sigma.fst (↑Q : Set (Σ v : Fin n, Fin (m v))) ∧
        Q.image Sigma.fst ⊆ S₀ ∧ Q.card = r)).card
      = (S₀.card).choose r * M ^ r := by
  classical
  rw [clone_total_card]
  -- Each summand `∏ v ∈ W, m v = M^r` since `W ⊆ S₀` (so `m v = M`) and `|W| = r`.
  have hsum : ∀ W ∈ S₀.powersetCard r, ∏ v ∈ W, m v = M ^ r := by
    intro W hW
    rw [Finset.mem_powersetCard] at hW
    obtain ⟨hWS, hWr⟩ := hW
    rw [Finset.prod_congr rfl (fun v hv => hM v (hWS hv)), Finset.prod_const, hWr]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

end FlagAlgebras.MetaTheory
