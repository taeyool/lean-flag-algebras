import Mathlib

/-! # Clone multiplicity counting

This file proves a single combinatorial counting lemma used in the blow-up /
clone-closure development.  A subset `Q` of the blow-up vertex set
`Σ v : Fin n, Fin (m v)` whose projection `Sigma.fst` is injective on `Q` and
whose image is a fixed finset `W` of base vertices is exactly a choice of one
"clone" `Fin (m v)` for each `v ∈ W`.  Hence there are `∏ v ∈ W, m v` such
subsets.

The proof is an explicit bijection (`Finset.card_bij'`) between the clone-fiber
subsets and the dependent-function type `(v : ↥W) → Fin (m v.val)`, whose
cardinality is `∏ v ∈ W, m v` by `Fintype.card_pi`. -/

open Classical

namespace FlagAlgebras.MetaTheory

variable {n : ℕ} {m : Fin n → ℕ}

/-- Transporting the second component of a dependent pair along an equality of its
first component reconstructs the original pair. -/
private theorem sigma_cast_fst {n : ℕ} {m : Fin n → ℕ}
    (x : Σ v : Fin n, Fin (m v)) (v : Fin n) (h : x.fst = v) :
    (⟨v, h ▸ x.snd⟩ : Σ v : Fin n, Fin (m v)) = x := by
  subst h; rfl

/-- **Clone multiplicity**: the number of subsets of the blow-up vertex set
`Σ v, Fin (m v)` that project injectively onto a fixed finset `W` of base vertices
is `∏ v ∈ W, m v` (one clone choice per vertex of `W`).

(The coercion `↑Q` carries an explicit `Set (Σ v, Fin (m v))` ascription only to
fix elaboration order; the proposition is `Set.InjOn Sigma.fst ↑Q`.) -/
theorem clone_fiber_card (W : Finset (Fin n)) :
    (Finset.univ.filter (fun Q : Finset (Σ v : Fin n, Fin (m v)) =>
      Set.InjOn Sigma.fst (↑Q : Set (Σ v : Fin n, Fin (m v))) ∧ Q.image Sigma.fst = W)).card
      = ∏ v ∈ W, m v := by
  classical
  -- The unique element of `Q` over a base vertex `v ∈ W`: injectivity gives at most
  -- one element over `v`, and `Q.image Sigma.fst = W ∋ v` gives at least one.
  have huniq : ∀ (Q : Finset (Σ v : Fin n, Fin (m v))),
      (Set.InjOn Sigma.fst (↑Q : Set (Σ v : Fin n, Fin (m v))) ∧ Q.image Sigma.fst = W) →
      ∀ (v : Fin n), v ∈ W → ∃! x : Σ v : Fin n, Fin (m v), x ∈ Q ∧ x.fst = v := by
    rintro Q ⟨hinj, himg⟩ v hv
    rw [← himg, Finset.mem_image] at hv
    obtain ⟨x, hxQ, hxv⟩ := hv
    refine ⟨x, ⟨hxQ, hxv⟩, ?_⟩
    rintro y ⟨hyQ, hyv⟩
    exact hinj hyQ hxQ (by rw [hyv, hxv])
  -- The "blow-up section" of a clone choice `g`: pick `⟨v, g v⟩` for each `v ∈ W`.
  set sec : ((v : (W : Finset (Fin n))) → Fin (m v.val)) →
      Finset (Σ v : Fin n, Fin (m v)) :=
    fun g => Finset.univ.image (fun v : (W : Finset (Fin n)) =>
      (⟨v.val, g v⟩ : Σ v : Fin n, Fin (m v))) with hsec
  -- `sec g` is a clone-fiber subset: `Sigma.fst`-injective with image `W`.
  have hsec_mem : ∀ g, sec g ∈ Finset.univ.filter
      (fun Q : Finset (Σ v : Fin n, Fin (m v)) =>
        Set.InjOn Sigma.fst (↑Q : Set (Σ v : Fin n, Fin (m v))) ∧ Q.image Sigma.fst = W) := by
    intro g
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- distinct base vertices give distinct pairs, so `Sigma.fst` is injective on `sec g`
      intro a ha b hb hab
      simp only [hsec, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
        true_and] at ha hb
      obtain ⟨va, rfl⟩ := ha
      obtain ⟨vb, rfl⟩ := hb
      simp only at hab
      rw [Subtype.ext hab]
    · -- the image of `sec g` under `Sigma.fst` is exactly `W`
      ext w
      simp only [hsec, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ⟨v, rfl⟩, rfl⟩; exact v.property
      · intro hw; exact ⟨⟨w, g ⟨w, hw⟩⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
  -- Rewrite the RHS product as the cardinality of `(v : ↥W) → Fin (m v.val)`.
  rw [show (∏ v ∈ W, m v) = Fintype.card ((v : (W : Finset (Fin n))) → Fin (m v.val)) by
        rw [Fintype.card_pi]; simp only [Fintype.card_fin]; rw [Finset.prod_coe_sort]]
  rw [← Finset.card_univ (α := (v : (W : Finset (Fin n))) → Fin (m v.val))]
  -- The bijection: forward picks the unique clone over each `v ∈ W`; backward is `sec`.
  refine Finset.card_bij'
    (i := fun Q hQ v =>
      (huniq Q (Finset.mem_filter.mp hQ).2 v.val v.property).choose_spec.1.2 ▸
        (huniq Q (Finset.mem_filter.mp hQ).2 v.val v.property).choose.snd)
    (j := fun g _ => sec g)
    (fun Q hQ => Finset.mem_univ _)
    (fun g _ => hsec_mem g)
    ?_ ?_
  · -- left inverse: `sec (i Q) = Q`
    intro Q hQ
    obtain ⟨hinj, himg⟩ := (Finset.mem_filter.mp hQ).2
    ext q
    simp only [hsec, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · -- each chosen clone lies in `Q`
      rintro ⟨v, rfl⟩
      rw [sigma_cast_fst _ _ (huniq Q (Finset.mem_filter.mp hQ).2 v.val v.property).choose_spec.1.2]
      exact (huniq Q (Finset.mem_filter.mp hQ).2 v.val v.property).choose_spec.1.1
    · -- conversely, every `q ∈ Q` is the chosen clone over `q.fst ∈ W`
      intro hqQ
      have hfst : q.fst ∈ W := by rw [← himg]; exact Finset.mem_image_of_mem _ hqQ
      refine ⟨⟨q.fst, hfst⟩, ?_⟩
      rw [sigma_cast_fst _ _ (huniq Q (Finset.mem_filter.mp hQ).2 q.fst hfst).choose_spec.1.2]
      have hspec := (huniq Q (Finset.mem_filter.mp hQ).2 q.fst hfst).choose_spec
      exact (hspec.2 q ⟨hqQ, rfl⟩).symm
  · -- right inverse: `i (sec g) = g`
    intro g _
    funext v
    have hmem := hsec_mem g
    -- the chosen clone of `sec g` over `v` is `⟨v, g v⟩`, by uniqueness
    have key : (⟨v.val, (huniq (sec g) (Finset.mem_filter.mp hmem).2 v.val v.property).choose_spec.1.2
          ▸ (huniq (sec g) (Finset.mem_filter.mp hmem).2 v.val v.property).choose.snd⟩
          : Σ v : Fin n, Fin (m v)) = ⟨v.val, g v⟩ := by
      rw [sigma_cast_fst _ _ (huniq (sec g) (Finset.mem_filter.mp hmem).2 v.val v.property).choose_spec.1.2]
      have hspec := (huniq (sec g) (Finset.mem_filter.mp hmem).2 v.val v.property).choose_spec
      refine (hspec.2 _ ⟨?_, rfl⟩).symm
      simp only [hsec, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨v, rfl⟩
    exact eq_of_heq (Sigma.mk.inj_iff.mp key).2

end FlagAlgebras.MetaTheory
