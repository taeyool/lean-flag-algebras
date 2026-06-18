import LeanFlagAlgebras.MetaTheory.PlantedCount
import LeanFlagAlgebras.MetaTheory.CloneTotal
import LeanFlagAlgebras.MetaTheory.LabeledCount

/-! # The reduced planted estimate (equal non-root clones)

This file assembles the combinatorial counts of `PlantedCount`, `CloneTotal`, and `LabeledCount`
into the reduced planted estimate (`lem:planted-estimate`): the density of `F₀` in the planted
blow-up differs from its density in the base by at most `1 - ρ`, where `ρ` is the probability that
a uniform `(ℓ-k)`-sample of non-root blow-up vertices meets each clone class at most once.

The proof runs through four counts of vertex subsets of size `ℓ` containing the roots:
* `A_blow` — those inducing `F₀` in the blow-up;
* `A_base` — those inducing `F₀` in the base;
* `A_good` — those inducing `F₀` *and* meeting each clone class at most once (`Sigma.fst`-InjOn);
* the "all/good" totals `T_all`, `T_good` (dropping the inducing condition).

`good_event_count` collapses `A_good` to `M^(ℓ-k)·A_base`; a good/bad split bounds
`A_blow - A_good ≤ T_all - T_good`; and a little rational algebra turns the count inequalities into
the stated density bound. -/

open Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras LabeledSubgraph

variable {n k ℓ : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}

/-- The number of size-`r` supersets of a fixed set `R` in a fintype is `C(|V|-|R|, r-|R|)`. -/
private theorem superset_count {V : Type} [Fintype V] [DecidableEq V] (R : Finset V) (r : ℕ)
    (hr : R.card ≤ r) :
    (Finset.univ.filter (fun S : Finset V => R ⊆ S ∧ S.card = r)).card
      = (Fintype.card V - R.card).choose (r - R.card) := by
  rw [show (Fintype.card V - R.card).choose (r - R.card)
        = (Rᶜ.powersetCard (r - R.card)).card by
        rw [Finset.card_powersetCard, Finset.card_compl]]
  apply Finset.card_nbij' (i := fun S => S \ R) (j := fun Q => Q ∪ R)
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨hsub, hcard⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · rw [Finset.subset_iff]; intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_compl]; exact hx.2
    · rw [Finset.card_sdiff_of_subset hsub, hcard]
  · intro Q hQ
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hQ
    obtain ⟨hQsub, hQcard⟩ := hQ
    have hdisj : Disjoint Q R := by
      rw [Finset.disjoint_right]; intro x hxR hxQ
      have := hQsub hxQ; rw [Finset.mem_compl] at this; exact this hxR
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.subset_union_right, ?_⟩
    rw [Finset.card_union_of_disjoint hdisj, hQcard]
    omega
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.sdiff_union_of_subset hS.1
  · intro Q hQ
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hQ
    have hdisj : Disjoint Q R := by
      rw [Finset.disjoint_right]; intro x hxR hxQ
      have := hQ.1 hxQ; rw [Finset.mem_compl] at this; exact this hxR
    exact Finset.union_sdiff_cancel_right hdisj

/-- The base roots finset is the image of `θ`. -/
private theorem baseRoots_eq_image (θ : H ↪g G) :
    (baseLabeledGraph θ).type_verts.toFinset = Finset.image (fun t => θ t) Finset.univ := by
  ext v
  simp only [Set.mem_toFinset, LabeledGraph.mem_type_verts, Finset.mem_image, Finset.mem_univ,
    true_and]
  rfl

/-- The base roots finset has cardinality `k`. -/
private theorem baseRoots_card (θ : H ↪g G) :
    (baseLabeledGraph θ).type_verts.toFinset.card = k := by
  rw [baseRoots_eq_image, Finset.card_image_of_injective _ θ.injective, Finset.card_univ,
    Fintype.card_fin]

/-- The planted roots project (`Sigma.fst`) onto the base roots. -/
private theorem plantedRoots_image' (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    ((blowupLabeledGraph m θ c).type_verts.toFinset).image Sigma.fst
      = (baseLabeledGraph θ).type_verts.toFinset := by
  ext v
  simp only [Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LabeledGraph.mem_type_verts] at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t, rfl⟩
  · intro hv
    rw [LabeledGraph.mem_type_verts] at hv
    obtain ⟨t, rfl⟩ := hv
    refine ⟨⟨θ t, c t⟩, ?_, rfl⟩
    rw [LabeledGraph.mem_type_verts]
    exact ⟨t, rfl⟩

/-- The planted roots project `Sigma.fst`-injectively. -/
private theorem plantedRoots_injOn' (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    Set.InjOn Sigma.fst (↑((blowupLabeledGraph m θ c).type_verts.toFinset)
      : Set (Σ v : Fin n, Fin (m v))) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Set.mem_toFinset, LabeledGraph.mem_type_verts] at ha hb
  obtain ⟨ta, rfl⟩ := ha
  obtain ⟨tb, rfl⟩ := hb
  simp only [blowupLabeledGraph_type_embed] at hab ⊢
  have : θ ta = θ tb := hab
  have htab : ta = tb := θ.injective this
  subst htab; rfl

/-- The planted roots finset has cardinality `k`. -/
private theorem plantedRoots_card (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) :
    (blowupLabeledGraph m θ c).type_verts.toFinset.card = k := by
  rw [← Finset.card_image_of_injOn (plantedRoots_injOn' m θ c), plantedRoots_image' m θ c,
    baseRoots_card]

/-- On a `Sigma.fst`-injective set `S'` containing the planted roots, a vertex projects into the
base roots iff it is itself a planted root. -/
private theorem mem_baseRoots_iff' (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (S' : Finset (Σ v : Fin n, Fin (m v)))
    (hroot : (blowupLabeledGraph m θ c).type_verts.toFinset ⊆ S')
    (hinj : Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))))
    (x : Σ v : Fin n, Fin (m v)) (hxS : x ∈ S') :
    x.fst ∈ (baseLabeledGraph θ).type_verts.toFinset
      ↔ x ∈ (blowupLabeledGraph m θ c).type_verts.toFinset := by
  constructor
  · intro hx
    rw [Set.mem_toFinset, LabeledGraph.mem_type_verts] at hx
    obtain ⟨t, ht⟩ := hx
    have hpr : (⟨θ t, c t⟩ : Σ v, Fin (m v)) ∈ (blowupLabeledGraph m θ c).type_verts.toFinset := by
      rw [Set.mem_toFinset, LabeledGraph.mem_type_verts]; exact ⟨t, rfl⟩
    have hprS : (⟨θ t, c t⟩ : Σ v, Fin (m v)) ∈ S' := hroot hpr
    have hxeq : x = ⟨θ t, c t⟩ := by
      apply hinj hxS hprS
      rw [baseLabeledGraph_type_embed] at ht
      simp only [ht]
    rw [hxeq]; exact hpr
  · intro hx
    rw [Set.mem_toFinset, LabeledGraph.mem_type_verts] at hx
    obtain ⟨t, ht⟩ := hx
    rw [Set.mem_toFinset, LabeledGraph.mem_type_verts]
    refine ⟨t, ?_⟩
    rw [← ht]
    simp only [baseLabeledGraph_type_embed, blowupLabeledGraph_type_embed]

/-- **Good total count**: the number of size-`ℓ` planted-root supersets that meet each clone class
at most once (`Sigma.fst`-InjOn) equals `C(n-k, ℓ-k)·M^(ℓ-k)`, when every non-root clone class has
size `M`. -/
private theorem good_total_count (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (M : ℕ) (hk : k ≤ ℓ)
    (hM : ∀ v, v ∉ Finset.image (fun t => θ t) Finset.univ → m v = M) :
    (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      (blowupLabeledGraph m θ c).type_verts.toFinset ⊆ S' ∧ S'.card = ℓ ∧
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))))).card
      = (n - k).choose (ℓ - k) * M ^ (ℓ - k) := by
  set pr := (blowupLabeledGraph m θ c).type_verts.toFinset with hpr
  set S₀ : Finset (Fin n) := (Finset.image (fun t => θ t) (Finset.univ : Finset (Fin k)))ᶜ with hS₀
  -- The non-root base vertices number `n - k`.
  have hS₀card : S₀.card = n - k := by
    rw [hS₀, Finset.card_compl, Finset.card_image_of_injective _ θ.injective, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
  -- The non-root clones all have size `M`.
  have hMS₀ : ∀ v ∈ S₀, m v = M := by
    intro v hv
    rw [hS₀, Finset.mem_compl] at hv
    exact hM v hv
  rw [show (n - k).choose (ℓ - k) * M ^ (ℓ - k) = S₀.card.choose (ℓ - k) * M ^ (ℓ - k) by
        rw [hS₀card], ← clone_total_card_const (m := m) S₀ (ℓ - k) M hMS₀]
  -- planted roots ↔ image θ as a finset (via the base-roots image).
  have hpr_img : pr.image Sigma.fst = Finset.image (fun t => θ t) (Finset.univ : Finset (Fin k)) := by
    rw [hpr, plantedRoots_image' m θ c, baseRoots_eq_image]
  have hpr_inj : Set.InjOn Sigma.fst (↑pr : Set (Σ v : Fin n, Fin (m v))) :=
    plantedRoots_injOn' m θ c
  have hpr_card : pr.card = k := plantedRoots_card m θ c
  refine Finset.card_nbij' (i := fun S' => S' \ pr) (j := fun Q => Q ∪ pr) ?_ ?_ ?_ ?_
  · -- forward map well-defined
    intro S' hS'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    obtain ⟨hroot, hcard, hinj⟩ := hS'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · -- InjOn on S' \ pr
      exact hinj.mono (by rw [Finset.coe_subset]; exact Finset.sdiff_subset)
    · -- image ⊆ S₀
      rw [Finset.subset_iff]
      intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨x, hxQ, rfl⟩ := hv
      rw [Finset.mem_sdiff] at hxQ
      obtain ⟨hxS, hxnr⟩ := hxQ
      rw [hS₀, Finset.mem_compl]
      intro hcontra
      apply hxnr
      have : x.fst ∈ (baseLabeledGraph θ).type_verts.toFinset := by
        rw [baseRoots_eq_image]; exact hcontra
      exact (mem_baseRoots_iff' m θ c S' hroot hinj x hxS).mp this
    · -- card = ℓ - k
      rw [Finset.card_sdiff_of_subset hroot, hcard, hpr_card]
  · -- backward map well-defined
    intro Q hQ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    obtain ⟨hQinj, hQimg, hQcard⟩ := hQ
    -- disjoint images, hence disjoint sets
    have hdisjImg : Disjoint (Q.image Sigma.fst) (pr.image Sigma.fst) := by
      rw [hpr_img]
      apply Finset.disjoint_left.mpr
      intro v hvQ hvpr
      have := hQimg hvQ
      rw [hS₀, Finset.mem_compl] at this
      exact this hvpr
    have hdisj : Disjoint Q pr := by
      rw [Finset.disjoint_left]
      intro x hxQ hxpr
      exact (Finset.disjoint_left.mp hdisjImg) (Finset.mem_image_of_mem _ hxQ)
        (Finset.mem_image_of_mem _ hxpr)
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.subset_union_right, ?_, ?_⟩
    · -- card = ℓ
      rw [Finset.card_union_of_disjoint hdisj, hQcard, hpr_card]
      omega
    · -- InjOn on Q ∪ pr
      intro a ha b hb hab
      rw [Finset.coe_union, Set.mem_union] at ha hb
      rw [Finset.disjoint_left] at hdisjImg
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hQinj ha hb hab
      · exact absurd (hab ▸ Finset.mem_image_of_mem _ hb) (hdisjImg (Finset.mem_image_of_mem _ ha))
      · exact absurd (hab ▸ Finset.mem_image_of_mem _ ha) (hdisjImg (Finset.mem_image_of_mem _ hb))
      · exact hpr_inj ha hb hab
  · -- left inverse
    intro S' hS'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    exact Finset.sdiff_union_of_subset hS'.1
  · -- right inverse
    intro Q hQ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    obtain ⟨hQinj, hQimg, hQcard⟩ := hQ
    have hdisj : Disjoint Q pr := by
      rw [Finset.disjoint_left]
      intro x hxQ hxpr
      have h1 : x.fst ∈ S₀ := hQimg (Finset.mem_image_of_mem _ hxQ)
      have h2 : x.fst ∈ Finset.image (fun t => θ t) (Finset.univ : Finset (Fin k)) := by
        rw [← hpr_img]; exact Finset.mem_image_of_mem _ hxpr
      rw [hS₀, Finset.mem_compl] at h1
      exact h1 h2
    exact Finset.union_sdiff_cancel_right hdisj

/-- A vertex set inducing a flag `≃f F₀` (with `F₀` on `Fin ℓ`) in any host has cardinality `ℓ`. -/
private theorem induced_iso_card {V : Type} [Fintype V] [DecidableEq V] (Grep : LabeledGraph H V)
    (F₀ : LabeledGraph H (Fin ℓ)) (W : Finset V)
    (hroot : Grep.type_verts ⊆ (↑W : Set V))
    (hiso : Nonempty ((inducedLabeledSubgraph Grep (↑W) hroot).coe ≃f F₀)) :
    W.card = ℓ := by
  obtain ⟨φ⟩ := hiso
  have hsz := labeledGraphIso_size_eq _ _ φ
  have hcoe : (inducedLabeledSubgraph Grep (↑W) hroot).coe.size
      = (inducedLabeledSubgraph Grep (↑W) hroot).size := rfl
  rw [hcoe, inducedLabeledSubgraph_size] at hsz
  simp only [LabeledGraph.size, Fintype.card_fin] at hsz
  rw [← hsz, ← Set.toFinset_card, Finset.toFinset_coe]

/-- **Good event count, collapsed** (equal non-root clones): with every non-root clone class of size
`M`, the good blow-up subsets inducing `F₀` number `M^(ℓ-k)` times the base subsets inducing `F₀`. -/
private theorem good_event_count_const (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (F₀ : LabeledGraph H (Fin ℓ)) (M : ℕ)
    (hM : ∀ v, v ∉ Finset.image (fun t => θ t) Finset.univ → m v = M) :
    (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (hroot : (blowupLabeledGraph m θ c).type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) ∧
        Nonempty ((inducedLabeledSubgraph (blowupLabeledGraph m θ c) (↑S') hroot).coe ≃f F₀))).card
      = M ^ (ℓ - k) *
        (Finset.univ.filter (fun W : Finset (Fin n) =>
          ∃ (hroot : (baseLabeledGraph θ).type_verts ⊆ (↑W : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑W) hroot).coe ≃f F₀))).card := by
  rw [good_event_count m θ c F₀]
  -- Each summand is `M^(ℓ-k)`.
  have hsummand : ∀ W ∈ (Finset.univ.filter (fun W : Finset (Fin n) =>
      ∃ (hroot : (baseLabeledGraph θ).type_verts ⊆ (↑W : Set (Fin n))),
        Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑W) hroot).coe ≃f F₀))),
      ∏ v ∈ (W \ (baseLabeledGraph θ).type_verts.toFinset), m v = M ^ (ℓ - k) := by
    intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
    obtain ⟨hroot, hiso⟩ := hW
    -- the product is over (ℓ - k) terms, each equal to M
    have hWcard : W.card = ℓ := induced_iso_card (baseLabeledGraph θ) F₀ W hroot hiso
    have hsub : (baseLabeledGraph θ).type_verts.toFinset ⊆ W := by
      rw [Set.toFinset_subset]; exact hroot
    rw [Finset.prod_congr rfl (fun v hv => ?_), Finset.prod_const,
      Finset.card_sdiff_of_subset hsub, hWcard, baseRoots_card]
    -- each `m v = M` since `v ∉ roots = image θ`
    rw [Finset.mem_sdiff] at hv
    obtain ⟨_, hvnr⟩ := hv
    apply hM
    rw [← baseRoots_eq_image]; exact hvnr
  rw [Finset.sum_congr rfl hsummand, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Good event count, collapsed — host-generic version**.  For any host `B` over the blow-up
vertex type with the *same* planted roots (`hBroots`) and whose good subsets induce `F₀` exactly when
the blow-up's do (`hBgood`), the good `B`-subsets inducing `F₀` number `M^(ℓ-k)` times the base
subsets inducing `F₀`.  Reduces to `good_event_count_const` by showing the two good-inducing filter
finsets are equal. -/
private theorem good_event_count_const_host (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (F₀ : LabeledGraph H (Fin ℓ)) (M : ℕ)
    (hM : ∀ v, v ∉ Finset.image (fun t => θ t) Finset.univ → m v = M)
    (B : LabeledGraph H (Σ v : Fin n, Fin (m v)))
    (hBroots : B.type_verts = (blowupLabeledGraph m θ c).type_verts)
    (hBgood : ∀ (S' : Finset (Σ v : Fin n, Fin (m v))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) →
        ∀ (hr : B.type_verts ⊆ (↑S' : Set _))
          (hr' : (blowupLabeledGraph m θ c).type_verts ⊆ (↑S' : Set _)),
          (Nonempty ((inducedLabeledSubgraph B (↑S') hr).coe ≃f F₀) ↔
           Nonempty ((inducedLabeledSubgraph (blowupLabeledGraph m θ c) (↑S') hr').coe ≃f F₀))) :
    (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (hroot : B.type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) ∧
        Nonempty ((inducedLabeledSubgraph B (↑S') hroot).coe ≃f F₀))).card
      = M ^ (ℓ - k) *
        (Finset.univ.filter (fun W : Finset (Fin n) =>
          ∃ (hroot : (baseLabeledGraph θ).type_verts ⊆ (↑W : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑W) hroot).coe ≃f F₀))).card := by
  rw [← good_event_count_const m θ c F₀ M hM]
  -- The two good-inducing filter finsets are equal.
  congr 1
  apply Finset.filter_congr
  intro S' _
  constructor
  · rintro ⟨hroot, hinj, hind⟩
    have hroot' : (blowupLabeledGraph m θ c).type_verts ⊆ (↑S' : Set _) := hBroots ▸ hroot
    exact ⟨hroot', hinj, (hBgood S' hinj hroot hroot').mp hind⟩
  · rintro ⟨hroot', hinj, hind⟩
    have hroot : B.type_verts ⊆ (↑S' : Set _) := hBroots ▸ hroot'
    exact ⟨hroot, hinj, (hBgood S' hinj hroot hroot').mpr hind⟩

/-- **Good/bad split** (count form): writing `A_blow, A_good, T_all, T_good` for the four counts,
`A_good ≤ A_blow` and `A_blow + T_good ≤ A_good + T_all`.  The first drops the InjOn condition; the
second observes that a *bad* (non-InjOn) inducing subset is a bad size-`ℓ` root-superset.  This is
host-generic: it depends on the host `B : LabeledGraph H (Σ v, Fin (m v))` only through its roots and
`induced_iso_card`, never through adjacency. -/
private theorem count_split (m : Fin n → ℕ)
    (B : LabeledGraph H (Σ v : Fin n, Fin (m v)))
    (F₀ : LabeledGraph H (Fin ℓ)) :
    let A_blow := (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (h : B.type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Nonempty ((inducedLabeledSubgraph B (↑S') h).coe ≃f F₀))).card
    let A_good := (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (hroot : B.type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) ∧
        Nonempty ((inducedLabeledSubgraph B (↑S') hroot).coe ≃f F₀))).card
    let T_all := (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      B.type_verts.toFinset ⊆ S' ∧ S'.card = ℓ)).card
    let T_good := (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      B.type_verts.toFinset ⊆ S' ∧ S'.card = ℓ ∧
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))))).card
    A_good ≤ A_blow ∧ A_blow + T_good ≤ A_good + T_all := by
  intro A_blow A_good T_all T_good
  -- abbreviate the four underlying finsets
  set Iall := Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (h : B.type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Nonempty ((inducedLabeledSubgraph B (↑S') h).coe ≃f F₀))
    with hIall
  set Igood := Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (hroot : B.type_verts ⊆ (↑S' : Set (Σ v : Fin n, Fin (m v)))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) ∧
        Nonempty ((inducedLabeledSubgraph B (↑S') hroot).coe ≃f F₀))
    with hIgood
  set Sall := Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      B.type_verts.toFinset ⊆ S' ∧ S'.card = ℓ) with hSall
  set Sgood := Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      B.type_verts.toFinset ⊆ S' ∧ S'.card = ℓ ∧
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v)))) with hSgood
  -- Igood ⊆ Iall
  have hsub_good : Igood ⊆ Iall := by
    intro S' hS'
    rw [hIgood, Finset.mem_filter] at hS'
    obtain ⟨hu, hroot, _, hind⟩ := hS'
    rw [hIall, Finset.mem_filter]
    exact ⟨hu, hroot, hind⟩
  -- Sgood ⊆ Sall
  have hsub_S : Sgood ⊆ Sall := by
    intro S' hS'
    rw [hSgood, Finset.mem_filter] at hS'
    obtain ⟨hu, hroot, hcard, _⟩ := hS'
    rw [hSall, Finset.mem_filter]
    exact ⟨hu, hroot, hcard⟩
  -- Iall \ Igood ⊆ Sall \ Sgood
  have hbad : Iall \ Igood ⊆ Sall \ Sgood := by
    intro S' hS'
    rw [Finset.mem_sdiff] at hS' ⊢
    obtain ⟨hin, hnin⟩ := hS'
    rw [hIall, Finset.mem_filter] at hin
    obtain ⟨_, hroot, hind⟩ := hin
    -- S' has card ℓ (inducing F₀) and contains the roots ⇒ ∈ Sall
    have hcard : S'.card = ℓ := induced_iso_card B F₀ S' hroot hind
    have hrootF : B.type_verts.toFinset ⊆ S' :=
      Set.toFinset_subset.mpr hroot
    have hmemSall : S' ∈ Sall := by
      rw [hSall, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hrootF, hcard⟩
    refine ⟨hmemSall, ?_⟩
    -- S' ∉ Sgood: else it would be InjOn, hence in Igood (contradiction)
    intro hmemSgood
    apply hnin
    rw [hSgood, Finset.mem_filter] at hmemSgood
    obtain ⟨_, _, _, hinj⟩ := hmemSgood
    rw [hIgood, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hroot, hinj, hind⟩
  refine ⟨Finset.card_le_card hsub_good, ?_⟩
  -- A_blow + T_good ≤ A_good + T_all from the partition bounds
  have h1 : Iall.card = Igood.card + (Iall \ Igood).card := by
    rw [← Finset.card_sdiff_add_card_eq_card hsub_good]; ring
  have h2 : Sall.card = Sgood.card + (Sall \ Sgood).card := by
    rw [← Finset.card_sdiff_add_card_eq_card hsub_S]; ring
  have h3 : (Iall \ Igood).card ≤ (Sall \ Sgood).card := Finset.card_le_card hbad
  show Iall.card + Sgood.card ≤ Igood.card + Sall.card
  omega

/-- **Reduced planted estimate, host-generic** (`lem:planted-estimate`, equal non-root clones).
The same bound as `planted_estimate` holds for *any* host `B` over the blow-up vertex type with the
same planted roots as `blowupLabeledGraph m θ c` (`hBroots`) and whose good subsets induce `F₀`
exactly when the blow-up's do (`hBgood`).  The host enters the proof only through these two
hypotheses: every other count depends solely on the planted-root finset and clone sizes. -/
theorem planted_estimate_host (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (F₀ : LabeledGraph H (Fin ℓ)) (M : ℕ)
    (hM : ∀ v, v ∉ Finset.image (fun t => θ t) Finset.univ → m v = M)
    (B : LabeledGraph H (Σ v : Fin n, Fin (m v)))
    (hBroots : B.type_verts = (blowupLabeledGraph m θ c).type_verts)
    (hBgood : ∀ (S' : Finset (Σ v : Fin n, Fin (m v))),
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))) →
        ∀ (hr : B.type_verts ⊆ (↑S' : Set _))
          (hr' : (blowupLabeledGraph m θ c).type_verts ⊆ (↑S' : Set _)),
          (Nonempty ((inducedLabeledSubgraph B (↑S') hr).coe ≃f F₀) ↔
           Nonempty ((inducedLabeledSubgraph (blowupLabeledGraph m θ c) (↑S') hr').coe ≃f F₀))) :
    |flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ)) (⟦B⟧ : Flag H (Σ v : Fin n, Fin (m v)))
       - flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ)) (⟦baseLabeledGraph θ⟧ : Flag H (Fin n))|
      ≤ 1 - (M ^ (ℓ - k) * ((n - k).choose (ℓ - k)) : ℚ)
            / (((∑ v, m v) - k).choose (ℓ - k)) := by
  -- The host roots, as a finset, coincide with the planted-root finset.
  have hBrootsF : B.type_verts.toFinset = (blowupLabeledGraph m θ c).type_verts.toFinset := by
    rw [Set.toFinset_congr hBroots]
  -- `F₀.type_embed : Fin k ↪ Fin ℓ` is injective, so `k ≤ ℓ`.
  have hk : k ≤ ℓ := by
    have := Fintype.card_le_of_injective (F₀.type_embed : Fin k → Fin ℓ) F₀.type_embed.injective
    simpa only [Fintype.card_fin] using this
  -- Abstract rational sandwich: `ρ·pb ≤ pblow ≤ ρ·pb + (1-ρ)` with `pb, ρ ∈ [0,1]` forces the bound.
  have final : ∀ (pb pblow ρ : ℚ), 0 ≤ pb → pb ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      ρ * pb ≤ pblow → pblow ≤ ρ * pb + (1 - ρ) → |pblow - pb| ≤ 1 - ρ := by
    intro pb pblow ρ hpb0 hpb1 hρ0 hρ1 hlo hhi
    rw [abs_le]; constructor <;> nlinarith
  -- The two densities are nonnegative and at most one.
  set pblow := flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ))
      (⟦B⟧ : Flag H (Σ v : Fin n, Fin (m v))) with hpblow_def
  set pbase := flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ)) (⟦baseLabeledGraph θ⟧ : Flag H (Fin n))
    with hpbase_def
  have hpbase0 : 0 ≤ pbase := flagListDensity₁_ge_zero _ _
  have hpbase1 : pbase ≤ 1 := flagListDensity₁_le_one _ _
  -- The two density-as-count equations.  `B.size = ∑ v, m v` since `B` is over the blow-up type.
  have hpblow_eq : pblow
      = ((Finset.univ.filter (fun S : Finset (Σ v : Fin n, Fin (m v)) =>
          ∃ (h : B.type_verts ⊆ (↑S : Set (Σ v : Fin n, Fin (m v)))),
            Nonempty ((inducedLabeledSubgraph B (↑S) h).coe
              ≃f F₀))).card : ℚ)
        / (((∑ v, m v) - k).choose (ℓ - k)) := by
    rw [hpblow_def, flagDensity₁_eq_subset_count_div F₀ B]
    simp only [LabeledGraph.size, Fintype.card_sigma, Fintype.card_fin, FlagType.size]
  have hpbase_eq : pbase
      = ((Finset.univ.filter (fun S : Finset (Fin n) =>
          ∃ (h : (baseLabeledGraph θ).type_verts ⊆ (↑S : Set (Fin n))),
            Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑S) h).coe ≃f F₀))).card : ℚ)
        / ((n - k).choose (ℓ - k)) := by
    rw [hpbase_def, flagDensity₁_eq_subset_count_div F₀ (baseLabeledGraph θ)]
    simp only [LabeledGraph.size, Fintype.card_fin, FlagType.size]
  -- Abbreviate the four counts and the denominators.
  set Aiall := (Finset.univ.filter (fun S : Finset (Σ v : Fin n, Fin (m v)) =>
      ∃ (h : B.type_verts ⊆ (↑S : Set (Σ v : Fin n, Fin (m v)))),
        Nonempty ((inducedLabeledSubgraph B (↑S) h).coe ≃f F₀))).card
    with hAiall
  set Aibase := (Finset.univ.filter (fun S : Finset (Fin n) =>
      ∃ (h : (baseLabeledGraph θ).type_verts ⊆ (↑S : Set (Fin n))),
        Nonempty ((inducedLabeledSubgraph (baseLabeledGraph θ) (↑S) h).coe ≃f F₀))).card
    with hAibase
  set Cblow : ℕ := ((∑ v, m v) - k).choose (ℓ - k) with hCblow
  set Cbase : ℕ := (n - k).choose (ℓ - k) with hCbase
  -- If `Cblow = 0` (i.e. `ℓ > N`), the bound is `≤ 1`, which holds since both densities lie in [0,1].
  have hpblow0 : 0 ≤ pblow := flagListDensity₁_ge_zero _ _
  have hpblow1 : pblow ≤ 1 := flagListDensity₁_le_one _ _
  rcases Nat.eq_zero_or_pos Cblow with hCblow0 | hCblowpos
  · rw [hpblow_eq] at hpblow0 hpblow1
    rw [hpbase_eq] at hpbase0 hpbase1
    rw [hpblow_eq, hpbase_eq]
    simp only [hCblow0, Nat.cast_zero, div_zero, sub_zero] at hpblow0 hpblow1 ⊢
    rw [abs_le]; constructor <;> nlinarith
  have hCblowQ : (0 : ℚ) < Cblow := by rw [Nat.cast_pos]; exact hCblowpos
  -- The total counts of size-`ℓ` host-root supersets ("all" and "good").  Computed over `B`'s roots,
  -- which equal the planted-root finset (`hBrootsF`).
  have hTall : (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      B.type_verts.toFinset ⊆ S' ∧ S'.card = ℓ)).card = Cblow := by
    rw [hBrootsF,
      superset_count (blowupLabeledGraph m θ c).type_verts.toFinset ℓ
        (by rw [plantedRoots_card m θ c]; exact hk),
      plantedRoots_card m θ c, hCblow]
    congr 2
    simp only [Fintype.card_sigma, Fintype.card_fin]
  have hTgood : (Finset.univ.filter (fun S' : Finset (Σ v : Fin n, Fin (m v)) =>
      B.type_verts.toFinset ⊆ S' ∧ S'.card = ℓ ∧
        Set.InjOn Sigma.fst (↑S' : Set (Σ v : Fin n, Fin (m v))))).card
      = Cbase * M ^ (ℓ - k) := by
    rw [hBrootsF, good_total_count m θ c M hk hM, hCbase]
  -- The count split: `A_good ≤ A_blow` and `A_blow + T_good ≤ A_good + T_all`.
  have hAgood : Aiall ≥ M ^ (ℓ - k) * Aibase ∧
      Aiall + Cbase * M ^ (ℓ - k) ≤ M ^ (ℓ - k) * Aibase + Cblow := by
    have hsplit := count_split m B F₀
    simp only at hsplit
    obtain ⟨hgood_le, hbad_le⟩ := hsplit
    rw [good_event_count_const_host m θ c F₀ M hM B hBroots hBgood] at hgood_le
    rw [good_event_count_const_host m θ c F₀ M hM B hBroots hBgood, hTall, hTgood] at hbad_le
    exact ⟨hgood_le, hbad_le⟩
  obtain ⟨hAgood_le, hbad_le⟩ := hAgood
  -- `T_good ≤ T_all`, i.e. `Cbase·M^(ℓ-k) ≤ Cblow`.
  have hgood_le_all : Cbase * M ^ (ℓ - k) ≤ Cblow := by
    rw [← hTgood, ← hTall]
    apply Finset.card_le_card
    intro S' hS'
    rw [Finset.mem_filter] at hS' ⊢
    obtain ⟨hu, hroot, hcard, _⟩ := hS'
    exact ⟨hu, hroot, hcard⟩
  -- `Aibase ≤ Cbase` (base density count bound).
  have hbaseSuperset : (Finset.univ.filter (fun S : Finset (Fin n) =>
      (baseLabeledGraph θ).type_verts.toFinset ⊆ S ∧ S.card = ℓ)).card = Cbase := by
    rw [superset_count (baseLabeledGraph θ).type_verts.toFinset ℓ
        (by rw [baseRoots_card]; exact hk), baseRoots_card, hCbase]
    congr 2
    rw [Fintype.card_fin]
  have hAibase_le : Aibase ≤ Cbase := by
    rw [hAibase, ← hbaseSuperset]
    apply Finset.card_le_card
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    obtain ⟨hu, hroot, hind⟩ := hS
    refine ⟨hu, Set.toFinset_subset.mpr hroot, ?_⟩
    exact induced_iso_card (baseLabeledGraph θ) F₀ S hroot hind
  -- Now the rational algebra.  Set `ρ := M^(ℓ-k)·Cbase/Cblow`, the "good" probability.
  set ρ : ℚ := (M ^ (ℓ - k) * (Cbase : ℚ)) / Cblow with hρ
  -- ρ ∈ [0, 1].
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hCblowQ]
    rw [show (M ^ (ℓ - k) * (Cbase : ℚ)) = ((Cbase * M ^ (ℓ - k) : ℕ) : ℚ) by push_cast; ring]
    exact_mod_cast hgood_le_all
  -- `ρ · pbase = M^(ℓ-k)·Aibase / Cblow`.
  have hρpb : ρ * ((Aibase : ℚ) / Cbase) = (M ^ (ℓ - k) * (Aibase : ℚ)) / Cblow := by
    rw [hρ]
    by_cases hCbase0 : Cbase = 0
    · have hAib0 : Aibase = 0 := Nat.le_zero.mp (hCbase0 ▸ hAibase_le)
      simp [hCbase0, hAib0]
    · have hCbaseQ : (Cbase : ℚ) ≠ 0 := by exact_mod_cast hCbase0
      field_simp
  -- Lower bound: `ρ·pbase ≤ pblow` (from `A_good = M^(ℓ-k)·A_base ≤ A_blow`).
  have hlo : ρ * ((Aibase : ℚ) / Cbase) ≤ (Aiall : ℚ) / Cblow := by
    rw [hρpb, div_le_div_iff_of_pos_right hCblowQ]
    rw [show (M ^ (ℓ - k) * (Aibase : ℚ)) = ((M ^ (ℓ - k) * Aibase : ℕ) : ℚ) by push_cast; ring]
    exact_mod_cast hAgood_le
  -- Upper bound: `pblow ≤ ρ·pbase + (1 - ρ)` (from `A_blow + T_good ≤ A_good + T_all`).
  have hhi : (Aiall : ℚ) / Cblow ≤ ρ * ((Aibase : ℚ) / Cbase) + (1 - ρ) := by
    rw [hρpb, hρ]
    have heq : (M ^ (ℓ - k) * (Aibase : ℚ)) / Cblow
          + (1 - (M ^ (ℓ - k) * (Cbase : ℚ)) / Cblow)
        = ((M ^ (ℓ - k) * Aibase + Cblow : ℕ) : ℚ) / Cblow
          - ((Cbase * M ^ (ℓ - k) : ℕ) : ℚ) / Cblow := by
      field_simp
      push_cast
      ring
    rw [heq, ← sub_div, div_le_div_iff_of_pos_right hCblowQ]
    rw [show ((M ^ (ℓ - k) * Aibase + Cblow : ℕ) : ℚ) - ((Cbase * M ^ (ℓ - k) : ℕ) : ℚ)
          = (((M ^ (ℓ - k) * Aibase + Cblow) - Cbase * M ^ (ℓ - k) : ℕ) : ℚ) by
        rw [Nat.cast_sub (by omega)]]
    exact_mod_cast (by omega : Aiall ≤ (M ^ (ℓ - k) * Aibase + Cblow) - Cbase * M ^ (ℓ - k))
  -- Assemble via the abstract sandwich.  `set` has already folded the counts/denominators, so
  -- `hpblow_eq`/`hpbase_eq` read `pblow = Aiall/Cblow`, `pbase = Aibase/Cbase`, and the goal's RHS
  -- is `1 - ρ`.
  rw [hpblow_eq, hpbase_eq]
  exact final ((Aibase : ℚ) / Cbase) ((Aiall : ℚ) / Cblow) ρ
    (by rw [← hpbase_eq]; exact hpbase0) (by rw [← hpbase_eq]; exact hpbase1) hρ0 hρ1 hlo hhi

/-- **Reduced planted estimate** (`lem:planted-estimate`, equal non-root clones): the density of
`F₀` in the planted blow-up differs from its density in the base by at most `1 - ρ`, where
`ρ = M^(ℓ-k)·C(n-k, ℓ-k) / C(N-k, ℓ-k)` (`N = ∑ v, m v`) is the probability a uniform
`(ℓ-k)`-sample of non-root blow-up vertices meets each clone class at most once.  The instance of
`planted_estimate_host` at the host `B = blowupLabeledGraph m θ c`. -/
theorem planted_estimate (m : Fin n → ℕ) (θ : H ↪g G) (c : ∀ i, Fin (m (θ i)))
    (F₀ : LabeledGraph H (Fin ℓ)) (M : ℕ)
    (hM : ∀ v, v ∉ Finset.image (fun t => θ t) Finset.univ → m v = M) :
    |flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ)) (⟦blowupLabeledGraph m θ c⟧ : Flag H (Σ v : Fin n, Fin (m v)))
       - flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ)) (⟦baseLabeledGraph θ⟧ : Flag H (Fin n))|
      ≤ 1 - (M ^ (ℓ - k) * ((n - k).choose (ℓ - k)) : ℚ)
            / (((∑ v, m v) - k).choose (ℓ - k)) :=
  planted_estimate_host m θ c F₀ M hM (blowupLabeledGraph m θ c) rfl
    (fun _ _ _ _ => Iff.rfl)

end FlagAlgebras.MetaTheory
